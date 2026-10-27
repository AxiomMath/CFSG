module

public import CFSG.RankThree.PartOne.AUTSL.FourAbs
public import CFSG.RankThree.PartOne.S15K.CovFour
import CFSG.RankThree.PartOne.S12.Sec1322Reflect

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def FourFacts (p : ℕ) (E I : Subgroup G) : Prop :=
  ∃ ℓ : Fin 3 → Subgroup ↥E,
    (∀ i, Nat.card ↥(ℓ i) = p) ∧ (⨆ i, ℓ i = ⊤) ∧ (∀ i, ℓ i ⊓ ⨆ j, ⨆ (_ : j ≠ i), ℓ j = ⊥) ∧
    (∀ (y : G) (hy : y ∈ Subgroup.normalizer (E : Set G)), y ∈ I →
      ∃ π : Equiv.Perm (Fin 3), ∀ i, (ℓ i).map (conjAut E y hy).toMonoidHom = ℓ (π i)) ∧
    (∀ D J S : Subgroup G, D ≤ E → p * Nat.card ↥D = Nat.card ↥E → J ≤ I →
      J ≤ Subgroup.centralizer (D : Set G) → ⁅J, J⁆ = J → S ≤ J → S ≠ ⊥ → IsPGroup 2 S →
      E ≤ Subgroup.normalizer (S : Set G) → S = ⁅S, E⁆ →
      ∃ k, D = (⨆ j, ⨆ (_ : j ≠ k), ℓ j).map E.subtype ∧ ∀ e : ↥E, (e : G) ∈ J → e ∈ ℓ k)

@[expose] def FourModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Four p E A (lieGenerated p E) → FourFacts p E (lieGenerated p E)

variable [Finite G]

theorem exists_other_two : ∀ k : Fin 3, ∃ i j : Fin 3, i ≠ k ∧ j ≠ k ∧ i ≠ j := by decide

theorem kf158FourShort_of_model (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hKF156 : KF156') (hM : FourModel) :
    KF158FourShort := by
  intro G _ _ p A c L E h15 hF h13 hout t ht K J hKt hKJ hmov hcard hJθ hS2
  classical
  have h := h15.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inl hout)))
  obtain ⟨ℓ, hℓcard, hℓtop, hℓind, hmono, hdata⟩ := hM G p A c L E h15 hF h13 hout
  obtain ⟨-, -, -, -, ⟨φ⟩, hEA, -⟩ := hout
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  have hpow : ∀ y : ↥E, y ^ p = 1 := fun y =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h y.2)
  let _ : CommGroup ↥E := commGroupOf hEc
  have hℓ : ThreeLines p ℓ := ⟨hℓcard, hℓtop, hℓind⟩
  set D : Subgroup G := A ⊓ Subgroup.centralizer (J : Set G) with hDdef
  have hDcard : Nat.card ↥D = p ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    rw [hcard, h.A_card]
    ring
  obtain ⟨b, hbD, hb1⟩ : ∃ b ∈ D, b ≠ 1 := by
    have hne : D ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hDcard
      have := hp.one_lt
      nlinarith
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩
  have hJX := Sec158.layer_ge_of_KF158A hS h82 h15 hcard hJθ hS2 hbD hb1
  have hJI : J ≤ lieGenerated p E :=
    hJX.trans (Sec158.zeroLayer_le_lieGenerated hKF156 h15 hF hout' b)
  have hJperf : ⁅J, J⁆ = J := by
    obtain ⟨L', hL', hLJ⟩ := hJθ
    have : Group.IsPerfect ↥L' := hL'.1
    have h2 : Group.IsPerfect ↥(L'.map (Subgroup.centralizer (D : Set G)).subtype) :=
      Group.IsPerfect.map _
    have hLJ' : L'.map (Subgroup.centralizer (D : Set G)).subtype = J := hLJ
    rw [hLJ'] at h2
    exact Subgroup.commutator_eq_self
  obtain ⟨S, hSJ, hS1, hS2', hSn, hSc⟩ := hS2
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := by
    intro j hj d hd
    have hd' : d ∈ A ⊓ Subgroup.centralizer (J : Set G) := hd
    exact (Subgroup.mem_centralizer_iff.1 hd'.2 j hj).symm
  have hDE : D ≤ E := by
    rw [hEA]
    exact inf_le_left
  have hDcardE : p * Nat.card ↥D = Nat.card ↥E := by rw [hEA]; exact hcard
  have hSn' : E ≤ Subgroup.normalizer (S : Set G) := by rw [hEA]; exact hSn
  have hSc' : S = ⁅S, E⁆ := by rw [hEA]; exact hSc
  obtain ⟨k, hDk, hJk⟩ := hdata D J S hDE hDcardE hJI hJD hJperf hSJ hS1 hS2' hSn' hSc'
  have hrefl : ∀ s ∈ reflectionSet p E, LineMono ℓ s := by
    rintro s ⟨-, X, hX, hsX⟩
    have hXI : X ≤ lieGenerated p E := hKF156 G p A c L E h15 hF hout' X hX.1
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hsX
    exact hmono n.1 n.2 (hXI (Subgroup.mem_subgroupOf.1 hn))
  have hXmono : ∀ x ∈ reflectionGroup p E, LineMono ℓ x := by
    have hle : reflectionGroup p E ≤ lineMonoSubgroup ℓ := (Subgroup.closure_le _).2 hrefl
    exact fun x hx => hle hx
  have htm : ∀ e : ↥E, t e * e⁻¹ ∈ ℓ k := by
    intro e
    have h0 : t e * e⁻¹ ∈ autMoved E t := Subgroup.subset_closure ⟨e, rfl⟩
    have h1 : ((t e * e⁻¹ : ↥E) : G) ∈ autMovedInG E t := Subgroup.mem_map_of_mem E.subtype h0
    exact hJk _ (hKJ (hmov h1))
  have hmovle : autMoved E t ≤ ℓ k := (Subgroup.closure_le _).2 (by rintro _ ⟨e, rfl⟩; exact htm e)
  have hmoveq : autMoved E t = ℓ k :=
    Subgroup.eq_of_le_of_card_ge hmovle (le_of_eq (by rw [ht.1.2, hℓcard k]))
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [ht.1.1, pow_two] at h1
    exact h1
  have hfix : Invol.fixS t = lineHyp ℓ k :=
    fixS_eq_lineHyp hp hp2 hℓ hEcard hpow (hrefl t ht) htt hmoveq
  refine ⟨?_, ?_⟩
  ·
    show D = autFixedInG E t
    rw [hDk]
    unfold autFixedInG
    have hfe : autFixed E t = Invol.fixS t := Subgroup.ext fun e => Iff.rfl
    rw [hfe, hfix]
    rfl
  · obtain ⟨i, j, hik, hjk, hij⟩ := exists_other_two k
    have hX : ∀ a b : Fin 3, ∃ w : G, ∃ hw : w ∈ Subgroup.normalizer (E : Set G),
        (ℓ a).map (conjAut E w hw).toMonoidHom = ℓ b := by
      intro a b
      obtain ⟨x, hx, hxab⟩ := exists_mem_map_eq hp hℓ (reflectionGroup p E) hXmono φ a b
      obtain ⟨w, hw, rfl⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hx)
      exact ⟨w, hw, hxab⟩
    have hconj : ∀ a : Fin 3, ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * t * (conjAut E w hw)⁻¹ ∈ reflectionSet p E ∧
        autMoved E (conjAut E w hw * t * (conjAut E w hw)⁻¹) = ℓ a := by
      intro a
      obtain ⟨w, hw, hwa⟩ := hX k a
      refine ⟨w, hw, conj_mem_reflectionSet hp ht hw, ?_⟩
      rw [Equivariance.autMoved_conj, hmoveq, hwa]
    obtain ⟨w₁, hw₁, hs₁, hm₁⟩ := hconj i
    obtain ⟨w₂, hw₂, hs₂, hm₂⟩ := hconj j
    have hmem : ∀ (s : MulAut ↥E) (a : Fin 3), autMoved E s = ℓ a → ∀ e : ↥E, s e * e⁻¹ ∈ ℓ a := by
      intro s a hs e
      rw [← hs]
      exact Subgroup.subset_closure ⟨e, rfl⟩
    set s₁ := conjAut E w₁ hw₁ * t * (conjAut E w₁ hw₁)⁻¹ with hs₁def
    set s₂ := conjAut E w₂ hw₂ * t * (conjAut E w₂ hw₂)⁻¹ with hs₂def
    refine ⟨s₁, hs₁, s₂, hs₂, ?_, ?_, ?_, ?_, ?_, ?_, ⟨w₁, hw₁, rfl⟩, ⟨w₂, hw₂, rfl⟩⟩
    · intro he
      have : ℓ i = ℓ k := by rw [← hm₁, he, hmoveq]
      exact hik (hℓ.injective hp this)
    · intro he
      have : ℓ j = ℓ k := by rw [← hm₂, he, hmoveq]
      exact hjk (hℓ.injective hp this)
    · intro he
      have : ℓ i = ℓ j := by rw [← hm₁, he, hm₂]
      exact hij (hℓ.injective hp this)
    · exact LineMono.comm hp hℓ (hrefl t ht) (hrefl s₁ hs₁) (Ne.symm hik) (hmem t k hmoveq)
        (hmem s₁ i hm₁)
    · exact LineMono.comm hp hℓ (hrefl t ht) (hrefl s₂ hs₂) (Ne.symm hjk) (hmem t k hmoveq)
        (hmem s₂ j hm₂)
    · exact LineMono.comm hp hℓ (hrefl s₁ hs₁) (hrefl s₂ hs₂) hij (hmem s₁ i hm₁) (hmem s₂ j hm₂)

end CFSG.RankThree.PartOne.AUTSL.Four
