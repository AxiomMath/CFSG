module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def IsDMin_uc6 (D Q : Subgroup G) : Prop :=
  ∀ Q₁ : Subgroup G, Q₁ ≤ Q → D ≤ normalizer (Q₁ : Set G) → ⁅D, Q₁⁆ = Q₁ → Q₁ = ⊥ ∨ Q₁ = Q

theorem mem_centerG_uc6 {Q : Subgroup G} {y : G} :
    y ∈ (center ↥Q).map Q.subtype ↔ y ∈ Q ∧ ∀ g ∈ Q, g * y = y * g := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun g hg => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩

theorem le_normalizer_of_invariant_uc6 {D S : Subgroup G}
    (h : ∀ d ∈ D, ∀ s ∈ S, d * s * d⁻¹ ∈ S) : D ≤ normalizer (S : Set G) := by
  intro d hd
  rw [mem_normalizer_iff]
  intro s
  refine ⟨h d hd s, fun hs => ?_⟩
  have := h d⁻¹ (D.inv_mem hd) _ hs
  simpa [mul_assoc] using this

theorem coprime_card_le_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {Q S : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hSQ : S ≤ Q) : Nat.Coprime r (Nat.card S) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hQ2.to_le hSQ)
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr Nat.prime_two).2 hr2)

theorem dmin_dichotomy_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hQ2 : IsPGroup 2 Q) (hmin : IsDMin_uc6 D Q) {S : Subgroup G}
    (hSQ : S ≤ Q) (hDS : D ≤ normalizer (S : Set G)) : ⁅S, D⁆ = ⊥ ∨ S = Q := by
  have hDp : IsPGroup r D := IsPGroup.of_card (n := 1) (by rw [hD, pow_one])
  have hidem : ⁅⁅S, D⁆, D⁆ = ⁅S, D⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent r hr D S hDp hDS
      (coprime_card_le_uc6 hr hr2 hQ2 hSQ)
  have hYS : ⁅S, D⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.1 hDS
  have hDY : D ≤ normalizer ((⁅S, D⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right S D
  rcases hmin ⁅S, D⁆ (hYS.trans hSQ) hDY (by rw [Subgroup.commutator_comm, hidem]) with h | h
  · exact Or.inl h
  · exact Or.inr (le_antisymm hSQ (h ▸ hYS))

theorem commute_of_commutator_eq_bot_uc6 {D S : Subgroup G} (h : ⁅S, D⁆ = ⊥) :
    ∀ s ∈ S, ∀ d ∈ D, d * s = s * d := by
  intro s hs d hd
  have h1 : ⁅s, d⁆ ∈ (⊥ : Subgroup G) := h ▸ Subgroup.commutator_mem_commutator hs hd
  exact (commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 h1)).symm

theorem orderOf_conj_coprime_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hDQ : D ≤ normalizer (Q : Set G)) {d : G} (hd : d ∈ D) :
    Nat.Coprime (orderOf (Q.normalizerMonoidHom ⟨d, hDQ hd⟩)) 2 := by
  have hdr : d ^ r = 1 := by
    have h1 : (⟨d, hd⟩ : ↥D) ^ r = 1 := hD ▸ pow_card_eq_one'
    simpa using congrArg Subtype.val h1
  have h2 : (Q.normalizerMonoidHom ⟨d, hDQ hd⟩) ^ r = 1 := by
    have h3 : (⟨d, hDQ hd⟩ : normalizer (Q : Set G)) ^ r = 1 := Subtype.ext (by simpa using hdr)
    rw [← map_pow, h3, map_one]
  exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)
    ((Nat.coprime_primes hr Nat.prime_two).2 hr2)

theorem d_centralizes_center_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hQ2 : IsPGroup 2 Q) (hDQ : D ≤ normalizer (Q : Set G))
    (hmin : IsDMin_uc6 D Q) (hnab : ¬ IsMulCommutative ↥Q) :
    ∀ d ∈ D, ∀ z ∈ (center ↥Q).map Q.subtype, d * z = z * d := by
  have hinv : ∀ d ∈ D, ∀ z ∈ (center ↥Q).map Q.subtype,
      d * z * d⁻¹ ∈ (center ↥Q).map Q.subtype := by
    intro d hd z hz
    rw [mem_centerG_uc6] at hz ⊢
    obtain ⟨hzQ, hzc⟩ := hz
    have hconj : ∀ g ∈ Q, d⁻¹ * g * d ∈ Q := fun g hg => by
      have := (mem_normalizer_iff.1 (hDQ (D.inv_mem hd)) g).1 hg
      simpa using this
    refine ⟨(mem_normalizer_iff.1 (hDQ hd) z).1 hzQ, fun g hg => ?_⟩
    have h1 := hzc _ (hconj g hg)
    calc g * (d * z * d⁻¹) = d * ((d⁻¹ * g * d) * z) * d⁻¹ := by group
      _ = d * (z * (d⁻¹ * g * d)) * d⁻¹ := by rw [h1]
      _ = (d * z * d⁻¹) * g := by group
  have hZQ : (center ↥Q).map Q.subtype ≤ Q := by
    intro z hz
    exact ((mem_centerG_uc6.1 hz).1)
  rcases dmin_dichotomy_uc6 hr hr2 hD hQ2 hmin hZQ (le_normalizer_of_invariant_uc6 hinv) with h | h
  · exact fun d hd z hz => commute_of_commutator_eq_bot_uc6 h z hz d hd
  · exfalso
    apply hnab
    refine ⟨⟨fun a b => ?_⟩⟩
    have : (a : G) ∈ (center ↥Q).map Q.subtype := by rw [h]; exact a.2
    exact Subtype.ext ((mem_centerG_uc6.1 this).2 b b.2).symm

theorem critical_eq_top_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) (hmin : IsDMin_uc6 D Q) :
    CFSG.SectionRank.Ccomm.IsThompsonCritical (⊤ : Subgroup ↥Q) := by
  obtain ⟨C, hC, -, hCfaith⟩ := CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical
    (p := 2) hQ2
  suffices hCtop : C = ⊤ by rw [← hCtop]; exact hC
  have hCchar : C.Characteristic := hC.1
  have hCg_inv : ∀ d ∈ D, ∀ c ∈ C.map Q.subtype, d * c * d⁻¹ ∈ C.map Q.subtype := by
    intro d hd c hc
    obtain ⟨g, hgC, rfl⟩ := hc
    refine ⟨Q.normalizerMonoidHom ⟨d, hDQ hd⟩ g, ?_, rfl⟩
    have hfix := Subgroup.Characteristic.fixed hCchar
      (Q.normalizerMonoidHom ⟨d, hDQ hd⟩ : MulAut ↥Q)
    have h1 : g ∈ C.comap (Q.normalizerMonoidHom ⟨d, hDQ hd⟩ : MulAut ↥Q).toMonoidHom := by
      rw [hfix]
      exact hgC
    exact h1
  have hCgle : C.map Q.subtype ≤ Q := Subgroup.map_subtype_le C
  rcases dmin_dichotomy_uc6 hr hr2 hD hQ2 hmin hCgle (le_normalizer_of_invariant_uc6 hCg_inv)
    with h0 | hCgQ
  · exfalso
    have hcent := commute_of_commutator_eq_bot_uc6 h0
    have hall : ∀ d ∈ D, ∀ x : ↥Q, d * (x : G) * d⁻¹ = x := by
      intro d hd x
      have hα1 : Q.normalizerMonoidHom ⟨d, hDQ hd⟩ = 1 :=
        hCfaith _ (orderOf_conj_coprime_uc6 hr hr2 hD hDQ hd) (fun y hy => by
          apply Subtype.ext
          show d * (y : G) * d⁻¹ = (y : G)
          rw [mul_inv_eq_iff_eq_mul]
          exact hcent (y : G) ⟨y, hy, rfl⟩ d hd)
      have h2 : ((Q.normalizerMonoidHom ⟨d, hDQ hd⟩ x : ↥Q) : G) = d * (x : G) * d⁻¹ := rfl
      rw [← h2, hα1]
      rfl
    apply hQne
    rw [← hcomm, eq_bot_iff, Subgroup.commutator_le]
    intro d hd q hq
    rw [Subgroup.mem_bot, commutatorElement_def, hall d hd ⟨q, hq⟩]
    simp
  · refine eq_top_iff.2 fun g _ => ?_
    have : (g : G) ∈ C.map Q.subtype := by rw [hCgQ]; exact g.2
    obtain ⟨c, hc, hcg⟩ := this
    exact (Subtype.ext hcg : c = g) ▸ hc

theorem structure1_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) (hmin : IsDMin_uc6 D Q)
    (hnab : ¬ IsMulCommutative ↥Q) :
    commutator ↥Q ≤ center ↥Q ∧ (∀ x : ↥Q, x ^ 2 ∈ center ↥Q) ∧
      ∀ d ∈ D, ∀ z ∈ (center ↥Q).map Q.subtype, d * z = z * d := by
  obtain ⟨-, hfr, hcomm', -⟩ := critical_eq_top_uc6 hr hr2 hD hQ2 hQne hDQ hcomm hmin
  refine ⟨?_, ?_, d_centralizes_center_uc6 hr hr2 hD hQ2 hDQ hmin hnab⟩
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 := hcomm' (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.1 h1.2) g (Subgroup.mem_top g)
  · intro x
    haveI : Fact (IsPGroup 2 ↥(⊤ : Subgroup ↥Q)) := ⟨hQ2.to_subgroup ⊤⟩
    have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2)
      (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup ↥Q))
    have h2 := hfr (Subgroup.mem_map_of_mem (⊤ : Subgroup ↥Q).subtype h1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.1 h2.2) g (Subgroup.mem_top g)

end CFSG.LocalAnalysis.UniquenessCase.UC6
