module

public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.S12.Sec158Defs
public import CFSG.RankThree.PartOne.S15K.SL2Model
import CFSG.RankThree.PartOne.S12.Sec13Base
import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S11d.ThetaCalc
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SplitKt (p : ℕ) (E : Subgroup G) (t : MulAut E) : Prop :=
  ∃ f : ℕ, p ∣ 2 ^ f - 1 ∧ KFAt p E f t

omit [Finite G] in
theorem kZero_le_centralizer (p : ℕ) (E : Subgroup G) (t : MulAut E) :
    kZero p E t ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
  unfold kZero pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact (Subgroup.map_subtype_le _) hx

omit [Finite G] in
theorem kZero_normalized (p : ℕ) (E : Subgroup G) (t : MulAut E) {h : G}
    (hh : h ∈ Subgroup.centralizer (autFixedInG E t : Set G)) :
    h ∈ Subgroup.normalizer (kZero p E t : Set G) := by
  set H : Subgroup G := Subgroup.centralizer (autFixedInG E t : Set G) with hH
  have hHn : conjBy h H = H := Equivariance.conjBy_eq_of_mem_normalizer
    (Subgroup.le_normalizer hh)
  have hK : conjBy h (kZero p E t) = kZero p E t := by
    unfold kZero
    rw [← Equivariance.pElementSubgroup_conjBy, ← Equivariance.inSubgroup_layer_conjBy, ← hH, hHn]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have := Equivariance.mem_conjBy (w := h) (x := h * x * h⁻¹) (H := kZero p E t)
  rw [hK] at this
  have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  rw [e] at this
  exact this.symm

omit [Finite G] in
theorem kZero_normal_in (p : ℕ) (E : Subgroup G) (t : MulAut E) :
    ((kZero p E t).subgroupOf (Subgroup.centralizer (autFixedInG E t : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (kZero_le_centralizer p E t)]
  intro n k hn hk
  exact (Subgroup.mem_normalizer_iff.1 (kZero_normalized p E t hk) n).1 hn

theorem kZero_mem_thetaCompCentralizer {p : ℕ} (hp : p.Prime) {E : Subgroup G} {t : MulAut E}
    (hq : CFSG.IsQuasisimple ↥(kZero p E t)) {D : Subgroup G} (hD : D = autFixedInG E t) :
    kZero p E t ∈ thetaCompCentralizer p D := by
  subst hD
  have hle := kZero_le_centralizer p E t
  refine ⟨(kZero p E t).subgroupOf (Subgroup.centralizer (autFixedInG E t : Set G)), ?_, ?_⟩
  · refine mem_thetaComponents_of_quasisimple hp ?_ (kZero_normal_in p E t).isSubnormal
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq
  · show ((kZero p E t).subgroupOf (Subgroup.centralizer (autFixedInG E t : Set G))).map
      (Subgroup.centralizer (autFixedInG E t : Set G)).subtype = kZero p E t
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle]

omit [Finite G] in
theorem exists_gen_autMovedInG {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    {t : MulAut E} (ht : IsAutReflection p E t) :
    ∃ a : G, a ∈ E ∧ a ≠ 1 ∧ a ^ p = 1 ∧ autMovedInG E t = Subgroup.zpowers a := by
  have : Fact p.Prime := ⟨hp⟩
  have hcardM : Nat.card ↥(autMovedInG E t) = p := by
    unfold autMovedInG
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact ht.2
  have hcycM : IsCyclic ↥(autMovedInG E t) := isCyclic_of_prime_card hcardM
  obtain ⟨a, haz⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (autMovedInG E t)).1 hcycM
  have haM : a ∈ autMovedInG E t := haz ▸ Subgroup.mem_zpowers a
  have haE : a ∈ E := (Subgroup.map_subtype_le _) haM
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 : Nat.card ↥(Subgroup.zpowers a) = 1 := by rw [h1]; simp
    rw [haz, hcardM] at h2
    exact hp.one_lt.ne' h2
  exact ⟨a, haE, ha1, CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ haE, haz.symm⟩

omit [Finite G] in
theorem mem_normalizer_map_subtype {K : Subgroup G} {S₀ : Subgroup K} {a : K}
    (ha : a ∈ Subgroup.normalizer (S₀ : Set K)) :
    (a : G) ∈ Subgroup.normalizer ((S₀.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨a * s * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha s).1 hs, by simp⟩
  · rintro ⟨s', hs', hx⟩
    have hxK : x ∈ K := by
      have : (a : G)⁻¹ * (s' : G) * (a : G) ∈ K := K.mul_mem (K.mul_mem (K.inv_mem a.2) s'.2) a.2
      have e : x = (a : G)⁻¹ * (s' : G) * (a : G) := by
        have h1 : (a : G) * x * (a : G)⁻¹ = s' := hx.symm
        calc x = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (a : G) := by group
          _ = _ := by rw [h1]
      rw [e]
      exact this
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have h2 : a * ⟨x, hxK⟩ * a⁻¹ ∈ S₀ := by
      have : a * ⟨x, hxK⟩ * a⁻¹ = s' := Subtype.ext hx.symm
      rw [this]
      exact hs'
    exact (Subgroup.mem_normalizer_iff.1 ha _).2 h2

theorem splitKt_data {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    (hs : SplitKt p E t) :
    IsKt p E t (kZero p E t) ∧ autMovedInG E t ≤ kZero p E t ∧
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (kZero p E t : Set G)) = Nat.card ↥A ∧
      kZero p E t ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (kZero p E t : Set G)) ∧
      ∃ S : Subgroup G, S ≤ kZero p E t ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        A ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A⁆ := by
  subst hEA
  obtain ⟨f, hpf, hne, hmod, hcent, hmov, -⟩ := hs
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.three_lt; omega
  obtain ⟨-, -, -, hcardE⟩ := Sec13Base.reflection_facts h ht
  obtain ⟨hdec, -, -⟩ := node121a_of_hyp G p E c L E h t ht
  refine ⟨⟨fun f' hf' => absurd ⟨f', hf'⟩ hne, fun _ => rfl⟩, hmov, ?_,
    kZero_mem_thetaCompCentralizer hp (isQuasisimple_of_model hmod) hcent, ?_⟩
  · rw [hcent]
    unfold autFixedInG
    rw [Subgroup.card_map_of_injective E.subtype_injective, hcardE, mul_comm]
  · obtain ⟨a, haE, ha1, hap, hMz⟩ := exists_gen_autMovedInG hp h.E_elem ht.1
    have haK : a ∈ kZero p E t := hmov (hMz ▸ Subgroup.mem_zpowers a)
    obtain ⟨S₀, hS1, hS2, hSn, hSc⟩ := exists_two_subgroup_of_model hmod hp hp2 hpf
      (a := (⟨a, haK⟩ : ↥(kZero p E t))) (fun h1 => ha1 (congrArg Subtype.val h1))
      (Subtype.ext hap)
    have hmapK : ∀ y : ↥(kZero p E t), Subgroup.zpowers (y : G) =
        (Subgroup.zpowers y).map (kZero p E t).subtype := fun y => by
      rw [MonoidHom.map_zpowers]
      rfl
    set S : Subgroup G := S₀.map (kZero p E t).subtype with hSdef
    have hSK : S ≤ kZero p E t := Subgroup.map_subtype_le _
    have hCS : autFixedInG E t ≤ Subgroup.centralizer (S : Set G) := by
      intro y hy
      have hy' : y ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := hcent ▸ hy
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hSK) hy'.2
    have haN : a ∈ Subgroup.normalizer (S : Set G) :=
      mem_normalizer_map_subtype (a := (⟨a, haK⟩ : ↥(kZero p E t))) hSn
    have hEN : E ≤ Subgroup.normalizer (S : Set G) := by
      rw [hdec]
      refine sup_le (hCS.trans (Subgroup.centralizer_le_normalizer _)) ?_
      rw [hMz, Subgroup.zpowers_le]
      exact haN
    refine ⟨S, hSK, ?_, hS2.map _, hEN, ?_⟩
    · intro hb
      apply hS1
      rw [hSdef, Subgroup.map_eq_bot_iff_of_injective _ (kZero p E t).subtype_injective] at hb
      exact hb
    · have hSc' : ⁅S, Subgroup.zpowers a⁆ = S := by
        have h1 := congrArg (Subgroup.map (kZero p E t).subtype) hSc
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at h1
        exact h1
      apply le_antisymm
      · calc S = ⁅S, Subgroup.zpowers a⁆ := hSc'.symm
          _ ≤ ⁅S, E⁆ := Subgroup.commutator_mono_right (Subgroup.zpowers_le.2 haE)
      · exact Subgroup.le_normalizer_iff_commutator_le_left.1 hEN

end CFSG.RankThree.PartOne.S15K
