module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SuzNWC
public import CFSG.Sporadic.SuzOddCore.InvCentralizers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification

variable {G : Type} [Group G]

structure Comp (z : G) (A R : Subgroup G) : Prop where
  standard : standardComponentIsStandard A
  type : TypeL34 (rankTwoQuot A)
  odd : Odd (Nat.card (center A))
  sylow : IsSylowOf 2 R (centralizer (A : Set G))
  elem : IsElemAbelian 2 R
  card : Nat.card R = 4
  z_mem : z ∈ A
  le_normalizer : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G)

theorem exists_comp {z : G} (h : SuzL34Data z) : ∃ A R : Subgroup G, Comp z A R := by
  obtain ⟨A, R, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨A, R, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem card_centralizer_conj (c r : G) :
    Nat.card (centralizer ({c * r * c⁻¹} : Set G)) = Nat.card (centralizer ({r} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x * c, mem_centralizer_singleton_iff.2 ?_⟩
      invFun := fun x => ⟨c * x * c⁻¹, mem_centralizer_singleton_iff.2 ?_⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  · have h := mem_centralizer_singleton_iff.1 x.2
    calc c⁻¹ * ↑x * c * r = c⁻¹ * (↑x * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * r * c⁻¹ * ↑x) * c := by rw [h]
      _ = r * (c⁻¹ * ↑x * c) := by group
  · have h := mem_centralizer_singleton_iff.1 x.2
    calc c * ↑x * c⁻¹ * (c * r * c⁻¹) = c * (↑x * r) * c⁻¹ := by group
      _ = c * (r * ↑x) * c⁻¹ := by rw [h]
      _ = c * r * c⁻¹ * (c * ↑x * c⁻¹) := by group

@[expose] def NonCentralSylow (z : G) : Prop :=
  ∀ t ∈ centralizer ({z} : Set G), orderOf t = 2 → ¬ IsConj t z →
    IsSylowOf 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))
        (centralizer ({t} : Set G)) ∧
      Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 512

namespace Comp

variable {z : G} {A R : Subgroup G}

theorem R_le_centralizer (hc : Comp z A R) : R ≤ centralizer (A : Set G) := by
  obtain ⟨Q, hQ⟩ := hc.sylow
  rw [← hQ]
  exact map_subtype_le _

theorem le_centralizer_of_mem (hc : Comp z A R) {r : G} (hr : r ∈ R) :
    A ≤ centralizer ({r} : Set G) := fun a ha =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hc.R_le_centralizer hr) a ha)

theorem centralizer_le_M (hc : Comp z A R) :
    centralizer (A : Set G) ≤ centralizer ({z} : Set G) :=
  centralizer_le (Set.singleton_subset_iff.2 hc.z_mem)

theorem R_le_M (hc : Comp z A R) : R ≤ centralizer ({z} : Set G) :=
  hc.R_le_centralizer.trans hc.centralizer_le_M

theorem comm (hc : Comp z A R) {x y : G} (hx : x ∈ R) (hy : y ∈ R) : x * y = y * x :=
  congrArg Subtype.val (hc.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem R_le_centralizer_of_mem (hc : Comp z A R) {r : G} (hr : r ∈ R) :
    R ≤ centralizer ({r} : Set G) := fun _ hx => mem_centralizer_singleton_iff.2 (hc.comm hx hr)

theorem orderOf_eq_two (hc : Comp z A R) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) : orderOf r = 2 :=
  orderOf_eq_prime (hc.elem.2 r hr) hr1

theorem exists_ne_one (hc : Comp z A R) : ∃ r ∈ R, r ≠ 1 := by
  have hne : R ≠ ⊥ := fun h => by
    have := hc.card
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨r, hr⟩, h1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  exact ⟨r, hr, fun h => h1 (Subtype.ext h)⟩

section Orders


theorem seven_dvd_card (hc : Comp z A R) : 7 ∣ Nat.card A := by
  obtain ⟨e⟩ := PSL3Four.nonempty_equiv_of_stated (rankTwoQuot A) hc.type
  have h1 : Nat.card (rankTwoQuot A) = 20160 := by
    rw [Nat.card_congr e.toEquiv, PSL3Four.card_S]
  rw [(center A).card_eq_card_quotient_mul_card_subgroup]
  exact Dvd.dvd.mul_right (by rw [h1]; norm_num) _

theorem not_isConj (hc : Comp z A R) (hM : Nat.card (centralizer ({z} : Set G)) = 3317760)
    {r : G} (hr : r ∈ R) : ¬ IsConj r z := by
  intro hconj
  obtain ⟨c, hcz⟩ := isConj_iff.1 hconj
  have h7 : 7 ∣ Nat.card (centralizer ({r} : Set G)) :=
    hc.seven_dvd_card.trans (Subgroup.card_dvd_of_le (hc.le_centralizer_of_mem hr))
  rw [← card_centralizer_conj c r, hcz, hM] at h7
  norm_num at h7

theorem isSylowOf_inf (hc : Comp z A R) (hM : Nat.card (centralizer ({z} : Set G)) = 3317760)
    (hH : NonCentralSylow z) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    IsSylowOf 2 (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G))
        (centralizer ({r} : Set G)) ∧
      Nat.card (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 512 :=
  hH r (hc.R_le_M hr) (hc.orderOf_eq_two hr hr1) (hc.not_isConj hM hr)

theorem isPGroup_inf (hc : Comp z A R) (hM : Nat.card (centralizer ({z} : Set G)) = 3317760)
    (hH : NonCentralSylow z) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    IsPGroup 2 (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) :=
  IsPGroup.of_card (n := 9) (by rw [(hc.isSylowOf_inf hM hH hr hr1).2]; norm_num)

variable [Finite G]

theorem center_eq_bot (hc : Comp z A R) (hM : Nat.card (centralizer ({z} : Set G)) = 3317760)
    (hH : NonCentralSylow z) : center A = ⊥ := by
  obtain ⟨r, hr, hr1⟩ := hc.exists_ne_one
  have hP := hc.isPGroup_inf hM hH hr hr1
  have hZ : IsPGroup 2 (center A) := fun g => by
    have hzg : z * ((g : A) : G) = ((g : A) : G) * z :=
      congrArg Subtype.val (mem_center_iff.1 g.2 ⟨z, hc.z_mem⟩)
    have hmem : ((g : A) : G) ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) :=
      ⟨hc.le_centralizer_of_mem hr (g : A).2, mem_centralizer_singleton_iff.2 hzg.symm⟩
    obtain ⟨k, hk⟩ := hP ⟨_, hmem⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ
  have hn0 : n = 0 := by
    by_contra h
    have heven : Even (Nat.card (center A)) := hn ▸ (Nat.even_pow.2 ⟨even_two, h⟩)
    exact (Nat.not_even_iff_odd.2 hc.odd) heven
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

theorem centralizer_inf_eq (hc : Comp z A R)
    (hM : Nat.card (centralizer ({z} : Set G)) = 3317760) (hH : NonCentralSylow z) {r : G}
    (hr : r ∈ R) (hr1 : r ≠ 1) : centralizer ({r} : Set G) ⊓ centralizer (A : Set G) = R := by
  have hP' : IsPGroup 2 (centralizer ({r} : Set G) ⊓ centralizer (A : Set G) : Subgroup G) :=
    (hc.isPGroup_inf hM hH hr hr1).to_le (inf_le_inf_left _ hc.centralizer_le_M)
  exact hc.sylow.eq_of_le (le_inf (hc.R_le_centralizer_of_mem hr) hc.R_le_centralizer)
    inf_le_right hP'

end Orders

end Comp

section Model


theorem card_M_of_mulEquiv {G : Type} [Group G] (S : CFSG.LargeExtraspecial.Setting G)
    (σ : S.M ≃* CFSG.Sporadic.SuzOddCore.invE 1) : Nat.card S.M = 3317760 := by
  rw [Nat.card_congr σ.toEquiv, CFSG.Sporadic.SuzOddCore.card_invE (i := 1) (by norm_num)]
  rfl

end Model

end CFSG.Sporadic.SuzRecog.LocalR
