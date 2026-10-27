module

public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
public import CFSG.RankThree.PartTwo.KFacts.KS21U34
import CFSG.Monster.Existence.StdOdd.Coprime
import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec21 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem image_conj_fixedInG {A : Subgroup G} (hA : IsMulCommutative A) (φ : MulAut A) {a : G}
    (ha : a ∈ A) : (MulAut.conj a) '' (fixedInG A φ : Set G) = fixedInG A φ := by
  have hfix : ∀ b ∈ fixedInG A φ, (MulAut.conj a) b = b := by
    rintro _ ⟨b, -, rfl⟩
    have hab : (⟨a, ha⟩ : A) * b = b * ⟨a, ha⟩ := hA.is_comm.comm _ _
    have hab' : a * (b : G) = (b : G) * a := congrArg Subtype.val hab
    rw [MulAut.conj_apply]
    change a * (b : G) * a⁻¹ = (b : G)
    rw [hab', mul_inv_cancel_right]
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hfix b hb]
    exact hb
  · intro hy
    exact ⟨y, hy, hfix y hy⟩

theorem map_conj_kZero {A : Subgroup G} (hA : IsMulCommutative A) (φ : MulAut A) {a : G}
    (ha : a ∈ A) : (kZero A φ).map (MulAut.conj a).toMonoidHom = kZero A φ := by
  rw [kZero, map_oPrimeResidualOf, map_inSubgroup_layer, map_centralizer_mulEquiv,
    image_conj_fixedInG hA φ ha]

theorem le_normalizer_kZero {A : Subgroup G} (hA : IsMulCommutative A) (φ : MulAut A) :
    A ≤ Subgroup.normalizer (kZero A φ : Set G) := fun _ ha =>
  mem_normalizer_of_map_conj_eq (map_conj_kZero hA φ ha)

theorem card_inf_kZero_eq_three [Finite G] {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) (φ : MulAut A)
    (hU : StatedClassicalModel (kZero A φ) .PSU 3 2 2) :
    Nat.card (A ⊓ kZero A φ : Subgroup G) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardK0 : Nat.card (kZero A φ) = 62400 := by
    obtain ⟨e⟩ := U34.nonempty_equiv_Y hU
    rw [Nat.card_congr e.toEquiv, U34.card_Y]
  have hApg : IsPGroup 3 A := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2 a a.2)⟩
  have hmod := CFSG.Monster.Existence.StdOdd.card_modEq_inf_centralizer hApg
    (le_normalizer_kZero hA.1 φ)
  rw [hcardK0] at hmod
  have hdvd : 3 ∣ Nat.card (kZero A φ ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (by decide))
  obtain ⟨⟨k, hkmem⟩, hk⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hk' : orderOf k = 3 :=
    (Subgroup.orderOf_coe (⟨k, hkmem⟩ :
      ↥(kZero A φ ⊓ Subgroup.centralizer (A : Set G)))).trans hk
  have hkK0 : k ∈ kZero A φ := (Subgroup.mem_inf.mp hkmem).1
  have hkC : k ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp hkmem).2
  have hkA : k ∈ A := by
    have hB := CFSG.RankThree.PartTwo.Sec15.isElemAbelian_sup_zpowers hA
      (by rw [← hk']; exact pow_orderOf_eq_one _)
      (fun e he => (Subgroup.mem_centralizer_iff.mp hkC e he))
    have hAB := hmax _ hB le_sup_left
    have hmem : k ∈ A ⊔ Subgroup.zpowers k := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [hAB] at hmem
  have hInfPg : IsPGroup 3 (A ⊓ kZero A φ : Subgroup G) := hApg.to_le inf_le_left
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hInfPg
  have hdvd60 : Nat.card (A ⊓ kZero A φ : Subgroup G) ∣ 62400 :=
    hcardK0 ▸ Subgroup.card_dvd_of_le inf_le_right
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have h9 : 9 ∣ Nat.card (A ⊓ kZero A φ : Subgroup G) := by
      rw [hj]
      exact Dvd.dvd.trans (by norm_num : 9 ∣ 3 ^ 2) (pow_dvd_pow 3 (by omega : 2 ≤ j))
    have := h9.trans hdvd60
    norm_num at this
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    have hbot := Subgroup.eq_bot_of_card_eq _ hj
    have hkmem' : k ∈ (A ⊓ kZero A φ : Subgroup G) := Subgroup.mem_inf.mpr ⟨hkA, hkK0⟩
    rw [hbot, Subgroup.mem_bot] at hkmem'
    rw [hkmem', orderOf_one] at hk'
    exact absurd hk' (by norm_num)
  rw [hj, show j = 1 by omega, pow_one]

theorem kOfWellDefined_of_maximal [Finite G] {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) :
    KOfWellDefined A := by
  intro φ _ hU
  set K0 := kZero A φ with hK0
  have hle : A ⊓ K0 ≤ K0 := inf_le_right
  have hT : Nat.card ((A ⊓ K0).subgroupOf K0) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact card_inf_kZero_eq_three hA hmax φ hU
  obtain ⟨K', ⟨hK', hTK'⟩, huniq⟩ := U34.existsUnique_psl24_of_card_three hU _ hT
  have hmodel_map : ∀ L : Subgroup K0, StatedClassicalModel L .PSL 2 2 2 →
      StatedClassicalModel (L.map K0.subtype) .PSL 2 2 2 := fun L hL =>
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (L.equivMapOfInjective K0.subtype K0.subtype_injective) hL
  refine ⟨K'.map K0.subtype, ⟨Subgroup.map_subtype_le K', hmodel_map K' hK', ?_⟩, ?_⟩
  · intro x hx
    exact ⟨⟨x, (Subgroup.mem_inf.mp hx).2⟩, hTK' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · rintro K ⟨hKK0, hK, hAK⟩
    have hKsub : StatedClassicalModel (K.subgroupOf K0) .PSL 2 2 2 :=
      CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hKK0).symm hK
    have hTK : (A ⊓ K0).subgroupOf K0 ≤ K.subgroupOf K0 := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hAK (Subgroup.mem_subgroupOf.mp hx))
    have := huniq _ ⟨hKsub, hTK⟩
    rw [← this, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKK0]

theorem kOfWellDefined_of_mem_partTwoF [Finite G] {A : Subgroup G}
    (hA : A ∈ CFSG.RankThree.LocalRank.partTwoF G) : KOfWellDefined A :=
  kOfWellDefined_of_maximal hA.1 hA.2.1

theorem kOfWellDefined_of_sec21Std [Finite G] {A : Subgroup G} (h : Sec21Std G A) :
    KOfWellDefined A :=
  kOfWellDefined_of_mem_partTwoF h.mem_S.1

end CFSG.RankThree.PartTwo.KFacts.KS21
