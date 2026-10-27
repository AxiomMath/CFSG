module

public import CFSG.Sporadic.Th.IndexNineAlt
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThAutModel
public import CFSG.GH74.KGroups.Generic3
public import CFSG.Sporadic.Th.Recog.Core
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Sporadic.Th

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique

theorem orderOf_max3_z :
    orderOf Max3.z = 2 := by
  apply orderOf_eq_prime
  · simpa [pow_two] using Max3.z_mul_self
  · exact Max3.z_ne_one

noncomputable def thPi :
    ↥Max3.M →* IndexNineA9.Alt :=
  Max3.kappa.toMonoidHom.comp Max3.AltQuot.proj

theorem thPi_surjective :
    Function.Surjective thPi :=
  Max3.kappa.surjective.comp Max3.AltQuot.proj_surjective

theorem thPi_ker :
    thPi.ker = Max3.Q.subgroupOf Max3.M := by
  ext g
  have h1 : thPi g = Max3.kappa (Max3.AltQuot.proj g) := rfl
  rw [MonoidHom.mem_ker, h1, ← map_one Max3.kappa, Max3.kappa.injective.eq_iff,
    Max3.AltQuot.proj_eq_one_iff]
  rfl

theorem card_thPi_ker :
    Nat.card thPi.ker = 512 := by
  rw [thPi_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Max3.Q_le_M).toEquiv, Max3.card_Q]

theorem isPGroup_thPi_ker :
    IsPGroup 2 thPi.ker := by
  rw [thPi_ker]
  exact Max3.AltQuot.isPGroup_Q_subgroupOf_M

noncomputable def thU :
    Subgroup ↥J :=
  (IndexNineA9.Ubar.comap thPi).map Max3.M.subtype

theorem thU_le_M :
    thU ≤ Max3.M := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem card_thU :
    Nat.card thU = 32768 := by
  rw [thU, Subgroup.card_map_of_injective (f := Max3.M.subtype) Subtype.val_injective,
    CFSG.GH74.KGroups.card_comap_of_surjective thPi thPi_surjective,
    IndexNineA9.card_Ubar, card_thPi_ker]

theorem isPGroup_thU :
    IsPGroup 2 thU :=
  IsPGroup.of_card (n := 15) (by rw [card_thU]; norm_num)

theorem isSylowTwoOf_thU :
    CFSG.QuasithinUnique.IsSylowTwoOf thU ⊤ := by
  refine ⟨le_top, isPGroup_thU, ?_⟩
  have hc : Nat.card (thU.subgroupOf ⊤) = Nat.card thU :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : thU ≤ ⊤)).toEquiv
  have hmul : Nat.card (thU.subgroupOf ⊤) * (thU.subgroupOf ⊤).index =
      Nat.card (⊤ : Subgroup ↥J) := Subgroup.card_mul_index (H := thU.subgroupOf ⊤)
  rw [Subgroup.card_top, hc, card_thU, Max3.natCard_J] at hmul
  have hidx : (thU.subgroupOf ⊤).index = 2769346432125 := by
    refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 32768) ?_
    rw [hmul]
  norm_num [hidx]

theorem Q_le_thU :
    Max3.Q ≤ thU := by
  intro q hq
  have hqM : q ∈ Max3.M := Max3.Q_le_M hq
  refine ⟨⟨q, hqM⟩, ?_, rfl⟩
  change thPi ⟨q, hqM⟩ ∈ IndexNineA9.Ubar
  have h1 : thPi ⟨q, hqM⟩ = Max3.kappa (Max3.AltQuot.proj ⟨q, hqM⟩) := rfl
  rw [h1]
  have hq' : (⟨q, hqM⟩ : ↥Max3.M) ∈ Max3.Q.subgroupOf Max3.M := hq
  have h2 : Max3.kappa (Max3.AltQuot.proj ⟨q, hqM⟩) = 1 := by
    rw [(Max3.AltQuot.proj_eq_one_iff (g := ⟨q, hqM⟩)).mpr hq', map_one]
  rw [h2]
  exact IndexNineA9.U.one_mem

theorem z_mem_thU :
    Max3.z ∈ thU :=
  Q_le_thU Max3.z_mem_Q

theorem centralizer_thU :
    ∀ x ∈ thU, (∀ y ∈ thU, x * y = y * x) → x = 1 ∨ x = Max3.z := by
  intro x hx hxc
  have hxM : x ∈ Max3.M := thU_le_M hx
  have hxQ : x ∈ Subgroup.centralizer (Max3.Q : Set ↥J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hxc q (Q_le_thU hq)).symm
  have hxcen : x ∈ Subgroup.centralizer (Max3.Q : Set ↥J) ⊓ Max3.M := ⟨hxQ, hxM⟩
  rw [Max3.centralizer_Q_inf_M] at hxcen
  exact CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.eq_one_or_eq_of_mem_zpowers
    orderOf_max3_z hxcen

theorem normalizer_thU_le_M :
    Subgroup.normalizer (thU : Set ↥J) ≤ Max3.M := by
  have hzc : ∀ y ∈ thU, Max3.z * y = y * Max3.z := by
    intro y hy
    exact (Max3.commute_z_of_mem_M (thU_le_M hy)).eq
  have h := CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.normalizer_le_centralizer_of_center
    (R := thU) (z := Max3.z) z_mem_thU Max3.z_ne_one hzc centralizer_thU
  rwa [CFSG.Sporadic.Th.Recog.centralizer_z_eq_M] at h

theorem th_mulAut_inner :
    ∀ α : MulAut ↥J, ∃ g : ↥J, ∀ x : ↥J, α x = g * x * g⁻¹ := by
  intro α
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Dickson.I271.th_allInner α
  refine ⟨g, fun x => ?_⟩
  rw [hg]
  rfl

theorem th_index_nine_package :
    IndexNinePackage ↥J := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Dickson.I271.th_finite
  exact indexNinePackage_of_quotient (Γ := ↥J) (Δ := IndexNineA9.Alt)
    th_mulAut_inner isSylowTwoOf_thU normalizer_thU_le_M thPi thPi_surjective
    isPGroup_thPi_ker IndexNineA9.innerIndexNinePackage_A9

end CFSG.Sporadic.Th
