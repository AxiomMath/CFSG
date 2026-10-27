module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_comm_eq_self_or_bot {W : Type} [CommGroup W]
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hN : L.map (MulAut.conj t).toMonoidHom = L) :
    ⁅L, Subgroup.zpowers t⁆ = L ∨ ⁅L, Subgroup.zpowers t⁆ = ⊥ := by
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hN
  have hzN : Subgroup.zpowers t ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr htN
  have hNL : ⁅L, Subgroup.zpowers t⁆ ≤ L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hzN
  have hnorm : (⁅L, Subgroup.zpowers t⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr
      (Subgroup.normalizer_commutator_ge_left L (Subgroup.zpowers t))
  haveI : (⁅L, Subgroup.zpowers t⁆.subgroupOf L).Normal := hnorm
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hL.2.2
      (⁅L, Subgroup.zpowers t⁆.subgroupOf L) with hcenter | htop
  · right
    have hdouble : ⁅⁅L, Subgroup.zpowers t⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxL : x ∈ L := hNL hx
      have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L :=
        hcenter ((Subgroup.mem_subgroupOf (H := ⁅L, Subgroup.zpowers t⁆)
          (K := L) (h := (⟨x, hxL⟩ : ↥L))).mpr hx)
      have hc := Subgroup.mem_center_iff.mp hxcenter (⟨y, hy⟩ : ↥L)
      exact congrArg Subtype.val hc
    haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
    exact CFSG.ComponentClassification.Quasisimple.perfect_double_commutator L
      (Subgroup.zpowers t) hdouble
  · left
    exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.mp htop)

theorem exists_component_comm (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} (S : Std136 Y t)
    (hF : ∀ p : ℕ, p.Prime → ⁅pCoreOf p Y, Subgroup.zpowers t⁆ = ⊥)
    (hfix : ∀ K : Subgroup (MulAut W), IsComponentOf K Y →
      K.map (MulAut.conj t).toMonoidHom = K) :
    ∃ L : Subgroup (MulAut W), IsComponentOf L Y ∧ ⁅L, Subgroup.zpowers t⁆ = L := by
  classical
  let t' : ↥Y := ⟨t, S.tY⟩
  have hcomp : ∀ L : Subgroup (MulAut W), IsComponentOf L Y →
      ⁅L, Subgroup.zpowers t⁆ = L ∨ ⁅L, Subgroup.zpowers t⁆ = ⊥ :=
    fun L hL => w1369_comm_eq_self_or_bot hL (hfix L hL)
  by_contra hno
  have hno' : ∀ L : Subgroup (MulAut W), IsComponentOf L Y →
      ⁅L, Subgroup.zpowers t⁆ ≠ L :=
    fun L hL heq => hno ⟨L, hL, heq⟩
  have hbot : ∀ L : Subgroup (MulAut W), IsComponentOf L Y →
      ⁅L, Subgroup.zpowers t⁆ = ⊥ :=
    fun L hL => (hcomp L hL).resolve_left (hno' L hL)
  have hE_le : Subgroup.zpowers t' ≤
      Subgroup.centralizer (genFittingLayer ↥Y : Set ↥Y) := by
    rw [genFittingLayer.eq_sSup]
    refine Subgroup.le_centralizer_iff.mp (sSup_le ?_)
    intro C hC
    let L : Subgroup (MulAut W) := C.map Y.subtype
    have hLY : L ≤ Y := Subgroup.map_subtype_le C
    have hL : IsComponentOf L Y := by
      refine (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hLY).mpr ?_
      have hCL : L.subgroupOf Y = C :=
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective C
      rw [hCL]
      exact hC
    have hcentL : L ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hbot L hL)
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro c hc
    apply Subtype.ext
    have hcL : (c : MulAut W) ∈ L := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hcentL hcL)) t
      (Subgroup.mem_zpowers t)
    exact hcomm.symm
  have hF_le : Subgroup.zpowers t' ≤
      Subgroup.centralizer (genFittingFitting ↥Y : Set ↥Y) := by
    rw [show genFittingFitting ↥Y = CFSG.fittingSubgroup ↥Y from rfl,
      CFSG.fitting_eq_sup_pCore]
    refine Subgroup.le_centralizer_iff.mp (iSup_le ?_)
    intro q
    refine Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have hxval : (x : MulAut W) ∈ pCoreOf q.1.1 Y :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have hcomm := (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hF q.1.1 hqprime)) hxval))
      t (Subgroup.mem_zpowers t)
    exact hcomm.symm
  have hFE_le : Subgroup.zpowers t' ≤
      Subgroup.centralizer (genFittingFStar ↥Y : Set ↥Y) := by
    rw [genFittingFStar.eq_sup]
    exact Subgroup.le_centralizer_iff.mp
      (sup_le (Subgroup.le_centralizer_iff.mp hF_le)
        (Subgroup.le_centralizer_iff.mp hE_le))
  have hcent : t' ∈ Subgroup.centralizer (genFittingFStar ↥Y : Set ↥Y) :=
    hFE_le (Subgroup.mem_zpowers t')
  have hBender : Subgroup.centralizer (genFittingFStar ↥Y : Set ↥Y) ≤
      genFittingFStar ↥Y :=
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le ↥Y
  let N : Subgroup ↥Y := Subgroup.centralizer (genFittingFStar ↥Y : Set ↥Y)
  haveI : (genFittingFStar ↥Y).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal ↥Y
  have hNnormal : N.Normal := inferInstance
  have hcommN : ∀ a b : N, a * b = b * a := fun a b =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp b.2) (a : ↥Y) (hBender a.2))
  let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hcommN }
  have hNnil : Group.IsNilpotent N := inferInstance
  have ht'N : t' ∈ N := hcent
  let a : N := ⟨t', ht'N⟩
  have ht'ord : orderOf t' = 2 := (Subgroup.orderOf_coe t').symm.trans S.t2
  have haord : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans ht'ord
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0 : IsPGroup 2 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, haord, pow_one]
  obtain ⟨Q, hP0Q⟩ := IsPGroup.exists_le_sylow hP0
  have haQ : a ∈ Q := hP0Q (Subgroup.mem_zpowers a)
  have ht'_pCore : t' ∈ CFSG.pCore 2 ↥Y :=
    Sylow.map_le_pCore hNnormal hNnil 2 Q (Subgroup.mem_map.mpr ⟨a, haQ, rfl⟩)
  have ht_pCoreOf : t ∈ pCoreOf 2 Y :=
    Subgroup.mem_map.mpr ⟨t', ht'_pCore, rfl⟩
  have hle : pCoreOf 2 Y ≤ Y := Subgroup.map_subtype_le _
  have hnorm : ((pCoreOf 2 Y).subgroupOf Y).Normal := by
    have h1 : (pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective (CFSG.pCore 2 ↥Y)
    rw [h1]
    exact CFSG.pCore_normal
  have h2 : IsPGroup 2 (pCoreOf 2 Y) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype
  have hpbot : pCoreOf 2 Y = ⊥ := S.o2 (pCoreOf 2 Y) hle hnorm h2
  have ht1 : t = 1 := Subgroup.mem_bot.mp (hpbot ▸ ht_pCoreOf)
  exact absurd (by simpa [ht1] using S.t2 : (1 : ℕ) = 2) (by norm_num)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
