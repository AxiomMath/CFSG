module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaSymp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139FormsA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139FormsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139McL
import CFSG.Quasithin.Background.G64Realize
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_index_sup_zpowers_le_two {A : Type*} [Group A] [Finite A] {K : Subgroup A}
    {e : A} (he2 : e ^ 2 = 1) (hN : Subgroup.zpowers e ≤ Subgroup.normalizer (K : Set A)) :
    (K.subgroupOf (K ⊔ Subgroup.zpowers e)).index ≤ 2 := by
  classical
  have hNsub : (K.subgroupOf (K ⊔ Subgroup.zpowers e)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hN)
  have htop : (K.subgroupOf (K ⊔ Subgroup.zpowers e)) ⊔
      (Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : K ≤ K ⊔ Subgroup.zpowers e)
      (le_sup_right : Subgroup.zpowers e ≤ K ⊔ Subgroup.zpowers e), Subgroup.subgroupOf_self]
  have hindex_eq : (K.subgroupOf (K ⊔ Subgroup.zpowers e)).index =
      (K.subgroupOf (K ⊔ Subgroup.zpowers e)).relIndex
        ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) := by
    rw [← Subgroup.relIndex_top_right (H := K.subgroupOf (K ⊔ Subgroup.zpowers e))]
    rw [← htop, Subgroup.relIndex_sup_left]
  rw [hindex_eq]
  have hbound : (K.subgroupOf (K ⊔ Subgroup.zpowers e)).relIndex
      ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) ≤
      Nat.card ↥((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) := by
    have h := Subgroup.relIndex_mul_card
      (K.subgroupOf (K ⊔ Subgroup.zpowers e))
      ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e))
    have hpos : 0 < Nat.card ↥((K.subgroupOf (K ⊔ Subgroup.zpowers e)) ⊓
        ((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e))) := Nat.card_pos
    nlinarith [h, hpos]
  refine hbound.trans ?_
  have hcard_le : Nat.card ↥((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) ≤
      Nat.card ↥(Subgroup.zpowers e) := by
    refine Nat.card_le_card_of_injective
      (fun z : ↥((Subgroup.zpowers e).subgroupOf (K ⊔ Subgroup.zpowers e)) =>
        (⟨((z.1 : ↥(K ⊔ Subgroup.zpowers e)) : A), z.2⟩ : ↥(Subgroup.zpowers e))) ?_
    intro z w h
    have h' : (z.1 : A) = (w.1 : A) :=
      congrArg (fun t : ↥(Subgroup.zpowers e) => (t : A)) h
    exact Subtype.ext (Subtype.ext h')
  have hcard_e : Nat.card ↥(Subgroup.zpowers e) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr he2)
  exact hcard_le.trans hcard_e

theorem beta_core {M : Type} [CommGroup M] [Finite M]
    (hM2 : ∀ m : M, m ^ 2 = 1) {K D : Subgroup (MulAut M)} (hKq : IsQuasisimple ↥K)
    (hKirr : IsIrrOn K ⊤ ⊥) (hDnorm : ∀ e ∈ D, K.map (MulAut.conj e).toMonoidHom = K)
    (hDel : IsElemAbelian2 D) (hD4 : 4 ≤ Nat.card D) (A : Subgroup M) (hA : rkIdx A = 1)
    (hDtv : ∀ e ∈ D, e ≠ 1 → fixV (Subgroup.zpowers e) = A ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 1)
    (hKe : ∀ e ∈ D, e ≠ 1 → ⁅K, Subgroup.zpowers e⁆ = K) (hn3 : 3 ≤ rk M) : K = ⊤ := by
  classical
  have hDne : D ≠ ⊥ := fun h => by rw [h] at hD4; simp at hD4
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have heD : (e : MulAut M) ∈ D := e.2
  have he1' : (e : MulAut M) ≠ 1 := fun h => he1 (Subtype.ext h)
  have he2 : (e : MulAut M) ^ 2 = 1 := hDel.2 (e : MulAut M) heD
  set J : Subgroup (MulAut M) := K ⊔ Subgroup.zpowers (e : MulAut M) with hJdef
  have hKleJ : K ≤ J := le_sup_left
  have heJ : (e : MulAut M) ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers (e : MulAut M))
  have heN : (e : MulAut M) ∈ Subgroup.normalizer (K : Set (MulAut M)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hDnorm (e : MulAut M) heD)
  have heNzp : Subgroup.zpowers (e : MulAut M) ≤
      Subgroup.normalizer (K : Set (MulAut M)) := Subgroup.zpowers_le.mpr heN
  have hJleN : J ≤ Subgroup.normalizer (K : Set (MulAut M)) :=
    sup_le Subgroup.le_normalizer heNzp
  have hNormal : (K.subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hJleN
  have hindex : (K.subgroupOf J).index ≤ 2 :=
    w1369_index_sup_zpowers_le_two he2 heNzp
  have hstabE : (e : MulAut M) ∈ stabSub (⊤ : Subgroup M) := by
    rw [mem_stabSub]
    intro u
    exact Iff.rfl
  have heTv : InducesTransvection (e : MulAut M) ⊤ :=
    ⟨hstabE, (hDtv (e : MulAut M) heD he1').2⟩
  let S : Set (MulAut M) := {t : MulAut M | t ∈ J ∧ InducesTransvection t ⊤}
  have hJgen' : J = Subgroup.closure S := by
    apply le_antisymm
    · rw [hJdef]
      refine sup_le ?_ ?_
      · rw [← hKe (e : MulAut M) heD he1']
        refine Subgroup.commutator_le.mpr ?_
        intro k hk y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [zpow_eq_zpow_emod j (show (e : MulAut M) ^ (2 : ℤ) = 1 by simpa using he2)]
        rcases Int.emod_two_eq_zero_or_one j with h0 | h1
        · rw [h0, zpow_zero, commutatorElement_one_right]
          exact Subgroup.one_mem _
        · rw [h1, zpow_one]
          have heq : ⁅k, (e : MulAut M)⁆ =
              (k * (e : MulAut M) * k⁻¹) * (e : MulAut M)⁻¹ := by
            rw [commutatorElement_def]
          rw [heq]
          refine Subgroup.mul_mem _ ?_ ?_
          · refine Subgroup.subset_closure (show k * (e : MulAut M) * k⁻¹ ∈ S from ?_)
            refine ⟨?_, ?_⟩
            · exact J.mul_mem (J.mul_mem (hKleJ hk) heJ) (J.inv_mem (hKleJ hk))
            · have hmap : (⊤ : Subgroup M).map ((k⁻¹).toMonoidHom) = ⊤ :=
                Subgroup.map_top_of_surjective _ (k⁻¹).surjective
              have hL : InducesTransvection (e : MulAut M) ((⊤ : Subgroup M).map
                  ((k⁻¹).toMonoidHom)) := by
                rw [hmap]; exact heTv
              have h := (s16_Mod_inducesTransvection_conj k⁻¹ (e : MulAut M)
                (⊤ : Subgroup M)).mp hL
              simpa using h
          · refine Subgroup.inv_mem _ ?_
            refine Subgroup.subset_closure (show (e : MulAut M) ∈ S from ?_)
            exact ⟨heJ, heTv⟩
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (show (e : MulAut M) ∈ S from ⟨heJ, heTv⟩)
    · rw [Subgroup.closure_le]
      exact fun t ht => ht.1
  have hJgen : J = Subgroup.closure {t : MulAut M | t ∈ J ∧ InducesTransvection t ⊤} := by
    simpa [S] using hJgen'
  have hJirr : IsIrrOn J ⊤ ⊥ := by
    refine ⟨hKirr.1, ?_, ?_, ?_⟩
    · intro x _ u _
      exact Subgroup.mem_top (x u)
    · intro x _ u hu
      rw [Subgroup.mem_bot.mp hu]
      exact Subgroup.mem_bot.mpr (map_one x)
    · intro J' hJ' _ _
      exact hKirr.2.2.2 J' (fun x hx u hu => hJ' x (hKleJ hx) u hu) bot_le le_top
  rcases mcLaughlin1969_holds M hM2 J K le_sup_left hNormal hindex hKq hJirr hJgen with
    ⟨m, _, hnat⟩ | ⟨msp, _, hsp⟩ | ⟨mop, _, hom⟩ | ⟨mom, _, hom'⟩ | ⟨ma, _, halt⟩
  · exact G64.BinaryNaturalSL.eq_top hnat
  · exact absurd (beta_core_no_sympform hM2 hKq hKirr hDnorm hDel hD4 A hA hDtv hn3
      (hasSympForm_of_natSpn hsp)) (by simp)
  · exact absurd (beta_core_no_sympform hM2 hKq hKirr hDnorm hDel hD4 A hA hDtv hn3
      (hasSympForm_of_natOmegaPlus hom)) (by simp)
  · exact absurd (beta_core_no_sympform hM2 hKq hKirr hDnorm hDel hD4 A hA hDtv hn3
      (hasSympForm_of_natOmegaMinus hom')) (by simp)
  · exact absurd (beta_core_no_sympform hM2 hKq hKirr hDnorm hDel hD4 A hA hDtv hn3
      (hasSympForm_of_alternatingNatural halt)) (by simp)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
