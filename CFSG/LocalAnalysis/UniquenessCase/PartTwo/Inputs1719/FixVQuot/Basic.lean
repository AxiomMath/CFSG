module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixMBound
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Local

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]
variable {Y L : Subgroup (MulAut W)}

theorem iSup_conjSet_eq_self_of_normal {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) : (⨆ X ∈ conjSet L Y, X) = L :=
  iSup_conjSet_eq_of_le_normalizer ((normal_subgroupOf_iff_le_normalizer hLY).mp hLn)

theorem le_stabSub_fixV_of_subgroupOf_normal {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) : Y ≤ stabSub (fixV L) := by
  refine le_stabSub_fixV fun y hy l hl => ?_
  have h := hLn.conj_mem (⟨l, hLY hl⟩ : ↥Y) hl ⟨y, hy⟩
  simpa using (Subgroup.mem_subgroupOf.mp h)

noncomputable def autQuotEquiv (hW : ∀ w : W, w ^ 2 = 1) (hO : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal)
    {X : Subgroup (MulAut W)} (hXY : X ≤ Y) : ↥X ≃* ↥(autQuot X (fixV L)) := by
  have hYstab : Y ≤ stabSub (fixV L) := le_stabSub_fixV_of_subgroupOf_normal hL.1 hLn
  have hXstab : X ≤ stabSub (fixV L) := hXY.trans hYstab
  have hH : L = ⨆ X ∈ conjSet L Y, X := (iSup_conjSet_eq_self_of_normal hL.1 hLn).symm
  let f : ↥X →* ↥(autQuot X (fixV L)) :=
    ((quotHom (fixV L)).comp (Subgroup.inclusion hXstab)).codRestrict (autQuot X (fixV L))
      fun x => mem_autQuot.mpr ⟨Subgroup.inclusion hXstab x, x.2, rfl⟩
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hquot : quotHom (fixV L) ⟨x.1, hXstab x.2⟩ = 1 := congrArg Subtype.val hx
    have hx1 : (x : MulAut W) = 1 := by
      refine eq_one_of_mem_fixV_quot hW hO hB hL hH (hXY x.2) fun w => ?_
      have h := congrArg (fun φ : MulAut (W ⧸ fixV L) => φ (QuotientGroup.mk w)) hquot
      simp only [quotHom_mk, MulAut.one_apply] at h
      exact (mk_eq_mk_iff (U := fixV L) ((x : MulAut W) w) w).mp h
    exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
  · rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    exact ⟨⟨g.1, hg⟩, Subtype.ext rfl⟩

theorem autQuot_subgroupOf_normal (hW : ∀ w : W, w ^ 2 = 1) (hO : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal) :
    ((autQuot L (fixV L)).subgroupOf (autQuot Y (fixV L))).Normal := by
  have hYstab : Y ≤ stabSub (fixV L) := le_stabSub_fixV_of_subgroupOf_normal hL.1 hLn
  let f : ↥Y →* ↥(autQuot Y (fixV L)) :=
    ((quotHom (fixV L)).comp (Subgroup.inclusion hYstab)).codRestrict (autQuot Y (fixV L))
      fun y => mem_autQuot.mpr ⟨Subgroup.inclusion hYstab y, y.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    exact ⟨⟨g.1, hg⟩, Subtype.ext rfl⟩
  have hmap : (L.subgroupOf Y).map f = (autQuot L (fixV L)).subgroupOf (autQuot Y (fixV L)) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact mem_autQuot.mpr ⟨⟨l.1, hYstab l.2⟩, hl, rfl⟩
    · intro hy
      obtain ⟨g, hg, hg'⟩ := mem_autQuot.mp (Subgroup.mem_subgroupOf.mp hy)
      refine ⟨⟨g.1, hL.1 hg⟩, hg, ?_⟩
      dsimp only [f]
      exact Subtype.ext hg'
  rw [← hmap]
  exact hLn.map f hf

theorem isComponentOf_autQuot (hW : ∀ w : W, w ^ 2 = 1) (hO : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal) :
    IsComponentOf (autQuot L (fixV L)) (autQuot Y (fixV L)) := by
  have hYstab : Y ≤ stabSub (fixV L) := le_stabSub_fixV_of_subgroupOf_normal hL.1 hLn
  have hH : L = ⨆ X ∈ conjSet L Y, X := (iSup_conjSet_eq_self_of_normal hL.1 hLn).symm
  have hcomp : IsComponentOf (L.subgroupOf (stabSub (fixV L))) (Y.subgroupOf (stabSub (fixV L))) :=
    B15P4.isComponentOf_subgroupOf (stabSub (fixV L)) hL hYstab
  have hnot : ¬ L.subgroupOf (stabSub (fixV L)) ≤ (quotHom (fixV L)).ker := by
    intro hle
    have hLbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      have hmem : (⟨l, hYstab (hL.1 hl)⟩ : ↥(stabSub (fixV L))) ∈
          L.subgroupOf (stabSub (fixV L)) := hl
      have hk : quotHom (fixV L) ⟨l, hYstab (hL.1 hl)⟩ = 1 := by
        have h := hle hmem
        rwa [MonoidHom.mem_ker] at h
      have hl1 : l = 1 := by
        refine eq_one_of_mem_fixV_quot hW hO hB hL hH (hL.1 hl) fun w => ?_
        have h := congrArg (fun φ : MulAut (W ⧸ fixV L) => φ (QuotientGroup.mk w)) hk
        simp only [quotHom_mk, MulAut.one_apply] at h
        exact (mk_eq_mk_iff (U := fixV L) (l w) w).mp h
      simpa using hl1
    exact B15P4.ne_bot_of_isComponentOf hL hLbot
  have := B15P4.isComponentOf_map_hom (quotHom (fixV L)) hcomp hnot
  simpa only [autQuot] using this

theorem map_mem_irrSet_autQuot (hW : ∀ w : W, w ^ 2 = 1) (hO : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal)
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    I.map (QuotientGroup.mk' (fixV L)) ∈ irrSet (autQuot L (fixV L)) ∧
      I.map (QuotientGroup.mk' (fixV L)) ⊓ fixV (autQuot L (fixV L)) = ⊥ := by
  have hH : L = ⨆ X ∈ conjSet L Y, X := (iSup_conjSet_eq_self_of_normal hL.1 hLn).symm
  have hLfix : L ≤ stabSub (fixV L) := RonanF918.le_stabSub_fixV L
  have hfix : fixV (autQuot L (fixV L)) = ⊥ := fixV_autQuot_eq_bot hL hH
  obtain ⟨hstable, hmax⟩ := map_mk_stable_irr (H := L) hLfix hI
  have hcomm : commSub (I.map (QuotientGroup.mk' (fixV L))) (autQuot L (fixV L)) =
      I.map (QuotientGroup.mk' (fixV L)) := by
    rw [commSub_map_mk hLfix I, hI.1]
  have hne : I.map (QuotientGroup.mk' (fixV L)) ≠ ⊥ := by
    intro hbot
    have hle : I ≤ fixV L := by
      rw [Subgroup.map_eq_bot_iff] at hbot
      simpa [QuotientGroup.ker_mk'] using hbot
    have hIC : I ⊓ fixV L = I := inf_eq_left.mpr hle
    have hlt := hI.2.1
    rw [hIC] at hlt
    exact (lt_irrefl I) hlt
  refine ⟨⟨hcomm, ?_⟩, by rw [hfix, inf_bot_eq]⟩
  rw [hfix, inf_bot_eq]
  exact ⟨bot_lt_iff_ne_bot.mpr hne, hstable,
    fun x _ u hu => by
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one],
    fun J hJ _ hJI => hmax J hJ hJI⟩

theorem aParam_autSub_autQuot_bot_top (Y : Subgroup (MulAut W)) :
    E3.aParam (autSub (autQuot Y (⊥ : Subgroup W)) ⊤) = E3.aParam Y := by
  let e : W ≃* W ⧸ (⊥ : Subgroup W) := (QuotientGroup.quotientBot (G := W)).symm
  have he : ∀ v : W, e v = (v : W ⧸ (⊥ : Subgroup W)) := QuotientGroup.quotientBot_symm_apply
  have hquot : ∀ g : stabSub (⊥ : Subgroup W),
      H.congrHom e (g : MulAut W) = quotHom (⊥ : Subgroup W) g := by
    intro g
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => rw [H.congrHom_apply, quotHom_mk, ← he v, e.symm_apply_apply, he]
  have hY : autQuot Y (⊥ : Subgroup W) = Y.map (H.congrHom e) := by
    ext φ
    rw [mem_autQuot, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, hquot g⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, B5.Ln.stabSub_bot_le Y hy⟩, hy, (hquot ⟨y, _⟩).symm⟩
  have hU : ∀ v, v ∈ (⊤ : Subgroup W) ↔ e v ∈ (⊤ : Subgroup (W ⧸ ⊥)) := fun v => by simp
  rw [hY, H.LU.autSub_map e Y hU, H.aParam_map_congrHom,
    H13.autSub_top_eq_map, H.aParam_map_congrHom]

theorem commV_eq_or_two_mul_rk_le (hW : ∀ w : W, w ^ 2 = 1) (hO : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal)
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    commV (autQuot L (fixV L)) = I.map (QuotientGroup.mk' (fixV L)) ∨
      2 * rk ↥(I.map (QuotientGroup.mk' (fixV L))) ≤ rk ↥(commV (autQuot L (fixV L))) := by
  have hH : L = ⨆ X ∈ conjSet L Y, X := (iSup_conjSet_eq_self_of_normal hL.1 hLn).symm
  set S : Set (Subgroup W) :=
    {U : Subgroup W | U ∈ irrSet L ∧ ¬ commSub U L ≤ fixV L} with hS
  have hI' : I ∈ S := by
    refine ⟨hI, ?_⟩
    intro hle
    have hIC : I ≤ fixV L := by rwa [hI.1] at hle
    have hinf : I ⊓ fixV L = I := inf_eq_left.mpr hIC
    have hlt := hI.2.1
    rw [hinf] at hlt
    exact (lt_irrefl I) hlt
  have hcommV := commV_autQuot_eq_iSup hW hO hB hL hH
  by_cases hEq : commV (autQuot L (fixV L)) = I.map (QuotientGroup.mk' (fixV L))
  · exact Or.inl hEq
  · right
    have hex : ∃ U ∈ S, ¬ U.map (QuotientGroup.mk' (fixV L)) ≤
        I.map (QuotientGroup.mk' (fixV L)) := by
      by_contra h
      push Not at h
      apply hEq
      rw [hcommV]
      exact le_antisymm (iSup₂_le h) (le_iSup₂_of_le I hI' le_rfl)
    obtain ⟨U, hU, hUnotle⟩ := hex
    have hIle : I.map (QuotientGroup.mk' (fixV L)) ≤ commV (autQuot L (fixV L)) := by
      rw [hcommV]
      exact le_iSup₂_of_le I hI' le_rfl
    have hUle : U.map (QuotientGroup.mk' (fixV L)) ≤ commV (autQuot L (fixV L)) := by
      rw [hcommV]
      exact le_iSup₂_of_le U hU le_rfl
    have hne : I ⊔ fixV L ≠ U ⊔ fixV L := by
      intro h
      apply hUnotle
      have hmap : I.map (QuotientGroup.mk' (fixV L)) = U.map (QuotientGroup.mk' (fixV L)) := by
        rw [show I.map (QuotientGroup.mk' (fixV L)) =
              (I ⊔ fixV L).map (QuotientGroup.mk' (fixV L)) by
            rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq],
          h,
          show (U ⊔ fixV L).map (QuotientGroup.mk' (fixV L)) =
              U.map (QuotientGroup.mk' (fixV L)) by
            rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]]
      exact hmap.ge
    have hinf : U.map (QuotientGroup.mk' (fixV L)) ⊓ I.map (QuotientGroup.mk' (fixV L)) = ⊥ :=
      map_mk_inf_eq_bot hL hH hI hU.1 hne
    have hrk : rk ↥(U.map (QuotientGroup.mk' (fixV L))) =
        rk ↥(I.map (QuotientGroup.mk' (fixV L))) := rk_map_mk_eq hW hO hB hL hH hU.1 hI
    have hsup : rk ↥(I.map (QuotientGroup.mk' (fixV L)) ⊔ U.map (QuotientGroup.mk' (fixV L))) =
        2 * rk ↥(I.map (QuotientGroup.mk' (fixV L))) := by
      have h := rk_sup_add_rk_inf (I.map (QuotientGroup.mk' (fixV L)))
        (U.map (QuotientGroup.mk' (fixV L)))
      rw [inf_comm, hinf, rk_bot, add_zero, hrk] at h
      omega
    calc 2 * rk ↥(I.map (QuotientGroup.mk' (fixV L))) =
        rk ↥(I.map (QuotientGroup.mk' (fixV L)) ⊔ U.map (QuotientGroup.mk' (fixV L))) :=
          hsup.symm
      _ ≤ rk ↥(commV (autQuot L (fixV L))) :=
          rk_mono (sup_le hIle hUle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot
