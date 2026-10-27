module

public import CFSG.Quasithin.Vol2.Ch10SecA1012Five
public import CFSG.Quasithin.Background.InternalSecFFB
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuVM_le_sup_of_eq (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) (hVV : fsuV T I = fsuVM T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuVM T L I ≤ fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t := by
  have hI : I ≤ ⁅fsuVM T L I, fsuL0 T L⁆ := by
    have h := hyp.fsu.irrPlus.2.2.2.1
    calc I = ⁅I, conjClosure L T⁆ := h.symm
      _ ≤ ⁅fsuVM T L I, fsuL0 T L⁆ := Subgroup.commutator_mono (le_fsuVM T L I) le_rfl
  have hTN : T ≤ Subgroup.normalizer ((⁅fsuVM T L I, fsuL0 T L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator (le_normalizer_fsuVM T L I) (le_fsuM T L)
  have hV : fsuVM T L I ≤ ⁅fsuVM T L I, fsuL0 T L⁆ := by
    have h : fsuV T I ≤ ⁅fsuVM T L I, fsuL0 T L⁆ := conjClosure_le fun s hs i hi =>
      (Subgroup.mem_normalizer_iff.mp (hTN hs) i).mp (hI hi)
    exact hVV ▸ h
  have hsup : ⁅fsuVM T L I, fsuL0 T L⁆ = fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    rw [fsuL0_eq_sup h37 h38 hyp ht htn]
    exact commutator_sup_left_of_le (fsuVM_le_fsuM hyp.fsu)
      ((le_fsuL0 T L).trans (fsuL0_le_fsuM T L))
      ((conjugate_le_fsuL0 ht).trans (fsuL0_le_fsuM T L)) (fsuM_le_normalizer_fsuVM T L I)
  rw [conjugate_commutator_fsuVM (le_fsuM T L ht), ← hsup]
  exact hV

theorem autOn_conjugate_ne (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    autOn (CFSG.conjugate L t) (fsuVM T L I) ≠ autOn L (fsuVM T L I) := by
  intro h1
  have := (isElemAbelian_fsuVM hyp).1
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLtV : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (conjugate_le_fsuL0 ht).trans (fsuL0_le_normalizer_fsuVM T L I)
  have h2 := congrArg commV h1
  rw [commV_autOn_eq hLtV, commV_autOn_eq hLV,
    ← conjugate_commutator_fsuVM (le_fsuM T L ht)] at h2
  apply fsuUL_ne_conjugate h37 h38 hyp ht htn
  have hUV : fsuUL T L I ≤ fsuVM T L I :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hUtV : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
    have h := conjugate_mono hUV t
    rwa [conjugate_fsuVM (le_fsuM T L ht)] at h
  have h2' : (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) =
      (fsuUL T L I).subgroupOf (fsuVM T L I) := h2
  rw [← Subgroup.map_subgroupOf_eq_of_le hUtV, h2', Subgroup.map_subgroupOf_eq_of_le hUV]

theorem mem_autOn_inf_normalizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {φ : MulAut ↥(fsuVM T L I)}
    (hφX : φ ∈ autOn (fsuL0 T L ⊔ T) (fsuVM T L I))
    (hφN : φ ∈ Subgroup.normalizer (autOn L (fsuVM T L I) : Set (MulAut ↥(fsuVM T L I)))) :
    φ ∈ autOn ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G)) (fsuVM T L I) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  obtain ⟨g, hgX, rfl⟩ := mem_autOn_iff'.mp hφX
  refine mem_autOn_iff'.mpr ⟨g, ⟨hgX, ?_⟩, rfl⟩
  have h0 : (conjAct (fsuVM T L I) g)⁻¹ ∈
      Subgroup.normalizer (autOn L (fsuVM T L I) : Set (MulAut ↥(fsuVM T L I))) :=
    (Subgroup.normalizer _).inv_mem hφN
  have h1 : autOn (CFSG.conjugate L g) (fsuVM T L I) = autOn L (fsuVM T L I) := by
    rw [autOn_conjugate g.2]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp h0
  have hgM : (g : G) ∈ fsuM T L := sup_le (fsuL0_le_fsuM T L) (le_fsuM T L) hgX
  rcases conjugate_eq_or h37 h38 hyp ht htn hgM with h | h
  · exact conjugate_eq_self_iff.mp h
  · rw [h] at h1
    exact absurd h1 (autOn_conjugate_ne h37 h38 hyp ht htn)

theorem not_isFFModule_of_case_five
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) (h322 : TmpL6_3_2_2_two)
    (h154 : AsB15Part4) (h51 : AsB51) (hyp : Ch10.Hyp10 G T L I)
    [IsMulCommutative ↥(fsuVM T L I)] (hVV : fsuV T I = fsuVM T L I)
    (hcard : Nat.card ↥I = 2 ^ 3) {s : G} (hsT : s ∈ T)
    (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hsO : s ∉ L ⊔ pCoreOf 2 (L ⊔ T ⊓ Subgroup.normalizer (L : Set G)))
    (hU : fsuUL T L I = I ⊔ CFSG.conjugate I s) (hinf : I ⊓ CFSG.conjugate I s = ⊥) :
    ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  have hel := isElemAbelian_fsuVM hyp
  have hVt : ∀ v : ↥(fsuVM T L I), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hel.2 _ v.2)
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  have htV : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) := le_normalizer_fsuVM T L I ht
  obtain ⟨hLI, hcommI, htop⟩ := facts_of_two h37 h38 hshape hyp hcard hU
  have hIU : I ≤ fsuUL T L I := hU ▸ le_sup_left
  have hIsU : CFSG.conjugate I s ≤ fsuUL T L I := hU ▸ le_sup_right
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hUab : IsMulCommutative ↥(fsuUL T L I) := isMulCommutative_of_le hUV
  have hIab : IsMulCommutative ↥I := isMulCommutative_of_le (hIU.trans hUV)
  have hI2 : ∀ w : ↥I, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hel.2 _ (hUV (hIU w.2)))
  have hU2 : ∀ v ∈ fsuUL T L I, v ^ 2 = 1 := fun v hv => hel.2 v (hUV hv)
  have hirrI := irr_of_autOn_eq_top hI2 hcard htop
  have hLIs : L ≤ Subgroup.normalizer (CFSG.conjugate I s : Set G) :=
    le_normalizer_conjugate_of hsN hLI
  have hirrIs : ∀ J : Subgroup G, J ≤ CFSG.conjugate I s →
      L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = CFSG.conjugate I s := by
    intro J hJ hLJ
    have hJ' : CFSG.conjugate J s⁻¹ ≤ I := by
      have h := conjugate_mono hJ s⁻¹
      rwa [conjugate_conjugate, mul_inv_cancel, conjugate_one] at h
    have hback : CFSG.conjugate (CFSG.conjugate J s⁻¹) s = J := by
      rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
    rcases hirrI _ hJ' (le_normalizer_conjugate_of ((Subgroup.normalizer _).inv_mem hsN) hLJ)
      with h | h
    · left
      rw [← hback, h]
      exact Subgroup.map_bot _
    · right
      rw [← hback, h]
  have hntI : ¬ I ≤ Subgroup.centralizer (L : Set G) := fun h =>
    hcommI (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  have hntIs : ¬ CFSG.conjugate I s ≤ Subgroup.centralizer (L : Set G) := by
    intro h
    apply hntI
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hsl : s⁻¹ * l * s ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hsN) l).mp hl
    have hsi : s⁻¹ * i * s ∈ CFSG.conjugate I s := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using hi
    have h1 := Subgroup.mem_centralizer_iff.mp (h hsi) _ hsl
    have h2 := congrArg (fun x => s * x * s⁻¹) h1
    simpa [mul_assoc] using h2
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hcommU : ⁅fsuUL T L I, L⁆ ≠ ⊥ := fun h =>
    hcommI (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hIU le_rfl))
  have hCU : L ⊓ Subgroup.centralizer (fsuUL T L I : Set G) = pCoreOf 2 L :=
    le_antisymm (inf_centralizer_le_pCoreOf h37 h38 hyp hLU hcommU)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
        ((pCoreOf_le_centralizer_fsuVM h322 hyp).trans (Subgroup.centralizer_le hUV)))
  set e := autOnEquivQuotOf hLU hCU
  have hs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  have hsU : IsSimpleGroup ↥(autOn L (fsuUL T L I)) := e.isSimpleGroup
  have hncU : ∃ a b : ↥(autOn L (fsuUL T L I)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_of_isQuasisimple hyp.fsu.quasisimple
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hq : CFSG.IsQuasisimple ↥(autOn L (fsuUL T L I)) := isQuasisimple_of_simple' hncU
  have := hyp.fsu.simple
  have hcore := qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke
  have hS : SQTKGroup ↥(autOn L (fsuUL T L I)) :=
    InternalSec.sqtkGroup_autOn hLU
      (InternalSec.sqtkGroup_of_localSQTK hcore.1 (pCoreOf_ne_bot_of_faithful hyp.fsu.faithful))
      (hCU ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hL32 : LBarL32 L := by
    have h := card_quot_dvd_card_autOn hLI (inf_centralizer_le_pCoreOf h37 h38 hyp hLI hcommI)
    have hAut : Nat.card (MulAut ↥I) = 168 := by
      rw [card_mulAut_of_sq_eq_one hI2 hcard, card_GL_three_two]
    have hdvd2 : Nat.card ↥(autOn L I) ∣ 168 := hAut ▸ Subgroup.card_subgroup_dvd_card _
    exact lBarL32_of_shape_dvd (hshape G T L I hyp.fsu hyp.lt hyp.three) (h.trans hdvd2)
  have hc168 : Nat.card ↥(autOn L (fsuUL T L I)) = 168 := by
    obtain ⟨e'⟩ := hL32
    rw [Nat.card_congr (e.trans e').toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three]
  have hnoniso : ¬ IsXSectionIso L ⊥ I (CFSG.conjugate I s) :=
    not_isXSectionIso_of h37 h38 hyp hsT hsN hsO hLI htop
      (inf_centralizer_le_pCoreOf h37 h38 hyp hLI hcommI)
  have hnotFF : ¬ IsFFModule
      (Subgroup.normalizer (autOn L (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I)))) :=
    InternalSec.not_isFFModule_normalizer_of_sum h51
      (fun v => Subtype.ext (by simpa using hU2 v v.2)) hq hS
      (InternalSec.sup_subgroupOf_eq_top hIU hIsU hU.symm)
      (InternalSec.inf_subgroupOf_eq_bot hinf) (InternalSec.autOn_inv_subgroupOf hLI)
      (InternalSec.autOn_inv_subgroupOf hLIs) (InternalSec.irr_subgroupOf hLU hirrI)
      (InternalSec.irr_subgroupOf hLU hirrIs) (InternalSec.not_le_fixV_subgroupOf hIU hLU hntI)
      (InternalSec.not_le_fixV_subgroupOf hIsU hLU hntIs)
      (InternalSec.not_secIsoL_of_not_isXSectionIso hIU hIsU hLU hLI hLIs hnoniso)
      (fun n hn π => not_surjective_statedSL hc168 n hn π)
  have hcomp := isComponentOf_autOn h37 h38 h322 hyp
  have key : ∀ B : Subgroup (MulAut ↥(fsuVM T L I)),
      IsFFStarOffender (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) B →
        ¬ B ≤ centSub ((fsuUL T L I).subgroupOf (fsuVM T L I)) → False := by
    intro B hB hnt
    have hBN := h154 _ hVt _ B hB _ hcomp
    have hBY : B ≤ autOn ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G)) (fsuVM T L I) :=
      fun φ hφ => mem_autOn_inf_normalizer h37 h38 hyp (hB.1 hφ) (hBN hφ)
    have hYU : (fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (fsuUL T L I : Set G) :=
      le_normalizer_commutator (inf_le_left.trans hHN) inf_le_right
    obtain ⟨C, hC, hCne, hCe, hCc⟩ := InternalSec.isFFModule_autOn_of_offender hel.2 hUV hYU
      ⟨hBY, hB.2⟩ hnt
    exact hnotFF ⟨C, hC.trans (autOn_le_normalizer_autOn inf_le_right), hCne, hCe, hCc⟩
  intro hFF
  obtain ⟨A, hA⟩ := ((B1_4_5 hVt _).out 1 2).1 hFF
  by_cases hAU : A ≤ centSub ((fsuUL T L I).subgroupOf (fsuVM T L I))
  · set tbar := conjAct (fsuVM T L I) ⟨t, htV⟩
    have htX : tbar ∈ autOn (fsuL0 T L ⊔ T) (fsuVM T L I) :=
      mem_autOn_iff'.mpr ⟨⟨t, htV⟩, Subgroup.mem_sup_right ht, rfl⟩
    refine key (B1.conjAut tbar A) (B1.isFFStarOffender_conjAut hA htX) fun h => hA.2.1 ?_
    have hUtV : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
      have h' := conjugate_mono hUV t
      rwa [conjugate_fsuVM (le_fsuM T L ht)] at h'
    have hVsup := fsuVM_le_sup_of_eq h37 h38 hyp hVV ht htn
    have htop' : (fsuUL T L I).subgroupOf (fsuVM T L I) ⊔
        (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) = ⊤ :=
      InternalSec.sup_subgroupOf_eq_top hUV hUtV (le_antisymm (sup_le hUV hUtV) hVsup)
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have h1 : ∀ w ∈ (fsuUL T L I).subgroupOf (fsuVM T L I), a w = w := fun w hw =>
      mem_centSub.mp (hAU ha) w hw
    have h2 : ∀ w ∈ (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I), a w = w := by
      intro w hw
      rw [subgroupOf_conjugate htV] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have hmem : tbar * a * tbar⁻¹ ∈ B1.conjAut tbar A := by
        rw [B1.mem_conjAut]
        simpa [mul_assoc] using ha
      show a (tbar⁻¹ u) = tbar⁻¹ u
      have h3 : (tbar * a * tbar⁻¹) u = u := mem_centSub.mp (h hmem) u hu
      rw [MulAut.mul_apply, MulAut.mul_apply] at h3
      calc a (tbar⁻¹ u) = tbar⁻¹ (tbar (a (tbar⁻¹ u))) := (tbar.symm_apply_apply _).symm
        _ = tbar⁻¹ u := by rw [h3]
    have hle : (⊤ : Subgroup ↥(fsuVM T L I)) ≤
        MonoidHom.eqLocus a.toMonoidHom (MonoidHom.id _) := by
      rw [← htop']
      exact sup_le (fun w hw => h1 w hw) (fun w hw => h2 w hw)
    ext v
    exact congrArg Subtype.val (hle (Subgroup.mem_top v))
  · exact key A hA hAU

end CFSG.Quasithin.Vol2.Ch10.SecA
