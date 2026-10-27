module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXD
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXEA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX.isPGroup
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem w16g_rk_commSub_sup_pair (hW : ∀ w : W, w * w = 1) {s : MulAut W}
    {U V : Subgroup W} (hdisj : Disjoint U V) (hU : ∀ u ∈ U, s u ∈ U)
    (hV : ∀ v ∈ V, s v ∈ V) :
    rk ↥(commSub (U ⊔ V) (Subgroup.zpowers s)) =
      rk ↥(commSub U (Subgroup.zpowers s)) + rk ↥(commSub V (Subgroup.zpowers s)) := by
  let F : Fin 2 → Subgroup W := fun i => if i = 0 then U else V
  have hF0 : F 0 = U := by simp [F]
  have hF1 : F 1 = V := by simp [F]
  have hFindep : iSupIndep F := by
    apply (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
      (fun k => by fin_cases k <;> simp)).mpr
    rw [hF0, hF1]
    exact hdisj
  have hFstable : ∀ i, ∀ u ∈ F i, s u ∈ F i := by
    intro i
    fin_cases i
    · change ∀ u ∈ F 0, s u ∈ F 0
      rw [hF0]
      exact hU
    · change ∀ u ∈ F 1, s u ∈ F 1
      rw [hF1]
      exact hV
  have hsum := rk_commSub_iSup_eq_sum hW s F hFindep hFstable
  rw [Fin.sum_univ_two, hF0, hF1] at hsum
  have hFsup : (⨆ i, F i) = U ⊔ V := by
    rw [← Finset.sup_univ_eq_iSup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl,
      Finset.sup_insert, Finset.sup_singleton, hF0, hF1]
  rw [hFsup] at hsum
  exact hsum

theorem s13_eight_t_fixes_comps (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N)
    (hrk6 : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)), rk ↥U = 6) :
    ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U.map t.toMonoidHom = U := by
  classical
  obtain ⟨hXe, hXA, -, -⟩ := w16g_s13_eight_X_facts h hD
  set X : Subgroup (MulAut W) := conjClosure A (Subgroup.zpowers z) with hXdef
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian h.hp (by norm_num) hXe
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx => hXA t h.htA x hx
  have htX' : ∀ x ∈ X, t⁻¹ * x * t ∈ X := by
    intro x hx
    simpa only [htinv] using htX x hx
  intro U hU
  by_contra hne
  have hne' : U ≠ U.map t.toMonoidHom := fun h' => hne h'.symm
  have hU' : U.map t.toMonoidHom ∈ s13IsoComps X := map_mem_s13IsoComps htX htX' hU
  have hdisj : Disjoint U (U.map t.toMonoidHom) :=
    (s13IsoComps_sSupIndep h.hW hodd).pairwiseDisjoint hU hU' hne'
  have hcost : rk ↥(commSub (U ⊔ U.map t.toMonoidHom) (Subgroup.zpowers t)) = rk ↥U :=
    (rk_commSub_swap h.hW htt (U' := U.map t.toMonoidHom) rfl (disjoint_iff.mp hdisj)).2
  have hle : rk ↥(commSub (U ⊔ U.map t.toMonoidHom) (Subgroup.zpowers t)) ≤ 3 := by
    have hmono : commSub (U ⊔ U.map t.toMonoidHom) (Subgroup.zpowers t) ≤
        commSub (⊤ : Subgroup W) (Subgroup.zpowers t) := commSub_mono le_top le_rfl
    have := rk_mono hmono
    rwa [hD.hrkt] at this
  have h6 : rk ↥U = 6 := hrk6 U hU
  omega

theorem s13_eight_t_central_off_W6 (h : Cfg133 A t 3) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N)
    (hrk6 : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)), rk ↥U = 6)
    (hW6 : commSub ⊤ (Subgroup.zpowers z) ∈
      s13IsoComps (conjClosure A (Subgroup.zpowers z))) :
    ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U ≠ commSub ⊤ (Subgroup.zpowers z) → commSub U (Subgroup.zpowers t) = ⊥ := by
  classical
  have hfix_all : ∀ U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)),
      U.map t.toMonoidHom = U := s13_eight_t_fixes_comps h hD hrk6
  obtain ⟨hXe, hXA, -, -⟩ := w16g_s13_eight_X_facts h hD
  set X : Subgroup (MulAut W) := conjClosure A (Subgroup.zpowers z) with hXdef
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian h.hp (by norm_num) hXe
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx => hXA t h.htA x hx
  have htX' : ∀ x ∈ X, t⁻¹ * x * t ∈ X := by
    intro x hx
    simpa only [htinv] using htX x hx
  intro U hU hne
  have hfixU : U.map t.toMonoidHom = U := hfix_all U hU
  have hfixW : (commSub ⊤ (Subgroup.zpowers z)).map t.toMonoidHom =
      commSub ⊤ (Subgroup.zpowers z) := hfix_all _ hW6
  have hsU : ∀ u ∈ U, t u ∈ U := by
    intro u hu
    rw [← hfixU]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hu
  have hsW : ∀ u ∈ commSub ⊤ (Subgroup.zpowers z), t u ∈ commSub ⊤ (Subgroup.zpowers z) := by
    intro u hu
    rw [← hfixW]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hu
  have hdisj : Disjoint U (commSub ⊤ (Subgroup.zpowers z)) :=
    (s13IsoComps_sSupIndep h.hW hodd).pairwiseDisjoint hU hW6 hne
  have hsum : rk ↥(commSub (U ⊔ commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) =
      rk ↥(commSub U (Subgroup.zpowers t)) +
        rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) :=
    w16g_rk_commSub_sup_pair h.hW hdisj hsU hsW
  have hleft : rk ↥(commSub (U ⊔ commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) ≤ 3 := by
    have hmono : commSub (U ⊔ commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t) ≤
        commSub (⊤ : Subgroup W) (Subgroup.zpowers t) := commSub_mono le_top le_rfl
    have := rk_mono hmono
    rwa [hD.hrkt] at this
  have hWcost : 2 ≤ rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) :=
    s13_eight_W6_cost_ge_two h hD
  have hUcost_le : rk ↥(commSub U (Subgroup.zpowers t)) ≤ 1 := by omega
  have hHmem := s13KerOn_mem_hyperplanes h.hW h.hp (by norm_num : (3 : ℕ) ≠ 2) hXe hU
  have hHX : s13KerOn X U ≤ X := hHmem.1
  have hidx : (s13KerOn X U).relIndex X = 3 := hHmem.2
  have hsH : ∀ x ∈ s13KerOn X U, t * x * t⁻¹ ∈ s13KerOn X U :=
    w16g_normalizes_kerOn htt htX hsU
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hXe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := hXe.2
  rcases w16g_inv_or_cent_of_relIndex_three hXc hX3 hHX hidx htt htX hsH with hinv | hcent
  · have hcost : 2 * rk ↥(commSub U (Subgroup.zpowers t)) = rk ↥U :=
      rk_commSub_fixed_inverted h.hW hXe htt htX hU hsU hinv
    have h6 : rk ↥U = 6 := hrk6 U hU
    omega
  · have heven : Even (rk ↥(commSub U (Subgroup.zpowers t))) :=
      even_rk_commSub_fixed_central h.hW hXe htt htX hU hsU hcent
    have hzero : rk ↥(commSub U (Subgroup.zpowers t)) = 0 := by
      obtain ⟨k, hk⟩ := heven
      omega
    exact (rk_eq_zero_iff (fun v : W => by rw [pow_two]; exact h.hW v)).mp hzero

end CFSG.LocalAnalysis.WeakClosure81
