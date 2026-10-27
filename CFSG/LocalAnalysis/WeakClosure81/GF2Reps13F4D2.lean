module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4A
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FourE
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsKernel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4D2Aux2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

structure S134Weights (x x' u : MulAut W) : Prop where
  rk_nine : rk ↥(commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x')) = 9
  eq_x : commSub ⊤ (Subgroup.zpowers x) = commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x')
  eq_x' : commSub ⊤ (Subgroup.zpowers x') = commSub ⊤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x')
  fix_x : commSub ⊤ (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) = ⊥
  supp_rk : ∀ D ∈ hypSupp 7 (Subgroup.zpowers x ⊔ Subgroup.zpowers x'),
    rk ↥(hypPart (Subgroup.zpowers x ⊔ Subgroup.zpowers x') D) = 3
  supp_trans : ∀ D ∈ hypSupp 7 (Subgroup.zpowers x ⊔ Subgroup.zpowers x'),
    ∀ D' ∈ hypSupp 7 (Subgroup.zpowers x ⊔ Subgroup.zpowers x'),
      ∃ m : ℕ, D' = D.map (MulAut.conj (u ^ m)).toMonoidHom

theorem s134b_caseB_data {Y K : Subgroup (MulAut W)} {t : MulAut W} (F : S134Frame Y K t)
    (hno : ∀ I ∈ irrSet K, commSub I (S134Conj t K) ≠ ⊥) :
    ∃ x ∈ K, ∃ u ∈ K, orderOf x = 7 ∧ u * x * u⁻¹ = x ^ 2 ∧
      S134Weights x (t * x * t⁻¹) u := by
  obtain ⟨x, hx, u, hu, hx7, hux⟩ := s134b_exists_seven_frame F.l3
  obtain ⟨hx'mem0, hx'70, hcomm0, htx'0, hx'notmem0⟩ := F.seven_data hx hx7
  let x' : MulAut W := t * x * t⁻¹
  have hx'mem : x' ∈ S134Conj t K := hx'mem0
  have hx'7 : orderOf x' = 7 := hx'70
  have hcomm : x * x' = x' * x := hcomm0
  have htx' : t * x' * t⁻¹ = x := htx'0
  have hx'notmem : x' ∉ Subgroup.zpowers x := hx'notmem0
  have hW2 : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact F.exp w
  have hW2' : ∀ w : W, w ^ 2 = 1 := F.exp
  have hEelem : CFSG.Open.IsElemAbelian 7 (f4d2_E x x') := by
    change CFSG.Open.IsElemAbelian 7 (Subgroup.zpowers x ⊔ Subgroup.zpowers x')
    exact w16g_isElemAbelian_sup_zpowers (by rw [← hx7]; exact pow_orderOf_eq_one x)
      (by rw [← hx'7]; exact pow_orderOf_eq_one x') hcomm
  have hEcard : Nat.card ↥(f4d2_E x x') = 49 := by
    change Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers x') = 49
    have h := w16g_card_sup_zpowers (G := MulAut W) Nat.prime_seven hx7 hx'7 hcomm hx'notmem
    norm_num at h ⊢
    exact h
  have hEodd : Odd (Nat.card ↥(f4d2_E x x')) := by rw [hEcard]; norm_num
  have hEcomm : ∀ a ∈ f4d2_E x x', ∀ b ∈ f4d2_E x x', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEelem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hMstab : StableUnder (f4d2_E x x') (commSub ⊤ (f4d2_E x x')) :=
    fun e he v hv => CFSG.Quasithin.Asc81c.commSub_stable' he hv
  have hME : commSub (commSub ⊤ (f4d2_E x x')) (f4d2_E x x') = commSub ⊤ (f4d2_E x x') :=
    CFSG.Quasithin.Asc81c.commSub_commSub_eq' hW2' hEodd
  have hMfix : commSub ⊤ (f4d2_E x x') ⊓ fixV (f4d2_E x x') = ⊥ := by
    rw [inf_comm]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2' hEodd
  have hdecomp := inf_fixV_hyperplane_decomposition hW2' Nat.prime_seven (by norm_num)
    (f4d2_E x x') hEelem hMstab hME
  have hdec : iSupIndep (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D) :=
    hdecomp.1
  have hsup : (⨆ D : hyperplanes 7 (f4d2_E x x'), hypPart (f4d2_E x x') D) =
      commSub ⊤ (f4d2_E x x') := hdecomp.2
  have hux' : u * x' * u⁻¹ = x' := by
    have hc : u * x' = x' * u := F.comm u hu x' hx'mem
    rw [hc]; group
  obtain ⟨hz_le, hthree, hcase⟩ :=
    s134_E_components hW2 F.ord F.rk_le hx7 hx'7 hcomm rfl htx' hx'notmem
  refine ⟨x, hx, u, hu, hx7, hux, ?_⟩
  have hXhyp : Subgroup.zpowers x ∈ hyperplanes 7 (f4d2_E x x') :=
    f4d2_X_mem hx7 hx'7 hcomm hx'notmem
  have hX'hyp : Subgroup.zpowers x' ∈ hyperplanes 7 (f4d2_E x x') := by
    rw [← f4d2_H_zero x x']
    exact f4d2_H_mem hx7 hx'7 hcomm hx'notmem 0
  rcases hcase with hcaseI | hcaseII
  ·
    have hUx : hypPart (f4d2_E x x') (Subgroup.zpowers x) = ⊥ := hcaseI.1
    have hUx' : hypPart (f4d2_E x x') (Subgroup.zpowers x') = ⊥ := hcaseI.2
    have heq_x : commSub ⊤ (Subgroup.zpowers x) = commSub ⊤ (f4d2_E x x') := by
      apply le_antisymm
      · exact commSub_mono le_top le_sup_left
      · rw [← hsup]
        refine iSup_le fun D => ?_
        by_cases hDX : (D : Subgroup (MulAut W)) = Subgroup.zpowers x
        · rw [hDX, hUx]; exact bot_le
        · exact f4d2_component_le_commSub hW2 hx7 hMstab hMfix hEcomm
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)) D.2 hXhyp hDX
    have heq_x' : commSub ⊤ (Subgroup.zpowers x') = commSub ⊤ (f4d2_E x x') := by
      apply le_antisymm
      · exact commSub_mono le_top le_sup_right
      · rw [← hsup]
        refine iSup_le fun D => ?_
        by_cases hDX' : (D : Subgroup (MulAut W)) = Subgroup.zpowers x'
        · rw [hDX', hUx']; exact bot_le
        · exact f4d2_component_le_commSub hW2 hx'7 hMstab hMfix hEcomm
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers x')) D.2 hX'hyp hDX'
    have hfix_x : commSub ⊤ (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
      rw [heq_x]; exact hUx
    have hbound := f4d2_sum_seven_le hW2 hx7 hx'7 hcomm hx'notmem hdec hMstab hMfix hEcomm
      hz_le
    have horbit := f4d2_orbit_bound hx7 hx'7 hcomm hx'notmem hux hux' hUx' hbound
    have hr1 := f4d2_r1_eq_zero hx7 hx'7 hcomm hx'notmem hthree horbit
    have hMne : commSub ⊤ (f4d2_E x x') ≠ ⊥ := by
      have hx1 : x ≠ 1 := by intro h; rw [h] at hx7; simp at hx7
      have hcommX_ne : commSub ⊤ (Subgroup.zpowers x) ≠ ⊥ := by
        intro h
        have hfix : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers x) := commSub_eq_bot_iff.mp h
        apply hx1
        ext w
        exact (mem_fixV.mp (hfix (Subgroup.mem_top w))) x (Subgroup.mem_zpowers x)
      intro h
      exact hcommX_ne (heq_x.trans h)
    have hrkM := f4d2_rk_commSub_eq hx7 hx'7 hcomm hx'notmem hux hux' hUx hUx' hdec hsup hr1
    have hrk9 := f4d2_rk_nine hW2' hx7 hx'7 hcomm hx'notmem hthree horbit hrkM hMne
    have hr3 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) = 3 := by omega
    have hsupp_rk :=
      f4d2_supp_rk hW2' hx7 hx'7 hcomm hx'notmem hux hux' hUx hUx' hr1 hr3
    have hclass :=
      f4d2_hypSupp_class hW2' hx7 hx'7 hcomm hx'notmem hux hux' hUx hUx' hr1 hr3
    have hsupp_trans :=
      f4d2_supp_trans hx7 hx'7 hcomm hx'notmem hux hux' hclass
    refine ⟨hrk9, heq_x, heq_x', hfix_x, ?_, ?_⟩
    · intro D hD; exact hsupp_rk D hD
    · intro D hD D' hD'; exact hsupp_trans D hD D' hD'
  ·
    rcases hcaseII with ⟨hrkX, hrkX', hrkt, hother⟩
    have hUz_bot : hypPart (f4d2_E x x') (Subgroup.zpowers (x * x'⁻¹)) = ⊥ :=
      f4d2_hypPart_z_eq_bot hW2' hx7 hx'7 hcomm hx'notmem hux hux' hother
    have hM_eq : commSub ⊤ (f4d2_E x x') =
        hypPart (f4d2_E x x') (Subgroup.zpowers x) ⊔
          hypPart (f4d2_E x x') (Subgroup.zpowers x') := by
      rw [← hsup]
      apply le_antisymm
      · refine iSup_le fun D => ?_
        by_cases hDX : (D : Subgroup (MulAut W)) = Subgroup.zpowers x
        · rw [hDX]; exact le_sup_left
        · by_cases hDX' : (D : Subgroup (MulAut W)) = Subgroup.zpowers x'
          · rw [hDX']; exact le_sup_right
          · by_cases hDz : (D : Subgroup (MulAut W)) = Subgroup.zpowers (x * x'⁻¹)
            · rw [hDz, hUz_bot]; exact bot_le
            · have hbot : hypPart (f4d2_E x x') (D : Subgroup (MulAut W)) = ⊥ :=
                hother (D : Subgroup (MulAut W)) D.2 hDX hDX' hDz
              rw [hbot]; exact bot_le
      · refine sup_le ?_ ?_
        · exact le_iSup (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D)
            ⟨Subgroup.zpowers x, hXhyp⟩
        · exact le_iSup (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D)
            ⟨Subgroup.zpowers x', hX'hyp⟩
    have hUXstab : StableUnder (Subgroup.zpowers x)
        (hypPart (f4d2_E x x') (Subgroup.zpowers x')) := by
      intro a ha v hv
      rw [Subgroup.mem_inf] at hv ⊢
      refine ⟨hMstab a (Subgroup.mem_sup_left ha) v hv.1, ?_⟩
      rw [mem_fixV] at hv ⊢
      intro b hb
      have hcomm_ab : a * b = b * a :=
        hEcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)
      rw [← MulAut.mul_apply, ← hcomm_ab, MulAut.mul_apply, hv.2 b hb]
    have hWx_le : commSub ⊤ (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers x') := by
      have hXodd : Odd (Nat.card ↥(Subgroup.zpowers x)) := by
        rw [Nat.card_zpowers, hx7]; norm_num
      have hcop : commSub (commSub ⊤ (Subgroup.zpowers x)) (Subgroup.zpowers x) =
          commSub ⊤ (Subgroup.zpowers x) :=
        CFSG.Quasithin.Asc81c.commSub_commSub_eq' hW2' hXodd
      calc commSub ⊤ (Subgroup.zpowers x)
          = commSub (commSub ⊤ (Subgroup.zpowers x)) (Subgroup.zpowers x) := hcop.symm
        _ ≤ commSub (commSub ⊤ (f4d2_E x x')) (Subgroup.zpowers x) :=
            commSub_mono (commSub_mono le_top le_sup_left) le_rfl
        _ = commSub (hypPart (f4d2_E x x') (Subgroup.zpowers x) ⊔
              hypPart (f4d2_E x x') (Subgroup.zpowers x')) (Subgroup.zpowers x) := by
            rw [← hM_eq]
        _ = commSub (hypPart (f4d2_E x x') (Subgroup.zpowers x)) (Subgroup.zpowers x) ⊔
              commSub (hypPart (f4d2_E x x') (Subgroup.zpowers x'))
                (Subgroup.zpowers x) := by
            rw [commSub_sup_left]
        _ ≤ fixV (Subgroup.zpowers x') := by
            refine sup_le ?_ ?_
            · have hbot : commSub (hypPart (f4d2_E x x') (Subgroup.zpowers x))
                  (Subgroup.zpowers x) = ⊥ := commSub_eq_bot_iff.mpr inf_le_right
              rw [hbot]; exact bot_le
            · exact (commSub_le_of_invariant hUXstab).trans inf_le_right
    have hStabK' : StableUnder (S134Conj t K) (commSub ⊤ (Subgroup.zpowers x)) := by
      intro k' hk' w hw
      rw [commSub] at hw ⊢
      refine Subgroup.closure_induction (p := fun c _ => k' c ∈ commSub ⊤ (Subgroup.zpowers x))
        ?_ ?_ ?_ ?_ hw
      · rintro c ⟨y, hy, v, -, rfl⟩
        have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hx) hy
        have hky : y * k' = k' * y := F.comm y hyK k' hk'
        have h1 : k' (y v) = y (k' v) := by
          have h2 := congrArg (fun f : MulAut W => f v) hky
          simpa [MulAut.mul_apply] using h2.symm
        have hmem : y (k' v) * (k' v)⁻¹ ∈ commSub ⊤ (Subgroup.zpowers x) :=
          Subgroup.subset_closure ⟨y, hy, k' v, Subgroup.mem_top _, rfl⟩
        simpa only [map_mul, map_inv, h1] using hmem
      · simp
      · intro a b _ _ ha hb
        rw [map_mul]
        exact (commSub ⊤ (Subgroup.zpowers x)).mul_mem ha hb
      · intro a _ ha
        rw [map_inv]
        exact (commSub ⊤ (Subgroup.zpowers x)).inv_mem ha
    have hB_le : commSub ⊤ (Subgroup.zpowers x) ≤ fixV (S134Conj t K) := by
      have : IsSimpleGroup ↥(S134Conj t K) := s134b_isSimpleGroup_of_isL3 F.l3'
      have hx'1 : x' ≠ 1 := by intro h; rw [h] at hx'7; simp at hx'7
      exact s134b_le_fixV_of_normalClosure (K := S134Conj t K) inferInstance hx'mem hx'1
        hStabK' hWx_le
    have hStabFix : StableUnder K (fixV (S134Conj t K)) := by
      intro a ha v hv
      rw [mem_fixV] at hv ⊢
      intro b hb
      have hcomm_ab : a * b = b * a := F.comm a ha b hb
      rw [← MulAut.mul_apply, ← hcomm_ab, MulAut.mul_apply, hv b hb]
    have hK_le : commSub ⊤ K ≤ fixV (S134Conj t K) := by
      have : IsSimpleGroup ↥K := s134b_isSimpleGroup_of_isL3 F.l3
      have hx1 : x ≠ 1 := by intro h; rw [h] at hx7; simp at hx7
      exact s134b_commSub_le_of_normalClosure (K := K) inferInstance hx hx1 hStabFix hB_le
    have hx1 : x ≠ 1 := by intro h; rw [h] at hx7; simp at hx7
    have hKne : K ≠ ⊥ := by
      intro h
      have hxbot : x ∈ (⊥ : Subgroup (MulAut W)) := h ▸ hx
      rw [Subgroup.mem_bot] at hxbot
      exact hx1 hxbot
    have hcommK : commutator ↥K = ⊤ :=
      Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr F.perfect)
    have hQ : QuadTrivial K := quadTrivial_of_commutator_eq_top hcommK
    obtain ⟨I, hI⟩ := exists_mem_irrSet_of_ne_bot hQ hKne
    have hKI : commSub I (S134Conj t K) = ⊥ := by
      rw [commSub_eq_bot_iff]
      calc I = commSub I K := hI.1.symm
        _ ≤ commSub ⊤ K := commSub_mono le_top le_rfl
        _ ≤ fixV (S134Conj t K) := hK_le
    exact absurd hKI (hno I hI)

end CFSG.LocalAnalysis.WeakClosure81
