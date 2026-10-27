module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Background.HB82Coc24
public import Certificates.Certificate8282

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Coc24
  CFSG.Quasithin.H.Coc CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.FixSyl

theorem hMB24Greedy :
    forallGreedy T24s2.invols predMB24 6 [] = true :=
  (forallGreedyP_eq pos24s2_eq predMB24 6 []).symm.trans
    (forallGreedyAll_le 6 [] Certificates.certificate8282 6 le_rfl)

theorem act24s2_comm_mem {B : List ℕ} {s : T24s2.Elem}
    (hs : chainCommIn24 B s = true) : ∀ m < 2 ^ 11, (act24s2 s m ^^^ m) ∈ combos B := by
  have hlin : XorLin (fun m => act24s2 s m ^^^ m) := by
    intro a b
    show actM (mats24s2[s.idx]!) (a ^^^ b) ^^^ (a ^^^ b) =
      (actM (mats24s2[s.idx]!) a ^^^ a) ^^^ (actM (mats24s2[s.idx]!) b ^^^ b)
    rw [actM_xor (mats24s2[s.idx]!) a b]
    ac_rfl
  refine mem_combos_of_xorLin (f := fun m => act24s2 s m ^^^ m) hlin (n := 11) ?_
  intro j hj
  simp only [chainCommIn24, List.all_eq_true, List.mem_range] at hs
  simpa using hs j hj

theorem fixV_comm_eq_UT
    {V : Type} [CommGroup V]
    [Finite V] {H X : Subgroup (MulAut V)} {e : V ≃* W11}
    (he : H.map (congrHom e) = (rho11 AutPerm le_rfl).range) (hX : Nat.card ↥X = 2 ^ 6)
    (hfX : Nat.card ↥(fixV X) = 2 ^ 3) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) :
    ∃ g : ↥AutPerm, fixV (X.map (congrHom (twistEquiv e rhoM24 g))) = UT ∧
      commV (X.map (congrHom (twistEquiv e rhoM24 g))) ≤ maskSub 11 r4L9 := by
  have hXR : X.map (congrHom e) ≤ rhoM24.range := by
    have h2 := Subgroup.le_normalizer_map (H := H) (congrHom e)
    have h3 : Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut W11)) :
        Set (MulAut W11)) = rhoM24.range :=
      (congrArg (fun K : Subgroup (MulAut W11) => Subgroup.normalizer (K : Set (MulAut W11)))
        he).trans normalizer_rho11_autPerm
    exact (Subgroup.map_mono hXN).trans (h2.trans h3.le)
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    hMB24Greedy e hXR (isElemAbelian2_iff.2 hXe) hX
  have hact := chainAct24 e g
  have hlen : l.length = 6 := by
    have h := card_of_chainSub hchain (chainAut24_injective e g) hind
    rw [hX] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfm : (fixMasks 11 act24s2 l).length = 8 := by
    rw [← card_fixV hact hchain, hfX]
    norm_num
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hind).1
  have hfm24 : (fixMasks24 l).length = 8 := by rw [fixMasks24_eq hinv]; exact hfm
  have hpred' : predKT l = true ∧ l.all (chainCommIn24 r4L9) = true := by
    unfold predMB24 at hpred
    rw [Bool.and_eq_true] at hpred
    refine ⟨hpred.1, ?_⟩
    have h2 := hpred.2
    simp only [hlen, hfm24, bne_self_eq_false, Bool.false_or] at h2
    exact h2
  have hU : fixMasks 11 act24s2 l = uTMasks := by
    have h := hpred'.1
    unfold predKT at h
    rw [fixMasks24_eq hinv, hlen, hfm] at h
    simpa using h
  refine ⟨g, ?_, ?_⟩
  · ext w
    refine (mem_fixV_map_congrHom _ X w).trans ?_
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
    have hv := vm_mem_fixV_iff hact hchain hm
    rw [MaskCoords.ofEquiv_vm] at hv
    refine hv.trans (Iff.trans ?_ (toW_mem_UT_iff hm).symm)
    rw [← hU, fixMasks, List.mem_filter, List.mem_range]
    exact ⟨fun h => ⟨hm, h⟩, fun h => h.2⟩
  · have hgen : ∀ y ∈ {y | ∃ s ∈ l, y = rhoM24 (phi24 s)}, ∀ v : W11,
        y v * v⁻¹ ∈ maskSub 11 r4L9 := by
      rintro _ ⟨s, hs, rfl⟩ v
      obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
      have hcomm := act24s2_comm_mem (B := r4L9)
        (List.all_eq_true.1 hpred'.2 s hs) m hm
      have e1 : rhoM24 (phi24 s) (toW 11 m) * (toW 11 m)⁻¹ = toW 11 (act24s2 s m ^^^ m) := by
        rw [rhoM24_phi24 s hm, toW_inv_self, toW_xor]
      exact Eq.mpr (congrArg (· ∈ maskSub 11 r4L9) e1) (toW_mem_maskSub hcomm)
    have hXcl : X.map (congrHom (twistEquiv e rhoM24 g)) ≤
        Subgroup.closure {y | ∃ s ∈ l, y = rhoM24 (phi24 s)} := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨s, hs, rfl⟩ := (hchain a).1 ha
      rw [congrHom_chainAut]
      exact subprods_map_mem_closure (rhoM24.comp phi24) l s hs
    exact (commV_mono_mat hXcl).trans (CFSG.Quasithin.H.ZTrans.commV_closure_le _ _ hgen)

end CFSG.Quasithin.H13.Mat
