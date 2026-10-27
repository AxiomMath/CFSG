module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Background.HFCode22U
public import Certificates.Certificate8281

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.Mathieu CFSG.Quasithin CFSG.Quasithin.H
  CFSG.Quasithin.H.Coc

theorem hMB22Greedy {k : ℕ}
    (hk : k ≤ 5) : forallGreedy T22s2.invols predMB22 k [] = true :=
  (forallGreedyP_eq pos22s2_eq predMB22 k []).symm.trans
    (forallGreedyAll_le 5 [] Certificates.certificate8281 k hk)

theorem codeAct22_comm_mem {B : List ℕ} {s : T22s2.Elem}
    (hs : chainCommIn B s = true) : ∀ m < 2 ^ 10, (codeAct22 s m ^^^ m) ∈ combos B := by
  have hlin : XorLin (fun m => codeAct22 s m ^^^ m) := by
    intro a b
    show actM (matsC22[s.idx]!) (a ^^^ b) ^^^ (a ^^^ b) =
      (actM (matsC22[s.idx]!) a ^^^ a) ^^^ (actM (matsC22[s.idx]!) b ^^^ b)
    rw [actM_xor (matsC22[s.idx]!) a b]
    ac_rfl
  refine mem_combos_of_xorLin (f := fun m => codeAct22 s m ^^^ m) hlin (n := 10) ?_
  intro j hj
  simp only [chainCommIn, List.all_eq_true, List.mem_range] at hs
  simpa using hs j hj

theorem code22_E32_comm_std
    {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}
    (h : MathieuCode22 H ⊤ ⊥) (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian 2 X) (hX : Nat.card ↥X = 2 ^ 5) :
    ∃ e : V ≃* W10, H.map (congrHom e) = imgC mog22 ∧
      fixV (X.map (congrHom e)) = maskSub 10 [19, 194, 354, 513] ∧
      commV (X.map (congrHom e)) ≤ maskSub 10 r2B9 ∧
      ¬ commV (X.map (congrHom e)) ≤ maskSub 10 r2W8 := by
  have hLM : IsOver H (Subgroup.normalizer (H : Set (MulAut V))) :=
    ⟨Subgroup.le_normalizer, le_rfl⟩
  obtain ⟨e, he⟩ := code22_std h
  have hXe2 : IsElemAbelian2 X := isElemAbelian2_iff.2 hXe
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC22 rhoC10_mog22plus_injective
    phi22 (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    (hMB22Greedy le_rfl) e (map_le_rangeC22 hLM he hXN) hXe2 hX
  have hcl := card_of_chainSub hchain (chainAutC22_injective e g) hind
  rw [hX] at hcl
  have hlen : l.length = 5 := (Nat.pow_right_injective (le_refl 2) hcl).symm
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hind).1
  have hpred' : predU22 l = true ∧ (l.all (chainCommIn r2B9) = true ∧
      l.any (fun s => !(chainCommIn r2W8 s)) = true) := by
    unfold predMB22 at hpred
    rw [Bool.and_eq_true] at hpred
    refine ⟨hpred.1, ?_⟩
    have h2 := hpred.2
    simp only [hlen, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at h2
    exact h2
  have hfix : fixMasks 10 codeAct22 l = u22Masks := by
    rw [← codeFixMasks22_eq hinv]
    have h1 := hpred'.1
    simp only [predU22, hlen, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h1
    exact h1
  set e' := twistEquiv e psiC22 g with he'
  have hc := chainActC22 e g
  refine ⟨e', ?_, ?_, ?_, ?_⟩
  ·
    have hN : psiC22 g ∈ Subgroup.normalizer
        ((rhoC10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) := by
      rw [normalizer_rhoC10_mog22]
      exact ⟨g, rfl⟩
    rw [← range_rhoC10_eq_imgC]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxr : congrHom e x ∈ (rhoC10 mog22 mog22_le_mog22plus).range := by
        rw [← he]
        exact ⟨x, hx, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp hxr
      have h3 := congrHom_trans_eq_conj e (psiC22 g) x
      exact (congrArg (· ∈ (rhoC10 mog22 mog22_le_mog22plus).range) h3).mpr h2
    · rintro _ ⟨k, rfl⟩
      have hk : rhoC10 mog22 mog22_le_mog22plus k ∈ (rhoC10 mog22 mog22_le_mog22plus).range :=
        ⟨k, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) _).mp hk
      rw [← he] at h1
      obtain ⟨x, hx, hxe⟩ := h1
      refine ⟨x, hx, MulEquiv.ext fun w => ?_⟩
      have h4 : congrHom e x ((psiC22 g)⁻¹ w) =
          (psiC22 g)⁻¹ (rhoC10 mog22 mog22_le_mog22plus k w) := by
        have := congrArg (fun f : MulAut W10 => f ((psiC22 g)⁻¹ w)) hxe
        simp only [MulAut.mul_apply, inv_inv, MulAut.apply_inv_self] at this
        exact this
      show psiC22 g (congrHom e x ((psiC22 g)⁻¹ w)) = _
      rw [h4, MulAut.apply_inv_self]
      rfl
  ·
    ext w
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
    refine (mem_fixV_map_congrHom_iff' e' X _).trans ?_
    change (MaskCoords.ofEquiv e').vm m ∈ fixV X ↔ _
    rw [vm_mem_fixV_iff hc hchain hm]
    have h2 : (l.all fun s => codeAct22 s m == m) = true ↔ m ∈ fixMasks 10 codeAct22 l := by
      have hm' : m < 1024 := hm
      simp [fixMasks, List.mem_range, hm']
    rw [h2, hfix]
    have h3 := toW_mem_UC_iff hm
    rw [show (u22Masks : List ℕ) = hbU0Masks from rfl]
    exact h3.symm
  ·
    have hgen : ∀ y ∈ {y | ∃ s ∈ l, y = psiC22 (phi22 s)}, ∀ v : W10,
        y v * v⁻¹ ∈ maskSub 10 r2B9 := by
      rintro _ ⟨s, hs, rfl⟩ v
      obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
      have hcomm := codeAct22_comm_mem (B := r2B9)
        (List.all_eq_true.1 hpred'.2.1 s hs) m hm
      have e1 : psiC22 (phi22 s) (toW 10 m) * (toW 10 m)⁻¹ = toW 10 (codeAct22 s m ^^^ m) := by
        rw [psiC22_phi22 s hm, toW_inv_self, toW_xor]
        rfl
      exact Eq.mpr (congrArg (· ∈ maskSub 10 r2B9) e1) (toW_mem_maskSub hcomm)
    have hXcl : X.map (congrHom e') ≤ Subgroup.closure {y | ∃ s ∈ l, y = psiC22 (phi22 s)} := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨s, hs, rfl⟩ := (hchain a).1 ha
      rw [congrHom_chainAut]
      exact subprods_map_mem_closure (psiC22.comp phi22) l s hs
    exact (commV_mono_mat hXcl).trans (CFSG.Quasithin.H.ZTrans.commV_closure_le _ _ hgen)
  ·
    intro hle
    obtain ⟨s, hs, hsn⟩ := List.any_eq_true.1 hpred'.2.2
    have hsn' : chainCommIn r2W8 s = false := by simpa using hsn
    unfold chainCommIn at hsn'
    obtain ⟨j, hjr, hjn⟩ := List.all_eq_false.1 hsn'
    have hj : j < 10 := List.mem_range.1 hjr
    have hmem : psiC22 (phi22 s) ∈ X.map (congrHom e') := by
      refine ⟨chainAut e psiC22 phi22 g s, (hchain _).2 ⟨s, mem_subprods_of_mem hs, rfl⟩, ?_⟩
      exact congrHom_chainAut e psiC22 phi22 g s
    have hc1 : psiC22 (phi22 s) (toW 10 (2 ^ j)) * (toW 10 (2 ^ j))⁻¹ ∈
        commV (X.map (congrHom e')) :=
      Subgroup.subset_closure ⟨_, hmem, toW 10 (2 ^ j), rfl⟩
    have hj2 : 2 ^ j < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) hj
    have e1 : psiC22 (phi22 s) (toW 10 (2 ^ j)) * (toW 10 (2 ^ j))⁻¹ =
        toW 10 (codeAct22 s (2 ^ j) ^^^ 2 ^ j) := by
      rw [psiC22_phi22 s hj2, toW_inv_self, toW_xor]
      rfl
    have hin := hle hc1
    rw [e1] at hin
    obtain ⟨m, hm, hme⟩ := hin
    have hlt : codeAct22 s (2 ^ j) ^^^ 2 ^ j < 2 ^ 10 :=
      Nat.xor_lt_two_pow (by
        rw [codeAct22, actM_matsC10 T22s2 (mats := matsC22) rfl s hj2]
        exact actC10_lt _ _) hj2
    have hr2W8lt : ∀ a ∈ r2W8, a < 2 ^ 10 := by decide
    have heq : m = codeAct22 s (2 ^ j) ^^^ 2 ^ j :=
      toW_inj (combos_lt hr2W8lt m hm) hlt hme
    exact hjn (by rw [← heq]; exact List.contains_iff_mem.2 hm)

end CFSG.Quasithin.H13.Mat
