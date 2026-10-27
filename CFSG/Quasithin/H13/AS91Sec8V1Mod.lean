module

public import CFSG.Quasithin.H13.AS91Sec8V1Cocycle
public import CFSG.Quasithin.H13.AS91Sec8V1Map
public import CFSG.Quasithin.H13.AS91Sec6Kzero
public import CFSG.Quasithin.AppendixH.H16.SextetO23
public import CFSG.Quasithin.AppendixH.H16.ConjNat

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.Quasithin.H.ModChk
open CFSG.Quasithin.H.LU24 CFSG.Quasithin CFSG.ASVolI.H16 CFSG.Open
open scoped Pointwise

@[expose] def tauArr : Array ℕ :=
  #[7, 6, 10, 19, 18, 15, 9, 13, 3, 8, 17, 0, 5, 21, 2, 12, 11, 22, 20, 16, 1, 4, 14, 23]

@[expose] def tauInvArr : Array ℕ :=
  #[11, 20, 14, 8, 21, 12, 1, 0, 9, 6, 2, 16, 15, 7, 22, 5, 19, 10, 4, 3, 18, 13, 17, 23]

theorem tau_ok : InvPairOK 24 tauArr tauInvArr = true := by decide +kernel

@[expose] def tau : S24 := permOfArr 24 tauArr tauInvArr tau_ok

theorem hasArr_tau : HasArr tau tauArr := hasArr_permOfArr tau_ok

theorem hasArr_tauInv : HasArr tau⁻¹ tauInvArr := hasArr_permOfArr_inv tau_ok

private theorem tau_basis : ∀ i : Fin 12, B i ∘ ⇑tau ∈ C := by
  decide +kernel

private theorem tau_basis' : ∀ i : Fin 12, B i ∘ ⇑tau⁻¹ ∈ C := by
  decide +kernel

theorem tau_mem : tau ∈ M24g := mem_AutPerm_of_basis tau_basis tau_basis'

theorem tau_smul : tau • stdSextet = sextFin 0 := by
  unfold sextFin sextOfL
  rw [sextList_zero]
  decide +kernel

theorem sextStab_eq_conjSubg :
    sextStab = conjSubg tau sxGen := by
  have h : sextStab = MY M24g (tau • stdSextet) := by
    rw [tau_smul]
    rfl
  rw [h, MY_smul_of_mem tau_mem, MY_stdSextet_eq]

theorem pCoreOf_sextStab :
    pCoreOf 2 sextStab = conjSubg tau sxKS := by
  rw [sextStab_eq_conjSubg, pCoreOf_conjSubg, pCoreOf_two_sxGen]

@[expose] def sg1 : S24 := tau * sxG1 * tau⁻¹

@[expose] def sg2 : S24 := tau * sxG2 * tau⁻¹

@[expose] def sgT : S24 := tau * sxT * tau⁻¹

@[expose] def sg1Arr : Array ℕ := cArr (cArr tauArr sxG1Arr) tauInvArr

@[expose] def sg2Arr : Array ℕ := cArr (cArr tauArr sxG2Arr) tauInvArr

@[expose] def sgTArr : Array ℕ := cArr (cArr tauArr sxTArr) tauInvArr

@[expose] def sgArrList : List (Array ℕ) := [sg1Arr, sg2Arr, sgTArr]

@[expose] def sgList : List S24 := [sg1, sg2, sgT]

theorem hasArr_sg1 : HasArr sg1 sg1Arr :=
  hasArr_mul (hasArr_mul hasArr_tau hasArr_sxG1) hasArr_tauInv

theorem hasArr_sg2 : HasArr sg2 sg2Arr :=
  hasArr_mul (hasArr_mul hasArr_tau hasArr_sxG2) hasArr_tauInv

theorem hasArr_sgT : HasArr sgT sgTArr :=
  hasArr_mul (hasArr_mul hasArr_tau hasArr_sxT) hasArr_tauInv

theorem hasArr_sgWord (w : List ℕ) : HasArr (wPerm sgList w) (wArr sgArrList w) := by
  refine hasArr_wPerm (ps := sgList) (gs := sgArrList) ?_ w
  intro i
  match i with
  | 0 => exact hasArr_sg1
  | 1 => exact hasArr_sg2
  | 2 => exact hasArr_sgT
  | _ + 3 => exact hasArr_one

theorem sgWord_mem
    (w : List ℕ) : wPerm sgList w ∈ sextStab := by
  refine wPerm_mem (K := sextStab) ?_ w
  intro p hp
  simp only [sgList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · rw [sextStab_eq_conjSubg]
    exact Subgroup.mem_map.mpr ⟨sxG1, Subgroup.subset_closure (by simp), by
      show MulAut.conj tau sxG1 = sg1
      rw [MulAut.conj_apply]; rfl⟩
  · rw [sextStab_eq_conjSubg]
    exact Subgroup.mem_map.mpr ⟨sxG2, Subgroup.subset_closure (by simp), by
      show MulAut.conj tau sxG2 = sg2
      rw [MulAut.conj_apply]; rfl⟩
  · rw [sextStab_eq_conjSubg]
    exact Subgroup.mem_map.mpr ⟨sxT, Subgroup.subset_closure (by simp), by
      show MulAut.conj tau sxT = sgT
      rw [MulAut.conj_apply]; rfl⟩

theorem sextStab_smul_31
    (s : ↥sextStab) :
    rho11 sextStab sextStab_le s (toW 11 31) = toW 11 31 := by
  have hU : IsSextet (sextFin 0) := isSextet_sextFin (by norm_num)
  have hs : (s : S24) • sextFin 0 = sextFin 0 :=
    MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp s.2).2
  calc rho11 sextStab sextStab_le s (toW 11 31)
      = rho11 sextStab sextStab_le s (sextClass (sextFin 0)) := by
        rw [sextClass_sextFin_zero]
    _ = rho11 AutPerm le_rfl ⟨(s : S24), sextStab_le s.2⟩ (sextClass (sextFin 0)) :=
        Loc49.rho11_sextStab_apply s _
    _ = sextClass ((s : S24) • sextFin 0) := (sextClass_smul (sextStab_le s.2) hU).symm
    _ = sextClass (sextFin 0) := by rw [hs]
    _ = toW 11 31 := sextClass_sextFin_zero

theorem sg1_mem :
    sg1 ∈ sextStab := by
  have h := sgWord_mem [0]
  simpa [sgList, wPerm] using h

theorem sg2_mem :
    sg2 ∈ sextStab := by
  have h := sgWord_mem [1]
  simpa [sgList, wPerm] using h

theorem sgT_mem :
    sgT ∈ sextStab := by
  have h := sgWord_mem [2]
  simpa [sgList, wPerm] using h

theorem fix_gens_masks : ∀ m < 2 ^ 11, (∀ g ∈ sgArrList, act11 g m = m) → m = 0 ∨ m = 31 := by
  decide +kernel

theorem conjSubg_sxKS_fixes :
    ∀ σ ∈ conjSubg tau sxKS, σ • sextFin 0 = sextFin 0 := by
  rintro σ ⟨y, hy, rfl⟩
  change MulAut.conj tau y • sextFin 0 = sextFin 0
  have hyU : y • stdSextet = stdSextet :=
    MulAction.mem_stabilizer_iff.mp (sxGen_le_stabilizer_stdSextet (sxKS_le_sxGen hy))
  have h1 : tau⁻¹ • sextFin 0 = stdSextet := by
    rw [← tau_smul, inv_smul_smul]
  rw [MulAut.conj_apply, mul_smul, mul_smul, h1, hyU, tau_smul]

theorem conjSubg_sxKS_le_M24 : conjSubg tau sxKS ≤ M24g := by
  rintro σ ⟨y, hy, rfl⟩
  change MulAut.conj tau y ∈ M24g
  rw [MulAut.conj_apply]
  exact M24g.mul_mem (M24g.mul_mem tau_mem (sxGen_le_AutPerm (sxKS_le_sxGen hy)))
    (M24g.inv_mem tau_mem)

theorem isPGroup_conjSubg_sxKS : IsPGroup 2 (conjSubg tau sxKS) :=
  isPGroup_KS.map (MulAut.conj tau).toMonoidHom

theorem conjSubg_sxKS_normalized :
    ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ conjSubg tau sxKS,
      σ * n * σ⁻¹ ∈ conjSubg tau sxKS := by
  intro σ hσ hσU n hn
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
  have hτ : tau⁻¹ * σ * tau ∈ sxGen := by
    rw [← MY_stdSextet_eq]
    refine ⟨M24g.mul_mem (M24g.mul_mem (M24g.inv_mem tau_mem) hσ) tau_mem, ?_⟩
    change (tau⁻¹ * σ * tau) • stdSextet = stdSextet
    rw [mul_smul, mul_smul, tau_smul, hσU, ← tau_smul, inv_smul_smul]
  refine Subgroup.mem_map.mpr ⟨(tau⁻¹ * σ * tau) * y * (tau⁻¹ * σ * tau)⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (sxGen_le_normalizer_KS hτ) y).mp hy
  · show MulAut.conj tau ((tau⁻¹ * σ * tau) * y * (tau⁻¹ * σ * tau)⁻¹) = σ * (MulAut.conj tau y) * σ⁻¹
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

theorem card_conjSubg_sxKS :
    Nat.card ↥(conjSubg tau sxKS) = 2 ^ 6 := by
  have h : conjSubg tau sxKS = sxKS.map (MulAut.conj tau).toMonoidHom := rfl
  rw [h, Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj tau)), card_sxKS]
  norm_num

theorem K0base_eq_pCoreOf :
    K0base = pCoreOf 2 sextStab := by
  have hEq : conjSubg tau sxKS = K0base :=
    eq_K0base_of_normal (conjSubg tau sxKS) conjSubg_sxKS_le_M24 isPGroup_conjSubg_sxKS
      conjSubg_sxKS_fixes conjSubg_sxKS_normalized card_conjSubg_sxKS
  rw [pCoreOf_sextStab, ← hEq]

@[expose] def ck (i : ℕ) : S24 := tau * ks6P i * tau⁻¹

@[expose] def ckArr (i : ℕ) : Array ℕ := cArr (cArr tauArr (ks6Arr i)) tauInvArr

theorem hasArr_ck (i : ℕ) : HasArr (ck i) (ckArr i) :=
  hasArr_mul (hasArr_mul hasArr_tau (hasArr_ks6 i)) hasArr_tauInv

theorem ck_mem_pCore (i : Fin 6) :
    ck i ∈ pCoreOf 2 sextStab := by
  rw [pCoreOf_sextStab]
  exact Subgroup.mem_map.mpr ⟨ks6P i, ks6_mem_KS i, by
    show MulAut.conj tau (ks6P i) = ck i
    rw [MulAut.conj_apply]; rfl⟩

theorem ck_mem_sextStab (i : Fin 6) :
    ck i ∈ sextStab := by
  rw [sextStab_eq_conjSubg]
  exact Subgroup.mem_map.mpr ⟨ks6P i, sxKS_le_sxGen (ks6_mem_KS i), by
    show MulAut.conj tau (ks6P i) = ck i
    rw [MulAut.conj_apply]; rfl⟩

theorem rho_ck_apply (i : Fin 6)
    (m : ℕ) :
    rho11 sextStab sextStab_le ⟨ck i, ck_mem_sextStab i⟩ (toW 11 m) =
      toW 11 (act11 (ckArr i) m) := by
  rw [Loc49.rho11_sextStab_apply]
  exact rho11_toW AutPerm le_rfl ⟨ck i, sextStab_le (ck_mem_sextStab i)⟩ (hasArr_ck i) m

theorem fix_ck_masks : ∀ m < 2 ^ 11, (∀ i < 6, act11 (ckArr i) m = m) → m = 0 ∨ m = 31 := by
  decide +kernel

@[expose] def sWitWord : List ℕ := [2, 1, 2, 0, 2, 0, 1, 0, 0, 0]

@[expose] def sWit : S24 := wPerm sgList sWitWord

@[expose] def sWitArr : Array ℕ := wArr sgArrList sWitWord

theorem hasArr_sWit : HasArr sWit sWitArr := hasArr_sgWord sWitWord

theorem sWit_mem :
    sWit ∈ sextStab := sgWord_mem sWitWord

theorem sWit_one : act11 sWitArr 1 = 1 := by decide +kernel

theorem sWit_masks : ∀ m < 2 ^ 11, act11 sWitArr m = m →
    m = 0 ∨ m = 1 ∨ m = 30 ∨ m = 31 := by
  decide +kernel

@[expose] def fBasis : List ℕ := [1, 10, 46, 706, 92, 1637, 153, 776, 1330, 1385, 1396]

@[expose] def fWord (j : ℕ) : List ℕ :=
  [[], [2], [1], [0], [1, 1], [2, 2], [0, 0], [0, 1], [2, 1], [2, 0], [0, 2]].getD j []

theorem fWord_spec : ∀ j < 11, act11 (wArr sgArrList (fWord j)) 1 = fBasis.getD j 0 := by
  decide +kernel

theorem fBasis_eq_map : fBasis = (List.range 11).map (fun j => fBasis.getD j 0) := by decide

theorem sg2_fBasis_four :
    act11 sg2Arr (fBasis.getD 4 0) =
      fBasis.getD 0 0 ^^^ fBasis.getD 3 0 ^^^ fBasis.getD 4 0 ^^^ fBasis.getD 9 0 := by
  decide +kernel

theorem fBasis_reduce :
    ∀ m < 2 ^ 11, CFSG.ASVolI.H16.reduceBy (CFSG.ASVolI.H16.echelon fBasis) m = 0 := by
  decide +kernel

theorem maskSub_fBasis : maskSub 11 fBasis = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  exact toW_mem_maskSub
    (CFSG.ASVolI.H16.mem_combos_of_reduceBy_echelon fBasis m
      (fBasis_reduce m (by simpa using hm)))

private theorem toW_2038 : toW 11 2038 =
    ((toW 11 (fBasis.getD 0 0) * toW 11 (fBasis.getD 3 0)) * toW 11 (fBasis.getD 4 0)) *
      toW 11 (fBasis.getD 9 0) := by
  rw [show (2038 : ℕ) = fBasis.getD 0 0 ^^^ fBasis.getD 3 0 ^^^ fBasis.getD 4 0
    ^^^ fBasis.getD 9 0 by decide, toW_xor, toW_xor, toW_xor, mul_assoc]

theorem sextStabEndScalar_holds :
    SextStabEndScalar := by
  classical
  intro f hf w
  have hZ2 : toW 11 31 * toW 11 31 = 1 := by
    rw [← toW_xor]
    norm_num
    exact toW_zero 11
  have hf31 : f (toW 11 31) = toW 11 31 := by
    have hfix : ∀ s : ↥sextStab, rho11 sextStab sextStab_le s (f (toW 11 31)) =
        f (toW 11 31) := by
      intro s
      rw [← hf s (toW 11 31), sextStab_smul_31 s]
    obtain ⟨m, hm, hmw⟩ := toW_surj 11 (f (toW 11 31))
    have hm' : m < 2 ^ 11 := by simpa using hm
    have hgen : ∀ g ∈ sgArrList, act11 g m = m := by
      intro g hg
      have hg' : g = sg1Arr ∨ g = sg2Arr ∨ g = sgTArr := by
        simpa [sgArrList] using hg
      rcases hg' with rfl | rfl | rfl
      · have h := hfix ⟨sg1, sg1_mem⟩
        rw [← hmw, Loc49.rho11_sextStab_apply,
          rho11_toW AutPerm le_rfl ⟨sg1, sextStab_le sg1_mem⟩ hasArr_sg1 m] at h
        exact toW_inj (act11_lt _ _) hm' h
      · have h := hfix ⟨sg2, sg2_mem⟩
        rw [← hmw, Loc49.rho11_sextStab_apply,
          rho11_toW AutPerm le_rfl ⟨sg2, sextStab_le sg2_mem⟩ hasArr_sg2 m] at h
        exact toW_inj (act11_lt _ _) hm' h
      · have h := hfix ⟨sgT, sgT_mem⟩
        rw [← hmw, Loc49.rho11_sextStab_apply,
          rho11_toW AutPerm le_rfl ⟨sgT, sextStab_le sgT_mem⟩ hasArr_sgT m] at h
        exact toW_inj (act11_lt _ _) hm' h
    rcases fix_gens_masks m hm' hgen with rfl | rfl
    · exfalso
      rw [toW_zero] at hmw
      have h1 : toW 11 31 = 1 := by
        refine f.injective ?_
        rw [← hmw]
        exact (map_one f).symm
      refine absurd (toW_inj (n := 11) (by norm_num : 31 < 2 ^ 11) (by norm_num : 0 < 2 ^ 11)
        (by rw [h1, toW_zero])) ?_
      norm_num
    · exact hmw.symm
  have hV : rho11 sextStab sextStab_le ⟨sWit, sWit_mem⟩ (toW 11 1) = toW 11 1 := by
    rw [Loc49.rho11_sextStab_apply,
      rho11_toW AutPerm le_rfl ⟨sWit, sextStab_le sWit_mem⟩ hasArr_sWit 1, sWit_one]
  have hcontra : f (toW 11 1) = toW 11 1 * toW 11 31 → False := by
    intro h30
    have hbase : ∀ j < 11, f (toW 11 (fBasis.getD j 0)) =
        toW 11 (fBasis.getD j 0) * toW 11 31 := by
      intro j hj
      have hb : toW 11 (fBasis.getD j 0) =
          rho11 sextStab sextStab_le ⟨wPerm sgList (fWord j), sgWord_mem (fWord j)⟩ (toW 11 1) := by
        rw [Loc49.rho11_sextStab_apply,
          rho11_toW AutPerm le_rfl
            ⟨wPerm sgList (fWord j), sextStab_le (sgWord_mem (fWord j))⟩
            (hasArr_sgWord (fWord j)) 1, fWord_spec j hj]
      rw [hb, hf, h30, map_mul, sextStab_smul_31, ← hb]
    have hfour : (toW 11 (fBasis.getD 0 0) * toW 11 31) *
        (toW 11 (fBasis.getD 3 0) * toW 11 31) *
        (toW 11 (fBasis.getD 4 0) * toW 11 31) *
        (toW 11 (fBasis.getD 9 0) * toW 11 31) =
        ((toW 11 (fBasis.getD 0 0) * toW 11 (fBasis.getD 3 0)) *
          toW 11 (fBasis.getD 4 0)) * toW 11 (fBasis.getD 9 0) := by
      calc _ = ((toW 11 (fBasis.getD 0 0) * toW 11 (fBasis.getD 3 0)) *
            toW 11 (fBasis.getD 4 0)) * toW 11 (fBasis.getD 9 0) *
            ((toW 11 31 * toW 11 31) * (toW 11 31 * toW 11 31)) := by ac_rfl
        _ = _ := by rw [hZ2, mul_one, mul_one]
    have hfu1 : f (toW 11 2038) = toW 11 2038 * toW 11 31 := by
      have hb : toW 11 (fBasis.getD 4 0) =
          rho11 sextStab sextStab_le ⟨wPerm sgList (fWord 4), sgWord_mem (fWord 4)⟩
            (toW 11 1) := by
        rw [Loc49.rho11_sextStab_apply,
          rho11_toW AutPerm le_rfl
            ⟨wPerm sgList (fWord 4), sextStab_le (sgWord_mem (fWord 4))⟩
            (hasArr_sgWord (fWord 4)) 1, fWord_spec 4 (by norm_num)]
      have hsg2 : rho11 sextStab sextStab_le ⟨sg2, sg2_mem⟩ (toW 11 (fBasis.getD 4 0)) =
          toW 11 2038 := by
        rw [Loc49.rho11_sextStab_apply,
          rho11_toW AutPerm le_rfl ⟨sg2, sextStab_le sg2_mem⟩ hasArr_sg2 (fBasis.getD 4 0),
          show act11 sg2Arr (fBasis.getD 4 0) = 2038 by
            rw [sg2_fBasis_four]; rfl]
      calc f (toW 11 2038)
          = f (rho11 sextStab sextStab_le ⟨sg2, sg2_mem⟩ (toW 11 (fBasis.getD 4 0))) := by
            rw [hsg2]
        _ = rho11 sextStab sextStab_le ⟨sg2, sg2_mem⟩
              (f (toW 11 (fBasis.getD 4 0))) := hf _ _
        _ = rho11 sextStab sextStab_le ⟨sg2, sg2_mem⟩
              (toW 11 (fBasis.getD 4 0) * toW 11 31) := by rw [hbase 4 (by norm_num)]
        _ = rho11 sextStab sextStab_le ⟨sg2, sg2_mem⟩ (toW 11 (fBasis.getD 4 0)) *
              rho11 sextStab sextStab_le ⟨sg2, sg2_mem⟩ (toW 11 31) := map_mul _ _ _
        _ = toW 11 2038 * toW 11 31 := by rw [hsg2, sextStab_smul_31]
    have hfu2 : f (toW 11 2038) = toW 11 2038 := by
      rw [toW_2038, map_mul, map_mul, map_mul, hbase 0 (by norm_num), hbase 3 (by norm_num),
        hbase 4 (by norm_num), hbase 9 (by norm_num)]
      exact hfour
    have hZ1 : toW 11 31 = 1 := by
      have h := hfu1
      rw [hfu2] at h
      have h2 := congrArg (fun x => (toW 11 2038)⁻¹ * x) h
      simpa [mul_assoc] using h2.symm
    have h31 : (31 : ℕ) = 0 :=
      toW_inj (n := 11) (by norm_num : 31 < 2 ^ 11) (by norm_num : 0 < 2 ^ 11)
        (by rw [hZ1, toW_zero])
    norm_num at h31
  have hfV : f (toW 11 1) = toW 11 1 := by
    obtain ⟨m, hm, hmw⟩ := toW_surj 11 (f (toW 11 1))
    have hm' : m < 2 ^ 11 := by simpa using hm
    have hfixm : act11 sWitArr m = m := by
      have h := hf ⟨sWit, sWit_mem⟩ (toW 11 1)
      rw [hV, ← hmw, Loc49.rho11_sextStab_apply,
        rho11_toW AutPerm le_rfl ⟨sWit, sextStab_le sWit_mem⟩ hasArr_sWit m] at h
      exact (toW_inj hm' (act11_lt _ _) h).symm
    rcases sWit_masks m hm' hfixm with rfl | rfl | rfl | rfl
    · exfalso
      rw [toW_zero] at hmw
      have h1 : (toW 11 1 : W11) = 1 := by
        refine f.injective ?_
        rw [← hmw]
        exact (map_one f).symm
      refine absurd (toW_inj (n := 11) (by norm_num : 1 < 2 ^ 11) (by norm_num : 0 < 2 ^ 11)
        (by rw [h1, toW_zero])) ?_
      norm_num
    · exact hmw.symm
    · exfalso
      exact hcontra (by rw [← hmw, show (30 : ℕ) = 1 ^^^ 31 by norm_num, toW_xor])
    · exfalso
      have h1 : (toW 11 1 : W11) = toW 11 31 := f.injective (by rw [← hmw, hf31])
      refine absurd (toW_inj (n := 11) (by norm_num : 1 < 2 ^ 11) (by norm_num : 31 < 2 ^ 11)
        h1) ?_
      norm_num
  have hbase : ∀ j < 11, f (toW 11 (fBasis.getD j 0)) = toW 11 (fBasis.getD j 0) := by
    intro j hj
    have hb : toW 11 (fBasis.getD j 0) =
        rho11 sextStab sextStab_le ⟨wPerm sgList (fWord j), sgWord_mem (fWord j)⟩ (toW 11 1) := by
      rw [Loc49.rho11_sextStab_apply,
        rho11_toW AutPerm le_rfl ⟨wPerm sgList (fWord j), sextStab_le (sgWord_mem (fWord j))⟩
          (hasArr_sgWord (fWord j)) 1, fWord_spec j hj]
    rw [hb, hf, hfV]
  let U : Subgroup W11 :=
    { carrier := {v | f v = v}
      one_mem' := map_one f
      mul_mem' := fun {a b} ha hb => by
        show f (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show f a⁻¹ = a⁻¹
        rw [W11_inv]
        exact ha }
  have hgen : ∀ a ∈ fBasis, toW 11 a ∈ U := by
    intro a ha
    rw [fBasis_eq_map] at ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact hbase j (List.mem_range.mp hj)
  have hle : maskSub 11 fBasis ≤ U := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.mp hv
    exact MaskCoords.vm_mem_of_combos (MaskCoords.std 11) U hgen m hm
  have htop : (⊤ : Subgroup W11) ≤ U := by rw [← maskSub_fBasis]; exact hle
  exact htop (Subgroup.mem_top w)

theorem sextStabOffender_holds :
    SextStabOffender := by
  classical
  intro B hBnorm hB2 hBne
  let N : Subgroup S24 := B.map sextStab.subtype
  have hNM : N ≤ M24g := by
    rintro _ ⟨b, -, rfl⟩
    exact sextStab_le b.2
  have hN2 : IsPGroup 2 N := hB2.map sextStab.subtype
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hBne
    refine le_antisymm ?_ bot_le
    intro b hb
    rw [Subgroup.mem_bot]
    have hb' : (b : S24) ∈ N := ⟨b, hb, rfl⟩
    rw [hbot] at hb'
    exact Subtype.ext (by simpa using hb')
  have hnorm : ∀ σ ∈ M24g, σ • sextFin 0 = sextFin 0 → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N := by
    intro σ hσ hσU n hn
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hn
    have hσS : σ ∈ sextStab :=
      Subgroup.mem_inf.mpr ⟨hσ, MulAction.mem_stabilizer_iff.mpr hσU⟩
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσS⟩ * b * ⟨σ, hσS⟩⁻¹,
      hBnorm.conj_mem b hb ⟨σ, hσS⟩, rfl⟩
  have hNK : N = K0base := by
    rcases normal_two_subgroup_of_base_sextet N hNM hN2 hnorm with h | h
    · exact absurd h hNne
    · exact h
  have hcardN : Nat.card ↥N = Nat.card ↥B :=
    Subgroup.card_map_of_injective (f := sextStab.subtype) (fun a b h => Subtype.ext h)
  have hcardB : Nat.card ↥B = 64 := by
    rw [← hcardN, hNK, card_K0base]
    norm_num
  have hfix : ∀ w : W11, (∀ b ∈ B, rho11 sextStab sextStab_le b w = w) → w = 1 ∨ w = toW 11 31 := by
    intro w hw
    obtain ⟨m, hm, hmw⟩ := toW_surj 11 w
    have hm' : m < 2 ^ 11 := by simpa using hm
    have hgen : ∀ i < 6, act11 (ckArr i) m = m := by
      intro i hi
      have hmem : ck i ∈ N := by
        rw [hNK, K0base_eq_pCoreOf]
        exact ck_mem_pCore ⟨i, hi⟩
      obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.mp hmem
      have hb_eq : b = ⟨ck i, ck_mem_sextStab ⟨i, hi⟩⟩ := Subtype.ext hbval
      have h := hw b hb
      rw [hb_eq, ← hmw, rho_ck_apply ⟨i, hi⟩] at h
      exact toW_inj (act11_lt _ _) hm' h
    rcases fix_ck_masks m hm' hgen with rfl | rfl
    · left
      rw [← hmw]
      exact toW_zero 11
    · right
      exact hmw.symm
  have hbound : Nat.card {w : W11 // ∀ b ∈ B, rho11 sextStab sextStab_le b w = w} ≤ 2 := by
    have hsub : {w : W11 | ∀ b ∈ B, rho11 sextStab sextStab_le b w = w} ⊆
        ({1, toW 11 31} : Set W11) := by
      intro w hw
      rcases hfix w hw with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    have hne : (1 : W11) ≠ toW 11 31 := by
      intro h
      have h' : (1 : W11) = toW 11 0 := (toW_zero 11).symm
      rw [h'] at h
      have := toW_inj (n := 11) (by norm_num : 0 < 2 ^ 11) (by norm_num : 31 < 2 ^ 11) h
      norm_num at this
    change Nat.card ↥({w : W11 | ∀ b ∈ B, rho11 sextStab sextStab_le b w = w} : Set W11) ≤ 2
    rw [Nat.card_coe_set_eq]
    calc ({w : W11 | ∀ b ∈ B, rho11 sextStab sextStab_le b w = w} : Set W11).ncard
        ≤ ({1, toW 11 31} : Set W11).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 := Set.ncard_pair hne
  calc Nat.card {w : W11 // ∀ b ∈ B, rho11 sextStab sextStab_le b w = w} * Nat.card ↥B
      ≤ 2 * 64 := Nat.mul_le_mul hbound (le_of_eq hcardB)
    _ < 2 ^ 11 := by norm_num

end CFSG.Quasithin.H13.AS91.M24G
