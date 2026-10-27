module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMClose
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMKill
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMTrans

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

inductive CStat where
  | five (u n c a b : List ℕ)
  | conj (t : List ℕ) (k : ℕ)
  | k761 (j : ℕ)
  | k763 (j : ℕ)
  | ko2 (j : ℕ) (w : List (List ℕ)) (e : List ℕ)

@[expose] def KData.dflt : KData := ⟨[], [], 0, [], [], 0, [], [], 0, []⟩

@[expose] def CStatChk (tLit t0Lit : List (List ℕ)) (Ks : List KData) (tops : List ℕ)
    (subs : List (List (List ℕ))) (stats : List CStat) (W : List (List ℕ)) : CStat → Bool
  | .five u n c a b => FiveChk tLit t0Lit W u n c a b
  | .conj t k => tLit.contains t && decide (k < subs.length) &&
      NFA6.Core.setEq W ((subs.getD k []).map (cconj t)) &&
      (match stats.getD k (.k761 0) with
        | .five u n c a b => FiveChk tLit t0Lit (subs.getD k []) u n c a b
        | _ => false)
  | .k761 j => tops.contains j && decide (j < Ks.length) && W.all tLit.contains &&
      !(W.all (Ks.getD j KData.dflt).qLit.contains) &&
      W.length != 2 * (W.filter (Ks.getD j KData.dflt).qLit.contains).length &&
      FaithChk (Ks.getD j KData.dflt) W
  | .k763 j => tops.contains j && decide (j < Ks.length) && W.all tLit.contains &&
      !(W.all (Ks.getD j KData.dflt).qLit.contains) &&
      K763Chk (Ks.getD j KData.dflt) W && FaithChk (Ks.getD j KData.dflt) W
  | .ko2 j w e => decide (j < Ks.length) && W.all (Ks.getD j KData.dflt).qLit.contains &&
      W.contains e && NonormChk tLit (Ks.getD j KData.dflt) w e

variable {i : Fin 4}

structure KList (i : Fin 4) (tLit : List (List ℕ)) (Ks : List KData) (tops : List ℕ) : Prop where
  enum : ∀ j < Ks.length, KEnum (Ks.getD j KData.dflt)
  chk : ∀ j < Ks.length, KChk tLit (Ks.getD j KData.dflt) = true
  o2 : ∀ j < Ks.length, ∃ ws, O2Chk (Ks.getD j KData.dflt) ws = true
  top : ∀ j ∈ tops, Sx i (Ks.getD j KData.dflt) = Tb i

abbrev CloseDisj (i : Fin 4) (U : Subgroup ↥(GB i)) : Prop :=
  (∃ H R Lh : Subgroup ↥(GB i), FiveWit (L1b i) (L2b i) (Tb i) U H R Lh) ∨
    ∃ K Y : Subgroup ↥(GB i), KillWit (L1b i) (L2b i) (Tb i) U K Y

theorem xdesc_eq {U V : Subgroup ↥(GB i)} {W W' : List (List ℕ)} (hU : XDesc U W)
    (hV : XDesc V W') (h : ∀ c, c ∈ W ↔ c ∈ W') : U = V := by
  ext x
  rw [hU.mem, hV.mem, h]

section Main

variable {tLit t0Gen t0Lit : List (List ℕ)} (hT : LDesc (TB i) tLit) (h0 : T0Data tLit t0Gen t0Lit)
  (hTp : IsPGroup 2 (Tb i)) (hTP : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true)
  {Ks : List KData} {tops : List ℕ} (hK : KList i tLit Ks tops)
include hT h0 hTp hTP

omit h0 hTP in
theorem killWit_of_top {D : KData} (hE : KEnum D) (hC : KChk tLit D = true)
    {ws : List (List (List ℕ))} (hO2 : O2Chk D ws = true) (hST : Sx i D = Tb i)
    {U : Subgroup ↥(GB i)} (hUT : U ≤ Tb i) (hUQ : ¬ U ≤ Qx i D)
    (hkill : Kill761 U (Kx i D) ∨ Kill763 U (Kx i D)) :
    KillWit (L1b i) (L2b i) (Tb i) U (Kx i D) (Yx i D) where
  le := hUT.trans (hST ▸ le_sup_right)
  irr := twoPTwoIrred_Kx hT hE hC hTp
  nonorm := (sevenWit_of_top hT hE hC hTp hST hO2 hUT hUQ).nonorm
  good := exists_good_Kx hT hE hC
  kill := Or.inr hkill

include hK in
theorem close_of_stat {subs : List (List (List ℕ))} {stats : List CStat} {W : List (List ℕ)}
    {U : Subgroup ↥(GB i)} (hU : XDesc U W) (hnd : W.Nodup) (hUT : U ≤ Tb i) (st : CStat)
    (hst : CStatChk tLit t0Lit Ks tops subs stats W st = true)
    (hsubs : ∀ k < subs.length, cid ∈ subs.getD k [] ∧ (∀ c ∈ subs.getD k [], c ∈ tLit) ∧
      (subs.getD k []).Nodup ∧
      ∀ c ∈ subs.getD k [], ∀ d ∈ subs.getD k [], Core.cmul c d ∈ subs.getD k []) :
    CloseDisj i U := by
  have hTd : XDesc (Tb i) tLit := ⟨mem_Tb_iff i hT, fun c hc => exists_Tb i hT hc⟩
  cases st with
  | five u n c a b =>
    exact Or.inl ⟨_, _, _, fiveWit_of_chk hT h0 hTp hU hnd hst⟩
  | conj t k =>
    simp only [CStatChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hst
    obtain ⟨⟨⟨htT, hk⟩, hseq⟩, hfive⟩ := hst
    obtain ⟨tX, htX, rfl⟩ := exists_Tb i hT htT
    obtain ⟨h1, h2, h3, h4⟩ := hsubs k hk
    set U0 := xsub i (subs.getD k []) h1 h4
    have hU0 : XDesc U0 (subs.getD k []) := xdesc_xsub hTd h1 h2 h4
    have hc0 : CloseDisj i U0 := by
      revert hfive
      cases hst' : stats.getD k (.k761 0) with
      | five u n c a b =>
        intro hfive
        exact Or.inl ⟨_, _, _, fiveWit_of_chk hT h0 hTp hU0 h3 hfive⟩
      | _ => intro hfive; exact absurd hfive (by simp)
    have heq : U = U0.map (MulAut.conj tX).toMonoidHom :=
      xdesc_eq hU (xdesc_map_conj i hU0 tX) (setEq_mem' hseq)
    rw [heq]
    exact close_conj i hTP htX hc0
  | k761 j =>
    simp only [CStatChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      Bool.not_eq_true', bne_iff_ne, ne_eq] at hst
    obtain ⟨⟨⟨⟨⟨htop, hj⟩, -⟩, hnq⟩, hidx⟩, hf⟩ := hst
    obtain ⟨ws, hO2⟩ := hK.o2 j hj
    have hST := hK.top j htop
    have hE := hK.enum j hj
    have hC := hK.chk j hj
    have hUQ : ¬ U ≤ Qx i (Ks.getD j KData.dflt) := by
      intro hle
      have hall : W.all (Ks.getD j KData.dflt).qLit.contains = true := by
        rw [List.all_eq_true]
        intro c hc
        obtain ⟨x, hx, rfl⟩ := hU.surj c hc
        exact List.contains_iff_mem.2 ((hE.q.mem _).1 (hle hx))
      rw [hall] at hnq
      exact Bool.noConfusion hnq
    refine Or.inr ⟨_, _, killWit_of_top hT hTp hE hC hO2 hST hUT hUQ
      (Or.inl (kill761_of_chk hT hE hC hTp hO2 hU hnd (hUT.trans (hST ▸ le_sup_right)) hidx hf))⟩
  | k763 j =>
    simp only [CStatChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      Bool.not_eq_true'] at hst
    obtain ⟨⟨⟨⟨⟨htop, hj⟩, -⟩, hnq⟩, h763⟩, hf⟩ := hst
    obtain ⟨ws, hO2⟩ := hK.o2 j hj
    have hST := hK.top j htop
    have hE := hK.enum j hj
    have hC := hK.chk j hj
    have hUQ : ¬ U ≤ Qx i (Ks.getD j KData.dflt) := by
      intro hle
      have hall : W.all (Ks.getD j KData.dflt).qLit.contains = true := by
        rw [List.all_eq_true]
        intro c hc
        obtain ⟨x, hx, rfl⟩ := hU.surj c hc
        exact List.contains_iff_mem.2 ((hE.q.mem _).1 (hle hx))
      rw [hall] at hnq
      exact Bool.noConfusion hnq
    refine Or.inr ⟨_, _, killWit_of_top hT hTp hE hC hO2 hST hUT hUQ
      (Or.inr (kill763_of_chk hT hE hC hTp hO2 hU hnd (hUT.trans (hST ▸ le_sup_right)) h763 hf))⟩
  | ko2 j w e =>
    simp only [CStatChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      List.all_eq_true] at hst
    obtain ⟨⟨⟨hj, hWq⟩, he⟩, hnn⟩ := hst
    obtain ⟨ws, hO2⟩ := hK.o2 j hj
    have hE := hK.enum j hj
    have hC := hK.chk j hj
    have hUQ : U ≤ Qx i (Ks.getD j KData.dflt) := fun x hx =>
      (hE.q.mem _).2 (hWq _ ((hU.mem x).1 hx))
    obtain ⟨eX, heU, rfl⟩ := hU.surj e he
    refine Or.inr ⟨_, _,
      { le := hUQ.trans ((Qx_le_Sx hT hE hC).trans le_sup_right)
        irr := twoPTwoIrred_Kx hT hE hC hTp
        nonorm := nonorm_of_chk hT hE hC hTp heU hnn
        good := exists_good_Kx hT hE hC
        kill := Or.inl (hUQ.trans (Qx_le_pCoreOf hT hE hC)) }⟩

end Main

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
