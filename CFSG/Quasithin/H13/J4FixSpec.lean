
module

public import Certificates.Data.CFSGNative.H13.J4Fix
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.J4.Action

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

theorem orbFixCount_spec (keys : ByteArray) (tab : Array V2) (n : ℕ) :
    Native.orbFixCount keys tab n =
      ((Finset.range n).filter fun i => Native.fixedAt keys tab i = true).card := by
  induction n with
  | zero => simp [Native.orbFixCount]
  | succ n ih =>
    have e : Native.orbFixCount keys tab (n + 1) = if Native.fixedAt keys tab n = true then
        Native.orbFixCount keys tab n + 1 else Native.orbFixCount keys tab n := by
      simp only [Native.orbFixCount, Nat.fold_succ]
    rw [e, ih, Finset.range_add_one, Finset.filter_insert]
    have hn : n ∉ (Finset.range n).filter fun i => Native.fixedAt keys tab i = true := by simp
    by_cases h : Native.fixedAt keys tab n = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h),
        Finset.card_insert_of_notMem hn]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem card_filter_fin (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i : Fin n => p i.val).card = ((Finset.range n).filter p).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi, i.isLt]
  · intro i _ j _ h
    exact Fin.ext h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨⟨k, hk.1⟩, by simp [hk.2], rfl⟩

theorem u_mem_J : u ∈ J := by
  rw [u_eq_wordProd]
  exact wordProd_mem J baseGL_mem _

theorem v_mem_J : v ∈ J := by
  rw [v_eq_wordProd]
  exact wordProd_mem J baseGL_mem _

theorem W_le_J : W ≤ J := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact u_mem_J
  · exact v_mem_J

theorem t_mem_J : t ∈ J := W_le_J t_mem_W

@[expose] def tJ : J := ⟨t, t_mem_J⟩

theorem tJ_coe : (tJ : GL (Fin 112) (ZMod 2)) = t := rfl

theorem rowsMatrix_tInvRows : rowsMatrix Native.tInvRows =
    ((t⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  prRep_t.2

theorem tJ_smul_vecAt (i : ℕ) :
    tJ • vecAt i = toRow (frApply (frTable Native.tInvRows) (rdV2 bs0.keys i)).toVec := by
  rw [← ofRow_inj, smul_row, vecAt, frApply_toVec_eq_vecMul, rowsMatrix_tInvRows]
  rfl

end CFSG.Quasithin.H13.J4
