module

public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Quasithin.Recognition.M12AmalAutData
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv

@[expose] def tl (i : ℕ) : List ℕ := telTab.getD i []

@[expose] def gl (k : ℕ) : List ℕ := genTab.getD k []

@[expose] def gil (k : ℕ) : List ℕ := genInvTab.getD k []

@[expose] def idl : List ℕ := List.range 24

theorem tl_inj_chk : ∀ i < 128, ∀ j < 128, tl i = tl j → i = j := by decide +kernel

theorem hg_chk : ∀ i' < 128, ∀ i < 128,
    compL (compL (dTab.getD 14 []) (tl i')) (dInvTab.getD 14 []) = tl i → tl i = idl := by
  decide +kernel

theorem a_ne_one_chk : gl 0 ≠ idl := by decide +kernel

theorem x_ne_one_chk : gl 3 ≠ idl := by decide +kernel

theorem y_ne_one_chk : gl 4 ≠ idl := by decide +kernel

theorem xN_chk : ∀ i' < 128, compL (compL (gl 3) (tl 1)) (gil 3) ≠ tl i' := by decide +kernel

theorem yN_chk : ∀ i' < 128, compL (compL (gl 4) (tl 2)) (gil 4) ≠ tl i' := by decide +kernel

theorem z_ne_one_chk : tl 111 ≠ idl := by decide +kernel

theorem z_comm_chk : ∀ k < 4, compL (gl k) (tl 111) = compL (tl 111) (gl k) := by decide +kernel

theorem U_norm_chk : ∀ k ∈ [0, 1, 2, 4], ∀ j ∈ [111, 36, 106],
    compL (compL (gl k) (tl j)) (gil k) ∈ [tl 111, tl 36, tl 106] ∧
      compL (compL (gil k) (tl j)) (gl k) ∈ [tl 111, tl 36, tl 106] := by decide +kernel

end CFSG.Quasithin.M12AmalAut
