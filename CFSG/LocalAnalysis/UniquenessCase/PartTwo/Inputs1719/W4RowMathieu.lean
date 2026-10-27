module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.Sporadic.Schreier CFSG.Blueprint

namespace W4Row

theorem m11_closure_conjSet_orderOf_eleven
    (B : Subgroup NativeSporadic.M11) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List NativeSporadic.M11, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (X1.conjSet cs (B : Set NativeSporadic.M11)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨cs, hcs, htop⟩ := m11_gen b (hsq b hbB) hb1'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := NativeSporadic.M11) 11
    (by rw [m11_card]; norm_num)
  refine ⟨cs, hcs, x, ?_, hx⟩
  have hle : Subgroup.closure {y | ∃ c ∈ cs, y = c * b * c⁻¹} ≤
      Subgroup.closure (X1.conjSet cs (B : Set NativeSporadic.M11)) := by
    apply Subgroup.closure_mono
    rintro y ⟨c, hc, rfl⟩
    exact ⟨c, hc, b, hbB, rfl⟩
  exact hle (htop ▸ Subgroup.mem_top x)

end W4Row

theorem w4Thm11_1RowM_M11_holds :
    W4Thm11_1RowM .M11 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : CQ L ≃* NativeSporadic.M11 := e₀
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e m11_autInner
  show 4 ≤ E3.mParam Y
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact W4Row.le_mParam_of_gen hW hO2 (fun t ht _ => hYL.le ht) e (k := 3) (p := 11)
    (by norm_num) (by norm_num) (by rw [m11_card]; norm_num)
    (by rw [orderOf_two_zmod_11]; norm_num) W4Row.m11_closure_conjSet_orderOf_eleven

theorem w4Thm11_1RowM_M12_holds :
    W4Thm11_1RowM .M12 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : CQ L ≃* S12 := e₀
  show 4 ≤ E3.mParam Y
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact W4Row.le_mParam_of_gen_out2 hW hLY hLn hF hq hO2 e m12_center_eq_bot' m12_mulAut_card
    (k := 3) (p := 11) (q := 11) (by norm_num) (by norm_num) (by norm_num)
    (by rw [m12_card]; norm_num) (by rw [orderOf_two_zmod_11]; norm_num)
    (by rw [orderOf_two_zmod_11]; norm_num) m12_gen1 m12_outer_dihedral

theorem w4Thm11_1RowM_M23_holds :
    W4Thm11_1RowM .M23 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : CQ L ≃* S23 := e₀
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e m23_autInner
  show 4 ≤ E3.mParam Y
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact W4Row.le_mParam_of_gen hW hO2 (fun t ht _ => hYL.le ht) e (k := 3) (p := 11)
    (by norm_num) (by norm_num) (by rw [m23_card]; norm_num)
    (by rw [orderOf_two_zmod_11]; norm_num) m23_gen1

theorem w4Thm11_1RowM_M24_holds :
    W4Thm11_1RowM .M24 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : CQ L ≃* S24 := e₀
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e
    (autInner_of_card_le m24_center_eq_bot' m24_mulAut_card)
  show 4 ≤ E3.mParam Y
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact W4Row.le_mParam_of_gen hW hO2 (fun t ht _ => hYL.le ht) e (k := 3) (p := 11)
    (by norm_num) (by norm_num) (by rw [m24_card]; norm_num)
    (by rw [orderOf_two_zmod_11]; norm_num) m24_gen1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
