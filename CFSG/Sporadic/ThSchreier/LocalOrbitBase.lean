
module

public import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem toVec_localRowV4 (i : ℕ) : toRow (localRowV4 i).toVec = localRow i := by
  rw [localRowV4, toVec_v4OfNat]
  rfl

theorem localOmega_finite : localOmega.Finite := by
  have : localOmega = (fun i : Fin 2457 => localRow i) '' Set.univ := by
    ext v
    simp only [localOmega, Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
    exact ⟨fun ⟨i, hi, he⟩ => ⟨⟨i, hi⟩, he⟩, fun ⟨i, he⟩ => ⟨i, i.isLt, he⟩⟩
  rw [this]
  exact Set.toFinite _

theorem planeW_coe : (planeW : Set RowV) = {0, wRow1, wRow2, wRow1 + wRow2} := span_pair_eq _ _

theorem rowPlane_wKeyRow : rowPlane wKeyRow = planeW := by
  rw [planeW_coe, wKeyRow, rowPlane_canon, toVec_v4OfNat, toVec_v4OfNat]
  rfl

theorem wRow1_ne_zero : wRow1 ≠ 0 := by
  intro h
  have h' : rowOfNat 0xb9318bc60b06215ff4eb15e228ba41526fe75848bd0133807208caa1fa8551 =
      rowOfNat 0 := by rw [rowOfNat_zero]; exact h
  exact absurd (rowOfNat_injective (by norm_num) (by norm_num) h') (by norm_num)

theorem wRow2_ne_zero : wRow2 ≠ 0 := by
  intro h
  have h' : rowOfNat 0x1e1057aa10c4abdf6972134ec61140ccf2027af03f80a7ed5002b65e4b1cca =
      rowOfNat 0 := by rw [rowOfNat_zero]; exact h
  exact absurd (rowOfNat_injective (by norm_num) (by norm_num) h') (by norm_num)

theorem wRow1_ne_wRow2 : wRow1 ≠ wRow2 := by
  intro h
  exact absurd (rowOfNat_injective (by norm_num) (by norm_num) h) (by norm_num)

theorem finrank_planeW : Module.finrank (ZMod 2) planeW = 2 :=
  finrank_span_pair_of_ne wRow1_ne_zero wRow2_ne_zero wRow1_ne_wRow2

end CFSG.Sporadic.ThSchreier
