module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA6
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL)

theorem false_of_psl2 {F : Type} [Field F] [Finite F] {r f : ℕ} [Fact r.Prime] (hr : r ≠ 3)
    (hF : Nat.card F = r ^ f) {X : Type} [Group X] [Finite X]
    (φ : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) {P : Subgroup X} (hP : IsA6Sub P) :
    False := by
  obtain ⟨R, -, hR, hR9, -⟩ := hP.exists_elemAbelian_nine
  haveI : NeZero ((3 : ℕ) : F) := ⟨by
    have := Sec4.three_ne_zero_of_card Fact.out hr hF
    exact_mod_cast this⟩
  have hle := RankThree.PartOne.K133.psl2_elemAb_card_le (K := F) Nat.prime_three (by norm_num)
    (R.map φ.toMonoidHom)
    (isElemAbelian_iff_isElementaryAbelian.mp (Sec4.isElemAbelian_map φ.toMonoidHom hR))
  rw [Subgroup.card_map_of_injective φ.injective, hR9] at hle
  omega

theorem false_of_projSL2 {X : Type} [Group X] [Finite X] {r f : ℕ} [Fact r.Prime] (hr : r ≠ 3)
    (hf : 1 ≤ f) (φ : X ≃* projSL 2 (GaloisField r f)) {P : Subgroup X} (hP : IsA6Sub P) :
    False :=
  false_of_psl2 (F := GaloisField r f) hr (GaloisField.card r f (by omega))
    (φ.trans (Sec4.projSLEquivPSL _)) hP

end CFSG.RankThree.PartTwo.Sec8.Hering611R
