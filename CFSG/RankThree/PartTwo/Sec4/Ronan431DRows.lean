module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431DChev
public import CFSG.RankThree.PartTwo.Sec4.Ronan431Open

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan431
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs PSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.LocalAnalysis.GLTheoremA (KDChevDownQ)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType)
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem rowSOf431_of_isChevSimple (hb : LieOrderBridge) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hD : KDChevDownQ 3 p) {T : TauCeti.CFSGIndex → Prop}
    (hT : ∀ (X : Type) [Group X] [Finite X], catalogIs X T → Nat.card X = 360)
    (hB : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS431 S A σ K →
        CompOfType S σ T)
    {X : Type} [Group X] (hX : IsChevSimple p X) : RowSOf431 X :=
  fun S _ _ hs hna ⟨e⟩ => (noCfgS431_of_isChevSimple hb hp hp3 hD hT hs hna
    (CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv e hX) (hB S hs hna)).rowS431

theorem rowSOf431_alt_of_not_dvd {T : TauCeti.CFSGIndex → Prop}
    (hT : ∀ (X : Type) [Group X] [Finite X], catalogIs X T → Nat.card X = 360)
    (hB : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS431 S A σ K →
        CompOfType S σ T)
    {n : ℕ} (hn : 5 ≤ n) (h6 : ¬ 3 ∣ n - 6) : RowSOf431 (alternatingGroup (Fin n)) := by
  intro S _ _ hs hna ⟨e⟩
  haveI := hs
  have hsA : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
  have hnaA : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  exact (NoCfgS431.of_mulEquiv e
    (noCfgS431_alt_of_not_dvd hT hn h6 (hB _ hsA hnaA))).rowS431

end CFSG.RankThree.PartTwo.Sec4.Ronan431D

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG.RankThree.PartTwo.Sec4.Ronan431D
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.LocalAnalysis.GLTheoremA (KDChevDownQ)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType)

theorem k431OpenD_of_bridge (hb : LieOrderBridge) (hD : ∀ q, KDChevDownQ 3 q)
    {T : TauCeti.CFSGIndex → Prop}
    (hT : ∀ (X : Type) [Group X] [Finite X], catalogIs X T → Nat.card X = 360)
    (hB : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS431 S A σ K →
        CompOfType S σ T) :
    K431OpenD where
  four_SL_mod_one p _ hp3 _ := rowSOf431_of_isChevSimple hb Fact.out hp3 (hD p) hT hB
    (isChevSimple_projSL_four p (by omega))
  four_SU_mod_two p _ hp3 _ := rowSOf431_of_isChevSimple hb Fact.out hp3 (hD p) hT hB
    (isChevSimple_projSU_four p)
  five_ten := rowSOf431_alt_of_not_dvd hT hB (by norm_num) (by norm_num)
  five_eleven := rowSOf431_alt_of_not_dvd hT hB (by norm_num) (by norm_num)

end CFSG.RankThree.PartTwo.Sec4.Ronan431
