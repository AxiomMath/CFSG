module

public import CFSG.RankThree.PartOne.KFCL.SpGen
public import CFSG.RankThree.PartOne.KFCL.SpDerived

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [CharP K 2] {p : ℕ}

theorem exists_spRoot [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p)
    (h4 : 4 ≤ Nat.card K) : ∃ R : RootData p (spTorus p 3 K), R.GenBlocks := by
  have hW : spWeyl 3 K ≤ Subgroup.normalizer (spTorus p 3 K : Set (StatedSp 3 K)) := spWeyl_le_normalizer
  have hne := not_le_centralizer_of_std hW (hne_std hp hp5 hζ)
  have hinj := hinj_of_std hW (hred_Sp hp hp5 hζ)
  have hder : ∀ S : Subgroup (StatedSp 3 K), S ≤ spTorus p 3 K →
      (S.relIndex (spTorus p 3 K) = p ∨
        ∃ e : StatedSp 3 K, e ∈ spTorus p 3 K ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) →
      ⁅Subgroup.centralizer (S : Set (StatedSp 3 K)), Subgroup.centralizer (S : Set (StatedSp 3 K))⁆ ≤
        ⨆ B : {B : ↥(blockOrbit (spWeyl 3 K) (SpStd K)) //
          S ≤ spTorus p 3 K ⊓ Subgroup.centralizer (B.1 : Set (StatedSp 3 K))}, B.1.1 :=
    fun S hST hshape => derived_le_sp' hp hp5 hζ hST hshape
  exact ⟨orbitRoot p (spTorus p 3 K) (spWeyl 3 K) hW (SpStd K) (hsimple_Sp h4) hne hinj hder,
    orbitRoot_genBlocks p (spTorus p 3 K) (spWeyl 3 K) hW (SpStd K) (hsimple_Sp h4) hne hinj hder
      hgen_Sp⟩

end CFSG.RankThree.PartOne.KFCL.Sp
