module

import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeSetup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w135c2_x1IsIrrOn_of_ctx {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) : X1.IsIrrOn L := by
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  refine ⟨?_, fun U hU => hirr.2.2.2 U hU bot_le le_top⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have := hnt
  exact (ne_of_lt hirr.1) (Subgroup.ext fun x => by simp [Subsingleton.elim x 1])

theorem w135c2_periodic_data {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (hirr : X1.IsIrrOn L) {S : Type} [Group S] (ι : S ≃* ↥L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (ιK : K →+* k)
      (ρ : Representation k S (Fin m → k)),
      1 ≤ δ ∧ 1 ≤ m ∧ ρ.IsIrreducible ∧ Function.Injective ρ ∧ Function.Injective ιK ∧
      Nat.card W = 2 ^ (δ * m) ∧
      (∀ s i j, (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i) := by
  obtain ⟨δ, m, k, hkField, hkFinite, hkChar, hAlg, ρ, -, hδ, hm, hsimple, hρinj, -, hWcard, -, -,
    hfrob⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4.exists_periodic_rep (G := S) hW hirr ι hn hK
  let : Field k := hkField
  let : Finite k := hkFinite
  let : CharP k 2 := hkChar
  let : Algebra K k := hAlg
  refine ⟨δ, m, k, inferInstance, inferInstance, inferInstance, algebraMap K k, ρ, hδ, hm, ?_,
    hρinj, (algebraMap K k).injective, hWcard, hfrob⟩
  exact (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).2 hsimple

end CFSG.LocalAnalysis.WeakClosure81
