module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43RedB
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

@[expose] def S16kU43SubgroupNoncyclic3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Blueprint.LieModel S .PSU 4 3 1 →
    ∀ X : Subgroup S, X.index ≤ 1365 →
      ∃ B : Subgroup S, B ≤ X ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B

theorem s16ku43_card_of_rk_twelve {W : Type} [CommGroup W] [Finite W]
    (hexp : ∀ w : W, w ^ 2 = 1) (hrk : rk ↥(⊤ : Subgroup W) = 12) : Nat.card W = 2 ^ 12 := by
  have hP : IsPGroup 2 W := fun w => ⟨1, by simpa using hexp w⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have h : rk ↥(⊤ : Subgroup W) = n := by
    unfold rk
    rw [Subgroup.card_top, hn]
    exact padicValNat.prime_pow n
  rw [hn, ← hrk, h]

theorem s16kU43Noncyclic3_of_subgroup (h : S16kU43SubgroupNoncyclic3) : S16kU43Noncyclic3 := by
  intro W _ _ hW H hS hrk hirr w hw
  obtain ⟨S, hGrp, hLie, hHat⟩ := hS
  letI := hGrp
  have hcard : Nat.card W = 2 ^ 12 := s16ku43_card_of_rk_twelve hW hrk
  haveI : Finite ↥H := inferInstance
  haveI : Finite S := by
    obtain ⟨-, -, ⟨e⟩⟩ := hHat
    exact Finite.of_equiv _ e.toEquiv
  obtain ⟨ψ, hψ, hidx⟩ := s16ku43_exists_embedding hHat hirr hcard hw
  obtain ⟨B, hBX, hB3, hBc⟩ :=
    s16ku43_noncyclic_in_subgroup (ptCent H w) ψ hψ (h S hLie) hidx
  refine ⟨B, hBX.trans inf_le_left, hB3, hBc, fun b hb => ?_⟩
  exact MulAction.mem_stabilizer_iff.mp (hBX hb).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
