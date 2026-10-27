module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure s16h_L3Coord {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (U : Subgroup W) where
  ρ : ↥L ≃* GL (Fin 3) (ZMod 2)
  ψ : ↥U ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))
  equivariant : ∀ (l : ↥L) (u : W) (hu : u ∈ U) (hlu : (l : MulAut W) u ∈ U),
    ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
      ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩))

theorem s16h_e3_l3_coord {W : Type} [CommGroup W] [Finite W] {L Y : Subgroup (MulAut W)}
    {U : Subgroup W} (hL : IsL3 ↥L 1) (hU : U = commSub ⊤ L)
    (hsum : SumOfNat (fun H V Z => BinaryNaturalSL H V Z 3 1) L U ⊥ 3)
    (hY : Y ≤ normalizer (L : Set (MulAut W)))
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L, ∃ g ∈ Y, I₂ = I₁.map g.toMonoidHom) :
    Nonempty (s16h_L3Coord L U) := by
  obtain ⟨I, -, hind, hsup, hI⟩ := hsum
  have hirr : ∀ i, I i ∈ irrSet L := fun i => s16c167_mem_irrSet_ln (by norm_num) (hI i)
  have hfix : ∀ i, I i ⊓ fixV L = ⊥ :=
    fun i => s16c167_inf_fixV_eq_bot_of_binaryNaturalSL (by norm_num) (hI i)
  have hU' : (⊥ ⊔ ⨆ i, I i) = commSub ⊤ L := hsup.trans hU
  obtain ⟨i, j, hij, hiso⟩ := s16h_e3_l3_two_iso hL hI
  have key1 : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide
  have key2 : ∀ i j k m : Fin 3, i ≠ j → i ≠ k → j ≠ k → m ≠ i → m ≠ j → m = k := by
    intro i j k m hij hik hjk hmi hmj
    simp only [ne_eq, Fin.ext_iff] at hij hik hjk hmi hmj ⊢
    omega
  obtain ⟨k, hik, hjk⟩ := key1 i j hij
  have hk := s16h_e3_l3_homog hirr hfix hind hU' hY htrans hij hik hjk hiso
  have hall : ∀ m : Fin 3, H.Pair.IsoMod L (I i) (I m) := by
    intro m
    by_cases hmi : m = i
    · subst hmi
      exact ⟨MulEquiv.refl _, fun l _ w _ => rfl⟩
    by_cases hmj : m = j
    · subst hmj
      exact hiso
    have hmk : m = k := key2 i j k m hij hik hjk hmi hmj
    subst hmk
    exact hk
  obtain ⟨ρ, ψ, h⟩ := s16h_e3_l3_coord_of_iso hL hI hind hsup i hall
  exact ⟨⟨ρ, ψ, h⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
