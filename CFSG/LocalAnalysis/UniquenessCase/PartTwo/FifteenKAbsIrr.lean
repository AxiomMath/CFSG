module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndLn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.RankThree.GF2n.Stroth80

open scoped Matrix

private theorem s15k_abs_two_cases {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · refine Or.inr ?_
    have hu : Nat.card Fˣ = 1 := by
      have h := Nat.card_units (α := F)
      omega
    haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) 1)

private theorem s15k_abs_comm_id {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (hF : Nat.card F = 2) (i0 : ι) {X : Subgroup (GL ι F)} (hX : AddCommutantScalar X)
    (g : (ι → F) ≃+ (ι → F))
    (hg : ∀ γ ∈ X, ∀ v : ι → F,
      g ((γ : Matrix ι ι F) *ᵥ v) = (γ : Matrix ι ι F) *ᵥ g v) (v : ι → F) : g v = v := by
  obtain ⟨c, hc⟩ := hX g.toAddMonoidHom hg
  rcases s15k_abs_two_cases hF c with rfl | rfl
  · exfalso
    have h0 : g (Pi.single i0 1) = g 0 := by
      rw [map_zero]
      exact (hc _).trans (zero_smul _ _)
    have h1 := congrFun (g.injective h0) i0
    simp at h1
  · exact (hc v).trans (one_smul _ _)

theorem s15k_abs_endUnits_sp {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} {n : ℕ} (hn : 6 ≤ n) (h : NatSpn H U ⊥ n 1) :
    Z391.EndUnitsTrivial H U := by
  obtain ⟨-, F, hF, hFf, hF2, hreal⟩ := h
  letI := hF
  haveI : Finite F := hFf
  have hF2' : Nat.card F = 2 := by simpa using hF2
  exact s15k_abs_endUnits_of_comm
    (fun g hg v => s15k_abs_comm_id hF2' (Sum.inl ⟨0, by omega⟩) addCommutantScalar_statedSp g hg v)
    hreal

theorem s15k_abs_endUnits_omegaPlus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U : Subgroup W} {n : ℕ} (hn : 6 ≤ n)
    (h : NatOmegaPlus H U ⊥ n 1) : Z391.EndUnitsTrivial H U := by
  obtain ⟨-, F, hF, hFf, hF2, hreal⟩ := h
  letI := hF
  haveI : Finite F := hFf
  have hF2' : Nat.card F = 2 := by simpa using hF2
  exact s15k_abs_endUnits_of_comm
    (fun g hg v => s15k_abs_comm_id hF2' (Sum.inl ⟨0, by omega⟩)
      (addCommutantScalar_statedOmegaPlus (by omega)) g hg v) hreal

theorem s15k_abs_endUnits_omegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U : Subgroup W} {n : ℕ} (hn : 6 ≤ n)
    (h : NatOmegaMinus H U ⊥ n 1) : Z391.EndUnitsTrivial H U := by
  obtain ⟨-, F, hF, hFf, b, c, hF2, hirr, hreal⟩ := h
  letI := hF
  haveI : Finite F := hFf
  have hF2' : Nat.card F = 2 := by simpa using hF2
  exact s15k_abs_endUnits_of_comm
    (fun g hg v => s15k_abs_comm_id hF2' (Sum.inr (Sum.inr 0))
      (addCommutantScalar_statedOmegaMinus (by omega) hirr) g hg v) hreal

theorem rAbsIrr153_holds : RAbsIrr153 := by
  intro V _ _ _ X _ K Z h x hx hc z hz
  have hE : Z391.EndUnitsTrivial K Z := by
    rcases h with ⟨n, hn, -, hZ⟩ | ⟨n, hn, -, hZ⟩ | ⟨n, hn, -, hZ⟩ | ⟨n, hn, -, hZ⟩ |
      ⟨n, hn, -, hZ⟩
    · exact s16c167_endUnits_ln hn hZ
    · exact s15k_abs_endUnits_sp hn hZ
    · exact s15k_abs_endUnits_omegaPlus hn hZ
    · exact s15k_abs_endUnits_omegaMinus hn hZ
    · exact s16c167_endUnits_alt hn hZ
  exact s15k_abs_apply_of_endUnits hE hx hc z hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
