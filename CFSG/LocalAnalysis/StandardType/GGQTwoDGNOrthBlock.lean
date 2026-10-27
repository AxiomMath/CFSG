module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPaths
public import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoResidual
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.RankThree.Classical2 (orthDerived)
open Multiplicative Matrix

local notation "𝔽₄" => GaloisField 2 2
local notation "σ₂" => unitaryInvolution (GaloisField 2 2) 2 1

@[expose] def omSwapPos {r : ℕ} (a b : Fin r) (hab : a ≠ b) : OmPlusIdx r :=
  if h : a < b then (⟨(a, b), h⟩, false)
  else (⟨(b, a), lt_of_le_of_ne (not_lt.mp h) hab.symm⟩, false)

theorem omSupp_omSwapPos {r : ℕ} (a b : Fin r) (hab : a ≠ b) :
    omSupp (omSwapPos a b hab) = {a, b} := by
  unfold omSwapPos
  split_ifs with h
  · rfl
  · exact Finset.pair_comm b a

theorem omPlusRefl_omSwapPos {p r : ℕ} (a b : Fin r) (hab : a ≠ b) :
    omPlusRefl p (omSwapPos a b hab) = SpCoord.permAut (Equiv.swap a b) := by
  unfold omSwapPos
  split_ifs with h
  · rfl
  · show SpCoord.permAut (Equiv.swap b a) = _
    rw [Equiv.swap_comm]

theorem eq_of_permAut_swap_eq {p r : ℕ} {f : Fin r → Multiplicative (ZMod p)} {a b : Fin r}
    (h : SpCoord.permAut (Equiv.swap a b) f = f) : f a = f b := by
  have h1 := congrFun h b
  simpa [SpCoord.permAut_apply, Equiv.swap_inv] using h1

section Block

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
  {Φ : OrthFrameCore p Bs X} [Algebra Φ.F 𝔽₄] (N : OrthNormData Φ)

theorem OrthNormData.block_le_rank2 (hr : 4 ≤ Φ.r) {I : Finset (Fin Φ.r)} (hI : I.card = 3) :
    ∃ x y : OmPlusIdx Φ.r,
      omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x ∧
        (coordBlockSU 𝔽₄ 2 1 I).map N.rep ≤ Φ.rank2 x y := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hI
  refine ⟨omSwapPos a b hab, omSwapPos b c hbc, ?_, ?_⟩
  · rw [omPlusRefl_not_comm_iff_supp (Fact.out), omSupp_omSwapPos, omSupp_omSwapPos]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ha : a ∈ ({b, c} : Finset (Fin Φ.r)) := h ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with h1 | h1
      · exact hab h1
      · exact hac h1
    · exact (Finset.not_disjoint_iff.mpr ⟨b, by simp, by simp⟩) h
  · set J : Finset (Fin Φ.r) := {a, b, c} with hJdef
    have hJ : J.card = 3 := hI
    have hθ : (N.rep.comp (blockSUOn 𝔽₄ 2 1 J)).range ≤ orthDerived Φ.Q ⊓
        Subgroup.centralizer ((Φ.fixTorus (omSwapPos a b hab) ⊓
          Φ.fixTorus (omSwapPos b c hbc) : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
            Set (Φ.V ≃ₗ[Φ.F] Φ.V)) := by
      rintro _ ⟨z, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨N.rep_range_le hr ⟨blockSUOn 𝔽₄ 2 1 J z, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨hx, hy⟩ := Subgroup.mem_inf.mp ht
      rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at hx hy
      obtain ⟨f, hf, rfl⟩ := hx
      obtain ⟨f', hf', hff'⟩ := hy
      have hf'f : f' = f := Φ.Δ.τ_inj hff'
      subst hf'f
      change omPlusRefl p (omSwapPos a b hab) f' = f' at hf
      change omPlusRefl p (omSwapPos b c hbc) f' = f' at hf'
      rw [omPlusRefl_omSwapPos] at hf hf'
      have hfa : f' a = f' b := eq_of_permAut_swap_eq hf
      have hfb : f' b = f' c := eq_of_permAut_swap_eq hf'
      have hconst : ∀ i ∈ J, f' i = f' a := by
        intro i hi
        simp only [hJdef, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · rfl
        · exact hfa.symm
        · exact hfb.symm.trans hfa.symm
      set v : Fin Φ.r → 𝔽₄ := fun i => (((N.ζ ^ (toAdd (f' i)).val : normOne σ₂) : 𝔽₄ˣ) : 𝔽₄)
        with hvdef
      have hv : ∀ i ∈ J, ∀ j ∈ J, v i = v j := by
        intro i hi j hj
        simp only [hvdef, hconst i hi, hconst j hj]
      have hg : blockSUOn 𝔽₄ 2 1 J z ∈ coordBlockSU 𝔽₄ 2 1 J := ⟨z, rfl⟩
      have hM := diagonal_mul_comm_of_mem_coordBlockSU hg hv
      apply N.cχ.injective
      rw [MonoidHom.comp_apply, map_mul, map_mul, N.cχ_tau, N.cχ_rep]
      apply LinearEquiv.ext
      intro u
      funext i
      have key : ∀ w : Fin Φ.r → 𝔽₄,
          (((blockSUOn 𝔽₄ 2 1 J z : Su 𝔽₄ 2 1 Φ.r) : GL (Fin Φ.r) 𝔽₄) :
              Matrix (Fin Φ.r) (Fin Φ.r) 𝔽₄) *ᵥ (fun j => v j * w j) =
            fun i => v i * ((((blockSUOn 𝔽₄ 2 1 J z : Su 𝔽₄ 2 1 Φ.r) : GL (Fin Φ.r) 𝔽₄) :
              Matrix (Fin Φ.r) (Fin Φ.r) 𝔽₄) *ᵥ w) i := by
        intro w
        have h1 : (fun j => v j * w j) = Matrix.diagonal v *ᵥ w := by
          funext j
          rw [Matrix.mulVec_diagonal]
        have h2 : (fun i => v i * ((((blockSUOn 𝔽₄ 2 1 J z : Su 𝔽₄ 2 1 Φ.r) : GL (Fin Φ.r) 𝔽₄) :
              Matrix (Fin Φ.r) (Fin Φ.r) 𝔽₄) *ᵥ w) i) =
            Matrix.diagonal v *ᵥ (((((blockSUOn 𝔽₄ 2 1 J z : Su 𝔽₄ 2 1 Φ.r) : GL (Fin Φ.r) 𝔽₄) :
              Matrix (Fin Φ.r) (Fin Φ.r) 𝔽₄)) *ᵥ w) := by
          funext j
          rw [Matrix.mulVec_diagonal]
        rw [h1, h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
      have hD : ∀ w : Fin Φ.r → 𝔽₄,
          (diagHom Φ.F σ₂ Φ.r (fun i => N.ζ ^ (toAdd (f' i)).val)) w = fun j => v j * w j := by
        intro w
        funext j
        simp [diagHom_apply, hvdef]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, suEndN_apply, suEndN_apply, smul_def,
        smul_def, hD, hD]
      exact (congrFun (key u) i).symm
    have h2 := ggSu_range_le_ggOTwoPrime qTwoD_card_gf4 (by omega : 2 ≤ J.card)
      (N.rep.comp (blockSUOn 𝔽₄ 2 1 J)) hθ
    have h3 : (coordBlockSU 𝔽₄ 2 1 J).map N.rep = (N.rep.comp (blockSUOn 𝔽₄ 2 1 J)).range := by
      rw [MonoidHom.range_comp]
      rfl
    rw [h3]
    exact h2

end Block

end CFSG.StandardType.QTwo

end
