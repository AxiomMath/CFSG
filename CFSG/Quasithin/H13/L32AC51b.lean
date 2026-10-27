module

public import CFSG.Quasithin.H13.L32AC51a
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.ComponentClassification
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lin

variable {n : ℕ}

abbrev par (n j : ℕ) : Subgroup (SLn n) := flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})

theorem det_gl (A : GL (Fin n) (ZMod 2)) : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 :=
  BinaryParabolic.eq_one_of_ne_zero _ ((isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

@[expose] def toSL (A : GL (Fin n) (ZMod 2)) : SLn n := ⟨A, det_gl A⟩

theorem toGL_toSL (A : GL (Fin n) (ZMod 2)) : SpecialLinearGroup.toGL (toSL A) = A :=
  Units.ext rfl

theorem aut_dichotomy (hn : 3 ≤ n) (α : MulAut (SLn n))
    (hα : ∀ u ∈ unitriangular n (ZMod 2), α u ∈ unitriangular n (ZMod 2)) :
    (∃ g : SLn n, α = MulAut.conj g) ∨
      ∀ d ≤ n, ∀ g ∈ stabilizer (flagSpace n (ZMod 2) d),
        α g ∈ stabilizer (flagSpace n (ZMod 2) (n - d)) := by
  obtain ⟨A, σ, ε, hε, hαeq⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn α
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  rw [map_one, mul_one] at hαeq
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    refine ⟨toSL A, ?_⟩
    rw [hαeq, pow_zero, mul_one]
    ext x : 1
    apply SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul,
      map_inv, toGL_toSL]
  · right
    rw [pow_one] at hαeq
    have hUU : (unitriangular n (ZMod 2)).map α.toMonoidHom = unitriangular n (ZMod 2) := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact hα u hu
      · rw [Subgroup.card_map_of_injective α.injective]
    intro d hd g hg
    set W := (dotOrth (flagSpace n (ZMod 2) d)).map
      (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2))) with hW
    have hmap : (stabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom = stabilizer W := by
      rw [hαeq, CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul]
      have h1 := map_stabilizer_slGraphAut (K := ZMod 2) (n := n) (flagSpace n (ZMod 2) d)
      have h2 := map_stabilizer_slConjugation (K := ZMod 2) A (dotOrth (flagSpace n (ZMod 2) d))
      exact (congrArg (fun P => P.map (CatalogueBHigherLinearAction.slConjugation n
        (ZMod 2) A).toMonoidHom) h1).trans h2
    have hUW : ∀ u ∈ unitriangular n (ZMod 2), ∀ v ∈ W,
        (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈ W := by
      intro u hu v hv
      have hu' : u ∈ (stabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom := by
        rw [← hUU] at hu
        obtain ⟨u', hu', rfl⟩ := hu
        exact ⟨u', mem_flagStabilizer.mp (BinaryParabolic.unitriangular_le_flagStabilizer {d} hu') d
          (Set.mem_singleton d), rfl⟩
      rw [hmap] at hu'
      have h3 := mem_stabilizer.mp hu'
      have h4 : (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈
          W.map (mulVecLin (u : Matrix (Fin n) (Fin n) (ZMod 2))) := ⟨v, hv, rfl⟩
      rwa [h3] at h4
    obtain ⟨m, hm, hWm⟩ := eq_flagSpace_of_invariant hUW
    have hfin : m = n - d := by
      have h1 := finrank_flagSpace (K := ZMod 2) hm
      rw [← hWm, hW, CFSG.QuasithinUnique.Setup.Family.finrank_map_mulVecLin_gl, finrank_dotOrth,
        finrank_flagSpace hd] at h1
      omega
    have hg' : α g ∈ (stabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom := ⟨g, hg, rfl⟩
    rw [hmap, hWm, hfin] at hg'
    exact hg'

theorem mem_par_of_swap {α : MulAut (SLn n)}
    (hα : ∀ d ≤ n, ∀ g ∈ stabilizer (flagSpace n (ZMod 2) d),
      α g ∈ stabilizer (flagSpace n (ZMod 2) (n - d))) {j : ℕ} {g : SLn n} (hg : g ∈ par n j) :
    α g ∈ par n (n - j) := by
  rw [mem_flagStabilizer] at hg ⊢
  rintro i ⟨⟨hi1, hin⟩, hij⟩
  have hij' : i ≠ n - j := hij
  have hd : n - i ∈ Set.Icc 1 (n - 1) \ {j} :=
    ⟨⟨by omega, by omega⟩, fun h => hij' (by rw [Set.mem_singleton_iff] at h; omega)⟩
  have := hα (n - i) (by omega) g (hg _ hd)
  rwa [show n - (n - i) = i by omega] at this

theorem eq_of_swap {α : MulAut (SLn n)}
    (hα : ∀ d ≤ n, ∀ g ∈ stabilizer (flagSpace n (ZMod 2) d),
      α g ∈ stabilizer (flagSpace n (ZMod 2) (n - d))) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n)
    (hP : ∀ g ∈ par n j, α g ∈ par n j) : n - j = j := by
  have hmap : (par n j).map α.toMonoidHom = par n j := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact hP g hg
    · rw [Subgroup.card_map_of_injective α.injective]
  have hr : reflection n (ZMod 2) j hj hjn ∈ par n j :=
    BinaryParabolic.reflection_mem_parabolic hj hjn
  rw [← hmap] at hr
  obtain ⟨g, hg, hge⟩ := hr
  have h1 := mem_par_of_swap hα hg
  have h2 : α g = reflection n (ZMod 2) j hj hjn := hge
  rw [h2] at h1
  exact (BinaryParabolic.eq_of_reflection_mem_parabolic hj hjn h1).symm

theorem eq_top_of_refl {Y : Subgroup (SLn n)} (hU : unitriangular n (ZMod 2) ≤ Y)
    (hr : ∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n), reflection n (ZMod 2) j hj hjn ∈ Y) : Y = ⊤ := by
  have h := (subflag_stabilizer_generation (K := ZMod 2) (n := n) ∅).1
  rw [flagStabilizer_empty] at h
  rw [eq_top_iff, h, Subgroup.closure_le]
  rintro g (hg | ⟨j, hj, hjn, -, rfl⟩)
  · exact hU (upper_eq_uni n ▸ hg)
  · exact hr j hj hjn

end Lin

end CFSG.Quasithin.H13.L32A.C
