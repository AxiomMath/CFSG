module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusRoot2
public import CFSG.LocalAnalysis.StandardType.GGTorusF4Split
public import CFSG.LocalAnalysis.StandardType.GGTorCTori
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

@[expose] public noncomputable section

namespace CFSG.StandardType.DSplitTorus

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.SeitzReduction Matrix Multiplicative
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open TableBSymp TableBOrth
open DScalarTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ}

def torusHom : (Fin N → Kˣ) →* StatedOmega (StatedQuadPlus N K) :=
  (OmegaPilot.diagOmega K N).codRestrict _ F4Pilot.diagOmega_mem_statedOmega

@[simp] theorem coe_torusHom (a : Fin N → Kˣ) :
    (torusHom a : GL (Fin N ⊕ Fin N) K) = OmegaPilot.diagOmega K N a := rfl

theorem torusHom_injective : Function.Injective (torusHom (K := K) (N := N)) := by
  intro a b hab
  funext i
  apply Units.ext
  have h := congrArg (fun x : StatedOmega (StatedQuadPlus N K) =>
    ((x : GL (Fin N ⊕ Fin N) K) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K)
      (Sum.inl i) (Sum.inl i)) hab
  simpa only [coe_torusHom, OmegaPilot.diagOmega_coe, Matrix.diagonal_apply_eq,
    SymplecticPilot.diagSpEntry_inl] using h

omit [Finite K] [CharP K 2] in
theorem exists_eq_torus_of_commute (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (g : GL (Fin N ⊕ Fin N) K)
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQPlus K N))
    (hcomm : ∀ f, g * omPlusTorusGL hζ f = omPlusTorusGL hζ f * g) :
    ∃ a : Fin N → Kˣ, g = OmegaPilot.diagOmega K N a := by
  classical
  have hdiag : (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K).IsDiag :=
    fun x y hxy => ggKGOmR_centralizer_diag hp hp2 hζ hζo hcomm x y hxy
  choose d hd using fun x => TauCeti.isUnit_apply_of_isDiag hdiag x
  have hgd : g = TauCeti.diagGL d := by
    apply Units.ext
    ext x y
    by_cases hxy : x = y
    · subst y
      simp only [TauCeti.diagGL_coe, Matrix.diagonal_apply_eq]
      exact (hd x).symm
    · simp only [TauCeti.diagGL_coe, Matrix.diagonal_apply_ne _ hxy]
      exact hdiag hxy
  have hpair : ∀ i, d (Sum.inr i) = (d (Sum.inl i))⁻¹ := by
    intro i
    have h := isometry_of_mem_orthGroup hg
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1)
    rw [hgd, TauCeti.diagGL_coe] at h
    have hm : (d (Sum.inl i) : K) * d (Sum.inr i) = 1 := by
      simpa [LargeEvenQPlus, StatedQuadPlus, Matrix.mulVec_diagonal,
        Pi.add_apply, Pi.single_apply] using h
    apply Units.ext
    simpa only [Units.val_inv_eq_inv_val] using eq_inv_of_mul_eq_one_right hm
  refine ⟨fun i => d (Sum.inl i), ?_⟩
  rw [hgd]
  change TauCeti.diagGL d = TauCeti.diagGL (pairedUnits fun i => d (Sum.inl i))
  congr 1
  funext x
  rcases x with i | i
  · rfl
  · exact hpair i

theorem centralizer_le_torus (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Subgroup.centralizer ((omPlusTorus (m := N) hζ).range :
      Set (StatedOmega (StatedQuadPlus N K))) ≤ (torusHom (K := K) (N := N)).range := by
  intro g hg
  obtain ⟨a, ha⟩ := exists_eq_torus_of_commute hp hp2 hζ hζo g
    (omega_le_orth (LargeEvenQPlus K N) g.2) fun f => by
      have h := (Subgroup.mem_centralizer_iff.mp hg _ ⟨f, rfl⟩).symm
      exact congrArg Subtype.val h
  exact ⟨a, Subtype.ext ha.symm⟩

theorem exists_simple_representatives (hK : 4 ≤ Nat.card K) (hN : 4 ≤ N) :
    ∃ n : Fin N → StatedOmega (StatedQuadPlus N K),
      ∀ (m : ℕ) (χ : Multiplicative (ZMod m) →* Kˣ) (i : Fin N)
        (a : Fin N → Multiplicative (ZMod m)),
        n i * torusHom (fun j => χ (a j)) * (n i)⁻¹ =
          torusHom (fun j => χ (simpleReflection hN i a j)) := by
  classical
  have hW : ∀ i : Fin N, ∃ n : StatedOmega (StatedQuadPlus N K),
      ∀ (m : ℕ) (χ : Multiplicative (ZMod m) →* Kˣ) (a : Fin N → Multiplicative (ZMod m)),
        n * torusHom (fun j => χ (a j)) * n⁻¹ =
          torusHom (fun j => χ (simpleReflection hN i a j)) := by
    intro i
    by_cases hi : i.val + 1 < N
    · let j : Fin N := ⟨i.val + 1, hi⟩
      have hij : i < j := by dsimp [j]; simp [Fin.lt_def]
      let P : GL (Fin N ⊕ Fin N) K :=
        (SymplecticPilot.permSp K (Equiv.swap i j) : GL (Fin N ⊕ Fin N) K)
      have hP : P ∈ StatedOmega (StatedQuadPlus N K) :=
        omPlusBlock_le hK (⟨(i, j), hij⟩, false)
          (OmegaPilot.permSp_swap_mem_siegelBlockGL i j)
      refine ⟨⟨P, hP⟩, ?_⟩
      intro m χ a
      apply Subtype.ext
      change P * OmegaPilot.diagOmega K N (fun j => χ (a j)) * P⁻¹ = _
      dsimp only [P]
      rw [OmegaPilot.permSp_swap_mul_diagOmega_mul_inv]
      congr 1
      funext k
      simp [simpleReflection, hi, SpCoord.permAut_apply, j, Equiv.swap_inv]
    · let a₀ : Fin N := ⟨N - 2, by omega⟩
      let b₀ : Fin N := ⟨N - 1, by omega⟩
      have hab : a₀ < b₀ := by dsimp [a₀, b₀]; simp only [Fin.lt_def]; omega
      let F : GL (Fin N ⊕ Fin N) K := OmegaPilot.flipGL K {b₀}
      let P : GL (Fin N ⊕ Fin N) K :=
        (SymplecticPilot.permSp K (Equiv.swap a₀ b₀) : GL (Fin N ⊕ Fin N) K)
      have hP : F * P * F⁻¹ ∈ StatedOmega (StatedQuadPlus N K) :=
        omPlusBlock_le hK (⟨(a₀, b₀), hab⟩, true)
          (Subgroup.mem_map_of_mem (MulAut.conj F).toMonoidHom
            (OmegaPilot.permSp_swap_mem_siegelBlockGL a₀ b₀))
      refine ⟨⟨F * P * F⁻¹, hP⟩, ?_⟩
      intro m χ a
      apply Subtype.ext
      change (F * P * F⁻¹) * OmegaPilot.diagOmega K N (fun j => χ (a j)) *
        (F * P * F⁻¹)⁻¹ = _
      have hF : F⁻¹ = F := OmegaPilot.flipGL_inv _
      have h1 : F⁻¹ * OmegaPilot.diagOmega K N (fun j => χ (a j)) * F =
          OmegaPilot.diagOmega K N (OmegaPilot.flipParam K {b₀} fun j => χ (a j)) := by
        rw [hF]
        have h := OmegaPilot.flipGL_mul_diagOmega_mul_inv {b₀} (fun j => χ (a j))
        simpa only [F, OmegaPilot.flipGL_inv] using h
      have h2 : P * OmegaPilot.diagOmega K N
          (OmegaPilot.flipParam K {b₀} fun j => χ (a j)) * P⁻¹ =
          OmegaPilot.diagOmega K N
            ((OmegaPilot.flipParam K {b₀} fun j => χ (a j)) ∘ Equiv.swap a₀ b₀) :=
        OmegaPilot.permSp_swap_mul_diagOmega_mul_inv a₀ b₀ _
      calc (F * P * F⁻¹) * OmegaPilot.diagOmega K N (fun j => χ (a j)) * (F * P * F⁻¹)⁻¹
          = F * (P * (F⁻¹ * OmegaPilot.diagOmega K N (fun j => χ (a j)) * F) * P⁻¹) * F⁻¹ := by group
        _ = F * (P * OmegaPilot.diagOmega K N
            (OmegaPilot.flipParam K {b₀} fun j => χ (a j)) * P⁻¹) * F⁻¹ := by rw [h1]
        _ = F * OmegaPilot.diagOmega K N
            ((OmegaPilot.flipParam K {b₀} fun j => χ (a j)) ∘ Equiv.swap a₀ b₀) * F⁻¹ := by rw [h2]
        _ = OmegaPilot.diagOmega K N (fun j => χ (simpleReflection hN i a j)) := by
          dsimp only [F]
          rw [OmegaPilot.flipGL_mul_diagOmega_mul_inv]
          congr 1
          funext k
          have hab' : a₀ ≠ b₀ := ne_of_lt hab
          simp only [OmegaPilot.flipParam_apply, Finset.mem_singleton,
            Function.comp_apply, simpleReflection, dif_neg hi, MulAut.mul_apply,
            SpCoord.sgnAut_apply, SpCoord.permAut_apply, Equiv.swap_inv,
            Function.update_apply]
          by_cases hka : k = a₀
          · subst k
            simp [a₀, b₀, Equiv.swap_apply_left, hab', map_inv]
          · by_cases hkb : k = b₀
            · subst k
              simp [a₀, b₀, Equiv.swap_apply_right, hab', Ne.symm hab', map_inv]
            · simp [a₀, b₀, hka, hkb, Equiv.swap_apply_of_ne_of_ne hka hkb]
  choose n hn using hW
  exact ⟨n, fun m χ i a => hn i m χ a⟩

end CFSG.StandardType.DSplitTorus
