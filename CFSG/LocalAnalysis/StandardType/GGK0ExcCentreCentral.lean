module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585Expl

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem lk0xpb2_connectedCentralizer_le_centralizer
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (b : Fin ρ.tau.rank → Omegaˣ)
    (hχ : ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1) :
    CFSG.StandardType.E6Centralizer1585.connectedCentralizer ρ ≤
      Subgroup.centralizer ({rootDiagUnit ρ.tau b} : Set (ModGL ρ.tau Omega)) := by
  rw [CFSG.StandardType.E6Centralizer1585.connectedCentralizer]
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨b', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm b' b]
  · refine iSup₂_le ?_
    intro α hα
    rw [CFSG.Blueprint.Chevalley.rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hconj := CFSG.LieType.Chevalley.rootDiagUnit_conj_pinnedX (K := Omega) b hα.1 c
    rw [hχ α hα] at hconj
    simp only [Units.val_one, one_mul] at hconj
    calc CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega α c * rootDiagUnit ρ.tau b
        = (rootDiagUnit ρ.tau b * CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega α c *
            (rootDiagUnit ρ.tau b)⁻¹) * rootDiagUnit ρ.tau b := by rw [hconj]
      _ = rootDiagUnit ρ.tau b * CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega α c := by group

theorem PB2_central_in_centralizer
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hc : GGKacCentred lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (z : ModGL ρ.tau Omega)
    (hz : ∃ b : Fin ρ.tau.rank → Omegaˣ, rootDiagUnit ρ.tau b = z ∧
      ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1)
    (m : ModGL ρ.tau Omega) (hm : m ∈ adjointGroup ρ.tau Omega)
    (hcomm : m * rootDiagUnit ρ.tau ρ.a = rootDiagUnit ρ.tau ρ.a * m) : m * z = z * m := by
  obtain ⟨b, hb, hχ⟩ := hz
  have hle := lk0xpb2_connectedCentralizer_le_centralizer ρ b hχ
  have hcentral : m ∈ Subgroup.centralizer
      ({rootDiagUnit ρ.tau ρ.a} : Set (ModGL ρ.tau Omega)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hmc : m ∈ CFSG.StandardType.E6Centralizer1585.connectedCentralizer ρ :=
    ρ.centred_centralizer_generated hc ⟨hm, hcentral⟩
  rw [← hb]
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hmc)

end CFSG.StandardType.GGK0ExcCentreU

end
