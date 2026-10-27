module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGNFGen
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGNFSimpleE
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutMain
public import CFSG.LieType.Chevalley.ExactNormalFormE

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private lemma irgE6_map_rootGroup_eq
    {F : Type*} [Field F] {G : Type*} [Group G]
    (D : UniversalRootDatum G) (x : (Fin D.rank → ℤ) → F → G) {γ γ' : Fin D.rank → ℤ}
    {g0 : G} {a : Fˣ} {φ : F ≃+* F} {α : G ≃* G}
    (hmem : ∀ z : G, z ∈ D.rootGroup γ ↔ ∃ c, x γ c = z)
    (hmem' : ∀ z : G, z ∈ D.rootGroup γ' ↔ ∃ c, x γ' c = z)
    (hx : ∀ c, α (x γ c) = g0 * x γ' ((a : F) * φ c) * g0⁻¹) :
    (D.rootGroup γ).map α.toMonoidHom =
      (D.rootGroup γ').map (MulAut.conj g0).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨c, rfl⟩ := (hmem z).1 hz
    refine ⟨x γ' ((a : F) * φ c), (hmem' _).2 ⟨_, rfl⟩, ?_⟩
    change g0 * x γ' ((a : F) * φ c) * g0⁻¹ = y
    exact (hx c).symm.trans hzy
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨c, rfl⟩ := (hmem' z).1 hz
    refine ⟨x γ (φ.symm ((a : F)⁻¹ * c)), (hmem _).2 ⟨_, rfl⟩, ?_⟩
    have ha : (a : F) ≠ 0 := Units.ne_zero a
    have hφ : (a : F) * φ (φ.symm ((a : F)⁻¹ * c)) = c := by
      rw [φ.apply_symm_apply, mul_inv_cancel_left₀ ha]
    change α (x γ (φ.symm ((a : F)⁻¹ * c))) = y
    rw [hx, hφ]
    change g0 * x γ' c * g0⁻¹ = y
    exact hzy

theorem irgRootPairAut_E6
    {g : ℕ} (hadm : StatedLieAdmissible .E6 0 2 g) : IRGRootPairAut .E6 0 g := by
  refine irg_pair_aut_of_simple_nf (t := .E6) (n := 0) (g := g) ?_ ?_ ?_
  · exact hasBruhatDatum .E6 0 2 g Nat.prime_two (by change True; trivial) hadm
  · rfl
  · intro θ
    obtain ⟨α, g0, a, φ, ε, hαθ, hform⟩ :=
      excAut_E6 (p := 2) (F := GaloisField 2 g) (X := IRGQuot .E6 0 g)
        (θ := QuotientGroup.mk' (Subgroup.center (ggU .E6 0 g).K))
        (hθ := QuotientGroup.mk'_surjective (Subgroup.center (ggU .E6 0 g).K))
        (hker := (QuotientGroup.ker_mk' (Subgroup.center (ggU .E6 0 g).K)).le.trans
          (le_rfl : Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 g)) ≤
            Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 g))))
        (σ := θ)
    refine ⟨α, g0, fun i => exactPerm Tag.E6 ε i, ?_, ?_, ?_⟩
    · intro y
      exact hαθ y
    · intro i
      constructor
      · exact irgE6_map_rootGroup_eq (D := (ggU .E6 0 g).D)
          (x := fun γ c => e6Data_valid.xm (GaloisField 2 g) γ c)
          (γ := Pi.single i 1) (γ' := Pi.single (exactPerm Tag.E6 ε i) 1) (g0 := g0)
          (a := a (exactPerm Tag.E6 ε i)) (φ := φ) (α := α)
          (fun z => e6Data_valid.mem_rootGroup (GaloisField 2 g))
          (fun z => e6Data_valid.mem_rootGroup (GaloisField 2 g))
          (fun c => (hform i c).1)
      · exact irgE6_map_rootGroup_eq (D := (ggU .E6 0 g).D)
          (x := fun γ c => e6Data_valid.xm (GaloisField 2 g) γ c)
          (γ := -Pi.single i 1) (γ' := -Pi.single (exactPerm Tag.E6 ε i) 1) (g0 := g0)
          (a := (a (exactPerm Tag.E6 ε i))⁻¹) (φ := φ) (α := α)
          (fun z => e6Data_valid.mem_rootGroup (GaloisField 2 g))
          (fun z => e6Data_valid.mem_rootGroup (GaloisField 2 g))
          (fun c => (hform i c).2)
    · intro i hlong
      obtain ⟨w, hw⟩ :=
        irg_simple_roots_conj_E (t := .E6) (g := g) (Or.inl rfl) i (exactPerm Tag.E6 ε i)
      have h1 := (CFSG.StandardType.LieKnownR2.Short.ggLongRoot_weylAction_iff (ggU .E6 0 g).D w
        (Pi.single i 1)).2 hlong
      rw [hw] at h1
      exact ⟨single_mem_roots (D := (ggU .E6 0 g).D) (exactPerm Tag.E6 ε i), Or.inl h1⟩

end CFSG.StandardType.RCKRP
