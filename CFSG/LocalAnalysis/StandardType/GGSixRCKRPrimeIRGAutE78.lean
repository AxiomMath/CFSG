module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGNFGen
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutMain

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private lemma irgE7_map_rootGroup_eq
    {F : Type*} [Field F] {G : Type*} [Group G]
    (D : UniversalRootDatum G) (x : (Fin D.rank → ℤ) → F → G) {γ : Fin D.rank → ℤ}
    {g0 : G} {a : Fˣ} {φ : F ≃+* F} {α : G ≃* G}
    (hmem : ∀ z : G, z ∈ D.rootGroup γ ↔ ∃ c, x γ c = z)
    (hx : ∀ c, α (x γ c) = g0 * x γ ((a : F) * φ c) * g0⁻¹) :
    (D.rootGroup γ).map α.toMonoidHom =
      (D.rootGroup γ).map (MulAut.conj g0).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨c, rfl⟩ := (hmem z).1 hz
    refine ⟨x γ ((a : F) * φ c), (hmem _).2 ⟨_, rfl⟩, ?_⟩
    change g0 * x γ ((a : F) * φ c) * g0⁻¹ = y
    exact (hx c).symm.trans hzy
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨c, rfl⟩ := (hmem z).1 hz
    refine ⟨x γ (φ.symm ((a : F)⁻¹ * c)), (hmem _).2 ⟨_, rfl⟩, ?_⟩
    have ha : (a : F) ≠ 0 := Units.ne_zero a
    have hφ : (a : F) * φ (φ.symm ((a : F)⁻¹ * c)) = c := by
      rw [φ.apply_symm_apply, mul_inv_cancel_left₀ ha]
    change α (x γ (φ.symm ((a : F)⁻¹ * c))) = y
    rw [hx, hφ]
    change g0 * x γ c * g0⁻¹ = y
    exact hzy

theorem irgRootPairAut_E7
    {g : ℕ} (hadm : StatedLieAdmissible .E7 0 2 g) : IRGRootPairAut .E7 0 g := by
  refine irg_pair_aut_of_simple_nf (t := .E7) (n := 0) (g := g) ?_ ?_ ?_
  · exact hasBruhatDatum .E7 0 2 g Nat.prime_two (by change True; trivial) hadm
  · rfl
  · intro θ
    obtain ⟨α, g0, a, φ, ε, hαθ, hform⟩ :=
      excAut_E7 (p := 2) (F := GaloisField 2 g) (X := IRGQuot .E7 0 g)
        (θ := QuotientGroup.mk' (Subgroup.center (ggU .E7 0 g).K))
        (hθ := QuotientGroup.mk'_surjective (Subgroup.center (ggU .E7 0 g).K))
        (hker := (QuotientGroup.ker_mk' (Subgroup.center (ggU .E7 0 g).K)).le.trans
          (le_rfl : Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 g)) ≤
            Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 g))))
        (σ := θ)
    refine ⟨α, g0, id, ?_, ?_, ?_⟩
    · intro y
      exact hαθ y
    · intro i
      constructor
      · exact irgE7_map_rootGroup_eq (D := (ggU .E7 0 g).D)
          (x := fun γ c => e7Data_valid.xm (GaloisField 2 g) γ c)
          (γ := Pi.single i 1) (g0 := g0) (a := a i) (φ := φ) (α := α)
          (fun z => e7Data_valid.mem_rootGroup (GaloisField 2 g))
          (fun c => (hform i c).1)
      · exact irgE7_map_rootGroup_eq (D := (ggU .E7 0 g).D)
          (x := fun γ c => e7Data_valid.xm (GaloisField 2 g) γ c)
          (γ := -Pi.single i 1) (g0 := g0) (a := (a i)⁻¹) (φ := φ) (α := α)
          (fun z => e7Data_valid.mem_rootGroup (GaloisField 2 g))
          (fun c => (hform i c).2)
    · intro i hlong
      exact ⟨single_mem_roots (D := (ggU .E7 0 g).D) i, Or.inl hlong⟩

theorem irgRootPairAut_E8
    {g : ℕ} (hadm : StatedLieAdmissible .E8 0 2 g) : IRGRootPairAut .E8 0 g := by
  refine irg_pair_aut_of_simple_nf (t := .E8) (n := 0) (g := g) ?_ ?_ ?_
  · exact hasBruhatDatum .E8 0 2 g Nat.prime_two (by change True; trivial) hadm
  · rfl
  · intro θ
    obtain ⟨α, g0, a, φ, ε, hαθ, hform⟩ :=
      excAut_E8 (p := 2) (F := GaloisField 2 g) (X := IRGQuot .E8 0 g)
        (θ := QuotientGroup.mk' (Subgroup.center (ggU .E8 0 g).K))
        (hθ := QuotientGroup.mk'_surjective (Subgroup.center (ggU .E8 0 g).K))
        (hker := (QuotientGroup.ker_mk' (Subgroup.center (ggU .E8 0 g).K)).le.trans
          (le_rfl : Subgroup.center ↥(adjointGroup Tag.E8 (GaloisField 2 g)) ≤
            Subgroup.center ↥(adjointGroup Tag.E8 (GaloisField 2 g))))
        (σ := θ)
    refine ⟨α, g0, id, ?_, ?_, ?_⟩
    · intro y
      exact hαθ y
    · intro i
      constructor
      · exact irgE7_map_rootGroup_eq (D := (ggU .E8 0 g).D)
          (x := fun γ c => e8Par (GaloisField 2 g) γ c)
          (γ := Pi.single i 1) (g0 := g0) (a := a i) (φ := φ) (α := α)
          (fun z => mem_rootGroup_iff (isRoot_single Tag.E8 i) z)
          (fun c => (hform i c).1)
      · exact irgE7_map_rootGroup_eq (D := (ggU .E8 0 g).D)
          (x := fun γ c => e8Par (GaloisField 2 g) γ c)
          (γ := -Pi.single i 1) (g0 := g0) (a := (a i)⁻¹) (φ := φ) (α := α)
          (fun z => mem_rootGroup_iff (isRoot_neg_single Tag.E8 i) z)
          (fun c => (hform i c).2)
    · intro i hlong
      exact ⟨single_mem_roots (D := (ggU .E8 0 g).D) i, Or.inl hlong⟩

end CFSG.StandardType.RCKRP
