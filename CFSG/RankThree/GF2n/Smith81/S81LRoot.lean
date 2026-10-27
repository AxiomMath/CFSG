module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Smith81.S81BA5Frame

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube
open scoped commutatorElement

section Model

variable {K : Type} [Field K]

theorem isTransvec_conj {n : ℕ} {c g : GL (Fin n) K} (hg : IsTransvec K g) :
    IsTransvec K (c⁻¹ * g * c) := by
  obtain ⟨hsq, hrk⟩ := hg
  have hcc : ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (c : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul c
  have hcc' : (c : Matrix (Fin n) (Fin n) K) *
      ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := Units.mul_inv c
  have hsub : ((c⁻¹ * g * c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) - 1) *
        (c : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hcc]
  refine ⟨?_, ?_⟩
  · rw [hsub]
    calc _ = ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((g : Matrix (Fin n) (Fin n) K) - 1) * ((c : Matrix (Fin n) (Fin n) K) *
            ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((g : Matrix (Fin n) (Fin n) K) - 1)) * (c : Matrix (Fin n) (Fin n) K) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hcc', mul_one, hsq]; simp
  · rw [hsub, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units c),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units c⁻¹)]
    exact hrk

end Model

section Points

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ψ : M₀.E ≃ₗ[K] Cube K} {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}

theorem EGeom.EUniData.exists_root_group (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (Hs : StrothHyp M Q Z) {ζ : Cube K} (hζ : IsPure K ζ) (hζ0 : ζ ≠ 0) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ ∃ a ∈ A, ψ (M₀.π a) = ζ := by
  obtain ⟨A₀, hctx₀⟩ := exists_ctx_of_strothHyp Hs
  obtain ⟨g₀, hg₀, himg₀, -⟩ := d.point A₀ hctx₀.conj hctx₀.le hctx₀.ne
  obtain ⟨h₀, -, rfl⟩ := Subgroup.mem_map.mp hg₀
  have hp0 : IsPure K (p0 K) := ⟨_, p0_eq⟩
  have hζ₀pure : IsPure K (rho K h₀ (p0 K)) := hp0.rho h₀
  have hζ₀ne : rho K h₀ (p0 K) ≠ 0 := fun h =>
    p0_ne_zero ((rhoEquiv K h₀).map_eq_zero_iff.mp h)
  have hmem : (rhoEquiv K h₀) (p0 K) ∈ (fun a : G => ψ (M₀.π a)) '' (A₀ : Set G) := by
    rw [himg₀]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a₀, ha₀, ha₀eq⟩ := hmem
  obtain ⟨g, hgdet, hgζ⟩ := isPure_transitive hζ₀pure hζ hζ₀ne hζ0
  have hgΓ : rhoEquiv K g ∈ φ.range := by
    rw [d.range]
    exact Subgroup.mem_map.mpr ⟨g, CFSG.Open.StatedAPI.mem_statedSL_of_det hgdet, rfl⟩
  obtain ⟨s, hs⟩ := hgΓ
  obtain ⟨g', hg'⟩ := hctx₀.conj
  have hsQ : ∀ y ∈ Q, (s : G) * y * (s : G)⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (d.le_normalizer s.2) y).mp hy
  have hA₀Q : a₀ ∈ Q := hctx₀.le ha₀
  have haA : (s : G) * a₀ * (s : G)⁻¹ ∈ conjSubgroup (s : G) A₀ := by
    rw [mem_conjSubgroup]
    have e : (s : G)⁻¹ * ((s : G) * a₀ * (s : G)⁻¹) * (s : G) = a₀ := by group
    rw [e]
    exact ha₀
  have hψa : ψ (M₀.π ((s : G) * a₀ * (s : G)⁻¹)) = ζ := by
    have ha₀eq' : ψ (M₀.π a₀) = rhoEquiv K h₀ (p0 K) := ha₀eq
    rw [d.equivariant s a₀ hA₀Q, hs, ha₀eq']
    exact hgζ
  have haQ : (s : G) * a₀ * (s : G)⁻¹ ∈ Q := hsQ a₀ hA₀Q
  refine ⟨conjSubgroup (s : G) A₀, ⟨(s : G) * g', by rw [hg', conjSubgroup_mul]⟩, ?_, ?_,
    _, haA, hψa⟩
  · intro y hy
    have h1 : (s : G)⁻¹ * y * (s : G) ∈ Q := hctx₀.le (mem_conjSubgroup.mp hy)
    have e : y = (s : G) * ((s : G)⁻¹ * y * (s : G)) * (s : G)⁻¹ := by group
    rw [e]
    exact hsQ _ h1
  · intro hAZ
    have haZ : (s : G) * a₀ * (s : G)⁻¹ ∈ Z := hAZ ▸ haA
    apply hζ0
    rw [← hψa, (M₀.π_ker _ haQ).mpr haZ, map_zero]

end Points

end CFSG.RankThree.GF2n.Smith81
