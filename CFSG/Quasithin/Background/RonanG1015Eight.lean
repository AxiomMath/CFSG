module

public import CFSG.Quasithin.Background.RonanG1015OuterOrth
public import CFSG.Quasithin.Background.RonanG1015EightModel
public import CFSG.Quasithin.Background.RonanG1015EightAbs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.Open CFSG.GroupTheory.WeirSylow
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv)

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem eight_induced [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 8)
    (hplus : IsPlusType (p4insporth_quad hq)) {K : Subgroup (GLV U)}
    (hK : K = ⁅orthSub q, orthSub q⁆) {Q : Subgroup (GLV U)} {v : U} (hv0 : v ≠ 0)
    (hqv : q v = 0) (hQO : Q ≤ orthSub q) (hvp : v ∈ perp f v)
    (hfull : FullTransvections Q (perp f v) v hvp)
    (hZ : ∀ z : ↥K, (∀ m, z * m = m * z) → z = 1) (α : ↥K ≃* ↥K)
    (hcomm : ∀ y ∈ Q, ∀ k k' : ↥K, (k' : GLV U) = y * (k : GLV U) * y⁻¹ →
      ((α k' : ↥K) : GLV U) = y * ((α k : ↥K) : GLV U) * y⁻¹) :
    ∃ g : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = g * (k : GLV U) * g⁻¹ := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (p4insporth_nondegenerate_quad hf hq) (n := 4)
    (by omega) hplus
  set ψ : U ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2) := e.toLinearEquiv with hψdef
  have hψ : ∀ x, StatedQuadPlus 4 (ZMod 2) (ψ x) = q x := fun x => by
    have := e.map_app x
    rw [p4insporth_quad_apply] at this
    rw [← CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact this
  set Φ : GLV U ≃* GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
    (p4insporth_cg ψ).trans (toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2)).symm with hΦdef
  have hKΦ : K.map Φ.toMonoidHom = StatedOmega (StatedQuadPlus 4 (ZMod 2)) := by
    rw [hK]
    exact map_commutator_eq_statedOmega (CFSG.LieType.Universal.Spin.coe_quadPlus 4 (ZMod 2)) ψ hψ
  have hΦ : ∀ (g : GLV U) (z : Fin 4 ⊕ Fin 4 → ZMod 2),
      ((Φ g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec z = ψ (g (ψ.symm z)) := by
    intro g z
    rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    have : toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (Φ g) = p4insporth_cg ψ g :=
      MulEquiv.apply_symm_apply _ _
    rw [this]
    rfl
  by_cases hQK : ∀ y ∈ Q, y ∈ K
  ·
    have hKO : K ≤ orthSub q := hK ▸ p4insporth_comm_le_self _
    have hQK' : Q ≤ K := fun y hy => hQK y hy
    let S : QSetting f q Q v := ⟨hf, hq, hv0, hqv, by omega, hQO, hvp, hfull⟩
    have hfixQ := fix_Q_of_commute hQK' α hZ hcomm
    have hfixQ' : ∀ (y : GLV U) (hy : y ∈ Q), α.symm ⟨y, hQK' hy⟩ = ⟨y, hQK' hy⟩ :=
      fun y hy => by
        rw [MulEquiv.symm_apply_eq]
        exact (hfixQ y hy).symm
    have h1 := alpha_fix_v S hKO hQK' α hfixQ
    have h2 : ∀ k : ↥K, ((α k : ↥K) : GLV U) v = v → (k : GLV U) v = v := fun k hk => by
      have := alpha_fix_v S hKO hQK' α.symm hfixQ' (α k) hk
      simpa using this
    have hw0 : ψ v ≠ 0 := fun h => hv0 (ψ.map_eq_zero_iff.1 h)
    have hQw : (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) (ψ v) = 0 := by
      have h := congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus 4 (ZMod 2)) (ψ v)
      rw [h, hψ, hqv]
    have hfix_iff : ∀ k : ↥K,
        (((subEquiv Φ hKΦ k : ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2)))) :
          GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec (ψ v) = ψ v ↔
          (k : GLV U) v = v := by
      intro k
      rw [coe_subEquiv, hΦ, LinearEquiv.symm_apply_apply]
      exact ψ.injective.eq_iff
    have hind := inducedByIso_of_fix (transportAut Φ hKΦ α) hw0 hQw
      (fun x hx => by
        obtain ⟨k, rfl⟩ := (subEquiv Φ hKΦ).surjective x
        rw [transportAut_apply]
        exact (hfix_iff (α k)).2 (h1 k ((hfix_iff k).1 hx)))
      (fun x hx => by
        obtain ⟨k, rfl⟩ := (subEquiv Φ hKΦ).surjective x
        rw [transportAut_apply] at hx
        exact (hfix_iff k).2 (h2 k ((hfix_iff (α k)).1 hx)))
    obtain ⟨g', -, hg'⟩ := hind
    exact induced_of_transport Φ hKΦ α g' hg'
  ·
    push Not at hQK
    obtain ⟨y, hyQ, hyK⟩ := hQK
    have hgiso : Φ y ∈ CFSG.LieType.ChevTwo.isoGrp (StatedQuadPlus 4 (ZMod 2)) := by
      intro x
      show StatedQuadPlus 4 (ZMod 2) (((Φ y : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec x) = StatedQuadPlus 4 (ZMod 2) x
      rw [hΦ, hψ, hQO hyQ (ψ.symm x), ← hψ, LinearEquiv.apply_symm_apply]
    have hgΩ : Φ y ∉ StatedOmega (StatedQuadPlus 4 (ZMod 2)) := by
      intro h
      rw [← hKΦ] at h
      obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 h
      exact hyK ((Φ.injective hkg) ▸ hk)
    have hnormal : ∀ k : ↥K, y * (k : GLV U) * y⁻¹ ∈ K := fun k => by
      have hk : (k : GLV U) ∈ ⁅orthSub q, orthSub q⁆ := hK ▸ k.2
      have hmem : ∀ z : GLV U, z ∈ ⁅orthSub q, orthSub q⁆ → z ∈ K := fun z hz => hK ▸ hz
      exact hmem _ ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.ChevTwo.OrthBasic.le_normalizer_commutator (orthSub q) (hQO hyQ)) _).mp hk)
    have e2 : ∀ k : ↥K, CFSG.LieType.ChevTwo.kappa (StatedQuadPlus 4 (ZMod 2)) ⟨Φ y, hgiso⟩
        (subEquiv Φ hKΦ k) = subEquiv Φ hKΦ ⟨y * (k : GLV U) * y⁻¹, hnormal k⟩ := fun k =>
      Subtype.ext (by
        rw [CFSG.LieType.ChevTwo.kappa_apply_val, coe_subEquiv, coe_subEquiv, map_mul, map_mul,
          map_inv])
    have hcommα' : transportAut Φ hKΦ α * CFSG.LieType.ChevTwo.kappa
        (StatedQuadPlus 4 (ZMod 2)) ⟨Φ y, hgiso⟩ = CFSG.LieType.ChevTwo.kappa
        (StatedQuadPlus 4 (ZMod 2)) ⟨Φ y, hgiso⟩ * transportAut Φ hKΦ α := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨k, rfl⟩ := (subEquiv Φ hKΦ).surjective x
      have e3 : α ⟨y * (k : GLV U) * y⁻¹, hnormal k⟩ =
          ⟨y * ((α k : ↥K) : GLV U) * y⁻¹, hnormal (α k)⟩ :=
        Subtype.ext (hcomm y hyQ k _ rfl)
      calc _ = transportAut Φ hKΦ α (CFSG.LieType.ChevTwo.kappa (StatedQuadPlus 4 (ZMod 2))
            ⟨Φ y, hgiso⟩ (subEquiv Φ hKΦ k)) := rfl
        _ = transportAut Φ hKΦ α (subEquiv Φ hKΦ ⟨y * (k : GLV U) * y⁻¹, hnormal k⟩) := by
          rw [e2]
        _ = subEquiv Φ hKΦ (α ⟨y * (k : GLV U) * y⁻¹, hnormal k⟩) := transportAut_apply _ _ _ _
        _ = subEquiv Φ hKΦ ⟨y * ((α k : ↥K) : GLV U) * y⁻¹, hnormal (α k)⟩ := by rw [e3]
        _ = CFSG.LieType.ChevTwo.kappa (StatedQuadPlus 4 (ZMod 2)) ⟨Φ y, hgiso⟩
            (subEquiv Φ hKΦ (α k)) := (e2 (α k)).symm
        _ = CFSG.LieType.ChevTwo.kappa (StatedQuadPlus 4 (ZMod 2)) ⟨Φ y, hgiso⟩
            (transportAut Φ hKΦ α (subEquiv Φ hKΦ k)) := by rw [transportAut_apply]
        _ = _ := rfl
    obtain ⟨g', -, hg'⟩ := CFSG.LieType.ChevTwo.commute_plusEight hgiso hgΩ _ hcommα'
    exact induced_of_transport Φ hKΦ α g' hg'

end RonanG1015

end CFSG.Quasithin
