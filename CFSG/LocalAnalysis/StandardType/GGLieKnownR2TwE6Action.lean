module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Comm

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

@[expose] def twE6TorusMul {k : Type} [Field k] (θ : k →+* k) (t : k) (i : Fin 8) : k :=
  t ^ twE6Exp2 i * θ t ^ twE6Exp4 i

private theorem teAction_toWeight_rho (j : Fin (Tag.rank .E6)) (v : Fin (Tag.rank .E6) → ℤ) :
    MinData.toWeight (rho v) j = MinData.toWeight v (rhoPerm j) := by
  have hc : ∀ i j : Fin (Tag.rank .E6),
      Tag.cartan .E6 j (rhoPerm i) = Tag.cartan .E6 (rhoPerm j) i := by decide
  simp only [MinData.toWeight, rho, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp rhoPerm (fun i => Tag.cartan .E6 j i * v (rhoPerm.symm i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Equiv.symm_apply_apply, hc i j]

private theorem twE6_toWeight_nd2 (i : Fin 8) :
    MinData.toWeight (twE6Lift i) (nd 2) = twE6Exp2 i := by
  fin_cases i <;> decide +kernel

private theorem twE6_toWeight_nd4 (i : Fin 8) :
    MinData.toWeight (twE6Lift i) (nd 4) = twE6Exp4 i := by
  fin_cases i <;> decide +kernel

private theorem twE6_reflect_perm (i : Fin 8) :
    reflect .E6 (nd 2) (reflect .E6 (nd 4) (twE6Lift i)) = twE6Lift (twE6Perm i) := by
  fin_cases i <;> decide +kernel

private theorem teAction_hPairE_conj_xm
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (t : kˣ) (c : k) :
    hPairE θ (nd 2) (nd 4) t * e6Data_valid.xm k γ c *
        (hPairE θ (nd 2) (nd 4) t)⁻¹ =
      e6Data_valid.xm k γ ((t : k) ^ MinData.toWeight γ (nd 2) *
        (θ (t : k)) ^ MinData.toWeight γ (nd 4) * c) := by
  change e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map θ t) *
        e6Data_valid.xm k γ c *
        (e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map θ t))⁻¹ =
      e6Data_valid.xm k γ ((t : k) ^ MinData.toWeight γ (nd 2) *
        (θ (t : k)) ^ MinData.toWeight γ (nd 4) * c)
  rw [show e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map θ t) *
        e6Data_valid.xm k γ c *
        (e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map θ t))⁻¹
      = e6Data_valid.hm k (nd 2) t *
        (e6Data_valid.hm k (nd 4) (Units.map θ t) * e6Data_valid.xm k γ c *
          (e6Data_valid.hm k (nd 4) (Units.map θ t))⁻¹) *
        (e6Data_valid.hm k (nd 2) t)⁻¹ from by group]
  rw [e6Data_valid.hm_conj_xm k hγ (nd 4) (Units.map θ t) c,
    e6Data_valid.hm_conj_xm k hγ (nd 2) t _]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.coe_map, mul_assoc]
  rfl

private theorem nm24_conj_xm
    {k : Type} [Field k] [CharP k 2] {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (c : k) :
    e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) * e6Data_valid.xm k γ c *
        (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹ =
      e6Data_valid.xm k (reflect .E6 (nd 2) (reflect .E6 (nd 4) γ)) c := by
  obtain ⟨σ4, hσ4, h4⟩ := e6Data_valid.nm_conj_xm k hγ (nd 4)
  have hγ4 : IsRoot .E6 (reflect .E6 (nd 4) γ) := hγ.reflect (nd 4)
  obtain ⟨σ2, hσ2, h2⟩ := e6Data_valid.nm_conj_xm k hγ4 (nd 2)
  have hσ : σ2 * (σ4 * c) = c := by
    have e2 : σ2 = 1 := by rcases hσ2 with h | h <;> simp [h, CharTwo.neg_eq]
    have e4 : σ4 = 1 := by rcases hσ4 with h | h <;> simp [h, CharTwo.neg_eq]
    rw [e2, e4, one_mul, one_mul]
  calc e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) * e6Data_valid.xm k γ c *
        (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹
      = e6Data_valid.nm k (nd 2) *
          (e6Data_valid.nm k (nd 4) * e6Data_valid.xm k γ c *
            (e6Data_valid.nm k (nd 4))⁻¹) * (e6Data_valid.nm k (nd 2))⁻¹ := by group
    _ = e6Data_valid.nm k (nd 2) * e6Data_valid.xm k (reflect .E6 (nd 4) γ) (σ4 * c) *
          (e6Data_valid.nm k (nd 2))⁻¹ := by rw [h4]
    _ = e6Data_valid.xm k (reflect .E6 (nd 2) (reflect .E6 (nd 4) γ))
          (σ2 * (σ4 * c)) := h2 (σ4 * c)
    _ = e6Data_valid.xm k (reflect .E6 (nd 2) (reflect .E6 (nd 4) γ)) c := by rw [hσ]

theorem twE6_torus_conj
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (t : kˣ) :
    ∃ h ∈ hHat k θ twE6ShortNode, ∀ (i : Fin 8) (c : k),
      h * twE6X θ hθ i c * h⁻¹ = twE6X θ hθ i (twE6TorusMul θ (t : k) i * c) := by
  refine ⟨⟨hPairE θ (nd 2) (nd 4) t,
    hHatE_le_fixedGroup θ hθ twE6ShortNode ⟨t, rfl⟩⟩, ?_, ?_⟩
  · rw [hHat, Subgroup.mem_subgroupOf]
    change hPairE θ (nd 2) (nd 4) t ∈ (hPairE θ (nd 2) (nd 4)).range
    exact ⟨t, rfl⟩
  · intro i c
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [twE6X, twE6X, xPair_val]
    have hA := teAction_hPairE_conj_xm θ (twE6Lift_isRoot i) t c
    have hB := teAction_hPairE_conj_xm θ (isRoot_rho (twE6Lift_isRoot i)) t
      ((twistSign (twE6Lift i) : k) * θ c)
    have he2 : MinData.toWeight (twE6Lift i) (nd 2) = twE6Exp2 i := twE6_toWeight_nd2 i
    have he4 : MinData.toWeight (twE6Lift i) (nd 4) = twE6Exp4 i := twE6_toWeight_nd4 i
    have hr2 : MinData.toWeight (rho (twE6Lift i)) (nd 2) = twE6Exp4 i := by
      rw [teAction_toWeight_rho, show rhoPerm (nd 2) = nd 4 from by decide, he4]
    have hr4 : MinData.toWeight (rho (twE6Lift i)) (nd 4) = twE6Exp2 i := by
      rw [teAction_toWeight_rho, show rhoPerm (nd 4) = nd 2 from by decide, he2]
    calc hPairE θ (nd 2) (nd 4) t *
          (e6Data_valid.xm k (twE6Lift i) c *
            e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ c)) *
          (hPairE θ (nd 2) (nd 4) t)⁻¹
        = (hPairE θ (nd 2) (nd 4) t * e6Data_valid.xm k (twE6Lift i) c *
              (hPairE θ (nd 2) (nd 4) t)⁻¹) *
            (hPairE θ (nd 2) (nd 4) t *
              e6Data_valid.xm k (rho (twE6Lift i)) ((twistSign (twE6Lift i) : k) * θ c) *
              (hPairE θ (nd 2) (nd 4) t)⁻¹) := by group
      _ = e6Data_valid.xm k (twE6Lift i)
            ((t : k) ^ twE6Exp2 i * (θ (t : k)) ^ twE6Exp4 i * c) *
          e6Data_valid.xm k (rho (twE6Lift i))
            ((t : k) ^ twE6Exp4 i * (θ (t : k)) ^ twE6Exp2 i *
              ((twistSign (twE6Lift i) : k) * θ c)) := by
            rw [hA, hB, he2, he4, hr2, hr4]
      _ = e6Data_valid.xm k (twE6Lift i) (twE6TorusMul θ (t : k) i * c) *
          e6Data_valid.xm k (rho (twE6Lift i))
            ((twistSign (twE6Lift i) : k) * θ (twE6TorusMul θ (t : k) i * c)) := by
            have h1 : (t : k) ^ twE6Exp2 i * (θ (t : k)) ^ twE6Exp4 i * c =
                twE6TorusMul θ (t : k) i * c := by rw [twE6TorusMul]
            have h2 : (t : k) ^ twE6Exp4 i * (θ (t : k)) ^ twE6Exp2 i *
                  ((twistSign (twE6Lift i) : k) * θ c) =
                (twistSign (twE6Lift i) : k) *
                  θ (twE6TorusMul θ (t : k) i * c) := by
              simp only [twE6TorusMul, map_mul, map_zpow₀, hθ]
              ring
            rw [h1, h2]

theorem twE6_nHat_conj
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    nHat θ twE6ShortNode * twE6X θ hθ i c * (nHat θ twE6ShortNode)⁻¹ =
      twE6X θ hθ (twE6Perm i) c := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [nHat_val, twE6X, twE6X, xPair_val]
  have hNE : nHatE k twE6ShortNode =
      e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) := nHatE_two
  rw [hNE]
  have hA := nm24_conj_xm (twE6Lift_isRoot i) c
  have hB := nm24_conj_xm (isRoot_rho (twE6Lift_isRoot i))
    ((twistSign (twE6Lift i) : k) * θ c)
  have hw : reflect .E6 (nd 2) (reflect .E6 (nd 4) (rho (twE6Lift i))) =
      rho (reflect .E6 (nd 2) (reflect .E6 (nd 4) (twE6Lift i))) := by
    rw [← twReflectHom_two, ← twReflectHom_two]
    exact twReflect_rho (nf 2) (twE6Lift i)
  have hε : (twistSign (twE6Lift i) : k) = (twistSign (twE6Lift (twE6Perm i)) : k) := by
    rcases twistSign_eq_one_or (twE6Lift i) with h | h <;>
      rcases twistSign_eq_one_or (twE6Lift (twE6Perm i)) with h' | h' <;>
      simp [h, h', CharTwo.neg_eq]
  calc e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) *
        (e6Data_valid.xm k (twE6Lift i) c *
          e6Data_valid.xm k (rho (twE6Lift i))
            ((twistSign (twE6Lift i) : k) * θ c)) *
        (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹
      = (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) *
            e6Data_valid.xm k (twE6Lift i) c *
            (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹) *
          (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) *
            e6Data_valid.xm k (rho (twE6Lift i))
              ((twistSign (twE6Lift i) : k) * θ c) *
            (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹) := by group
    _ = e6Data_valid.xm k (reflect .E6 (nd 2) (reflect .E6 (nd 4) (twE6Lift i))) c *
          e6Data_valid.xm k (reflect .E6 (nd 2) (reflect .E6 (nd 4) (rho (twE6Lift i))))
            ((twistSign (twE6Lift i) : k) * θ c) := by rw [hA, hB]
    _ = e6Data_valid.xm k (twE6Lift (twE6Perm i)) c *
          e6Data_valid.xm k (rho (twE6Lift (twE6Perm i)))
            ((twistSign (twE6Lift (twE6Perm i)) : k) * θ c) := by
          rw [hw, twE6_reflect_perm i, hε]

end CFSG.StandardType.LieKnownR2.Short
