module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {K : Type} [Field K] [CharP K 2]


@[expose] noncomputable def g2Lin (g : ↥(cayleyGroup K)) : (Ix3 → K) →ₗ[K] (Ix3 → K) :=
  zornLin (g : quasithinZorn K ≃ₗ[K] quasithinZorn K)

theorem g2Lin_apply (g : ↥(cayleyGroup K)) (x : Ix3 → K) : g2Lin g x = g2Act g x := rfl

theorem g2Lin_mul (g h : ↥(cayleyGroup K)) : g2Lin (g * h) = g2Lin g ∘ₗ g2Lin h :=
  LinearMap.ext fun x => g2Act_mul_apply g h x

theorem g2Lin_one : g2Lin (1 : ↥(cayleyGroup K)) = LinearMap.id :=
  LinearMap.ext fun x => by
    rw [g2Lin_apply, map_one]
    rfl

@[expose] noncomputable def g2Mat : ↥(cayleyGroup K) →* GL Ix3 K where
  toFun g :=
    { val := LinearMap.toMatrix' (g2Lin g)
      inv := LinearMap.toMatrix' (g2Lin g⁻¹)
      val_inv := by
        rw [← LinearMap.toMatrix'_comp, ← g2Lin_mul, mul_inv_cancel, g2Lin_one,
          LinearMap.toMatrix'_id]
      inv_val := by
        rw [← LinearMap.toMatrix'_comp, ← g2Lin_mul, inv_mul_cancel, g2Lin_one,
          LinearMap.toMatrix'_id] }
  map_one' := Units.ext (by
    change LinearMap.toMatrix' (g2Lin 1) = 1
    rw [g2Lin_one, LinearMap.toMatrix'_id])
  map_mul' g h := Units.ext (by
    change LinearMap.toMatrix' (g2Lin (g * h)) =
      LinearMap.toMatrix' (g2Lin g) * LinearMap.toMatrix' (g2Lin h)
    rw [g2Lin_mul, LinearMap.toMatrix'_comp])

theorem g2Mat_mulVec (g : ↥(cayleyGroup K)) (x : Ix3 → K) :
    ((g2Mat g : GL Ix3 K) : Matrix Ix3 Ix3 K).mulVec x = g2Act g x := by
  change (LinearMap.toMatrix' (g2Lin g)).mulVec x = _
  rw [LinearMap.toMatrix'_mulVec, g2Lin_apply]

theorem g2Mat_apply (g : ↥(cayleyGroup K)) (k l : Ix3) :
    ((g2Mat g : GL Ix3 K) : Matrix Ix3 Ix3 K) k l = g2Act g (Pi.single l 1) k := by
  change LinearMap.toMatrix' (g2Lin g) k l = _
  rw [LinearMap.toMatrix'_apply, g2Lin_apply]

theorem g2Mat_injective : Function.Injective (g2Mat (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine cayley_eq_one fun w => ?_
  rw [← g2Mat_mulVec, hg, Units.val_one, Matrix.one_mulVec]

noncomputable abbrev g2Gam (K : Type) [Field K] [CharP K 2] : Subgroup (GL Ix3 K) :=
  (g2Mat (K := K)).range

theorem hasScalarCommutant_g2Gam : HasScalarCommutant (g2Gam K) := by
  intro T hT
  refine commutant_cayley T fun g x => ?_
  rw [← g2Mat_mulVec, hT _ ⟨g, rfl⟩, g2Mat_mulVec]

@[expose] noncomputable def g2Rho : ↥(cayleyGroup K) →* MulAut (StdMod Ix3 K) :=
  matHom.comp g2Mat

theorem toAddMap_g2Rho (g : ↥(cayleyGroup K)) (v : Ix3 → K) :
    toAddMap (g2Rho g) v = g2Act g v :=
  g2Mat_mulVec g v

theorem g2Rho_injective : Function.Injective (g2Rho (K := K)) :=
  matHom_injective.comp g2Mat_injective

theorem range_g2Rho : (g2Rho (K := K)).range = natImage (g2Gam K) := by
  rw [g2Rho, MonoidHom.range_comp, natImage_eq_map]

theorem g2Rho_mem_natImage (g : ↥(cayleyGroup K)) : g2Rho g ∈ natImage (g2Gam K) := by
  rw [← range_g2Rho]
  exact ⟨g, rfl⟩

theorem g2Rho_mem_linSub (g : ↥(cayleyGroup K)) : g2Rho g ∈ linSub :=
  natImage_le_linSub _ (g2Rho_mem_natImage g)

@[expose] noncomputable def g2Phi : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(g2Gam K) :=
  (g2Mat (K := K)).rangeRestrict.comp (Subgroup.inclusion g2Derived_le)

theorem g2Phi_injective : Function.Injective (g2Phi (K := K)) := fun _ _ h =>
  Subgroup.inclusion_injective g2Derived_le (g2Mat_injective (congrArg Subtype.val h))

theorem g2Phi_surjective {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Function.Surjective (g2Phi (K := K)) := by
  rintro ⟨_, g, rfl⟩
  exact ⟨⟨g, (g2Derived_eq hc0 hc1).ge g.2⟩, rfl⟩

theorem lmG_lin (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (x : Ix3 → K) :
    (lmG K).lin γ x = ((g2Phi γ : GL Ix3 K) : Matrix Ix3 Ix3 K).mulVec x := by
  rw [show ((g2Phi γ : GL Ix3 K)) = g2Mat ⟨γ, g2Derived_le γ.2⟩ from rfl, g2Mat_mulVec]
  rfl

@[expose] def e6 : Ix3 ≃ Fin 6 where
  toFun k := ⟨ht k, ht_lt_six k⟩
  invFun i := bv i
  left_inv k := (eq_bv_of_ht (k := k) rfl).symm
  right_inv i := Fin.ext (ht_bv i.2)

@[expose] noncomputable def g2Six : ↥(cayleyGroup K) →* GL (Fin 6) K :=
  (Units.map (Matrix.reindexAlgEquiv K K e6).toMonoidHom).comp g2Mat

theorem g2Six_apply (g : ↥(cayleyGroup K)) (i j : Fin 6) :
    ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
      g2Act g (Pi.single (bv j) 1) (bv i) := by
  change Matrix.reindex e6 e6 ((g2Mat g : GL Ix3 K) : Matrix Ix3 Ix3 K) i j = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, g2Mat_apply]
  rfl

theorem g2Six_injective : Function.Injective (g2Six (K := K)) := by
  intro g h hgh
  apply g2Mat_injective
  apply Units.ext
  have := congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) hgh
  exact (Matrix.reindex e6 e6).injective this

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
