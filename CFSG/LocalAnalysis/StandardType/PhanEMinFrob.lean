module

public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LocalAnalysis.StandardType.PhanEStdFrob

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {k k' : Type} [Field k] [Field k']
  (ι : k →+* k')

private theorem q2nPE_mapRange_digVec (d c : ℕ) :
    Finsupp.mapRange ι ι.map_zero (digVec k d c) = digVec k' d c := by
  unfold digVec
  split_ifs with h
  · rw [mapRange_smul_ringHom]
    simp only [Finsupp.mapRange_single, map_one, map_pow, map_neg]
  · exact Finsupp.mapRange_zero

private theorem q2nPE_minEndBC_toEnd (M : ℕ) :
    minEndBC ι (toEnd k D.d M) = toEnd k' D.d M :=
  minEnd_ext fun a => by
    rw [minEndBC_single, toEnd_single, toEnd_single, q2nPE_mapRange_digVec]

theorem minEndBC_rootOp (γ : Fin τ.rank → ℤ) :
    minEndBC ι (D.rootOp k γ) = D.rootOp k' γ := by
  unfold MinData.rootOp MinData.E
  split_ifs with h
  · exact q2nPE_minEndBC_toEnd ι (D.op (Nat.find h))
  · refine minEnd_ext fun a => ?_
    simp [minEndBC_single]

private theorem q2nPE_minUnitsBC_xu (γ : Fin τ.rank → ℤ) (c : k) :
    minUnitsBC ι (hV.xu k γ c) = hV.xu k' γ (ι c) := by
  ext1
  rw [coe_minUnitsBC, hV.xu_val, hV.xu_val, minEndBC_add, minEndBC_one, minEndBC_smul,
    minEndBC_rootOp]

theorem minBC_xm (γ : Fin τ.rank → ℤ) (c : k) :
    minBC hV ι (hV.xm k γ c) = hV.xm k' γ (ι c) :=
  Subtype.ext (q2nPE_minUnitsBC_xu hV ι γ c)

theorem minBC_nt (i : Fin τ.rank) (t : kˣ) :
    minBC hV ι (hV.nt k i t) = hV.nt k' i (Units.map (ι : k →* k') t) := by
  change minBC hV ι (hV.xm k (Pi.single i 1) t *
      hV.xm k (-Pi.single i 1) (-((t⁻¹ : kˣ) : k)) * hV.xm k (Pi.single i 1) t) =
    hV.xm k' (Pi.single i 1) ((Units.map (ι : k →* k') t : k'ˣ) : k') *
      hV.xm k' (-Pi.single i 1) (-((((Units.map (ι : k →* k') t)⁻¹ : k'ˣ)) : k')) *
        hV.xm k' (Pi.single i 1) ((Units.map (ι : k →* k') t : k'ˣ) : k')
  rw [map_mul, map_mul, minBC_xm, minBC_xm]
  have h1 : ι (-((t⁻¹ : kˣ) : k)) = -((((Units.map (ι : k →* k') t)⁻¹ : k'ˣ)) : k') := by
    rw [map_neg, ← map_inv (Units.map (ι : k →* k')) t, Units.coe_map]
    rfl
  rw [h1]
  rfl

theorem minBC_nm (i : Fin τ.rank) : minBC hV ι (hV.nm k i) = hV.nm k' i := by
  change minBC hV ι (hV.nt k i 1) = hV.nt k' i 1
  rw [minBC_nt, map_one]

theorem minBC_hm (i : Fin τ.rank) (t : kˣ) :
    minBC hV ι (hV.hm k i t) = hV.hm k' i (Units.map (ι : k →* k') t) := by
  change minBC hV ι (hV.nt k i t * (hV.nt k i 1)⁻¹) =
    hV.nt k' i (Units.map (ι : k →* k') t) * (hV.nt k' i 1)⁻¹
  rw [map_mul, map_inv, minBC_nt, minBC_nt, map_one]

theorem map_rootGroup_minBC_le (γ : Fin τ.rank → ℤ) :
    (hV.rootGroup k γ).map (minBC hV ι) ≤ hV.rootGroup k' γ := by
  rintro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
  rw [minBC_xm]
  exact hV.xm_mem_rootGroup k' γ (ι c)

theorem map_torus_minBC_le (i : Fin τ.rank) :
    (hV.torus k i).map (minBC hV ι) ≤ hV.torus k' i := by
  rintro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hx
  rw [minBC_hm]
  exact hV.hm_mem_torus k' i (Units.map (ι : k →* k') t)

theorem minBC_involutive (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (g : hV.minGroup k) :
    minBC hV θ (minBC hV θ g) = g := by
  have h : (minBC hV θ).comp (minBC hV θ) = MonoidHom.id (hV.minGroup k) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top hV k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · show minBC hV θ (minBC hV θ (hV.xm k (Pi.single i 1) c)) = hV.xm k (Pi.single i 1) c
      rw [minBC_xm, minBC_xm, hθ]
    · show minBC hV θ (minBC hV θ (hV.xm k (-Pi.single i 1) c)) = hV.xm k (-Pi.single i 1) c
      rw [minBC_xm, minBC_xm, hθ]
  exact DFunLike.congr_fun h g

variable (hA : TauCeti.IsFiniteType τ.cartan)

theorem map_posUnipotent_minBC_le (θ : k →+* k) :
    (posUnipotent (hV.minDatum hA k)).map (minBC hV θ) ≤ posUnipotent (hV.minDatum hA k) := by
  unfold CFSG.LieType.Steinberg.posUnipotent
  rw [Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hγ => le_iSup₂_of_le γ hγ (map_rootGroup_minBC_le hV θ γ)

theorem map_iSup_torus_minBC_le (θ : k →+* k) :
    (⨆ i, hV.torus k i).map (minBC hV θ) ≤ ⨆ i, hV.torus k i := by
  rw [Subgroup.map_iSup]
  exact iSup_le fun i => (map_torus_minBC_le hV θ i).trans (le_iSup _ i)

@[expose] noncomputable def minFrobData (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {w₀ : (coxeterMatrix hA).Group}
    (hop : ∀ i, w₀ * (coxeterMatrix hA).toCoxeterSystem.simple i * w₀ =
      (coxeterMatrix hA).toCoxeterSystem.simple i) :
    FrobData (hV.minDatum hA k) (hV.nm k) (hV.torus k) w₀ where
  φ := minBC hV θ
  invol := minBC_involutive hV θ hθ
  op := id
  hop := hop
  pos := map_posUnipotent_minBC_le hV hA θ
  torus := map_iSup_torus_minBC_le hV θ
  n_map i := minBC_nm hV θ i

end CFSG.ClassicalInvolution.Phan.PhanE
