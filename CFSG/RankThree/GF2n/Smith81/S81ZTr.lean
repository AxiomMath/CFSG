module

public import CFSG.RankThree.GF2n.Smith81.S81ZTrG
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81XE7Fin
public import CFSG.RankThree.GF2n.Smith81.S81XE7Grp

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z.Tr

variable {K K' : Type} [Field K] [Field K']

theorem vMapG_digVec (σ : K ≃+* K') (d c : ℕ) :
    vMapG σ (digVec K d c) = digVec K' d c := by
  unfold digVec
  split_ifs with h
  · rw [vMapG_smul, vMapG_single, map_pow, map_neg, map_one]
  · exact map_zero _

theorem twistEnd_toEnd (σ : K ≃+* K') (d M : ℕ) :
    twistEnd σ (toEnd K d M) = toEnd K' d M := by
  unfold toEnd
  rw [twistEnd_linearCombination]
  congr 1
  funext a
  exact vMapG_digVec σ d _

theorem twistEnd_rootOp (σ : K ≃+* K') (γ : Fin (Tag.rank .E7) → ℤ) :
    twistEnd σ (e7Data.rootOp K γ) = e7Data.rootOp K' γ := by
  classical
  unfold MinData.rootOp
  by_cases h : ∃ k, k < (Tag.rootCertificate .E7).roots.length ∧ (Tag.rootCertificate .E7).root k = γ
  · rw [dif_pos h, dif_pos h]
    exact twistEnd_toEnd σ _ _
  · rw [dif_neg h, dif_neg h]
    exact twistEnd_zero σ

@[expose] def twistUnits (σ : K ≃+* K') :
    (Module.End K (V K))ˣ ≃* (Module.End K' (V K'))ˣ :=
  Units.mapEquiv (twistEndEquiv σ)

theorem twistUnits_val (σ : K ≃+* K') (u : (Module.End K (V K))ˣ) :
    ((twistUnits σ u : (Module.End K' (V K'))ˣ) : Module.End K' (V K')) =
      twistEnd σ (u : Module.End K (V K)) := rfl

theorem twistUnits_xu (σ : K ≃+* K') (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    twistUnits σ (e7Data_valid.xu K γ c) = e7Data_valid.xu K' γ (σ c) := by
  apply Units.ext
  rw [twistUnits_val, e7Data_valid.xu_val, e7Data_valid.xu_val, twistEnd_add, twistEnd_one,
    twistEnd_smul, twistEnd_rootOp]

theorem twistUnits_mem_minGroup (σ : K ≃+* K') {u : (Module.End K (V K))ˣ}
    (hu : u ∈ e7Data_valid.minGroup K) : twistUnits σ u ∈ e7Data_valid.minGroup K' := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, c, rfl⟩ := hx
    rw [twistUnits_xu]
    exact e7Data_valid.xu_mem K' γ (σ c)
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem twistUnits_symm_twistUnits (σ : K ≃+* K') (u : (Module.End K (V K))ˣ) :
    twistUnits σ.symm (twistUnits σ u) = u := by
  apply Units.ext
  rw [twistUnits_val, twistUnits_val, twistEnd_trans, RingEquiv.self_trans_symm, twistEnd_refl]

theorem twistUnits_twistUnits_symm (σ : K ≃+* K') (u : (Module.End K' (V K'))ˣ) :
    twistUnits σ (twistUnits σ.symm u) = u := by
  apply Units.ext
  rw [twistUnits_val, twistUnits_val, twistEnd_trans, RingEquiv.symm_trans_self, twistEnd_refl]

@[expose] def twistGp (σ : K ≃+* K') : Gp K ≃* Gp K' where
  toFun g := ⟨twistUnits σ g.1, twistUnits_mem_minGroup σ g.2⟩
  invFun g := ⟨twistUnits σ.symm g.1, twistUnits_mem_minGroup σ.symm g.2⟩
  left_inv g := Subtype.ext (twistUnits_symm_twistUnits σ g.1)
  right_inv g := Subtype.ext (twistUnits_twistUnits_symm σ g.1)
  map_mul' g h := Subtype.ext (map_mul (twistUnits σ) g.1 h.1)

theorem twistGp_xE (σ : K ≃+* K') (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    twistGp σ (xE γ c) = xE γ (σ c) :=
  Subtype.ext (twistUnits_xu σ γ c)

theorem twistGp_nt (σ : K ≃+* K') (j : Fin (Tag.rank .E7)) (t : Kˣ) :
    twistGp σ (e7Data_valid.nt K j t) = e7Data_valid.nt K' j (Units.map (σ : K →* K') t) := by
  unfold MinData.Valid.nt
  rw [map_mul, map_mul, twistGp_xE, twistGp_xE]
  have h : σ (-(((t⁻¹ : Kˣ)) : K)) = -((((Units.map (σ : K →* K') t)⁻¹ : K'ˣ)) : K') := by
    rw [map_neg]
    congr 1
  have h2 : (((Units.map (σ : K →* K') t : K'ˣ)) : K') = σ (t : K) := rfl
  rw [h, h2]

theorem twistGp_nm (σ : K ≃+* K') (j : Fin (Tag.rank .E7)) :
    twistGp σ (e7Data_valid.nm K j) = e7Data_valid.nm K' j := by
  have := twistGp_nt σ j 1
  rw [map_one] at this
  exact this

theorem twistGp_hm (σ : K ≃+* K') (j : Fin (Tag.rank .E7)) (t : Kˣ) :
    twistGp σ (e7Data_valid.hm K j t) = e7Data_valid.hm K' j (Units.map (σ : K →* K') t) := by
  unfold MinData.Valid.hm
  rw [map_mul, map_inv, twistGp_nt, twistGp_nt, map_one]

theorem twistGp_UA (σ : K ≃+* K') : (UA K a7).map (twistGp σ).toMonoidHom = UA K' a7 := by
  unfold UA
  rw [MonoidHom.map_closure]
  congr 1
  ext g'
  constructor
  · rintro ⟨g, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, σ c, (twistGp_xE σ γ c)⟩
  · rintro ⟨γ, hγ, c', rfl⟩
    exact ⟨xE γ (σ.symm c'), ⟨γ, hγ, σ.symm c', rfl⟩, by
      show twistGp σ (xE γ (σ.symm c')) = _
      rw [twistGp_xE, RingEquiv.apply_symm_apply]⟩

variable (K) in
@[expose] def eAutEquiv : Gp K ≃* ↥(EAut K) :=
  Subgroup.equivMapOfInjective (EGrp K) (vAut K).toMonoidHom (vAut K).injective

theorem eAutEquiv_apply (g : Gp K) (v : V K) :
    ((eAutEquiv K g : ↥(EAut K)) : V K ≃ₗ[K] V K) v = endoE g v := rfl

@[expose] def twistEAut (σ : K ≃+* K') : ↥(EAut K) ≃* ↥(EAut K') :=
  (eAutEquiv K).symm.trans ((twistGp σ).trans (eAutEquiv K'))

end CFSG.RankThree.GF2n.Smith81.S81Z
