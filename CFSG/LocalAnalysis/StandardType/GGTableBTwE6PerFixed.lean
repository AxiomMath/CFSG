module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerWeyl

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Chevalley.ExceptionalCover
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

namespace TwE6Per


variable {k : Type} [Field k] (θ : k →+* k)

theorem nm3_mem : e6Data_valid.nm k (nd 3) ∈ fixedGroup k θ := by
  rw [mem_fixedGroup, sigma_nm, rhoPerm_nd3]

theorem sElt3_mem {c : k} (hc : θ c = c) : sElt (nd 3) c ∈ fixedGroup k θ := by
  refine mul_mem (nm3_mem θ) ?_
  rw [mem_fixedGroup, sigma_xm_single, rhoPerm_nd3, hc]

theorem N1_mem : e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) ∈ fixedGroup k θ := by
  rw [← nHatE_three]
  exact sigma_nHatE θ (nf 3)

theorem N2_mem : e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) ∈ fixedGroup k θ := by
  rw [← nHatE_two]
  exact sigma_nHatE θ (nf 2)

theorem torusHom_mem {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) :
    torusHom k u ∈ fixedGroup k θ :=
  minTorus_mem_fixedGroup θ hu

theorem xth_mem {c : k} (hc : θ c = c) : e6Data_valid.xm k vth c ∈ fixedGroup k θ := by
  rw [mem_fixedGroup, sigma_xm θ isRoot_vth, rho_vth, twistSign_of_rho_eq isRoot_vth rho_vth,
    Int.cast_one, one_mul, hc]

variable [CharP k 2]

theorem conj_N2_mem {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k vb3) :
    e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) * x *
      (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹ ∈ rankOne k vb2 := by
  have e : e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) * x *
      (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4))⁻¹ =
      e6Data_valid.nm k (nd 2) * (e6Data_valid.nm k (nd 4) * x * (e6Data_valid.nm k (nd 4))⁻¹) *
        (e6Data_valid.nm k (nd 2))⁻¹ := by group
  rw [e, ← reflect_vb3]
  exact conj_mem_rankOne (isRoot_vb3.reflect _) _ (conj_mem_rankOne isRoot_vb3 _ hx)

theorem conj_N1_mem {x : e6Data_valid.minGroup k} (hx : x ∈ rankOne k vb2) :
    e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) * x *
      (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))⁻¹ ∈ rankOne k vb1 := by
  have e : e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) * x *
      (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))⁻¹ =
      e6Data_valid.nm k (nd 0) * (e6Data_valid.nm k (nd 5) * x * (e6Data_valid.nm k (nd 5))⁻¹) *
        (e6Data_valid.nm k (nd 0))⁻¹ := by group
  rw [e, ← reflect_vb2]
  exact conj_mem_rankOne (isRoot_vb2.reflect _) _ (conj_mem_rankOne isRoot_vb2 _ hx)

variable {θ}

section Elements

variable (hθ : ∀ c, θ (θ c) = c) (μ : kˣ) (hθμ : Units.map (θ : k →* k) μ = μ⁻¹)

omit
  [CharP k 2] in
theorem theta_c (hθμ : Units.map (θ : k →* k) μ = μ⁻¹) :
    θ ((μ : k) + ((μ⁻¹ : kˣ) : k)) = (μ : k) + ((μ⁻¹ : kˣ) : k) := by
  have h1 : θ (μ : k) = ((μ⁻¹ : kˣ) : k) := by
    have := congrArg (fun v : kˣ => (v : k)) hθμ
    simpa using this
  have h2 : θ ((μ⁻¹ : kˣ) : k) = (μ : k) := by
    have := congrArg (fun v : kˣ => (v⁻¹ : kˣ)) hθμ
    simp only [inv_inv] at this
    have h := congrArg (fun v : kˣ => (v : k)) this
    simpa [map_inv] using h
  rw [map_add, h1, h2, add_comm]

variable (θ) in
@[expose] noncomputable def uM1 : fixedGroup k θ := ⟨_, N1_mem θ⟩

variable (θ) in
@[expose] noncomputable def uM2 : fixedGroup k θ := ⟨_, N2_mem θ⟩

variable (θ) in
@[expose] noncomputable def uW3 : fixedGroup k θ := ⟨_, nm3_mem θ⟩

@[expose] noncomputable def uS3 : fixedGroup k θ := ⟨_, sElt3_mem θ (theta_c μ hθμ)⟩

@[expose] noncomputable def uS2 : fixedGroup k θ := uM2 θ * uS3 μ hθμ * (uM2 θ)⁻¹

@[expose] noncomputable def uS1 : fixedGroup k θ := uM1 θ * uS2 μ hθμ * (uM1 θ)⁻¹

variable (θ) in
@[expose] noncomputable def uW2 : fixedGroup k θ := uM2 θ * uW3 θ * (uM2 θ)⁻¹

variable (θ) in
@[expose] noncomputable def uW1 : fixedGroup k θ := uM1 θ * uW2 θ * (uM1 θ)⁻¹

@[expose] noncomputable def uT1 : fixedGroup k θ := ⟨_, torusHom_mem θ (isSymU_uOne θ hθ hθμ)⟩

@[expose] noncomputable def uT2 : fixedGroup k θ := ⟨_, torusHom_mem θ (isSymU_uTwo θ hθ hθμ)⟩

omit [CharP k 2] in
theorem val_S3_mem : ((uS3 μ hθμ : fixedGroup k θ) : e6Data_valid.minGroup k) ∈ rankOne k vb3 :=
  vb3_eq ▸ sElt_mem_rankOne (nd 3) _

omit [CharP k 2] in
theorem val_W3_mem : ((uW3 θ : fixedGroup k θ) : e6Data_valid.minGroup k) ∈ rankOne k vb3 :=
  vb3_eq ▸ nm_mem_rankOne (nd 3)

theorem val_S2_mem : ((uS2 μ hθμ : fixedGroup k θ) : e6Data_valid.minGroup k) ∈ rankOne k vb2 :=
  conj_N2_mem (val_S3_mem μ hθμ)

theorem val_W2_mem : ((uW2 θ : fixedGroup k θ) : e6Data_valid.minGroup k) ∈ rankOne k vb2 :=
  conj_N2_mem (val_W3_mem (θ := θ))

theorem val_S1_mem : ((uS1 μ hθμ : fixedGroup k θ) : e6Data_valid.minGroup k) ∈ rankOne k vb1 :=
  conj_N1_mem (val_S2_mem μ hθμ)

theorem val_W1_mem : ((uW1 θ : fixedGroup k θ) : e6Data_valid.minGroup k) ∈ rankOne k vb1 :=
  conj_N1_mem (val_W2_mem (θ := θ))

end Elements

end TwE6Per

end CFSG.StandardType
