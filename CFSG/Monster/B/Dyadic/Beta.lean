module

public import CFSG.Monster.B.Dyadic.Lattice
public import CFSG.Monster.B.Dyadic.FixedLine

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native
open scoped Matrix

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℚ V]
  (R : Basis (Fin 4371) ℚ V) (ρ : G →* (V ≃ₗ[ℚ] V))

theorem lam_stable
    [Finite G] (gens : Fin 26 → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (s : G) :
    ∀ x ∈ Lam R, ρ s x ∈ Lam R := by
  let H : Submonoid G :=
    { carrier := {s | ∀ x ∈ Lam R, ρ s x ∈ Lam R}
      one_mem' := by
        show ∀ x ∈ Lam R, ρ 1 x ∈ Lam R
        intro x hx
        rw [map_one]
        exact hx
      mul_mem' := by
        intro a b ha hb
        have ha' : ∀ x ∈ Lam R, ρ a x ∈ Lam R := ha
        have hb' : ∀ x ∈ Lam R, ρ b x ∈ Lam R := hb
        show ∀ x ∈ Lam R, ρ (a * b) x ∈ Lam R
        intro x hx
        rw [map_mul, LinearEquiv.mul_apply]
        exact ha' _ (hb' x hx) }
  have hgens : Set.range gens ⊆ H := by
    rintro _ ⟨g, rfl⟩
    exact lam_mapsTo R g (ρ (gens g) : V →ₗ[ℚ] V) (hact g)
  have hle : Submonoid.closure (Set.range gens) ≤ H := Submonoid.closure_le.2 hgens
  rw [← Subgroup.closure_toSubmonoid_of_finite, hgen] at hle
  exact hle (Subgroup.mem_top s)

variable (hΛ : ∀ s, ∀ x ∈ Lam R, ρ s x ∈ Lam R)

@[expose] noncomputable def lamRep : G →* Module.End ℤ (Lam R) where
  toFun s := lamEnd R (ρ s : V →ₗ[ℚ] V) (hΛ s)
  map_one' := LinearMap.ext fun x => Subtype.ext (by
    show ((lamEnd R (ρ 1 : V →ₗ[ℚ] V) (hΛ 1) x : Lam R) : V) = (x : V)
    rw [coe_lamEnd, map_one]
    rfl)
  map_mul' a b := LinearMap.ext fun x => Subtype.ext (by
    show ((lamEnd R (ρ (a * b) : V →ₗ[ℚ] V) (hΛ (a * b)) x : Lam R) : V) =
      ((lamEnd R (ρ a : V →ₗ[ℚ] V) (hΛ a) (lamEnd R (ρ b : V →ₗ[ℚ] V) (hΛ b) x) : Lam R) : V)
    rw [coe_lamEnd, coe_lamEnd, coe_lamEnd, map_mul]
    rfl)

theorem modTwoMap_one {M : Type*} [AddCommGroup M] : modTwoMap (1 : Module.End ℤ M) = 1 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact modTwoMap_mkQ _ y

theorem modTwoMap_mul {M : Type*} [AddCommGroup M] (φ ψ : Module.End ℤ M) :
    modTwoMap (φ * ψ) = modTwoMap φ * modTwoMap ψ := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact modTwoMap_mkQ _ y

@[expose] noncomputable def modRep : G →* Module.End (ZMod 2) (ModN (Lam R) 2) where
  toFun s := modTwoMap (lamRep R ρ hΛ s)
  map_one' := by
    show modTwoMap (lamRep R ρ hΛ 1) = 1
    rw [map_one, modTwoMap_one]
  map_mul' a b := by
    show modTwoMap (lamRep R ρ hΛ (a * b)) =
      modTwoMap (lamRep R ρ hΛ a) * modTwoMap (lamRep R ρ hΛ b)
    rw [map_mul, modTwoMap_mul]

@[expose] noncomputable def bb :
    Basis (Fin 4371) (ZMod 2) (ModN (Lam R) 2) :=
  ModN.basis (ellZBasis R)

theorem modRep_basis_of
    {s : G} {sh : ℕ} {M : Array (Array (ℕ × UInt32))} {num : ℕ → ℕ → ℤ}
    (h : ReducesOn R (ρ s : V →ₗ[ℚ] V) sh M num) (k : Fin 4371) :
    modRep R ρ hΛ s (bb R k) = ∑ l, parMat sh M k l • bb R l :=
  modTwo_ell_of h (hΛ s) k

theorem modRep_gen_toMatrix
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (g : Fin 26) :
    (LinearMap.toMatrix (bb R) (bb R) (modRep R ρ hΛ (gens g))).transpose = Cmat g :=
  toMatrix_modTwo R g _ (hact g) (hΛ (gens g))

theorem modRep_gen_basis
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (g : Fin 26) (k : Fin 4371) :
    modRep R ρ hΛ (gens g) (bb R k) = ∑ l, Cmat g k l • bb R l :=
  modTwo_ell R g _ (hact g) (hΛ (gens g)) k

include hΛ in
theorem Cmat_isUnit
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (g : Fin 26) : IsUnit (Cmat g) := by
  have hu : IsUnit (LinearMap.toMatrix (bb R) (bb R) (modRep R ρ hΛ (gens g))) := by
    have h := ((Group.isUnit (gens g)).map (modRep R ρ hΛ)).map
      (LinearMap.toMatrixAlgEquiv (bb R))
    convert h using 1
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrixAlgEquiv_apply]
  rw [← modRep_gen_toMatrix R ρ hΛ gens hact g, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
  exact hu

theorem modRep_mrange [Finite G] (gens : Fin 26 → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤) :
    MonoidHom.mrange (modRep R ρ hΛ) =
      Submonoid.closure (Set.range fun g => modRep R ρ hΛ (gens g)) := by
  have hm : Submonoid.closure (Set.range gens) = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, hgen]
    rfl
  rw [MonoidHom.mrange_eq_map, ← hm, MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

@[expose] noncomputable def fbar :
    ModN (Lam R) 2 := (bb R).equivFun.symm fvec

theorem equivFun_sum
    (c : Fin 4371 → ZMod 2) : (bb R).equivFun (∑ l, c l • bb R l) = c := by
  rw [Basis.equivFun_apply, Basis.repr_sum_self]

theorem fbar_fixed
    (gens : Fin 26 → G) (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u) (s : G) :
    modRep R ρ hΛ s (fbar R) = fbar R := by
  let H : Subgroup G :=
    { carrier := {s | modRep R ρ hΛ s (fbar R) = fbar R}
      one_mem' := by
        show modRep R ρ hΛ 1 (fbar R) = fbar R
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro a b ha hb
        have ha' : modRep R ρ hΛ a (fbar R) = fbar R := ha
        have hb' : modRep R ρ hΛ b (fbar R) = fbar R := hb
        show modRep R ρ hΛ (a * b) (fbar R) = fbar R
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : modRep R ρ hΛ a (fbar R) = fbar R := ha
        show modRep R ρ hΛ a⁻¹ (fbar R) = fbar R
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have e1 : fbar R = ∑ k, fvec k • bb R k := by
    rw [fbar, Basis.equivFun_symm_apply]
  have hgens : Set.range gens ⊆ H := by
    rintro _ ⟨g, rfl⟩
    change modRep R ρ hΛ (gens g) (fbar R) = fbar R
    have key : modRep R ρ hΛ (gens g) (∑ k, fvec k • bb R k) =
        ∑ l, (fvec ᵥ* Cmat g) l • bb R l := by
      rw [map_sum]
      simp_rw [map_smul, modRep_gen_basis R ρ hΛ gens hact g, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_smul]
      rfl
    rw [e1, key, fvec_fixed g]
  have hle : Subgroup.closure (Set.range gens) ≤ H := (Subgroup.closure_le H).2 hgens
  rw [hgen] at hle
  exact hle (Subgroup.mem_top s)

@[expose] noncomputable def Phi :
    ModN (Lam R) 2 →ₗ[ZMod 2] (Fin 4370 → ZMod 2) :=
  Pmap ∘ₗ (bb R).equivFun.toLinearMap

theorem Phi_surjective :
    Function.Surjective (Phi R) :=
  Pmap_surjective.comp (bb R).equivFun.surjective

theorem Phi_apply
    (x : ModN (Lam R) 2) : Phi R x = Pmap ((bb R).equivFun x) := rfl

theorem mem_ker_Phi_iff
    (x : ModN (Lam R) 2) : x ∈ LinearMap.ker (Phi R) ↔ x = 0 ∨ x = fbar R := by
  rw [LinearMap.mem_ker, Phi_apply, Pmap_eq_zero_iff]
  constructor
  · rintro (h | h)
    · left
      exact (bb R).equivFun.injective (by rw [h, map_zero])
    · right
      rw [fbar, ← h, LinearEquiv.symm_apply_apply]
  · rintro (rfl | rfl)
    · left
      exact map_zero _
    · right
      rw [fbar, LinearEquiv.apply_symm_apply]

theorem ker_Phi_stable
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (s : G) :
    LinearMap.ker (Phi R) ≤ (LinearMap.ker (Phi R)).comap (modRep R ρ hΛ s) := by
  intro x hx
  rw [Submodule.mem_comap, mem_ker_Phi_iff]
  rcases (mem_ker_Phi_iff R x).1 hx with rfl | rfl
  · left
    exact map_zero _
  · right
    exact hf s

@[expose] noncomputable def coordQ :
    (ModN (Lam R) 2 ⧸ LinearMap.ker (Phi R)) ≃ₗ[ZMod 2] (Fin 4370 → ZMod 2) :=
  (Phi R).quotKerEquivOfSurjective (Phi_surjective R)

theorem coordQ_mk
    (x : ModN (Lam R) 2) :
    coordQ R (Submodule.Quotient.mk x) = Phi R x := rfl

@[expose] noncomputable def quotEnd
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (s : G) :
    Module.End (ZMod 2) (ModN (Lam R) 2 ⧸ LinearMap.ker (Phi R)) :=
  (LinearMap.ker (Phi R)).mapQ (LinearMap.ker (Phi R)) (modRep R ρ hΛ s)
    (ker_Phi_stable R ρ hΛ hf s)

theorem quotEnd_mk
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (s : G)
    (y : ModN (Lam R) 2) :
    quotEnd R ρ hΛ hf s (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (modRep R ρ hΛ s y) := rfl

@[expose] noncomputable def quotRep
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) :
    G →* Module.End (ZMod 2) (ModN (Lam R) 2 ⧸ LinearMap.ker (Phi R)) where
  toFun s := quotEnd R ρ hΛ hf s
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show quotEnd R ρ hΛ hf 1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
    rw [quotEnd_mk, map_one, Module.End.one_apply]
  map_mul' a b := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show quotEnd R ρ hΛ hf (a * b) (Submodule.Quotient.mk y) =
      quotEnd R ρ hΛ hf a (quotEnd R ρ hΛ hf b (Submodule.Quotient.mk y))
    rw [quotEnd_mk, quotEnd_mk, quotEnd_mk, map_mul, Module.End.mul_apply]

@[expose] noncomputable def betaLin
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (s : G) :
    Module.End (ZMod 2) (Fin 4370 → ZMod 2) :=
  (coordQ R).toLinearMap ∘ₗ quotRep R ρ hΛ hf s ∘ₗ (coordQ R).symm.toLinearMap

@[expose] noncomputable def betaMat
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) :
    G →* Matrix (Fin 4370) (Fin 4370) (ZMod 2) where
  toFun s := LinearMap.toMatrix' (betaLin R ρ hΛ hf s)
  map_one' := by
    show LinearMap.toMatrix' (betaLin R ρ hΛ hf 1) = 1
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [betaLin, LinearMap.comp_apply, map_one, Module.End.one_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  map_mul' a b := by
    show LinearMap.toMatrix' (betaLin R ρ hΛ hf (a * b)) =
      LinearMap.toMatrix' (betaLin R ρ hΛ hf a) * LinearMap.toMatrix' (betaLin R ρ hΛ hf b)
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [betaLin, LinearMap.comp_apply, map_mul, Module.End.mul_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

@[expose] noncomputable def beta
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) :
    G →* GL (Fin 4370) (ZMod 2) :=
  (betaMat R ρ hΛ hf).toHomUnits

theorem coe_beta
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (s : G) :
    ((beta R ρ hΛ hf s : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      betaMat R ρ hΛ hf s := rfl

theorem coordQ_symm_single
    (j : Fin 4370) :
    (coordQ R).symm (Pi.single j 1) = Submodule.Quotient.mk (bb R (pIdx.succAbove j)) := by
  rw [LinearEquiv.symm_apply_eq, coordQ_mk, Phi_apply]
  have : (bb R).equivFun (bb R (pIdx.succAbove j)) = Pi.single (pIdx.succAbove j) 1 := by
    funext k
    rw [Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = pIdx.succAbove j
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [this, Pmap_single]

theorem beta_of_basis
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) {s : G}
    {X : Matrix (Fin 4371) (Fin 4371) (ZMod 2)}
    (h : ∀ k, modRep R ρ hΛ s (bb R k) = ∑ l, X k l • bb R l) :
    ((beta R ρ hΛ hf s : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      (Matrix.of fun j t => Pmap (fun l => X (pIdx.succAbove j) l) t).transpose := by
  ext i j
  rw [coe_beta, Matrix.transpose_apply, Matrix.of_apply]
  change LinearMap.toMatrix' (betaLin R ρ hΛ hf s) i j = _
  rw [LinearMap.toMatrix'_apply, betaLin, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [coordQ_symm_single]
  change coordQ R (quotEnd R ρ hΛ hf s (Submodule.Quotient.mk (bb R (pIdx.succAbove j)))) i = _
  rw [quotEnd_mk, coordQ_mk, Phi_apply, h, equivFun_sum]

theorem beta_of_reducesOn
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) {s : G} {sh : ℕ}
    {M : Array (Array (ℕ × UInt32))} {num : ℕ → ℕ → ℤ}
    (h : ReducesOn R (ρ s : V →ₗ[ℚ] V) sh M num) :
    ((beta R ρ hΛ hf s : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      (Matrix.of fun j t => Pmap (fun l => parMat sh M (pIdx.succAbove j) l) t).transpose :=
  beta_of_basis R ρ hΛ hf (modRep_basis_of R ρ hΛ h)

theorem Pmap_parMat (sh : ℕ) (M : Array (Array (ℕ × UInt32))) (k : Fin 4371) (t : Fin 4370) :
    Pmap (fun l => parMat sh M k l) t =
      if rowBit (qRowBytes (bytesOfNat fixedVector) (binRow sh basisRowsK diagExpK M k)) t then 1
      else 0 := by
  unfold parMat
  rw [rowBit_qRowBytes _ _ t.2, Pmap_apply, srcIdx_eq t,
    rowBit_bytesOfNat _ (by have := (pIdx.succAbove t).2; omega)]
  exact (xor_ite_zmod2 _ _ _).symm

theorem beta_packet
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) {s : G} (j : ℕ)
    (hN : ∀ t, (ρ s : V →ₗ[ℚ] V) (R t) = ∑ u : Fin 4371, ((numerAt j t u : ℚ) / 8) • R u)
    (hok : ∀ i < 4371, (reduceRow 3 basisRowsK diagExpK (packetMat j) i).isSome) :
    ((beta R ρ hΛ hf s : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      (Matrix.of fun (i t : Fin 4370) => (if rowBit (qRowBytes (bytesOfNat fixedVector)
        (binRow 3 basisRowsK diagExpK (packetMat j) (pIdx.succAbove i))) t then 1
          else 0 : ZMod 2)).transpose := by
  rw [beta_of_reducesOn R ρ hΛ hf (reducesOn_packet R j _ hN hok)]
  ext a b
  rw [Matrix.transpose_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply,
    Pmap_parMat]

theorem beta_gen
    (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) (g : Fin 26) :
    ((beta R ρ hΛ hf (gens g) : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = (Qmat g).transpose := by
  rw [beta_of_basis R ρ hΛ hf (modRep_gen_basis R ρ hΛ gens hact g)]
  ext i j
  rw [Matrix.transpose_apply, Matrix.transpose_apply, Matrix.of_apply, Qmat_apply]

theorem beta_range
    (gens : Fin 26 → G) (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) :
    (beta R ρ hΛ hf).range = Subgroup.closure (Set.range fun g => beta R ρ hΛ hf (gens g)) := by
  rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem beta_injective
    [IsSimpleGroup G] (gens : Fin 26 → G)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) : Function.Injective (beta R ρ hΛ hf) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (beta R ρ hΛ hf).ker with h | h
  · exact h
  · exfalso
    have hmem : gens 25 ∈ (beta R ρ hΛ hf).ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have := beta_gen R ρ hΛ gens hact hf 25
    rw [hmem, Units.val_one] at this
    apply Q25_ne_one
    rw [← Matrix.transpose_transpose (Qmat 25), ← this, Matrix.transpose_one]

end CFSG.Monster.B.Dyadic
