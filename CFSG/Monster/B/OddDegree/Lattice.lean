module

public import CFSG.Monster.B.Gen.MinkowskiTwo
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Monster.B.OddDegree

open Module Matrix

variable {G : Type*} [Group G] {n : ℕ} (ρ : G →* GL (Fin n) ℚ)

@[expose] noncomputable def lat : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ (Set.range fun p : G × Fin n =>
    (ρ p.1 : Matrix (Fin n) (Fin n) ℚ) *ᵥ Pi.single p.2 1)

theorem single_mem_lat (i : Fin n) : (Pi.single i 1 : Fin n → ℚ) ∈ lat ρ :=
  Submodule.subset_span ⟨(1, i), by
    show (ρ 1 : Matrix (Fin n) (Fin n) ℚ) *ᵥ Pi.single i 1 = Pi.single i 1
    rw [map_one, Units.val_one, one_mulVec]⟩

theorem mulVec_mem_lat (g : G) {x : Fin n → ℚ} (hx : x ∈ lat ρ) :
    (ρ g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x ∈ lat ρ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hy
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul]
    exact Submodule.subset_span ⟨(g * h, i), rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℚ, mulVec_smul, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ a hx

@[expose] noncomputable def latEnd (g : G) : lat ρ →ₗ[ℤ] lat ρ :=
  ((Matrix.mulVecLin (ρ g : Matrix (Fin n) (Fin n) ℚ)).restrictScalars ℤ).restrict
    fun _ hx => mulVec_mem_lat ρ g hx

theorem coe_latEnd (g : G) (x : lat ρ) :
    ((latEnd ρ g x : lat ρ) : Fin n → ℚ) = (ρ g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x := rfl

theorem latEnd_mul (g h : G) : latEnd ρ (g * h) = latEnd ρ g ∘ₗ latEnd ρ h := by
  ext x : 1
  apply Subtype.ext
  rw [LinearMap.comp_apply, coe_latEnd, coe_latEnd, coe_latEnd, map_mul, Units.val_mul,
    mulVec_mulVec]

theorem latEnd_one : latEnd ρ 1 = LinearMap.id := by
  ext x : 1
  apply Subtype.ext
  rw [coe_latEnd, map_one, Units.val_one, one_mulVec, LinearMap.id_apply]

theorem eq_one_of_latEnd {g : G} (h : latEnd ρ g = LinearMap.id) : ρ g = 1 := by
  apply Units.ext
  rw [Units.val_one]
  ext i j
  have hj := congrArg (fun f : lat ρ →ₗ[ℤ] lat ρ => ((f ⟨_, single_mem_lat ρ j⟩ : lat ρ) :
    Fin n → ℚ) i) h
  simp only [coe_latEnd, LinearMap.id_apply] at hj
  rw [mulVec_single_one] at hj
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hj

variable [Finite G]

instance : Module.Finite ℤ (lat ρ) := by
  have : Finite (G × Fin n) := inferInstance
  exact Module.Finite.span_of_finite ℤ (Set.finite_range _)

instance : Module.Free ℤ (lat ρ) := Module.free_of_finite_type_torsion_free'

theorem finrank_lat : finrank ℤ (lat ρ) = n := by
  apply le_antisymm
  · let b := Module.Free.chooseBasis ℤ (lat ρ)
    have hli : LinearIndependent ℤ fun i => ((b i : lat ρ) : Fin n → ℚ) :=
      b.linearIndependent.map' (lat ρ).subtype (Submodule.ker_subtype _)
    have hliQ := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
    rw [Module.finrank_eq_card_chooseBasisIndex]
    simpa using hliQ.fintype_card_le_finrank
  · have hliQ : LinearIndependent ℚ fun i : Fin n => (Pi.single i 1 : Fin n → ℚ) := by
      have h := (Pi.basisFun ℚ (Fin n)).linearIndependent
      have he : ⇑(Pi.basisFun ℚ (Fin n)) = fun i => (Pi.single i 1 : Fin n → ℚ) :=
        funext fun i => Pi.basisFun_apply ℚ (Fin n) i
      rw [he] at h
      exact h
    have hliZ := (LinearIndependent.iff_fractionRing ℤ ℚ).2 hliQ
    have hli : LinearIndependent ℤ fun i : Fin n => (⟨Pi.single i 1, single_mem_lat ρ i⟩ : lat ρ) :=
      LinearIndependent.of_comp (lat ρ).subtype hliZ
    simpa using hli.fintype_card_le_finrank

@[expose] noncomputable def latBasis : Module.Basis (Fin n) ℤ (lat ρ) :=
  Module.finBasisOfFinrankEq ℤ (lat ρ) (finrank_lat ρ)

@[expose] noncomputable def intMatHom : G →* Matrix (Fin n) (Fin n) ℤ where
  toFun g := LinearMap.toMatrix (latBasis ρ) (latBasis ρ) (latEnd ρ g)
  map_one' := by rw [latEnd_one, LinearMap.toMatrix_id (latBasis ρ)]
  map_mul' g h := by
    rw [latEnd_mul, LinearMap.toMatrix_comp (latBasis ρ) (latBasis ρ) (latBasis ρ)]

@[expose] noncomputable def intRep : G →* GL (Fin n) ℤ := (intMatHom ρ).toHomUnits

theorem coe_intRep (g : G) :
    ((intRep ρ g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) =
      LinearMap.toMatrix (latBasis ρ) (latBasis ρ) (latEnd ρ g) := rfl

theorem intRep_injective (hρ : Function.Injective ρ) : Function.Injective (intRep ρ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h1 : LinearMap.toMatrix (latBasis ρ) (latBasis ρ) (latEnd ρ g) = 1 := by
    rw [← coe_intRep, hg, Units.val_one]
  have h2 : latEnd ρ g = LinearMap.id := by
    rw [← LinearMap.toMatrix_id (latBasis ρ)] at h1
    exact (LinearMap.toMatrix (latBasis ρ) (latBasis ρ)).injective h1
  rw [Subgroup.mem_bot]
  exact hρ ((eq_one_of_latEnd ρ h2).trans (map_one ρ).symm)

@[expose] noncomputable def modRep : G →* GL (Fin n) (ZMod 2) :=
  (Units.map (Int.castRingHom (ZMod 2)).mapMatrix.toMonoidHom).comp (intRep ρ)

theorem coe_modRep (g : G) :
    ((modRep ρ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((intRep ρ g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom (ZMod 2)) :=
  rfl

theorem divTwoPow_one_of_map_eq_one {M : Matrix (Fin n) (Fin n) ℤ}
    (h : M.map (Int.castRingHom (ZMod 2)) = 1) : DivTwoPow 1 (M - 1) := by
  refine ⟨Matrix.of fun i j => (M - 1) i j / 2, ?_⟩
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.map_apply, eq_intCast, Matrix.one_apply] at hij
  have h0 : (((M - 1) i j : ℤ) : ZMod 2) = 0 := by
    rw [Matrix.sub_apply, Int.cast_sub, hij, Matrix.one_apply]
    split_ifs <;> simp
  have hdvd : (2 : ℤ) ∣ (M - 1) i j := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((M - 1) i j) 2).1 h0
    exact_mod_cast this
  rw [Matrix.smul_apply, Matrix.of_apply, pow_one, smul_eq_mul, Int.mul_ediv_cancel' hdvd]

theorem sq_mem_ker_of_mem_ker_modRep {g : G} (hg : modRep ρ g = 1) : intRep ρ (g ^ 2) = 1 := by
  have hmod : ((intRep ρ g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ).map
      (Int.castRingHom (ZMod 2)) = 1 := by
    rw [← coe_modRep, hg, Units.val_one]
  have hpos : 0 < orderOf g := orderOf_pos g
  have hpow : ((intRep ρ g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) ^ orderOf g = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hsq := sq_eq_one_of_modTwo_of_pow_eq_one (divTwoPow_one_of_map_eq_one hmod) hpos hpow
  apply Units.ext
  rw [map_pow, Units.val_pow_eq_pow_val, hsq, Units.val_one]

theorem modRep_injective [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hρ : Function.Injective ρ) : Function.Injective (modRep ρ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (modRep ρ).ker with h | h
  · exact h
  · exfalso
    have hsq : ∀ g : G, g ^ 2 = 1 := by
      intro g
      have hg : modRep ρ g = 1 := (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top g)
      exact intRep_injective ρ hρ ((sq_mem_ker_of_mem_ker_modRep ρ hg).trans (map_one _).symm)
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq x)
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]

end CFSG.Monster.B.OddDegree
