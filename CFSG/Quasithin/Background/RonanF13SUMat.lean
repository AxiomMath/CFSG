module

public import CFSG.Quasithin.Background.RonanF13SUEigen
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.Quasithin.RonanF13

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Matrix

section Semi

variable {F : Type} [Field F]

@[expose] def semiMap (A : GL (Fin 3) F) (φ : F ≃+* F) (v : Fin 3 → F) : Fin 3 → F :=
  (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (fun i => φ (v i))

theorem semiMap_add (A : GL (Fin 3) F) (φ : F ≃+* F) (v w : Fin 3 → F) :
    semiMap A φ (v + w) = semiMap A φ v + semiMap A φ w := by
  unfold semiMap
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem semiMap_smul (A : GL (Fin 3) F) (φ : F ≃+* F) (c : F) (v : Fin 3 → F) :
    semiMap A φ (c • v) = φ c • semiMap A φ v := by
  unfold semiMap
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem semiMap_bijective (A : GL (Fin 3) F) (φ : F ≃+* F) : Function.Bijective (semiMap A φ) := by
  have h1 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro v w h
    unfold semiMap at h
    have h3 := congrArg
      (fun u => ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h3
    funext i
    exact φ.injective (congrFun h3 i)
  · intro u
    refine ⟨fun i => φ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) i), ?_⟩
    unfold semiMap
    have : (fun i => φ (φ.symm ((((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u) i))) =
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
      funext i
      simp
    rw [this, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

theorem semiMap_mulVec (A : GL (Fin 3) F) (φ : F ≃+* F) (x : GL (Fin 3) F) (v : Fin 3 → F) :
    semiMap A φ (((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((A * glAut φ x * A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ semiMap A φ v := by
  unfold semiMap
  have h1 : (fun i => φ ((((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
      ((x : Matrix (Fin 3) (Fin 3) F).map φ) *ᵥ (fun i => φ (v i)) := by
    funext i
    exact RingHom.map_mulVec (φ : F →+* F) _ _ i
  have hinv : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [Units.val_mul, Units.val_mul, coe_glAut]
  simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]

end Semi

section Group

variable {F : Type} [Field F] [Finite F] [CharP F 2] {S : Subgroup (GL (Fin 3) F)}

@[expose] noncomputable def Mv (S : Subgroup (GL (Fin 3) F)) :
    ↥S →* Module.End F (Fin 3 → F) where
  toFun x := Matrix.mulVecLin ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp [Matrix.mulVec_mulVec]

theorem Mv_apply (x : ↥S) (v : Fin 3 → F) :
    Mv S x v = ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
  simp [Mv]

theorem semiMap_iter_mulVec (α : MulAut ↥S) (A : GL (Fin 3) F) (φ : F ≃+* F)
    (hα : ∀ x : ↥S, ((α x : ↥S) : GL (Fin 3) F) = A * glAut φ (x : GL (Fin 3) F) * A⁻¹)
    (x : ↥S) (v : Fin 3 → F) (j : ℕ) :
    (semiMap A φ)^[j] (Mv S x v) = Mv S ((α ^ j) x) ((semiMap A φ)^[j] v) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Mv_apply,
      semiMap_mulVec, pow_succ', MulAut.mul_apply, Mv_apply, hα]

theorem semiMap_iter_smul (A : GL (Fin 3) F) (φ : F ≃+* F) (c : F) (v : Fin 3 → F) (j : ℕ) :
    (semiMap A φ)^[j] (c • v) = (φ^[j] c) • (semiMap A φ)^[j] v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, semiMap_smul]

@[expose] noncomputable def fixedSpace (T : Subgroup ↥S) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ t ∈ T, Mv S t v = v}
  add_mem' := by
    intro v w hv hw t ht
    rw [map_add, hv t ht, hw t ht]
  zero_mem' := by
    intro t ht
    simp
  smul_mem' := by
    intro c v hv t ht
    rw [map_smul, hv t ht]

theorem mem_fixedSpace {T : Subgroup ↥S} {v : Fin 3 → F} :
    v ∈ fixedSpace T ↔ ∀ t ∈ T, Mv S t v = v := Iff.rfl

theorem fixedSpace_ne_bot (T : Subgroup ↥S) (hT : IsPGroup 2 T) : fixedSpace T ≠ ⊥ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : MulAction ↥T (Fin 3 → F) :=
    { smul := fun t v => Mv S (t : ↥S) v
      one_smul := fun v => by
        show Mv S (1 : ↥S) v = v
        rw [map_one]
        rfl
      mul_smul := fun s t v => by
        show Mv S ((s : ↥S) * (t : ↥S)) v = Mv S (s : ↥S) (Mv S (t : ↥S) v)
        rw [map_mul]
        rfl }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : 2 ∣ Nat.card (Fin 3 → F) := by
    obtain ⟨m, -, hm⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, hm]
    simp only [Fintype.card_fin]
    exact Dvd.dvd.pow (dvd_pow_self 2 (PNat.ne_zero m)) (by norm_num)
  have h0 : (0 : Fin 3 → F) ∈ MulAction.fixedPoints ↥T (Fin 3 → F) := by
    intro t
    show Mv S (t : ↥S) 0 = 0
    simp
  obtain ⟨b, hb, hb0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 3 → F) hcard h0
  intro hbot
  have hbmem : b ∈ fixedSpace T := fun t ht => hb ⟨t, ht⟩
  rw [hbot, Submodule.mem_bot] at hbmem
  exact hb0 hbmem.symm

theorem Mv_injective : Function.Injective (Mv S) := by
  intro x y h
  have h1 : (Matrix.toLin' ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.toLin' ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
    exact h
  exact Subtype.ext (Units.ext (Matrix.toLin'.injective h1))

theorem semiMap_Mv (α : MulAut ↥S) (A : GL (Fin 3) F) (φ : F ≃+* F)
    (hα : ∀ x : ↥S, ((α x : ↥S) : GL (Fin 3) F) = A * glAut φ (x : GL (Fin 3) F) * A⁻¹)
    (x : ↥S) (v : Fin 3 → F) : semiMap A φ (Mv S x v) = Mv S (α x) (semiMap A φ v) := by
  rw [Mv_apply, semiMap_mulVec, Mv_apply, hα]

theorem frob_of_semilinear (α : MulAut ↥S) (A : GL (Fin 3) F) (φ : F ≃+* F) (ν : ℕ)
    (hν : ∀ c, φ c = c ^ ν)
    (hα : ∀ x : ↥S, ((α x : ↥S) : GL (Fin 3) F) = A * glAut φ (x : GL (Fin 3) F) * A⁻¹)
    (r : ℕ) (hr : Odd r) (hαr : α ^ r = 1) (hφr : φ ^ r = 1)
    (T D : Subgroup ↥S) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set ↥S)) (hαT : ∀ x, α x ∈ T ↔ x ∈ T)
    (hαD : ∀ x, α x ∈ D ↔ x ∈ D)
    (d₀ : ↥S) (hd₀ : d₀ ∈ D) (hd₀pow : d₀ ^ (Nat.card F - 1) = 1)
    (hDgen : ∀ x ∈ D, ∃ (a : ℕ) (z : ↥S) (c : F),
      (∀ v : Fin 3 → F, Mv S z v = c • v) ∧ x = d₀ ^ a * z) :
    α d₀ = d₀ ^ ν := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hg : Mv S d₀ ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, hcard, hd₀pow, map_one]
  have hψg' : ∀ w, semiMap A φ (Mv S (α⁻¹ d₀) w) = Mv S d₀ (semiMap A φ w) := by
    intro w
    rw [semiMap_Mv α A φ hα, MulAut.apply_inv_self]
  have hg'sc : ∀ μ : F, ∃ c : F, ∀ w ∈ Module.End.eigenspace (Mv S d₀) μ,
      Mv S (α⁻¹ d₀) w = c • w := by
    intro μ
    have hmemD : α⁻¹ d₀ ∈ D := by
      rw [← hαD, MulAut.apply_inv_self]
      exact hd₀
    obtain ⟨a, z, c₀, hz, hx⟩ := hDgen _ hmemD
    refine ⟨c₀ * μ ^ a, fun w hw => ?_⟩
    have hw' : Mv S d₀ w = μ • w := Module.End.mem_eigenspace_iff.mp hw
    have hpow : ∀ j : ℕ, (Mv S d₀ ^ j) w = μ ^ j • w := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hw', smul_smul, pow_succ]
    rw [hx, map_mul, Module.End.mul_apply, hz, map_smul, map_pow, hpow, smul_smul]
  have hkey := eigen_frobenius (K := F) (W := Fin 3 → F) (by simp) (Mv S d₀) (Mv S (α⁻¹ d₀))
    (Mv S (α d₀)) φ ν hν (semiMap A φ) (semiMap_add A φ) (semiMap_smul A φ)
    (semiMap_bijective A φ) hg (semiMap_Mv α A φ hα d₀) hψg' hg'sc r hr ?_ ?_ (fixedSpace T)
    (fixedSpace_ne_bot T hT) ?_ ?_ ?_
  · rw [← map_pow] at hkey
    exact Mv_injective hkey
  · intro w
    rw [semiMap_iter_mulVec α A φ hα, hαr]
    simp
  · intro c w
    rw [semiMap_iter_smul]
    have h1 : (φ ^ r) c = c := by rw [hφr]; rfl
    rw [RingAut.coe_pow] at h1
    rw [h1]
  · intro hTop
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have h1 : ∀ v, Mv S t v = v := fun v =>
      mem_fixedSpace.mp (hTop ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule F (Fin 3 → F)))) t ht
    have h2 : Mv S t = Mv S 1 := by
      refine LinearMap.ext fun v => ?_
      rw [h1 v, map_one]
      rfl
    exact ht1' (Mv_injective h2)
  · intro w hw t ht
    have hinv : d₀⁻¹ ∈ Subgroup.normalizer (T : Set ↥S) := Subgroup.inv_mem _ (hDT hd₀)
    have hd : d₀⁻¹ * t * d₀ ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp hinv t).mp ht
      simpa using this
    calc Mv S t (Mv S d₀ w) = Mv S (t * d₀) w := by rw [map_mul]; rfl
      _ = Mv S (d₀ * (d₀⁻¹ * t * d₀)) w := by congr 2; group
      _ = Mv S d₀ (Mv S (d₀⁻¹ * t * d₀) w) := by rw [map_mul]; rfl
      _ = Mv S d₀ w := by rw [mem_fixedSpace.mp hw _ hd]
  · intro w hw t ht
    have h1 : α⁻¹ t ∈ T := by
      rw [← hαT, MulAut.apply_inv_self]
      exact ht
    rw [← MulAut.apply_inv_self _ α t, ← semiMap_Mv α A φ hα, mem_fixedSpace.mp hw _ h1]

end Group

end CFSG.Quasithin.RonanF13
