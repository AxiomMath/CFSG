module

public import CFSG.Quasithin.Vol2.Ch11SecJEnd1
public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open scoped MatrixGroups Matrix
open CFSG.Assembly.LowTwoRank (StatedSL)

variable {F : Type} [Field F]

theorem exists_scalar_of_commute {K : Type*} [Group K] {α : K →* SL(2, F)}
    (hα : Function.Surjective α) (f : (Fin 2 → F) → (Fin 2 → F))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (heq : ∀ k x, f (((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) =
      ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ f x) :
    ∃ a : F, ∀ x, f x = a • x := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  let f' : (Fin 2 → F) →+ (Fin 2 → F) := ⟨⟨f, h0⟩, hadd⟩
  refine CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := F) le_rfl f' fun γ hγ v => ?_
  rw [CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL] at hγ
  obtain ⟨A, rfl⟩ := hγ
  obtain ⟨k, rfl⟩ := hα A
  exact heq k v

namespace NatPair

variable {G : Type} [Group G] {U V V₁ W K : Subgroup G}
  {α : ↥K →* SL(2, F)} {βV : ↥V →* Multiplicative (Fin 2 → F)}
  {βU : ↥U →* Multiplicative (Fin 2 → F)} (P : NatPair U V V₁ W K α βV βU)
  {c : G} (hcU : c ∈ Subgroup.normalizer (U : Set G))

@[expose] def cU (u : ↥U) : ↥U := ⟨c * u * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcU u).mp u.2⟩

@[expose] noncomputable def T (p : (Fin 2 → F) × (Fin 2 → F)) : (Fin 2 → F) × (Fin 2 → F) :=
  P.X (cU hcU (Function.surjInv P.X_surjective p))

include P

theorem X_eq_iff (a b : ↥U) : P.X a = P.X b ↔ (a : G)⁻¹ * b ∈ V₁ := by
  have h := P.X_mul a (a⁻¹ * b)
  rw [mul_inv_cancel_left] at h
  have e0 := P.X_eq_zero_iff (a⁻¹ * b)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e0
  rw [← e0, h]
  constructor
  · intro e
    simpa using e
  · intro e
    rw [e, add_zero]

variable {hcU} in
theorem T_X (hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G)) (u : ↥U) :
    P.T hcU (P.X u) = P.X (cU hcU u) := by
  set u' := Function.surjInv P.X_surjective (P.X u) with hu'
  have h1 : P.X u' = P.X u := Function.surjInv_eq P.X_surjective _
  rw [P.X_eq_iff] at h1
  show P.X (cU hcU u') = P.X (cU hcU u)
  rw [P.X_eq_iff]
  have := (Subgroup.mem_normalizer_iff.mp hcV₁ _).mp h1
  simpa [cU, mul_assoc] using this

theorem conj_K_mem_U (k : ↥K) (u : ↥U) : (k : G) * u * (k : G)⁻¹ ∈ U := by
  obtain ⟨v, hv, w, hw, hvw⟩ := P.exists_dec u.2
  have hkv := (Subgroup.mem_normalizer_iff.mp (P.hKV k.2) v).mp hv
  have hkw := (Subgroup.mem_normalizer_iff.mp (P.hKW k.2) w).mp hw
  have h := U.mul_mem (P.hVU hkv) (P.hWU hkw)
  rw [← hvw]
  convert h using 1
  group

variable {hcU} in
theorem T_add (hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G)) (p q : (Fin 2 → F) × (Fin 2 → F)) :
    P.T hcU (p + q) = P.T hcU p + P.T hcU q := by
  obtain ⟨a, rfl⟩ := P.X_surjective p
  obtain ⟨b, rfl⟩ := P.X_surjective q
  rw [← P.X_mul, P.T_X hcV₁, P.T_X hcV₁, P.T_X hcV₁, ← P.X_mul]
  congr 1
  apply Subtype.ext
  show c * ((a : G) * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹)
  group

variable {hcU} in
theorem T_K (hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G))
    (hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ U) (k : ↥K) (x y : Fin 2 → F) :
    P.T hcU (((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x,
        ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) =
      (((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ (P.T hcU (x, y)).1,
        ((α k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ (P.T hcU (x, y)).2) := by
  obtain ⟨u, hu⟩ := P.X_surjective (x, y)
  have hx : (P.X u).1 = x := by rw [hu]
  have hy : (P.X u).2 = y := by rw [hu]
  have hku := P.X_conj_K k u ⟨_, P.conj_K_mem_U k u⟩ rfl
  rw [hx, hy] at hku
  rw [← hku, ← hu, P.T_X hcV₁, P.T_X hcV₁]
  have h1 := P.X_conj_K k (cU hcU u) ⟨_, P.conj_K_mem_U k (cU hcU u)⟩ rfl
  rw [← h1]
  refine P.X_conj_U (hcK k k.2) _ _ ?_
  show c * ((k : G) * u * (k : G)⁻¹) * c⁻¹ = c * k * c⁻¹ * (k : G)⁻¹ *
    ((k : G) * (c * u * c⁻¹) * (k : G)⁻¹) * (c * k * c⁻¹ * (k : G)⁻¹)⁻¹
  group

@[expose] noncomputable def mat : Matrix (Fin 2) (Fin 2) F :=
  !![(P.T hcU (Pi.single 0 1, 0)).1 0, (P.T hcU (0, Pi.single 0 1)).1 0;
    (P.T hcU (Pi.single 0 1, 0)).2 0, (P.T hcU (0, Pi.single 0 1)).2 0]

omit P in
theorem eq_smul_single {f : (Fin 2 → F) → (Fin 2 → F)} (hf : ∃ a : F, ∀ x, f x = a • x)
    (x : Fin 2 → F) : f x = f (Pi.single 0 1) 0 • x := by
  obtain ⟨a, ha⟩ := hf
  rw [ha, ha (Pi.single 0 1)]
  simp

variable {hcU} in
theorem T_eq (hα : Function.Surjective α) (hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G))
    (hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ U) (x y : Fin 2 → F) :
    P.T hcU (x, y) = (P.mat hcU 0 0 • x + P.mat hcU 0 1 • y,
      P.mat hcU 1 0 • x + P.mat hcU 1 1 • y) := by
  have hT0 : ∀ p q : Fin 2 → F, P.T hcU (p, q) = P.T hcU (p, 0) + P.T hcU (0, q) := fun p q => by
    rw [← P.T_add hcV₁, Prod.mk_add_mk, add_zero, zero_add]
  have hadd1 : ∀ p p' : Fin 2 → F, P.T hcU (p + p', 0) = P.T hcU (p, 0) + P.T hcU (p', 0) :=
    fun p p' => by rw [← P.T_add hcV₁, Prod.mk_add_mk, add_zero]
  have hadd2 : ∀ q q' : Fin 2 → F, P.T hcU (0, q + q') = P.T hcU (0, q) + P.T hcU (0, q') :=
    fun q q' => by rw [← P.T_add hcV₁, Prod.mk_add_mk, add_zero]
  have hK1 : ∀ (k : ↥K) (p : Fin 2 → F), P.T hcU (((α k : SL(2, F)) : Matrix _ _ F) *ᵥ p, 0) =
      (((α k : SL(2, F)) : Matrix _ _ F) *ᵥ (P.T hcU (p, 0)).1,
        ((α k : SL(2, F)) : Matrix _ _ F) *ᵥ (P.T hcU (p, 0)).2) := fun k p => by
    rw [← P.T_K hcV₁ hcK k p 0, Matrix.mulVec_zero]
  have hK2 : ∀ (k : ↥K) (q : Fin 2 → F), P.T hcU (0, ((α k : SL(2, F)) : Matrix _ _ F) *ᵥ q) =
      (((α k : SL(2, F)) : Matrix _ _ F) *ᵥ (P.T hcU (0, q)).1,
        ((α k : SL(2, F)) : Matrix _ _ F) *ᵥ (P.T hcU (0, q)).2) := fun k q => by
    rw [← P.T_K hcV₁ hcK k 0 q, Matrix.mulVec_zero]
  have s00 := eq_smul_single (exists_scalar_of_commute hα (fun p => (P.T hcU (p, 0)).1)
    (fun p p' => by simp only [hadd1, Prod.fst_add]) (fun k p => by rw [hK1])) x
  have s10 := eq_smul_single (exists_scalar_of_commute hα (fun p => (P.T hcU (p, 0)).2)
    (fun p p' => by simp only [hadd1, Prod.snd_add]) (fun k p => by rw [hK1])) x
  have s01 := eq_smul_single (exists_scalar_of_commute hα (fun q => (P.T hcU (0, q)).1)
    (fun q q' => by simp only [hadd2, Prod.fst_add]) (fun k q => by rw [hK2])) y
  have s11 := eq_smul_single (exists_scalar_of_commute hα (fun q => (P.T hcU (0, q)).2)
    (fun q q' => by simp only [hadd2, Prod.snd_add]) (fun k q => by rw [hK2])) y
  rw [hT0]
  exact Prod.ext (by rw [Prod.fst_add, s00, s01]; rfl) (by rw [Prod.snd_add, s10, s11]; rfl)

end NatPair

end CFSG.Quasithin.Vol2.Ch11.SecJ
