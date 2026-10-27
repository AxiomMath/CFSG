module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableB

section Diag

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem largeEvenDiagMap_single_inl (a : Fin r → Kˣ) (i : Fin r) (c : K) :
    LargeEvenDiagMap A K a (Finsupp.single (Sum.inl i) c) = Finsupp.single (Sum.inl i) c := by
  simp [LargeEvenDiagMap, LargeEvenHVec]

theorem largeEvenDiagMap_single_inr (a : Fin r → Kˣ) (α : {v : Fin r → ℤ // LargeEvenIsRoot A v})
    (c : K) : LargeEvenDiagMap A K a (Finsupp.single (Sum.inr α) c) =
      ((∏ i, a i ^ α.1 i : Kˣ) : K) • Finsupp.single (Sum.inr α) c := by
  simp [LargeEvenDiagMap, mul_comm]

theorem largeEvenDiagMap_mul (a b : Fin r → Kˣ) :
    LargeEvenDiagMap A K (a * b) = LargeEvenDiagMap A K a * LargeEvenDiagMap A K b := by
  apply Finsupp.lhom_ext
  rintro (i | α) c
  · simp [largeEvenDiagMap_single_inl]
  · simp only [Module.End.mul_apply, largeEvenDiagMap_single_inr, map_smul, smul_smul]
    congr 1
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]
    ring

theorem largeEvenDiagMap_one : LargeEvenDiagMap A K 1 = 1 := by
  apply Finsupp.lhom_ext
  rintro (i | α) c
  · simp [largeEvenDiagMap_single_inl]
  · simp [largeEvenDiagMap_single_inr]

@[expose] noncomputable def diagHom : (Fin r → Kˣ) →* LargeEvenChevGL A K where
  toFun a := ⟨LargeEvenDiagMap A K a, LargeEvenDiagMap A K a⁻¹,
    by rw [← largeEvenDiagMap_mul, mul_inv_cancel, largeEvenDiagMap_one],
    by rw [← largeEvenDiagMap_mul, inv_mul_cancel, largeEvenDiagMap_one]⟩
  map_one' := Units.ext (largeEvenDiagMap_one A K)
  map_mul' a b := Units.ext (largeEvenDiagMap_mul A K a b)

theorem coe_diagHom (a : Fin r → Kˣ) :
    (diagHom A K a : Module.End K (LargeEvenChevModule A K)) = LargeEvenDiagMap A K a :=
  rfl

variable {A K}

theorem diag_rel_iff (a : Fin r → Kˣ) (g g' : LargeEvenChevGL A K) :
    (g' : Module.End K (LargeEvenChevModule A K)) * LargeEvenDiagMap A K a =
        LargeEvenDiagMap A K a * (g : Module.End K (LargeEvenChevModule A K)) ↔
      g' = diagHom A K a * g * (diagHom A K a)⁻¹ := by
  rw [← coe_diagHom, ← Units.val_mul, ← Units.val_mul, Units.val_inj]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    rw [h, inv_mul_cancel_right]

@[expose] def IsDiagOf (H : Subgroup (LargeEvenChevGL A K)) (φ : MulAut (LargeEvenCenterQuot H))
    (a : Fin r → Kˣ) : Prop :=
  (∀ h ∈ H, diagHom A K a * h * (diagHom A K a)⁻¹ ∈ H) ∧
    ∀ (h : H) (hh : diagHom A K a * h * (diagHom A K a)⁻¹ ∈ H),
      φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H ⟨_, hh⟩

theorem exists_isDiagOf {H : Subgroup (LargeEvenChevGL A K)} {φ : MulAut (LargeEvenCenterQuot H)}
    (hφ : φ ∈ LargeEvenChevDiagImage A K H) : ∃ a, IsDiagOf H φ a := by
  obtain ⟨a, hN, -, hG⟩ := hφ
  refine ⟨a, fun h hh => ?_, fun h hh => ?_⟩
  · obtain ⟨h', hh'⟩ := hN ⟨h, hh⟩
    have h1 : (h' : LargeEvenChevGL A K) = diagHom A K a * h * (diagHom A K a)⁻¹ :=
      (diag_rel_iff a _ _).mp hh'
    rw [← h1]
    exact h'.2
  · exact hG h ⟨diagHom A K a * h * (diagHom A K a)⁻¹, hh⟩ ((diag_rel_iff a _ _).mpr rfl)

end Diag

section Main

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
  {H : Subgroup (LargeEvenChevGL A K)}

theorem isDiagOf_eq_conj {φ : MulAut (LargeEvenCenterQuot H)} {a : Fin r → Kˣ}
    (hφ : IsDiagOf H φ a) (ha : diagHom A K a ∈ H) :
    φ = MulAut.conj (LargeEvenCenterMk H ⟨diagHom A K a, ha⟩) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    show φ (LargeEvenCenterMk H h) =
      MulAut.conj (LargeEvenCenterMk H ⟨diagHom A K a, ha⟩) (LargeEvenCenterMk H h)
    rw [hφ.2 h (hφ.1 h h.2), MulAut.conj_apply]
    rw [show (⟨diagHom A K a * h * (diagHom A K a)⁻¹, hφ.1 h h.2⟩ : H) =
      ⟨diagHom A K a, ha⟩ * h * ⟨diagHom A K a, ha⟩⁻¹ from rfl, map_mul, map_mul, map_inv]

theorem isDiagOf_pow {φ : MulAut (LargeEvenCenterQuot H)} {a : Fin r → Kˣ}
    (hφ : IsDiagOf H φ a) (k : ℕ) : IsDiagOf H (φ ^ k) (a ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun h hh => by simpa using hh, fun h hh => ?_⟩
    rw [pow_zero, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp
  | succ k ih =>
    have hmul : ∀ h : LargeEvenChevGL A K, diagHom A K (a ^ (k + 1)) * h *
        (diagHom A K (a ^ (k + 1)))⁻¹ = diagHom A K (a ^ k) *
          (diagHom A K a * h * (diagHom A K a)⁻¹) * (diagHom A K (a ^ k))⁻¹ := by
      intro h
      rw [pow_succ, map_mul]
      group
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · rw [hmul h]
      exact ih.1 _ (hφ.1 h hh)
    · rw [pow_succ, MulAut.mul_apply, hφ.2 h (hφ.1 h h.2),
        ih.2 ⟨_, hφ.1 h h.2⟩ (by rw [← hmul h]; exact hh)]
      congr 1
      apply Subtype.ext
      exact (hmul h).symm

theorem isDiagOf_eq_pow_mul_conj {φ φ₀ : MulAut (LargeEvenCenterQuot H)} {a a₀ t : Fin r → Kˣ}
    (hφ : IsDiagOf H φ a) (hφ₀ : IsDiagOf H φ₀ a₀) (k : ℕ) (ht : diagHom A K t ∈ H)
    (hat : a = a₀ ^ k * t) :
    φ = φ₀ ^ k * MulAut.conj (LargeEvenCenterMk H ⟨diagHom A K t, ht⟩) := by
  have hk := isDiagOf_pow hφ₀ k
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    have hmem : diagHom A K t * h * (diagHom A K t)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem ht h.2) (H.inv_mem ht)
    have e : LargeEvenCenterMk H ⟨_, hmem⟩ = LargeEvenCenterMk H ⟨diagHom A K t, ht⟩ *
        LargeEvenCenterMk H h * (LargeEvenCenterMk H ⟨diagHom A K t, ht⟩)⁻¹ := by
      rw [show (⟨_, hmem⟩ : H) = ⟨diagHom A K t, ht⟩ * h * ⟨diagHom A K t, ht⟩⁻¹ from rfl,
        map_mul, map_mul, map_inv]
    show φ (LargeEvenCenterMk H h) =
      (φ₀ ^ k * MulAut.conj (LargeEvenCenterMk H ⟨_, ht⟩)) (LargeEvenCenterMk H h)
    rw [MulAut.mul_apply, MulAut.conj_apply, ← e, hk.2 ⟨_, hmem⟩ (hk.1 _ hmem),
      hφ.2 h (hφ.1 h h.2)]
    congr 1
    apply Subtype.ext
    show diagHom A K a * h * (diagHom A K a)⁻¹ =
      diagHom A K (a₀ ^ k) * (diagHom A K t * h * (diagHom A K t)⁻¹) * (diagHom A K (a₀ ^ k))⁻¹
    rw [hat, map_mul]
    group

theorem ggOutdiagCyclic_chevID (T : Subgroup (Fin r → Kˣ)) (hT : ∀ t ∈ T, diagHom A K t ∈ H)
    (hQ : ∀ a a' : Fin r → Kˣ, (∀ h ∈ H, diagHom A K a * h * (diagHom A K a)⁻¹ ∈ H) →
      (∀ h ∈ H, diagHom A K a' * h * (diagHom A K a')⁻¹ ∈ H) → a' ∉ T →
        ∃ k : ℕ, a * (a' ^ k)⁻¹ ∈ T) :
    GGOutdiagCyclic (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) := by
  classical
  suffices h : ∃ φ₀ : MulAut (LargeEvenCenterQuot H), LargeEvenChevDiagImage A K H ⊆
      ((MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range ⊔
        Subgroup.zpowers φ₀ : Subgroup (MulAut (LargeEvenCenterQuot H))) by
    obtain ⟨φ₀, hφ₀⟩ := h
    refine ⟨φ₀, fun φ hφ => ?_⟩
    have hle : Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage A K H) ≤
        (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range ⊔
          Subgroup.zpowers φ₀ := by
      rw [Subgroup.closure_le]
      refine Set.union_subset ?_ hφ₀
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_sup_left ⟨x, rfl⟩
    exact hle hφ
  by_cases hex : ∃ (φ₀ : MulAut (LargeEvenCenterQuot H)) (a₀ : Fin r → Kˣ),
      IsDiagOf H φ₀ a₀ ∧ a₀ ∉ T
  · obtain ⟨φ₀, a₀, h₀, ha₀⟩ := hex
    refine ⟨φ₀, fun φ hφ => ?_⟩
    obtain ⟨a, ha⟩ := exists_isDiagOf hφ
    by_cases haT : a ∈ T
    · rw [isDiagOf_eq_conj ha (hT a haT)]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · obtain ⟨k, hk⟩ := hQ a a₀ ha.1 h₀.1 ha₀
      rw [isDiagOf_eq_pow_mul_conj ha h₀ k (hT _ hk)
        (by rw [mul_comm (a₀ ^ k), inv_mul_cancel_right])]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
        (Subgroup.mem_sup_left ⟨_, rfl⟩)
  · refine ⟨1, fun φ hφ => ?_⟩
    obtain ⟨a, ha⟩ := exists_isDiagOf hφ
    by_cases haT : a ∈ T
    · rw [isDiagOf_eq_conj ha (hT a haT)]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · exact absurd ⟨φ, a, ha, haT⟩ hex

theorem ggOutdiagCyclic_chevID_of_subsingleton [Subsingleton Kˣ]
    (H : Subgroup (LargeEvenChevGL A K)) :
    GGOutdiagCyclic (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) :=
  ggOutdiagCyclic_chevID ⊤ (fun t _ => by rw [Subsingleton.elim t 1, map_one]; exact H.one_mem)
    (fun _ a' _ _ h => absurd (Subgroup.mem_top a') h)

end Main

end TableB

end CFSG.StandardType
