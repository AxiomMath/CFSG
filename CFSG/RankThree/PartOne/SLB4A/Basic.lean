module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

abbrev C2 : Type := Multiplicative (ZMod 2)

abbrev V2 (n : ℕ) : Type := Fin n → C2

abbrev c2gen : C2 := Multiplicative.ofAdd 1

theorem c2_mul_self (x : C2) : x * x = 1 := by
  revert x
  decide

theorem c2_sq (x : C2) : x ^ 2 = 1 := by
  rw [sq]
  exact c2_mul_self x

theorem v2_sq {n : ℕ} (v : V2 n) : v ^ 2 = 1 := by
  funext i
  simpa using c2_sq (v i)

theorem c2_eq_one_or_gen (x : C2) : x = 1 ∨ x = c2gen := by
  revert x
  decide

theorem card_v2 (n : ℕ) : Nat.card (V2 n) = 2 ^ n := by
  rw [Nat.card_pi]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem exists_two_pow_five_of_injective {G : Type*} [Group G] (ρ : V2 5 →* G)
    (hρ : Function.Injective ρ) :
    ∃ U : Subgroup G, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine ⟨ρ.range, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      refine Subtype.ext ?_
      show ρ x * ρ y = ρ y * ρ x
      rw [← map_mul, ← map_mul, mul_comm]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => ?_
      obtain ⟨_, x, rfl⟩ := a
      refine Subtype.ext ?_
      change ρ x ^ 2 = 1
      rw [← map_pow, v2_sq, map_one]
  · rw [← card_v2 5]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm

theorem exists_two_pow_five_quot {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (s : V2 5 → G)
    (hmul : ∀ v w, (s v * s w)⁻¹ * s (v * w) ∈ N) (hind : ∀ v, s v ∈ N → v = 1) :
    ∃ U : Subgroup (G ⧸ N), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  let ρ : V2 5 →* G ⧸ N :=
    { toFun := fun v => QuotientGroup.mk (s v)
      map_one' := by
        have h := hmul 1 1
        rw [mul_one, show (s 1 * s 1)⁻¹ * s 1 = (s 1)⁻¹ by group] at h
        exact (QuotientGroup.eq_one_iff _).2 (N.inv_mem_iff.1 h)
      map_mul' := fun v w => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq,
          show (s (v * w))⁻¹ * (s v * s w) = ((s v * s w)⁻¹ * s (v * w))⁻¹ by group]
        exact N.inv_mem (hmul v w) }
  refine exists_two_pow_five_of_injective ρ ((injective_iff_map_eq_one ρ).2 fun v hv => ?_)
  exact hind v (QuotientGroup.eq_one_iff _ |>.1 hv)

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem mem_statedScalars_iff {A : GL ι K} :
    A ∈ StatedScalars ι K ↔ ∃ c : Kˣ, (A : Matrix ι ι K) = Matrix.scalar ι (c : K) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, Matrix.GeneralLinearGroup.coe_scalar (n := ι) c⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar (n := ι), hc])⟩

theorem inv_mul_mem_scalars (X Y : GL ι K) (c : K) (hc : c ≠ 0)
    (h : (Y : Matrix ι ι K) = c • (X : Matrix ι ι K)) : X⁻¹ * Y ∈ StatedScalars ι K := by
  rw [mem_statedScalars_iff]
  refine ⟨Units.mk0 c hc, ?_⟩
  rw [Units.val_mul, h, Matrix.mul_smul, Units.inv_mul]
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem mem_scalars_of_eq_smul_one (Y : GL ι K) (c : K) (hc : c ≠ 0)
    (h : (Y : Matrix ι ι K) = c • (1 : Matrix ι ι K)) : Y ∈ StatedScalars ι K := by
  rw [mem_statedScalars_iff]
  refine ⟨Units.mk0 c hc, ?_⟩
  rw [h]
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem exists_two_pow_five_statedProj (H : Subgroup (GL ι K)) (S : V2 5 → GL ι K)
    (hS : ∀ v, S v ∈ H)
    (hmul : ∀ v w, (S v * S w)⁻¹ * S (v * w) ∈ StatedScalars ι K)
    (hind : ∀ v, S v ∈ StatedScalars ι K → v = 1) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_quot ((StatedScalars ι K).subgroupOf H) (fun v => ⟨S v, hS v⟩) ?_ ?_
  · intro v w
    rw [Subgroup.mem_subgroupOf]
    exact hmul v w
  · intro v hv
    exact hind v (Subgroup.mem_subgroupOf.1 hv)

end Matrices

theorem exists_mem_of_mulSingle {n : ℕ} {G : Type*} [Group G] (ρ : V2 n →* G) (H : Subgroup G)
    (h : ∀ k : Fin n, ρ (Pi.mulSingle k c2gen) ∈ H) (v : V2 n) : ρ v ∈ H := by
  have hv : v = ∏ k, Pi.mulSingle k (v k) := (Finset.univ_prod_mulSingle v).symm
  have key : ∀ (S : Finset (Fin n)), ρ (∏ k ∈ S, Pi.mulSingle k (v k)) ∈ H := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, map_mul]
      refine mul_mem ?_ ih
      rcases c2_eq_one_or_gen (v k) with h1 | h1
      · rw [h1]
        simp
      · rw [h1]
        exact h k
  rw [hv]
  exact key _


theorem exists_of_mulEquiv {T G : Type*} [Group T] [Group G] (e : T ≃* G)
    (h : ∃ U : Subgroup G, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨U, hU, hc⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU
  refine ⟨U.map e.symm.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hc]

theorem neg_one_ne_one_of_card_odd (K : Type) [Field K] [Finite K] (h : Nat.card K % 2 = 1) :
    (-1 : K) ≠ 1 := by
  have := Fintype.ofFinite K
  refine Ring.neg_one_ne_one_of_char_ne_two fun h2 => ?_
  have := FiniteField.even_card_iff_char_two.1 h2
  rw [← Nat.card_eq_fintype_card] at this
  omega

theorem two_ne_zero_of_card_odd (K : Type) [Field K] [Finite K] (h : Nat.card K % 2 = 1) :
    (2 : K) ≠ 0 := fun h2 => neg_one_ne_one_of_card_odd K h (by linear_combination -h2)

theorem exists_sq_neg_one (K : Type) [Field K] [Finite K] (h : Nat.card K % 4 = 1) :
    ∃ u : Kˣ, (u : K) * u = -1 := by
  have := Fintype.ofFinite K
  have h4 : Fintype.card K % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff).2 h4
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, by simpa using hr.symm⟩

@[expose] def ex (x : C2) : ℕ := (Multiplicative.toAdd x).val

theorem ex_one : ex 1 = 0 := by simp [ex]

theorem ex_gen : ex c2gen = 1 := by
  simp only [ex, c2gen, toAdd_ofAdd]
  exact rfl

theorem pow_ex_mul {G : Type*} [Group G] {a : G} (ha : a * a = 1) (x y : C2) :
    a ^ ex (x * y) = a ^ ex x * a ^ ex y := by
  rcases c2_eq_one_or_gen x with rfl | rfl <;> rcases c2_eq_one_or_gen y with rfl | rfl <;>
    simp [ex_one, ex_gen, c2_mul_self, ha]

theorem ex_cases (x : C2) : ex x = 0 ∨ ex x = 1 := by
  rcases c2_eq_one_or_gen x with rfl | rfl
  · exact Or.inl ex_one
  · exact Or.inr ex_gen

theorem eq_one_of_ex_eq_zero {x : C2} (h : ex x = 0) : x = 1 := by
  rcases c2_eq_one_or_gen x with rfl | rfl
  · rfl
  · rw [ex_gen] at h
    omega

theorem exists_two_pow_five_of_commInvol {G : Type*} [Group G] (g : Fin 5 → G)
    (hc : ∀ i j, g i * g j = g j * g i) (hs : ∀ i, g i * g i = 1)
    (hind : ∀ v : V2 5, g 0 ^ ex (v 0) * g 1 ^ ex (v 1) * g 2 ^ ex (v 2) * g 3 ^ ex (v 3) *
      g 4 ^ ex (v 4) = 1 → v = 1) :
    ∃ U : Subgroup G, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  let A : Subgroup G := Subgroup.closure (Set.range g)
  have hcomm : (Set.range g).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  have hA : IsMulCommutative A := Subgroup.isMulCommutative_closure hcomm
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => hA.is_comm.comm x y }
  let a : Fin 5 → A := fun k => ⟨g k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  have ha : ∀ k, a k * a k = 1 := fun k => Subtype.ext (hs k)
  let ρA : V2 5 →* A :=
    { toFun := fun v => ∏ k, a k ^ ex (v k)
      map_one' := by simp [ex_one]
      map_mul' := fun v w => by
        simp only [Pi.mul_apply, pow_ex_mul (ha _), Finset.prod_mul_distrib] }
  let ρ : V2 5 →* G := A.subtype.comp ρA
  refine exists_two_pow_five_of_injective ρ ((injective_iff_map_eq_one ρ).2 fun v hv => hind v ?_)
  have h : ρ v = g 0 ^ ex (v 0) * g 1 ^ ex (v 1) * g 2 ^ ex (v 2) * g 3 ^ ex (v 3) *
      g 4 ^ ex (v 4) := by
    show ((∏ k, a k ^ ex (v k) : A) : G) = _
    simp [Fin.prod_univ_five, a, mul_assoc]
  rw [← h]
  exact hv

section Matrices2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_two_pow_five_statedProj_inv (H : Subgroup (GL ι K)) (h : Fin 5 → GL ι K)
    (hH : ∀ k, h k ∈ H) (hc : ∀ i j, (h i * h j)⁻¹ * (h j * h i) ∈ StatedScalars ι K)
    (hs : ∀ k, h k * h k ∈ StatedScalars ι K)
    (hind : ∀ v : V2 5, h 0 ^ ex (v 0) * h 1 ^ ex (v 1) * h 2 ^ ex (v 2) * h 3 ^ ex (v 3) *
      h 4 ^ ex (v 4) ∈ StatedScalars ι K → v = 1) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  let g : Fin 5 → StatedProj H := fun k => QuotientGroup.mk ⟨h k, hH k⟩
  refine exists_two_pow_five_of_commInvol g ?_ ?_ ?_
  · intro i j
    show (QuotientGroup.mk ⟨h i, hH i⟩ : StatedProj H) * QuotientGroup.mk ⟨h j, hH j⟩ =
      QuotientGroup.mk ⟨h j, hH j⟩ * QuotientGroup.mk ⟨h i, hH i⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hc i j
  · intro k
    show (QuotientGroup.mk ⟨h k, hH k⟩ : StatedProj H) * QuotientGroup.mk ⟨h k, hH k⟩ = 1
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hs k
  · intro v hv
    refine hind v ?_
    have e : g 0 ^ ex (v 0) * g 1 ^ ex (v 1) * g 2 ^ ex (v 2) * g 3 ^ ex (v 3) * g 4 ^ ex (v 4) =
        QuotientGroup.mk (⟨h 0, hH 0⟩ ^ ex (v 0) * ⟨h 1, hH 1⟩ ^ ex (v 1) * ⟨h 2, hH 2⟩ ^ ex (v 2) *
          ⟨h 3, hH 3⟩ ^ ex (v 3) * ⟨h 4, hH 4⟩ ^ ex (v 4)) := by
      simp only [g, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    rw [e, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv
    simpa using hv

end Matrices2

end CFSG.RankThree.PartOne.SLB4A
