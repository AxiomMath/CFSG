module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne.StrongP

open Matrix

@[expose] def HasNoncommPair (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ x y : G, x ^ p = 1 ∧ y ^ p = 1 ∧ x * y ≠ y * x ∧
    IsPGroup p (Subgroup.closure ({x, y} : Set G))

theorem HasNoncommPair.map {p : ℕ} {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (h : HasNoncommPair p G) : HasNoncommPair p G' := by
  obtain ⟨x, y, hx, hy, hxy, hQ⟩ := h
  refine ⟨f x, f y, by rw [← map_pow, hx, map_one], by rw [← map_pow, hy, map_one], ?_, ?_⟩
  · intro h
    exact hxy (hf (by rw [map_mul, map_mul, h]))
  · have hmap : Subgroup.closure ({f x, f y} : Set G') =
        (Subgroup.closure ({x, y} : Set G)).map f := by
      rw [MonoidHom.map_closure, Set.image_pair]
    rw [hmap]
    exact hQ.map f

section Heisenberg

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

def Nform (a b c : ι) (α β γ : K) : Matrix ι ι K :=
  1 + single a b α + single b c β + single a c γ

omit [Fintype ι] in
theorem Nform_congr {a b c : ι} {α β γ α' β' γ' : K} (h1 : α = α') (h2 : β = β') (h3 : γ = γ') :
    Nform a b c α β γ = Nform a b c α' β' γ' := by
  subst h1 h2 h3; rfl

theorem Nform_mul {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ α' β' γ' : K) :
    Nform a b c α β γ * Nform a b c α' β' γ' =
      Nform a b c (α + α') (β + β') (γ + γ' + α * β') := by
  simp only [Nform, mul_add, add_mul, one_mul, mul_one]
  simp [Matrix.single_mul_single_of_ne _ _ _ _ hab.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hbc.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hac.symm, Matrix.single_mul_single_same,
    Matrix.single_add]
  abel

omit [Fintype ι] in
theorem Nform_zero (a b c : ι) : Nform a b c (0 : K) 0 0 = 1 := by simp [Nform]

omit [Fintype ι] in
theorem Nform_apply_ac {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ : K) :
    Nform a b c α β γ a c = γ := by
  simp [Nform, Matrix.one_apply_ne hac, hbc, hab.symm]

def uSL {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ : K) :
    Matrix.SpecialLinearGroup ι K :=
  Matrix.SpecialLinearGroup.transvection hab α * Matrix.SpecialLinearGroup.transvection hbc β *
    Matrix.SpecialLinearGroup.transvection hac (γ - α * β)

theorem uSL_coe {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ : K) :
    ((uSL hab hbc hac α β γ : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) =
      Nform a b c α β γ := by
  have h1 : ((Matrix.SpecialLinearGroup.transvection hab α : Matrix.SpecialLinearGroup ι K) :
      Matrix ι ι K) = Nform a b c α 0 0 := by
    simp [Matrix.SpecialLinearGroup.transvection_coe, Nform]
  have h2 : ((Matrix.SpecialLinearGroup.transvection hbc β : Matrix.SpecialLinearGroup ι K) :
      Matrix ι ι K) = Nform a b c 0 β 0 := by
    simp [Matrix.SpecialLinearGroup.transvection_coe, Nform]
  have h3 : ((Matrix.SpecialLinearGroup.transvection hac (γ - α * β) :
      Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) = Nform a b c 0 0 (γ - α * β) := by
    simp [Matrix.SpecialLinearGroup.transvection_coe, Nform]
  unfold uSL
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1, h2, h3,
    Nform_mul hab hbc hac, Nform_mul hab hbc hac]
  exact Nform_congr (by ring) (by ring) (by ring)

theorem uSL_mul {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ α' β' γ' : K) :
    uSL hab hbc hac α β γ * uSL hab hbc hac α' β' γ' =
      uSL hab hbc hac (α + α') (β + β') (γ + γ' + α * β') := by
  have h : ((uSL hab hbc hac α β γ * uSL hab hbc hac α' β' γ' : Matrix.SpecialLinearGroup ι K) :
      Matrix ι ι K) = ((uSL hab hbc hac (α + α') (β + β') (γ + γ' + α * β') :
        Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, uSL_coe, uSL_coe, uSL_coe, Nform_mul hab hbc hac]
  exact Subtype.ext h

theorem uSL_zero {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    uSL hab hbc hac (0 : K) 0 0 = 1 := by
  have h : ((uSL hab hbc hac (0 : K) 0 0 : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) =
      ((1 : Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) := by
    rw [uSL_coe, Nform_zero]; rfl
  exact Subtype.ext h

theorem uSL_inv {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ : K) :
    (uSL hab hbc hac α β γ)⁻¹ = uSL hab hbc hac (-α) (-β) (α * β - γ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [uSL_mul, ← uSL_zero hab hbc hac]
  congr 1 <;> ring

def uSLGroup {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Subgroup (Matrix.SpecialLinearGroup ι K) where
  carrier := {u | ∃ α β γ : K, u = uSL hab hbc hac α β γ}
  mul_mem' := by
    rintro _ _ ⟨α, β, γ, rfl⟩ ⟨α', β', γ', rfl⟩
    exact ⟨α + α', β + β', γ + γ' + α * β', uSL_mul hab hbc hac α β γ α' β' γ'⟩
  one_mem' := ⟨0, 0, 0, (uSL_zero hab hbc hac).symm⟩
  inv_mem' := by
    rintro _ ⟨α, β, γ, rfl⟩
    exact ⟨-α, -β, α * β - γ, uSL_inv hab hbc hac α β γ⟩

theorem uSL_pow {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ : K) (k : ℕ) :
    (uSL hab hbc hac α β γ) ^ k =
      uSL hab hbc hac (k * α) (k * β) (k * γ + (k.choose 2 : K) * (α * β)) := by
  induction k with
  | zero => simpa using (uSL_zero hab hbc hac).symm
  | succ k ih =>
    rw [pow_succ, ih, uSL_mul]
    congr 1
    · push_cast; ring
    · push_cast; ring
    · rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast; ring

theorem uSL_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p) {a b c : ι}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (α β γ : K) :
    (uSL hab hbc hac α β γ) ^ p = 1 := by
  rw [uSL_pow]
  have h1 : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have h2 : ((p.choose 2 : ℕ) : K) = 0 := by
    refine (CharP.cast_eq_zero_iff K p _).mpr ?_
    exact (Fact.out : p.Prime).dvd_choose_self (by norm_num) (by omega)
  rw [h1, h2]
  simp only [zero_mul, add_zero]
  exact uSL_zero hab hbc hac

theorem closure_le_uSLGroup {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Subgroup.closure ({uSL hab hbc hac (1 : K) 0 0, uSL hab hbc hac (0 : K) 1 0} :
        Set (Matrix.SpecialLinearGroup ι K)) ≤ uSLGroup hab hbc hac := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨1, 0, 0, rfl⟩
  · exact ⟨0, 1, 0, rfl⟩

theorem hasNoncommPair_psl (p n : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p) (hn : 3 ≤ n) :
    HasNoncommPair p (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hbc : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hac : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨QuotientGroup.mk (uSL hab hbc hac (1 : K) 0 0),
    QuotientGroup.mk (uSL hab hbc hac (0 : K) 1 0), ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, uSL_pow_char p hp3, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, uSL_pow_char p hp3, QuotientGroup.mk_one]
  · intro h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, uSL_mul, uSL_mul,
      uSL_inv, uSL_mul] at h
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have h2 := congrFun (congrFun hr ⟨0, by omega⟩) ⟨2, by omega⟩
    rw [uSL_coe, Nform_apply_ac hab hbc hac] at h2
    simp [Matrix.scalar_apply] at h2
  · have hmap : (Subgroup.closure ({uSL hab hbc hac (1 : K) 0 0, uSL hab hbc hac (0 : K) 1 0} :
        Set (Matrix.SpecialLinearGroup (Fin n) K))).map
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))) =
        Subgroup.closure ({QuotientGroup.mk (uSL hab hbc hac (1 : K) 0 0),
          QuotientGroup.mk (uSL hab hbc hac (0 : K) 1 0)} :
          Set (ProjectiveSpecialLinearGroup (Fin n) K)) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rintro ⟨w, hw⟩
    rw [← hmap] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨α, β, γ, rfl⟩ := closure_le_uSLGroup hab hbc hac hu
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    simp [uSL_pow_char p hp3]

end Heisenberg

end CFSG.RankThree.PartOne.StrongP
