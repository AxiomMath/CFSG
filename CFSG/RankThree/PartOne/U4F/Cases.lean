module

public import CFSG.RankThree.PartOne.U4F.Torus

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU

theorem le_inSubgroup_perfectResidual_of_perfect {H : Type*} [Group H] [Finite H]
    {P X : Subgroup H} (hPX : P ≤ X) (hP : Group.IsPerfect ↥P) :
    P ≤ inSubgroup perfectResidual X := by
  have hperf : Group.IsPerfect (P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have h := (perfect_residual_transport (MonoidHom.id X)).2.2 (P.subgroupOf X) hperf
  exact fun x hx => ⟨⟨x, hPX hx⟩, h hx, rfl⟩

theorem isPerfect_map_conj {H : Type*} [Group H] {X : Subgroup H} (hX : Group.IsPerfect ↥X)
    (g : H) : Group.IsPerfect ↥(X.map (MulAut.conj g).toMonoidHom) := by
  have := hX
  exact Group.IsPerfect.map _

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem sq_ne_one_of_pow_eq_one {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {u : Kˣ} (hu : u ^ r = 1)
    (hu1 : u ≠ 1) : u ^ 2 ≠ 1 := by
  intro h2
  have hcop : Nat.Coprime r 2 := (Nat.coprime_primes hr Nat.prime_two).2 hr2
  have := pow_gcd_eq_one.2 ⟨hu, h2⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  exact hu1 this

theorem perfect_commute_diag (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) (hK4 : 4 ≤ Nat.card K)
    (hF4 : 4 ≤ Nat.card (fixF σ)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hfix : ∀ u : Kˣ, u ^ r = 1 → σ (u : K) = u) {a b : Kˣ} (ha : a ^ r = 1) (hb : b ^ r = 1)
    (hab : ¬ (a = 1 ∧ b = 1)) {X : Subgroup ↥(SU σ 4)} (hX : Group.IsPerfect ↥X) (hXn : X ≠ ⊥)
    {γ : ↥(SU σ 4)} (hγ : (γ : GL (Fin 4) K) = diagU (dvec4 a b))
    (hXc : ∀ x ∈ X, x * γ = γ * x) :
    (a = b ∧ X ≤ (suBlockB σ hσσ).range) ∨
    (a = b⁻¹ ∧ X.map (MulAut.conj (piU σ)).toMonoidHom ≤ (suBlockB σ hσσ).range) ∨
    (a = 1 ∧ X ≤ (suBlock σ).range) ∨
    (b = 1 ∧ X.map (MulAut.conj (omU σ)).toMonoidHom ≤ (suBlock σ).range) := by
  classical
  by_cases h1 : a = b
  · left
    refine ⟨h1, ?_⟩
    subst h1
    have ha1 : a ≠ 1 := fun h => hab ⟨h, h⟩
    have hγ' : γ = bB σ a (hfix a ha) := Subtype.ext hγ
    have hXC : X ≤ Subgroup.centralizer ({bB σ a (hfix a ha)} : Set ↥(SU σ 4)) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2 (hγ' ▸ hXc x hx)
    have := le_inSubgroup_perfectResidual_of_perfect hXC hX
    rwa [perfectResidual_centralizer_bB σ hσσ hK4 (hfix a ha)
      (sq_ne_one_of_pow_eq_one hr hr2 ha ha1)] at this
  by_cases h2 : a = b⁻¹
  · right; left
    refine ⟨h2, ?_⟩
    have ha1 : a ≠ 1 := fun h => hab ⟨h, by rw [h, eq_comm, inv_eq_one] at h2; exact h2⟩
    have hγ' : piU σ * γ * (piU σ)⁻¹ = bB σ a (hfix a ha) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hγ, Subgroup.coe_inv, piU_conj_diag, ← h2]
      rfl
    have hXC : X.map (MulAut.conj (piU σ)).toMonoidHom ≤
        Subgroup.centralizer ({bB σ a (hfix a ha)} : Set ↥(SU σ 4)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hγ']
      show piU σ * x * (piU σ)⁻¹ * (piU σ * γ * (piU σ)⁻¹) =
        piU σ * γ * (piU σ)⁻¹ * (piU σ * x * (piU σ)⁻¹)
      calc piU σ * x * (piU σ)⁻¹ * (piU σ * γ * (piU σ)⁻¹) = piU σ * (x * γ) * (piU σ)⁻¹ := by
            group
        _ = piU σ * (γ * x) * (piU σ)⁻¹ := by rw [hXc x hx]
        _ = _ := by group
    have := le_inSubgroup_perfectResidual_of_perfect hXC (isPerfect_map_conj hX (piU σ))
    rwa [perfectResidual_centralizer_bB σ hσσ hK4 (hfix a ha)
      (sq_ne_one_of_pow_eq_one hr hr2 ha ha1)] at this
  by_cases h3 : a = 1
  · right; right; left
    refine ⟨h3, ?_⟩
    subst h3
    have hb1 : b ≠ 1 := fun h => hab ⟨rfl, h⟩
    have hγ' : γ = b5 σ b (hfix b hb) := Subtype.ext hγ
    have hXC : X ≤ Subgroup.centralizer ({b5 σ b (hfix b hb)} : Set ↥(SU σ 4)) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2 (hγ' ▸ hXc x hx)
    have := le_inSubgroup_perfectResidual_of_perfect hXC hX
    rwa [perfectResidual_centralizer_b5 σ hF4 (hfix b hb) hb1
      (sq_ne_one_of_pow_eq_one hr hr2 hb hb1)] at this
  by_cases h4 : b = 1
  · right; right; right
    refine ⟨h4, ?_⟩
    subst h4
    have hγ' : omU σ * γ * (omU σ)⁻¹ = b5 σ a (hfix a ha) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hγ, Subgroup.coe_inv, omU_conj_diag]
      rfl
    have hXC : X.map (MulAut.conj (omU σ)).toMonoidHom ≤
        Subgroup.centralizer ({b5 σ a (hfix a ha)} : Set ↥(SU σ 4)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hγ']
      show omU σ * x * (omU σ)⁻¹ * (omU σ * γ * (omU σ)⁻¹) =
        omU σ * γ * (omU σ)⁻¹ * (omU σ * x * (omU σ)⁻¹)
      calc omU σ * x * (omU σ)⁻¹ * (omU σ * γ * (omU σ)⁻¹) = omU σ * (x * γ) * (omU σ)⁻¹ := by
            group
        _ = omU σ * (γ * x) * (omU σ)⁻¹ := by rw [hXc x hx]
        _ = _ := by group
    have := le_inSubgroup_perfectResidual_of_perfect hXC (isPerfect_map_conj hX (omU σ))
    rwa [perfectResidual_centralizer_b5 σ hF4 (hfix a ha) h3
      (sq_ne_one_of_pow_eq_one hr hr2 ha h3)] at this
  exfalso
  have hsa : a ≠ a⁻¹ := fun h => sq_ne_one_of_pow_eq_one hr hr2 ha h3 (by
    calc a ^ 2 = a * a := pow_two a
      _ = a * a⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel a)
  have hsb : b ≠ b⁻¹ := fun h => sq_ne_one_of_pow_eq_one hr hr2 hb h4 (by
    calc b ^ 2 = b * b := pow_two b
      _ = b * b⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel b)
  have hall : ∀ i j : Fin 4, i ≠ j → dvec4 a b i ≠ dvec4 a b j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [dvec4] at hij ⊢
    · exact h1
    · exact h2
    · exact hsa
    · exact fun h => h1 h.symm
    · exact hsb
    · exact fun h => h2 (by rw [h, inv_inv])
    · exact fun h => h2 h.symm
    · exact fun h => hsb h.symm
    · exact fun h => h1 h.symm
    · exact fun h => hsa h.symm
    · exact fun h => h2 (by rw [← h, inv_inv])
    · exact h1
  have hdiag : ∀ x ∈ X, ∃ d : Fin 4 → Kˣ, diagU d = (x : GL (Fin 4) K) := by
    intro x hx
    apply exists_diagU_of_isDiag
    intro i j hij
    have hcomm : (x : GL (Fin 4) K) * diagU (dvec4 a b) =
        diagU (dvec4 a b) * (x : GL (Fin 4) K) := by
      rw [← hγ]
      exact congrArg Subtype.val (hXc x hx)
    exact apply_eq_zero_of_commute_diagU hcomm (hall i j hij)
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    obtain ⟨d, hd⟩ := hdiag x hx
    obtain ⟨e, he⟩ := hdiag y hy
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hd, ← he, diagU_mul, diagU_mul, mul_comm]
  have : Group.IsPerfect ↥X := hX
  have : IsMulCommutative ↥X := ⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩
  apply hXn
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have : (⟨x, hx⟩ : ↥X) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

end CFSG.RankThree.PartOne.U4F
