module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem HSL_mul_HSL {F : Type*} [Field F] (t t' : Fˣ) : HSL t * HSL t' = HSL (t * t') := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one_eq_one {F : Type*} [Field F] : HSL (1 : Fˣ) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem HSL_pow {F : Type*} [Field F] (t : Fˣ) (n : ℕ) : HSL t ^ n = HSL (t ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, HSL_one_eq_one]
  | succ n ih => rw [pow_succ, ih, HSL_mul_HSL, pow_succ]

theorem exists_orderOf_HSL_eq {F H : Type*} [Field F] [Finite F] [Group H] (ρ : SL2 F →* H)
    (hker : ∀ g ∈ ρ.ker, ∃ l : Fˣ, (l : F) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card F - 1) :
    ∃ u : Fˣ, orderOf (ρ (HSL u)) = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_units] at hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨u, orderOf_eq_prime ?_ fun h1 => ?_⟩
  · rw [← map_pow, HSL_pow, ← hu, pow_orderOf_eq_one, HSL_one_eq_one, map_one]
  · obtain ⟨l, hl, hg⟩ := hker _ h1
    have h00 := congrFun (congrFun hg 0) 0
    simp only [HSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h00
    have hu2 : u ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h00, hl, Units.val_one])
    have h := orderOf_dvd_of_pow_eq_one hu2
    rw [hu] at h
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd two_pos h) hp.two_le)

theorem not_dvd_card_sub_one_of_range_le {F H : Type*} [Field F] [Finite F] [Group H]
    (ρ : SL2 F →* H)
    (hker : ∀ g ∈ ρ.ker, ∃ l : Fˣ, (l : F) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F))
    {C : Subgroup H} (hC : ρ.range ≤ C) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpC : ¬ p ∣ Nat.card C) : ¬ p ∣ Nat.card F - 1 := by
  intro hdvd
  obtain ⟨u, hu⟩ := exists_orderOf_HSL_eq ρ hker hp hp2 hdvd
  have hmem : ρ (HSL u) ∈ C := hC ⟨_, rfl⟩
  apply hpC
  rw [← hu, ← Subgroup.orderOf_mk (ρ (HSL u)) hmem]
  exact orderOf_dvd_natCard _

theorem isCyclic_of_le_of_coprime_ker {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    [Fact p.Prime] {A₀ : Subgroup X} (δ : A₀ →* Y) (hδ : IsCyclic δ.range)
    (hker : Nat.Coprime (Nat.card δ.ker) p) {Q : Subgroup X} (hQA : Q ≤ A₀)
    (hQ : IsPGroup p Q) : IsCyclic Q := by
  have e : Q.subgroupOf A₀ ≃* Q := Subgroup.subgroupOfEquivOfLe hQA
  have : IsCyclic (Q.subgroupOf A₀) :=
    isCyclic_of_injective _ (injective_comp_of_isPGroup δ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (hQ.of_equiv e.symm))
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem isCyclic_of_isPGroup_of_conj_mul {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hpC : ¬ p ∣ Nat.card C) {A : Subgroup (MulAut C)}
    (hIA : ∀ α : MulAut C, ∃ c : C, ∃ β ∈ A, α = MulAut.conj c * β)
    (hA : ∀ Q : Subgroup (MulAut C), Q ≤ A → IsPGroup p Q → IsCyclic Q)
    {P : Subgroup (MulAut C)} (hP : IsPGroup p P) : IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  refine isCyclic_of_isPGroup_of_normal_mul (coprime_card_inner hp hpC) (fun α => ?_) hA hP
  obtain ⟨c, β, hβ, rfl⟩ := hIA α
  exact ⟨MulAut.conj c, ⟨c, rfl⟩, β, hβ, rfl⟩

theorem eq_one_of_pow_eq_one_of_pow_prime_pow_eq_one {G : Type*} [Monoid G] {x : G} {m p k : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : x ^ m = 1) (hk : x ^ p ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have h := pow_gcd_eq_one.2 ⟨hk, hm⟩
  rwa [hcop, pow_one] at h

theorem perm_pow_card_factorial {n : ℕ} (π : Equiv.Perm (Fin n)) : π ^ n.factorial = 1 := by
  have h := pow_card_eq_one (x := π)
  rwa [Fintype.card_perm, Fintype.card_fin] at h

theorem coprime_of_dvd_of_lt {m n p : ℕ} (hp : p.Prime) (hmn : m ∣ n) (hn : 0 < n)
    (hnp : n < p) : Nat.Coprime m p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
    absurd (Nat.le_of_dvd hn (h.trans hmn)) (by omega)).symm

theorem isCyclic_of_le_range_of_inf_map_ker_eq_bot {Γ X Y : Type*} [Group Γ] [Group X]
    [Group Y] (κ : Γ →* X) (ψ : Γ →* Y) (hψ : IsCyclic ψ.range) {A : Subgroup X}
    (hA : A ≤ κ.range) (hAD : A ⊓ ψ.ker.map κ = ⊥) : IsCyclic A := by
  set B := A.comap κ
  let f : B →* A := (κ.comp B.subtype).codRestrict A fun b => b.2
  let g : B →* ψ.range := (ψ.comp B.subtype).codRestrict ψ.range fun b => ⟨b, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨γ, rfl⟩ := hA hx
    exact ⟨⟨γ, hx⟩, rfl⟩
  have hker : g.ker ≤ f.ker := by
    intro b hb
    have hb' : ψ b = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hb)
    have hmem : κ b ∈ A ⊓ ψ.ker.map κ := ⟨b.2, ⟨b, hb', rfl⟩⟩
    rw [hAD, Subgroup.mem_bot] at hmem
    exact (MonoidHom.mem_ker).2 (Subtype.ext hmem)
  have := hψ
  let θ : g.range →* A := (QuotientGroup.lift g.ker f hker).comp
    (QuotientGroup.quotientKerEquivRange g).symm.toMonoidHom
  refine isCyclic_of_surjective θ fun a => ?_
  obtain ⟨b, rfl⟩ := hf a
  refine ⟨QuotientGroup.quotientKerEquivRange g (b : B ⧸ g.ker), ?_⟩
  simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    QuotientGroup.lift_mk]

theorem not_dvd_factorial_of_le_four {p n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hn : n ≤ 4) :
    ¬ p ∣ n.factorial := by
  rw [hp.dvd_factorial]
  intro h
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp (by norm_num)

end CFSG.RankThree.Automorphisms
