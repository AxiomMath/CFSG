module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndClassical
public import CFSG.RankThree.GF2n.Stroth80.Sec86SpOrder

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem statedSp3_hom_cyclic (hK : 4 ≤ Nat.card K) (C : Type) [Group C] [IsCyclic C]
    (h : ↥(StatedSp 3 K) →* C) : h = 1 := by
  obtain ⟨hS, h16, -⟩ := endg_sp_facts hK (m := 3) (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal h.ker with hker | hker
  · exfalso
    have hinj : Function.Injective h := (MonoidHom.ker_eq_bot_iff h).mp hker
    haveI : IsCyclic ↥(StatedSp 3 K) := isCyclic_of_injective h hinj
    haveI : IsMulCommutative ↥(StatedSp 3 K) :=
      ⟨⟨fun a b => (IsCyclic.commGroup (α := ↥(StatedSp 3 K))).mul_comm a b⟩⟩
    have hprime := Group.is_simple_iff_prime_card.mp hS
    rcases Nat.Prime.eq_one_or_self_of_dvd hprime 16 h16 with h' | h'
    · omega
    · rw [← h'] at hprime
      norm_num at hprime
  · exact MonoidHom.ext fun g => by
      have : g ∈ h.ker := by rw [hker]; trivial
      simpa using this

theorem statedSp3_hom_perm (hK : 4 ≤ Nat.card K) (ι : Type) [Fintype ι]
    (hι : Fintype.card ι ≤ 8) (h : ↥(StatedSp 3 K) →* Equiv.Perm ι) : h = 1 := by
  classical
  obtain ⟨hS, -, -⟩ := endg_sp_facts hK (m := 3) (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal h.ker with hker | hker
  · exfalso
    have hinj : Function.Injective h := (MonoidHom.ker_eq_bot_iff h).mp hker
    have hdvd := Subgroup.card_dvd_of_injective h hinj
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm ι), Fintype.card_perm] at hdvd
    have h8 : (Fintype.card ι).factorial ∣ (8 : ℕ).factorial := Nat.factorial_dvd_factorial hι
    have hdvd8 := hdvd.trans h8
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf'⟩ := FiniteField.card K 2
    have hf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf'
    obtain ⟨o, hodd, hord⟩ := exists_odd_card_statedSp (K := K) (f := (f : ℕ)) f.pos hf 3
    have hf2 : 2 ≤ (f : ℕ) := by
      by_contra hlt
      have : (f : ℕ) = 1 := by have := f.pos; omega
      rw [this] at hf
      omega
    have hpos : 0 < (8 : ℕ).factorial := Nat.factorial_pos 8
    have hle := Nat.le_of_dvd hpos hdvd8
    have hge : 4 ^ 9 ≤ Nat.card ↥(StatedSp 3 K) := by
      rw [hord]
      have ho : 1 ≤ o := by
        obtain ⟨k, hk⟩ := hodd
        omega
      have e : (2 ^ (f : ℕ)) ^ (3 ^ 2) = 2 ^ ((f : ℕ) * 9) := by
        rw [← pow_mul]
        norm_num
      have h1 : 4 ^ 9 ≤ (2 ^ (f : ℕ)) ^ (3 ^ 2) := by
        rw [e]
        calc 4 ^ 9 = 2 ^ 18 := by norm_num
          _ ≤ 2 ^ ((f : ℕ) * 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact h1.trans (Nat.le_mul_of_pos_right _ ho)
    have : (8 : ℕ).factorial = 40320 := by decide
    omega
  · exact MonoidHom.ext fun g => by
      have : g ∈ h.ker := by rw [hker]; trivial
      simpa using this

theorem hom_trivial_of_surj {R G₀ H : Type} [Group R] [Group G₀] [Group H] (φ : R →* G₀)
    (hφ : Function.Surjective φ) (htriv : ∀ h' : G₀ →* H, h' = 1) (h : R →* H)
    (hker : ∀ g : R, φ g = 1 → h g = 1) : h = 1 := by
  have hle : φ.ker ≤ h.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact hker g hg
  have h1 := htriv (MonoidHom.liftOfSurjective φ hφ ⟨h, hle⟩)
  refine MonoidHom.ext fun x => ?_
  have h2 := MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ)
    (Function.rightInverse_surjInv hφ) ⟨h, hle⟩ x
  have h3 : (φ.liftOfSurjective hφ ⟨h, hle⟩) (φ x) = h x := h2
  rw [h1] at h3
  simpa using h3.symm

theorem statedSp3_surj_cyclic (hK : 4 ≤ Nat.card K) {R : Type} [Group R]
    (φ : R →* ↥(StatedSp 3 K)) (hφ : Function.Surjective φ) (C : Type) [Group C] [IsCyclic C]
    (h : R →* C) (hker : ∀ g : R, φ g = 1 → h g = 1) : h = 1 :=
  hom_trivial_of_surj φ hφ (statedSp3_hom_cyclic hK C) h hker

theorem statedSp3_surj_perm (hK : 4 ≤ Nat.card K) {R : Type} [Group R]
    (φ : R →* ↥(StatedSp 3 K)) (hφ : Function.Surjective φ) (ι : Type) [Fintype ι]
    (hι : Fintype.card ι ≤ 8) (h : R →* Equiv.Perm ι) (hker : ∀ g : R, φ g = 1 → h g = 1) :
    h = 1 :=
  hom_trivial_of_surj φ hφ (statedSp3_hom_perm hK ι hι) h hker

end CFSG.RankThree.GF2n.Stroth80
