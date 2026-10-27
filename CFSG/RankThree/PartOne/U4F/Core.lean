module

public import CFSG.RankThree.PartOne.U4F.CoreDiag
public import CFSG.RankThree.PartOne.K1320.SU4Gen
public import CFSG.RankThree.PartOne.KF.SUSylow

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

theorem pow_eq_one_of_closure_pair {G : Type*} [Group G] {ρ τ : G} {r : ℕ} (hρ : ρ ^ r = 1)
    (hτ : τ ^ r = 1) (hc : ρ * τ = τ * ρ) : ∀ x ∈ Subgroup.closure {ρ, τ}, x ^ r = 1 := by
  have hgen : ∀ a ∈ ({ρ, τ} : Set G), ∀ b ∈ ({ρ, τ} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hc
    · exact hc.symm
    · rfl
  have hpair : ({ρ, τ} : Set G).Pairwise Commute := fun a ha b hb _ => hgen a ha b hb
  have := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ x ∈ Subgroup.closure {ρ, τ}, ∀ y ∈ Subgroup.closure {ρ, τ}, x * y = y * x :=
    fun x hx y hy => setLike_mul_comm hx hy
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x ^ r = 1) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with rfl | rfl
    · exact hρ
    · exact hτ
  · exact one_pow r
  · intro x y hx hy hxr hyr
    rw [Commute.mul_pow (show Commute x y from hcomm x hx y hy), hxr, hyr, mul_one]
  · intro x hx hxr
    rw [inv_pow, hxr, inv_one]

theorem exists_primitiveRoot_of_dvd {K : Type} [Field K] [Finite K] {f r : ℕ} (hr : r.Prime)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hrq : r ∣ 2 ^ f - 1) : ∃ ζ : Kˣ, IsPrimitiveRoot ζ r := by
  have : Fact r.Prime := ⟨hr⟩
  have hdvd : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
    exact hrq.trans h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hdvd
  refine ⟨z, ?_⟩
  have := IsPrimitiveRoot.orderOf z
  rwa [hz] at this

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem Config.sup_eq_top (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f - 1) {A B : Subgroup ↥(SU (unitaryInvolution K 2 f) 4)}
    {ρ τ : ↥(SU (unitaryInvolution K 2 f) 4)} (c : Config (unitaryInvolution K 2 f) r A B ρ τ) :
    A ⊔ B = ⊤ := by
  classical
  have hσσ : ∀ x, unitaryInvolution K 2 f (unitaryInvolution K 2 f x) = x :=
    unitaryInvolution_involutive hK
  have hFq : Nat.card (fixF (unitaryInvolution K 2 f)) = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hF4 : 4 ≤ Nat.card (fixF (unitaryInvolution K 2 f)) := by rw [hFq]; exact h4
  have hlt : Nat.card (fixF (unitaryInvolution K 2 f)) < Nat.card K := by
    rw [hFq, hK]
    nlinarith
  have hfix : ∀ u : Kˣ, u ^ r = 1 → unitaryInvolution K 2 f (u : K) = u :=
    fun u hu => fix_of_pow_eq_one hrq hu
  have hprim := exists_primitiveRoot_of_dvd hr hK hrq
  have hgen := CFSG.RankThree.PartOne.K1320.suBlock_sup_suBlockB_eq_top hK (by omega : 1 ≤ f)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hK hr hr2 hrq
    (Subgroup.closure {ρ, τ}) (pow_eq_one_of_closure_pair c.rho_pow c.tau_pow c.comm)
  exact sup_eq_top_of_map_conj g (core_diag hσσ hK4 hF4 hlt hr hr2 hfix hprim hgen (c.conj g)
    (hg ρ (Subgroup.subset_closure (by simp))) (hg τ (Subgroup.subset_closure (by simp))))

end CFSG.RankThree.PartOne.U4F
