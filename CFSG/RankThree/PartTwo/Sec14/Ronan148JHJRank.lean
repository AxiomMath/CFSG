module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JProd
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree.PartTwo

theorem card_sup_eq_mul_of_commute {X : Type*} [Group X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hint : U ⊓ V = ⊥) :
    Nat.card ↥(U ⊔ V) = Nat.card U * Nat.card V := by
  obtain ⟨e⟩ := nonempty_mulEquiv_prod_of_commute hUV hint
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]

theorem card_zpowers_sup_zpowers_eq_nine {X : Type*} [Group X] {x y : X} (hxy : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hy : y ∉ Subgroup.zpowers x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hy (Subgroup.one_mem _)
  have hcx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hcy : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hfin : Finite (Subgroup.zpowers y) := Nat.finite_of_card_ne_zero (by omega)
  have hUV : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute x y from hxy).zpow_zpow k l).eq
  have hint : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers y)
      rwa [hcy] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · rw [Subgroup.card_eq_one] at h1
      exact h1
    · exfalso
      have hIeq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hyI : y ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
        rw [hIeq]
        exact Subgroup.mem_zpowers y
      exact hy (Subgroup.mem_inf.mp hyI).1
  rw [card_sup_eq_mul_of_commute hUV hint, hcx, hcy]

theorem card_le_nine_of_le_tripleCover {Γ : Type} [Group Γ] {K E : Subgroup Γ} [Finite K]
    (hK : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6))) (hKp : Group.IsPerfect ↥K)
    (hEK : E ≤ K) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Sec19.IsTripleA6 ↥K := hK
  have hcardK : Nat.card ↥K = 1080 := Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hK3
  have hpow : ∀ x ∈ E.subgroupOf K, x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    simpa using hE3 _ (Subgroup.mem_subgroupOf.mp hx)
  have hcomm : ∀ a b : ↥(E.subgroupOf K), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hEc _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
  have hel : CFSG.Open.IsElemAbelian 3 (E.subgroupOf K) := ⟨⟨⟨fun a b => hcomm a b⟩⟩, hpow⟩
  have hp : IsPGroup 3 ↥(E.subgroupOf K) := fun g =>
    ⟨1, Subtype.ext (by simpa using hpow g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hcardE : Nat.card ↥(E.subgroupOf K) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hdvd : Nat.card ↥(E.subgroupOf K) ∣ 1080 := by
    have h := Subgroup.card_subgroup_dvd_card (E.subgroupOf K)
    rwa [hcardK] at h
  have hne27 : Nat.card ↥(E.subgroupOf K) ≠ 27 :=
    Sec19.Item19Res4Proof.card_ne_twentySeven_of_isTripleA6 hK3 (E.subgroupOf K) hel
  rw [← hcardE]
  rw [hn] at hdvd hne27 ⊢
  have hlt : n < 7 := by
    by_contra hcon
    have h1 : 3 ^ 7 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ n ≤ 1080 := Nat.le_of_dvd (by norm_num) hdvd
    have h7 : (3 : ℕ) ^ 7 = 2187 := by norm_num
    omega
  have key : ∀ k : ℕ, k < 7 → (3 : ℕ) ^ k ∣ 1080 → (3 : ℕ) ^ k ≠ 27 → (3 : ℕ) ^ k ≤ 9 := by
    decide
  exact key n hlt hdvd hne27

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
