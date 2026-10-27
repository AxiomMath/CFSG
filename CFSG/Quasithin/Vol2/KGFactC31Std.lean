module

public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import CFSG.Quasithin.Vol2.KGFactC31Act

public section

namespace CFSG.Quasithin.KGC31

theorem exists_conj_zpowers {X : Type} [Group X] [Finite X] {N₀ : Subgroup X} {x : X}
    (hxN : x ∈ N₀) {p : ℕ} [hp : Fact p.Prime] (hx : orderOf x = p)
    (hp2 : ¬ p ^ 2 ∣ Nat.card N₀) {y : X} (hyN : y ∈ N₀) (hy : ∃ k : ℕ, y ^ p ^ k = 1)
    (hy1 : y ≠ 1) :
    ∃ n ∈ N₀, n * y * n⁻¹ ∈ Subgroup.zpowers x ∧ x ∈ Subgroup.zpowers (n * y * n⁻¹) := by
  set x' : N₀ := ⟨x, hxN⟩
  set y' : N₀ := ⟨y, hyN⟩
  set P : Subgroup N₀ := Subgroup.zpowers x' with hPdef
  have hx' : orderOf x' = p := by rw [Subgroup.orderOf_mk, hx]
  have hPc : Nat.card P = p := by rw [Nat.card_zpowers, hx']
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hPc, pow_one])
  have hPi : ¬ p ∣ P.index := by
    intro hdvd
    apply hp2
    rw [← P.card_mul_index, hPc, pow_two]
    exact Nat.mul_dvd_mul_left p hdvd
  have hy' : ∃ k : ℕ, y' ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hPp hPi hy'
  have hmem : (g : X)⁻¹ * y * g ∈ Subgroup.zpowers x := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa [x', y'] using congrArg Subtype.val hi⟩
  have hne : (g : X)⁻¹ * y * g ≠ 1 := by
    intro h
    apply hy1
    have h' : y = (g : X) * ((g : X)⁻¹ * y * g) * (g : X)⁻¹ := by group
    rw [h', h]
    group
  refine ⟨(g : X)⁻¹, N₀.inv_mem g.2, ?_, ?_⟩
  · simpa using hmem
  · have := mem_zpowers_of_prime hp.out hx hmem hne
    simpa using this

theorem false_of_conj_not_normalizer {A : Type*} [Group A] {M₀ R V : Subgroup A}
    (hNRM : Subgroup.normalizer (R : Set A) ≤ Subgroup.normalizer (M₀ : Set A))
    (hM₀V : M₀ ≤ Subgroup.normalizer (V : Set A)) {x g : A} (hx : x ∈ M₀)
    (hg : g ∈ Subgroup.normalizer (R : Set A))
    (hgx : g * x * g⁻¹ ∉ Subgroup.normalizer (V : Set A)) : False :=
  hgx (hM₀V ((Subgroup.mem_normalizer_iff.mp (hNRM hg) x).mp hx))

theorem eq_bot_of_perfect_of_isSolvable {X : Type*} [Group X] {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hs : Group.IsSolvable K) : K = ⊥ := by
  have hc : commutator K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, hK, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hd : ∀ k, derivedSeries K k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hc]
  obtain ⟨k, hk⟩ := (Group.isSolvable_def _).mp hs
  have htb : (⊤ : Subgroup K) = ⊥ := (hd k).symm.trans hk
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : K) ∈ (⊥ : Subgroup K) := htb ▸ Subgroup.mem_top _
  have h2 : (⟨x, hx⟩ : K) = 1 := Subgroup.mem_bot.mp h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

theorem eq_bot_of_perfect_of_card {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hc : Nat.card K = p ^ a * q ^ b) : K = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  exact eq_bot_of_perfect_of_isSolvable hK
    (CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
      (by rwa [← Nat.card_eq_fintype_card]))

end CFSG.Quasithin.KGC31

end
