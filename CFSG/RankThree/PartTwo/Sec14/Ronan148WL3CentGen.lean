module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun β : MulAut G => (β : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)

@[expose] def mapsToSub {G : Type*} [Group G] [Finite G] (W : Subgroup G) :
    Subgroup (MulAut G) where
  carrier := {β | ∀ w ∈ W, β w ∈ W}
  mul_mem' {a b} ha hb w hw := ha _ (hb w hw)
  one_mem' w hw := hw
  inv_mem' {a} ha := by
    have := finite_mulAut G
    have hpow : ∀ n : ℕ, ∀ w ∈ W, (a ^ n) w ∈ W := by
      intro n
      induction n with
      | zero => intro w hw; simpa using hw
      | succ n ih =>
        intro w hw
        rw [pow_succ, MulAut.mul_apply]
        exact ih _ (ha w hw)
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
    intro w hw
    change (a⁻¹ : MulAut G) w ∈ W
    rw [hinv]
    exact hpow _ w hw

variable {K : Type} [Field K] {p f : ℕ} {π : Bool} {ι : Type*}
  {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))} {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem finite_projImage (hK : PiField π p f K) :
    Finite (projImage (slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  exact Subtype.finite

theorem CentConfig.mem_sup (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (hc : CentConfig π p f K α e₀) (he₀1 : e₀ ≠ 1) (he₀3 : e₀ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range α)) ∣ 9)
    {γ : MulAut (projImage (slPi π 3 (p ^ f) K))}
    (hγR : γ ∈ Subgroup.closure (Set.range α)) (hγo : ∀ u, γ ≠ MulAut.conj u) (x : ι) :
    α x ∈ Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers γ := by
  have := finite_projImage hK
  have := finite_mulAut (projImage (slPi π 3 (p ^ f) K))
  set R := Subgroup.closure (Set.range α) with hR
  set H := Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers γ with hH
  have hconjR : MulAut.conj e₀ ∈ R := by
    obtain ⟨x₀, hx₀⟩ := hc.conj_e
    rw [← hx₀]
    exact Subgroup.subset_closure ⟨x₀, rfl⟩
  have hHR : H ≤ R := sup_le (Subgroup.zpowers_le.mpr hconjR) (Subgroup.zpowers_le.mpr hγR)
  have hord : orderOf (MulAut.conj e₀) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, he₀3, map_one])
      (fun h => he₀1 (eq_one_of_conj_eq_one hK hq hq2 h))
  have hZ3 : Nat.card (Subgroup.zpowers (MulAut.conj e₀)) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hne : Nat.card H ≠ 3 := by
    intro h
    have heq : Subgroup.zpowers (MulAut.conj e₀) = H :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hZ3])
    have hγ : γ ∈ Subgroup.zpowers (MulAut.conj e₀) :=
      heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hγ
    exact hγo (e₀ ^ k) (by rw [← hk, map_zpow])
  have hdvdHR : Nat.card H ∣ Nat.card R := Subgroup.card_dvd_of_le hHR
  have hdvdH : Nat.card H ∣ 3 ^ 2 := dvd_trans hdvdHR hcard
  have h3H' : Nat.card (Subgroup.zpowers (MulAut.conj e₀)) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le le_sup_left
  rw [hZ3] at h3H'
  have hH9 : Nat.card H = 9 := by
    obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvdH
    rw [hkH] at hne h3H' ⊢
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact absurd h3H' (by norm_num)
    · exact absurd rfl hne
    · rfl
  have hHR' : H = R := Subgroup.eq_of_le_of_card_ge hHR (by
    rw [hH9]
    exact Nat.le_of_dvd (by norm_num) hcard)
  rw [hHR']
  exact Subgroup.subset_closure ⟨x, rfl⟩

theorem fixed_of_mem_sup {G : Type*} [Group G] {a b β : MulAut G} {w : G} (ha : a w = w)
    (hb : b w = w) (hβ : β ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : β w = w := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ MulAction.stabilizer (MulAut G) w :=
    sup_le (Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact ha))
      (Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hb))
  have := hle hβ
  rwa [MulAction.mem_stabilizer_iff] at this

theorem mapsTo_of_mem_sup {G : Type*} [Group G] [Finite G] {a b β : MulAut G} {W : Subgroup G}
    (ha : ∀ w ∈ W, a w ∈ W) (hb : ∀ w ∈ W, b w ∈ W)
    (hβ : β ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : ∀ w ∈ W, β w ∈ W := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ mapsToSub W :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  exact hle hβ

theorem CentConfig.exists_outer (hfalse : (∀ x, ∃ u : projImage (slPi π 3 (p ^ f) K),
      α x = MulAut.conj u) → False) :
    ∃ x, ∀ u, α x ≠ MulAut.conj u := by
  by_contra h
  push Not at h
  exact hfalse h

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
