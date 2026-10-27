module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open scoped IsMulCommutative

theorem thompson_transfer_quartic {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) {Q : Subgroup X}
    (hindex : Q.relIndex (P : Subgroup X) = 2) {g : X}
    (hgP : g ∈ (P : Subgroup X)) (hg4 : g ^ 4 = 1) (hg2 : ∀ x : X, x⁻¹ * g ^ 2 * x = g ^ 2)
    (hQg : ∀ x : X, x⁻¹ * g * x ∉ Q) :
    ∃ N : Subgroup X, N.Normal ∧ N.index = 2 ∧ (∀ x : X, x ^ 2 ∈ N) ∧ g ∉ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup X := (P : Subgroup X) with hP'
  set Q' : Subgroup P' := Q.subgroupOf P' with hQ'
  have hQ'index : Q'.index = 2 := hindex
  have : Q'.Normal := Subgroup.normal_of_index_eq_two hQ'index
  have hcard : Nat.card (P' ⧸ Q') = 2 := by rw [← Subgroup.index_eq_card]; exact hQ'index
  have : IsCyclic (P' ⧸ Q') := isCyclic_of_prime_card hcard
  let ϕ : P' →* P' ⧸ Q' := QuotientGroup.mk' Q'
  have hgnot : (⟨g, hgP⟩ : P') ∉ Q' := fun hmem =>
    hQg 1 (by simpa using Subgroup.mem_subgroupOf.1 hmem)
  have hconjnot : ∀ (a : X) (ha : a⁻¹ * g * a ∈ P'), (⟨a⁻¹ * g * a, ha⟩ : P') ∉ Q' :=
    fun a ha hmem => hQg a (Subgroup.mem_subgroupOf.1 hmem)
  have hsame : ∀ x y : P', x ∉ Q' → y ∉ Q' → ϕ x = ϕ y := by
    intro x y hx hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mul_mem_iff_of_index_two hQ'index]
    simp only [inv_mem_iff]
    exact iff_of_false hx hy
  have hg3 : g ^ 3 = g⁻¹ := by
    have : g ^ 3 * g = 1 := by rw [← pow_succ, hg4]
    exact (eq_inv_of_mul_eq_one_left this)
  have hpow : ∀ k : ℕ, g ^ k = g ^ (k % 4) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, hg4, one_pow, one_mul]
  have hV := transfer_eq_pow_of_forall ϕ hgP (by
    intro k a ha
    have hmk : g ^ (k % 4) = g ^ k := (hpow k).symm
    have hkP : a⁻¹ * g ^ (k % 4) * a ∈ P' := by rw [hmk]; exact ha
    have e1 : (⟨a⁻¹ * g ^ k * a, ha⟩ : P') = ⟨a⁻¹ * g ^ (k % 4) * a, hkP⟩ :=
      Subtype.ext (by simp only [hmk])
    have e2 : (⟨g ^ k, P'.pow_mem hgP k⟩ : P') = ⟨g ^ (k % 4), P'.pow_mem hgP _⟩ :=
      Subtype.ext hmk.symm
    rw [e1, e2]
    have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize k % 4 = r at hr hkP ⊢
    interval_cases r
    · simp
    · have ha' : a⁻¹ * g * a ∈ P' := by simpa using hkP
      exact hsame _ _ (by simpa using hconjnot a ha') (by simpa using hgnot)
    · have e3 : (⟨a⁻¹ * g ^ 2 * a, hkP⟩ : P') = ⟨g ^ 2, P'.pow_mem hgP 2⟩ :=
        Subtype.ext (by simpa using hg2 a)
      rw [e3]
    · have ha' : a⁻¹ * g * a ∈ P' := by
        have h1 : (a⁻¹ * g ^ 3 * a)⁻¹ ∈ P' := P'.inv_mem hkP
        have h2 : (a⁻¹ * g ^ 3 * a)⁻¹ = a⁻¹ * g * a := by
          rw [hg3]; group
        rwa [h2] at h1
      have n1 : (⟨a⁻¹ * g ^ 3 * a, hkP⟩ : P') ∉ Q' := by
        intro hmem
        have h1 := Subgroup.mem_subgroupOf.1 hmem
        have h2 : a⁻¹ * g * a = (a⁻¹ * g ^ 3 * a)⁻¹ := by rw [hg3]; group
        exact hconjnot a ha' (Subgroup.mem_subgroupOf.2 (by simpa [h2] using Q.inv_mem h1))
      have n2 : (⟨g ^ 3, P'.pow_mem hgP 3⟩ : P') ∉ Q' := by
        intro hmem
        have h1 := Subgroup.mem_subgroupOf.1 hmem
        have h2 : g = (g ^ 3)⁻¹ := by rw [hg3]; simp
        exact hgnot (Subgroup.mem_subgroupOf.2 (by
          have := Q.inv_mem h1
          rwa [← h2] at this))
      exact hsame _ _ n1 n2)
  set z : P' ⧸ Q' := ϕ ⟨g, hgP⟩ with hz
  have hz1 : z ≠ 1 := fun h => hgnot ((QuotientGroup.eq_one_iff _).1 h)
  have hsq : ∀ w : P' ⧸ Q', w ^ 2 = 1 := fun w => by
    simpa [hcard] using pow_card_eq_one' (G := P' ⧸ Q') (x := w)
  have hodd : Odd P'.index := by
    have := P.not_dvd_index
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 this)
  have hVg : MonoidHom.transfer ϕ g = z := by
    rw [hV]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hsq z, one_pow, one_mul]
  have hrange : (MonoidHom.transfer ϕ).range = ⊤ := by
    have hle : (MonoidHom.transfer ϕ).range ≠ ⊥ := fun h => by
      have : MonoidHom.transfer ϕ g ∈ (MonoidHom.transfer ϕ).range := ⟨g, rfl⟩
      rw [h, Subgroup.mem_bot, hVg] at this
      exact hz1 this
    have hc : Nat.card (MonoidHom.transfer ϕ).range ∣ 2 := hcard ▸ Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_two).1 hc with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hle
    · exact Subgroup.eq_top_of_card_eq _ (by rw [h, hcard])
  refine ⟨(MonoidHom.transfer ϕ).ker, inferInstance, ?_, fun x => ?_, fun hg => ?_⟩
  · rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcard]
  · rw [MonoidHom.mem_ker, map_pow, hsq]
  · rw [MonoidHom.mem_ker, hVg] at hg
    exact hz1 hg

variable {G : Type*} [Group G]

theorem thompson_transfer_quartic_subgroup [Finite G] {X P Q : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.relIndex X) (hQidx : Q.relIndex P = 2) {g : G}
    (hgP : g ∈ P) (hg4 : g ^ 4 = 1) (hg2 : ∀ x ∈ X, x⁻¹ * g ^ 2 * x = g ^ 2)
    (hQg : ∀ x ∈ X, x⁻¹ * g * x ∉ Q) :
    ∃ N : Subgroup G, N ≤ X ∧ (N.subgroupOf X).Normal ∧ N.relIndex X = 2 ∧
      (∀ x ∈ X, x ^ 2 ∈ N) ∧ g ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  let S : Sylow 2 X := hP2'.toSylow (by simpa [Subgroup.relIndex] using hPidx)
  have hQidx' : (Q.subgroupOf X).relIndex (S : Subgroup X) = 2 := by
    have hS : (S : Subgroup X) = P.subgroupOf X := rfl
    rw [hS, Subgroup.relIndex_subgroupOf hPX]
    exact hQidx
  have hgX : g ∈ X := hPX hgP
  obtain ⟨N', hN'n, hN'i, hN'sq, hN'g⟩ := thompson_transfer_quartic S hQidx'
    (g := (⟨g, hgX⟩ : X)) (Subgroup.mem_subgroupOf.2 hgP)
    (Subtype.ext (by simpa using hg4))
    (fun x => Subtype.ext (by simpa using hg2 x x.2))
    (fun x hmem => hQg x x.2 (by simpa using Subgroup.mem_subgroupOf.1 hmem))
  have hcomap : (N'.map X.subtype).subgroupOf X = N' :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective N'
  refine ⟨N'.map X.subtype, Subgroup.map_subtype_le N', ?_, ?_, ?_, ?_⟩
  · rw [hcomap]; exact hN'n
  · rw [Subgroup.relIndex, hcomap]; exact hN'i
  · intro x hx
    exact ⟨⟨x, hx⟩ ^ 2, hN'sq ⟨x, hx⟩, rfl⟩
  · rintro ⟨n, hn, hnu⟩
    have : n = ⟨g, hgX⟩ := Subtype.ext hnu
    exact hN'g (this ▸ hn)

end CFSG.Quasithin
