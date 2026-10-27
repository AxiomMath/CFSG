module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin

@[expose] def NoE9CentralizedByInvolution (X : Type) [Group X] : Prop :=
  ∀ l : X, l * l = 1 → l ≠ 1 →
    ∀ P : Subgroup X, P ≤ Subgroup.centralizer ({l} : Set X) → Nat.card P = 9 →
      (∀ x ∈ P, x ^ 3 = 1) → False

theorem NoE9CentralizedByInvolution.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoE9CentralizedByInvolution Y) : NoE9CentralizedByInvolution X := by
  intro l hl2 hl1 P hPl hP9 hP3
  refine h (e l) ?_ ?_ (P.map e.toMonoidHom) ?_ ?_ ?_
  · rw [← map_mul, hl2, map_one]
  · exact fun h1 => hl1 (e.injective (by rw [h1, map_one]))
  · rintro _ ⟨p, hp, rfl⟩
    have hp' := Subgroup.mem_centralizer_singleton_iff.1 (hPl hp)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e p * e l = e l * e p
    rw [← map_mul, ← map_mul, hp']
  · rw [Subgroup.card_map_of_injective e.injective, hP9]
  · rintro _ ⟨p, hp, rfl⟩
    change e p ^ 3 = 1
    rw [← map_pow, hP3 p hp, map_one]

theorem noE9CentralizedByInvolution_of_not_dvd {X : Type} [Group X]
    (h : ∀ l : X, l * l = 1 → l ≠ 1 → ¬ 9 ∣ Nat.card (Subgroup.centralizer ({l} : Set X))) :
    NoE9CentralizedByInvolution X := by
  intro l hl2 hl1 P hPl hP9 _
  exact h l hl2 hl1 (hP9 ▸ Subgroup.card_dvd_of_le hPl)

open scoped Pointwise in
theorem false_of_orderOf_nine_of_card_nine {Q : Type*} [Group Q] [Finite Q] {m : ℕ}
    (hQ : Nat.card Q = 9 * m) (hm : ¬ 3 ∣ m) {g : Q} (hg : orderOf g = 9)
    {E : Subgroup Q} (hE9 : Nat.card E = 9) (hE3 : ∀ x ∈ E, x ^ 3 = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT9 : Nat.card (Subgroup.zpowers g) = 9 := by rw [Nat.card_zpowers, hg]
  have hTp : IsPGroup 3 (Subgroup.zpowers g) := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hindex : ∀ K : Subgroup Q, Nat.card K = 9 → ¬ 3 ∣ K.index := by
    intro K hK
    have h := K.card_mul_index
    rw [hK, hQ] at h
    have : K.index = m := by omega
    rw [this]
    exact hm
  let ST : Sylow 3 Q := hTp.toSylow (hindex _ hT9)
  let SE : Sylow 3 Q := hEp.toSylow (hindex _ hE9)
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q ST SE
  have hmem : q * g * q⁻¹ ∈ E := by
    have h1 : ((q • ST : Sylow 3 Q) : Subgroup Q) = MulAut.conj q • (ST : Subgroup Q) :=
      Sylow.coe_subgroup_smul
    rw [hq] at h1
    have h2 : (MulAut.conj q) g ∈ MulAut.conj q • (ST : Subgroup Q) :=
      Subgroup.smul_mem_pointwise_smul g (MulAut.conj q) _ (Subgroup.mem_zpowers g)
    rw [← h1] at h2
    exact h2
  have h3 : (q * g * q⁻¹) ^ 3 = 1 := hE3 _ hmem
  have h4 : g ^ 3 = 1 := by
    have : (q * g * q⁻¹) ^ 3 = q * g ^ 3 * q⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow]
      rfl
    rw [this] at h3
    have h5 : g ^ 3 = q⁻¹ * (q * g ^ 3 * q⁻¹) * q := by group
    rw [h5, h3]
    group
  have h6 := orderOf_dvd_of_pow_eq_one h4
  rw [hg] at h6
  omega

theorem centralizer_singleton_le_normalizer_zpowers {X : Type} [Group X] (l : X) :
    Subgroup.centralizer ({l} : Set X) ≤ Subgroup.normalizer (Subgroup.zpowers l : Set X) := by
  have h : Subgroup.centralizer ({l} : Set X) =
      Subgroup.centralizer (Subgroup.zpowers l : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h]
  exact Subgroup.centralizer_le_normalizer _

theorem card_centralizer_singleton_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [← hc]
  constructor
  · intro hx
    calc c * x * c⁻¹ * (c * a * c⁻¹) = c * (x * a) * c⁻¹ := by group
      _ = c * (a * x) * c⁻¹ := by rw [hx]
      _ = c * a * c⁻¹ * (c * x * c⁻¹) := by group
  · intro hx
    have : c * (x * a) * c⁻¹ = c * (a * x) * c⁻¹ := by
      calc c * (x * a) * c⁻¹ = c * x * c⁻¹ * (c * a * c⁻¹) := by group
        _ = c * a * c⁻¹ * (c * x * c⁻¹) := hx
        _ = c * (a * x) * c⁻¹ := by group
    simpa using this

end CFSG.Quasithin
