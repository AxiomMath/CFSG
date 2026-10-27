module

public import CFSG.Quasithin.EmptyFaithful.S153E57B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace S153E58

open S153E57

theorem finite_mulAut_of_finite (W : Type*) [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W)) (fun _ _ h => MulEquiv.ext (congrFun h))

section Inverting

variable {W : Type*} [CommGroup W]

theorem commIn153_top_eq_commV (X : Subgroup (MulAut W)) :
    commIn153 X (⊤ : Subgroup W) = commV X := by
  unfold commIn153 commV
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, w, -, rfl⟩
    exact ⟨a, ha, w, rfl⟩
  · rintro ⟨a, ha, w, rfl⟩
    exact ⟨a, ha, w, Subgroup.mem_top _, rfl⟩

theorem commV_zpowers_eq_map {a : MulAut W} (ha2 : a ^ 2 = 1) :
    commV (Subgroup.zpowers a) = (⊤ : Subgroup W).map (phi a) := by
  rw [← commIn153_top_eq_commV]
  refine commIn153_eq_map (V := Subgroup.zpowers a) (Subgroup.mem_zpowers a) ?_ ⊤
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul]
    simp [ha2]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul]
    simp [ha2]

theorem fixSub_le_range_phi [Finite W] (hW : ∀ w : W, w * w = 1) {K : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card ↥K)) {a : MulAut W}
    (hinv : ∀ k ∈ K, a * k * a⁻¹ = k⁻¹) (hfix : ∀ x : W, (∀ k ∈ K, k x = x) → x = 1) :
    fixSub a ≤ (⊤ : Subgroup W).map (phi a) := by
  classical
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  have : Fintype ↥K := Fintype.ofFinite _
  intro x hx
  set R : Subgroup W := (⊤ : Subgroup W).map (phi a) with hR
  let π : W →* W ⧸ R := QuotientGroup.mk' R
  let f : ↥K → W ⧸ R := fun k => π ((k : MulAut W) x)
  have hax : a x = x := hx
  have hN : (∏ k : ↥K, (k : MulAut W) x) = 1 := by
    apply hfix
    intro k' hk'
    have : (k' : MulAut W) (∏ k : ↥K, (k : MulAut W) x) = ∏ k : ↥K, (k' : MulAut W) ((k : MulAut W) x) :=
      map_prod (k' : MulAut W) _ _
    rw [this]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨k', hk'⟩ : ↥K)) _ _ fun k => ?_
    rfl
  have hprod : ∏ k : ↥K, f k = 1 := by
    have : ∏ k : ↥K, f k = π (∏ k : ↥K, (k : MulAut W) x) := (map_prod π _ _).symm
    rw [this, hN, map_one]
  have hpair : ∏ k ∈ (Finset.univ : Finset ↥K).erase 1, f k = 1 := by
    refine Finset.prod_involution (fun k _ => k⁻¹) ?_ ?_ ?_ ?_
    · intro k _
      have hak : a * (k : MulAut W) = (k : MulAut W)⁻¹ * a := by
        have := hinv k k.2
        calc a * (k : MulAut W) = (a * (k : MulAut W) * a⁻¹) * a := by group
          _ = (k : MulAut W)⁻¹ * a := by rw [this]
      have h1 : a ((k : MulAut W) x) = ((k⁻¹ : ↥K) : MulAut W) x := by
        have : a ((k : MulAut W) x) = (a * (k : MulAut W)) x := rfl
        rw [this, hak]
        change ((k : MulAut W)⁻¹ * a) x = _
        rw [MulAut.mul_apply, hax]
        rfl
      have h2 : (k : MulAut W) x * ((k⁻¹ : ↥K) : MulAut W) x = phi a ((k : MulAut W) x) := by
        rw [← h1, phi_apply]
        have := hW ((k : MulAut W) x)
        calc (k : MulAut W) x * a ((k : MulAut W) x) = a ((k : MulAut W) x) * (k : MulAut W) x := mul_comm _ _
          _ = a ((k : MulAut W) x) * ((k : MulAut W) x)⁻¹ * ((k : MulAut W) x * (k : MulAut W) x) := by group
          _ = a ((k : MulAut W) x) * ((k : MulAut W) x)⁻¹ := by rw [this, mul_one]
      have hmem : (k : MulAut W) x * ((k⁻¹ : ↥K) : MulAut W) x ∈ R := by
        rw [h2]
        exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩
      show f k * f k⁻¹ = 1
      simp only [f, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    · intro k hk _
      have hk1 : k ≠ 1 := (Finset.mem_erase.1 hk).1
      intro hkk
      have hk2 : k * k = 1 := by
        calc k * k = k * k⁻¹ := by rw [hkk]
          _ = 1 := mul_inv_cancel k
      have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hk2)
      have hodd' : Odd (orderOf k) := hodd.of_dvd_nat (orderOf_dvd_natCard k)
      have h1 : orderOf k = 1 := by
        have : orderOf k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        have hpos := orderOf_pos k
        interval_cases h : orderOf k
        · rfl
        · exact absurd hodd' (by decide)
      exact hk1 (orderOf_eq_one_iff.1 h1)
    · intro k hk
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_erase.1 hk).1 (inv_eq_one.1 h)
    · intro k _
      exact inv_inv k
  have h1 : f 1 = 1 := by
    have := Finset.mul_prod_erase (Finset.univ : Finset ↥K) f (Finset.mem_univ 1)
    rw [hpair, mul_one] at this
    exact this.trans hprod
  have : π x = 1 := by
    have : f 1 = π x := by simp [f]
    rw [← this]
    exact h1
  exact (QuotientGroup.eq_one_iff _).1 this

theorem card_eq_fix_mul_range [Finite W] (a : MulAut W) :
    Nat.card W = Nat.card ↥(fixSub a) * Nat.card ↥((⊤ : Subgroup W).map (phi a)) := by
  have h := Subgroup.card_ker_mul_card_range (phi a)
  have hker : (phi a).ker = fixSub a := by
    ext x
    rw [MonoidHom.mem_ker, phi_eq_one_iff]
    rfl
  rw [hker, MonoidHom.range_eq_map] at h
  exact h.symm

theorem card_le_sq_of_inverting [Finite W] (hW : ∀ w : W, w * w = 1) {K : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card ↥K)) {a : MulAut W}
    (hinv : ∀ k ∈ K, a * k * a⁻¹ = k⁻¹) (hfix : ∀ x : W, (∀ k ∈ K, k x = x) → x = 1) :
    Nat.card W ≤ Nat.card ↥((⊤ : Subgroup W).map (phi a)) ^ 2 := by
  rw [card_eq_fix_mul_range a, pow_two]
  exact Nat.mul_le_mul_right _
    (Subgroup.card_le_of_le (fixSub_le_range_phi hW hodd hinv hfix))

end Inverting

section Involution

variable {Γ : Type*} [Group Γ]

theorem eq_inv_of_forall_ne [Finite Γ] {K : Subgroup Γ} {a : Γ} (ha : a * a = 1)
    (hK : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hfix : ∀ k ∈ K, a * k * a⁻¹ = k → k = 1) :
    ∀ k ∈ K, a * k * a⁻¹ = k⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let ψ : ↥K → ↥K := fun k => ⟨(k : Γ)⁻¹ * (a * k * a⁻¹), K.mul_mem (K.inv_mem k.2) (hK k k.2)⟩
  have hinj : Function.Injective ψ := by
    intro k l hkl
    have h1 : (k : Γ)⁻¹ * (a * k * a⁻¹) = (l : Γ)⁻¹ * (a * l * a⁻¹) := congrArg Subtype.val hkl
    have h2 : a * ((l : Γ) * (k : Γ)⁻¹) * a⁻¹ = (l : Γ) * (k : Γ)⁻¹ := by
      calc a * ((l : Γ) * (k : Γ)⁻¹) * a⁻¹ = (a * l * a⁻¹) * (a * k * a⁻¹)⁻¹ := by group
        _ = (l : Γ) * (k : Γ)⁻¹ := by
          have e1 : a * (l : Γ) * a⁻¹ = (l : Γ) * ((k : Γ)⁻¹ * (a * k * a⁻¹)) := by
            calc a * (l : Γ) * a⁻¹ = (l : Γ) * ((l : Γ)⁻¹ * (a * l * a⁻¹)) := by group
              _ = _ := by rw [← h1]
          rw [e1]
          group
    have h3 : (l : Γ) * (k : Γ)⁻¹ = 1 := hfix _ (K.mul_mem l.2 (K.inv_mem k.2)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h3).symm
  have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.1 hinj
  intro k hk
  obtain ⟨j, hj⟩ := hsurj ⟨k, hk⟩
  have hjk : (j : Γ)⁻¹ * (a * j * a⁻¹) = k := congrArg Subtype.val hj
  rw [← hjk]
  set j' : Γ := (j : Γ) with hj'
  have ha2' : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ha, inv_one]
  have : a * (j'⁻¹ * (a * j' * a⁻¹)) * a⁻¹ = (a * j'⁻¹ * a⁻¹) * ((a * a) * j' * (a⁻¹ * a⁻¹)) := by
    group
  rw [this, ha, ha2']
  group

end Involution

end S153E58

end CFSG.Quasithin
