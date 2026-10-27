module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre41c
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42d
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43b
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43j

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem pow_conj_mem {Y : Subgroup G} {f : G} (hf : ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) :
    ∀ m : ℕ, ∀ y ∈ Y, f ^ m * y * (f ^ m)⁻¹ ∈ Y := by
  intro m
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
    intro y hy
    have e : f ^ (m + 1) * y * (f ^ (m + 1))⁻¹ = f * (f ^ m * y * (f ^ m)⁻¹) * f⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact hf _ (ih y hy)

theorem pow_mul_mem {Y : Subgroup G} {f : G} (hf : ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) {y : G}
    (hy : y ∈ Y) : ∀ m : ℕ, ∃ y' ∈ Y, (y * f) ^ m = y' * f ^ m := by
  intro m
  induction m with
  | zero => exact ⟨1, Y.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨y', hy', hm⟩ := ih
    refine ⟨y' * (f ^ m * y * (f ^ m)⁻¹), Y.mul_mem hy' (pow_conj_mem hf m y hy), ?_⟩
    rw [pow_succ, hm, pow_succ]
    group

theorem two_pow_sq_mod_three (k : ℕ) : (2 ^ k * 2 ^ k) % 3 = 1 := by
  rw [← mul_pow]
  norm_num [Nat.pow_mod]

theorem W_comm_E (h23 : FF84_2_3) (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) (hC : CommTheta b b₁ b₂) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hinv : ∀ t ∈ T, ∀ β ∈ B, β * t * β⁻¹ ∈ T) {w : G} (hwT : w ∈ T)
    (hwD : w ∈ Cen (b * b₁)) :
    ∀ e ∈ Subgroup.closure ({b, b₁} : Set G), w * e = e * w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = Cen (b * b₁) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = Opp 3 D := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = Subgroup.closure ({b, b₁} : Set G) := ⟨_, rfl⟩
  rw [← hD] at hwD
  rw [← hE]
  have hBD : B ≤ D := hD ▸ B_le_cen_bb₁ h
  have hED : E ≤ D := fun e he => hBD (E_le_B h (hE ▸ he))
  have hYD : Y ≤ D := hY ▸ FF79.L14.Opp_le 3 D
  have hYn : ∀ g ∈ D, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy =>
    hY ▸ FF79.L14.Opp_conj_mem hg (hY ▸ hy)
  have hTY2 : IsPGroup 2 ↥(T ⊓ Y) := hT2.to_inf_left
  have hTY : T ⊓ Y ≤ CenS B := by
    refine two_group_cenS hA h hTY2 ?_ ?_ ?_
    · intro t ht β hβ
      exact ⟨hinv t ht.1 β hβ, hYn β (hBD hβ) t ht.2⟩
    · intro t ht
      have := hYD ht.2
      rw [hD] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    · intro t ht
      have hb₂B := mem_b₂ h
      have hc : b₂ * t * b₂⁻¹ * t⁻¹ ∈ Theta D := hD ▸ hC t (hD ▸ hY ▸ ht.2)
      have hin : b₂ * t * b₂⁻¹ * t⁻¹ ∈ T ⊓ Y :=
        ⟨T.mul_mem (hinv t ht.1 b₂ hb₂B) (T.inv_mem ht.1),
          Y.mul_mem (hYn b₂ (hBD hb₂B) t ht.2) (Y.inv_mem ht.2)⟩
      have hodd : Odd (Nat.card (Theta D)) := hD ▸ S42_theta_odd hA h
      have h1 := eq_one_of_two_group_odd hTY2 hodd hin hc
      exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  intro e he
  have heB : e ∈ B := E_le_B h (hE ▸ he)
  have he3 : e ^ 3 = 1 := pow3_of_mem h heB
  have hfirst := S41_first h23 h hA w (hD ▸ hwD)
  rw [← hD, ← hY, ← hE] at hfirst
  obtain ⟨y, hy, n, hn, hwyn⟩ := hfirst
  obtain ⟨hnD, hnN⟩ := Subgroup.mem_inf.1 hn
  have he' : n * e * n⁻¹ ∈ E := by
    have := (Subgroup.mem_normalizer_iff.1 hnN e).1 (hE ▸ he)
    exact hE ▸ this
  obtain ⟨e', he'd⟩ : ∃ e' : G, e' = n * e * n⁻¹ := ⟨_, rfl⟩
  rw [← he'd] at he'
  obtain ⟨f, hfd⟩ : ∃ f : G, f = e' * e⁻¹ := ⟨_, rfl⟩
  have hfE : f ∈ E := hfd ▸ E.mul_mem he' (E.inv_mem he)
  obtain ⟨u, hu⟩ : ∃ u : G, u = w * e * w⁻¹ * e⁻¹ := ⟨_, rfl⟩
  have huT : u ∈ T := by
    have h1 := T.mul_mem hwT (hinv w⁻¹ (T.inv_mem hwT) e heB)
    rwa [show w * (e * w⁻¹ * e⁻¹) = u by rw [hu]; group] at h1
  have hu2 : ∃ k : ℕ, u ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hT2 ⟨u, huT⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨k, hk⟩ := hu2
  have huy : u = (y * (e' * y⁻¹ * e'⁻¹)) * f := by
    rw [hu, hwyn, hfd, he'd]; group
  have hy₁ : y * (e' * y⁻¹ * e'⁻¹) ∈ Y :=
    Y.mul_mem hy (hYn e' (hED he') y⁻¹ (Y.inv_mem hy))
  have hfn : ∀ z ∈ Y, f * z * f⁻¹ ∈ Y := fun z hz => hYn f (hED hfE) z hz
  obtain ⟨y', hy', hpow⟩ := pow_mul_mem hfn hy₁ (2 ^ k)
  have hfk : f ^ 2 ^ k ∈ Y := by
    rw [← huy, hk] at hpow
    have : f ^ 2 ^ k = y'⁻¹ := by
      have := congrArg (fun x => y'⁻¹ * x) hpow
      simpa using this.symm
    rw [this]; exact Y.inv_mem hy'
  have hf3 : f ^ 3 = 1 := pow3_of_mem h (E_le_B h (hE ▸ hfE))
  have hfY : f ∈ Y := by
    have e1 : f = (f ^ 2 ^ k) ^ 2 ^ k := by
      rw [← pow_mul, pow_eq_pow_mod _ hf3, two_pow_sq_mod_three, pow_one]
    rw [e1]; exact Y.pow_mem hfk _
  have huY : u ∈ Y := huy ▸ Y.mul_mem hy₁ hfY
  have huC : e * u = u * e := Subgroup.mem_centralizer_iff.1 (hTY ⟨huT, huY⟩) e heB
  have hu3 : u ^ 3 = 1 := by
    have hcube : (w * e * w⁻¹) ^ 3 = 1 := by rw [conj_pow, he3]; group
    have e1 : w * e * w⁻¹ = u * e := by rw [hu]; group
    rw [e1, (show Commute u e from huC.symm).mul_pow, he3, mul_one] at hcube
    exact hcube
  have hu1 : u = 1 := by
    have d1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have d2 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop3 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left d1 hcop3) d2)
  rw [hu1] at hu
  have := mul_inv_eq_one.1 hu.symm
  exact (mul_inv_eq_iff_eq_mul.1 this)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
