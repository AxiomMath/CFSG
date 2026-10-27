module

public import CFSG.Quasithin.H13.A6S1372L74m
public import CFSG.Quasithin.EmptyFaithful.S1417Blocks
public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin

namespace A6L74

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem mem_zpowers_of_mem_zpowers {d w : Γ} (hd : d ^ 3 = 1) (hw : w ∈ Subgroup.zpowers d)
    (hw1 : w ≠ 1) : d ∈ Subgroup.zpowers w := by
  rcases eq_or_of_mem_zpowers_three hd hw with h | h | h
  · exact absurd h hw1
  · rw [h]
    exact Subgroup.mem_zpowers d
  · rw [h, Subgroup.zpowers_inv]
    exact Subgroup.mem_zpowers d

omit [Finite Γ] in
theorem eq_one_of_central_of_equiv {L : Subgroup Γ} (e : ↥L ≃* S1417.SL2) {z : Γ} (hz : z ∈ L)
    (hc : ∀ y ∈ L, z * y = y * z) : z = 1 := by
  have h1 : e ⟨z, hz⟩ = 1 := by
    refine S1417.SL2_center _ fun t => ?_
    obtain ⟨y, rfl⟩ := e.surjective t
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2)
  have h2 : (⟨z, hz⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem comm_of_one_block {K L : Subgroup Γ} (e : ↥L ≃* S1417.SL2)
    (hK3 : ∀ k ∈ K, k ^ 3 = 1) (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK9 : Nat.card K = 9)
    (hLK : ∀ y ∈ L, y ^ 3 = 1 → y ∈ K) (hKL : ∀ k ∈ K, ∀ y ∈ L, k * y * k⁻¹ ∈ L) {σ : Γ}
    (hσ : σ ^ 3 = 1) (hσK : ∀ k ∈ K, σ * k * σ⁻¹ ∈ K) (hσL : ∀ y ∈ L, σ * y * σ⁻¹ ∈ L) :
    ∀ k ∈ K, σ * k = k * σ := by
  obtain ⟨d, hdL, hdK, hd3, hd1, hdD⟩ := exists_three_of_equiv e hK3 hLK
  obtain ⟨t₀, ht₀2, ht₀1⟩ := SL2_exists_two
  set t : Γ := ((e.symm t₀ : ↥L) : Γ) with htdef
  have htL : t ∈ L := (e.symm t₀).2
  have ht2 : t ^ 2 = 1 := by
    have h : (e.symm t₀) ^ 2 = 1 := by rw [← map_pow, ht₀2, map_one]
    simpa [htdef] using congrArg Subtype.val h
  have hx3 : e ⟨d, hdL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hx1 : e ⟨d, hdL⟩ ≠ 1 := by
    intro h
    apply hd1
    have : (⟨d, hdL⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val this
  have het : e ⟨t, htL⟩ = t₀ := by
    have : (⟨t, htL⟩ : ↥L) = e.symm t₀ := rfl
    rw [this, e.apply_symm_apply]
  have hgen : ∀ y ∈ L, y = 1 ∨ y = d ∨ y = d⁻¹ ∨ y = t ∨ y = d * t ∨ y = d⁻¹ * t := by
    intro y hy
    have h := SL2_gen t₀ (e ⟨d, hdL⟩) (e ⟨y, hy⟩) ht₀2 ht₀1 hx3 hx1
    rw [← het] at h
    have key : ∀ a : ↥L, e ⟨y, hy⟩ = e a → y = (a : Γ) := fun a h' => by
      simpa using congrArg Subtype.val (e.injective h')
    rcases h with h | h | h | h | h | h
    · left; simpa using key 1 (by rw [h, map_one])
    · right; left; exact key ⟨d, hdL⟩ h
    · right; right; left; simpa using key ⟨d, hdL⟩⁻¹ (by rw [h, map_inv])
    · right; right; right; left; exact key ⟨t, htL⟩ h
    · right; right; right; right; left; simpa using key (⟨d, hdL⟩ * ⟨t, htL⟩) (by rw [h, map_mul])
    · right; right; right; right; right
      simpa using key (⟨d, hdL⟩⁻¹ * ⟨t, htL⟩) (by rw [h, map_mul, map_inv])
  have hcentL : ∀ c : Γ, c * d = d * c → c * t = t * c → ∀ y ∈ L, c * y = y * c := by
    intro c hcd hct y hy
    have hcdi : c * d⁻¹ = d⁻¹ * c := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hcd, ← mul_assoc, inv_mul_cancel, one_mul]
    rcases hgen y hy with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · exact hcd
    · exact hcdi
    · exact hct
    · rw [← mul_assoc, hcd, mul_assoc, hct, ← mul_assoc]
    · rw [← mul_assoc, hcdi, mul_assoc, hct, ← mul_assoc]
  have hσd : σ * d * σ⁻¹ = d := by
    refine conj_eq_of_mem_zpowers hσ hd3 hd1 ?_
    rcases hdD _ (hσL d hdL) (hσK d hdK) with h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers d
    · rw [h]; exact (Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d)
  obtain ⟨k₀, hk₀K, hk₀d⟩ : ∃ k₀ ∈ K, k₀ ∉ Subgroup.zpowers d := by
    by_contra h
    push Not at h
    have hle : K ≤ Subgroup.zpowers d := fun k hk => h k hk
    have h1 := Subgroup.card_le_of_le hle
    rw [hK9, Nat.card_zpowers, orderOf_eq_prime hd3 hd1] at h1
    exact absurd h1 (by norm_num)
  have hτL : k₀ * t * k₀⁻¹ ∈ L := hKL k₀ hk₀K t htL
  have hτ2 : (k₀ * t * k₀⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ht2, mul_one, mul_inv_cancel]
  have hτ1 : k₀ * t * k₀⁻¹ ≠ 1 := by
    intro h
    apply ht₀1
    have ht1 : t = 1 := by
      have e1 : t = k₀⁻¹ * (k₀ * t * k₀⁻¹) * k₀ := by group
      rw [e1, h]
      group
    rw [← het]
    have : (⟨t, htL⟩ : ↥L) = 1 := Subtype.ext ht1
    rw [this, map_one]
  obtain ⟨c, hc, hcτ⟩ : ∃ c ∈ Subgroup.zpowers d, k₀ * t * k₀⁻¹ = c * t * c⁻¹ := by
    have hτ2' : e ⟨_, hτL⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨_, hτL⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hτ2)
      rw [this, map_one]
    have hτ1' : e ⟨_, hτL⟩ ≠ 1 := by
      intro h
      apply hτ1
      have : (⟨_, hτL⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
      simpa using congrArg Subtype.val this
    rcases SL2_inv_conj t₀ (e ⟨_, hτL⟩) (e ⟨d, hdL⟩) ⟨ht₀2, ht₀1, hτ2', hτ1', hx3, hx1⟩ with
      h | h | h
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [← het] at h
      have := congrArg Subtype.val (e.injective h)
      simpa using this
    · refine ⟨d, Subgroup.mem_zpowers d, ?_⟩
      rw [← het, ← map_inv, ← map_mul, ← map_mul] at h
      have := congrArg Subtype.val (e.injective h)
      simpa using this
    · refine ⟨d⁻¹, (Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d), ?_⟩
      rw [← het, ← map_inv, ← map_mul, ← map_mul] at h
      have := congrArg Subtype.val (e.injective h)
      simpa using this
  have hcK : c ∈ K := (Subgroup.zpowers_le.2 hdK) hc
  set e₀ : Γ := c⁻¹ * k₀ with he₀
  have he₀K : e₀ ∈ K := K.mul_mem (K.inv_mem hcK) hk₀K
  have he₀t : e₀ * t = t * e₀ := by
    rw [← mul_inv_eq_iff_eq_mul]
    calc e₀ * t * e₀⁻¹ = c⁻¹ * (k₀ * t * k₀⁻¹) * c := by rw [he₀]; group
      _ = t := by rw [hcτ]; group
  have he₀C : ∀ y ∈ L, e₀ * y = y * e₀ := hcentL e₀ (hKc e₀ he₀K d hdK) he₀t
  have he₀d : e₀ ∉ Subgroup.zpowers d := by
    intro h
    apply hk₀d
    have e1 : k₀ = c * e₀ := by rw [he₀]; group
    rw [e1]
    exact (Subgroup.zpowers d).mul_mem hc h
  have he₀1 : e₀ ≠ 1 := fun h => he₀d (h ▸ Subgroup.one_mem _)
  have hKde : Subgroup.zpowers d ⊔ Subgroup.zpowers e₀ = K :=
    sup_zpowers_eq_of_card hK9 hdK he₀K hd3 hd1 he₀d
  have hσe : σ * e₀ * σ⁻¹ = e₀ := by
    refine conj_eq_of_mem_zpowers hσ (hK3 e₀ he₀K) he₀1 ?_
    have hmem : σ * e₀ * σ⁻¹ ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers e₀ := by
      rw [hKde]; exact hσK e₀ he₀K
    obtain ⟨u, hu, v, hv, huv⟩ := S1417.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hKc a ((Subgroup.zpowers_le.2 hdK) ha) b
        ((Subgroup.zpowers_le.2 he₀K) hb)) hmem
    have hσeC : ∀ y ∈ L, σ * e₀ * σ⁻¹ * y = y * (σ * e₀ * σ⁻¹) := by
      intro y hy
      have hy' : σ⁻¹ * y * σ ∈ L := by
        have e1 : σ⁻¹ * y * σ = σ * (σ * y * σ⁻¹) * σ⁻¹ := by
          have hσi : σ⁻¹ = σ * σ := by
            rw [inv_eq_iff_mul_eq_one, ← pow_three, hσ]
          calc σ⁻¹ * y * σ = (σ * σ) * y * σ := by rw [hσi]
            _ = σ * (σ * y * σ⁻¹) * σ⁻¹ * (σ * σ * σ) := by
              simp only [mul_assoc, inv_mul_cancel_left]
            _ = σ * (σ * y * σ⁻¹) * σ⁻¹ := by rw [← pow_three', hσ, mul_one]
        rw [e1]
        exact hσL _ (hσL y hy)
      have h1 := he₀C _ hy'
      calc σ * e₀ * σ⁻¹ * y = σ * (e₀ * (σ⁻¹ * y * σ)) * σ⁻¹ := by group
        _ = σ * ((σ⁻¹ * y * σ) * e₀) * σ⁻¹ := by rw [h1]
        _ = y * (σ * e₀ * σ⁻¹) := by group
    have hvC : ∀ y ∈ L, v * y = y * v := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      intro y hy
      exact (Commute.zpow_left (he₀C y hy) m)
    have huC : ∀ y ∈ L, u * y = y * u := by
      intro y hy
      have e1 : u = (σ * e₀ * σ⁻¹) * v⁻¹ := by rw [← huv]; group
      rw [e1]
      have h1 := hσeC y hy
      have h2 : v⁻¹ * y = y * v⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hvC y hy, mul_inv_cancel_right]
      calc σ * e₀ * σ⁻¹ * v⁻¹ * y = σ * e₀ * σ⁻¹ * (v⁻¹ * y) := by group
        _ = σ * e₀ * σ⁻¹ * (y * v⁻¹) := by rw [h2]
        _ = (σ * e₀ * σ⁻¹ * y) * v⁻¹ := by group
        _ = y * (σ * e₀ * σ⁻¹) * v⁻¹ := by rw [h1]
        _ = y * (σ * e₀ * σ⁻¹ * v⁻¹) := by group
    have huL : u ∈ L := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact L.zpow_mem hdL m
    have hu1 : u = 1 := eq_one_of_central_of_equiv e huL huC
    rw [← huv, hu1, one_mul]
    exact hv
  have hle : K ≤ Subgroup.centralizer ({σ} : Set Γ) := by
    rw [← hKde]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hσd).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hσe).symm
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm

end A6L74

end CFSG.Quasithin.H13.A6
