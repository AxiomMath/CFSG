module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem u43_exists_sylow_of_card_nine {H : Type} [Group H] [Finite H] (hH : Nat.card H = 1152)
    (A : Subgroup H) (hA : Nat.card A = 9) : ∃ P : Sylow 3 H, (P : Subgroup H) = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : (Nat.card H).factorization 3 = 2 := by
    rw [hH, Nat.factorization_def _ Nat.prime_three,
      show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  exact ⟨Sylow.ofCard A (by rw [hA, hf]; norm_num), rfl⟩

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem exists_conj_T_T1 : ∃ g : G, ∀ t ∈ S.Tg, g * t * g⁻¹ ∈ S.T1 := by
  obtain ⟨k, hk⟩ := S.exists_conj_u
  set Hu : Subgroup G := Hz (S.u : G) with hHu
  have hHuc : Nat.card Hu = 1152 := S.card_Hz_u
  set A₁ : Subgroup G := S.Tg.map (MulAut.conj k).toMonoidHom with hA₁
  have hA₁le : A₁ ≤ Hu := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hHu, Subgroup.mem_centralizer_singleton_iff, ← hk]
    have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (S.Tg_le_Hz ht)
    show (MulAut.conj k) t * (k * z * k⁻¹) = (k * z * k⁻¹) * (MulAut.conj k) t
    simp only [MulAut.conj_apply]
    calc k * t * k⁻¹ * (k * z * k⁻¹) = k * (t * z) * k⁻¹ := by group
      _ = k * (z * t) * k⁻¹ := by rw [htz]
      _ = (k * z * k⁻¹) * (k * t * k⁻¹) := by group
  have hT₁le : S.T1 ≤ Hu := inf_le_right
  have hA₁c : Nat.card (A₁.subgroupOf Hu) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁le).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj k).injective, S.card_Tg]
  have hT₁c : Nat.card (S.T1.subgroupOf Hu) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁le).toEquiv, S.card_T1]
  obtain ⟨PA, hPA⟩ := u43_exists_sylow_of_card_nine hHuc _ hA₁c
  obtain ⟨PT, hPT⟩ := u43_exists_sylow_of_card_nine hHuc _ hT₁c
  obtain ⟨h, hh⟩ := exists_conj_sylow PA PT
  refine ⟨(h : G) * k, fun t ht => ?_⟩
  have hat : k * t * k⁻¹ ∈ A₁ := ⟨t, ht, rfl⟩
  set x : ↥Hu := ⟨k * t * k⁻¹, hA₁le hat⟩ with hx
  have h1 : x ∈ (PA : Subgroup ↥Hu) := by
    rw [hPA]
    exact hat
  have e1 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  have h2 := (hh (h * x * h⁻¹)).mpr (by rw [e1]; exact h1)
  rw [hPT] at h2
  have h3 : (h : G) * (k * t * k⁻¹) * (h : G)⁻¹ ∈ S.T1 := h2
  have e : (h : G) * k * t * ((h : G) * k)⁻¹ = (h : G) * (k * t * k⁻¹) * (h : G)⁻¹ := by group
  rw [e]
  exact h3

end JWSetup

end CFSG.Quasithin.H13.U43
