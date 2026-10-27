module

public import CFSG.Quasithin.Vol2.Ch10SecB3L32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

namespace L32

theorem card_Pa' : Nat.card Pa = 24 := by
  rw [Nat.card_eq_fintype_card, ← card_Pa]
  exact Fintype.card_subtype (· ∈ Pa)

theorem card_Pb' : Nat.card Pb = 24 := by
  rw [Nat.card_eq_fintype_card, ← card_Pb]
  exact Fintype.card_subtype (· ∈ Pb)

theorem card_par {A : Subgroup Γ} (hA : A = Pa ∨ A = Pb) : Nat.card A = 24 := by
  rcases hA with rfl | rfl
  · exact card_Pa'
  · exact card_Pb'

theorem relIndex_par {A : Subgroup Γ} (hA : A = Pa ∨ A = Pb) :
    (U3.prod U3).relIndex (A.prod A) = 9 := by
  have hU : U3 ≤ A := by
    rcases hA with rfl | rfl
    · exact u3_le_pa
    · exact u3_le_pb
  have h := Subgroup.relIndex_mul_card (U3.prod U3) (A.prod A)
  rw [inf_of_le_left (Subgroup.prod_mono hU hU), card_prod_self, card_prod_self, card_U3,
    card_par hA] at h
  omega

end L32

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem preIn_subgroupOf {X : Subgroup G} {Q : Type*} [Group Q] (Ψ : ↥X →* Q)
    (C : Subgroup Q) : (preIn Ψ C).subgroupOf X = C.comap Ψ :=
  Subgroup.comap_map_eq_self_of_injective X.subtype_injective _

theorem relIndex_T0_preIn {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
    {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ} (hT : quasithinIsSylowTwo T)
    (hC : L0CoordG T L t Ψ α ψ) {A : Subgroup L32.Γ} (hA : A = L32.Pa ∨ A = L32.Pb) :
    (T0 T L).relIndex (preIn Ψ (A.prod A)) = 9 := by
  rw [← Subgroup.relIndex_subgroupOf (preIn_le Ψ _), T0_eq_preIn_gen hT hC, preIn_subgroupOf,
    preIn_subgroupOf, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hC.surj]
  exact L32.relIndex_par hA

namespace Ctx3

variable {H B : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {α : MulAut L32.Γ}
  {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ}

theorem T_le (c : Ctx3 T L I H B t Ψ α ψ) : T ≤ H ⊓ fsuM T L :=
  le_inf c.hH.1.1 (SecA.le_fsuM T L)

theorem relIndex_two_pow (c : Ctx3 T L I H B t Ψ α ψ) {X : Subgroup G} (hBX : B ≤ X)
    (hX : X ≤ H ⊓ fsuM T L) : ∃ j : ℕ, B.relIndex X = 2 ^ j := by
  obtain ⟨k, hk⟩ := c.hB.2.2
  have e := Subgroup.relIndex_mul_relIndex B X (H ⊓ fsuM T L) hBX hX
  rw [hk] at e
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ e)
  exact ⟨j, hj⟩

theorem card_eq_nine (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) : Nat.card B = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hY, -⟩ := c.classify' hB1
  have hBY : B ≤ preIn Ψ (A.prod A) := hY ▸ c.le_Y
  have hT0Y : T0 T L ≤ preIn Ψ (A.prod A) := hY ▸ inf_le_inf_right _ c.T_le
  have e1 := Subgroup.relIndex_mul_card (T0 T L) (preIn Ψ (A.prod A))
  rw [inf_of_le_left hT0Y, relIndex_T0_preIn c.hyp.fsu.sylow c.hC hA] at e1
  obtain ⟨j, hj⟩ := c.relIndex_two_pow hBY (hY ▸ inf_le_left)
  have e2 := Subgroup.relIndex_mul_card B (preIn Ψ (A.prod A))
  rw [inf_of_le_left hBY, hj] at e2
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (c.hyp.fsu.sylow.1.to_le (inf_le_left : T0 T L ≤ T))
  rw [hm] at e1
  have hodd := c.hB.2.1
  have hcop : Nat.Coprime (Nat.card B) 2 := (Nat.coprime_two_left.mpr hodd).symm
  have h1 : Nat.card B ∣ 9 := by
    have : Nat.card B ∣ 9 * 2 ^ m := ⟨2 ^ j, by rw [e1, ← e2, mul_comm]⟩
    exact (Nat.Coprime.pow_right m hcop).dvd_of_dvd_mul_right this
  have h2 : 9 ∣ Nat.card B := by
    have : 9 ∣ 2 ^ j * Nat.card B := ⟨2 ^ m, by rw [e2, ← e1]⟩
    exact (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_left this
  exact Nat.dvd_antisymm h1 h2

theorem injOn (c : Ctx3 T L I H B t Ψ α ψ) {b : G} (hb : b ∈ B) (hb0 : b ∈ fsuL0 T L)
    (h : Ψ ⟨b, hb0⟩ = 1) : b = 1 :=
  eq_one_of_mem_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ((c.hC.ker _).mp h)
    (c.odd_of_mem hb)

theorem card_img (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) : Nat.card (imgIn Ψ B) = 9 := by
  have hBL0 : B ≤ fsuL0 T L := fun b hb => (c.le_Y hb).2
  have hinj : Function.Injective (Ψ.comp (B.subgroupOf (fsuL0 T L)).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨b, hb0⟩, hbB⟩ hk
    have h1 := c.injOn (Subgroup.mem_subgroupOf.mp hbB) hb0 hk
    exact Subtype.ext (Subtype.ext h1)
  have himg : imgIn Ψ B = (Ψ.comp (B.subgroupOf (fsuL0 T L)).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [himg, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL0).toEquiv, c.card_eq_nine hB1]

theorem img_eq_prod (c : Ctx3 T L I H B t Ψ α ψ) (hB1 : B ≠ ⊥) :
    ∃ A : Subgroup L32.Γ, (A = L32.Pa ∨ A = L32.Pb) ∧
      (H ⊓ fsuM T L) ⊓ fsuL0 T L = preIn Ψ (A.prod A) ∧ A.map α.toMonoidHom = A ∧
      ∃ P₁ P₂ : Subgroup L32.Γ, imgIn Ψ B = P₁.prod P₂ ∧ Nat.card P₁ = 3 ∧ Nat.card P₂ = 3 ∧
        P₁ ≤ A ∧ P₂ ≤ A := by
  obtain ⟨A, hA, hY, hαA⟩ := c.classify' hB1
  refine ⟨A, hA, hY, hαA, ?_⟩
  set P₁ := (imgIn Ψ B).map (MonoidHom.fst L32.Γ L32.Γ)
  set P₂ := (imgIn Ψ B).map (MonoidHom.snd L32.Γ L32.Γ)
  have hle : imgIn Ψ B ≤ P₁.prod P₂ := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have hBA : imgIn Ψ B ≤ A.prod A := by
    rw [← imgIn_preIn c.hC.surj (A.prod A), ← hY]
    exact imgIn_mono Ψ c.le_Y
  have hP₁ : P₁ ≤ A := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hBA hp).1
  have hP₂ : P₂ ≤ A := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hBA hp).2
  have h9 := c.card_img hB1
  have hd : ∀ P : Subgroup L32.Γ, P ≤ A → Nat.card P ∣ 9 → Nat.card P ∣ 3 := by
    intro P hPA hP9
    have h24 : Nat.card P ∣ 24 := L32.card_par hA ▸ Subgroup.card_dvd_of_le hPA
    exact (Nat.dvd_gcd hP9 h24).trans (by norm_num)
  have h₁ := hd P₁ hP₁ (h9 ▸ Subgroup.card_map_dvd _ _)
  have h₂ := hd P₂ hP₂ (h9 ▸ Subgroup.card_map_dvd _ _)
  have hcard : 9 ≤ Nat.card P₁ * Nat.card P₂ := by
    rw [← Nat.card_prod, ← Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, ← h9]
    exact Subgroup.card_le_of_le hle
  have hc₁ : Nat.card P₁ = 3 := by
    have h2 := Nat.le_of_dvd (by norm_num) h₂
    rcases (Nat.dvd_prime Nat.prime_three).mp h₁ with h | h
    · rw [h] at hcard; omega
    · exact h
  have hc₂ : Nat.card P₂ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h₂ with h | h
    · rw [h, hc₁] at hcard; omega
    · exact h
  refine ⟨P₁, P₂, Subgroup.eq_of_le_of_card_ge hle ?_, hc₁, hc₂, hP₁, hP₂⟩
  rw [Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, Nat.card_prod, hc₁, hc₂, h9]

end Ctx3

end CFSG.Quasithin.Vol2.Ch10.SecB
