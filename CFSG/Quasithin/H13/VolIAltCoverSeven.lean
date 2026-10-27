module

public import CFSG.Quasithin.H13.VolIAltCoverSevenCosets

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

theorem card_sup_le_mul {W : Type*} [CommGroup W] [Finite W] (A B : Subgroup W) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hN : A ≤ normalizer (B : Set W) := by
    rw [normalizer_eq_top]
    exact le_top
  rw [← card_sup_mul_card_inf hN]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem card_dnQuot_seven : Nat.card (DnQuot 7) = 64 := by
  have hker : zpowers (allOnes 7) ⊓ coreMod 7 = ⊥ := by
    have h2 : orderOf (allOnes 7) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    rw [mem_zpowers_iff_mem_range_orderOf, h2] at hx1
    simp only [Finset.mem_image, Finset.mem_range] at hx1
    obtain ⟨n, hn, rfl⟩ := hx1
    interval_cases n
    · simp
    · exact absurd (by simpa using hx2) allOnes_seven_not_mem
  have e : (zpowers (allOnes 7) ⊓ coreMod 7).subgroupOf (coreMod 7) = ⊥ := by
    rw [hker, bot_subgroupOf]
  show Nat.card (↥(coreMod 7) ⧸ (zpowers (allOnes 7) ⊓ coreMod 7).subgroupOf (coreMod 7)) = 64
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq e).trans
    QuotientGroup.quotientBot).toEquiv, card_coreMod_seven]

theorem altNaturalCoverSeven_holds : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
      AlternatingNatural H ⊤ Z 7 → Z = ⊥ := by
  intro W _ _ hW2 H Z hZ hcomm hnat
  obtain ⟨π₀, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  let π : ↥(alternatingGroup (Fin 7)) →* ↥H := π₀
  let ρ : ↥(alternatingGroup (Fin 7)) →* MulAut W := H.subtype.comp π
  let M : Subgroup W := ((commMap (ρ a7c012)).range ⊔ (commMap (ρ a7c234)).range) ⊔
    (commMap (ρ a7c456)).range
  let P : ↥(alternatingGroup (Fin 7)) → Prop := fun σ => ∀ w, ρ σ w * w⁻¹ ∈ M
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb w
    have e : ρ (a * b) w * w⁻¹ = (ρ a (ρ b w) * (ρ b w)⁻¹) * (ρ b w * w⁻¹) := by
      rw [map_mul, MulAut.mul_apply]
      group
    rw [e]
    exact mul_mem (ha _) (hb w)
  have h₁ : P a7c012 := fun w => mem_sup_left (mem_sup_left ⟨w, rfl⟩)
  have h₂ : P a7c234 := fun w => mem_sup_left (mem_sup_right ⟨w, rfl⟩)
  have h₃ : P a7c456 := fun w => mem_sup_right ⟨w, rfl⟩
  have hA5 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 5 = 5 →
      (σ : Perm (Fin 7)) 6 = 6 → P σ := by
    intro σ h5 h6 w
    exact mem_sup_left (comm_mem_sup_of_isWord6 ((alt7_words σ h5 h6).map ρ) w)
  have hs : P a7s := hmul _ _ (hmul _ _ h₃ h₂) (hmul _ _ h₃ h₃)
  have hA6 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 6 = 6 → P σ := by
    intro σ h6
    rcases alt7_cosets5 σ h6 with h5 | ⟨h, hh, hk5⟩
    · exact hA5 σ h5 h6
    · obtain ⟨hh5, hh6⟩ := a7reps5_fix h hh
      have hk6 : (((h * a7s)⁻¹ * σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 6 = 6 := by
        have hs6 : (((h * a7s : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))) 6 = 6 := by
          rw [Subgroup.coe_mul, Perm.mul_apply, a7s_six, hh6]
        rw [Subgroup.coe_mul, Perm.mul_apply, h6, Subgroup.coe_inv, Perm.inv_eq_iff_eq, hs6]
      have e : σ = h * a7s * ((h * a7s)⁻¹ * σ) := by group
      rw [e]
      exact hmul _ _ (hmul _ _ (hA5 h hh5 hh6) hs) (hA5 _ hk5 hk6)
  have hA7 : ∀ σ, P σ := by
    intro σ
    rcases alt7_cosets6 σ with h6 | ⟨h, hh, hk6⟩
    · exact hA6 σ h6
    · have e : σ = h * a7c456 * ((h * a7c456)⁻¹ * σ) := by group
      rw [e]
      exact hmul _ _ (hmul _ _ (hA6 h (a7reps6_fix h hh)) h₃) (hA6 _ hk6)
  have hle : (⊤ : Subgroup W) ≤ M := by
    rw [← hcomm]
    refine (closure_le _).2 ?_
    rintro _ ⟨x, hx, w, rfl⟩
    obtain ⟨σ, hσ⟩ := hπs ⟨x, hx⟩
    have hx' : ρ σ = x := congrArg Subtype.val hσ
    rw [← hx']
    exact hA7 σ w
  let β' : W →* DnQuot 7 :=
    { toFun := fun v => β ⟨v, mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
  have hcard : ∀ γ : ↥(alternatingGroup (Fin 7)), γ ^ 3 = 1 → ∀ T : Finset (PermMod 7),
      (∀ m : PermMod 7, permAct 7 (γ : Perm (Fin 7)) m * m⁻¹ ∈ T) →
      Nat.card (commMap (ρ γ)).range ≤ T.card := fun γ hγ T hT =>
    card_commMap_range_le (β := β') hW2 (fun v => hβk ⟨v, mem_top v⟩)
      (by rw [← Subgroup.coe_pow, ← map_pow, hγ, map_one]; rfl) (fun z hz => hZ hz _ (π γ).2)
      (fun v m h => hβe γ ⟨v, mem_top v⟩ m (mem_top _) (permAct_mem_coreMod _ m.2) h) T hT
  have c₁ := hcard a7c012 a7c012_pow _ comm_mem_evenOn_seven_012
  have c₂ := hcard a7c234 a7c234_pow _ comm_mem_evenOn_seven_234
  have c₃ := hcard a7c456 a7c456_pow _ comm_mem_evenOn_seven_456
  rw [evenOn_seven_012_card] at c₁
  rw [evenOn_seven_234_card] at c₂
  rw [evenOn_seven_456_card] at c₃
  have hV : Nat.card W ≤ 64 :=
    calc Nat.card W = Nat.card (⊤ : Subgroup W) := card_top.symm
      _ ≤ Nat.card M := card_le_of_le hle
      _ ≤ Nat.card ↥((commMap (ρ a7c012)).range ⊔ (commMap (ρ a7c234)).range) *
          Nat.card (commMap (ρ a7c456)).range := card_sup_le_mul _ _
      _ ≤ (Nat.card (commMap (ρ a7c012)).range * Nat.card (commMap (ρ a7c234)).range) *
          Nat.card (commMap (ρ a7c456)).range :=
          Nat.mul_le_mul_right _ (card_sup_le_mul _ _)
      _ ≤ (4 * 4) * 4 := Nat.mul_le_mul (Nat.mul_le_mul c₁ c₂) c₃
  have hbij : Function.Bijective β :=
    hβs.bijective_of_nat_card_le (by rw [card_top]; exact hV.trans card_dnQuot_seven.symm.le)
  rw [eq_bot_iff]
  intro z hz
  have h1 : β ⟨z, mem_top _⟩ = β 1 := by rw [(hβk _).2 hz, map_one]
  exact congrArg Subtype.val (hbij.1 h1)

end CFSG.Quasithin.H13.VolI
