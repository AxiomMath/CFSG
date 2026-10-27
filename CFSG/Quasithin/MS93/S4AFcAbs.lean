module

public import CFSG.Quasithin.MS93.S4AFAbs

public section

namespace CFSG.Quasithin.MS93.S4A.F

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S46
open scoped Matrix

section Fix

variable {F : Type} [Field F] [Finite F] {n : ℕ} {H : Type} [Group H]
  {X : Type} [CommGroup X] [Finite X]

theorem fix_of_sections (hX2 : ∀ x : X, x ^ 2 = 1) {Q : Subgroup H} [Q.Normal]
    (hQ2 : IsPGroup 2 Q) (ρ : H →* MulAut X) {L : Subgroup H} (hL : ⁅L, L⁆ = L)
    (hsec : ∀ N N₁ : Subgroup X, (∀ h, ∀ x ∈ N, ρ h x ∈ N) → (∀ h, ∀ x ∈ N₁, ρ h x ∈ N₁) →
      N₁ ≤ N → N ≤ commV (Q.map ρ) → (∀ q ∈ Q, ∀ x ∈ N, ρ q x * x⁻¹ ∈ N₁) →
      ∀ l ∈ L, ∀ x ∈ N, ρ l x * x⁻¹ ∈ N₁) :
    ∀ l ∈ L, ∀ x ∈ commV (Q.map ρ), ρ l x = x := by
  set K := commV (Q.map ρ) with hKdef
  have hKinv : ∀ h, ∀ x ∈ K, ρ h x ∈ K := fun h x hx => commV_map_inv ρ h hx
  have key : ∀ m : ℕ, ∀ N : Subgroup X, Nat.card N ≤ m → (∀ h, ∀ x ∈ N, ρ h x ∈ N) →
      N ≤ K → ∀ l ∈ L, ∀ x ∈ N, ρ l x = x := by
    intro m
    induction m with
    | zero =>
      intro N hNc
      have : 0 < Nat.card N := Nat.card_pos
      omega
    | succ m ih =>
      intro N hNc hNinv hNK
      by_cases hN1 : N = ⊥
      · intro l _ x hx
        rw [hN1, Subgroup.mem_bot] at hx
        rw [hx, map_one]
      set N₁ := G6.commOn (Q.map ρ) N with hN₁def
      have hN₁N : N₁ ≤ N := by
        rw [hN₁def, G6.commOn, Subgroup.closure_le]
        rintro _ ⟨_, ⟨q, -, rfl⟩, u, hu, rfl⟩
        exact N.mul_mem (hNinv q u hu) (N.inv_mem hu)
      have hQ₀ : IsPGroup 2 (Q.map ρ) := hQ2.map ρ
      have hN₁ne : N₁ ≠ N := commOn_ne_of_isPGroup hX2 hQ₀
        (fun a ha n hn => by obtain ⟨q, -, rfl⟩ := ha; exact hNinv q n hn) hN1
      have hN₁inv : ∀ h, ∀ x ∈ N₁, ρ h x ∈ N₁ := fun h x hx => commOn_map_inv ρ hNinv h hx
      have hN₁c : Nat.card N₁ ≤ m := by
        have h1 : Nat.card N₁ < Nat.card N := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hN₁N) fun h => hN₁ne ?_
          exact Subgroup.eq_of_le_of_card_ge hN₁N h.ge
        omega
      have hfix₁ := ih N₁ hN₁c hN₁inv (hN₁N.trans hNK)
      exact fix_of_two_step ρ hL hfix₁ (hsec N N₁ hNinv hN₁inv hN₁N hNK
        fun q hq x hx => Subgroup.subset_closure ⟨ρ q, ⟨q, hq, rfl⟩, x, hx, rfl⟩)
  exact key (Nat.card K) K le_rfl hKinv le_rfl

theorem fix_commV_ker_ff (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ψ : H →* SL3 F)
    (hψ : Function.Surjective ψ) {Q : Subgroup H} (hQ : ψ.ker = Q) (hQ2 : IsPGroup 2 Q)
    (ρ : H →* MulAut X) {L : Subgroup H} (hL : ⁅L, L⁆ = L) {A : Subgroup H}
    (hA2 : ∀ a ∈ A, ψ a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, ψ a * ψ b = ψ b * ψ a)
    (hqA : Nat.card F ≤ Nat.card (A.map ψ))
    (hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV (A.map ρ)))
    (hN : ¬ commV (L.map ρ) ≤ commV (Q.map ρ)) :
    ∀ l ∈ L, ∀ x ∈ commV (Q.map ρ), ρ l x = x := by
  have : Q.Normal := hQ ▸ MonoidHom.normal_ker ψ
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  set K := commV (Q.map ρ) with hKdef
  have hKinv : ∀ h, ∀ x ∈ K, ρ h x ∈ K := fun h x hx => commV_map_inv ρ h hx
  have htop : ∀ h, ∀ x ∈ (⊤ : Subgroup X), ρ h x ∈ (⊤ : Subgroup X) :=
    fun _ _ _ => Subgroup.mem_top _
  set B : Subgroup (SL3 F) := A.map ψ with hBdef
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA2 a ha
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact hAc a ha a' ha'
  have hB : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hqA
    omega
  have hcardB : Nat.card X ≤ Nat.card B * Nat.card (fixV (A.map ρ)) :=
    hidx.trans (Nat.mul_le_mul_right _ hqA)
  have hker₀ := ker_le_ker_secRho hQ ρ htop hKinv fun q hq w _ =>
    G6.mem_commV_of_mem (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩) w
  have hnt₀ : ∃ h y, secRho ρ htop hKinv h y ≠ y := secRho_nt_of_not_le ρ hN
  have hlow₀ := le_index_fixV h14 hSQ hsq hF (sec_sq hX2) (liftRho ψ hψ _ hker₀)
    (liftRho_nt hψ hker₀ hnt₀) hB hB2 hBc (by
      rw [map_liftRho]
      exact sec_card_le ρ htop hKinv le_top A hcardB)
  rw [map_liftRho, map_secRho] at hlow₀
  have hAtop : A.map ρ ≤ stabSub (⊤ : Subgroup X) :=
    (Subgroup.map_le_range ρ A).trans (range_le_stabSub ρ htop)
  have hd₀ := card_inf_fixV_le_autSec (le_top : K ≤ ⊤) hAtop
  rw [top_inf_eq] at hd₀
  have hcs₀ := card_sec_mul (le_top : K ≤ ⊤)
  rw [Subgroup.card_top] at hcs₀
  refine fix_of_sections hX2 hQ2 ρ hL fun N N₁ hNinv hN₁inv hN₁N hNK hQN => ?_
  by_contra hstep
  push Not at hstep
  obtain ⟨l, hl, x, hx, hlx⟩ := hstep
  have hker₁ := ker_le_ker_secRho hQ ρ hNinv hN₁inv hQN
  have hnt₁ : ∃ h y, secRho ρ hNinv hN₁inv h y ≠ y := sec_nt ρ hNinv hN₁inv hx hlx
  have hlow₁ := le_index_fixV h14 hSQ hsq hF (sec_sq hX2) (liftRho ψ hψ _ hker₁)
    (liftRho_nt hψ hker₁ hnt₁) hB hB2 hBc (by
      rw [map_liftRho]
      exact sec_card_le ρ hNinv hN₁inv hN₁N A hcardB)
  rw [map_liftRho] at hlow₁
  have h1 := card_mul_inf_fixV_le_of_sec ρ hNinv hN₁inv hN₁N A hlow₁
  have h2 := card_mul_inf_fixV_mono hNK (fixV (A.map ρ)) h1
  have hc : 0 < Nat.card (fixV (A.map ρ)) := Nat.card_pos
  have h3 : Nat.card F * Nat.card F * Nat.card (fixV (A.map ρ)) ≤
      Nat.card F * Nat.card (fixV (A.map ρ)) :=
    calc Nat.card F * Nat.card F * Nat.card (fixV (A.map ρ))
        ≤ Nat.card F * Nat.card F * (Nat.card (fixV (autSec (A.map ρ) ⊤ K)) *
            Nat.card ↥(K ⊓ fixV (A.map ρ))) := Nat.mul_le_mul_left _ hd₀
      _ = (Nat.card F * Nat.card (fixV (autSec (A.map ρ) ⊤ K))) *
            (Nat.card F * Nat.card ↥(K ⊓ fixV (A.map ρ))) := by ring
      _ ≤ Nat.card (Sec ⊤ K) * Nat.card K := Nat.mul_le_mul hlow₀ h2
      _ = Nat.card X := hcs₀
      _ ≤ Nat.card F * Nat.card (fixV (A.map ρ)) := hidx
  have h4 : Nat.card F * Nat.card F ≤ Nat.card F := Nat.le_of_mul_le_mul_right h3 hc
  have : Nat.card F * 2 ≤ Nat.card F * Nat.card F := Nat.mul_le_mul_left _ hq2
  omega

end Fix

section Split

variable {F : Type} [Field F] [Finite F] {n : ℕ} {H : Type} [Group H]
  {X : Type} [CommGroup X] [Finite X]

theorem natSplit_quot_ff (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Nat.card F = 2 ^ n) (hX2 : ∀ x : X, x ^ 2 = 1) (ψ : H →* SL3 F)
    (hψ : Function.Surjective ψ) {Q : Subgroup H} (hQ : ψ.ker = Q) (ρ : H →* MulAut X)
    {A : Subgroup H} (hA2 : ∀ a ∈ A, ψ a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, ψ a * ψ b = ψ b * ψ a)
    (hqA : Nat.card F ≤ Nat.card (A.map ψ))
    (hidx : Nat.card X ≤ Nat.card F * Nat.card (fixV (A.map ρ)))
    (hnt : ¬ commV ρ.range ≤ commV (Q.map ρ)) :
    ∃ C : Subgroup X, commV (Q.map ρ) ≤ C ∧
      (∀ h, ∀ c ∈ C, ρ h c * c⁻¹ ∈ commV (Q.map ρ)) ∧
      commV ρ.range ⊔ C = ⊤ ∧ commV ρ.range ⊓ C = commV (Q.map ρ) ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
        ∃ (τ : H →* SL3 F') (β : ↥(commV ρ.range) →* Multiplicative (Fin 3 → F')),
          Function.Surjective τ ∧ Function.Surjective β ∧
          (∀ p : ↥(commV ρ.range), β p = 1 ↔ (p : X) ∈ commV (Q.map ρ)) ∧
          ∀ h (p : ↥(commV ρ.range)),
            β (resRho ρ (commV ρ.range) (fun g _ hx => commV_inv ρ g hx) h p) =
              Multiplicative.ofAdd ((τ h : Matrix (Fin 3) (Fin 3) F') *ᵥ
                Multiplicative.toAdd (β p)) := by
  have : Q.Normal := hQ ▸ MonoidHom.normal_ker ψ
  have hKinv : ∀ h, ∀ x ∈ commV (Q.map ρ), ρ h x ∈ commV (Q.map ρ) :=
    fun h x hx => commV_map_inv ρ h hx
  have htop : ∀ h, ∀ x ∈ (⊤ : Subgroup X), ρ h x ∈ (⊤ : Subgroup X) :=
    fun _ _ _ => Subgroup.mem_top _
  set B : Subgroup (SL3 F) := A.map ψ with hBdef
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA2 a ha
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact hAc a ha a' ha'
  have hB : B ≠ ⊥ := by
    intro hbot
    have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hbot, Subgroup.card_bot] at hqA
    omega
  have hker₀ := ker_le_ker_secRho hQ ρ htop hKinv fun q hq w _ =>
    G6.mem_commV_of_mem (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩) w
  have hnt₀ : ∃ h y, secRho ρ htop hKinv h y ≠ y :=
    secRho_nt_of_not_le (L := ⊤) ρ (by rw [← MonoidHom.range_eq_map]; exact hnt)
  have hidx' : Nat.card (Sec ⊤ (commV (Q.map ρ))) ≤
      Nat.card F * Nat.card (fixV (B.map (liftRho ψ hψ _ hker₀))) := by
    rw [map_liftRho]
    exact sec_card_le ρ htop hKinv le_top A hidx
  exact natSplit_core ψ hψ ρ htop hKinv hker₀ (ffOff_decomp h14 hSQ hsq hF (sec_sq hX2) _
    (liftRho_nt hψ hker₀ hnt₀) hB hB2 hBc hqA hidx')

end Split

end CFSG.Quasithin.MS93.S4A.F
