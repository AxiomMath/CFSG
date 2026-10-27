module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspDefs
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU5

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem two_pow_mul_four_pow_injective :
    Function.Injective (fun n : ℕ => 2 ^ n * (4 ^ n - 1)) := by
  have hmono : StrictMono (fun n : ℕ => 2 ^ n * (4 ^ n - 1)) := by
    intro a b hab
    have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    have h2 : 4 ^ a < 4 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    have h3 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
    show 2 ^ a * (4 ^ a - 1) < 2 ^ b * (4 ^ b - 1)
    calc 2 ^ a * (4 ^ a - 1) ≤ 2 ^ a * (4 ^ b - 1) := Nat.mul_le_mul_left _ (by omega)
      _ < 2 ^ b * (4 ^ b - 1) := Nat.mul_lt_mul_of_pos_right h1 (by omega)
  exact hmono.injective

theorem isPSp4_quot_center {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : IsPSp4 2 n X) :
    IsPSp4 2 n (X ⧸ Subgroup.center X) := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  let ψ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F)
      ⟨CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo,
        QuotientGroup.mk'_surjective _⟩
  have hc : Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq]
    exact CFSG.QuasithinUnique.Vol2Native.A312L.spScalars_eq_bot
  have hcX : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (e.trans ψ.symm) x ∈ Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y', rfl⟩ := (e.trans ψ.symm).surjective y
      rw [← map_mul, ← map_mul, hx y']
    rw [hc, Subgroup.mem_bot, map_eq_one_iff _ (e.trans ψ.symm).injective] at hx'
    rw [Subgroup.mem_bot]
    exact hx'
  have e' : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcX).trans QuotientGroup.quotientBot
  exact IsPSp4.of_mulEquiv e'.symm ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩

theorem insp436Sp4_of (hG2 : Insp436G2) (hD4 : Insp436D4) (hF4 : Insp436F4)
    (hM : Insp436M22M23) : Insp436Sp4 := by
  have hL3 := CFSG.Quasithin.H13.Ch4.insp436L3_holds
  intro G _ _ H R M L V K R₀ n hn hLie _ hK hC31 hcase hV hR₀2 hR₀H hR₀N hR₀L hR₀K hNM
  obtain ⟨hLeq, hnorm, hM0K, hMK, hZ2, -⟩ := hC31
  have hKq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hKH : K ≤ H := hK.1
  have hNK : K ⊓ Subgroup.normalizer (R₀ : Set G) ≤ M := fun x hx => hNM ⟨hKH hx.1, hx.2⟩
  have hNMK : K ⊓ Subgroup.normalizer (R₀ : Set G) ≤ M ⊓ K := fun x hx => ⟨hNK hx, hx.1⟩
  rcases hcase with h1 | ⟨rfl, h2⟩
  · obtain ⟨n', hlie, hPmax, hM0eq, hpsl, hnat⟩ := h1
    have hn' : n' = n := by
      have hc1 := F420.card_of_statedPSL_two_two hpsl
      have hc2 := F420.card_of_statedPSL_two_two
        (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie)
      rw [← hLeq] at hc1
      exact two_pow_mul_four_pow_injective (hc1.symm.trans hc2)
    subst hn'
    have hLP : L = perfectCore (M ⊓ K) := hLeq.trans hM0eq
    have hR₀P : R₀ ≤ Subgroup.centralizer (perfectCore (M ⊓ K) : Set G) := hLP ▸ hR₀L
    rcases hnat with hnat | ⟨hSp, hnat2⟩
    swap
    · exact ⟨⟨n', hlie, hPmax, hM0eq, hpsl, Or.inr ⟨hSp, hnat2⟩⟩,
        isPSp4_quot_center (by omega) hSp⟩
    have hnat' : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n' ∧
        IsNaturalSection (perfectCore (M ⊓ K)) V (V ⊓ centerOf K)
          (CFSG.pCore 2 ↥(perfectCore (M ⊓ K))) (CFSG.Assembly.LowTwoRank.StatedSL 2 F) := by
      rw [← hM0eq]
      exact hnat
    have hpsl' : IsPSL 2 2 n' (ModO2 (perfectCore (M ⊓ K))) := by
      rw [← hM0eq]
      exact hpsl
    have hV' : V ≤ pCoreOf 2 (perfectCore (M ⊓ K)) ⊓
        Subgroup.centralizer (pCoreOf 2 (perfectCore (M ⊓ K)) : Set G) := hLP ▸ hV
    rcases hlie with hL | hSp | hG | hD | hF | hU4 | hU5 | ⟨h1, -⟩
    · exact absurd (hL3 G K (M ⊓ K) R₀ n' hn hKq hL hPmax hR₀N hR₀P) hR₀K
    · exact ⟨⟨n', Or.inr (Or.inl hSp), hPmax, hM0eq, hpsl, Or.inl hnat⟩, hSp⟩
    · exact absurd (hG2 G K (M ⊓ K) V R₀ n' hn hKq hG hPmax hpsl' hnat' hV' hR₀2 hR₀N hR₀P
        hNMK) hR₀K
    · exact absurd (hD4 G K (M ⊓ K) V R₀ n' hn hKq hD hPmax hpsl' hnat' hV' hR₀2 hR₀N hR₀P
        hNMK) hR₀K
    · exact absurd (hF4 G K (M ⊓ K) V R₀ n' hn hKq hF hPmax hpsl' hnat' hV' hR₀2 hR₀N hR₀P
        hNMK) hR₀K
    · exact False.elim (U4A.false_of_isPSU4_natural K (M ⊓ K) V n' hn hZ2 hU4 hPmax
        hpsl' hnat' hV')
    · exact False.elim (U5A.false_of_isPSU5_natural K (M ⊓ K) V n' hn hZ2 hU5 hPmax
        hpsl' hnat' hV')
    · omega
  · have h2' : C436Two M (conjClosure L M) K := by
      rw [← hLeq]
      exact h2
    have hR₀M0 : R₀ ≤ Subgroup.centralizer (conjClosure L M : Set G) := hLeq ▸ hR₀L
    exact absurd (hM G K M (conjClosure L M) R₀ hKq hM0K hnorm hMK h2'
      (by rw [← hLeq]; exact hLeq.symm) hR₀2 hR₀N hR₀M0 hNK) hR₀K

end CFSG.Quasithin.H13.Ch4
