module

public import CFSG.Quasithin.EmptyFaithful.S152He2Module
public import CFSG.Quasithin.EmptyFaithful.S152He3Mod
public import CFSG.Quasithin.EmptyFaithful.S152He3Chief
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

theorem heNoSmallCommutatorModule_holds
 :
    HeNoSmallCommutatorModule := by
  classical
  intro Γ _ _ K T X Q E L N hXKT hXn hKHe hsyl hET _ hQX hQ2 hchief hnot
  by_contra hcon
  have hlt : Nat.card ↥(⁅N, E⁆ ⊔ L) < 8 * Nat.card L := not_le.mp hcon
  have hKX : K ≤ X := by
    rw [hXKT]
    exact le_sup_left
  have hTX : T ≤ X := hsyl.1
  have hEX : E ≤ X := hET.trans hTX
  have hXL : X ≤ Subgroup.normalizer (L : Set Γ) := D14.le_normalizer_of_isNormalIn hchief.2.1
  have hXN : X ≤ Subgroup.normalizer (N : Set Γ) := D14.le_normalizer_of_isNormalIn hchief.1
  have hNQ : N ≤ Q := hchief.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set Γ) := (hNQ.trans hQX).trans hXL
  have hLN : L ≤ N := hchief.2.2.1.le
  have hKnorm : X ≤ Subgroup.normalizer (K : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hXn g hg k hk, fun hk => ?_⟩
    have := hXn g⁻¹ (X.inv_mem hg) _ hk
    simpa [mul_assoc] using this
  have hE' : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hchief hQX hQ2
  let _ : CommGroup ↥(Ch3z.chiefMod L N) := Ch3z.chiefCG hE'
  have hW : ∀ w : ↥(Ch3z.chiefMod L N), w * w = 1 := fun w => by
    simpa [sq] using Ch3z.chiefMod_sq hE' w
  set ψ : ↥X →* MulAut ↥(Ch3z.chiefMod L N) := Ch3z.chiefPsi hXL hXN with hψ
  set X' : Subgroup (MulAut ↥(Ch3z.chiefMod L N)) := Ch3z.chiefAut X L N with hX'
  have hψX' : ∀ g, ψ g ∈ X' := Ch3z.chiefPsi_mem hXL hXN
  have hsurj : ∀ x ∈ X', ∃ g, ψ g = x := by
    intro x hx
    obtain ⟨g, hg⟩ := Ch3z.chiefHom_surjective hXL hXN ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  have hO2 : ∀ Q' : Subgroup (MulAut ↥(Ch3z.chiefMod L N)), Q' ≤ X' →
      (Q'.subgroupOf X').Normal → IsPGroup 2 Q' → Q' = ⊥ :=
    fun Q' h1 h2 h3 => D15Proof.normal_two_eq_bot hQX hchief hE' Q' h1 h2 h3
  set K' : Subgroup (MulAut ↥(Ch3z.chiefMod L N)) := (K.subgroupOf X).map ψ with hK'
  have hKX' : K' ≤ X' := by
    rintro _ ⟨g, -, rfl⟩
    exact hψX' g
  have hn' : ∀ x ∈ X', ∀ k ∈ K', x * k * x⁻¹ ∈ K' := by
    intro x hx k hk
    obtain ⟨g, rfl⟩ := hsurj x hx
    obtain ⟨κ, hκ, rfl⟩ := hk
    refine ⟨g * κ * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    simpa using hXn g g.2 κ (Subgroup.mem_subgroupOf.mp hκ)
  have h2pow : ∀ x ∈ X', ∃ m : ℕ, x ^ 2 ^ m ∈ K' := by
    intro x hx
    obtain ⟨g, rfl⟩ := hsurj x hx
    have hgsup : (g : Γ) ∈ K ⊔ T := by
      rw [← hXKT]
      exact g.2
    obtain ⟨m, hm⟩ := InternalSec.two_of_sup hsyl.2.1 (hTX.trans hKnorm) _ hgsup
    refine ⟨m, g ^ 2 ^ m, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_pow]⟩
    simpa using hm
  have hPn : ∀ g ∈ X, ∀ p ∈ pCoreOf 2 K, g * p * g⁻¹ ∈ pCoreOf 2 K := fun g hg p hp =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hKnorm hg)) p).mp hp
  have hP : ∀ g : ↥X, (g : Γ) ∈ pCoreOf 2 K → ψ g = 1 := fun g hg =>
    map_eq_one_of_normal_two152 ψ hψX' hsurj hO2 hPn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hg
  have hex : ∃ e₁ : ↥X, (e₁ : Γ) ∈ E ∧ ψ e₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnot
    exact Subgroup.commutator_le.mpr fun n hn e he =>
      commutator_mem_of_chiefPsi_eq_one hXL hXN hNL (hall ⟨e, hEX he⟩ he) hn
  obtain ⟨e₁, he₁E, he₁⟩ := hex
  by_cases hK'bot : K' = ⊥
  · have hX'bot : X' = ⊥ := eq_bot_of_two_pow152 hO2 h2pow (fun k hk => by
      rw [hK'bot] at hk
      exact Subgroup.mem_bot.mp hk)
    apply he₁
    have := hψX' e₁
    rw [hX'bot] at this
    exact Subgroup.mem_bot.mp this
  obtain ⟨e0⟩ := hKHe
  have hs := isSimpleGroup_carrier_he
  let ψK : ↥K →* ↥K' := (ψ.comp (Subgroup.inclusion hKX)).codRestrict K'
    (fun κ => ⟨Subgroup.inclusion hKX κ, Subgroup.mem_subgroupOf.mpr κ.2, rfl⟩)
  have hle : CFSG.Open.pCore 2 ↥K ≤ ψK.ker := by
    intro κ hκ
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hP (Subgroup.inclusion hKX κ) ⟨κ, hκ, rfl⟩
  let π0 : OTwoQuot K →* ↥K' := QuotientGroup.lift _ ψK hle
  have hπ0 : Function.Surjective π0 := by
    rintro ⟨y, g, hg, rfl⟩
    exact ⟨QuotientGroup.mk ⟨(g : Γ), Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩
  have hiso : Nonempty (NativeSporadic.Carrier .He ≃* ↥K') := by
    let π : NativeSporadic.Carrier .He →* ↥K' := π0.comp e0.symm.toMonoidHom
    have hπ : Function.Surjective π := hπ0.comp e0.symm.surjective
    refine ⟨MulEquiv.ofBijective π ⟨?_, hπ⟩⟩
    rcases hs.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).mp h
    · exfalso
      apply hK'bot
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨h1, hh1⟩ := hπ ⟨y, hy⟩
      have h1k : h1 ∈ π.ker := by
        rw [h]
        exact Subgroup.mem_top h1
      rw [MonoidHom.mem_ker] at h1k
      rw [h1k] at hh1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hh1).symm
  obtain ⟨e⟩ := hiso
  have hZ : ∀ k ∈ K', (∀ k' ∈ K', k * k' = k' * k) → k = 1 := by
    intro k hk hc
    have hcen : e.symm ⟨k, hk⟩ ∈ Subgroup.center (NativeSporadic.Carrier .He) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext ((hc _ (e g).2).symm)
    rw [center_carrier_he_eq_bot, Subgroup.mem_bot] at hcen
    have h1 := congrArg e hcen
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    exact congrArg Subtype.val h1
  have hC := eq_one_of_commute_of_two_pow152 hO2 hn' h2pow hZ
  set E' : Subgroup (MulAut ↥(Ch3z.chiefMod L N)) := (E.subgroupOf X).map ψ with hE'def
  have hE'2 : IsPGroup 2 E' := by
    rintro ⟨_, ⟨p, hp, rfl⟩⟩
    obtain ⟨k, hk⟩ := hsyl.2.1 ⟨(p : Γ), hET (Subgroup.mem_subgroupOf.mp hp)⟩
    refine ⟨k, Subtype.ext ?_⟩
    have : p ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp [← map_pow, this]
  have hE'X' : E' ≤ X' := by
    rintro _ ⟨p, -, rfl⟩
    exact hψX' p
  have he₁E' : ψ e₁ ∈ E' := ⟨e₁, Subgroup.mem_subgroupOf.mpr he₁E, rfl⟩
  have h2dvd : 2 ∣ Nat.card ↥E' := by
    rcases hE'2.card_eq_or_dvd with h1 | h1
    · exfalso
      have h0 : E' = ⊥ := Subgroup.card_eq_one.mp h1
      rw [h0, Subgroup.mem_bot] at he₁E'
      exact he₁ he₁E'
    · exact h1
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hτ2 : (τ : MulAut ↥(Ch3z.chiefMod L N)) * τ = 1 := by
    have h1 : τ ^ 2 = 1 := by
      have := pow_orderOf_eq_one τ
      rwa [hτ] at this
    simpa [sq] using congrArg Subtype.val h1
  have hτ1 : (τ : MulAut ↥(Ch3z.chiefMod L N)) ≠ 1 := by
    intro h
    have : τ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hτ
    omega
  have hτX' : (τ : MulAut ↥(Ch3z.chiefMod L N)) ∈ X' := hE'X' τ.2
  obtain ⟨e', he'E, he'τ⟩ := τ.2
  have hτK : ∃ k ∈ K', (τ : MulAut ↥(Ch3z.chiefMod L N)) * k *
      (τ : MulAut ↥(Ch3z.chiefMod L N))⁻¹ ≠ k := by
    by_contra hall
    push Not at hall
    refine hτ1 (hC _ hτX' fun k hk => ?_)
    have h1 := hall k hk
    calc (τ : MulAut ↥(Ch3z.chiefMod L N)) * k
        = ((τ : MulAut ↥(Ch3z.chiefMod L N)) * k * (τ : MulAut ↥(Ch3z.chiefMod L N))⁻¹) * τ := by
          group
      _ = k * τ := by rw [h1]
  have key := two_pow_eight_le_index_fixV_of_he hW hKX' hn' e.symm hτX' hτ2 hτK
  have hlt8 := index_fixV_zpowers_chiefPsi_lt hXL hXN hNL hLN hEX hE' (Subgroup.mem_subgroupOf.mp he'E)
    hlt
  rw [he'τ] at hlt8
  obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW (Subgroup.zpowers (τ : MulAut ↥(Ch3z.chiefMod L N)))
  rw [hm] at key hlt8
  have hm3 : m < 3 := by
    by_contra h
    push Not at h
    have h8 : 8 ≤ 2 ^ m := calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases m <;> norm_num at key

end CFSG.Quasithin
