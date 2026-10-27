module

public import CFSG.Quasithin.H13.L32A511Qg
public import CFSG.Quasithin.H13.L32A511Qe

public section

namespace CFSG.Quasithin.H13.Q511

open CFSG.Quasithin
open scoped commutatorElement IsMulCommutative

theorem commute_of_action {G : Type*} [Group G] [Finite G] {W H P A : Subgroup G}
    [IsMulCommutative ↥W] (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hHN : H ≤ Subgroup.normalizer (W : Set G)) (hPH : P ≤ H)
    (hPn : H ≤ Subgroup.normalizer (P : Set G)) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hPp : ∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (W : Set G))
    {s c : G} (hsH : s ∈ H) (hcH : c ∈ H) (hsA : s ∈ A) (hcA : c ∈ A) (hs2 : s ^ 2 = 1)
    (hc2 : c ^ 2 = 1) (hcs : c * s = s * c)
    (hb : Nat.card W ≤ 4 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ∨
      (c ∉ Subgroup.centralizer (W : Set G) ∧
        Nat.card W ≤ 8 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))))
    {S₀ : Set G} (hS : ∀ x ∈ S₀, x ∈ H ∧ x ^ 3 = 1 ∧
      (s * x * s⁻¹ * x ∉ Subgroup.centralizer (W : Set G) →
        (s * x * s⁻¹ * x) * (s * x * s⁻¹ * x) ∈ Subgroup.centralizer (W : Set G) ∧
        x * (s * x * s⁻¹ * x) * x⁻¹ * (s * x * s⁻¹ * x)⁻¹ ∈ Subgroup.centralizer (W : Set G)) ∧
      c * x * c⁻¹ * x⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    ∀ g ∈ P, ∀ x ∈ Subgroup.closure S₀, ⁅g, x⁆ ∈ Subgroup.centralizer (W : Set G) := by
  classical
  set CW := Subgroup.centralizer (W : Set G) with hCW
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW2 v v.2)
  set ρ : ↥H →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hHN) with hρ
  have hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ CW := by
    intro h
    rw [← MonoidHom.mem_ker, hρ, ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
    rfl
  have hρapp : ∀ (h : ↥H) (w : ↥W), ((ρ h w : ↥W) : G) = h * w * (h : G)⁻¹ := fun h w => rfl
  have hρc : ∀ a b : ↥H, ((⁅a, b⁆ : ↥H) : G) ∈ CW → ρ a * ρ b = ρ b * ρ a := by
    intro a b h
    have h1 := (hρ1 ⁅a, b⁆).mpr h
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  set D : Subgroup (MulAut ↥W) := (P.subgroupOf H).map ρ with hD
  have hDp : IsPGroup p ↥D := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨k, hk⟩ := hPp g hg
    refine ⟨k, Subtype.ext ?_⟩
    show ρ g ^ p ^ k = 1
    rw [← map_pow, hρ1]
    simpa using hk
  have hDn : ∀ h : ↥H, ∀ d ∈ D, ρ h * d * (ρ h)⁻¹ ∈ D := by
    rintro h _ ⟨g, hg, rfl⟩
    refine ⟨h * g * h⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hPn h.2) g).mp hg
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  obtain ⟨sH, hsHc⟩ : ∃ sH : ↥H, (sH : G) = s := ⟨⟨s, hsH⟩, rfl⟩
  obtain ⟨cH, hcHc⟩ : ∃ cH : ↥H, (cH : G) = c := ⟨⟨c, hcH⟩, rfl⟩
  have hs2' : ρ sH ^ 2 = 1 := by
    rw [← map_pow]
    have : sH ^ 2 = 1 := Subtype.ext (by simpa [hsHc] using hs2)
    rw [this, map_one]
  have hc2' : ρ cH ^ 2 = 1 := by
    rw [← map_pow]
    have : cH ^ 2 = 1 := Subtype.ext (by simpa [hcHc] using hc2)
    rw [this, map_one]
  have hcs' : ρ cH * ρ sH = ρ sH * ρ cH := by
    rw [← map_mul, ← map_mul]
    have : cH * sH = sH * cH := Subtype.ext (by simpa [hsHc, hcHc] using hcs)
    rw [this]
  have hfix : Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(fixV (Subgroup.zpowers (ρ sH)) ⊓ fixV (Subgroup.zpowers (ρ cH))) := by
    have hle : (W ⊓ Subgroup.centralizer (A : Set G)).subgroupOf W ≤
        fixV (Subgroup.zpowers (ρ sH)) ⊓ fixV (Subgroup.zpowers (ρ cH)) := by
      intro w hw
      rw [Subgroup.mem_subgroupOf] at hw
      have hwA := Subgroup.mem_centralizer_iff.mp hw.2
      refine Subgroup.mem_inf.mpr ⟨mem_fixV_zpowers_iff.mpr (Subtype.ext ?_),
        mem_fixV_zpowers_iff.mpr (Subtype.ext ?_)⟩
      · rw [hρapp, hsHc, hwA s hsA]; group
      · rw [hρapp, hcHc, hwA c hcA]; group
    calc Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))
        = Nat.card ↥((W ⊓ Subgroup.centralizer (A : Set G)).subgroupOf W) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv.symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hb' : rk ((⊤ : Subgroup ↥W).map (commHom (ρ sH))) ≤ 2 ∨
      (ρ cH ≠ 1 ∧ rkIdx (fixV (Subgroup.zpowers (ρ sH)) ⊓
        fixV (Subgroup.zpowers (ρ cH))) ≤ 3) := by
    rcases hb with h | ⟨hc, h⟩
    · refine Or.inl (rk_map_le_of_card_le hV ?_)
      have h1 := hfix.trans (Subgroup.card_le_of_le inf_le_left)
      calc Nat.card ↥W ≤ 4 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := h
        _ ≤ 2 ^ 2 * Nat.card ↥(fixV (Subgroup.zpowers (ρ sH))) := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
          exact Nat.mul_le_mul_left _ h1
    · refine Or.inr ⟨fun h1 => hc (hcHc ▸ (hρ1 cH).mp h1), rkIdx_le_of_card_le hV ?_⟩
      calc Nat.card ↥W ≤ 8 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := h
        _ ≤ 2 ^ 3 * _ := by
          rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
          exact Nat.mul_le_mul_left _ hfix
  have hkey : ∀ xH : ↥H, (xH : G) ∈ S₀ → ∀ d ∈ D, ρ xH * d = d * ρ xH := by
    intro xH hxS
    obtain ⟨-, hx3, hq, hcx⟩ := hS _ hxS
    have hx3' : ρ xH ^ 3 = 1 := by
      rw [← map_pow]
      have : xH ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    obtain ⟨qH, hqHd⟩ : ∃ qH : ↥H, qH = sH * xH * sH⁻¹ * xH := ⟨_, rfl⟩
    have hqc : (qH : G) = s * xH * s⁻¹ * xH := by rw [hqHd]; simp [hsHc]
    have hqe : ρ qH = ρ sH * ρ xH * (ρ sH)⁻¹ * ρ xH := by
      rw [hqHd, map_mul, map_mul, map_mul, map_inv]
    have hq2 : ρ qH ≠ 1 → ρ qH * ρ qH = 1 := by
      intro hne
      have h1 := (hq fun h => hne ((hρ1 qH).mpr (hqc ▸ h))).1
      rw [← map_mul, hρ1]
      simpa [hqc] using h1
    have hxq : ρ qH ≠ 1 → ρ xH * ρ qH * (ρ xH)⁻¹ = ρ qH := by
      intro hne
      have h1 := (hq fun h => hne ((hρ1 qH).mpr (hqc ▸ h))).2
      have h2 := hρc xH qH (by simpa [commutatorElement_def, hqc] using h1)
      rw [h2]
      group
    have hinv := inv_of_sq_eq_one hx3' hqe hq2 hxq
    have hcx' : ρ cH * ρ xH = ρ xH * ρ cH :=
      hρc cH xH (by simpa [commutatorElement_def, hcHc] using hcx)
    exact commute_of_pgroup hV hp5 hDp hx3' hs2' hc2' hinv hcx' hcs' (hDn xH) (hDn sH) (hDn cH)
      hb'
  have hS₀ : Subgroup.closure S₀ ≤
      ((Subgroup.centralizer (D : Set (MulAut ↥W))).comap ρ).map H.subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, (hS x hx).1⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hkey ⟨x, (hS x hx).1⟩ hx d hd).symm
  intro g hg x hx
  obtain ⟨xH, hxH, rfl⟩ := hS₀ hx
  have h1 : ρ ⟨g, hPH hg⟩ ∈ D := ⟨⟨g, hPH hg⟩, hg, rfl⟩
  have h2 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hxH) _ h1
  have h3 : ρ ⁅(⟨g, hPH hg⟩ : ↥H), xH⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, h2]
  have := (hρ1 _).mp h3
  simpa [commutatorElement_def] using this

end CFSG.Quasithin.H13.Q511

end
