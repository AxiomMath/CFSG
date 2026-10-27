module

public import CFSG.RankThree.GF2n.Smith81.LinOddSteps
public import CFSG.RankThree.GF2n.Smith81.LinCount
public import CFSG.RankThree.GF2n.Smith81.Sec115

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Step6

theorem exists_nonswap {T V₁ V₂ : Subgroup G} (hT4 : 4 ≤ Nat.card T)
    (hT2 : ∀ t ∈ T, t * t = 1)
    (hsw : ∀ t ∈ T, (conjSubgroup t V₁ = V₁ ∧ conjSubgroup t V₂ = V₂) ∨
      (conjSubgroup t V₁ = V₂ ∧ conjSubgroup t V₂ = V₁)) :
    ∃ t ∈ T, t ≠ 1 ∧ conjSubgroup t V₁ = V₁ ∧ conjSubgroup t V₂ = V₂ := by
  by_contra hcon
  push Not at hcon
  have hswap : ∀ t ∈ T, t ≠ 1 → conjSubgroup t V₁ = V₂ ∧ conjSubgroup t V₂ = V₁ := by
    intro t ht ht1
    rcases hsw t ht with ⟨h1, h2⟩ | h
    · exact absurd h2 (hcon t ht ht1 h1)
    · exact h
  have hne : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT4
    omega
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ht₁1' : t₁ ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  have hnot : ¬ T ≤ Subgroup.zpowers t₁ := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf t₁ ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hT2 t₁ ht₁)
    omega
  obtain ⟨t₂, ht₂T, ht₂⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht₂1 : t₂ ≠ 1 := fun h => ht₂ (h ▸ Subgroup.one_mem _)
  have ht₃1 : t₁ * t₂ ≠ 1 := by
    intro h
    apply ht₂
    have : t₂ = t₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers t₁)
  obtain ⟨h11, h12⟩ := hswap t₁ ht₁ ht₁1'
  obtain ⟨h21, h22⟩ := hswap t₂ ht₂T ht₂1
  have h31 : conjSubgroup (t₁ * t₂) V₁ = V₁ := by
    rw [conjSubgroup_mul, h21, h12]
  have h32 : conjSubgroup (t₁ * t₂) V₂ = V₂ := by
    rw [conjSubgroup_mul, h22, h11]
  exact hcon (t₁ * t₂) (T.mul_mem ht₁ ht₂T) ht₃1 h31 h32

end Step6

variable {M Q Z B Y : Subgroup G} {V V' : Subgroup G}

theorem step6_aux (S : OddSetup M Q Z B V V') {e d r : ℕ} (hr : 2 ≤ r) (hd : 2 ≤ d)
    (hdr : e + 1 = d + r)
    (hSwap : ∀ t ∈ H0 M Z, (conjSubgroup t V = V ∧ conjSubgroup t V' = V') ∨
      (conjSubgroup t V = V' ∧ conjSubgroup t V' = V))
    (hNon : ∀ t ∈ H0 M Z, t * t ∈ Q → conjSubgroup t V = V → t ∈ Lgen M (LB M Q B))
    (hVcardV : Nat.card V = Nat.card Z ^ e)
    {y₀ : G} (hsY : Sit M Q Z Y y₀) (hQY : Q ⊓ QB Y = ⊥)
    (hD : Nat.card ↥(V ⊓ Subgroup.centralizer ({y₀} : Set G)) = Nat.card Z ^ d)
    (T : Subgroup G) (hTL : T ≤ Lx M Y)
    (hrank : ∀ a ∈ T, a ≠ 1 → a ∈ Lgen M (LB M Q B) →
      Nat.card ↥(⁅V, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z ^ r)
    (hcard : Nat.card Z ^ (d - 1) < Nat.card T) : False := by
  have h12 := smith_1_12 hsY
  have hq : 2 ≤ Nat.card Z := by have := S.hyp.q4; omega
  have hqpos : 0 < Nat.card Z := by omega
  set D : Subgroup G := V ⊓ Subgroup.centralizer ({y₀} : Set G) with hDdef
  have hy₀C : y₀ ∈ Subgroup.centralizer (Z : Set G) := (h12.1 hsY.mem).2
  have hZD : Z ≤ D := fun z hz => ⟨S.ZV hz, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hy₀C z hz)⟩
  have hDV : D ≤ V := inf_le_left
  have hDne : ∃ u ∈ V, u ∉ D := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ D := fun u hu => hcon u hu
    have h1 := Subgroup.card_le_of_le hle
    rw [hVcardV, hD] at h1
    have := Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z) |>.mp h1
    omega
  have hTH : ∀ s ∈ T, s ∈ H0 M Z := fun s hs => Lx_le_H0 hsY h12 (hTL hs)
  have hT2 : ∀ s ∈ T, s * s = 1 := fun s hs => by
    rw [← pow_two]; exact Lx_sq_eq_one hsY hQY (hTL hs)
  have hfix : ∀ s ∈ T, ∀ d' ∈ D, s * d' * s⁻¹ = d' := by
    intro s hs d' hd'
    have hdK : d' ∈ Kx Q Y := by
      rw [Kx_eq hsY h12]
      exact ⟨S.VQ hd'.1, hd'.2⟩
    have hc := (smith_1_15_elem hsY hQY).2.1 d' hdK s (hTL hs)
    rw [← hc]; group
  have hDZ : ∃ d' ∈ D, d' ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Z := fun d' hd' => hcon d' hd'
    have h1 := Subgroup.card_le_of_le hle
    rw [hD] at h1
    have hpow : Nat.card Z ^ 1 < Nat.card Z ^ d :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one] at hpow
    omega
  have hnon : ∀ s ∈ T, conjSubgroup s V = V := by
    intro s hs
    rcases hSwap s (hTH s hs) with h | h
    · exact h.1
    · exfalso
      obtain ⟨d', hdD, hdZ⟩ := hDZ
      have hd1 : s * d' * s⁻¹ ∈ conjSubgroup s V := by
        rw [mem_conjSubgroup]; simpa [mul_assoc] using hdD.1
      rw [hfix s hs d' hdD, h.1] at hd1
      exact hdZ (by rw [← S.int]; exact ⟨hdD.1, hd1⟩)
  have hLg : ∀ s ∈ T, s ∈ Lgen M (LB M Q B) := fun s hs =>
    hNon s (hTH s hs) (by rw [hT2 s hs]; exact Q.one_mem) (hnon s hs)
  have hSN : ∀ s ∈ T, ∀ v ∈ V, s * v * s⁻¹ ∈ V := fun s hs v hv =>
    (Subgroup.mem_normalizer_iff.mp (S.normV s (hLg s hs)) v).mp hv
  have hker : ∀ s ∈ T, s ≠ 1 → ∀ v ∈ V, ⁅s, v⁆ ∈ Z → v ∈ D := by
    intro s hs hs1 v hv hvZ
    have hc := LinCount.lin_card_preimage_Z S.abV S.ZV (hSN s hs) (hT2 s hs)
    rw [hrank s hs hs1 (hLg s hs), hVcardV] at hc
    have hP : Nat.card {v : G // v ∈ V ∧ ⁅s, v⁆ ∈ Z} = Nat.card Z ^ d := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hqpos r)
      rw [hc, ← pow_succ, ← pow_add, hdr]
    have hsub : (D : Set G) ⊆ {v : G | v ∈ V ∧ ⁅s, v⁆ ∈ Z} := by
      intro d' hd'
      refine ⟨hd'.1, ?_⟩
      have : ⁅s, d'⁆ = 1 := by
        simp only [commutatorElement_def]
        rw [hfix s hs d' hd']; group
      rw [this]; exact Z.one_mem
    have hnc : Set.ncard {v : G | v ∈ V ∧ ⁅s, v⁆ ∈ Z} = Nat.card Z ^ d := by
      rw [← Nat.card_coe_set_eq]; exact hP
    have hnd : Set.ncard (D : Set G) = Nat.card Z ^ d := by
      rw [← Nat.card_coe_set_eq]; exact hD
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hnc, hnd]) (Set.toFinite _)
    have hv' : v ∈ (D : Set G) := by rw [heq]; exact ⟨hv, hvZ⟩
    exact hv'
  have hle := LinCount.lin_card_le_of_fixed S.abV S.sqV hZD hDV hDne hSN hT2 hfix hker
  rw [hD] at hle
  have hp : Nat.card Z ^ d = Nat.card Z ^ (d - 1) * Nat.card Z := by
    rw [← pow_succ]; congr 1; omega
  rw [hp] at hle
  nlinarith

end CFSG.RankThree.GF2n.Smith81
