module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Line

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} {Γ : SimpleGraph V}

namespace Line

section Translate

variable {G : Type*} [Group G] [MulAction G V]

private lemma div_mod_spec {m : ℕ} (hm : 1 ≤ m) (j : ℤ) :
    0 ≤ j % (m : ℤ) ∧ j % (m : ℤ) < (m : ℤ) ∧
      j % (m : ℤ) + (m : ℤ) * (j / (m : ℤ)) = j :=
  ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega),
    Int.emod_add_mul_ediv j _⟩

@[expose] def ofTranslate (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {m : ℕ} (hm : 1 ≤ m) (γ : Arc Γ m) (t : G) (h0 : t • γ.vert 0 = γ.vert m)
    (h1 : t • γ.vert 1 ≠ γ.vert (m - 1)) : Line Γ where
  vert j := t ^ (j / (m : ℤ)) • γ.vert (j % (m : ℤ)).toNat
  adj j := by
    change Γ.Adj (t ^ (j / (m : ℤ)) • γ.vert (j % (m : ℤ)).toNat)
      (t ^ ((j + 1) / (m : ℤ)) • γ.vert ((j + 1) % (m : ℤ)).toNat)
    have hm0 : (0 : ℤ) < (m : ℤ) := by omega
    obtain ⟨he0, helt, hdec⟩ := div_mod_spec hm j
    set q : ℤ := j / (m : ℤ) with hq
    set e : ℤ := j % (m : ℤ) with he
    have he_int : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he0
    have he_lt : e.toNat < m := by omega
    have hdec' : e + (m : ℤ) * q = j := by
      rw [hq, he]
      exact hdec
    by_cases hlast : e + 1 = (m : ℤ)
    · have hdiv : (j + 1) / (m : ℤ) = q + 1 ∧ (j + 1) % (m : ℤ) = 0 := by
        rw [Int.ediv_emod_unique hm0]
        refine ⟨?_, le_rfl, hm0⟩
        rw [zero_add, mul_add, mul_one]
        omega
      have he_nat : e.toNat = m - 1 := by
        have h : (e.toNat : ℤ) = (m : ℤ) - 1 := by omega
        have h2 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
          rw [Nat.cast_sub hm, Nat.cast_one]
        omega
      have hgi : Γ.Adj (γ.vert (m - 1)) (γ.vert m) := by
        have h0 := γ.adj (m - 1) (by omega)
        rwa [Nat.sub_add_cancel hm] at h0
      rw [hdiv.1, hdiv.2, he_nat]
      simp only [Int.toNat_zero]
      rw [zpow_add, zpow_one, mul_smul, h0]
      exact (hadj (t ^ q) _ _).2 hgi
    · have hlt : e + 1 < (m : ℤ) := by omega
      have hdiv : (j + 1) / (m : ℤ) = q ∧ (j + 1) % (m : ℤ) = e + 1 := by
        rw [Int.ediv_emod_unique hm0]
        exact ⟨by omega, by omega, by omega⟩
      have hstep : (e + 1).toNat = e.toNat + 1 := by omega
      rw [hdiv.1, hdiv.2, hstep]
      exact (hadj (t ^ q) _ _).2 (γ.adj e.toNat he_lt)
  nb j := by
    change t ^ (j / (m : ℤ)) • γ.vert (j % (m : ℤ)).toNat ≠
      t ^ ((j + 2) / (m : ℤ)) • γ.vert ((j + 2) % (m : ℤ)).toNat
    have hm0 : (0 : ℤ) < (m : ℤ) := by omega
    obtain ⟨he0, helt, hdec⟩ := div_mod_spec hm j
    set q : ℤ := j / (m : ℤ) with hq
    set e : ℤ := j % (m : ℤ) with he
    have he_int : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he0
    have hdec' : e + (m : ℤ) * q = j := by
      rw [hq, he]
      exact hdec
    by_cases hlt2 : e + 2 < (m : ℤ)
    · have hdiv : (j + 2) / (m : ℤ) = q ∧ (j + 2) % (m : ℤ) = e + 2 := by
        rw [Int.ediv_emod_unique hm0]
        exact ⟨by omega, by omega, by omega⟩
      have hstep : (e + 2).toNat = e.toNat + 2 := by omega
      have he2 : e.toNat + 2 ≤ m := by
        have h : (e.toNat : ℤ) + 2 ≤ (m : ℤ) := by omega
        have h' : ((e.toNat + 2 : ℕ) : ℤ) ≤ (m : ℤ) := by
          rw [Nat.cast_add, Nat.cast_ofNat]
          exact h
        exact (Nat.cast_le (α := ℤ)).1 h'
      have hgn : γ.vert e.toNat ≠ γ.vert (e.toNat + 2) := γ.nb e.toNat he2
      rw [hdiv.1, hdiv.2, hstep]
      intro h
      exact hgn ((MulAction.injective (t ^ q)) h)
    · by_cases heq2 : e + 2 = (m : ℤ)
      · have hdiv : (j + 2) / (m : ℤ) = q + 1 ∧ (j + 2) % (m : ℤ) = 0 := by
          rw [Int.ediv_emod_unique hm0]
          refine ⟨?_, le_rfl, hm0⟩
          rw [zero_add, mul_add, mul_one]
          omega
        have he_nat : e.toNat = m - 2 := by
          have h : (e.toNat : ℤ) = (m : ℤ) - 2 := by omega
          have h2 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by
            rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
          omega
        have hgn : γ.vert (m - 2) ≠ γ.vert ((m - 2) + 2) := γ.nb (m - 2) (by omega)
        rw [show (m - 2) + 2 = m by omega] at hgn
        rw [hdiv.1, hdiv.2, he_nat]
        simp only [Int.toNat_zero]
        rw [zpow_add, zpow_one, mul_smul, h0]
        intro h
        exact hgn ((MulAction.injective (t ^ q)) h)
      · have hlast : e + 2 = (m : ℤ) + 1 := by omega
        by_cases hm1 : m = 1
        · subst hm1
          rw [hq, he]
          simp only [Nat.cast_one, Int.ediv_one, Int.emod_one, Int.toNat_zero]
          intro h
          rw [zpow_add, mul_smul] at h
          have h' : γ.vert 0 = t ^ (2 : ℤ) • γ.vert 0 := (MulAction.injective (t ^ j)) h
          have ht2 : t ^ (2 : ℤ) • γ.vert 0 = t • γ.vert 1 := by
            rw [show (2 : ℤ) = 1 + 1 by omega, zpow_add, zpow_one, mul_smul, h0]
          have h1' : t • γ.vert 1 ≠ γ.vert 0 := by simpa using h1
          rw [ht2] at h'
          exact h1' h'.symm
        · have hm2 : 2 ≤ m := by omega
          have hdiv : (j + 2) / (m : ℤ) = q + 1 ∧ (j + 2) % (m : ℤ) = 1 := by
            rw [Int.ediv_emod_unique hm0]
            refine ⟨?_, by omega, by omega⟩
            rw [mul_add, mul_one]
            omega
          have he_nat : e.toNat = m - 1 := by
            have h : (e.toNat : ℤ) = (m : ℤ) - 1 := by omega
            have h2 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
              rw [Nat.cast_sub hm, Nat.cast_one]
            omega
          rw [hdiv.1, hdiv.2, he_nat]
          simp only [Int.toNat_one]
          rw [zpow_add, zpow_one, mul_smul]
          intro h
          have h' : γ.vert (m - 1) = t • γ.vert 1 := (MulAction.injective (t ^ q)) h
          exact h1 h'.symm

theorem ofTranslate_vert (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {m : ℕ} (hm : 1 ≤ m) (γ : Arc Γ m) (t : G) (h0 : t • γ.vert 0 = γ.vert m)
    (h1 : t • γ.vert 1 ≠ γ.vert (m - 1)) {i : ℕ} (hi : i ≤ m) :
    (ofTranslate hadj hm γ t h0 h1).vert (i : ℤ) = γ.vert i := by
  change t ^ ((i : ℤ) / (m : ℤ)) • γ.vert ((i : ℤ) % (m : ℤ)).toNat = γ.vert i
  have hm0 : (0 : ℤ) < (m : ℤ) := by omega
  by_cases him : i = m
  · rw [him]
    have hdiv : (m : ℤ) / (m : ℤ) = 1 ∧ (m : ℤ) % (m : ℤ) = 0 := by
      rw [Int.ediv_emod_unique hm0]
      exact ⟨by omega, le_rfl, hm0⟩
    rw [hdiv.1, hdiv.2]
    simp only [Int.toNat_zero, zpow_one]
    exact h0
  · have hlt : i < m := by omega
    have hdiv : (i : ℤ) / (m : ℤ) = 0 ∧ (i : ℤ) % (m : ℤ) = (i : ℤ) := by
      rw [Int.ediv_emod_unique hm0]
      exact ⟨by omega, Int.natCast_nonneg i, by omega⟩
    rw [hdiv.1, hdiv.2]
    simp only [Int.toNat_natCast, zpow_zero, one_smul]

theorem ofTranslate_fix (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {m : ℕ} (hm : 1 ≤ m) (γ : Arc Γ m) (t : G) (h0 : t • γ.vert 0 = γ.vert m)
    (h1 : t • γ.vert 1 ≠ γ.vert (m - 1)) {c : G} (hct : Commute c t)
    (hc : ∀ i : ℕ, i ≤ m → c • γ.vert i = γ.vert i) (j : ℤ) :
    c • (ofTranslate hadj hm γ t h0 h1).vert j =
      (ofTranslate hadj hm γ t h0 h1).vert j := by
  change c • (t ^ (j / (m : ℤ)) • γ.vert (j % (m : ℤ)).toNat) =
    t ^ (j / (m : ℤ)) • γ.vert (j % (m : ℤ)).toNat
  obtain ⟨he0, helt, hdec⟩ := div_mod_spec hm j
  set q : ℤ := j / (m : ℤ) with hq
  set e : ℤ := j % (m : ℤ) with he
  have he_int : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he0
  have he_le : e.toNat ≤ m := by omega
  calc c • (t ^ q • γ.vert e.toNat)
      = (c * t ^ q) • γ.vert e.toNat := (mul_smul ..).symm
    _ = (t ^ q * c) • γ.vert e.toNat := by rw [(hct.zpow_right q).eq]
    _ = t ^ q • (c • γ.vert e.toNat) := mul_smul ..
    _ = t ^ q • γ.vert e.toNat := by rw [hc e.toNat he_le]

end Translate

private def gammaVert {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} (β : Arc Γ ℓ) (b : G)
    (e : ℕ) : V :=
  if e ≤ ℓ then β.vert e else b • β.vert (2 * ℓ - e)

private lemma gammaVert_of_le {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} {β : Arc Γ ℓ}
    {b : G} {e : ℕ} (he : e ≤ ℓ) : gammaVert β b e = β.vert e := by
  simp [gammaVert, he]

private lemma gammaVert_of_lt {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} {β : Arc Γ ℓ}
    {b : G} {e : ℕ} (he : ℓ < e) : gammaVert β b e = b • β.vert (2 * ℓ - e) := by
  simp [gammaVert, not_le.2 he]

private lemma gammaVert_last {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (β : Arc Γ ℓ) {b : G} : gammaVert β b (2 * ℓ) = b • β.vert 0 := by
  rw [gammaVert_of_lt (β := β) (b := b) (by omega), Nat.sub_self]

private lemma gammaVert_last_one {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (β : Arc Γ ℓ) {b : G} (hbℓ : b • β.vert ℓ = β.vert ℓ) :
    gammaVert β b (2 * ℓ - 1) = b • β.vert 1 := by
  by_cases h : 2 * ℓ - 1 ≤ ℓ
  · have hℓ1 : ℓ = 1 := by omega
    subst hℓ1
    rw [gammaVert_of_le (β := β) (b := b) h]
    rw [show 2 * 1 - 1 = 1 by omega]
    exact hbℓ.symm
  · rw [gammaVert_of_lt (β := β) (b := b) (by omega)]
    have h2 : 2 * ℓ - (2 * ℓ - 1) = 1 := by omega
    rw [h2]

private def gamma {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (β : Arc Γ ℓ) {b : G}
    (hbℓ : b • β.vert ℓ = β.vert ℓ)
    (hbℓ1 : b • β.vert (ℓ - 1) ≠ β.vert (ℓ - 1)) : Arc Γ (2 * ℓ) where
  vert := gammaVert β b
  adj i hi := by
    by_cases h1 : i + 1 ≤ ℓ
    · rw [gammaVert_of_le (β := β) (b := b) (by omega), gammaVert_of_le (β := β) (b := b) h1]
      exact β.adj i (by omega)
    · have hℓi : ℓ ≤ i := by omega
      rcases eq_or_lt_of_le hℓi with rfl | hlt
      · rw [gammaVert_of_le (β := β) (b := b) le_rfl,
          gammaVert_of_lt (β := β) (b := b) (by omega)]
        rw [show 2 * ℓ - (ℓ + 1) = ℓ - 1 by omega]
        have hb : Γ.Adj (b • β.vert (ℓ - 1)) (b • β.vert ℓ) := by
          have h0 := (hadj b (β.vert (ℓ - 1)) (β.vert ((ℓ - 1) + 1))).2
            (β.adj (ℓ - 1) (by omega))
          rwa [show (ℓ - 1) + 1 = ℓ by omega] at h0
        rw [hbℓ] at hb
        exact hb.symm
      · rw [gammaVert_of_lt (β := β) (b := b) hlt,
          gammaVert_of_lt (β := β) (b := b) (by omega)]
        rw [show 2 * ℓ - i = (2 * ℓ - (i + 1)) + 1 by omega]
        exact ((hadj b _ _).2 (β.adj (2 * ℓ - (i + 1)) (by omega))).symm
  nb i hi := by
    by_cases h2 : i + 2 ≤ ℓ
    · rw [gammaVert_of_le (β := β) (b := b) (by omega), gammaVert_of_le (β := β) (b := b) h2]
      exact β.nb i h2
    · by_cases h1 : i + 1 ≤ ℓ
      · have hi' : i = ℓ - 1 := by omega
        rw [hi']
        rw [gammaVert_of_le (β := β) (b := b) (by omega),
          gammaVert_of_lt (β := β) (b := b) (by omega)]
        rw [show 2 * ℓ - (ℓ - 1 + 2) = ℓ - 1 by omega]
        exact fun h => hbℓ1 h.symm
      · by_cases heq : i = ℓ
        · rw [heq]
          rw [gammaVert_of_le (β := β) (b := b) le_rfl,
            gammaVert_of_lt (β := β) (b := b) (by omega)]
          rw [show 2 * ℓ - (ℓ + 2) = ℓ - 2 by omega]
          intro h
          refine (β.nb (ℓ - 2) (by omega)) ?_
          rw [show ℓ - 2 + 2 = ℓ by omega]
          have hb : b • β.vert ℓ = b • β.vert (ℓ - 2) := by
            rw [hbℓ]
            exact h
          exact ((MulAction.injective b) hb).symm
        · have hlt : ℓ < i := by omega
          rw [gammaVert_of_lt (β := β) (b := b) hlt,
            gammaVert_of_lt (β := β) (b := b) (by omega)]
          intro h
          have hab : β.vert (2 * ℓ - i) = β.vert (2 * ℓ - (i + 2)) :=
            (MulAction.injective b) h
          rw [show 2 * ℓ - i = (2 * ℓ - (i + 2)) + 2 by omega] at hab
          exact (β.nb (2 * ℓ - (i + 2)) (by omega)) hab.symm

private lemma gamma_smul_zero {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (β : Arc Γ ℓ) {a b : G} (ha0 : a • β.vert 0 = β.vert 0) :
    (b * a) • gammaVert β b 0 = gammaVert β b (2 * ℓ) := by
  rw [gammaVert_of_le (β := β) (b := b) (Nat.zero_le ℓ), gammaVert_last hℓ β, mul_smul, ha0]

private lemma gamma_smul_one_ne {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (β : Arc Γ ℓ) {a b : G} (ha1 : a • β.vert 1 ≠ β.vert 1)
    (hbℓ : b • β.vert ℓ = β.vert ℓ) :
    (b * a) • gammaVert β b 1 ≠ gammaVert β b (2 * ℓ - 1) := by
  intro h
  rw [gammaVert_of_le (β := β) (b := b) hℓ, mul_smul, gammaVert_last_one hℓ β hbℓ] at h
  exact ha1 ((MulAction.injective b) h)

private lemma gammaVert_fix {G : Type*} [Group G] [MulAction G V] {ℓ : ℕ} (β : Arc Γ ℓ)
    {b c : G} (hcb : Commute c b) (hc : ∀ i : ℕ, i ≤ ℓ → c • β.vert i = β.vert i) (e : ℕ) :
    c • gammaVert β b e = gammaVert β b e := by
  by_cases he : e ≤ ℓ
  · rw [gammaVert_of_le (β := β) (b := b) he, hc e he]
  · rw [gammaVert_of_lt (β := β) (b := b) (not_le.1 he)]
    have hbc : c • (b • β.vert (2 * ℓ - e)) = b • (c • β.vert (2 * ℓ - e)) := by
      calc c • (b • β.vert (2 * ℓ - e)) = (c * b) • β.vert (2 * ℓ - e) :=
            (mul_smul ..).symm
        _ = (b * c) • β.vert (2 * ℓ - e) := by rw [hcb.eq]
        _ = b • (c • β.vert (2 * ℓ - e)) := mul_smul ..
    rw [hbc, hc (2 * ℓ - e) (by omega)]

theorem exists_of_pair {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (β : Arc Γ ℓ) {a b : G}
    (ha0 : a • β.vert 0 = β.vert 0) (ha1 : a • β.vert 1 ≠ β.vert 1)
    (hbℓ : b • β.vert ℓ = β.vert ℓ) (hbℓ1 : b • β.vert (ℓ - 1) ≠ β.vert (ℓ - 1)) :
    ∃ L : Line Γ, (∀ i : ℕ, i ≤ ℓ → L.vert i = β.vert i) ∧
      ∀ c : G, Commute c a → Commute c b → (∀ i : ℕ, i ≤ ℓ → c • β.vert i = β.vert i) →
        ∀ j : ℤ, c • L.vert j = L.vert j := by
  let γ : Arc Γ (2 * ℓ) := gamma hadj hℓ β hbℓ hbℓ1
  let t : G := b * a
  have ht0 : t • γ.vert 0 = γ.vert (2 * ℓ) := by
    dsimp only [γ, t]
    exact gamma_smul_zero hℓ β ha0
  have ht1 : t • γ.vert 1 ≠ γ.vert (2 * ℓ - 1) := by
    dsimp only [γ, t]
    exact gamma_smul_one_ne hℓ β ha1 hbℓ
  let L : Line Γ := ofTranslate hadj (by omega : 1 ≤ 2 * ℓ) γ t ht0 ht1
  refine ⟨L, ?_, ?_⟩
  · intro i hi
    have hL := ofTranslate_vert hadj (by omega : 1 ≤ 2 * ℓ) γ t ht0 ht1 (i := i) (by omega)
    dsimp only [L] at hL ⊢
    rw [hL]
    exact gammaVert_of_le hi
  · intro c hca hcb hc j
    have hct : Commute c t := by
      dsimp only [t]
      exact hcb.mul_right hca
    refine ofTranslate_fix hadj (by omega : 1 ≤ 2 * ℓ) γ t ht0 ht1 hct ?_ j
    intro i hi
    dsimp only [γ]
    exact gammaVert_fix β hcb hc i

end Line

end CFSG.Quasithin.Fan86
