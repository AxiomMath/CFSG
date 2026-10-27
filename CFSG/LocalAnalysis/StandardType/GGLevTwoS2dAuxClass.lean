module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxPhi
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxFormCoord
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxRank
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxZc
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2d_mem_Phi_iff {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ)
    {a b : Fin n} (hab : a ≠ b) {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    {β : Fin n → ℤ} (hβ : toStdD n β = Pi.single a s + Pi.single b t) :
    β ∈ Φ ↔ (s : ZMod p) * levTwoS2d_d n hn c a + (t : ZMod p) * levTwoS2d_d n hn c b = 0 := by
  rw [levTwoS2d_Phi_eq_lambda n hn p hp2 c hΦ]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hlam⟩
    rwa [levTwoS2d_lam_eps n hn hp2 c hβ] at hlam
  · intro hlam
    refine ⟨?_, ?_⟩
    · rw [levTwoS2d_isRt_iff n (by omega) β]
      exact ⟨a, b, s, t, hab, hs, ht, hβ⟩
    · rwa [levTwoS2d_lam_eps n hn hp2 c hβ]

theorem levTwoS2d_mem_Phi_diff {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {a b : Fin n} (hab : a ≠ b)
    {β : Fin n → ℤ} (hβ : toStdD n β = Pi.single a 1 - Pi.single b 1) :
    β ∈ Φ ↔ levTwoS2d_d n hn c a = levTwoS2d_d n hn c b := by
  have hβ' : toStdD n β = Pi.single a (1 : ℤ) + Pi.single b (-1) := by
    rw [hβ, Pi.single_neg, sub_eq_add_neg]
  rw [levTwoS2d_mem_Phi_iff n hn hp2 c hΦ hab (Or.inl rfl) (Or.inr rfl) hβ']
  simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
  exact add_neg_eq_zero

theorem levTwoS2d_mem_Phi_add {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {a b : Fin n} (hab : a ≠ b)
    {β : Fin n → ℤ} (hβ : toStdD n β = Pi.single a 1 + Pi.single b 1) :
    β ∈ Φ ↔ levTwoS2d_d n hn c a = - levTwoS2d_d n hn c b := by
  rw [levTwoS2d_mem_Phi_iff n hn hp2 c hΦ hab (Or.inl rfl) (Or.inl rfl) hβ]
  simp only [Int.cast_one, one_mul]
  exact eq_neg_iff_add_eq_zero.symm

theorem levTwoS2d_d_eq_zero_of_eq_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {x : ZMod p} (h : x = - x) : x = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hzero
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hx : (2 : ZMod p) * x = 0 := by
    rw [two_mul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (mul_eq_zero.mp hx).resolve_left h2

private theorem levTwoS2d_not_dvd_det {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (cartanD n).det := by
  rw [show (cartanD n).det = 4 from by rw [cartanD_eq]; exact CartanMatrix.D_det hn]
  intro h
  have h4 : p ∣ 4 := by exact_mod_cast h
  have hp_ge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases p
  · exact hp2 rfl
  · norm_num at h4
  · exact absurd (Fact.out : Nat.Prime 4) (by norm_num)

theorem levTwoS2d_classification {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) :
    (∀ a, levTwoS2d_d n hn c a = 0) ∨
    (∃ (k : Fin n) (c₀ : ZMod p), c₀ ≠ 0 ∧
      (levTwoS2d_d n hn c k = c₀ ∨ levTwoS2d_d n hn c k = -c₀) ∧
      ∀ a, a ≠ k → levTwoS2d_d n hn c a = 0) ∨
    (∃ c₀ : ZMod p, c₀ ≠ 0 ∧
      ∀ a, levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀) := by
  classical
  obtain ⟨s, hsΦ, hlin, hcard3, hcard2, hdet⟩ := hΦ.rank
  have hp_not_dvd : ¬ (p : ℤ) ∣ (cartanD n).det := levTwoS2d_not_dvd_det n (by omega) hp2
  have hscard : n ≤ s.card + 1 := by
    rcases hdet with h | h
    · simpa [Fintype.card_fin] using h
    · exact absurd h hp_not_dvd
  set Z := levTwoS2d_Z n hn c with hZdef
  set SZ : Finset (Fin n) := Finset.univ.filter (fun a => a ∈ Z) with hSZdef
  have hSZmem : ∀ a, a ∈ SZ ↔ a ∈ Z := by intro a; simp [hSZdef]
  have hSZcard : SZ.card = Nat.card Z := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set Supp := levTwoS2d_Supp n hn c Φ with hSuppdef
  set SS : Finset (Fin n) := Finset.univ.filter (fun a => a ∈ Supp) with hSSdef
  have hSSmem : ∀ a, a ∈ SS ↔ a ∈ Supp := by intro a; simp [hSSdef]
  have hSScard : SS.card = Nat.card Supp := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hSZle : SZ.card ≤ n := by
    calc SZ.card ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by simp
  have hSSle : SS.card ≤ n := by
    calc SS.card ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by simp
  rcases levTwoS2d_Supp_subset n hn hp2 c hΦ with hZ | hZc
  ·
    have hleZ := levTwoS2d_card_le_Z n hn hp2 c hΦ hsΦ hlin hZ
    have hSZge : n - 1 ≤ SZ.card := by rw [hSZcard, hZdef]; omega
    rcases (by omega : SZ.card = n ∨ SZ.card = n - 1) with hZn | hZn1
    · left
      intro a
      have : a ∈ Z := by
        have : a ∈ SZ := by rw [Finset.eq_univ_of_card SZ (by rw [hZn, Fintype.card_fin])]; exact Finset.mem_univ a
        exact (hSZmem a).mp this
      exact this
    · right; left
      have hproper : SZ ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hZn1; omega
      obtain ⟨k, hk⟩ : ∃ k, k ∉ SZ := by
        by_contra h; push Not at h
        exact hproper (Finset.eq_univ_of_forall h)
      have hkZ : k ∉ Z := fun hkZ => hk ((hSZmem k).mpr hkZ)
      refine ⟨k, levTwoS2d_d n hn c k, hkZ, Or.inl rfl, ?_⟩
      intro a ha
      by_contra haZ
      have haSZ : a ∉ SZ := fun h => haZ ((hSZmem a).mp h)
      have hle2 : SZ.card ≤ n - 2 := by
        have hsub : SZ ⊆ (Finset.univ.erase k).erase a := by
          intro x hx
          rw [Finset.mem_erase, Finset.mem_erase]
          exact ⟨fun hxa => haSZ (by rw [← hxa]; exact hx),
            fun hxk => hk (by rw [← hxk]; exact hx), Finset.mem_univ x⟩
        calc SZ.card ≤ ((Finset.univ.erase k).erase a).card := Finset.card_le_card hsub
          _ = n - 2 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩),
              Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
            simp only [Fintype.card_fin]; omega
      omega
  ·
    have hleS := levTwoS2d_card_le_Supp n hn hp2 c hΦ hsΦ hlin hZc
    have hSSge : n ≤ SS.card := by rw [hSScard, hSuppdef]; omega
    have hSSn : SS.card = n := le_antisymm hSSle hSSge
    have hSupp_univ : ∀ a, a ∈ Supp := by
      intro a
      have : a ∈ SS := by rw [Finset.eq_univ_of_card SS (by rw [hSSn, Fintype.card_fin])]; exact Finset.mem_univ a
      exact (hSSmem a).mp this
    rcases levTwoS2d_Phi_side_abs n hn hp2 c hΦ with hZ' | ⟨c₀, hc₀, hQ⟩
    · exfalso
      obtain ⟨β, hβ⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      have hβΦ : β ∈ Φ := hsΦ (Finset.mem_coe.mpr hβ)
      obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ :=
        (levTwoS2d_isRt_iff n (by omega) β).1 (hΦ.isRt β hβΦ)
      have hi : toStdD n β i ≠ 0 := by
        rw [hcoord]; simp only [Pi.add_apply, Pi.single_apply]
        rcases hsi with rfl | rfl <;> simp [hij]
      exact hZc ⟨β, hβΦ, hi⟩ (hZ' β hβΦ i hi)
    · right; right
      refine ⟨c₀, hc₀, fun a => ?_⟩
      obtain ⟨β, hβΦ, ha⟩ := hSupp_univ a
      exact hQ β hβΦ a ha

end CFSG.StandardType.LevTwo
