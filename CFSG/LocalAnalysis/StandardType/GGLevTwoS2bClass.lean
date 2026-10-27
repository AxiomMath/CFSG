module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bZc
import Mathlib.Algebra.Field.ZMod
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCoord
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bForm
public import CFSG.LocalAnalysis.StandardType.GGLevTwoTrans
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin
open scoped Matrix

theorem levTwoS2b_det_cartanB (n : ℕ) (hn : 1 ≤ n) :
    (CFSG.LieType.Universal.Spin.cartanB n).det = 2 := by
  rw [CFSG.LieType.Universal.Spin.cartanB_eq_transpose, Matrix.det_transpose]
  exact CartanMatrix.B_det (by omega)

private theorem levTwoS2b_not_dvd_det {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n)
    (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ (CFSG.LieType.Universal.Spin.cartanB n).det := by
  rw [levTwoS2b_det_cartanB n hn]
  intro h
  have h2 : p ∣ 2 := by exact_mod_cast h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

theorem levTwoS2b_Supp_subset_Z_of_single {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n)
    (hp2 : p ≠ 2) (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) {k : Fin n}
    (hk : levTwoS2b_D c k ≠ 0) (hZ : ∀ a : Fin n, a ≠ k → levTwoS2b_D c a = 0) :
    levTwoS2b_Supp n c Φ ⊆ levTwoS2b_Z c := by
  rintro a ⟨β, hβ, haβ⟩
  simp only [levTwoS2b_Z, Set.mem_setOf_eq]
  have hlong := levTwoS2b_isLong_of_mem_Phi n hn Fact.out hp2 c hΦ hβ
  obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ := hlong
  have hβeq : β = levTwoS2b_ofCoord n (Pi.single i si + Pi.single j sj) := by
    apply levTwoS2b_coord_injective n
    rw [levTwoS2b_coord_ofCoord, hcoord]
  have hlam := hΦ.fix β hβ
  rw [hβeq, levTwoS2b_lam_eps_gen n p c hij] at hlam
  have hik : i ≠ k := by
    intro hik
    have hjk : j ≠ k := by rintro rfl; exact hij hik
    have hj0 : levTwoS2b_D c j = 0 := hZ j hjk
    rw [hik, hj0, mul_zero, add_zero] at hlam
    exact hk ((mul_eq_zero.mp hlam).resolve_left (levTwoS2b_intCast_ne_zero' (p := p) hsi))
  have hjk : j ≠ k := by
    intro hjk
    have hik : i ≠ k := by rintro rfl; exact hij hjk.symm
    have hi0 : levTwoS2b_D c i = 0 := hZ i hik
    rw [hjk, hi0, mul_zero, zero_add] at hlam
    exact hk ((mul_eq_zero.mp hlam).resolve_left (levTwoS2b_intCast_ne_zero' (p := p) hsj))
  have hmem : a = i ∨ a = j := by
    rw [hcoord] at haβ
    simp only [Pi.add_apply, Pi.single_apply] at haβ
    by_cases hai : a = i
    · exact Or.inl hai
    · by_cases haj : a = j
      · exact Or.inr haj
      · simp [hai, haj] at haβ
  rcases hmem with h | h
  · rw [h]; exact hZ i hik
  · rw [h]; exact hZ j hjk

theorem levTwoS2b_classification {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) :
    (∀ a, levTwoS2b_D c a = 0) ∨
    (∃ (k : Fin n) (c₀ : ZMod p), c₀ ≠ 0 ∧
      (levTwoS2b_D c k = c₀ ∨ levTwoS2b_D c k = -c₀) ∧
      ∀ a, a ≠ k → levTwoS2b_D c a = 0) ∨
    (∃ c₀ : ZMod p, c₀ ≠ 0 ∧ ∀ a, levTwoS2b_D c a = c₀ ∨ levTwoS2b_D c a = -c₀) := by
  classical
  obtain ⟨s, hsΦ, hlin, hcard3, hcard2, hdet⟩ := hΦ.rank
  have hp_not_dvd : ¬ (p : ℤ) ∣ (CFSG.LieType.Universal.Spin.cartanB n).det :=
    levTwoS2b_not_dvd_det n (by omega) hp2
  have hscard : n ≤ s.card + 1 := by
    rcases hdet with h | h
    · simpa [Fintype.card_fin] using h
    · exact absurd h hp_not_dvd
  set Z := levTwoS2b_Z c with hZdef
  set SZ : Finset (Fin n) := Finset.univ.filter (fun a => a ∈ Z) with hSZdef
  have hSZmem : ∀ a, a ∈ SZ ↔ a ∈ Z := by intro a; simp [hSZdef]
  have hSZcard : SZ.card = Nat.card Z := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set Supp := levTwoS2b_Supp n c Φ with hSuppdef
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
  rcases levTwoS2b_Supp_subset n hn hp2 c hΦ with hZ | hZc
  ·
    have hleZ := levTwoS2b_card_le_Z n (by omega) hp2 c hΦ hsΦ hlin hZ
    have hSZge : n - 1 ≤ SZ.card := by rw [hSZcard, hZdef]; omega
    rcases (by omega : SZ.card = n ∨ SZ.card = n - 1) with hZn | hZn1
    · left
      intro a
      have : a ∈ Z := by
        have : a ∈ SZ := by
          rw [Finset.eq_univ_of_card SZ (by rw [hZn, Fintype.card_fin])]
          exact Finset.mem_univ a
        exact (hSZmem a).mp this
      exact this
    · right; left
      have hproper : SZ ≠ Finset.univ := by
        intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hZn1; omega
      obtain ⟨k, hk⟩ : ∃ k, k ∉ SZ := by
        by_contra h; push Not at h
        exact hproper (Finset.eq_univ_of_forall h)
      have hkZ : k ∉ Z := fun hkZ => hk ((hSZmem k).mpr hkZ)
      refine ⟨k, levTwoS2b_D c k, hkZ, Or.inl rfl, ?_⟩
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
    have hleS := levTwoS2b_card_le_Supp n hn hp2 c hΦ hsΦ hlin hZc
    have hSSge : n ≤ SS.card := by rw [hSScard, hSuppdef]; omega
    have hSSn : SS.card = n := le_antisymm hSSle hSSge
    have hSupp_univ : ∀ a, a ∈ Supp := by
      intro a
      have : a ∈ SS := by
        rw [Finset.eq_univ_of_card SS (by rw [hSSn, Fintype.card_fin])]
        exact Finset.mem_univ a
      exact (hSSmem a).mp this
    rcases levTwoS2b_Phi_side_abs n hn hp2 c hΦ with hZ' | ⟨c₀, hc₀, hQ⟩
    · exfalso
      obtain ⟨β, hβ⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      have hβΦ : β ∈ Φ := hsΦ (Finset.mem_coe.mpr hβ)
      obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ :=
        levTwoS2b_isLong_of_mem_Phi n hn Fact.out hp2 c hΦ hβΦ
      have hi : levTwoS2b_coord n β i ≠ 0 := by
        rw [hcoord]; simp only [Pi.add_apply, Pi.single_apply]
        rcases hsi with rfl | rfl <;> simp [hij]
      exact hZc ⟨β, hβΦ, hi⟩ (hZ' β hβΦ i hi)
    · right; right
      refine ⟨c₀, hc₀, fun a => ?_⟩
      obtain ⟨β, hβΦ, ha⟩ := hSupp_univ a
      exact hQ β hβΦ a ha

theorem levTwoS2b_Phi_cases (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) p c Φ) :
    Φ = levTwoS2b_allLong n ∨
      (∃ k : Fin n, 3 ≤ n - 1 ∧ levTwoS2b_D c k ≠ 0 ∧
        (∀ a : Fin n, a ≠ k → levTwoS2b_D c a = 0) ∧ Φ = levTwoS2b_PhiCase2 n k) ∨
      (∃ (a₀ : Fin n) (η : Fin n → ℤ), (∀ a : Fin n, η a = 1 ∨ η a = -1) ∧
        levTwoS2b_D c a₀ ≠ 0 ∧
        (∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀) ∧
        Φ = levTwoS2b_PhiCase3 n p c) := by
  have : Fact p.Prime := ⟨hp⟩
  have hΦ3 := levTwoS2b_Phi_eq_PhiCase3 n hn p hp hp2 c Φ h
  have hn1 : 1 ≤ n := by omega
  rcases levTwoS2b_classification n hn hp2 c h with hD | ⟨k, c₀, hc₀, hk, hZ⟩ | ⟨c₀, hc₀, hc⟩
  · left
    rw [hΦ3]
    exact levTwoS2b_allLong_of_D_zero n p c hD
  · right; left
    have hkne : levTwoS2b_D c k ≠ 0 := by
      rcases hk with hk | hk
      · rw [hk]; exact hc₀
      · rw [hk]; exact neg_ne_zero.mpr hc₀
    refine ⟨k, ?_, hkne, hZ, ?_⟩
    · have hSuppZ := levTwoS2b_Supp_subset_Z_of_single n hn hp2 c h hkne hZ
      obtain ⟨s, hsΦ, hlin, h3, -, -⟩ := h.rank
      have hle := levTwoS2b_card_le_Z n hn1 hp2 c h hsΦ hlin hSuppZ
      have hZcard : Nat.card (levTwoS2b_Z c) = n - 1 := by
        have hset : levTwoS2b_Z c = {a : Fin n | a ≠ k} := by
          ext a
          simp only [levTwoS2b_Z, Set.mem_setOf_eq]
          constructor
          · intro ha; rintro rfl; exact hkne ha
          · intro ha; exact hZ a ha
        rw [hset]
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp only [Set.mem_setOf_eq]
        have hfil : (Finset.univ.filter (fun a : Fin n => a ≠ k)) = Finset.univ.erase k := by
          ext a; simp [Finset.mem_erase, and_comm]
        rw [hfil, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
          Fintype.card_fin]
      omega
    · rw [hΦ3]
      exact levTwoS2b_case2_of_single_nonzero n p hp c k hkne hZ
  · right; right
    have hne : ∀ a : Fin n, levTwoS2b_D c a ≠ 0 := by
      intro a h0
      rcases hc a with ha | ha <;> rw [ha] at h0
      · exact hc₀ h0
      · exact hc₀ (neg_eq_zero.mp h0)
    have hclass : ∀ a b : Fin n, levTwoS2b_D c a = levTwoS2b_D c b ∨
        levTwoS2b_D c a = - levTwoS2b_D c b := by
      intro a b
      rcases hc a with ha | ha <;> rcases hc b with hb | hb
      · exact Or.inl (ha.trans hb.symm)
      · exact Or.inr (by rw [ha, hb]; exact (neg_neg c₀).symm)
      · exact Or.inr (by rw [ha, hb])
      · exact Or.inl (by rw [ha, hb])
    obtain ⟨a₀, η, hη, h0, hD⟩ := levTwoS2b_eta_of_support_all n hn1 p c hne hclass
    exact ⟨a₀, η, hη, h0, hD, hΦ3⟩

end CFSG.StandardType.LevTwo
