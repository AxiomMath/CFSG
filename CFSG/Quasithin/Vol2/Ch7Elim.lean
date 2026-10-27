module

public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem fsuL0_eq_of_le_normalizer (h : T ≤ Subgroup.normalizer (L : Set G)) :
    fsuL0 T L = L := by
  apply le_antisymm
  · rw [fsuL0, conjClosure, Subgroup.closure_le]
    rintro _ ⟨t, ht, l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (h ht) l).mp hl
  · exact le_fsuL0 T L

omit [Finite G] in
theorem fsuM_le_normalizer_of_le_normalizer (h : T ≤ Subgroup.normalizer (L : Set G)) :
    fsuM T L ≤ Subgroup.normalizer (L : Set G) := by
  rw [fsuM, fsuL0_eq_of_le_normalizer h]

theorem le_of_fwci {r w β : ℕ∞} {m₂ k B c : ℕ} (hfw : r ≤ (m₂ : ℕ∞) + w) (hw : w ≤ k)
    (hr : β ≤ r) (hB : (B : ℕ∞) ≤ c * β) : B ≤ c * (m₂ + k) := by
  have h1 : β ≤ ((m₂ + k : ℕ) : ℕ∞) := by
    calc β ≤ r := hr
      _ ≤ m₂ + w := hfw
      _ ≤ m₂ + k := add_le_add_right hw _
      _ = ((m₂ + k : ℕ) : ℕ∞) := by push_cast; rfl
  have h2 : (B : ℕ∞) ≤ ((c * (m₂ + k) : ℕ) : ℕ∞) := by
    calc (B : ℕ∞) ≤ c * β := hB
      _ ≤ c * ((m₂ + k : ℕ) : ℕ∞) := mul_le_mul_right h1 _
      _ = ((c * (m₂ + k) : ℕ) : ℕ∞) := by push_cast; rfl
  exact_mod_cast h2

theorem stmt7_3_5_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h732 : Stmt7_3_2) (h734 : Stmt7_3_4)
    (h721 : Stmt7_2_1_Sp4Pair) : Stmt7_3_5 := by
  intro G _ _ T L I hyp h731 hc hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hm := h732 G T L I hyp h731 hV
  obtain ⟨-, hwn, -, hn'⟩ := h734 G T L I hyp h731 hV
  obtain ⟨-, -, -, -, -, hSp, hA6, -, -⟩ := hn' hc
  obtain ⟨htw, hrow'⟩ := hrow
  have htab := h721 G T L I hyp hV hN hNM hc htw
  have key : ∀ k : ℕ, nPrime (autI hV ⊤) = k → aParam (autI hV ⊤) < mParam (autI hV ⊤) →
      mParam (autI hV ⊤) - aParam (autI hV ⊤) ≤ k := by
    intro k hk ham
    have hw := lemma_7_3_3 hyp hV hN hm ham
    have h1 : ((mParam (autI hV ⊤) - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
      rw [← hk]
      exact hw.trans hwn
    exact_mod_cast h1
  rcases hrow' with ⟨n, hn2, hsp⟩ | halt
  · obtain ⟨ha, hm3⟩ := htab.1 n hn2 hsp
    have := key n (hSp n hn2 htw hsp) (by omega)
    omega
  · obtain ⟨ha, hm3⟩ := htab.2 halt
    have := key 1 (hA6 htw halt) (by omega)
    omega

theorem betaH_le_of_fwci (h734 : Stmt7_3_4) (h741 : Stmt7_4_1) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (hLM : fsuM T L ≤ Subgroup.normalizer (L : Set G)) (hα : alphaH (autI hV ⊤) = 1)
    {B c : ℕ} (hB : (B : ℕ∞) ≤ c * betaH (autI hV ⊤)) :
    B ≤ c * (CFSG.Open.pRank 2 (autI hV ⊤) + nPrime (autI hV ⊤)) := by
  have hfw := lemma_7_5_1 hyp hV hN hNM
  obtain ⟨-, hwn, -, -⟩ := h734 G T L I hyp h731 hV
  have hr := h741 G T L I hyp h731 hLM hV
  rw [alphaE_eq_top_of_alphaH_eq_one hα, min_top_left] at hr
  exact le_of_fwci hfw hwn hr hB

theorem stmt7_5_2_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h734 : Stmt7_3_4) (h741 : Stmt7_4_1)
    (hSU3 : Stmt7_2_1_SU3) (hSz : Stmt7_2_1_Sz) (hM22 : Stmt7_2_1_M22Hat)
    (hSL3 : Stmt7_2_1_SL3Pair) : Stmt7_5_2 := by
  intro G _ _ T L I hyp h731 hc
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨-, -, -, hn'⟩ := h734 G T L I hyp h731 hV
  obtain ⟨hkSU3, hkSz, -, hkM, hkSL3, -, -, -, -⟩ := hn' hc
  have key := betaH_le_of_fwci h734 h741 hyp h731 hV hN hNM
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨n, hn2, hrow⟩
    obtain ⟨-, -, hm2, hβ, hα⟩ := hSU3 G T L I hyp hV hNM hc n hn2 hrow
    have h1 := key (fsuM_le_normalizer_of_le_normalizer (h711 G T L I hyp hc
      (Or.inl ⟨n, hn2, hrow⟩))) hα (B := 4 * n) (c := 1) (by rw [Nat.cast_one, one_mul]; exact hβ)
    rw [hkSU3 n hn2 hrow] at h1
    omega
  · rintro ⟨n, hrow⟩
    obtain ⟨hm2, hβ, hα⟩ := hSz G T L I hyp hV hNM hc n hrow
    have h1 := key (fsuM_le_normalizer_of_le_normalizer (h711 G T L I hyp hc
      (Or.inr (Or.inl ⟨n, hrow⟩)))) hα (B := 8 * n) (c := 3) (by exact_mod_cast hβ)
    rw [hkSz n hrow] at h1
    obtain ⟨a, ha, rfl, -⟩ := hrow
    omega
  · intro hrow
    obtain ⟨hm2, hβ, hα⟩ := hM22 G T L I hyp hV hNM hc hrow
    have h1 := key (fsuM_le_normalizer_of_le_normalizer (h711 G T L I hyp hc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow))))))) hα (B := 8) (c := 1)
      (by rw [Nat.cast_one, one_mul]; exact_mod_cast hβ)
    rw [hkM (Or.inr (Or.inl hrow))] at h1
    omega
  · intro n hrow
    have hn0 : n ≠ 0 := by
      rintro rfl
      obtain ⟨-, K, _, _, hK, -⟩ := hrow
      have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
      rw [hK, pow_zero] at this
      exact lt_irrefl 1 this
    by_contra hn1
    have hn2 : 2 ≤ n := by omega
    obtain ⟨hm2, hβ, hα⟩ := hSL3 G T L I hyp hV hN hNM hc n hn2 hrow
    have hrow' : ∃ n : ℕ, Row711SL3Pair T L I n := ⟨n, hrow⟩
    have h1 := key (fsuM_le_normalizer_of_le_normalizer (h711 G T L I hyp hc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hrow')))))))))))))) hα (B := 4 * n) (c := 1)
      (by rw [Nat.cast_one, one_mul]; exact hβ)
    rw [hkSL3 n hrow] at h1
    omega

end CFSG.Quasithin.H13
