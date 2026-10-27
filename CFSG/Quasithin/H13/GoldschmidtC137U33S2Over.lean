module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Cases
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2CaseData

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

@[expose] def rword (r : ℕ) : List ℕ := if r = 0 then [] else [0]

@[expose] def bword : List ℕ := [1, 3, 1, 3]

@[expose] def caseWordB (j r : ℕ) : List ℕ := nWords.getD j [] ++ rword r ++ bword

theorem words_lt : ∀ j < 6, ∀ x ∈ nWords.getD j [], x < 4 := by
  decide +kernel

theorem caseWordB_lt (j r : ℕ) (hj : j < 6) : ∀ x ∈ caseWordB j r, x < 4 := by
  intro x hx
  simp only [caseWordB, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact words_lt j hj x hx
  · unfold rword at hx
    split_ifs at hx
    · simp at hx
    · simp only [List.mem_singleton] at hx
      omega
  · unfold bword at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

theorem caseA_ok : ∀ j < 5, caseOk (nWords.getD (j + 1) []) (certA.getD j ([], [])) = true := by
  decide +kernel

theorem caseB_ok : ∀ j < 6, ∀ r < 2,
    caseOk (caseWordB j r) (certB.getD (2 * j + r) ([], [])) = true := by
  decide +kernel

theorem decTab_ok : ∀ c ∈ omegaL, c ≠ 8 → ∃ e ∈ decTab, e.1 = c ∧ e.2.1 < 64 ∧ 1 ≤ e.2.2 ∧
    e.2.2 < 6 ∧ mact (sM e.2.1) (mact (wcode (nWords.getD e.2.2 [])) 8) = c := by
  decide +kernel

theorem splitOk : ∀ i < 64, (splitTab.getD i (0, 0, 0)).1 < 2 ∧
    (splitTab.getD i (0, 0, 0)).2.1 < 64 ∧ (splitTab.getD i (0, 0, 0)).2.2 < 64 ∧
    sM i = mmul (sM (splitTab.getD i (0, 0, 0)).1) (sM (splitTab.getD i (0, 0, 0)).2.1) ∧
    mmul (mmul (mmul bCode bCode) (sM (splitTab.getD i (0, 0, 0)).2.1)) bCode =
      sM (splitTab.getD i (0, 0, 0)).2.2 := by
  decide +kernel

theorem wd_rword (r : ℕ) (hr : r < 2) : wd (rword r) = sEltG r := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · simp [rword, wd, sEltG_zero]
  · simpa [rword] using wd0_eq

theorem wd_caseWordB (j r : ℕ) (hr : r < 2) :
    wd (caseWordB j r) = wd (nWords.getD j []) * sEltG r * b₀ := by
  rw [caseWordB, wd_append, wd_append, wd_rword r hr, bword, wdb_eq]

theorem cover {g : Gam} (hg : g ∉ Ppt) :
    (∃ j < 5, ∃ s ∈ sSubG, ∃ s' ∈ sSubG, g = s * wd (nWords.getD (j + 1) []) * s') ∨
    (∃ j < 6, ∃ r < 2, ∃ s ∈ sSubG, ∃ s' ∈ sSubG, g = s * wd (caseWordB j r) * s') := by
  have h8 : isPt 8 = true := by decide
  have hlt : (8 : ℕ) ∈ o0Codes := by decide
  have hc : act g 8 ∈ omegaL :=
    isPt_iff_mem _ (mact_mem_o0Codes g.2 hlt) (isPt_act g (by norm_num) h8)
  have hc8 : act g 8 ≠ 8 := fun h => hg (mem_Ppt.2 h)
  obtain ⟨e, -, he1, hi, hj1, hj6, hm⟩ := decTab_ok _ hc hc8
  set i := e.2.1 with hidef
  set j := e.2.2 with hjdef
  set n : Gam := wd (nWords.getD j []) with hn
  have hnw := words_lt j hj6
  have hact_n : act n 8 = mact (wcode (nWords.getD j [])) 8 := by
    unfold act
    rw [hn, matCode_wd hnw]
  have hact : act (sEltG i * n) 8 = act g 8 := by
    rw [act_mul _ _ (by norm_num), hact_n, act_sEltG hi, hm]
  set p : Gam := (sEltG i * n)⁻¹ * g with hpdef
  have hp : p ∈ Ppt := by
    rw [hpdef, mem_Ppt, act_mul _ _ (by norm_num), ← hact, act_inv_act _ (by norm_num)]
  have hgp : g = sEltG i * n * p := by rw [hpdef]; group
  have hjj : j = (j - 1) + 1 := by omega
  rcases mem_Ppt_iff.1 hp with hS | ⟨s₁, hs₁, s₂, hs₂, hq⟩
  · left
    refine ⟨j - 1, by omega, sEltG i, mem_sSubG.2 ⟨i, hi, rfl⟩, p, hS, ?_⟩
    rw [← hjj]
    exact hgp
  · right
    obtain ⟨i₁, hi₁, rfl⟩ := mem_sSubG.1 hs₁
    obtain ⟨hr, hk, hl, hsplit, hconj⟩ := splitOk i₁ hi₁
    set r := (splitTab.getD i₁ (0, 0, 0)).1
    set k := (splitTab.getD i₁ (0, 0, 0)).2.1
    set l := (splitTab.getD i₁ (0, 0, 0)).2.2
    have h1 : sEltG i₁ = sEltG r * sEltG k :=
      eq_of_code (by
        rw [matCode_mulG, matCode_sEltG hi₁, matCode_sEltG (by omega : r < 64),
          matCode_sEltG hk]
        exact hsplit)
    have h2 : b₀⁻¹ * sEltG k * b₀ = sEltG l :=
      eq_of_code (by
        rw [matCode_mulG, matCode_mulG, b₀_inv, matCode_mulG, matCode_b₀, matCode_sEltG hk,
          matCode_sEltG hl]
        exact hconj)
    refine ⟨j, hj6, r, hr, sEltG i, mem_sSubG.2 ⟨i, hi, rfl⟩, sEltG l * s₂,
      mul_mem (mem_sSubG.2 ⟨l, hl, rfl⟩) hs₂, ?_⟩
    rw [wd_caseWordB j r hr, hgp, hq, h1]
    have h3 : sEltG k * b₀ = b₀ * sEltG l := by
      rw [← h2]
      group
    calc sEltG i * n * (sEltG r * sEltG k * b₀ * s₂)
        = sEltG i * n * sEltG r * (sEltG k * b₀) * s₂ := by simp only [mul_assoc]
      _ = sEltG i * n * sEltG r * (b₀ * sEltG l) * s₂ := by rw [h3]
      _ = sEltG i * (n * sEltG r * b₀) * (sEltG l * s₂) := by simp only [mul_assoc]

theorem gstar {g : Gam} (hP : g ∉ Ppt) (hL : g ∉ Pline) {H : Subgroup Gam} (hS : sSubG ≤ H)
    (hg : g ∈ H) : H = ⊤ := by
  have hSP := sSubG_le_Ppt
  have hSL := sSubG_le_Pline
  have key : ∀ (gc s s' : Gam), s ∈ sSubG → s' ∈ sSubG → g = s * gc * s' →
      (gc ∈ Ppt ∨ gc ∈ Pline ∨ ∀ H : Subgroup Gam, sSubG ≤ H → gc ∈ H → H = ⊤) → H = ⊤ := by
    intro gc s s' hs hs' hgc h
    rcases h with h | h | h
    · exact absurd (by rw [hgc]; exact mul_mem (mul_mem (hSP hs) h) (hSP hs')) hP
    · exact absurd (by rw [hgc]; exact mul_mem (mul_mem (hSL hs) h) (hSL hs')) hL
    · refine h H hS ?_
      have : gc = s⁻¹ * g * s'⁻¹ := by rw [hgc]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (hS hs)) hg) (inv_mem (hS hs'))
  rcases cover hP with ⟨j, hj, s, hs, s', hs', hgc⟩ | ⟨j, hj, r, hr, s, hs, s', hs', hgc⟩
  · exact key _ s s' hs hs' hgc
      (case_sound _ (words_lt (j + 1) (by omega)) _ (caseA_ok j hj))
  · exact key _ s s' hs hs' hgc (case_sound _ (caseWordB_lt j r hj) _ (caseB_ok j hj r hr))

theorem overgroup {P : Subgroup Gam} (hS : sSubG ≤ P) (hne : P ≠ ⊤) : P ≤ Ppt ∨ P ≤ Pline := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨g, hgP, hgn⟩ := IsConcreteLE.not_le_iff_exists.1 hcon.1
  obtain ⟨h, hhP, hhn⟩ := IsConcreteLE.not_le_iff_exists.1 hcon.2
  by_cases hgl : g ∈ Pline
  · by_cases hhp : h ∈ Ppt
    ·
      refine hne (gstar (g := g * h) ?_ ?_ hS (mul_mem hgP hhP))
      · intro hgh
        exact hgn (by simpa using mul_mem hgh (inv_mem hhp))
      · intro hgh
        exact hhn (by simpa using mul_mem (inv_mem hgl) hgh)
    · exact hne (gstar hhp hhn hS hhP)
  · exact hne (gstar hgn hgl hS hgP)

end CFSG.Quasithin.H13.U3.GC137.S2
