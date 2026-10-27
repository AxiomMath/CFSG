module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth76_of_steps (hNR : Sec7NormZ0Statement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hTr : Stroth73bTransStatement) (hSyl : Sec7SylowLBStatement)
    (hE : Step76EStatement) (hEnd : Sec7EndStatement) : Stroth76Statement := by
  intro G _ _ M Q Z B hc n t hs hno
  by_contra hnom
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc hs.toSec5.mem
  have hTI := Z0_normalizes_of_nat hNR hZV G M Q Z B hc n t hs hnom Z0 hZ0
  have hSyl' := exists_sylow_Z0_of_trans hc hs hno hZc hZ0 hTI hTr (hSyl G M Q Z B hc n t hs)
  exact hEnd G M Q Z B hc n t hs Z0 hZ0 hTI hSyl' (hE G M Q Z B hc n t hs hno hnom Z0 hZ0)

theorem isIrredModule_of_min (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZc : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {e : ℕ} (he : 1 ≤ e)
    (hN : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ e)
    (hmin : ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 →
      Nat.card ↥Z0 * Nat.card Z ^ e ≤ Nat.card ↥A) :
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have h5 := hs.toSec5
  obtain ⟨-, hcard, hcomm, hopp⟩ := h51 G M Q Z B hc n t h5 (Or.inr hs.omegaNat) r hr.mem
    hr.plane (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t)
    (Rt M (LB M Q B) t) rfl rfl rfl rfl rfl
  have hIZ : LB M Q B ⊓ LB M Q (conjSubgroup r B) = Z0 := by
    have hle : LB M Q B ⊓ LB M Q (conjSubgroup r B) ≤ Z0 := by
      intro x hx
      refine (hZ0 x).mpr ⟨le_Rt (M := M) (LB M Q B) h5.mem hx.1, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hcomm ρ hρ x hx)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hZc G M Q Z B hc n t hs Z0 hZ0])
  rw [hIZ] at hopp
  obtain ⟨hI1, hI2, -, -, -, -, hab, hsq, -, -⟩ := hopp
  have hZ0N : Z0 ≤ hc.CN t := hI1.trans hI2
  have hq2 : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  refine ⟨hab, hsq, lt_of_le_of_ne hZ0N fun h => ?_, ?_⟩
  · have h1 : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 := by rw [h]
    have h2 : 2 ≤ Nat.card Z ^ e := by
      calc 2 ≤ Nat.card Z := hq2
        _ = Nat.card Z ^ 1 := (pow_one _).symm
        _ ≤ Nat.card Z ^ e := Nat.pow_le_pow_right (by omega) he
    have h3 : 0 < Nat.card ↥Z0 := Nat.card_pos
    rw [hN] at h1
    nlinarith
  · intro A hA1 hA2 hinv
    by_cases hAZ : A = Z0
    · exact Or.inl hAZ
    · right
      exact Subgroup.eq_of_le_of_card_ge hA2 (by rw [hN]; exact hmin A hA1 hA2 hinv hAZ)

theorem stroth79_of_inputs (h78 : Stroth78Statement) (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hZc : Sec7ZCardStatement) (hMin : Sec79MinOrderStatement) :
    Stroth79Statement := by
  intro G _ _ M Q Z B hc n t h5 hlarge hnp hex
  obtain ⟨m, hm, htype⟩ := hex
  have hs : Sec7Hyp hc n t := ⟨h5, hnp, ⟨m, hm, htype⟩, hlarge⟩
  have hC78 := h78 G M Q Z B hc n t h5 hlarge hnp m hm htype
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc h5.mem
  have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z := hZc G M Q Z B hc n t hs Z0 hZ0
  have irr : ∀ e : ℕ, 1 ≤ e → Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ e →
      (∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
        (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 →
        Nat.card ↥Z0 * Nat.card Z ^ e ≤ Nat.card ↥A) → Conc79 hc n t :=
    fun e he hN hmin => Or.inl ⟨Z0, hZ0, isIrredModule_of_min h51 hA hZc hc hs hZ0 he hN hmin⟩
  have hmin_minus : ∀ m' : ℕ, 2 ≤ m' → OmegaMinusNat hc t m' → ∀ A : Subgroup G, Z0 ≤ A →
      A ≤ hc.CN t → (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 →
      Nat.card ↥Z0 * Nat.card Z ^ (2 ^ m') ≤ Nat.card ↥A :=
    fun m' hm' h A hZA hAN hinv hAZ =>
      ((hMin G M Q Z B hc n t hs Z0 hZ0 A hZA hAN hinv hAZ m' hm').1 h)
  have hmin_plus : ∀ m' : ℕ, 3 ≤ m' → OmegaPlusNat hc t m' → ∀ A : Subgroup G, Z0 ≤ A →
      A ≤ hc.CN t → (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 →
      Nat.card ↥Z0 * Nat.card Z ^ (2 ^ (m' - 1)) ≤ Nat.card ↥A :=
    fun m' hm' h A hZA hAN hinv hAZ =>
      ((hMin G M Q Z B hc n t hs Z0 hZ0 A hZA hAN hinv hAZ m' (by omega)).2 h hm')
  rcases hC78 with ⟨hm3, -, hN⟩ | ⟨hm4, hn16, hN⟩ | ⟨hm4, hp, -, hN⟩ | ⟨hm5, hp, -, hN⟩ |
    ⟨hm6, hp, -, hN⟩
  · subst hm3
    rcases htype with hp | hmn
    · exact Or.inr (Or.inl hp)
    · refine irr 8 (by norm_num) (by rw [hN, hZ0card]; ring) ?_
      exact hmin_minus 3 (by norm_num) hmn
  · subst hm4
    rcases htype with hp | hmn
    · exact Or.inr (Or.inr ⟨hp, hn16⟩)
    · refine irr 16 (by norm_num) (by rw [hN, hZ0card]; ring) ?_
      exact hmin_minus 4 (by norm_num) hmn
  · refine irr 8 (by norm_num) (by rw [hN, hZ0card]; ring) ?_
    simpa using hmin_plus 4 (by norm_num) hp
  · refine irr 16 (by norm_num) (by rw [hN, hZ0card]; ring) ?_
    simpa using hmin_plus 5 (by norm_num) hp
  · refine irr 32 (by norm_num) (by rw [hN, hZ0card]; ring) ?_
    simpa using hmin_plus 6 (by norm_num) hp

end CFSG.RankThree.GF2n.Stroth80
