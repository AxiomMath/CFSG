module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c5_exists_centralizesBar {K : Subgroup G} {n p : ℕ} (hL2 : IsL2 (Bar2 K) n)
    (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hBN : B ≤ normalizer (K : Set G))
    (hinn : ∀ b (hb : b ∈ B),
      UC6S846.rhoL K ⟨b, hBN hb⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range) :
    ∃ C : Subgroup G, C ≤ B ∧ (∀ c ∈ C, CentralizesBar c K) ∧ Nat.card B ≤ p * Nat.card C := by
  let φ : ↥B →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hBN)
  have hinj : Function.Injective (MulAut.conj : Bar2 K →* MulAut (Bar2 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot (uc22p22g_center_bot hL2)
  have hpow : ∀ b : ↥B, φ b ^ p = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ p = 1 := Subtype.ext (by simpa using hB.2 _ b.2)
    rw [this, map_one]
  have hinn' : φ.range ≤ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
    rintro _ ⟨b, rfl⟩
    exact hinn b b.2
  set Q : Subgroup (Bar2 K) := φ.range.comap MulAut.conj with hQ
  have hQcard : Nat.card Q = Nat.card φ.range := by
    rw [← Subgroup.map_comap_eq_self hinn', Subgroup.card_map_of_injective hinj]
  have hQel : IsElemAbelian p Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · obtain ⟨a, ha⟩ : MulAut.conj (x : Bar2 K) ∈ φ.range := x.2
      obtain ⟨b, hb⟩ : MulAut.conj (y : Bar2 K) ∈ φ.range := y.2
      have hab : a * b = b * a := by
        have := hB.1
        exact mul_comm' a b
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← ha, ← hb, ← map_mul, hab,
        map_mul]
    · obtain ⟨a, ha⟩ : MulAut.conj x ∈ φ.range := hx
      rw [map_pow, ← ha, hpow, map_one]
  have := hQel.isElementaryAbelian
  have hQle : Nat.card Q ≤ p := uc22p22g_rank hp hp2 hL2 Q
  refine ⟨φ.ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨hBN b.2, fun l hl => ?_⟩
    have h1 : UC6S846.rhoL K (Subgroup.inclusion hBN b) = 1 := hb
    have h2 : UC6S846.rhoL K (Subgroup.inclusion hBN b) (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h1, MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K _ ⟨l, hl⟩).1 h2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_ker_mul_card_range φ,
      mul_comm p]
    exact Nat.mul_le_mul_left _ (hQcard ▸ hQle)

theorem uc22r899c5_sp_of_inner {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3)
    (hinn : ∀ K ∈ conjSetOf D.M L, ∀ a ∈ D.M, ∀ haK : a ∈ normalizer (K : Set G), a ^ p = 1 →
      UC6S846.rhoL K ⟨a, haK⟩ ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range) :
    IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  refine uc22s21r899_sp_of_lift hSg hfour h614 h76 hL hc3 (Or.inl hL2) hs hsn hr hrs hp hp3 ?_
  rintro K₁ h1S K₂ h2S - A₀ hA₀M hA₀el hA₀c hA₀N a₁ a₂ ha₁ ha₂ - -
  have h1C := uc22p2214_calC_of_mem_conjSetOf hL h1S
  have h2C := uc22p2214_calC_of_mem_conjSetOf hL h2S
  have hcb : ∀ A ∈ conjSetOf D.M L, ∀ B : Subgroup G, B ≤ A₀ →
      ∀ hBN : B ≤ normalizer (A : Set G), ∃ C : Subgroup G, C ≤ B ∧
        (∀ c ∈ C, CentralizesBar c A) ∧ Nat.card B ≤ p * Nat.card C :=
    fun A hA B hBA hBN => uc22r899c5_exists_centralizesBar (uc22s21r899_isL2_of_mem hA hL2) hpp
      hp2 (hA₀el.mono hBA) hBN
      (fun b hb => hinn A hA b (hA₀M (hBA hb)) (hBN hb) (hA₀el.2 b (hBA hb)))
  obtain ⟨B₁, hB₁, hB₁c, hB₁card⟩ := hcb K₁ h1S A₀ le_rfl (hA₀N K₁ h1S)
  obtain ⟨B₂, hB₂, hB₂c, hB₂card⟩ := hcb K₂ h2S B₁ hB₁ (hB₁.trans (hA₀N K₂ h2S))
  have hB₂p : p ^ 2 ≤ Nat.card B₂ := by
    rw [hA₀c] at hB₁card
    have h4 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card B₂ :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ p * Nat.card B₁ := hB₁card
        _ ≤ p * (p * Nat.card B₂) := Nat.mul_le_mul_left _ hB₂card
        _ = p ^ 2 * Nat.card B₂ := by ring
    exact Nat.le_of_mul_le_mul_left h4 (pow_pos hpp.pos 2)
  obtain ⟨A, hAB, hAel, hAc⟩ := UC6S846.exists_card_p_sq hpp (hA₀el.mono (hB₂.trans hB₁)) hB₂p
  refine ⟨A, hAB.trans (hB₂.trans (hB₁.trans hA₀M)), hAel, hAc, fun e he a ha => ?_⟩
  exact uc22p2213e_comm_mem_pCoreOf h1C h2C (hB₁c a (hB₂ (hAB ha))) (hB₂c a (hAB ha))
    (sup_le_sup (zpowers_le.2 ha₁) (zpowers_le.2 ha₂) he)

end CFSG.LocalAnalysis.UniquenessCase.UC22
