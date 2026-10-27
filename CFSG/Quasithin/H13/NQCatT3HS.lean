module

public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.Sporadic.SmallOddCore.HSWordBound

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_hs
    (h : Star513 Q R S B D) (hQ : IsSporadic .HS ↥Q)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₀⟩ := hQ
  let eP := e₀.trans CFSG.Sporadic.Schreier.hsPermEquiv
  have hZ : Subgroup.center ↥Q = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : ((eP z : CFSG.Sporadic.Schreier.hsP) : Equiv.Perm (Fin 3850)) ∈
        Subgroup.centralizer (CFSG.Sporadic.Schreier.hsP : Set (Equiv.Perm (Fin 3850))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨y, hy⟩ := eP.surjective ⟨g, hg⟩
      have h2 := congrArg eP (Subgroup.mem_center_iff.mp hz y)
      rw [map_mul, map_mul, hy] at h2
      exact congrArg Subtype.val h2
    rw [CFSG.Sporadic.SmallOddCore.hs_centralizer_eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (eP.injective (Subtype.ext (by rw [h1, map_one]; rfl)))
  let ψQ : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Finite (↥Q ⧸ Subgroup.center ↥Q) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ := by
    have h1 := (Subgroup.map_center_eq (G := ↥Q ⧸ Subgroup.center ↥Q) (H := ↥Q) ψQ).trans hZ
    exact (Subgroup.map_eq_bot_iff_of_injective _ ψQ.injective).mp h1
  have hP : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 44352000 :=
    (Nat.card_congr (ψQ.trans eP).toEquiv).trans CFSG.Sporadic.Schreier.card_hsP
  have hinn : ∀ α : MulAut (↥Q ⧸ Subgroup.center ↥Q), Odd (orderOf α) →
      ∃ x, α = MulAut.conj x := by
    refine oddInner_of_card_le hcen ?_
    rw [Nat.card_congr (MulAut.congr (ψQ.trans eP)).toEquiv, hP]
    exact CFSG.Sporadic.SmallOddCore.hs_card_mulAut_le.trans (by norm_num)
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨b, hb, hb3⟩ := exists_b_three e h
  obtain ⟨hE3, hE9⟩ := exists_three_group e hcen hinn h hD3 hnot hb hb3
  have hcard := card_sup_three e hcen hinn h hD3 hb hb3
  set E := iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) with hEdef
  set T := pImg Q e (S ⊓ Q) with hTdef
  have hE : Nat.card E = 9 := by
    obtain ⟨m, hm⟩ := hE3.exists_card_eq
    have hdvd : 3 ^ m ∣ 44352000 := hm ▸ hP ▸ Subgroup.card_subgroup_dvd_card E
    rw [hm] at hE9 ⊢
    have hm2 : m ≤ 2 := by
      by_contra hm3
      have : 3 ^ 3 ∣ 44352000 := (pow_dvd_pow 3 (by omega)).trans hdvd
      revert this
      decide
    interval_cases m
    · norm_num at hE9
    · norm_num at hE9
    · norm_num
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hT : Nat.card T = 2 ^ 9 :=
    CFSG.QuasithinUnique.A5.G3.card_eq_of_odd_index hT2 hTi (m := 86625)
      (by rw [hP]; norm_num) (by decide)
  have hET : Nat.card ↥(E ⊔ T) = 9 * 2 ^ 9 := by rw [hcard, hE, hT]
  rcases CFSG.QuasithinUnique.Ch1.SporLat.HS.hs_overgroups ⟨ψQ.trans e₀⟩
      (K1.isSylowTwoOf_top_iff.mpr ⟨hT2, hTi⟩) (le_sup_right : T ≤ E ⊔ T) with
    htop | ⟨m, hm, hcm, -⟩
  · rw [htop, Subgroup.card_top, hP] at hET
    norm_num at hET
  · rw [hET] at hcm
    simp only [CFSG.QuasithinUnique.Ch1.SporLat.HS.hsMems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hcm

end CFSG.Quasithin.H13.NQCat.T3
