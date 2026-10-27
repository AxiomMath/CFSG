module

public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_ru
    (h : Star513 Q R S B D) (hQ : IsSporadic .Ru ↥Q)
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₀⟩ := hQ
  let eP := e₀.trans CFSG.Sporadic.RuSchreier.ruEquivP
  have hZ : Subgroup.center ↥Q = ⊥ := by
    have h1 := (Subgroup.map_center_eq (G := ↥Q) (H := ↥CFSG.Sporadic.RuSchreier.ruP) eP).trans
      CFSG.Sporadic.RuSchreier.center_ruP
    exact (Subgroup.map_eq_bot_iff_of_injective _ eP.injective).mp h1
  let ψQ : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Finite (↥Q ⧸ Subgroup.center ↥Q) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ := by
    have h1 := (Subgroup.map_center_eq (G := ↥Q ⧸ Subgroup.center ↥Q) (H := ↥Q) ψQ).trans hZ
    exact (Subgroup.map_eq_bot_iff_of_injective _ ψQ.injective).mp h1
  have hP : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 145926144000 :=
    (Nat.card_congr (ψQ.trans eP).toEquiv).trans CFSG.Sporadic.RuSchreier.card_ruP'
  have hinn : ∀ α : MulAut (↥Q ⧸ Subgroup.center ↥Q), Odd (orderOf α) →
      ∃ x, α = MulAut.conj x :=
    oddInner_of_mulEquiv (ψQ.trans eP) fun α _ => CFSG.Sporadic.RuSchreier.mulAut_inner α
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨b, hb, hb3⟩ := exists_b_three e h
  obtain ⟨hE3, hE9⟩ := exists_three_group e hcen hinn h hD3 hnot hb hb3
  have hcard := card_sup_three e hcen hinn h hD3 hb hb3
  set E := iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) with hEdef
  set T := pImg Q e (S ⊓ Q) with hTdef
  obtain ⟨m, hm⟩ := hE3.exists_card_eq
  have hm23 : m = 2 ∨ m = 3 := by
    have hdvd : 3 ^ m ∣ 145926144000 := hm ▸ hP ▸ Subgroup.card_subgroup_dvd_card E
    rw [hm] at hE9
    have hm3 : m ≤ 3 := by
      by_contra hm4
      have : 3 ^ 4 ∣ 145926144000 := (pow_dvd_pow 3 (by omega)).trans hdvd
      revert this
      decide
    interval_cases m
    · norm_num at hE9
    · norm_num at hE9
    · left; rfl
    · right; rfl
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hT : Nat.card T = 2 ^ 14 :=
    CFSG.QuasithinUnique.A5.G3.card_eq_of_odd_index hT2 hTi (m := 8906625)
      (by rw [hP]; norm_num) (by decide)
  have hET : Nat.card ↥(E ⊔ T) = 3 ^ m * 2 ^ 14 := by rw [hcard, hm, hT]
  rcases CFSG.QuasithinUnique.Ch1.SporLat.Ru.ru_overgroups ⟨ψQ.trans e₀⟩
      (K1.isSylowTwoOf_top_iff.mpr ⟨hT2, hTi⟩) (le_sup_right : T ≤ E ⊔ T) with
    htop | ⟨r, hr, hcr, -⟩
  · rw [htop, Subgroup.card_top, hP] at hET
    rcases hm23 with rfl | rfl <;> norm_num at hET
  · rw [hET] at hcr
    simp only [CFSG.QuasithinUnique.Ch1.SporLat.Ru.ruMems, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hm23 with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num at hcr

end CFSG.Quasithin.H13.NQCat.T3
