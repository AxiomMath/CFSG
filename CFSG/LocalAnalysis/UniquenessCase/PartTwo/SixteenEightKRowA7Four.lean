module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_a7four (h : S16gRowCtx D V₀ V L hV)
    (hN : A7Four (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨α, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hN
  have hkerβ : β.ker = (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)).subgroupOf
      (commSub ⊤ (lBar V₀ V hV L)) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have hsec : Nat.card (↥(commSub ⊤ (lBar V₀ V hV L)) ⧸
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)).subgroupOf
        (commSub ⊤ (lBar V₀ V hV L))) = 2 ^ 4 := by
    rw [← hkerβ, Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv]
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 2 ^ 4
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
  have hmq : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 4 := by
    rw [E3.mQuot, Subgroup.relIndex, Subgroup.index_eq_card, hsec]
    exact padicValNat.prime_pow 4
  obtain ⟨Q, hQc, hQf, L', N, hexp, hcard, -, -, hnorm, hrank, -⟩ :=
    s16k_exists_quot_data h
  letI := hQc
  letI := hQf
  have hcardQ : Nat.card Q = 16 := by
    rw [hcard, hmq]
    norm_num
  have hN2 : CFSG.Open.pRank p N ≤ 2 :=
    s16k_pRank_le_two_of_aut_sixteen hcardQ hexp N hp hp2
  have hM : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 2 := (hrank p hp).trans hN2
  have h3 : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := h.three_le_pRank hpσ
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
