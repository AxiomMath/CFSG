module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
  (outer_card_le_four inner_conjugation_injective)

private theorem exists_conj_pow_eq_one {τ : MulAut (alternatingGroup (Fin 6))} {m : ℕ}
    (hτ : τ ^ m = 1) (hm : Nat.Coprime m 6) :
    ∃ t : alternatingGroup (Fin 6), MulAut.conj t = τ ∧ t ^ m = 1 := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  have hinner : τ ∈ inner (alternatingGroup (Fin 6)) := by
    have hom : (QuotientGroup.mk τ : Outer (alternatingGroup (Fin 6))) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
    have hdvdm := orderOf_dvd_of_pow_eq_one hom
    have hdvdO := orderOf_dvd_natCard (QuotientGroup.mk τ : Outer (alternatingGroup (Fin 6)))
    have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
    have hle : orderOf (QuotientGroup.mk τ : Outer (alternatingGroup (Fin 6))) ≤ 4 :=
      (Nat.le_of_dvd hpos hdvdO).trans outer_card_le_four
    have hcop := Nat.Coprime.coprime_dvd_left hdvdm hm
    have hone : orderOf (QuotientGroup.mk τ : Outer (alternatingGroup (Fin 6))) = 1 := by
      generalize orderOf (QuotientGroup.mk τ : Outer (alternatingGroup (Fin 6))) = n at hcop hle
      interval_cases n <;> first | rfl | exact absurd hcop (by decide)
    have h1 := orderOf_eq_one_iff.mp hone
    rwa [QuotientGroup.eq_one_iff] at h1
  obtain ⟨t, rfl⟩ := hinner
  refine ⟨t, rfl, inner_conjugation_injective ?_⟩
  rw [map_pow, hτ, map_one]

private theorem false_of_commute_of_coprime_six {σ τ : MulAut (alternatingGroup (Fin 6))}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {m : ℕ} (hτ : τ ^ m = 1) (hm : Nat.Coprime m 6)
    (hτ1 : τ ≠ 1) (hστ : σ * τ = τ * σ) : False := by
  obtain ⟨t, rfl, htm⟩ := exists_conj_pow_eq_one hτ hm
  have hσt : σ t = t := by
    apply inner_conjugation_injective
    apply MulEquiv.ext
    intro x
    have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ (σ.symm x)) hστ
    change σ (t * σ.symm x * t⁻¹) = t * σ (σ.symm x) * t⁻¹ at h2
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    exact h2
  have ht1 : t = 1 := Sec14.Item148PtRes.eq_one_of_fixed_alternating_six hσ3 hσ1 hσt htm
    (Nat.Coprime.coprime_dvd_right (by norm_num) hm)
  exact hτ1 (by rw [ht1, map_one])

theorem res3NoDatumA6_holds : Res3NoDatumA6 := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  haveI : Group.IsPerfect J := hq.1
  let Φ : MulAut J →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom J)
  have hΦ : Function.Injective Φ :=
    (MulAut.congr e).injective.comp (PerfectAutomorphisms.centerQuotientHom_injective J)
  refine false_of_commute_of_coprime_six (σ := Φ c) (τ := Φ g) (m := orderOf g) ?_ ?_ ?_
    hd.coprime_six ?_ ?_
  · rw [← map_pow, hd.c_pow, map_one]
  · exact fun h => hd.c_ne_one (hΦ (h.trans (map_one Φ).symm))
  · rw [← map_pow, pow_orderOf_eq_one, map_one]
  · exact fun h => hd.g_ne_one (hΦ (h.trans (map_one Φ).symm))
  · rw [← map_mul, ← map_mul, hd.comm.eq]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
