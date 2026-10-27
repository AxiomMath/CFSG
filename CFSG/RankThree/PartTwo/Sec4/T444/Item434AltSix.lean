module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltCtx
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSixAut

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Alt

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Equiv Equiv.Perm Subgroup Item434AltPerm
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem not_three_dvd_card_outer_six : ¬ 3 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have hf1 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (swap 0 1)) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← CFSG.Quasithin.SteinbergCB.map_conjPerm_alternatingGroup] at h
    obtain ⟨a, ha, hae⟩ := h
    have := CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num) hae
    rw [this, SetLike.mem_coe, mem_alternatingGroup, sign_swap (by decide)] at ha
    exact absurd ha (by decide)
  have hf2 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (swap 0 1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, sq, swap_mul_self, map_one, map_one]
  have hord := orderOf_eq_prime hf2 hf1
  have hdvd : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) :=
    hord ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  intro h3
  omega

theorem mem_range_conj_of_pow_three {φ : MulAut (alternatingGroup (Fin 6))} (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  set q := QuotientGroup.mk' (inner (alternatingGroup (Fin 6))) φ with hq
  have hq3 : q ^ 3 = 1 := by rw [hq, ← map_pow, hφ, map_one]
  have hcop : Nat.Coprime 3 (Nat.card (Outer (alternatingGroup (Fin 6)))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr not_three_dvd_card_outer_six
  have hd : orderOf q ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard q)
  have hq1 : q = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
  exact hq1

theorem factorization_alternating_six :
    (Nat.card (alternatingGroup (Fin 6))).factorization 3 = 2 := by
  rw [CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.card_alternating_six,
    show (360 : ℕ) = 3 ^ 2 * 40 by norm_num, factorization_three_pow_mul 2 (by norm_num)]

theorem false_of_alt_six (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 6)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set δ := quotConj e with hδ
  set ι := (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) with hι
  have hιinj : Function.Injective ι :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  have hker : δ.ker = Subgroup.centralizer (layer G : Set G) := by
    ext g
    rw [MonoidHom.mem_ker, quotConj_eq_one_iff h.isQuasisimple]
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hQC := Item434.inf_centralizer_layer_eq_bot h
  have hQcard : Nat.card (Q.map δ) = Nat.card Q := by
    have h1 := card_eq_card_inf_ker_mul_card_map δ Q
    rw [hker, hQC, Subgroup.card_bot, one_mul] at h1
    exact h1.symm
  have hAinn : A.map δ ≤ ι.range := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_range_conj_of_pow_three (by rw [← map_pow, h.isE27.1.2 a ha, map_one])
  set P := (A.map δ).comap ι with hP
  have hPmap : P.map ι = A.map δ := Subgroup.map_comap_eq_self hAinn
  have hPcard : Nat.card P = Nat.card (A.map δ) := by
    rw [← hPmap, Subgroup.card_map_of_injective hιinj]
  have hPp : IsPGroup 3 P := by
    have h1 : IsPGroup 3 (A.map δ) := h.isE27.isPGroup.map δ
    exact h1.comap_of_injective ι hιinj
  have hP9 : Nat.card P = 9 := by
    have hle := card_le_of_isPGroup hPp
    rw [factorization_alternating_six] at hle
    have h27 := card_eq_card_inf_ker_mul_card_map δ A
    rw [h.isE27.2, hker] at h27
    have hC3 := h.card_inf_centralizer_layer_le
    rw [← hPcard] at h27
    set c := Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G)
    set d := Nat.card P
    have hd9 : d ≤ 9 := by simpa using hle
    have hc3 : c = 3 := by
      by_contra hc
      have : c ≤ 2 := by omega
      have : c * d ≤ 2 * 9 := Nat.mul_le_mul this hd9
      omega
    rw [hc3] at h27
    omega
  obtain ⟨k, hk⟩ := exists_le_map_conj_of_card (P₀ := F06)
    (by rw [card_F06, factorization_alternating_six]; norm_num) hPp
  have hPeq : P = F06.map (MulAut.conj k).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hk (by
      rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, card_F06, hP9])
  set ψ : MulAut (MulAut (alternatingGroup (Fin 6))) := MulAut.conj (ι k) with hψ
  have hAδ : A.map δ = (F06.map ι).map ψ.toMonoidHom := by
    rw [← hPmap, hPeq, Subgroup.map_map, Subgroup.map_map]
    congr 1
  set X := (Q.map δ).map ψ⁻¹.toMonoidHom with hX
  have hXcard : Nat.card X = Nat.card Q := by
    rw [hX, Subgroup.card_map_of_injective (ψ⁻¹).injective, hQcard]
  have hNX : F06.map ι ≤ normalizer (X : Set (MulAut (alternatingGroup (Fin 6)))) := by
    have h1 : A.map δ ≤ normalizer ((Q.map δ : Subgroup _) : Set (MulAut (alternatingGroup
        (Fin 6)))) :=
      (Subgroup.map_mono hAQ).trans (Subgroup.le_normalizer_map δ)
    have h2 := (Subgroup.map_mono (f := ψ⁻¹.toMonoidHom) h1).trans
      (Subgroup.le_normalizer_map ψ⁻¹.toMonoidHom)
    rw [hAδ, Subgroup.map_map] at h2
    convert h2 using 1
    rw [eq_comm]
    convert Subgroup.map_id (F06.map ι)
    ext φ
    simp
  have hXbot := eq_bot_of_F06_le_normalizer (by rw [hXcard]; exact hQ3) hNX
  apply h.ne_bot
  rw [← Subgroup.card_eq_one, ← hXcard, hXbot, Subgroup.card_bot]

end CFSG.RankThree.PartTwo.Sec4.Item434Alt
