module

public import CFSG.RankThree.PartTwo.Sec17.Item172Proof
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step172PermPt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → ∀ B : Subgroup G, IsHyperplane A B →
    ∀ g ∈ Subgroup.normalizer (B : Set G), ∀ b ∈ B, b ≠ 1 →
      ¬ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) ≤
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) →
      (omegaA A = {Subgroup.zpowers c} → Subgroup.zpowers b ≠ Subgroup.zpowers c) →
      (Subgroup.zpowers b ∈ omegaA A ∨
        ∃ H : Subgroup G, IsHyperplane A H ∧ b ∈ H ∧ lB A H ≠ ⊥) →
      (xb172 A b).map (MulAut.conj g).toMonoidHom ≤ xB172 A B

namespace Proof176Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_three_element_sup {L J : Subgroup G}
    (hJL : J ≤ Subgroup.normalizer (L : Set G)) (hJ3 : ¬ 3 ∣ Nat.card J) {y : G}
    (hy : y ∈ J ⊔ L) {k : ℕ} (hyk : y ^ 3 ^ k = 1) : y ∈ L := by
  set S := J ⊔ L with hS
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := sup_le hJL Subgroup.le_normalizer
  have hLS : L ≤ S := le_sup_right
  have hN : (L.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLS).mpr hSL
  have hy' : y ∈ ((J ⊔ L : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J L hJL] at hy'
  obtain ⟨j, hj, l, hl, rfl⟩ := hy'
  set π := QuotientGroup.mk' (L.subgroupOf S) with hπ
  have hjS : j ∈ S := Subgroup.mem_sup_left hj
  have hlS : l ∈ S := hLS hl
  have hπl : π ⟨l, hlS⟩ = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hl
  have hπy : π ⟨j * l, hy⟩ = π ⟨j, hjS⟩ := by
    rw [show (⟨j * l, hy⟩ : ↥S) = ⟨j, hjS⟩ * ⟨l, hlS⟩ from rfl, map_mul, hπl, mul_one]
  have h1 : π ⟨j * l, hy⟩ ^ 3 ^ k = 1 := by
    rw [← map_pow, show (⟨j * l, hy⟩ : ↥S) ^ 3 ^ k = 1 from Subtype.ext (by simpa using hyk),
      map_one]
  have h2 : orderOf (π ⟨j * l, hy⟩) ∣ Nat.card J := by
    rw [hπy]
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard J hj
  have hcop : Nat.Coprime (3 ^ k) (Nat.card J) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hJ3)
  have h3 : orderOf (π ⟨j * l, hy⟩) = 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) h2
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at this
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h3
  exact h3

omit [Finite G] in
theorem oPrimeResidualOf_eq_bot {D : Subgroup G} (hD : ¬ 3 ∣ Nat.card D) :
    oPrimeResidualOf 3 D = ⊥ := by
  rw [eq_bot_iff, oPrimeResidualOf_eq_closure 3 D, Subgroup.closure_le]
  rintro y ⟨hyD, k, hyk⟩
  have hcop : Nat.Coprime (3 ^ k) (Nat.card D) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD)
  have h1 : orderOf y = 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyk) (Subgroup.orderOf_dvd_natCard D hyD)
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at this
  rw [orderOf_eq_one_iff] at h1
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  exact h1

theorem not_three_dvd_card_sup {A : Subgroup G} {a : G}
    (hAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G)) :
    ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Subgroup G) :
        Set G) :=
    (pPrimeCoreOf_le 3 _).trans (hAa.trans (le_normalizer_pPrimeCoreOf 3 _))
  rw [sup_comm]
  exact Sec6.not_dvd_card_sup Nat.prime_three hON
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))

theorem mem_normalizer_of_map_le {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom ≤ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Proof176Steps

section Point

variable {G : Type} [Group G] [Finite G]

open Proof176Steps in
theorem map_xb172_c_le (h142 : Item142R) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hsp : ¬ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({c} : Set G))) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)))
    {g : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    (xb172 A c).map (MulAut.conj g).toMonoidHom ≤ xb172 A c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hcA : c ∈ A := h.toSec13Data.mem_A
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set Nc := pPrimeCoreOf 3 C with hNc
  set D := delta A (lB A) C with hD
  have hCH : C ≤ H := centralizer_singleton_le_normalizer_zpowers c
  have hDH : D ≤ delta A (lB A) H := Sec14.delta_mono hCH
  have hHD : delta A (lB A) H ≤ D := Proof171Steps.delta_normalizer_le hcA hc
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨-, halt⟩ := h142 G A c L h.toSec15R Qs hQs
  rcases halt with ⟨-, -, hOKH, hcard⟩ | ⟨hKH, -⟩
  ·
    exfalso
    apply hsp
    have h3 : ¬ 3 ∣ Nat.card (delta A (lB A) H) := by
      rw [show delta A (lB A) H = k142 A (lB A) c from rfl, hcard]
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3' | h3'
      · omega
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h3'
    have hD3 : ¬ 3 ∣ Nat.card D := fun h3' => h3 (h3'.trans (Subgroup.card_dvd_of_le hDH))
    rw [oPrimeResidualOf_eq_bot hD3]
    exact bot_le
  ·
    have hKH' : delta A (lB A) H = L ⊔ pPrimeCoreOf 3 H ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := hKH
    have h3L : 3 ∣ Nat.card L := by
      have hdvd := Sec14.three_dvd_card_of_types148
        (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
      exact hdvd
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L
    set J := pPrimeCoreOf 3 H ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hJ
    have hAC : Subgroup.centralizer (A : Set G) ≤ C :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)
    have hO'H : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ H :=
      (pPrimeCoreOf_le 3 _).trans (hAC.trans hCH)
    have hJH : J ≤ H := sup_le (pPrimeCoreOf_le 3 H) hO'H
    have hJ3 : ¬ 3 ∣ Nat.card J := by
      rw [hJ, sup_comm]
      exact Sec6.not_dvd_card_sup Nat.prime_three (hO'H.trans (le_normalizer_pPrimeCoreOf 3 H))
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
    have hΔ : delta A (lB A) H = J ⊔ L := by
      rw [hKH', hJ, sup_assoc, sup_comm]
    have hRL : oPrimeResidualOf 3 D ≤ L := by
      rw [oPrimeResidualOf_eq_closure 3 D, Subgroup.closure_le]
      rintro y ⟨hyD, k, hyk⟩
      have hyJL : y ∈ J ⊔ L := hΔ ▸ hDH hyD
      exact mem_of_three_element_sup (hJH.trans hHL) hJ3 hyJL hyk
    have hLR : L ≤ oPrimeResidualOf 3 D := by
      rw [Proof171Steps.eq_oPrimeResidualOf_of_types h.mem_lA.1
        (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1]
      refine Proof171Steps.oPrimeResidualOf_mono_three ?_
      refine le_trans ?_ hHD
      rw [hKH']
      exact le_sup_of_le_left le_sup_left
    have hX : xb172 A c = Nc ⊔ L := le_antisymm (sup_le_sup_left hRL _) (sup_le_sup_left hLR _)
    have hgc : Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c := by
      have h1 : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c :=
        Late.map_conj_eq_of_mem_normalizer hg
      rw [MonoidHom.map_zpowers] at h1
      exact h1
    have hCg : C.map (MulAut.conj g).toMonoidHom = C := by
      rw [hC, map_centralizer_singleton (MulAut.conj g) c]
      exact centralizer_singleton_eq_of_zpowers_eq hgc
    have hNg : Nc.map (MulAut.conj g).toMonoidHom = Nc := by
      rw [hNc, map_pPrimeCoreOf 3 (MulAut.conj g), hCg]
    have hLg : L.map (MulAut.conj g).toMonoidHom = L := Late.map_conj_eq_of_mem_normalizer (hHL hg)
    rw [hX, Subgroup.map_sup, hNg, hLg]

end Point

open Proof176Steps in
theorem step172Perm_of (h142 : Item142R) (h175 : Item175R) (hbal : Step143Balance)
    (hpt : Step172PermPt) : Step172Perm := by
  intro G _ _ A c L Y₀ h h1514 B hB g hg
  have key : ∀ b ∈ B, b ≠ 1 → (xb172 A b).map (MulAut.conj g).toMonoidHom ≤ xB172 A B := by
    intro b hbB hb1
    have hgb : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg b).mp hbB
    have hgb1 : g * b * g⁻¹ ≠ 1 := fun h1 => hb1 (by
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this)
    have hle : ∀ x : G, x ∈ B → x ≠ 1 → xb172 A x ≤ xB172 A B := fun x hx hx1 =>
      le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 le_rfl))
    by_cases hsp : oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))
    ·
      have hXb : xb172 A b = pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
        sup_eq_left.mpr hsp
      rw [hXb, map_pPrimeCoreOf 3 (MulAut.conj g), map_centralizer_singleton (MulAut.conj g) b]
      exact le_sup_left.trans (hle _ hgb hgb1)
    · by_cases hcp : omegaA A = {Subgroup.zpowers c} ∧ Subgroup.zpowers b = Subgroup.zpowers c
      ·
        obtain ⟨hΩ, hbc⟩ := hcp
        have hCbc := centralizer_singleton_eq_of_zpowers_eq hbc
        have hXbc : xb172 A b = xb172 A c := by
          rw [xb172, xb172, hCbc]
        have hcB : c ∈ B := (Subgroup.zpowers_le.mpr hbB) (hbc ▸ Subgroup.mem_zpowers c)
        have hc1 : c ≠ 1 := h.toSec13Data.ne_one
        have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
          have hgcB : g * c * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg c).mp hcB
          have hle' : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
              Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
            rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
            exact Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
              (h.toSec13Data.A_le_centralizer (hB.1 hgcB))
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
            (h175 G A c L h.toSec15R hΩ g hle')
        have hsp' : ¬ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({c} : Set G))) ≤
            pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) := by
          rw [← hCbc]
          exact hsp
        rw [hXbc]
        exact (map_xb172_c_le h142 h hsp' hgH).trans (hle c hcB hc1)
      ·
        have hspecial : Subgroup.zpowers b ∈ omegaA A ∨
            ∃ H : Subgroup G, IsHyperplane A H ∧ b ∈ H ∧ lB A H ≠ ⊥ := by
          by_contra hns
          push Not at hns
          obtain ⟨hbΩ, hLB⟩ := hns
          have hbA : b ∈ A := hB.1 hbB
          apply hsp
          rw [Sec14.delta_eq_sup_of_lB_eq_bot hbal h.toSec14Std hbA hb1 hbΩ hLB,
            oPrimeResidualOf_eq_bot (not_three_dvd_card_sup
              (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)))]
          exact bot_le
        exact hpt G A c L Y₀ h h1514 B hB g hg b hbB hb1 hsp (fun hΩ hbc => hcp ⟨hΩ, hbc⟩)
          hspecial
  refine mem_normalizer_of_map_le ?_
  rw [xB172, Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hb1 => key b hb hb1

end CFSG.RankThree.PartTwo.Sec17
