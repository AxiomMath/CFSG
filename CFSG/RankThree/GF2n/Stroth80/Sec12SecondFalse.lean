module

import CFSG.RankThree.GF2n.Stroth80.Sec12SecondGrp
public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCases
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondSchur
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondSL2
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondOrders
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondIneq
import CFSG.RankThree.GF2n.Stroth80.Sec12SecondSimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X]

private theorem isPerfect_of_isSimpleGroup_of_noncomm {Y : Type} [Group Y] [IsSimpleGroup Y]
    (h : ∃ x y : Y, x * y ≠ y * x) : Group.IsPerfect Y := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h0 | h0
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    apply hxy
    rw [← commutatorElement_eq_one_iff_mul_comm, ← Subgroup.mem_bot, ← h0, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  · exact h0

theorem false_of_fst_trivial {N R S : Subgroup X} (hS : ConfigSatz N) (hNR : N ≤ R)
    (hRS : R ≤ S) (hSC : S ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X))
    (hirr : ∀ A : Subgroup X, cen N ≤ A → A ≤ N → (∀ r ∈ R, conjSubgroup r A = A) →
      A = cen N ∨ A = N)
    [(N.subgroupOf S).Normal] {A B : Type} [Group A] [Group B]
    (e : ↥S ⧸ N.subgroupOf S ≃* A × B) (hAn : ∃ x y : A, x * y ≠ y * x)
    (hfst : ∀ r : ↥R, (e (QuotientGroup.mk (Subgroup.inclusion hRS r))).1 = 1) : False := by
  let ψ : ↥S →* B := (MonoidHom.snd A B).comp (e.toMonoidHom.comp
    (QuotientGroup.mk' (N.subgroupOf S)))
  let D : Subgroup X := ψ.ker.map S.subtype
  have hDS : D ≤ S := Subgroup.map_subtype_le _
  have hDH : D ≤ H0 (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) (cen N) :=
    fun x hx => ⟨(Subgroup.centralizer_le_normalizer _) (hSC (hDS hx)), hSC (hDS hx)⟩
  have hRH : R ≤ H0 (Subgroup.normalizer ((cen N : Subgroup X) : Set X)) (cen N) :=
    fun x hx => ⟨(Subgroup.centralizer_le_normalizer _) (hSC (hRS hx)), hSC (hRS hx)⟩
  have hmemD : ∀ s : ↥S, (e (QuotientGroup.mk s)).2 = 1 → (s : X) ∈ D :=
    fun s hs => ⟨s, hs, rfl⟩
  have hcomm : ∀ d ∈ D, ∀ r ∈ R, ⁅d, r⁆ ∈ N := by
    rintro _ ⟨d, hd, rfl⟩ r hr
    have hd2 : (e (QuotientGroup.mk d)).2 = 1 := hd
    have hr1 := hfst ⟨r, hr⟩
    have hrS : r ∈ S := hRS hr
    have h1 : (e (QuotientGroup.mk d)) * (e (QuotientGroup.mk (⟨r, hrS⟩ : ↥S))) =
        (e (QuotientGroup.mk (⟨r, hrS⟩ : ↥S))) * (e (QuotientGroup.mk d)) := by
      have hr1' : (e (QuotientGroup.mk (⟨r, hrS⟩ : ↥S))).1 = 1 := hr1
      refine Prod.ext ?_ ?_
      · simp [hr1']
      · simp [hd2]
    have h2 : QuotientGroup.mk (⁅d, (⟨r, hrS⟩ : ↥S)⁆) = (1 : ↥S ⧸ N.subgroupOf S) := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement]
      refine commutatorElement_eq_one_iff_mul_comm.mpr (e.injective ?_)
      rw [map_mul, map_mul]
      exact h1
    have h3 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    simpa [commutatorElement_def] using h3
  obtain ⟨x, y, hxy⟩ := hAn
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm (x, 1))
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm (y, 1))
  have ha2 : (e (QuotientGroup.mk a)).2 = 1 := by rw [ha]; simp
  have hb2 : (e (QuotientGroup.mk b)).2 = 1 := by rw [hb]; simp
  have hcc := commutators_mem_of_irreducible hS.1 hRH hDH hirr hcomm a (hmemD a ha2) b
    (hmemD b hb2)
  apply hxy
  have h4 : QuotientGroup.mk (⁅a, b⁆) = (1 : ↥S ⧸ N.subgroupOf S) := by
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using hcc)
  rw [← QuotientGroup.mk'_apply, map_commutatorElement] at h4
  have h5 := commutatorElement_eq_one_iff_mul_comm.mp h4
  have h6 := congrArg e h5
  rw [map_mul, map_mul] at h6
  have ha' : e (QuotientGroup.mk' (N.subgroupOf S) a) = (x, 1) := by
    have : (QuotientGroup.mk' (N.subgroupOf S) a : ↥S ⧸ N.subgroupOf S) = e.symm (x, 1) := ha
    rw [this]
    simp
  have hb' : e (QuotientGroup.mk' (N.subgroupOf S) b) = (y, 1) := by
    have : (QuotientGroup.mk' (N.subgroupOf S) b : ↥S ⧸ N.subgroupOf S) = e.symm (y, 1) := hb
    rw [this]
    simp
  rw [ha', hb'] at h6
  simpa using congrArg Prod.fst h6

theorem quot_embeds_prod {N R S : Subgroup X} (hNR : N ≤ R) (hRS : R ≤ S)
    [(N.subgroupOf R).Normal] [(N.subgroupOf S).Normal] {A B : Type} [Group A] [Group B]
    [Finite A] [Finite B] (e : ↥S ⧸ N.subgroupOf S ≃* A × B)
    [IsSimpleGroup (↥R ⧸ N.subgroupOf R)] :
    Nat.card (↥R ⧸ N.subgroupOf R) ≤ Nat.card A ∨
      (Nat.card (↥R ⧸ N.subgroupOf R) ≤ Nat.card B ∧
        ∀ r : ↥R, (e (QuotientGroup.mk (Subgroup.inclusion hRS r))).1 = 1) := by
  obtain ⟨ι, hι, hιmk⟩ := exists_injective_quotient hNR hRS
  rcases card_le_or_le_of_embeds (e.toMonoidHom.comp ι) (e.injective.comp hι) with h | ⟨h, h1⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, fun r => ?_⟩
    have := h1 (QuotientGroup.mk r)
    simpa [hιmk r] using this

theorem secondCfgFalse_omegaMinus4 : SecondCfgFalse (IsOmegaMinus 4) 8 := by
  intro X _ _ N R hS _ hW hNR hRC hQS hirr
  obtain ⟨hnR, hP⟩ := hQS
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hq4 : 4 ≤ Nat.card (cen N) := hS.1.q4
  obtain ⟨hRs, hRn, -, hRcard⟩ := isOmegaMinus_four_facts hqa hP
  haveI := hRs
  have hperf : QuotSat R N (fun Y _ => Group.IsPerfect Y) :=
    ⟨hnR, isPerfect_of_isSimpleGroup_of_noncomm hRn⟩
  obtain ⟨S, hNS, hSC, hRS, hT⟩ := secondCfg_le (Or.inr rfl) hS hW (fun h => by omega)
    (fun h => by omega) hNR hRC hperf hirr
  rcases hT with ⟨h84, -⟩ | ⟨m, hm2, hm, hQ⟩
  · omega
  · have hm4 : m = 4 := by omega
    subst hm4
    rcases hQ with hQp | hQm
    · obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQp
      obtain ⟨hAs, hAn, -, hAcard⟩ := isSLModel_two_facts hqa hA
      obtain ⟨hBs, hBn, -, hBcard⟩ := isOmegaPlus_four_facts hqa hB
      haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
      haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B))) (fun x y h =>
        (Prod.mk.inj h).1)
      haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b)) (fun x y h =>
        (Prod.mk.inj h).2)
      rcases quot_embeds_prod hNR hRS e with h | ⟨h, -⟩
      · rw [hRcard, hAcard] at h
        exact absurd h (not_le.mpr (sl2_lt_om8 _ hq4))
      · rw [hRcard, hBcard] at h
        exact absurd h (not_le.mpr (op8_lt_om8 _ hq4))
    · obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQm
      obtain ⟨hAs, hAn, -, hAcard⟩ := isSLModel_two_facts hqa hA
      obtain ⟨hBs, hBn, -, hBcard⟩ := isOmegaMinus_four_facts hqa hB
      haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
      haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B))) (fun x y h =>
        (Prod.mk.inj h).1)
      haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b)) (fun x y h =>
        (Prod.mk.inj h).2)
      rcases quot_embeds_prod hNR hRS e with h | ⟨-, hfst⟩
      · rw [hRcard, hAcard] at h
        exact absurd h (not_le.mpr (sl2_lt_om8 _ hq4))
      · exact false_of_fst_trivial hS hNR hRS hSC hirr e hAn hfst

theorem width8_false_of_large {N R : Subgroup X} (hS : ConfigSatz N)
    (hW : Width N (cen N) 8) (hNR : N ≤ R)
    (hRC : R ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X))
    (hirr : ∀ A : Subgroup X, cen N ≤ A → A ≤ N → (∀ r ∈ R, conjSubgroup r A = A) →
      A = cen N ∨ A = N)
    (hnR : (N.subgroupOf R).Normal) [hRs : IsSimpleGroup (↥R ⧸ N.subgroupOf R)]
    (hRn : ∃ x y : ↥R ⧸ N.subgroupOf R, x * y ≠ y * x) {c : ℕ}
    (hRcard : Nat.card (↥R ⧸ N.subgroupOf R) = c)
    (hc1 : Nat.card (cen N) * (Nat.card (cen N) ^ 2 - 1) < c)
    (hc2 : Nat.card (cen N) ^ 12 * (Nat.card (cen N) ^ 4 - 1) * ((Nat.card (cen N) ^ 2 - 1) *
      (Nat.card (cen N) ^ 4 - 1) * (Nat.card (cen N) ^ 6 - 1)) < c)
    (hc3 : Nat.card (cen N) ^ 12 * (Nat.card (cen N) ^ 4 + 1) * ((Nat.card (cen N) ^ 2 - 1) *
      (Nat.card (cen N) ^ 4 - 1) * (Nat.card (cen N) ^ 6 - 1)) < c) : False := by
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hperf : QuotSat R N (fun Y _ => Group.IsPerfect Y) :=
    ⟨hnR, isPerfect_of_isSimpleGroup_of_noncomm hRn⟩
  obtain ⟨S, hNS, hSC, hRS, hT⟩ := secondCfg_le (Or.inr rfl) hS hW (fun h => by omega)
    (fun h => by omega) hNR hRC hperf hirr
  rcases hT with ⟨h84, -⟩ | ⟨m, hm2, hm, hQ⟩
  · omega
  · have hm4 : m = 4 := by omega
    subst hm4
    rcases hQ with hQp | hQm
    · obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQp
      obtain ⟨hAs, hAn, -, hAcard⟩ := isSLModel_two_facts hqa hA
      obtain ⟨hBs, hBn, -, hBcard⟩ := isOmegaPlus_four_facts hqa hB
      haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
      haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B))) (fun x y h =>
        (Prod.mk.inj h).1)
      haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b)) (fun x y h =>
        (Prod.mk.inj h).2)
      haveI := hnR
      rcases quot_embeds_prod hNR hRS e with h | ⟨h, -⟩
      · rw [hRcard, hAcard] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hBcard] at h
        exact absurd h (not_le.mpr hc2)
    · obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQm
      obtain ⟨hAs, hAn, -, hAcard⟩ := isSLModel_two_facts hqa hA
      obtain ⟨hBs, hBn, -, hBcard⟩ := isOmegaMinus_four_facts hqa hB
      haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
      haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B))) (fun x y h =>
        (Prod.mk.inj h).1)
      haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b)) (fun x y h =>
        (Prod.mk.inj h).2)
      haveI := hnR
      rcases quot_embeds_prod hNR hRS e with h | ⟨h, -⟩
      · rw [hRcard, hAcard] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hBcard] at h
        exact absurd h (not_le.mpr hc3)

theorem secondCfgFalse_sp4 : SecondCfgFalse (IsSpModel 4) 8 := by
  intro X _ _ N R hS _ hW hNR hRC hQS hirr
  obtain ⟨hnR, hP⟩ := hQS
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hq4 : 4 ≤ Nat.card (cen N) := hS.1.q4
  obtain ⟨hRs, hRn⟩ := isSpModel_facts hqa (by norm_num) hP
  haveI := hRs
  exact width8_false_of_large hS hW hNR hRC hirr hnR hRn (isSpModel_four_card hqa hP)
    (sl2_lt_sp8 _ hq4) (op8_lt_sp8 _ hq4) (om8_lt_sp8 _ hq4)

theorem secondCfgFalse_omegaPlus5 : SecondCfgFalse (IsOmegaPlus 5) 8 := by
  intro X _ _ N R hS _ hW hNR hRC hQS hirr
  obtain ⟨hnR, hP⟩ := hQS
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hq4 : 4 ≤ Nat.card (cen N) := hS.1.q4
  obtain ⟨hRs, hRn⟩ := isOmegaPlus_facts hqa (by norm_num) hP
  haveI := hRs
  exact width8_false_of_large hS hW hNR hRC hirr hnR hRn (isOmegaPlus_five_card hqa hP)
    (sl2_lt_op10 _ hq4) (op8_lt_op10 _ hq4) (om8_lt_op10 _ hq4)

theorem width4_false_of_large {N R : Subgroup X} (hS : ConfigSatz N)
    (hW : Width N (cen N) 4) (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement)
    (hNR : N ≤ R) (hRC : R ≤ Subgroup.centralizer ((cen N : Subgroup X) : Set X))
    (hirr : ∀ A : Subgroup X, cen N ≤ A → A ≤ N → (∀ r ∈ R, conjSubgroup r A = A) →
      A = cen N ∨ A = N)
    (hnR : (N.subgroupOf R).Normal) [hRs : IsSimpleGroup (↥R ⧸ N.subgroupOf R)]
    (hRn : ∃ x y : ↥R ⧸ N.subgroupOf R, x * y ≠ y * x) {c : ℕ}
    (hRcard : Nat.card (↥R ⧸ N.subgroupOf R) = c)
    (hc1 : Nat.card (cen N) * (Nat.card (cen N) ^ 2 - 1) < c)
    (hc2 : Nat.card (cen N) ^ 3 * (Nat.card (cen N) ^ 6 - 1) < c)
    (hc3 : Nat.card (cen N) ^ 2 * (Nat.card (cen N) ^ 4 - 1) < c) : False := by
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hperf : QuotSat R N (fun Y _ => Group.IsPerfect Y) :=
    ⟨hnR, isPerfect_of_isSimpleGroup_of_noncomm hRn⟩
  obtain ⟨S, hNS, hSC, hRS, hT⟩ := secondCfg_le (Or.inl rfl) hS hW (fun _ => hgen)
    (fun _ => hCi) hNR hRC hperf hirr
  haveI := hnR
  rcases hT with ⟨-, hS3⟩ | ⟨m, hm2, hm, hQ⟩
  · obtain ⟨hnS, hX⟩ := hS3
    haveI := hnS
    have hq3 : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) ^ 3 = 2 ^ a' :=
      ⟨3 * a, by omega, by rw [haq, ← pow_mul, mul_comm]⟩
    obtain ⟨-, -, -, hXcard⟩ := isSLModel_two_facts hq3 hX
    obtain ⟨ι, hι, -⟩ := exists_injective_quotient hNR hRS
    have hle : Nat.card (↥R ⧸ N.subgroupOf R) ≤ Nat.card (↥S ⧸ N.subgroupOf S) :=
      Nat.card_le_card_of_injective ι hι
    rw [hRcard, hXcard, ← pow_mul] at hle
    exact absurd hle (not_le.mpr hc2)
  · have hm2' : m = 2 := by omega
    subst hm2'
    rcases hQ with hQp | hQm
    · obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQp
      haveI := hnS
      obtain ⟨B₁, B₂, _, _, hB₁, hB₂, ⟨e'⟩⟩ := isOmegaPlus_two_split hqa hB
      obtain ⟨-, -, -, hAc⟩ := isSLModel_two_facts hqa hA
      obtain ⟨-, -, -, hB₁c⟩ := isSLModel_two_facts hqa hB₁
      obtain ⟨-, -, -, hB₂c⟩ := isSLModel_two_facts hqa hB₂
      let e3 : ↥S ⧸ N.subgroupOf S ≃* A × (B₁ × B₂) :=
        e.trans (MulEquiv.prodCongr (MulEquiv.refl A) e')
      haveI : Finite (A × (B₁ × B₂)) := Finite.of_equiv _ e3.toEquiv
      haveI : Finite A := Finite.of_injective (fun a : A => (a, ((1 : B₁), (1 : B₂))))
        (fun x y h => (Prod.mk.inj h).1)
      haveI : Finite B₁ := Finite.of_injective (fun b : B₁ => ((1 : A), (b, (1 : B₂))))
        (fun x y h => (Prod.mk.inj (Prod.mk.inj h).2).1)
      haveI : Finite B₂ := Finite.of_injective (fun b : B₂ => ((1 : A), ((1 : B₁), b)))
        (fun x y h => (Prod.mk.inj (Prod.mk.inj h).2).2)
      obtain ⟨ι, hι, -⟩ := exists_injective_quotient hNR hRS
      rcases card_le_or_le_of_embeds3 (e3.toMonoidHom.comp ι) (e3.injective.comp hι) with
        h | h | h
      · rw [hRcard, hAc] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hB₁c] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hB₂c] at h
        exact absurd h (not_le.mpr hc1)
    · obtain ⟨hnS, A, B, _, _, hA, hB, ⟨e⟩⟩ := hQm
      haveI := hnS
      obtain ⟨-, -, -, hAc⟩ := isSLModel_two_facts hqa hA
      obtain ⟨-, -, -, hBc⟩ := isOmegaMinus_two_facts hqa hB
      haveI : Finite (A × B) := Finite.of_equiv _ e.toEquiv
      haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B))) (fun x y h =>
        (Prod.mk.inj h).1)
      haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b)) (fun x y h =>
        (Prod.mk.inj h).2)
      rcases quot_embeds_prod hNR hRS e with h | ⟨h, -⟩
      · rw [hRcard, hAc] at h
        exact absurd h (not_le.mpr hc1)
      · rw [hRcard, hBc] at h
        exact absurd h (not_le.mpr hc3)

theorem secondCfgFalse_sp3 (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement) :
    SecondCfgFalse (IsSpModel 3) 4 := by
  intro X _ _ N R hS _ hW hNR hRC hQS hirr
  obtain ⟨hnR, hP⟩ := hQS
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hq4 : 4 ≤ Nat.card (cen N) := hS.1.q4
  obtain ⟨hRs, hRn⟩ := isSpModel_facts hqa (by norm_num) hP
  haveI := hRs
  exact width4_false_of_large hS hW hgen hCi hNR hRC hirr hnR hRn (isSpModel_three_card hqa hP)
    (sl2_lt_sp6 _ hq4) (sl2c_lt_sp6 _ hq4) (om4_lt_sp6 _ hq4)

theorem secondCfgFalse_omegaPlus4 (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement) :
    SecondCfgFalse (IsOmegaPlus 4) 4 := by
  intro X _ _ N R hS _ hW hNR hRC hQS hirr
  obtain ⟨hnR, hP⟩ := hQS
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hq4 : 4 ≤ Nat.card (cen N) := hS.1.q4
  obtain ⟨hRs, hRn, -, hRcard⟩ := isOmegaPlus_four_facts hqa hP
  haveI := hRs
  exact width4_false_of_large hS hW hgen hCi hNR hRC hirr hnR hRn hRcard
    (sl2_lt_op8 _ hq4) (sl2c_lt_op8 _ hq4) (om4_lt_op8 _ hq4)

theorem secondCfgFalse_omegaMinus3 (hgen : StrothGenByBStatement) (hCi : Stroth4iStatement) :
    SecondCfgFalse (IsOmegaMinus 3) 4 := by
  intro X _ _ N R hS _ hW hNR hRC hQS hirr
  obtain ⟨hnR, hP⟩ := hQS
  obtain ⟨a, ha2, haq⟩ := hS.card_cen
  have hqa : ∃ a' : ℕ, 2 ≤ a' ∧ Nat.card (cen N) = 2 ^ a' := ⟨a, ha2, haq⟩
  have hq4 : 4 ≤ Nat.card (cen N) := hS.1.q4
  obtain ⟨hRs, hRn, hRcard⟩ := isOmegaMinus_three_facts hqa hP
  haveI := hRs
  exact width4_false_of_large hS hW hgen hCi hNR hRC hirr hnR hRn hRcard
    (sl2_lt_um6 _ hq4) (sl2c_lt_um6 _ hq4) (om4_lt_um6 _ hq4)

end CFSG.RankThree.GF2n.Stroth80
