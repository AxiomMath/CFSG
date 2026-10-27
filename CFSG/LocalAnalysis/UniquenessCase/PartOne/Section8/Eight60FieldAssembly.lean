module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSp
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldSU
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldOut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List863
public import CFSG.Adapters.LieModelSimple
public import CFSG.ClassicalInvolution.Asc77.AscSCH22
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourMat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne (omegaOne)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Open (StatedProj StatedSL StatedSU StatedSp StatedScalars StatedLieTag)
open CFSG.Blueprint (LieModel classicalTags)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotient_inner_le)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom centerQuotientHom_injective)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

@[expose] def List857Clause1Lie (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 4 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧
      (LieModel X .PSL 5 p f ∨
        ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) X)) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧
      (LieModel X .PSU 5 p f ∨
        ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) X)) ∨
    (∃ p f : ℕ, LieModel X .PSp 2 p f)

@[expose] def List857Clause1Small (X : Type) [Group X] : Prop :=
  IsSpor X .M11 ∨ IsSpor X .M22 ∨ IsSpor X .M23 ∨ IsSpor X .HS ∨ IsAlt X 7 ∨ IsAlt X 6

theorem list857Clause1_iff {X : Type} [Group X] :
    List857Clause1 X ↔ List857Clause1Lie X ∨ List857Clause1Small X := by
  unfold List857Clause1 List857Clause1Lie List857Clause1Small
  simp only [or_assoc]

@[expose] def Eight60FieldNoThreeCover : Prop :=
  ∀ (X : Type) [Group X] (p f : ℕ),
    ¬ ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) X ∧
    ¬ ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) X

@[expose] def Eight60FieldSmallInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List857Clause1Small X →
    (∀ α : MulAut X, IsPGroup 3 (Subgroup.zpowers α) → α ∈ inner X) ∧
    (∀ Q : Sylow 3 X, ∀ x ∈ (Q : Subgroup X), ∀ y ∈ (Q : Subgroup X), x * y = y * x) ∧
    ¬ 3 ∣ Nat.card (Subgroup.center X)

theorem center_eq_bot_of_lieModel_clause1 {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : (t = .PSL ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ n = 2))
    (h : LieModel X t n p f) : Subgroup.center X = ⊥ := by
  have htc : t ∈ classicalTags := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hsimple : IsSimpleGroup X := LieModel.isSimpleGroup_of_mem_classicalTags htc h
  have hperf : Group.IsPerfect X := by
    rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩
    · obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel htc
      let : Field K := hfield
      let : Finite K := hfinite
      have hH : Group.IsPerfect (StatedSL n K) := by
        rcases hn with rfl | rfl
        · exact CFSG.ClassicalInvolution.Asc77.SCH.isPerfect_statedSL_four K
        · exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL K
            (by norm_num) (by omega) (by omega)
      have : Group.IsPerfect (StatedSL n K) := hH
      have : ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)).Normal :=
        Subgroup.Normal.subgroupOf (inferInstance : (StatedScalars (Fin n) K).Normal) _
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    · obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel htc
      let : Field K := hfield
      let : Finite K := hfinite
      have : Fact p.Prime := ⟨hadm.1⟩
      have : CharP K p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := p) (f := f) hK
      have hH : Group.IsPerfect (StatedSU n (p ^ f) K) :=
        CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK
          (by rcases hn with rfl | rfl <;> norm_num)
          (by rcases hn with rfl | rfl <;> simp)
      have : Group.IsPerfect (StatedSU n (p ^ f) K) := hH
      have : ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)).Normal :=
        Subgroup.Normal.subgroupOf (inferInstance : (StatedScalars (Fin n) K).Normal) _
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    · obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel htc
      let : Field K := hfield
      let : Finite K := hfinite
      have hadm' := hadm
      simp only [CFSG.Open.StatedLieAdmissible] at hadm'
      have hq2 : p ^ f ≠ 2 := by
        intro h2
        exact hadm'.2.2.2 (by simp [h2])
      have hq3 : 3 ≤ Nat.card K := by
        rw [hK]
        have h2p : 2 ≤ p := hadm'.1.two_le
        have hf1 : 1 ≤ f := hadm'.2.1
        have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        omega
      have hH : Group.IsPerfect (StatedSp 2 K) := by
        refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 K ?_
        by_cases hq3' : Nat.card K = 3
        · exact Or.inr (Or.inl ⟨hq3', by norm_num⟩)
        · left
          have : Fintype K := Fintype.ofFinite K
          have h4 : 4 ≤ Nat.card K := by omega
          obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
            (s := (Finset.univ : Finset K)) (n := 4) (by
              simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4)
          exact ⟨s, hs⟩
      have : Group.IsPerfect (StatedSp 2 K) := hH
      have : ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)).Normal :=
        Subgroup.Normal.subgroupOf
          (inferInstance : (StatedScalars (Fin 2 ⊕ Fin 2) K).Normal) _
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Group.IsPerfect X := hperf
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht'
  · exact hb
  · exfalso
    exact Group.IsPerfect.not_isMulCommutative (G := X)
      ⟨⟨fun a b => Subgroup.mem_center_iff.mp (ht' ▸ Subgroup.mem_top b) a⟩⟩

open CFSG.AGLEmbedding.KlingenSpFour (xEl xEl_mul xEl_zero xEl_inj xEl_mem_unipotent) in
theorem three_le_pRank_of_lieModel_psp_three {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : LieModel X .PSp 2 3 f) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  let : Field K := hfield
  let : Finite K := hfinite
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K 3 := hchar
  let χ : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  let fA : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 2 K :=
    { toFun := fun v => xEl (χ (v.toAdd 0)) (χ (v.toAdd 1)) (χ (v.toAdd 2))
      map_one' := by
        simp only [toAdd_one, Pi.zero_apply, map_zero, xEl_zero]
      map_mul' := by
        intro a b
        simp only [toAdd_mul, Pi.add_apply, map_add, xEl_mul] }
  let N : Subgroup (StatedSp 2 K) :=
    (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)
  let F : Multiplicative (Fin 3 → ZMod 3) →* StatedProj (StatedSp 2 K) :=
    (QuotientGroup.mk' N).comp fA
  have hcomm : ∀ a b : Multiplicative (Fin 3 → ZMod 3), a * b = b * a := fun a b => mul_comm a b
  have hpow : ∀ a : Multiplicative (Fin 3 → ZMod 3), a ^ 3 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [nsmul_eq_mul]
    change ((3 : ℕ) : ZMod 3) * Multiplicative.toAdd a i = 0
    rw [ZMod.natCast_self, zero_mul]
  have hcard : Nat.card (Multiplicative (Fin 3 → ZMod 3)) = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  have hfinj : Function.Injective F := by
    intro a b hab
    have hN : (xEl (χ (a.toAdd 0)) (χ (a.toAdd 1)) (χ (a.toAdd 2)) : StatedSp 2 K)⁻¹ *
        xEl (χ (b.toAdd 0)) (χ (b.toAdd 1)) (χ (b.toAdd 2)) ∈ N := by
      change QuotientGroup.mk' N (xEl (χ (a.toAdd 0)) (χ (a.toAdd 1)) (χ (a.toAdd 2))) =
        QuotientGroup.mk' N (xEl (χ (b.toAdd 0)) (χ (b.toAdd 1)) (χ (b.toAdd 2))) at hab
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
      exact hab
    have hU : (xEl (χ (a.toAdd 0)) (χ (a.toAdd 1)) (χ (a.toAdd 2)) : StatedSp 2 K)⁻¹ *
        xEl (χ (b.toAdd 0)) (χ (b.toAdd 1)) (χ (b.toAdd 2)) ∈
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 2 K :=
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 2 K).mul_mem
        ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 2 K).inv_mem
          (xEl_mem_unipotent _ _ _))
        (xEl_mem_unipotent _ _ _)
    have hbot : (xEl (χ (a.toAdd 0)) (χ (a.toAdd 1)) (χ (a.toAdd 2)) : StatedSp 2 K)⁻¹ *
        xEl (χ (b.toAdd 0)) (χ (b.toAdd 1)) (χ (b.toAdd 2)) = 1 := by
      have hmem : _ ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 2 K ⊓ N :=
        ⟨hU, hN⟩
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent_inf_scalars
        (r := 2) (K := K) (by norm_num)] at hmem
      exact Subgroup.mem_bot.mp hmem
    have heq : (xEl (χ (a.toAdd 0)) (χ (a.toAdd 1)) (χ (a.toAdd 2)) : StatedSp 2 K) =
        xEl (χ (b.toAdd 0)) (χ (b.toAdd 1)) (χ (b.toAdd 2)) :=
      inv_mul_eq_one.mp hbot
    obtain ⟨h0, h1, h2⟩ := xEl_inj heq
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · exact χ.injective h0
    · exact χ.injective h1
    · exact χ.injective h2
  have hproj : 3 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedSp 2 K))) :=
    CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm hpow hcard F hfinj le_top
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact hproj

theorem pRank_three_bar2_le {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ CFSG.Open.pRank 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn]
    exact fun hd => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (G := ↥L)
    (N := CFSG.pCore 2 ↥L) hN3
  have hL := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L
  exact le_of_eq (hq.trans hL.symm)

theorem ne_three_of_pRank_two_of_lieModel_psp {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {p f : ℕ} (hr : CFSG.Open.pRank 3 L = 2) (h : LieModel (Bar2 L) .PSp 2 p f) : p ≠ 3 := by
  rintro rfl
  have h1 := three_le_pRank_of_lieModel_psp_three h
  have h2 := pRank_three_bar2_le L
  omega

theorem autOmegaCentral_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hcl : (t = .PSL ∧ (n = 4 ∨ n = 5) ∧ p ^ f % 3 = 2) ∨
      (t = .PSU ∧ (n = 4 ∨ n = 5) ∧ p ^ f % 3 = 1) ∨ (t = .PSp ∧ n = 2 ∧ p ≠ 3))
    (h : LieModel X t n p f) : AutOmegaCentral X := by
  rcases hcl with ⟨rfl, hn, hq⟩ | ⟨rfl, hn, hq⟩ | ⟨rfl, rfl, hp3⟩
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
    have hX : LieModel (StatedProj (StatedSL n K)) .PSL n p f := LieModel.of_mulEquiv e h
    have hout : ¬ 3 ^ (f.factorization 3 + 1) ∣ Nat.card (Outer (StatedProj (StatedSL n K))) := by
      rcases hn with rfl | rfl
      · exact not_three_pow_succ_dvd_card_outer_of_four (Or.inl ⟨rfl, rfl⟩) hX
      · exact not_three_pow_succ_dvd_card_outer_of_five (Or.inl rfl) hX
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (StatedProj (StatedSL n K))) := by
      rw [center_eq_bot_of_lieModel_clause1 (Or.inl ⟨rfl, hn⟩) hX, Subgroup.card_bot]
      omega
    exact autOmegaCentral_of_mulEquiv e
      (autOmegaCentral_of_fieldSylowData hZ hout (fieldSylowData_statedSL hn hp hf hq hK))
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
    have hX : LieModel (StatedProj (StatedSU n (p ^ f) K)) .PSU n p f := LieModel.of_mulEquiv e h
    have hout : ¬ 3 ^ (f.factorization 3 + 1) ∣
        Nat.card (Outer (StatedProj (StatedSU n (p ^ f) K))) := by
      rcases hn with rfl | rfl
      · exact not_three_pow_succ_dvd_card_outer_of_four (Or.inr (Or.inl ⟨rfl, rfl⟩)) hX
      · exact not_three_pow_succ_dvd_card_outer_of_five (Or.inr rfl) hX
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (StatedProj (StatedSU n (p ^ f) K))) := by
      rw [center_eq_bot_of_lieModel_clause1 (Or.inr (Or.inl ⟨rfl, hn⟩)) hX, Subgroup.card_bot]
      omega
    exact autOmegaCentral_of_mulEquiv e
      (autOmegaCentral_of_fieldSylowData hZ hout (fieldSylowData_statedSU hn hp hf hq hK))
  · obtain ⟨⟨hp, hf, hadm⟩, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
    have hX : LieModel (StatedProj (StatedSp 2 K)) .PSp 2 p f := LieModel.of_mulEquiv e h
    have hq3 : 3 ≤ p ^ f := by
      have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
      have h3 : p ^ f ≠ 2 := fun h2' => hadm.2 (by simp [h2'])
      omega
    have hout : ¬ 3 ^ (f.factorization 3 + 1) ∣ Nat.card (Outer (StatedProj (StatedSp 2 K))) :=
      not_three_pow_succ_dvd_card_outer_of_four (Or.inr (Or.inr ⟨rfl, rfl⟩)) hX
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (StatedProj (StatedSp 2 K))) := by
      rw [center_eq_bot_of_lieModel_clause1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hX, Subgroup.card_bot]
      omega
    exact autOmegaCentral_of_mulEquiv e
      (autOmegaCentral_of_fieldSylowData hZ hout (fieldSylowData_statedSp hp hp3 hf hq3 hK))

theorem omegaOne_le_center_of_list857Clause1Lie {G : Type} [Group G] [Finite G]
    {M L Q P : Subgroup G} (hNC : Eight60FieldNoThreeCover)
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) (hcl : List857Clause1Lie (Bar2 L))
    (hr : CFSG.Open.pRank 3 L = 2) (hQ : IsSylowOf 3 Q L) (hP : IsSylowOf 3 P M) (hQP : Q ≤ P) :
    omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype := by
  have hPL : P ≤ Subgroup.normalizer (L : Set G) := hP.le.trans hLM
  have hZ : ∀ {t : StatedLieTag} {n p f : ℕ},
      ((t = .PSL ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSp ∧ n = 2)) →
      LieModel (Bar2 L) t n p f → ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    intro t n p f ht h
    rw [center_eq_bot_of_lieModel_clause1 ht h, Subgroup.card_bot]
    omega
  have key : AutOmegaCentral (Bar2 L) ∧ ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    rcases hcl with ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h | h⟩ | ⟨p, f, hq, h | h⟩ |
      ⟨p, f, h⟩
    · exact ⟨autOmegaCentral_of_lieModel (Or.inl ⟨rfl, Or.inl rfl, hq⟩) h,
        hZ (Or.inl ⟨rfl, Or.inl rfl⟩) h⟩
    · exact ⟨autOmegaCentral_of_lieModel (Or.inr (Or.inl ⟨rfl, Or.inl rfl, hq⟩)) h,
        hZ (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) h⟩
    · exact ⟨autOmegaCentral_of_lieModel (Or.inl ⟨rfl, Or.inr rfl, hq⟩) h,
        hZ (Or.inl ⟨rfl, Or.inr rfl⟩) h⟩
    · exact absurd h (hNC (Bar2 L) p f).1
    · exact ⟨autOmegaCentral_of_lieModel (Or.inr (Or.inl ⟨rfl, Or.inr rfl, hq⟩)) h,
        hZ (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)) h⟩
    · exact absurd h (hNC (Bar2 L) p f).2
    · exact ⟨autOmegaCentral_of_lieModel
        (Or.inr (Or.inr ⟨rfl, rfl, ne_three_of_pRank_two_of_lieModel_psp hr h⟩)) h,
        hZ (Or.inr (Or.inr ⟨rfl, rfl⟩)) h⟩
  exact omegaOne_le_center_of_autOmegaCentral hPL hP.isPGroup hQ.le hQP key.1 key.2

theorem omegaOne_le_center_of_list857Clause1Small {G : Type} [Group G] [Finite G]
    {M L Q P : Subgroup G} (hSmall : Eight60FieldSmallInput)
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) (hcl : List857Clause1Small (Bar2 L))
    (hQ : IsSylowOf 3 Q L) (hP : IsSylowOf 3 P M) (hQP : Q ≤ P) :
    omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype := by
  obtain ⟨h1, h2, h3⟩ := hSmall (Bar2 L) hcl
  exact omegaOne_le_center_of_autOmegaCentral (hP.le.trans hLM) hP.isPGroup hQ.le hQP
    (autOmegaCentral_of_oddInner h1 h2) h3

theorem omegaOne_le_center_of_list857Clause1 {G : Type} [Group G] [Finite G]
    {M L Q P : Subgroup G} (hNC : Eight60FieldNoThreeCover) (hSmall : Eight60FieldSmallInput)
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) (hcl : List857Clause1 (Bar2 L))
    (hr : CFSG.Open.pRank 3 L = 2) (hQ : IsSylowOf 3 Q L) (hP : IsSylowOf 3 P M) (hQP : Q ≤ P) :
    omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype := by
  rcases list857Clause1_iff.mp hcl with hl | hs
  · exact omegaOne_le_center_of_list857Clause1Lie hNC hLM hl hr hQ hP hQP
  · exact omegaOne_le_center_of_list857Clause1Small hSmall hLM hs hQ hP hQP


private theorem mem_center_map_subtype_iff_assembly {M : Type*} [Group M] (R : Subgroup M)
    {x : M} :
    x ∈ (Subgroup.center ↥R).map R.subtype ↔ x ∈ R ∧ ∀ r ∈ R, r * x = x * r := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun r hr => ?_⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨r, hr⟩)
    simpa using h1
  · rintro ⟨hxR, hx⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun r => Subtype.ext (hx r.1 r.2)

theorem autOmegaCentral_of_perfect_centerQuotient {K : Type} [Group K] (hK : Group.IsPerfect K)
    (h : AutOmegaCentral (K ⧸ Subgroup.center K)) : AutOmegaCentral K := by
  intro R hR
  let ρ : MulAut K →* MulAut (K ⧸ Subgroup.center K) := centerQuotientHom K
  let R' : Subgroup (MulAut (K ⧸ Subgroup.center K)) := R.map ρ
  have hR' : IsPGroup 3 R' := hR.map ρ
  have hinj : Function.Injective ρ := centerQuotientHom_injective K
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨⟨hxR, hxInner⟩, hx3⟩ := hx
  have hmem' : ρ x ∈ omegaOne 3 (R' ⊓ inner (K ⧸ Subgroup.center K)) := by
    refine Subgroup.subset_closure ⟨⟨Subgroup.mem_map_of_mem ρ hxR, ?_⟩, ?_⟩
    · exact centerQuotient_inner_le hxInner
    · rw [← map_pow, hx3, map_one]
  have hc := h R' hR' hmem'
  have hcomm := (mem_center_map_subtype_iff_assembly R').mp hc
  refine (mem_center_map_subtype_iff_assembly R).mpr ⟨hxR, fun r hr => ?_⟩
  have h2 := hcomm.2 (ρ r) (Subgroup.mem_map_of_mem ρ hr)
  exact hinj (by simpa using h2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
