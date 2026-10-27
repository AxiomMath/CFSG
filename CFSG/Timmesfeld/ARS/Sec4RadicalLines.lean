module

public import CFSG.Timmesfeld.ARS.Sec4Radical

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section Lines

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

theorem opposite_of_le_sup_of_special {Y P₀ X S B T : Subgroup G} (hY : Y ∈ R)
    (hP₀ : P₀ ∈ lambdaSet R Y) (hX : X ∈ R) (hXle : X ≤ Y ⊔ P₀) (hB : B ∈ R) (hXB : Opposite X B)
    (hS : S ∈ R) (hSle : S ≤ Y ⊔ P₀) (hBS : Special R B S) (hT : T ∈ R) (hTle : T ≤ Y ⊔ P₀)
    (hTS : T ≠ S) : Opposite B T := by
  have hXS : X ≠ S := by
    rintro rfl
    exact Special.not_opposite hR hB hBS hXB.symm
  obtain ⟨hSΛ, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hY hP₀ hX hXle hS hSle hXS
  by_cases hTX : T = X
  · rw [hTX]
    exact hXB.symm
  have hTΛ := (mem_lambdaSet_of_le_sup hR hiso hY hP₀ hX hXle hT hTle (Ne.symm hTX)).1
  have hBT : ¬ Commuting B T := not_commuting_of_opposite_of_mem_lambdaSet hR hB hXB.symm hTΛ
  have hne : B ≠ T := fun e => hBT (e ▸ hR.commuting_self hB)
  rcases hR.rel B hB T hT hne with h | h | h
  · exact absurd h hBT
  · exact h
  · exact absurd ((existsUnique_mem_psiSet_of_le hR hiso hX hB hXB hSΛ).unique
      ⟨hT, hsup ▸ hTle, hT, h⟩ ⟨hS, le_sup_right, hS, hBS⟩) hTS

omit hR hiso in
theorem eq_of_mem_of_card_eq_two {C : Subgroup G} (hq : Nat.card C = 2) {c x : G} (hc : c ∈ C)
    (hc1 : c ≠ 1) (hx : x ∈ C) (hx1 : x ≠ 1) : x = c := by
  by_contra hne
  have hsub : ({1, c, x} : Set G) ⊆ C := by
    rintro y (rfl | rfl | rfl)
    · exact C.one_mem
    · exact hc
    · exact hx
  have h3 : ({1, c, x} : Set G).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, c, x, hc1.symm, hx1.symm, fun e => hne e.symm, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hq] at hle
  omega

omit hiso in
theorem card_eq_two_or_four_le {A : Subgroup G} (hA : A ∈ R) :
    Nat.card A = 2 ∨ 4 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hR.isPGroup hA)
  have h1 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
  rcases n with _ | _ | n
  · rw [hn, pow_zero] at h1
    omega
  · exact Or.inl (by rw [hn, pow_one])
  · refine Or.inr ?_
    rw [hn, pow_succ, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem eq_or_eq_or_eq_of_card_eq_two {Y P₀ Q₁ Q₂ Q₃ T : Subgroup G} (hY : Y ∈ R)
    (hP₀ : P₀ ∈ lambdaSet R Y) (hq : Nat.card Y = 2) (hQ₁ : Q₁ ∈ R) (hQ₁le : Q₁ ≤ Y ⊔ P₀)
    (hQ₂ : Q₂ ∈ R) (hQ₂le : Q₂ ≤ Y ⊔ P₀) (hQ₃ : Q₃ ∈ R) (hQ₃le : Q₃ ≤ Y ⊔ P₀) (h12 : Q₁ ≠ Q₂)
    (h13 : Q₁ ≠ Q₃) (h23 : Q₂ ≠ Q₃) (hT : T ∈ R) (hTle : T ≤ Y ⊔ P₀) :
    T = Q₁ ∨ T = Q₂ ∨ T = Q₃ := by
  have hsub : ({Q₁, Q₂, Q₃} : Set (Subgroup G)) ⊆ {Q | Q ∈ R ∧ Q ≤ Y ⊔ P₀} := by
    rintro Q (rfl | rfl | rfl)
    · exact ⟨hQ₁, hQ₁le⟩
    · exact ⟨hQ₂, hQ₂le⟩
    · exact ⟨hQ₃, hQ₃le⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [ncard_setOf_mem_le_sup hR hiso hY hP₀, hq,
      Set.ncard_eq_three.2 ⟨Q₁, Q₂, Q₃, h12, h13, h23, rfl⟩]) (Set.toFinite _)
  have hmem : T ∈ ({Q₁, Q₂, Q₃} : Set (Subgroup G)) := heq ▸ ⟨hT, hTle⟩
  exact hmem

theorem opposite_conjSub_of_special {X S C E : Subgroup G} {m : G} (hX : X ∈ R)
    (hC : C ∈ lambdaSet R X) (hS : S ∈ R) (hSle : S ≤ X ⊔ C) (hSC : S ≠ C) (hXS : X ≠ S)
    (hE : E ∈ R) (hCE : Opposite C E) (hES : Special R E S)
    (hXm : conjSub X m ∈ rootClosure R X) (hSm : conjSub S m ∈ rootClosure R S) :
    Opposite (conjSub C m) E := by
  have hCR : C ∈ R := hC.1.1
  have hXΛ : X ∈ lambdaSet R C := mem_lambdaSet_comm hX hC
  have hXE : Opposite X E := by
    have hEX : ¬ Commuting E X := not_commuting_of_opposite_of_mem_lambdaSet hR hE hCE.symm hXΛ
    have hne : X ≠ E := fun e => hEX (e ▸ hR.commuting_self hX)
    rcases hR.rel X hX E hE hne with h | h | h
    · exact absurd h.symm hEX
    · exact h
    · exact absurd ((existsUnique_mem_psiSet_of_le hR hiso hCR hE hCE hXΛ).unique
        ⟨hX, le_sup_right, hX, h.symm⟩ ⟨hS, (sup_comm X C) ▸ hSle, hS, hES⟩) hXS
  have hXmE : Opposite (conjSub X m) E := by
    have := omegaSet_eq_of_mem_rootClosure hR hiso hX hXm
    exact (this ▸ ⟨hE, hXE⟩ : E ∈ omegaSet R (conjSub X m)).2
  have hSmE : Special R (conjSub S m) E := by
    have := psiSet_eq_of_mem_rootClosure hR hiso hS hSm
    exact (this ▸ ⟨hE, hES.symm⟩ : E ∈ psiSet R (conjSub S m)).2
  have hCmΛ : conjSub C m ∈ lambdaSet R (conjSub X m) := conjSub_mem_lambdaSet hR hC m
  have hSmle : conjSub S m ≤ conjSub X m ⊔ conjSub C m := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono hSle
  have hSmC : conjSub S m ≠ conjSub C m := fun e => hSC (map_conj_inj.1 e)
  have hECm : ¬ Commuting E (conjSub C m) :=
    not_commuting_of_opposite_of_mem_lambdaSet hR hE hXmE.symm hCmΛ
  have hne : E ≠ conjSub C m := fun e => hECm (e ▸ hR.commuting_self hE)
  rcases hR.rel E hE _ (hR.conjSub_mem hCR m) hne with h | h | h
  · exact absurd h hECm
  · exact h.symm
  · exact absurd ((existsUnique_mem_psiSet_of_le hR hiso (hR.conjSub_mem hX m) hE hXmE
      hCmΛ).unique ⟨hR.conjSub_mem hS m, hSmle, hR.conjSub_mem hS m, hSmE.symm⟩
      ⟨hR.conjSub_mem hCR m, le_sup_right, hR.conjSub_mem hCR m, h⟩) hSmC

end Lines

section Canonical

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hZ : Subgroup.center G = ⊥)
include hR hiso hnd hZ

theorem commutatorElement_mem_radPart {X Y : Subgroup G} (hX : X ∈ R) (hY : Y ∈ omegaSet R X)
    {n u : G} (hn : n ∈ radPart R X) (hu : u ∈ gen (rootClosure R Y)) : ⁅n, u⁆ ∈ radPart R Y := by
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hX hY] at hn
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hY.1 ⟨hX, hY.2.symm⟩]
  exact commutatorElement_mem_rootNorm hR hiso hX hY.1 hY.2 hn hu

theorem commute_of_mem_radPart {X Y : Subgroup G} (hX : X ∈ R) (hY : Y ∈ omegaSet R X)
    {n m : G} (hn : n ∈ radPart R X) (hm : m ∈ radPart R Y) : Commute n m := by
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hX hY] at hn
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hY.1 ⟨hX, hY.2.symm⟩] at hm
  exact commute_of_mem_rootNorm hR hiso hnd hZ hX hY hn hm

theorem bijOn_commutatorElement_radPart {X Y : Subgroup G} (hX : X ∈ R)
    (hY : Y ∈ omegaSet R X) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) :
    Set.BijOn (fun m => ⁅m, x⁆) (radPart R Y : Set G) (radPart R X : Set G) := by
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hX hY,
    ← rootNorm_eq_radPart hR hiso hnd hZ hY.1 ⟨hX, hY.2.symm⟩]
  exact bijOn_commutatorElement_rootNorm hR hiso hnd hZ hX hY hx hx1

theorem notMem_rootElts_of_mem_radPart {X : Subgroup G} (hX : X ∈ R) {n : G}
    (hn : n ∈ radPart R X) : n ∉ rootElts R := by
  obtain ⟨Y, hY, hXY⟩ := hiso X hX
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hX ⟨hY, hXY⟩] at hn
  exact notMem_rootElts_of_mem_rootNorm hR hiso hX ⟨hY, hXY⟩ hn

theorem radPart_le_stabSet {X Y : Subgroup G} (hX : X ∈ R) (hY : Y ∈ omegaSet R X) :
    radPart R X ≤ stabSet (rootClosure R Y) := by
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hX hY]
  exact rootNorm_le_stabSet X Y

theorem exists_mul_eq_of_mem_gen_rootClosure' {X : Subgroup G} (hX : X ∈ R) {x : G}
    (hx : x ∈ gen (rootClosure R X)) : ∃ c ∈ X, ∃ n ∈ radPart R X, c * n = x := by
  obtain ⟨Y, hY, hXY⟩ := hiso X hX
  rw [← rootNorm_eq_radPart hR hiso hnd hZ hX ⟨hY, hXY⟩]
  exact exists_mul_eq_of_mem_gen_rootClosure hR hiso hX hY hXY hx

theorem radPart_le_sup_of_four_le_card {A C : Subgroup G} (hA : A ∈ R) (hC : C ∈ lambdaSet R A)
    (hq : 4 ≤ Nat.card A) :
    ∃ P ∈ R, ∃ P' ∈ R, P ≤ A ⊔ C ∧ P' ≤ A ⊔ C ∧ P ≠ C ∧ P' ≠ C ∧
      radPart R C ≤ radPart R P ⊔ radPart R P' := by
  have hCR : C ∈ R := hC.1.1
  have hAΛ : A ∈ lambdaSet R C := mem_lambdaSet_comm hA hC
  have hcard : Nat.card C = Nat.card A := hR.card_eq hCR hA
  obtain ⟨B', hB', hCB'⟩ := hiso C hCR
  obtain ⟨S, ⟨hSR, hSle, hSψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hCR hB' hCB' hAΛ
  obtain ⟨P, hPR, hPle, hPs⟩ := exists_mem_le_sup_notMem hR hiso hCR hAΛ (s := {C, S})
    ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]; omega))
  have hPC : P ≠ C := fun e => hPs (Or.inl e)
  have hPS : P ≠ S := fun e => hPs (Or.inr e)
  obtain ⟨P', hP'R, hP'le, hP's⟩ := exists_mem_le_sup_notMem hR hiso hCR hAΛ (s := {C, S, P})
    ((Set.ncard_insert_le _ _).trans (by
      have := Set.ncard_insert_le S ({P} : Set (Subgroup G))
      rw [Set.ncard_singleton] at this
      omega))
  have hP'C : P' ≠ C := fun e => hP's (Or.inl e)
  have hP'S : P' ≠ S := fun e => hP's (Or.inr (Or.inl e))
  have hPP' : P ≠ P' := fun e => hP's (Or.inr (Or.inr e.symm))
  have hB'P : Opposite B' P := opposite_of_le_sup_of_special hR hiso hCR hAΛ hCR le_sup_left hB'
    hCB' hSR hSle hSψ.2 hPR hPle hPS
  have hB'P' : Opposite B' P' := opposite_of_le_sup_of_special hR hiso hCR hAΛ hCR le_sup_left hB'
    hCB' hSR hSle hSψ.2 hP'R hP'le hP'S
  obtain ⟨hP'Λ, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hCR hAΛ hPR hPle hP'R hP'le hPP'
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
  have hle : P ≤ Subgroup.normalizer (P' : Set G) := le_normalizer_of_conjSub_le fun p hp =>
    (conjSub_of_forall_commute fun p' hp' => hP'Λ.1.2.2 p hp p' hp').le
  have hcPP' : c ∈ ((P ⊔ P' : Subgroup G) : Set G) := hsup ▸ Subgroup.mem_sup_left hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hcPP'
  obtain ⟨p, hp, p', hp', hpp'⟩ := hcPP'
  replace hpp' : p * p' = c := hpp'
  refine ⟨P, hPR, P', hP'R, sup_comm C A ▸ hPle, sup_comm C A ▸ hP'le, hPC, hP'C, ?_⟩
  intro n hn
  obtain ⟨m, hm, hmn⟩ :=
    (bijOn_commutatorElement_radPart hR hiso hnd hZ hCR ⟨hB', hCB'⟩ hc hc1).surjOn hn
  have hmn' : ⁅m, c⁆ = n := hmn
  have h1 : ⁅m, p⁆ ∈ radPart R P := commutatorElement_mem_radPart hR hiso hnd hZ hB' ⟨hPR, hB'P⟩
    hm (le_gen (mem_rootClosure_self hPR) hp)
  have h2 : ⁅m, p'⁆ ∈ radPart R P' := commutatorElement_mem_radPart hR hiso hnd hZ hB'
    ⟨hP'R, hB'P'⟩ hm (le_gen (mem_rootClosure_self hP'R) hp')
  have hcomm : Commute p ⁅m, p'⁆ :=
    ((commuting_gen_rootClosure_of_mem_centralSet ⟨hPR, hP'Λ.1.2.2.symm⟩) _
      (radPart_le_gen P' h2) p hp).symm
  have e : ⁅m, p * p'⁆ = ⁅m, p⁆ * (p * ⁅m, p'⁆ * p⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [← hmn', ← hpp', e, hcomm.eq, mul_inv_cancel_right]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

theorem radPart_le_sup_of_card_eq_two {A B C : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ omegaSet R A) (hC : C ∈ lambdaSet R A) (hBC : Special R B C)
    (hq : Nat.card A = 2) :
    ∃ D ∈ R, D ≤ A ⊔ C ∧ D ≠ A ∧ D ≠ C ∧ radPart R C ≤ radPart R A ⊔ radPart R D := by
  have hCR : C ∈ R := hC.1.1
  have hBR : B ∈ R := hB.1
  have hAB : Opposite A B := hB.2
  have hCA : C ≠ A := hC.1.2.1
  have hAΛC : A ∈ lambdaSet R C := mem_lambdaSet_comm hA hC
  obtain ⟨D, hDR, hDle, hDA, hDC⟩ := exists_mem_le_sup_ne_ne hR hiso hA hC A C
  obtain ⟨hDΛ, hsupAD⟩ := mem_lambdaSet_of_le_sup hR hiso hA hC hA le_sup_left hDR hDle hDA.symm
  obtain ⟨hCΛD, hsupDC⟩ := mem_lambdaSet_of_le_sup hR hiso hA hC hDR hDle hCR le_sup_right hDC
  have hBD : Opposite B D := opposite_of_le_sup_of_special hR hiso hA hC hA le_sup_left hBR hAB hCR
    le_sup_right hBC hDR hDle hDC
  have hAΩB : A ∈ omegaSet R B := ⟨hA, hAB.symm⟩
  have hDΩB : D ∈ omegaSet R B := ⟨hDR, hBD⟩
  have hqC : Nat.card C = 2 := (hR.card_eq hCR hA).trans hq
  have hN1 : ∀ m ∈ radPart R B, conjSub C m ∈ rootClosure R C := by
    intro m hm
    have hAm : conjSub A m ∈ rootClosure R A := conjSub_mem_of_mem_stabSet
      (radPart_le_stabSet hR hiso hnd hZ hBR hAΩB hm) (mem_rootClosure_self hA)
    have hDm : conjSub D m ∈ rootClosure R D := conjSub_mem_of_mem_stabSet
      (radPart_le_stabSet hR hiso hnd hZ hBR hDΩB hm) (mem_rootClosure_self hDR)
    have hsub : omegaSet R C ⊆ omegaSet R (conjSub C m) := by
      rintro E ⟨hE, hCE⟩
      refine ⟨hE, ?_⟩
      obtain ⟨S, ⟨hSR, hSle, hSψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hCR hE hCE hAΛC
      have hSC : S ≠ C := by
        rintro rfl
        exact Special.not_opposite hR hE hSψ.2 hCE.symm
      rcases eq_or_eq_or_eq_of_card_eq_two hR hiso hA hC hq hA le_sup_left hCR le_sup_right hDR
        hDle hCA.symm hDA.symm hDC.symm hSR (sup_comm C A ▸ hSle) with hSA | hSC' | hSD
      · subst hSA
        exact opposite_conjSub_of_special hR hiso hDR hCΛD hSR (hsupDC ▸ le_sup_left) hSC hDA hE
          hCE hSψ.2 hDm hAm
      · exact absurd hSC' hSC
      · subst hSD
        exact opposite_conjSub_of_special hR hiso hA hC hSR hDle hSC hDA.symm hE hCE hSψ.2 hAm hDm
    have heq : omegaSet R C = omegaSet R (conjSub C m) := Set.eq_of_subset_of_ncard_le hsub (by
      rw [omegaSet_conjSub hR, conjSet,
        Set.ncard_image_of_injective _ fun _ _ h => map_conj_inj.1 h]) (Set.toFinite _)
    exact mem_rootClosure_of_omegaSet_eq hR hiso hCR (hR.conjSub_mem hCR m) heq.symm
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
  have hstar : ∀ m ∈ radPart R B, ⁅m, c⁆ ∈ radPart R C := by
    intro m hm
    have hcm : m * c * m⁻¹ ∈ gen (rootClosure R C) := le_gen (hN1 m hm) (conj_mem_conjSub m hc)
    obtain ⟨c₀, hc₀, n₀, hn₀, he⟩ := exists_mul_eq_of_mem_gen_rootClosure' hR hiso hnd hZ hCR hcm
    have hc₀1 : c₀ ≠ 1 := by
      rintro rfl
      rw [one_mul] at he
      exact notMem_rootElts_of_mem_radPart hR hiso hnd hZ hCR hn₀ (he ▸ ⟨conjSub C m,
        hR.conjSub_mem hCR m, conj_mem_conjSub m hc, fun h => hc1 (conj_eq_one_iff.1 h)⟩)
    have hc₀c : c₀ = c := eq_of_mem_of_card_eq_two hqC hc hc1 hc₀ hc₀1
    have hcomm : Commute c n₀ := commuting_gen_rootClosure hR hCR c
      (le_gen (mem_rootClosure_self hCR) hc) n₀ (radPart_le_gen C hn₀)
    have : ⁅m, c⁆ = n₀ := by
      rw [commutatorElement_def, ← he, hc₀c, hcomm.eq, mul_inv_cancel_right]
    rw [this]
    exact hn₀
  have hleAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_of_conjSub_le fun a ha =>
    (conjSub_of_forall_commute fun d hd => hDΛ.1.2.2 a ha d hd).le
  have hcAD : c ∈ ((A ⊔ D : Subgroup G) : Set G) := hsupAD ▸ Subgroup.mem_sup_right hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hleAD] at hcAD
  obtain ⟨a, ha, d, hd, had⟩ := hcAD
  replace had : a * d = c := had
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at had
    have hmem : c ∈ D ⊓ C := Subgroup.mem_inf.2 ⟨had ▸ hd, hc⟩
    rw [inf_eq_bot hR hiso hDR hCR hDC, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hAle : radPart R A ≤ radPart R C ⊔ radPart R D := by
    intro n hn
    obtain ⟨m, hm, hmn⟩ := (bijOn_commutatorElement_radPart hR hiso hnd hZ hA hB ha ha1).surjOn hn
    have hmn' : ⁅m, a⁆ = n := hmn
    have h1 := hstar m hm
    have h2 : ⁅m, d⁆ ∈ radPart R D := commutatorElement_mem_radPart hR hiso hnd hZ hBR hDΩB hm
      (le_gen (mem_rootClosure_self hDR) hd)
    have hcomm : Commute a ⁅m, d⁆ :=
      ((commuting_gen_rootClosure_of_mem_centralSet ⟨hA, hDΛ.1.2.2.symm⟩) _
        (radPart_le_gen D h2) a ha).symm
    have e : ⁅m, c⁆ = ⁅m, a⁆ * ⁅m, d⁆ := by
      rw [← had]
      calc ⁅m, a * d⁆ = ⁅m, a⁆ * (a * ⁅m, d⁆ * a⁻¹) := by
            simp only [commutatorElement_def]
            group
        _ = ⁅m, a⁆ * ⁅m, d⁆ := by rw [hcomm.eq, mul_inv_cancel_right]
    have hn' : n = ⁅m, c⁆ * ⁅m, d⁆⁻¹ := by rw [e, ← hmn', mul_inv_cancel_right]
    rw [hn']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ h2))
  have hAΛD : A ∈ lambdaSet R D :=
    (mem_lambdaSet_of_le_sup hR hiso hA hC hDR hDle hA le_sup_left hDA).1
  have hsupDA : D ⊔ A = A ⊔ C :=
    (mem_lambdaSet_of_le_sup hR hiso hA hC hDR hDle hA le_sup_left hDA).2
  obtain ⟨U, hU, u, hu, hAu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hDR hAΛD hA le_sup_right
    hDA.symm hCR (hsupDA ▸ le_sup_right) hDC.symm
  have huu : u * u = 1 := hR.mul_self U hU.1.1 u hu
  have hCu : conjSub C u = A := by rw [← hAu, ← conjSub_mul, huu, conjSub_one]
  have hDu : conjSub D u = D := conjSub_of_forall_commute fun x hx => (hU.1.2.2 x hx u hu).symm
  refine ⟨D, hDR, hDle, hDA, hDC, ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj u).toMonoidHom) hAle
  rwa [Subgroup.map_sup, ← conjSub, ← conjSub, ← conjSub, conjSub_radPart hR,
    conjSub_radPart hR, conjSub_radPart hR, hAu, hCu, hDu] at this

theorem radPart_le_sup_of_special {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A)
    (hC : C ∈ lambdaSet R A) (hBC : Special R B C) :
    ∃ P ∈ R, ∃ P' ∈ R, P ≤ A ⊔ C ∧ P' ≤ A ⊔ C ∧ P ≠ C ∧ P' ≠ C ∧
      radPart R C ≤ radPart R P ⊔ radPart R P' := by
  rcases card_eq_two_or_four_le hR hA with hq | hq
  · obtain ⟨D, hDR, hDle, -, hDC, hle⟩ :=
      radPart_le_sup_of_card_eq_two hR hiso hnd hZ hA hB hC hBC hq
    exact ⟨A, hA, D, hDR, le_sup_left, hDle, hC.1.2.1.symm, hDC, hle⟩
  · exact radPart_le_sup_of_four_le_card hR hiso hnd hZ hA hC hq

end Canonical

end CFSG.Timmesfeld.ARS
