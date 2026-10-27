module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6Data
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6
import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofTwoGroup
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open Equiv

namespace Item419Res3

@[expose] def AutThreeTwo (X : Type) [Group X] : Prop :=
  ∀ β : MulAut X, β ^ 3 = 1 → β ≠ 1 →
    ∃ T : Subgroup X, IsPGroup 2 T ∧ (∀ t ∈ T, β t ∈ T) ∧ ∃ t ∈ T, β t ≠ t

@[expose] def ElemThreeTwo (X : Type) [Group X] : Prop :=
  ∀ k : X, k ^ 3 = 1 → k ≠ 1 →
    ∃ T : Subgroup X, IsPGroup 2 T ∧ (∀ t ∈ T, k * t * k⁻¹ ∈ T) ∧ ∃ t ∈ T, k * t * k⁻¹ ≠ t

@[expose] def OuterThreeTwo (X : Type) [Group X] : Prop :=
  ∀ β : MulAut X, β ^ 3 = 1 → ¬ IsInnerAut β →
    ∃ T : Subgroup X, IsPGroup 2 T ∧ (∀ t ∈ T, β t ∈ T) ∧ ∃ t ∈ T, β t ≠ t

theorem autThreeTwo_of {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) (hin : ElemThreeTwo X)
    (hout : OuterThreeTwo X) : AutThreeTwo X := by
  intro β hβ3 hβ1
  by_cases hβ : IsInnerAut β
  · obtain ⟨k, rfl⟩ := hβ
    have hk3 : k ^ 3 = 1 := by
      have h1 : MulAut.conj (k ^ 3) = 1 := by rw [map_pow]; exact hβ3
      have h2 : k ^ 3 ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun γ : MulAut X => γ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * k ^ 3 = k ^ 3 * y * (k ^ 3)⁻¹ * k ^ 3 := by rw [this]
          _ = k ^ 3 * y := by group
      rwa [hZ, Subgroup.mem_bot] at h2
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hβ1 (map_one _)
    obtain ⟨T, hT, hTn, t, htT, ht⟩ := hin k hk3 hk1
    exact ⟨T, hT, fun s hs => hTn s hs, t, htT, ht⟩
  · exact hout β hβ3 hβ

theorem outerThreeTwo_of_forall {X : Type} [Group X]
    (h : ∀ β : MulAut X, β ^ 3 = 1 → IsInnerAut β) : OuterThreeTwo X :=
  fun β hβ3 hβ => (hβ (h β hβ3)).elim

theorem autThreeTwo_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutThreeTwo Y) : AutThreeTwo X := by
  intro β hβ3 hβ1
  set β' := MulAut.congr e β with hβ'
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hβ3, map_one]
  have hβ'1 : β' ≠ 1 := fun h1 => hβ1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  obtain ⟨T, hT, hTn, t, htT, ht⟩ := h β' hβ'3 hβ'1
  have happ : ∀ x : X, β' (e x) = e (β x) := fun x => by
    rw [hβ']
    show e (β (e.symm (e x))) = e (β x)
    rw [MulEquiv.symm_apply_apply]
  refine ⟨T.comap e.toMonoidHom, hT.comap_of_injective e.toMonoidHom e.injective, ?_,
    e.symm t, ?_, ?_⟩
  · intro x hx
    change e (β x) ∈ T
    rw [← happ]
    exact hTn _ hx
  · change e (e.symm t) ∈ T
    rw [MulEquiv.apply_symm_apply]
    exact htT
  · intro h1
    apply ht
    have h2 := congrArg e h1
    rw [← happ, MulEquiv.apply_symm_apply] at h2
    exact h2

theorem k419AutThree_of_autThreeTwo
    (h : ∀ (X : Type) [Group X], IsType419 X → AutThreeTwo X) : K419AutThree := by
  intro G _ _ K ht b hb hb3 hbC
  set β : MulAut K := K.normalizerMonoidHom ⟨b, hb⟩ with hβ
  have happ : ∀ k : K, ((β k : K) : G) = b * k * b⁻¹ := fun k => rfl
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨b, hb⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext hb3
    rw [this, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hbC
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 := congrArg (fun γ : MulAut K => ((γ ⟨k, hk⟩ : K) : G)) h1
    simp only [MulAut.one_apply] at h2
    rw [happ] at h2
    calc k * b = b * k * b⁻¹ * b := by rw [h2]
      _ = b * k := by group
  obtain ⟨T, hT, hTn, t, htT, ht'⟩ := h K ht β hβ3 hβ1
  refine ⟨T.map K.subtype, Subgroup.map_subtype_le T, hT.map K.subtype, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨β y, hTn y hy, ?_⟩
    exact happ y
  · intro hle
    apply ht'
    have h1 : (t : G) * b = b * (t : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨t, htT, rfl⟩)
    apply Subtype.ext
    rw [happ, ← h1, mul_inv_cancel_right]

@[expose] def subgroupOfInvolutions {Y : Type*} [Group Y] [DecidableEq Y] (F : Finset Y)
    (h1 : (1 : Y) ∈ F) (hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) (hinv : ∀ x ∈ F, x * x = 1) :
    Subgroup Y where
  carrier := ↑F
  one_mem' := h1
  mul_mem' {x y} hx hy := hmul x hx y hy
  inv_mem' {x} hx := by
    have : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hinv x hx)
    rw [this]
    exact hx

@[expose] def fourA : Finset (Perm (Fin 6)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

@[expose] def fourB : Finset (Perm (Fin 6)) :=
  {1, swap 0 3 * swap 1 4, swap 1 4 * swap 2 5, swap 0 3 * swap 2 5}

theorem fourA_group : (1 : Perm (Fin 6)) ∈ fourA ∧ (∀ x ∈ fourA, ∀ y ∈ fourA, x * y ∈ fourA) ∧
    (∀ x ∈ fourA, x * x = 1) ∧ (∀ x ∈ fourA, Perm.sign x = 1) := by
  decide +kernel

theorem fourA_norm :
    ∀ x ∈ fourA, Sec14.Item148HJ.cA * x * Sec14.Item148HJ.cA⁻¹ ∈ fourA := by
  decide +kernel

theorem fourA_move : swap 0 1 * swap 2 3 ∈ fourA ∧
    Sec14.Item148HJ.cA * (swap 0 1 * swap 2 3) * Sec14.Item148HJ.cA⁻¹ ≠ swap 0 1 * swap 2 3 := by
  decide +kernel

theorem fourA_facts : (1 : Perm (Fin 6)) ∈ fourA ∧ (∀ x ∈ fourA, ∀ y ∈ fourA, x * y ∈ fourA) ∧
    (∀ x ∈ fourA, x * x = 1) ∧ (∀ x ∈ fourA, Perm.sign x = 1) ∧
    (∀ x ∈ fourA, Sec14.Item148HJ.cA * x * Sec14.Item148HJ.cA⁻¹ ∈ fourA) ∧
    ∃ x ∈ fourA, Sec14.Item148HJ.cA * x * Sec14.Item148HJ.cA⁻¹ ≠ x :=
  ⟨fourA_group.1, fourA_group.2.1, fourA_group.2.2.1, fourA_group.2.2.2, fourA_norm, _,
    fourA_move.1, fourA_move.2⟩

theorem fourB_group : (1 : Perm (Fin 6)) ∈ fourB ∧ (∀ x ∈ fourB, ∀ y ∈ fourB, x * y ∈ fourB) ∧
    (∀ x ∈ fourB, x * x = 1) ∧ (∀ x ∈ fourB, Perm.sign x = 1) := by
  decide +kernel

theorem fourB_norm :
    ∀ x ∈ fourB, Sec14.Item148HJ.cB * x * Sec14.Item148HJ.cB⁻¹ ∈ fourB := by
  decide +kernel

theorem fourB_move : swap 0 3 * swap 1 4 ∈ fourB ∧
    Sec14.Item148HJ.cB * (swap 0 3 * swap 1 4) * Sec14.Item148HJ.cB⁻¹ ≠ swap 0 3 * swap 1 4 := by
  decide +kernel

theorem fourB_facts : (1 : Perm (Fin 6)) ∈ fourB ∧ (∀ x ∈ fourB, ∀ y ∈ fourB, x * y ∈ fourB) ∧
    (∀ x ∈ fourB, x * x = 1) ∧ (∀ x ∈ fourB, Perm.sign x = 1) ∧
    (∀ x ∈ fourB, Sec14.Item148HJ.cB * x * Sec14.Item148HJ.cB⁻¹ ∈ fourB) ∧
    ∃ x ∈ fourB, Sec14.Item148HJ.cB * x * Sec14.Item148HJ.cB⁻¹ ≠ x :=
  ⟨fourB_group.1, fourB_group.2.1, fourB_group.2.2.1, fourB_group.2.2.2, fourB_norm, _,
    fourB_move.1, fourB_move.2⟩

theorem elem_witness_of_conj {h : alternatingGroup (Fin 6)} {σ c : Perm (Fin 6)}
    (hσ : σ * (h : Perm (Fin 6)) * σ⁻¹ = c) {F : Finset (Perm (Fin 6))}
    (hF : (1 : Perm (Fin 6)) ∈ F ∧ (∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) ∧ (∀ x ∈ F, x * x = 1) ∧
      (∀ x ∈ F, Perm.sign x = 1) ∧ (∀ x ∈ F, c * x * c⁻¹ ∈ F) ∧ ∃ x ∈ F, c * x * c⁻¹ ≠ x) :
    ∃ T : Subgroup (alternatingGroup (Fin 6)), IsPGroup 2 T ∧
      (∀ t ∈ T, h * t * h⁻¹ ∈ T) ∧ ∃ t ∈ T, h * t * h⁻¹ ≠ t := by
  obtain ⟨h1, hmul, hinv, hsign, hnorm, v, hvF, hv⟩ := hF
  set V := subgroupOfInvolutions F h1 hmul hinv
  set T : Subgroup (alternatingGroup (Fin 6)) :=
    (V.comap (MulAut.conj σ).toMonoidHom).comap (alternatingGroup (Fin 6)).subtype with hT
  have hmemT : ∀ y : alternatingGroup (Fin 6), y ∈ T ↔ σ * (y : Perm (Fin 6)) * σ⁻¹ ∈ F :=
    fun y => Iff.rfl
  have hconj : ∀ y : alternatingGroup (Fin 6),
      σ * ((h * y * h⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ⁻¹ =
        c * (σ * (y : Perm (Fin 6)) * σ⁻¹) * c⁻¹ := by
    intro y
    rw [← hσ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  refine ⟨T, ?_, ?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    set y : Perm (Fin 6) := ((g : alternatingGroup (Fin 6)) : Perm (Fin 6)) with hy
    have hg : σ * y * σ⁻¹ ∈ F := (hmemT _).mp g.2
    have h2 := hinv _ hg
    have h3 : y * y = 1 := by
      have h4 : σ * (y * y) * σ⁻¹ = 1 := by rw [← h2]; group
      have h5 := congrArg (fun z => σ⁻¹ * z * σ) h4
      simpa [mul_assoc] using h5
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext h3)
  · intro t ht
    rw [hmemT, hconj]
    exact hnorm _ ((hmemT t).mp ht)
  ·
    have hvA : σ⁻¹ * v * σ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, hsign v hvF, mul_one,
        ← Perm.sign_mul, inv_mul_cancel, Perm.sign_one]
    refine ⟨⟨σ⁻¹ * v * σ, hvA⟩, ?_, ?_⟩
    · rw [hmemT]
      change σ * (σ⁻¹ * v * σ) * σ⁻¹ ∈ F
      simpa [mul_assoc] using hvF
    · intro heq
      apply hv
      have h2 := congrArg (fun y : alternatingGroup (Fin 6) => σ * (y : Perm (Fin 6)) * σ⁻¹) heq
      simp only at h2
      rw [hconj] at h2
      have h3 : σ * (σ⁻¹ * v * σ) * σ⁻¹ = v := by group
      change c * (σ * (σ⁻¹ * v * σ) * σ⁻¹) * c⁻¹ = σ * (σ⁻¹ * v * σ) * σ⁻¹ at h2
      rwa [h3] at h2

theorem elemThreeTwo_alternatingGroup_six : ElemThreeTwo (alternatingGroup (Fin 6)) := by
  intro h h3 h1
  have hx3 : (h : Perm (Fin 6)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3]
    rfl
  have hx1 : (h : Perm (Fin 6)) ≠ 1 := fun e => h1 (Subtype.ext e)
  obtain ⟨σ, hσ | hσ⟩ := Sec14.Item148HJ.exists_conj_eq_rep hx3 hx1
  · exact elem_witness_of_conj hσ fourA_facts
  · exact elem_witness_of_conj hσ fourB_facts

theorem autThreeTwo_alternatingGroup_six : AutThreeTwo (alternatingGroup (Fin 6)) :=
  autThreeTwo_of (alternatingGroup.center_eq_bot (by simp)) elemThreeTwo_alternatingGroup_six
    (outerThreeTwo_of_forall fun _ hβ => Sec14.Item148PtRes.mem_inner_of_pow_three hβ)

theorem isInnerAut_of_isPGroup_two_outer {X : Type} [Group X] [Finite X]
    (h2 : IsPGroup 2 (Outer X)) {β : MulAut X} (hβ3 : β ^ 3 = 1) : IsInnerAut β := by
  have : Finite (MulAut X) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hS : ¬ 3 ∣ Nat.card (Outer X) := by
    rw [hk]
    intro h3
    have := (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  exact Sec21.Item21Res7Proof.mem_inner_of_not_three_dvd hS (k := 1) (by rw [pow_one]; exact hβ3)

theorem outerThreeTwo_tits
    {X : Type} [Group X] (hX : ReeTitsModel X .Tits 2 1) :
    OuterThreeTwo X := by
  have : Finite X := by
    obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 hX
    exact Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨h2, -⟩ := CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier X 2 1 hX
  exact outerThreeTwo_of_forall fun _ hβ => isInnerAut_of_isPGroup_two_outer h2 hβ

theorem outerThreeTwo_u33 : OuterThreeTwo (projSU 3 3 1) := by
  have h := unitaryFieldData_galoisField 3 1 le_rfl
  set e := projSUEquivUnitaryPSU 3 1 h
  have hcard : Nat.card (Outer (unitaryPSU h 3)) = 2 := by
    rw [(CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order h
      le_rfl (by norm_num)).2.2.2.2.1]
    norm_num
  have hS : ¬ 3 ∣ Nat.card (Outer (unitaryPSU h 3)) := by rw [hcard]; norm_num
  refine outerThreeTwo_of_forall fun β hβ3 => ?_
  have hβ' : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hin := Sec21.Item21Res7Proof.mem_inner_of_not_three_dvd hS (k := 1)
    (by rw [pow_one]; exact hβ')
  exact (KFacts.isInnerAut_congr e β).mp hin

end Item419Res3

open Item419Res3

@[expose] def K419AutThreeInnerSp4 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ElemThreeTwo (projSp 2 (GaloisField 2 n))

@[expose] def K419AutThreeOuterSp4 : Prop :=
  ∀ n : ℕ, 2 ≤ n → OuterThreeTwo (projSp 2 (GaloisField 2 n))

@[expose] def K419AutThreeInnerG2 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), ChevalleyExceptionalModel X .G2 2 n → ElemThreeTwo X

@[expose] def K419AutThreeOuterG2 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), ChevalleyExceptionalModel X .G2 2 n → OuterThreeTwo X

@[expose] def K419AutThreeInnerF4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), ReeTitsModel X .twistedF4 2 n → ElemThreeTwo X

@[expose] def K419AutThreeOuterF4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), ReeTitsModel X .twistedF4 2 n → OuterThreeTwo X

@[expose] def K419AutThreeInnerTits : Prop :=
  ∀ (X : Type) [Group X], ReeTitsModel X .Tits 2 1 → ElemThreeTwo X

@[expose] def K419AutThreeInnerU33 : Prop :=
  ElemThreeTwo (projSU 3 3 1)

theorem k419AutThree_of
    (hSpI : K419AutThreeInnerSp4) (hSpO : K419AutThreeOuterSp4) (hG2I : K419AutThreeInnerG2)
    (hG2O : K419AutThreeOuterG2) (hF4I : K419AutThreeInnerF4) (hF4O : K419AutThreeOuterF4)
    (hTI : K419AutThreeInnerTits) (hUI : K419AutThreeInnerU33) : K419AutThree := by
  apply k419AutThree_of_autThreeTwo
  intro X _ ht
  have hZ := Res419Two.center_eq_bot_of_isType419 ht
  rcases ht with ⟨n, hG2⟩ | hU' | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e⟩⟩ | hA
  · exact autThreeTwo_of hZ (hG2I X n hG2) (hG2O X n hG2)
  · obtain ⟨e⟩ := hU'
    have hU : IsType419 (projSU 3 3 1) := Or.inr (Or.inl ⟨MulEquiv.refl _⟩)
    exact autThreeTwo_of_mulEquiv e
      (autThreeTwo_of (Res419Two.center_eq_bot_of_isType419 hU) hUI outerThreeTwo_u33)
  · exact autThreeTwo_of hZ (hF4I X n hF4) (hF4O X n hF4)
  · exact autThreeTwo_of hZ (hTI X hT) (outerThreeTwo_tits hT)
  · have hS : IsType419 (projSp 2 (GaloisField 2 n)) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨MulEquiv.refl _⟩⟩))))
    exact autThreeTwo_of_mulEquiv e
      (autThreeTwo_of (Res419Two.center_eq_bot_of_isType419 hS) (hSpI n hn) (hSpO n hn))
  · obtain ⟨e⟩ := hA
    exact autThreeTwo_of_mulEquiv e autThreeTwo_alternatingGroup_six

end CFSG.RankThree.PartTwo.Sec4
