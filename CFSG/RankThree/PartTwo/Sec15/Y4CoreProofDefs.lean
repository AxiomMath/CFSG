module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsComp
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofY4
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def comp3In (Y : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ thetaComponentsIn Y ∧ J = oPrimeResidualOf 3 J}

@[expose] noncomputable def Y4CoreReadR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY A, Y = delta A (lB A) Y →
      (∃ J₁ J₂ : Subgroup G, ∀ J ∈ comp3In Y, J = J₁ ∨ J = J₂) ∧
        deltaZero A (lB A) Y ≤ sSup (comp3In Y) ⊔ pPrimeCoreOf 3 Y

@[expose] noncomputable def Y4CoreMemR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        J ∈ scriptY0 A (lB A)

namespace Y4Core

omit [Finite G] in
theorem map_conj_map_conj (X : Subgroup G) (g h : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      X.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem map_conj_one (X : Subgroup G) : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  simp

omit [Finite G] in
theorem map_conj_pow_succ (X : Subgroup G) (g : G) (k : ℕ) :
    X.map (MulAut.conj (g ^ (k + 1))).toMonoidHom =
      (X.map (MulAut.conj (g ^ k)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_conj_map_conj, pow_succ']

omit [Finite G] in
theorem map_conj_eq_of_odd {S : Set (Subgroup G)} {J₁ J₂ : Subgroup G}
    (hS : ∀ J ∈ S, J = J₁ ∨ J = J₂) {g : G} {n : ℕ} (hn : Odd n) (hg : g ^ n = 1)
    (hgS : ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) {J : Subgroup G} (hJ : J ∈ S) :
    J.map (MulAut.conj g).toMonoidHom = J := by
  set σ : Subgroup G → Subgroup G := fun X => X.map (MulAut.conj g).toMonoidHom with hσ
  have hσinj : Function.Injective σ := Subgroup.map_injective (MulAut.conj g).injective
  by_contra hne
  have h1 : σ J ∈ S := hgS J hJ
  have h2 : σ (σ J) ∈ S := hgS _ h1
  have hne2 : σ (σ J) ≠ σ J := fun h => hne (hσinj h)
  have h3 : σ (σ J) = J := by
    have hne' : σ J ≠ J := hne
    rcases hS J hJ with hJ1 | hJ1 <;> rcases hS _ h1 with h11 | h11 <;>
      rcases hS _ h2 with h21 | h21
    all_goals first
      | exact absurd (h11.trans hJ1.symm) hne'
      | exact absurd (h21.trans h11.symm) hne2
      | exact h21.trans hJ1.symm
  have hsq : J.map (MulAut.conj (g ^ 2)).toMonoidHom = J := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, map_conj_pow_succ, pow_one]
    exact h3
  have heven : ∀ k : ℕ, J.map (MulAut.conj (g ^ (2 * k))).toMonoidHom = J := by
    intro k
    induction k with
    | zero => rw [Nat.mul_zero, pow_zero, map_conj_one]
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, ← map_conj_map_conj, hsq, ih]
  obtain ⟨k, rfl⟩ := hn
  apply hne
  calc σ J = (J.map (MulAut.conj (g ^ (2 * k))).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        rw [heven k]
    _ = J.map (MulAut.conj (g ^ (2 * k + 1))).toMonoidHom := (map_conj_pow_succ J g (2 * k)).symm
    _ = J := by rw [hg, map_conj_one]

omit [Finite G] in
theorem le_of_mem_comp3In {Y J : Subgroup G} (hJ : J ∈ comp3In Y) : J ≤ Y :=
  le_of_mem_thetaComponentsIn hJ.1

theorem ne_bot_of_mem_thetaComponentsIn {Y J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) :
    J ≠ ⊥ := by
  rintro rfl
  have hq := isQuasisimple_theta_of_mem_thetaComponentsIn hJ
  have : Nontrivial (↥(⊥ : Subgroup G) ⧸ aschbacherSolvableCore 3 ↥(⊥ : Subgroup G)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨x, y, hxy⟩ :=
    exists_pair_ne (↥(⊥ : Subgroup G) ⧸ aschbacherSolvableCore 3 ↥(⊥ : Subgroup G))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (by rw [Subsingleton.elim x y])

theorem ne_bot {Y J : Subgroup G} (hJ : J ∈ comp3In Y) : J ≠ ⊥ :=
  ne_bot_of_mem_thetaComponentsIn hJ.1

theorem not_le_pPrimeCoreOf {Y J : Subgroup G} (hJ : J ∈ comp3In Y) :
    ¬ J ≤ pPrimeCoreOf 3 Y := by
  intro hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card J := fun h3 =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y))
      (h3.trans (Subgroup.card_dvd_of_le hle))
  apply ne_bot hJ
  rw [hJ.2]
  exact Sec16.Proof1610.oPrimeResidualOf_eq_bot_of_coprime h3

theorem pPrimeCoreOf_le_normalizer {Y J : Subgroup G} (hJ : J ∈ comp3In Y) :
    pPrimeCoreOf 3 Y ≤ Subgroup.normalizer (J : Set G) := by
  have hJO := not_le_pPrimeCoreOf hJ
  obtain ⟨⟨J', hJ', rfl⟩, -⟩ := hJ
  have hUs : (CFSG.pPrimeCore 3 ↥Y).IsSubnormal :=
    (CFSG.pPrimeCore_normal (p := 3) (G := ↥Y)).isSubnormal
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hJ' hUs with
    h | ⟨h, -⟩
  · exact absurd (Subgroup.map_mono h) hJO
  · exact (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map Y.subtype)

theorem three_dvd_card {Y J : Subgroup G} (hJ : J ∈ comp3In Y) : 3 ∣ Nat.card J := by
  have hJO := not_le_pPrimeCoreOf hJ
  obtain ⟨⟨J', hJ', rfl⟩, -⟩ := hJ
  by_contra h3
  apply hJO
  have h3' : ¬ 3 ∣ Nat.card J' := by
    rwa [Subgroup.card_map_of_injective Y.subtype_injective] at h3
  exact Subgroup.map_mono (Sec4.le_pPrimeCore_of_isSubnormal hJ'.2.1 h3')

theorem map_conj_mem {Y J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (hJ : J ∈ comp3In Y) : J.map (MulAut.conj g).toMonoidHom ∈ comp3In Y := by
  refine ⟨map_conj_mem_thetaComponentsIn hg hJ.1, ?_⟩
  rw [← Sec17.HeadProof.map_oPrimeResidualOf (MulAut.conj g) 3 J, ← hJ.2]

theorem mem_normalizer_of_odd {Y J₁ J₂ : Subgroup G} (hS : ∀ J ∈ comp3In Y, J = J₁ ∨ J = J₂)
    {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1)
    {J : Subgroup G} (hJ : J ∈ comp3In Y) : g ∈ Subgroup.normalizer (J : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_conj_eq_of_odd hS hn hgn (fun _ hJ' => map_conj_mem hg hJ') hJ)

theorem le_normalizer_of_isPGroup {Y J₁ J₂ : Subgroup G} (hS : ∀ J ∈ comp3In Y, J = J₁ ∨ J = J₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G} (hJ : J ∈ comp3In Y) :
    P ≤ Subgroup.normalizer (J : Set G) := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact mem_normalizer_of_odd hS (hPY hx) ((hp.odd_of_ne_two hp2).pow) hk' hJ

theorem le_normalizer_of_isElemAbelian {Y J₁ J₂ : Subgroup G}
    (hS : ∀ J ∈ comp3In Y, J = J₁ ∨ J = J₂) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    {J : Subgroup G} (hJ : J ∈ comp3In Y) : E ≤ Subgroup.normalizer (J : Set G) :=
  fun x hx => mem_normalizer_of_odd hS (hEY hx) (by decide : Odd 3) (hE.2 x hx) hJ

theorem pPrimeCoreOf_le_normalizer_sSup (Y : Subgroup G) :
    pPrimeCoreOf 3 Y ≤ Subgroup.normalizer ((sSup (comp3In Y) : Subgroup G) : Set G) :=
  le_normalizer_sSup fun _ hJ => pPrimeCoreOf_le_normalizer hJ

theorem oPrimeResidualOf_le_sSup {A : Subgroup G} (hA : Late.IsE27 A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYΔ : Y = delta A (lB A) Y)
    (hD : deltaZero A (lB A) Y ≤ sSup (comp3In Y) ⊔ pPrimeCoreOf 3 Y) :
    oPrimeResidualOf 3 Y ≤ sSup (comp3In Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, -, h3⟩ := rank3II_14_5_lB hA hbot hAY
  set D := deltaZero A (lB A) Y with hDdef
  set C := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC
  have hCD : C ≤ Subgroup.normalizer (D : Set G) := by
    refine inf_le_right.trans ?_
    rw [hYΔ]
    exact h3
  have hC3 : Nat.Coprime 3 (Nat.card C) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  have hO3 : Nat.Coprime 3 (Nat.card (pPrimeCoreOf 3 Y)) := coprime_card_pPrimeCoreOf 3 Y
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  have hyY : y ∈ D ⊔ C := by
    rw [← h1, ← hYΔ]
    exact hy
  have hyD : y ∈ D := mem_of_mem_sup_of_pow_eq_one hCD hC3 hyY hk
  exact mem_of_mem_sup_of_pow_eq_one (pPrimeCoreOf_le_normalizer_sSup Y) hO3 (hD hyD) hk

end Y4Core

end CFSG.RankThree.PartTwo.Sec15
