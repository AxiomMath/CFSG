module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Setup
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Small
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L3SD
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L27
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512J1
public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Exc
public import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterJ1
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Blueprint (LieModel)

@[expose] def Asch80L3EpsWreathed : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (E T : Subgroup Y) (p f : ℕ), E.Normal → p.Prime → p ≠ 2 →
    ((LieModel ↥E .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel ↥E .PSU 3 p f ∧ p ^ f % 4 = 3)) →
    Subgroup.centralizer (E : Set Y) = ⊥ → IsSylowIn 2 T ⊤ → ¬ HasUniqueMaxOver T

@[expose] def L3EpsWreathedNoCalL1 : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (p f : ℕ), p.Prime → p ≠ 2 →
    ((LieModel E .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel E .PSU 3 p f ∧ p ^ f % 4 = 3)) →
    ∀ X : Subgroup E, ¬ HasCompFactor X IsCalL1

@[expose] def CalL1OverCF {Y : Type} [Group Y] (T : Subgroup Y) : Prop :=
  ∀ X : Subgroup Y, T ≤ X → ∀ (L : Type) [Group L], E1.IsCompositionFactor ↥X L → IsCalL1 L →
    E1.IsCompositionFactor Y L

@[expose] def Shape512Quot {Y : Type} [Group Y] (E : Subgroup Y) : Prop :=
  (∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 9 < p ^ e ∧ F6.IsL2 p e ↥E) ∨
  (∃ p f : ℕ, p.Prime ∧ 5 ≤ p ∧
    ((p ^ f % 3 = 2 ∧ p ^ f % 4 = 3 ∧ LieModel ↥E .PSL 3 p f) ∨
     (p ^ f % 3 = 1 ∧ p ^ f % 4 = 1 ∧ LieModel ↥E .PSU 3 p f))) ∨
  (F6.IsL2 7 1 ↥E ∧ F6.IsPGL2 7 Y) ∨
  (∃ n : ℕ, 1 ≤ n ∧ (IsL2 ↥E (2 * n) ∨ IsU3 ↥E (2 * n)))

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem calL1OverCF_of_forall {T : Subgroup Y}
    (h : ∀ X : Subgroup Y, ¬ HasCompFactor X IsCalL1) : CalL1OverCF T :=
  fun X _ L _ hcf hL => absurd ⟨L, inferInstance, hcf, hL⟩ (h X)

@[expose] def subgroupOfSwap (E X : Subgroup Y) : ↥(E.subgroupOf X) ≃* ↥(X.subgroupOf E) where
  toFun x := ⟨⟨((x : ↥X) : Y), Subgroup.mem_subgroupOf.mp x.2⟩,
    Subgroup.mem_subgroupOf.mpr (x : ↥X).2⟩
  invFun y := ⟨⟨((y : ↥E) : Y), Subgroup.mem_subgroupOf.mp y.2⟩,
    Subgroup.mem_subgroupOf.mpr (y : ↥E).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem not_hasCompFactor_of_forall_subgroup_normal {E : Subgroup Y} [E.Normal]
    (hq : Group.IsSolvable (Y ⧸ E)) (hE : ∀ X : Subgroup ↥E, ¬ HasCompFactor X IsCalL1)
    (X : Subgroup Y) : ¬ HasCompFactor X IsCalL1 := by
  rintro ⟨L, _, hcf, hL⟩
  haveI : Finite L := isCompositionFactor_finite hcf
  have h1 :=
    isCompositionFactor_subgroupOf_of_isSolvable_quot hq hcf (exists_mul_ne_of_isCalL1 hL)
  exact hE (X.subgroupOf E) ⟨L, inferInstance,
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr (subgroupOfSwap E X)).1 h1, hL⟩

theorem not_isSolvable_of_simple_normal (E : Subgroup Y) (hEs : IsSimpleGroup ↥E)
    (hEnab : ∃ a b : ↥E, a * b ≠ b * a) : ¬ Group.IsSolvable Y := by
  intro hY
  haveI : IsSimpleGroup ↥E := hEs
  haveI : Group.IsSolvable ↥E := inferInstance
  obtain ⟨a, b, hab⟩ := hEnab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)

theorem calL1OverCF_and_shape_of_psl_two_seven {E T : Subgroup Y} [E.Normal]
    (hm : LieModel ↥E .PSL 2 7 1) (hq : Group.IsSolvable (Y ⧸ E))
    (hEC : Subgroup.centralizer (E : Set Y) = ⊥) (hT : IsSylowIn 2 T ⊤) :
    CalL1OverCF T ∧ (HasUniqueMaxOver T → Shape512Quot E) := by
  refine ⟨calL1OverCF_of_forall (not_hasCompFactor_isCalL1_of_sectionalTwoRankLE hq
    (CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model
      (by norm_num) hm)), fun hU => ?_⟩
  by_cases hEtop : E = ⊤
  · exfalso
    have hY : LieModel Y .PSL 2 7 1 :=
      hm.of_mulEquiv ((MulEquiv.subgroupCongr hEtop).trans Subgroup.topEquiv)
    exact not_hasUniqueMaxOver_of_psl_two_seven hY hT hU
  · exact Or.inr (Or.inr (Or.inl ⟨hm.statedClassicalModel (by decide),
      isPGL2_seven_of_ne_top hm hEC hEtop⟩))

end Generic

section Cases

set_option linter.unusedSectionVars false


theorem asch512_quot (hA : Asch80L3EpsWreathed) (hS : L3EpsWreathedNoCalL1)
    {Y : Type} [Group Y] [Finite Y] {E T : Subgroup Y} [E.Normal]
    (hEs : IsSimpleGroup ↥E) (hEnab : ∃ a b : ↥E, a * b ≠ b * a)
    (hEC : Subgroup.centralizer (E : Set Y) = ⊥) (hq : Group.IsSolvable (Y ⧸ E))
    (hKE : CFSG.Open.IsKGroup ↥E) (h3E : CFSG.Open.pRank 3 (⊤ : Subgroup ↥E) = 1)
    (hT : IsSylowIn 2 T ⊤) (hEno : ¬ IsCalL1 ↥E) :
    (CalL1OverCF T ∧ (HasUniqueMaxOver T → Shape512Quot E)) ∨ lGen IsCalL1 ⊤ T = ⊤ := by
  have hYns : ¬ Group.IsSolvable Y := not_isSolvable_of_simple_normal E hEs hEnab
  have hTlt : T < ⊤ := lt_top_of_isSylowIn_of_not_isSolvable hT hYns
  have hsect : CFSG.GH74.SectionalTwoRankLE ↥E 2 → CalL1OverCF T := fun h =>
    calL1OverCF_of_forall (not_hasCompFactor_isCalL1_of_sectionalTwoRankLE hq h)
  have hwr : ∀ p f : ℕ, p.Prime → p ≠ 2 →
      ((LieModel ↥E .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel ↥E .PSU 3 p f ∧ p ^ f % 4 = 3)) →
      lGen IsCalL1 ⊤ T = ⊤ := fun p f hp hp2 hw =>
    lGen_eq_top_of_not_hasUniqueMaxOver
      (fun X _ _ => not_hasCompFactor_of_forall_subgroup_normal hq (hS ↥E p f hp hp2 hw) X)
      hTlt (hA Y E T p f inferInstance hp hp2 hw hEC hT)
  have hben : fusionIsBenderGroup ↥E → CalL1OverCF T := fun hB X hTX L _ hcf hL =>
    isCompositionFactor_of_bender hB hq hT hTX hcf hL
  have hp5 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → 5 ≤ p := fun p hp hp2 hp3 => by
    have := hp.two_le
    by_contra h
    interval_cases p <;> first | omega | norm_num at hp
  rcases CFSG.LocalAnalysis.UniquenessCase.UCK.k32_holds ↥E hKE hEs hEnab h3E with
    ⟨p, f, hm⟩ | ⟨p, f, hq3, hm⟩ | ⟨p, f, hq3, hm⟩ | hJ
  ·
    obtain ⟨hp, hf1, -, hne2, hne3⟩ := hm.admissible
    by_cases hp2 : p = 2
    · subst hp2
      have hf2 : 2 ≤ f := by
        by_contra h
        exact hne2 (by rw [show f = 1 by omega]; rfl)
      rcases Nat.even_or_odd f with ⟨n, hn⟩ | hodd
      · left
        refine ⟨hben (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2214_bor_bender_L2 hm),
          fun _ => Or.inr (Or.inr (Or.inr ⟨n, by omega, Or.inl ?_⟩))⟩
        rw [show 2 * n = f by omega]
        exact hm
      · exact absurd ⟨f, hodd, by omega, Or.inl hm⟩ hEno
    by_cases hp3 : p = 3
    · subst hp3
      have := two_le_pRank_three_of_lieModel_psl_two_three hm
      omega
    have hp5' := hp5 p hp hp2 hp3
    have hs := hsect (CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model
      hp2 hm)
    by_cases h9 : 9 < p ^ f
    · exact Or.inl ⟨hs, fun _ => Or.inl ⟨p, f, hp, hp5', h9, hm.statedClassicalModel (by decide)⟩⟩
    · have hf : f = 1 := by
        by_contra hf
        have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
        nlinarith
      subst hf
      have hp57 : p = 5 ∨ p = 7 := by
        rw [pow_one] at h9
        interval_cases p <;> simp_all <;> norm_num at hp
      rcases hp57 with rfl | rfl
      · left
        refine ⟨hs, fun _ => Or.inr (Or.inr (Or.inr ⟨1, le_rfl, Or.inl ?_⟩))⟩
        obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm.statedClassicalModel (by decide)
        exact CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.lieModel_psl_two_five_two_two
          (by rw [hK]; norm_num) eK
      · exact Or.inl (calL1OverCF_and_shape_of_psl_two_seven hm hq hEC hT)
  ·
    obtain ⟨hp, hf1, -⟩ := hm.admissible
    by_cases hp2 : p = 2
    · subst hp2
      have hodd := odd_of_two_pow_mod_three_eq_two hq3
      by_cases hf : f = 1
      · subst hf
        exact Or.inl (calL1OverCF_and_shape_of_psl_two_seven
          (CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hm)
          hq hEC hT)
      · exact absurd ⟨f, hodd, by omega, Or.inr (Or.inr hm)⟩ hEno
    have hp3 : p ≠ 3 := by
      rintro rfl
      rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega)] at hq3
      simp at hq3
    rcases pow_mod_four_eq_one_or_three (f := f) hp hp2 with h1 | h3
    · exact Or.inr (hwr p f hp hp2 (Or.inl ⟨hm, h1⟩))
    · exact Or.inl ⟨hsect (sectionalTwoRankLE_two_of_lieModel_psl_three hp hp2 hm h3),
        fun _ => Or.inr (Or.inl ⟨p, f, hp, hp5 p hp hp2 hp3, Or.inl ⟨hq3, h3, hm⟩⟩)⟩
  ·
    obtain ⟨hp, hf1, -⟩ := hm.admissible
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨n, hn⟩ := even_of_two_pow_mod_three_eq_one hq3
      left
      refine ⟨hben (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2214_bor_bender_U3 hm),
        fun _ => Or.inr (Or.inr (Or.inr ⟨n, by omega, Or.inr ?_⟩))⟩
      rw [show 2 * n = f by omega]
      exact hm
    have hp3 : p ≠ 3 := by
      rintro rfl
      rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega)] at hq3
      simp at hq3
    rcases pow_mod_four_eq_one_or_three (f := f) hp hp2 with h1 | h3
    · exact Or.inl ⟨hsect (sectionalTwoRankLE_two_of_lieModel_psu_three hp hp2 hm h1),
        fun _ => Or.inr (Or.inl ⟨p, f, hp, hp5 p hp hp2 hp3, Or.inr ⟨hq3, h1, hm⟩⟩)⟩
    · exact Or.inr (hwr p f hp hp2 (Or.inr ⟨hm, h3⟩))
  ·
    right
    obtain ⟨eJ⟩ := hJ
    have hEtop : E = ⊤ :=
      CFSG.Quasithin.H13.S3320.eq_top_of_J1 hEC (eJ.trans CFSG.Walter.walterJ1EquivNative.symm)
    have hJ1 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsJ1 ↥(⊤ : Subgroup Y) :=
      ⟨(MulEquiv.subgroupCongr hEtop.symm).trans eJ⟩
    exact lGen_calL1_eq_of_isJ1 hJ1 le_top hT.isPGroup

end Cases

end CFSG.LocalAnalysis.WeakClosure81

end
