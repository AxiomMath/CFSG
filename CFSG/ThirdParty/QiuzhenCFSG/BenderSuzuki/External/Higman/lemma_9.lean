module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 9
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped IsMulCommutative commutatorElement

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Higman Lemma 9: a maximal normal abelian `X`-invariant subgroup has
exponent at most four and contains the Frattini subgroup. -/
public theorem lemma9_maximal_abelian_contains_frattini
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (_hA_normal : A.Normal)
    (_hA_abelian : IsMulCommutative A) (_hA_X : IsXInvariantSubgroup X A)
    (_hmax : ∀ B : Subgroup P, B.Normal → IsMulCommutative B →
      IsXInvariantSubgroup X B → A < B → False) :
    (∀ x : A, x ^ 4 = 1) ∧
      (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype ≤ A := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup _hP
  have hA_lt_top : A < (⊤ : Subgroup P) := by
    refine lt_top_iff_ne_top.mpr ?_
    intro hAtop
    apply _hP.2.1
    letI : IsMulCommutative A := _hA_abelian
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    let ax : A := ⟨x, by rw [hAtop]; trivial⟩
    let ay : A := ⟨y, by rw [hAtop]; trivial⟩
    exact congrArg Subtype.val (mul_comm ax ay)
  have hcover_exists :
      ∃ C : Subgroup P,
        C.Normal ∧ IsXInvariantSubgroup X C ∧ A < C ∧
          ∀ B : Subgroup P, B.Normal → IsXInvariantSubgroup X B →
            A < B → B < C → False := by
    letI : Fintype (Subgroup P) := Fintype.ofFinite _
    let S : Finset (Subgroup P) :=
      Finset.univ.filter fun C =>
        C.Normal ∧ IsXInvariantSubgroup X C ∧ A < C
    have htop_X : IsXInvariantSubgroup X (⊤ : Subgroup P) := by
      intro x p
      simp
    have htop_mem : (⊤ : Subgroup P) ∈ S := by
      change (⊤ : Subgroup P) ∈ Finset.univ.filter (fun C =>
        C.Normal ∧ IsXInvariantSubgroup X C ∧ A < C)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, inferInstance, htop_X, hA_lt_top⟩
    obtain ⟨C, hCmem, hCmin⟩ :=
      Finset.exists_minimal (s := S) ⟨⊤, htop_mem⟩
    have hCdata := (Finset.mem_filter.mp hCmem).2
    refine ⟨C, hCdata.1, hCdata.2.1, hCdata.2.2, ?_⟩
    intro B hB_normal hB_X hAB hBC
    have hBmem : B ∈ S := by
      change B ∈ Finset.univ.filter (fun C =>
        C.Normal ∧ IsXInvariantSubgroup X C ∧ A < C)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hB_normal, hB_X, hAB⟩
    exact (not_le_of_gt hBC) (hCmin hBmem hBC.le)
  obtain ⟨C, hC_normal, hC_X, hAC, hcover⟩ := hcover_exists
  have hA_exp4 : ∀ x : A, x ^ 4 = 1 := by
    letI : IsInvariant X P C := ⟨hC_X⟩
    let PhiA : Subgroup P := (frattini A).map A.subtype
    let PhiC : Subgroup P := (frattini C).map C.subtype
    let Asq : Subgroup P :=
      Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x}
    let Ccomm : Subgroup P := (commutator C).map C.subtype
    have hAsq_eq_PhiA : Asq = PhiA := by
      letI : Finite A := inferInstance
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fact (IsPGroup 2 A) :=
        ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup A⟩
      letI : IsMulCommutative A := _hA_abelian
      have hPhi : frattini A = (powMonoidHom 2 : A →* A).range := by
        have hcomm : commutator A = ⊥ := by
          rw [commutator_eq_bot_iff_center_eq_top]
          apply eq_top_iff.mpr
          intro x _hx
          exact Subgroup.mem_center_iff.mpr
            (fun y => ((IsMulCommutative.is_comm (M := A)).comm x y).symm)
        rw [frattini_eq_closure_commutator_union_powers (R := A) (p := 2)]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          intro x hx
          rcases hx with hxcomm | hxpow
          · have hxbot : x ∈ (⊥ : Subgroup A) := by
              simpa [hcomm] using hxcomm
            have hx1 : x = 1 := by simpa using hxbot
            subst x
            exact ⟨1, by simp⟩
          · simpa [powMonoidHom] using hxpow
        · intro x hx
          exact Subgroup.subset_closure
            (Or.inr (by simpa [powMonoidHom] using hx))
      change
        Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} =
          (frattini A).map A.subtype
      rw [hPhi]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x ⟨a, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨a ^ 2, MonoidHom.mem_range.mpr
            ⟨a, by simp [powMonoidHom]⟩, rfl⟩
      · rintro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
        exact Subgroup.subset_closure ⟨a, by simp [powMonoidHom]⟩
    have hPhiA_le_PhiC : PhiA ≤ PhiC := by
      letI : Finite C := inferInstance
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fact (IsPGroup 2 C) :=
        ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup C⟩
      rw [← hAsq_eq_PhiA]
      change
        Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} ≤
          (frattini C).map C.subtype
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      let aC : C := ⟨a, hAC.le a.property⟩
      refine ⟨aC ^ 2, pth_power_mem_frattini_of_isPGroup
        (R := C) (p := 2) aC, ?_⟩
      rfl
    have hPhiC_normal : PhiC.Normal := by
      constructor
      intro z hz p
      rcases hz with ⟨c, hc, rfl⟩
      let cp : C := MulAut.conjNormal (H := C) p c
      have hcp : cp ∈ frattini C :=
        (Subgroup.characteristic_iff_le_comap.mp
          (frattini_characteristic (G := C))
          (MulAut.conjNormal (H := C) p)) hc
      refine ⟨cp, hcp, ?_⟩
      simp [cp, MulAut.conjNormal_apply]
    have hPhiC_X : IsXInvariantSubgroup X PhiC := by
      have hforward : ∀ x : X, ∀ p : P, p ∈ PhiC → x • p ∈ PhiC := by
        intro x p hp
        rcases hp with ⟨c, hc, rfl⟩
        refine ⟨x • c, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (frattini_characteristic (G := C))
            (MulDistribMulAction.toMulAut X C x)) hc
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hPhiC_le_C : PhiC ≤ C := by
      rintro _ ⟨c, _hc, rfl⟩
      exact c.property
    have hPhiC_le_A : PhiC ≤ A := by
      by_contra hnot
      have hA_lt_sup : A < A ⊔ PhiC := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hnot
        exact le_sup_right.trans (le_of_eq heq.symm)
      have hsup_le_C : A ⊔ PhiC ≤ C :=
        sup_le hAC.le hPhiC_le_C
      have hsup_normal : (A ⊔ PhiC).Normal := by
        letI : A.Normal := _hA_normal
        letI : PhiC.Normal := hPhiC_normal
        infer_instance
      have hsup_X : IsXInvariantSubgroup X (A ⊔ PhiC) := by
        letI : IsInvariant X P A := ⟨_hA_X⟩
        letI : IsInvariant X P PhiC := ⟨hPhiC_X⟩
        exact (isInvariant_sup A PhiC).invariant
      have hsup_eq_C : A ⊔ PhiC = C := by
        by_contra hne
        exact False.elim
          (hcover (A ⊔ PhiC) hsup_normal hsup_X hA_lt_sup
            (lt_of_le_of_ne hsup_le_C hne))
      let AC : Subgroup C := A.subgroupOf C
      have hACmap : AC.map C.subtype = A :=
        Subgroup.map_subgroupOf_eq_of_le hAC.le
      have htopmap : (⊤ : Subgroup C).map C.subtype = C := by
        apply le_antisymm
        · rintro _ ⟨c, _hc, rfl⟩
          exact c.property
        · intro c hc
          exact ⟨⟨c, hc⟩, trivial, rfl⟩
      have hinside : AC ⊔ frattini C = ⊤ := by
        apply Subgroup.map_injective C.subtype_injective
        rw [Subgroup.map_sup, hACmap, htopmap]
        exact hsup_eq_C
      have hACtop : AC = ⊤ := frattini_nongenerating hinside
      have hAeqC : A = C := by
        rw [← hACmap, hACtop, htopmap]
      exact hAC.ne hAeqC
    have hpower_dichotomy :
        ∀ B : Subgroup P, B ≤ A → IsXInvariantSubgroup X B →
          B ≤ Asq ∨ B = A := by
      obtain ⟨e, r, hAcoord, hApowers⟩ :=
        lemma1_abelian_invariant_homocyclic
          _hP _hXtrans _hA_abelian _hA_X
      intro B hBA hB_X
      obtain ⟨s, hs, hB⟩ := hApowers B hBA hB_X
      by_cases hs0 : s = 0
      · right
        rw [hB, hs0]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨a, rfl⟩
          simp
        · intro x hx
          exact Subgroup.subset_closure
            ⟨⟨x, hx⟩, by simp⟩
      · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hs0
        subst s
        left
        rw [hB, show Asq =
          Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} by rfl,
          Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact Subgroup.subset_closure
          ⟨a ^ (2 ^ t), by simp [pow_succ, pow_mul]⟩
    have hPhiC_cases : PhiC = PhiA ∨ PhiC = A := by
      rcases hpower_dichotomy PhiC hPhiC_le_A hPhiC_X with hle | heq
      · left
        apply le_antisymm
        · simpa [hAsq_eq_PhiA] using hle
        · exact hPhiA_le_PhiC
      · exact Or.inr heq
    rcases hPhiC_cases with hPhi | hPhi
    · exact lemma3_covering_phi_case_exponent_le_four
        _hP _hXtrans _hA_normal _hA_abelian _hA_X
          hC_normal hC_X hAC hcover hPhi
    · have hCcomm_normal : Ccomm.Normal := by
        constructor
        intro z hz p
        rcases hz with ⟨c, hc, rfl⟩
        let cp : C := MulAut.conjNormal (H := C) p c
        have hcp : cp ∈ commutator C :=
          (Subgroup.characteristic_iff_le_comap.mp
            (show (commutator C).Characteristic from inferInstance)
            (MulAut.conjNormal (H := C) p)) hc
        refine ⟨cp, hcp, ?_⟩
        simp [cp, MulAut.conjNormal_apply]
      have hCcomm_X : IsXInvariantSubgroup X Ccomm := by
        have hforward : ∀ x : X, ∀ p : P, p ∈ Ccomm → x • p ∈ Ccomm := by
          intro x p hp
          rcases hp with ⟨c, hc, rfl⟩
          refine ⟨x • c, ?_, rfl⟩
          exact
            (Subgroup.characteristic_iff_le_comap.mp
              (show (commutator C).Characteristic from inferInstance)
              (MulDistribMulAction.toMulAut X C x)) hc
        intro x p
        constructor
        · exact hforward x p
        · intro hp
          have hpinv := hforward x⁻¹ (x • p) hp
          simpa [smul_smul] using hpinv
      have hCcomm_le_PhiC : Ccomm ≤ PhiC := by
        letI : Finite C := inferInstance
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : Fact (IsPGroup 2 C) :=
          ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup C⟩
        rintro _ ⟨c, hc, rfl⟩
        exact ⟨c, commutator_le_frattini_of_isPGroup
          (R := C) (p := 2) hc, rfl⟩
      have hCcomm_le_A : Ccomm ≤ A := by
        simpa [hPhi] using hCcomm_le_PhiC
      rcases hpower_dichotomy Ccomm hCcomm_le_A hCcomm_X with hle | heq
      · have hC_abelian : IsMulCommutative C :=
          lemma7_cover_commutator_case_abelian
            _hP _hXcyclic _hXfaithful _hXtrans
              _hA_normal _hA_abelian _hA_X hC_normal hC_X hAC hcover
                hPhi.symm hle
        exact False.elim (_hmax C hC_normal hC_abelian hC_X hAC)
      · have hA_two : ∀ x : A, x ^ 2 = 1 :=
          lemma8_cover_commutator_case_exponent_two
            _hP _hXcyclic _hXfaithful _hXtrans
              _hA_normal _hA_abelian _hA_X hC_normal hC_X hAC hcover heq
        intro x
        calc
          x ^ 4 = (x ^ 2) ^ 2 := by group
          _ = 1 := by rw [hA_two x]; simp
  have hPhi_le_A :
      (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype ≤ A := by
    letI : A.Normal := _hA_normal
    letI : IsInvariant X P A := ⟨_hA_X⟩
    let PhiP : Subgroup P :=
      (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype
    let Asq : Subgroup P :=
      Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x}
    let A4 : Subgroup P :=
      Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 4 = x}
    change PhiP ≤ A
    by_contra hPhi_not_le
    have hA_ne : A ≠ ⊥ := by
      letI : Nontrivial P := by
        rcases _hP.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
        exact ⟨⟨x, y, hxy⟩⟩
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcenter : (⊥ : Subgroup P) < Subgroup.center P :=
        IsPGroup.bot_lt_center (isPGroup_of_isSuzukiTwoGroup _hP)
      intro hAbot
      exact _hmax (Subgroup.center P) (by infer_instance) (by infer_instance)
        (isXInvariantSubgroup_center X P) (by simpa [hAbot] using hcenter)
    have hPhiP_normal : PhiP.Normal := by
      constructor
      intro z hz p
      rcases hz with ⟨c, hc, rfl⟩
      let cp : (⊤ : Subgroup P) :=
        MulAut.conjNormal (H := (⊤ : Subgroup P)) p c
      have hcp : cp ∈ frattini (⊤ : Subgroup P) :=
        (Subgroup.characteristic_iff_le_comap.mp
          (frattini_characteristic (G := (⊤ : Subgroup P)))
          (MulAut.conjNormal (H := (⊤ : Subgroup P)) p)) hc
      refine ⟨cp, hcp, ?_⟩
      simp [cp, MulAut.conjNormal_apply]
    have hPhiP_X : IsXInvariantSubgroup X PhiP := by
      letI : IsInvariant X P (⊤ : Subgroup P) :=
        ⟨by intro x p; simp⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ PhiP → x • p ∈ PhiP := by
        intro x p hp
        rcases hp with ⟨c, hc, rfl⟩
        refine ⟨x • c, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (frattini_characteristic (G := (⊤ : Subgroup P)))
            (MulDistribMulAction.toMulAut X (⊤ : Subgroup P) x)) hc
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_data :
        ∃ D B : Subgroup P,
          D.Normal ∧ IsXInvariantSubgroup X D ∧ A < D ∧
            (∀ E : Subgroup P, E.Normal → IsXInvariantSubgroup X E →
              A < E → E < D → False) ∧
          B.Normal ∧ IsXInvariantSubgroup X B ∧ B ≤ PhiP ∧
            D = A ⊔ B ∧ ¬ B ≤ A := by
      let U : Subgroup P := A ⊔ PhiP
      have hA_lt_U : A < U := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hPhi_not_le
        exact le_sup_right.trans (le_of_eq heq.symm)
      have hU_normal : U.Normal := by
        letI : PhiP.Normal := hPhiP_normal
        infer_instance
      have hU_X : IsXInvariantSubgroup X U := by
        letI : IsInvariant X P PhiP := ⟨hPhiP_X⟩
        exact (isInvariant_sup A PhiP).invariant
      letI : Fintype (Subgroup P) := Fintype.ofFinite _
      let S : Finset (Subgroup P) :=
        Finset.univ.filter fun D =>
          D.Normal ∧ IsXInvariantSubgroup X D ∧ A < D ∧ D ≤ U
      have hU_mem : U ∈ S := by
        change U ∈ Finset.univ.filter (fun D =>
          D.Normal ∧ IsXInvariantSubgroup X D ∧ A < D ∧ D ≤ U)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hU_normal, hU_X, hA_lt_U, le_rfl⟩
      obtain ⟨D, hDmem, hDmin⟩ :=
        Finset.exists_minimal (s := S) ⟨U, hU_mem⟩
      have hDdata := (Finset.mem_filter.mp hDmem).2
      let B : Subgroup P := D ⊓ PhiP
      have hB_normal : B.Normal := by
        letI : D.Normal := hDdata.1
        letI : PhiP.Normal := hPhiP_normal
        infer_instance
      have hB_X : IsXInvariantSubgroup X B := by
        letI : IsInvariant X P D := ⟨hDdata.2.1⟩
        letI : IsInvariant X P PhiP := ⟨hPhiP_X⟩
        exact (isInvariant_inf D PhiP).invariant
      have hD_eq : D = A ⊔ B := by
        apply le_antisymm
        · intro d hd
          have hdU : d ∈ A ⊔ PhiP := hDdata.2.2.2 hd
          rcases Subgroup.mem_sup_of_normal_left.mp hdU with
            ⟨a, ha, p, hp, hap⟩
          have haD : a ∈ D := hDdata.2.2.1.le ha
          have hp_eq : p = a⁻¹ * d := by
            calc
              p = a⁻¹ * (a * p) := by group
              _ = a⁻¹ * d := by rw [hap]
          have hpD : p ∈ D := by
            rw [hp_eq]
            exact D.mul_mem (D.inv_mem haD) hd
          rw [← hap]
          exact (A ⊔ B).mul_mem
            ((show A ≤ A ⊔ B from le_sup_left) ha)
            ((show B ≤ A ⊔ B from le_sup_right) ⟨hpD, hp⟩)
        · exact sup_le hDdata.2.2.1.le inf_le_left
      have hB_not_le : ¬ B ≤ A := by
        intro hBA
        have hDA : D ≤ A := by
          rw [hD_eq]
          exact sup_le le_rfl hBA
        exact (not_le_of_gt hDdata.2.2.1) hDA
      refine ⟨D, B, hDdata.1, hDdata.2.1, hDdata.2.2.1, ?_,
        hB_normal, hB_X, inf_le_right, hD_eq, hB_not_le⟩
      intro E hE_normal hE_X hAE hED
      have hEmem : E ∈ S := by
        change E ∈ Finset.univ.filter (fun K =>
          K.Normal ∧ IsXInvariantSubgroup X K ∧ A < K ∧ K ≤ U)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hE_normal, hE_X, hAE,
          hED.le.trans hDdata.2.2.2⟩
      exact (not_le_of_gt hED) (hDmin hEmem hED.le)
    obtain ⟨D, B, hD_normal, hD_X, hAD, hD_cover,
      hB_normal, hB_X, hB_le_Phi, hD_eq, hB_not_le⟩ := hD_data
    have hPAcomm_le_Asq : ⁅(⊤ : Subgroup P), A⁆ ≤ Asq := by
      let K : Subgroup P := ⁅(⊤ : Subgroup P), A⁆
      have hK_proper : K < A := by
        refine lt_of_le_of_ne (by
          simpa [K] using
            (Subgroup.commutator_le_right (⊤ : Subgroup P) A)) ?_
        intro hKA
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hnil : Group.IsNilpotent P :=
          IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup _hP)
        obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
        have hA_le : ∀ i : ℕ, A ≤ (⊤ : Subgroup P).lowerCentralSeries i := by
          intro i
          induction i with
          | zero => simp
          | succ i ih =>
              rw [Subgroup.lowerCentralSeries_succ]
              calc
                A = ⁅(⊤ : Subgroup P), A⁆ := by
                  simpa [K] using hKA.symm
                _ = ⁅A, (⊤ : Subgroup P)⁆ :=
                  Subgroup.commutator_comm _ _
                _ ≤ ⁅(⊤ : Subgroup P).lowerCentralSeries i,
                      (⊤ : Subgroup P)⁆ :=
                  Subgroup.commutator_mono ih le_rfl
        have hbot : A ≤ ⊥ := by
          rw [← hn]
          exact hA_le n
        exact hA_ne (bot_unique hbot)
      have hK_X : IsXInvariantSubgroup X K := by
        have hmap (x : X) :
            K.map (MulDistribMulAction.toMulAut X P x).toMonoidHom = K := by
          have hAmap :
              A.map (MulDistribMulAction.toMulAut X P x).toMonoidHom = A := by
            apply le_antisymm
            · rintro y ⟨z, hz, rfl⟩
              exact (_hA_X x z).mp hz
            · intro y hy
              refine ⟨x⁻¹ • y, (_hA_X x⁻¹ y).mp hy, ?_⟩
              simp [MulDistribMulAction.toMulAut_apply, smul_smul]
          have htopmap :
              (⊤ : Subgroup P).map
                  (MulDistribMulAction.toMulAut X P x).toMonoidHom = ⊤ :=
            Subgroup.map_top_of_surjective _
              (MulDistribMulAction.toMulAut X P x).surjective
          change ⁅(⊤ : Subgroup P), A⁆.map
              (MulDistribMulAction.toMulAut X P x).toMonoidHom =
            ⁅(⊤ : Subgroup P), A⁆
          rw [Subgroup.map_commutator, htopmap, hAmap]
        intro x a
        constructor
        · intro ha
          have hmem :
              (MulDistribMulAction.toMulAut X P x) a ∈
                K.map (MulDistribMulAction.toMulAut X P x).toMonoidHom :=
            ⟨a, ha, rfl⟩
          rw [hmap x] at hmem
          simpa [MulDistribMulAction.toMulAut_apply] using hmem
        · intro ha
          have hmem :
              (MulDistribMulAction.toMulAut X P x⁻¹) (x • a) ∈
                K.map (MulDistribMulAction.toMulAut X P x⁻¹).toMonoidHom :=
            ⟨x • a, ha, rfl⟩
          rw [hmap x⁻¹] at hmem
          simpa [MulDistribMulAction.toMulAut_apply, smul_smul] using hmem
      obtain ⟨e, r, hAcoord, hApowers⟩ :=
        lemma1_abelian_invariant_homocyclic
          _hP _hXtrans _hA_abelian _hA_X
      obtain ⟨s, hs, hK⟩ := hApowers K hK_proper.le hK_X
      by_cases hs0 : s = 0
      · have hK_eq_A : K = A := by
          rw [hK, hs0]
          apply le_antisymm
          · rw [Subgroup.closure_le]
            rintro _ ⟨a, rfl⟩
            simp
          · intro x hx
            exact Subgroup.subset_closure ⟨⟨x, hx⟩, by simp⟩
        exact False.elim (hK_proper.ne hK_eq_A)
      · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hs0
        subst s
        change K ≤ Asq
        rw [hK, show Asq =
          Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} by rfl,
          Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact Subgroup.subset_closure
          ⟨a ^ (2 ^ t), by simp [pow_succ, pow_mul]⟩
    have hPhi_comm_le_A4 :
        ∀ b : P, b ∈ PhiP →
          Subgroup.closure {x : P | ∃ a : A, ⁅b, (a : P)⁆ = x} ≤ A4 := by
      have hA4_normal : A4.Normal := by
        constructor
        intro x hx p
        refine Subgroup.closure_induction (fun y hy => ?_) ?_
          (fun y z _ _ hy' hz' => ?_) (fun y _ hy' => ?_) hx
        · exact Subgroup.subset_closure <| by
            rcases hy with ⟨a, rfl⟩
            refine ⟨⟨p * (a : P) * p⁻¹,
              _hA_normal.conj_mem (a : P) a.property p⟩, ?_⟩
            exact conj_pow
        · simp
        · rw [← conj_mul]
          exact A4.mul_mem hy' hz'
        · rw [← conj_inv]
          exact A4.inv_mem hy'
      letI : A4.Normal := hA4_normal
      have hPhiP_le_squares : PhiP ≤ squaresSubgroup P := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : Fact (IsPGroup 2 (⊤ : Subgroup P)) :=
          ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup ⊤⟩
        have hcomm_le_squares :
            commutator (⊤ : Subgroup P) ≤
              (squaresSubgroup P).comap (⊤ : Subgroup P).subtype := by
          rw [_root_.commutator_def, Subgroup.commutator_le]
          intro x _hx y _hy
          change ⁅(x : P), (y : P)⁆ ∈ squaresSubgroup P
          have hx2 : (x : P) ^ 2 ∈ squaresSubgroup P :=
            Subgroup.subset_closure ⟨(x : P), rfl⟩
          have hxy2 : ((x : P)⁻¹ * (y : P)) ^ 2 ∈ squaresSubgroup P :=
            Subgroup.subset_closure ⟨(x : P)⁻¹ * (y : P), rfl⟩
          have hy2inv : ((y : P) ^ 2)⁻¹ ∈ squaresSubgroup P :=
            (squaresSubgroup P).inv_mem
              (Subgroup.subset_closure ⟨(y : P), rfl⟩)
          rw [show ⁅(x : P), (y : P)⁆ =
              (x : P) ^ 2 * ((x : P)⁻¹ * (y : P)) ^ 2 *
                ((y : P) ^ 2)⁻¹ by
            simp only [commutatorElement_def, pow_two]
            group]
          exact (squaresSubgroup P).mul_mem
            ((squaresSubgroup P).mul_mem hx2 hxy2) hy2inv
        have hPhi_top_le :
            frattini (⊤ : Subgroup P) ≤
              (squaresSubgroup P).comap (⊤ : Subgroup P).subtype := by
          rw [frattini_eq_closure_commutator_union_powers
            (R := (⊤ : Subgroup P)) (p := 2), Subgroup.closure_le]
          intro z hz
          rcases hz with hz | ⟨x, rfl⟩
          · exact hcomm_le_squares hz
          · exact Subgroup.subset_closure ⟨(x : P), by simp⟩
        rintro _ ⟨z, hz, rfl⟩
        exact hPhi_top_le hz
      have hsquare_comm_mem_A4 :
          ∀ g : P, ∀ a : A, ⁅g ^ 2, (a : P)⁆ ∈ A4 := by
        letI : IsMulCommutative A := _hA_abelian
        have hAsq_eq_range :
            Asq = (powMonoidHom 2 : A →* A).range.map A.subtype := by
          change Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} =
            (powMonoidHom 2 : A →* A).range.map A.subtype
          apply le_antisymm
          · rw [Subgroup.closure_le]
            rintro _ ⟨a, rfl⟩
            exact Subgroup.mem_map.mpr
              ⟨a ^ 2, MonoidHom.mem_range.mpr
                ⟨a, by simp [powMonoidHom]⟩, rfl⟩
          · rintro _ hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
            exact Subgroup.subset_closure ⟨a, by simp [powMonoidHom]⟩
        have hAsq_root :
            ∀ x : P, x ∈ Asq → ∃ a : A, (a : P) ^ 2 = x := by
          intro x hx
          rw [hAsq_eq_range] at hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
          exact ⟨a, by simp [powMonoidHom]⟩
        intro g a
        have hga_mem : ⁅g, (a : P)⁆ ∈ Asq :=
          hPAcomm_le_Asq (Subgroup.subset_closure
            ⟨g, trivial, (a : P), a.property, rfl⟩)
        obtain ⟨d, hd⟩ := hAsq_root _ hga_mem
        have hgd_mem : ⁅g, (d : P)⁆ ∈ Asq :=
          hPAcomm_le_Asq (Subgroup.subset_closure
            ⟨g, trivial, (d : P), d.property, rfl⟩)
        obtain ⟨e, he⟩ := hAsq_root _ hgd_mem
        have hconj_mem : g * (d : P) * g⁻¹ ∈ A :=
          _hA_normal.conj_mem (d : P) d.property g
        let gdg : A := ⟨g * (d : P) * g⁻¹, hconj_mem⟩
        have hcommute : Commute (g * (d : P) * g⁻¹) (d : P) := by
          change (g * (d : P) * g⁻¹) * (d : P) =
            (d : P) * (g * (d : P) * g⁻¹)
          exact congrArg A.subtype
            ((IsMulCommutative.is_comm (M := A)).comm gdg d)
        have hcomm_pow : ⁅g, (d : P) ^ 2⁆ = ⁅g, (d : P)⁆ ^ 2 := by
          calc
            ⁅g, (d : P) ^ 2⁆ =
                (g * (d : P) * g⁻¹) ^ 2 * ((d : P)⁻¹) ^ 2 := by
              simp only [commutatorElement_def, pow_two]
              group
            _ = ((g * (d : P) * g⁻¹) * (d : P)⁻¹) ^ 2 :=
              (hcommute.inv_right.mul_pow 2).symm
            _ = ⁅g, (d : P)⁆ ^ 2 := by
              rfl
        have hdouble :
            ⁅g ^ 2, (a : P)⁆ =
              ⁅g, ⁅g, (a : P)⁆⁆ * ⁅g, (a : P)⁆ ^ 2 := by
          simp only [commutatorElement_def, pow_two]
          group
        refine Subgroup.subset_closure ⟨e * d, ?_⟩
        rw [hdouble, ← hd, hcomm_pow, ← he]
        calc
          ((e * d : A) : P) ^ 4 = (e : P) ^ 4 * (d : P) ^ 4 := by
            have hed : Commute e d :=
              (IsMulCommutative.is_comm (M := A)).comm e d
            exact congrArg A.subtype (hed.mul_pow 4)
          _ = ((e : P) ^ 2) ^ 2 * ((d : P) ^ 2) ^ 2 := by
            group
      let q : P →* P ⧸ A4 := QuotientGroup.mk' A4
      let Abar : Subgroup (P ⧸ A4) := A.map q
      let Good : Subgroup P :=
        (Subgroup.centralizer (Abar : Set (P ⧸ A4))).comap q
      have hGood_iff :
          ∀ b : P, b ∈ Good ↔ ∀ a : A, ⁅b, (a : P)⁆ ∈ A4 := by
        intro b
        change q b ∈ Subgroup.centralizer (Abar : Set (P ⧸ A4)) ↔
          ∀ a : A, ⁅b, (a : P)⁆ ∈ A4
        constructor
        · intro hb a
          have hcomm : q b * q (a : P) = q (a : P) * q b :=
            ((Subgroup.mem_centralizer_iff.mp hb) (q (a : P))
              ⟨a, a.property, rfl⟩).symm
          apply (QuotientGroup.eq_one_iff ⁅b, (a : P)⁆).mp
          change q ⁅b, (a : P)⁆ = 1
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
        · intro hb
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rcases hy with ⟨a, ha, rfl⟩
          have hqcomm : q ⁅b, a⁆ = 1 := by
            apply (QuotientGroup.eq_one_iff ⁅b, a⁆).mpr
            exact hb ⟨a, ha⟩
          rw [map_commutatorElement] at hqcomm
          exact (commutatorElement_eq_one_iff_mul_comm.mp hqcomm).symm
      have hsquares_le_Good : squaresSubgroup P ≤ Good := by
        rw [squaresSubgroup, Subgroup.closure_le]
        rintro _ ⟨g, rfl⟩
        exact (hGood_iff (g ^ 2)).mpr (hsquare_comm_mem_A4 g)
      intro b hb
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact (hGood_iff b).mp
        (hsquares_le_Good (hPhiP_le_squares hb)) a
    have hPhiD_eq_A : (frattini D).map D.subtype = A := by
      letI : IsInvariant X P D := ⟨hD_X⟩
      let PhiD : Subgroup P := (frattini D).map D.subtype
      change PhiD = A
      have hPhiD_normal : PhiD.Normal := by
        constructor
        intro z hz p
        rcases hz with ⟨d, hd, rfl⟩
        let dp : D := MulAut.conjNormal (H := D) p d
        have hdp : dp ∈ frattini D :=
          (Subgroup.characteristic_iff_le_comap.mp
            (frattini_characteristic (G := D))
            (MulAut.conjNormal (H := D) p)) hd
        refine ⟨dp, hdp, ?_⟩
        simp [dp, MulAut.conjNormal_apply]
      have hPhiD_X : IsXInvariantSubgroup X PhiD := by
        have hforward : ∀ x : X, ∀ p : P, p ∈ PhiD → x • p ∈ PhiD := by
          intro x p hp
          rcases hp with ⟨d, hd, rfl⟩
          refine ⟨x • d, ?_, rfl⟩
          exact
            (Subgroup.characteristic_iff_le_comap.mp
              (frattini_characteristic (G := D))
              (MulDistribMulAction.toMulAut X D x)) hd
        intro x p
        constructor
        · exact hforward x p
        · intro hp
          have hpinv := hforward x⁻¹ (x • p) hp
          simpa [smul_smul] using hpinv
      have hPhiD_le_D : PhiD ≤ D := by
        rintro _ ⟨d, _hd, rfl⟩
        exact d.property
      have hPhiD_le_A : PhiD ≤ A := by
        by_contra hnot
        have hA_lt_sup : A < A ⊔ PhiD := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro heq
          apply hnot
          exact le_sup_right.trans (le_of_eq heq.symm)
        have hsup_le_D : A ⊔ PhiD ≤ D :=
          sup_le hAD.le hPhiD_le_D
        have hsup_normal : (A ⊔ PhiD).Normal := by
          letI : A.Normal := _hA_normal
          letI : PhiD.Normal := hPhiD_normal
          infer_instance
        have hsup_X : IsXInvariantSubgroup X (A ⊔ PhiD) := by
          letI : IsInvariant X P A := ⟨_hA_X⟩
          letI : IsInvariant X P PhiD := ⟨hPhiD_X⟩
          exact (isInvariant_sup A PhiD).invariant
        have hsup_eq_D : A ⊔ PhiD = D := by
          by_contra hne
          exact False.elim
            (hD_cover (A ⊔ PhiD) hsup_normal hsup_X hA_lt_sup
              (lt_of_le_of_ne hsup_le_D hne))
        let AD : Subgroup D := A.subgroupOf D
        have hADmap : AD.map D.subtype = A :=
          Subgroup.map_subgroupOf_eq_of_le hAD.le
        have htopmap : (⊤ : Subgroup D).map D.subtype = D := by
          apply le_antisymm
          · rintro _ ⟨d, _hd, rfl⟩
            exact d.property
          · intro d hd
            exact ⟨⟨d, hd⟩, trivial, rfl⟩
        have hinside : AD ⊔ frattini D = ⊤ := by
          apply Subgroup.map_injective D.subtype_injective
          rw [Subgroup.map_sup, hADmap, htopmap]
          exact hsup_eq_D
        have hADtop : AD = ⊤ := frattini_nongenerating hinside
        have hAeqD : A = D := by
          rw [← hADmap, hADtop, htopmap]
        exact hAD.ne hAeqD
      have hPhiD_not_le_Asq : ¬ PhiD ≤ Asq := by
        obtain ⟨b, hbB, hbA⟩ := SetLike.not_le_iff_exists.mp hB_not_le
        have hbD : b ∈ D := by
          rw [hD_eq]
          exact (le_sup_right : B ≤ A ⊔ B) hbB
        let bD : D := ⟨b, hbD⟩
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : Fact (IsPGroup 2 D) :=
          ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup D⟩
        have hb_sq_PhiD : b ^ 2 ∈ PhiD := by
          refine ⟨bD ^ 2,
            pth_power_mem_frattini_of_isPGroup (R := D) (p := 2) bD, ?_⟩
          rfl
        intro hPhiD_Asq
        exact lemma2_no_external_square_commutator_exception
          _hP _hXtrans _hA_normal _hA_abelian _hA_X hA_ne b hbA
            ⟨hPhiD_Asq hb_sq_PhiD, hPhi_comm_le_A4 b (hB_le_Phi hbB)⟩
      obtain ⟨e, r, hAcoord, hApowers⟩ :=
        lemma1_abelian_invariant_homocyclic
          _hP _hXtrans _hA_abelian _hA_X
      obtain ⟨s, hs, hPhiD_power⟩ :=
        hApowers PhiD hPhiD_le_A hPhiD_X
      by_cases hs0 : s = 0
      · rw [hPhiD_power, hs0]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨a, rfl⟩
          simp
        · intro x hx
          exact Subgroup.subset_closure ⟨⟨x, hx⟩, by simp⟩
      · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hs0
        subst s
        exfalso
        apply hPhiD_not_le_Asq
        rw [hPhiD_power, show Asq =
          Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} by rfl,
          Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact Subgroup.subset_closure
          ⟨a ^ (2 ^ t), by simp [pow_succ, pow_mul]⟩
    let Dcomm : Subgroup P := (commutator D).map D.subtype
    have hDcomm_cases : Dcomm ≤ Asq ∨ Dcomm = A := by
      letI : IsInvariant X P D := ⟨hD_X⟩
      have hDcomm_X : IsXInvariantSubgroup X Dcomm := by
        have hforward : ∀ x : X, ∀ p : P, p ∈ Dcomm → x • p ∈ Dcomm := by
          intro x p hp
          rcases hp with ⟨d, hd, rfl⟩
          refine ⟨x • d, ?_, rfl⟩
          exact
            (Subgroup.characteristic_iff_le_comap.mp
              (show (commutator D).Characteristic from inferInstance)
              (MulDistribMulAction.toMulAut X D x)) hd
        intro x p
        constructor
        · exact hforward x p
        · intro hp
          have hpinv := hforward x⁻¹ (x • p) hp
          simpa [smul_smul] using hpinv
      have hDcomm_le_A : Dcomm ≤ A := by
        letI : Finite D := inferInstance
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : Fact (IsPGroup 2 D) :=
          ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup D⟩
        rw [← hPhiD_eq_A]
        rintro _ ⟨d, hd, rfl⟩
        exact ⟨d, commutator_le_frattini_of_isPGroup
          (R := D) (p := 2) hd, rfl⟩
      obtain ⟨e, r, hAcoord, hApowers⟩ :=
        lemma1_abelian_invariant_homocyclic
          _hP _hXtrans _hA_abelian _hA_X
      obtain ⟨s, hs, hDcomm_power⟩ :=
        hApowers Dcomm hDcomm_le_A hDcomm_X
      by_cases hs0 : s = 0
      · right
        rw [hDcomm_power, hs0]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨a, rfl⟩
          simp
        · intro x hx
          exact Subgroup.subset_closure ⟨⟨x, hx⟩, by simp⟩
      · left
        obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hs0
        subst s
        rw [hDcomm_power, show Asq =
          Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} by rfl,
          Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        exact Subgroup.subset_closure
          ⟨a ^ (2 ^ t), by simp [pow_succ, pow_mul]⟩
    have hA_two : ∀ a : A, a ^ 2 = 1 := by
      rcases hDcomm_cases with hcomm_le | hcomm_eq
      · have hD_abelian : IsMulCommutative D :=
          lemma7_cover_commutator_case_abelian
            _hP _hXcyclic _hXfaithful _hXtrans
              _hA_normal _hA_abelian _hA_X hD_normal hD_X hAD hD_cover
                hPhiD_eq_A.symm hcomm_le
        exact False.elim (_hmax D hD_normal hD_abelian hD_X hAD)
      · exact lemma8_cover_commutator_case_exponent_two
          _hP _hXcyclic _hXfaithful _hXtrans
            _hA_normal _hA_abelian _hA_X hD_normal hD_X hAD hD_cover hcomm_eq
    have hA_eq_center : A = Subgroup.center P := by
      have hAsq_bot : Asq = ⊥ := by
        apply bot_unique
        change Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} ≤ ⊥
        rw [Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        have ha2 := congrArg A.subtype (hA_two a)
        simpa using ha2
      have hA_le_center : A ≤ Subgroup.center P := by
        intro a ha
        rw [Subgroup.mem_center_iff]
        intro g
        have hcomm_mem : ⁅g, a⁆ ∈ Asq :=
          hPAcomm_le_Asq (Subgroup.subset_closure
            ⟨g, trivial, a, ha, rfl⟩)
        rw [hAsq_bot] at hcomm_mem
        have hcomm_one : ⁅g, a⁆ = 1 := by
          simpa using hcomm_mem
        exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_one
      apply le_antisymm hA_le_center
      by_contra hnot
      have hlt : A < Subgroup.center P :=
        lt_of_le_of_ne hA_le_center (fun heq => hnot (le_of_eq heq.symm))
      exact _hmax (Subgroup.center P) (by infer_instance) (by infer_instance)
        (isXInvariantSubgroup_center X P) hlt
    have hclass_two : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ := by
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : Group.IsNilpotent P :=
        IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup _hP)
      have hnontrivial_abelian_unique
          (K : Subgroup P) (hK_ne : K ≠ ⊥) (hK_normal : K.Normal)
          (hK_abelian : IsMulCommutative K)
          (hK_X : IsXInvariantSubgroup X K) : K = A := by
        have hA_le_K : A ≤ K := by
          intro a ha
          by_cases ha_one : a = 1
          · simp [ha_one]
          · apply lemma1_involutions_mem_of_nontrivial_invariant
              _hP _hXtrans hK_X hK_ne a
            refine ⟨ha_one, ?_⟩
            let aa : A := ⟨a, ha⟩
            have haa := congrArg A.subtype (hA_two aa)
            simpa [aa] using haa
        rcases lt_or_eq_of_le hA_le_K with hlt | heq
        · exact False.elim (_hmax K hK_normal hK_abelian hK_X hlt)
        · exact heq.symm
      have hlower_weight :
          ∀ i j : ℕ,
            ⁅(⊤ : Subgroup P).lowerCentralSeries i,
              (⊤ : Subgroup P).lowerCentralSeries j⁆ ≤
                (⊤ : Subgroup P).lowerCentralSeries (i + j + 1) := by
        intro i
        induction i with
        | zero =>
            intro j
            calc
              ⁅(⊤ : Subgroup P).lowerCentralSeries 0,
                  (⊤ : Subgroup P).lowerCentralSeries j⁆ =
                    ⁅(⊤ : Subgroup P),
                      (⊤ : Subgroup P).lowerCentralSeries j⁆ := by
                rw [Subgroup.lowerCentralSeries_zero]
              _ = ⁅(⊤ : Subgroup P).lowerCentralSeries j,
                    (⊤ : Subgroup P)⁆ :=
                Subgroup.commutator_comm _ _
              _ = (⊤ : Subgroup P).lowerCentralSeries (j + 1) :=
                (Subgroup.lowerCentralSeries_succ (⊤ : Subgroup P) j).symm
              _ ≤ (⊤ : Subgroup P).lowerCentralSeries (0 + j + 1) := by
                simp
        | succ i ih =>
            intro j
            let N := (⊤ : Subgroup P).lowerCentralSeries (i.succ + j + 1)
            let q : P →* P ⧸ N := QuotientGroup.mk' N
            have htop_map : (⊤ : Subgroup P).map q = ⊤ :=
              Subgroup.map_top_of_surjective q
                (QuotientGroup.mk'_surjective N)
            change ⁅(⊤ : Subgroup P).lowerCentralSeries i.succ,
              (⊤ : Subgroup P).lowerCentralSeries j⁆ ≤ N
            rw [← QuotientGroup.ker_mk' N]
            apply
              (Subgroup.map_eq_bot_iff
                (⁅(⊤ : Subgroup P).lowerCentralSeries i.succ,
                  (⊤ : Subgroup P).lowerCentralSeries j⁆)).mp
            rw [Subgroup.map_commutator]
            have hsucc_map :
                ((⊤ : Subgroup P).lowerCentralSeries i.succ).map q =
                  ⁅((⊤ : Subgroup P).lowerCentralSeries i).map q, ⊤⁆ := by
              change (⁅(⊤ : Subgroup P).lowerCentralSeries i,
                (⊤ : Subgroup P)⁆).map q =
                  ⁅((⊤ : Subgroup P).lowerCentralSeries i).map q, ⊤⁆
              rw [Subgroup.map_commutator, htop_map]
            rw [hsucc_map]
            apply Subgroup.commutator_commutator_eq_bot_of_rotate
            · calc
                ⁅⁅(⊤ : Subgroup (P ⧸ N)),
                    ((⊤ : Subgroup P).lowerCentralSeries j).map q⁆,
                    ((⊤ : Subgroup P).lowerCentralSeries i).map q⁆ =
                    (⁅⁅(⊤ : Subgroup P),
                        (⊤ : Subgroup P).lowerCentralSeries j⁆,
                      (⊤ : Subgroup P).lowerCentralSeries i⁆).map q := by
                  rw [Subgroup.map_commutator,
                    Subgroup.map_commutator, htop_map]
                _ = ⊥ := by
                  apply
                    (Subgroup.map_eq_bot_iff
                      (⁅⁅(⊤ : Subgroup P),
                          (⊤ : Subgroup P).lowerCentralSeries j⁆,
                        (⊤ : Subgroup P).lowerCentralSeries i⁆)).mpr
                  rw [QuotientGroup.ker_mk']
                  calc
                    ⁅⁅(⊤ : Subgroup P),
                        (⊤ : Subgroup P).lowerCentralSeries j⁆,
                        (⊤ : Subgroup P).lowerCentralSeries i⁆ =
                        ⁅(⊤ : Subgroup P).lowerCentralSeries i,
                          (⊤ : Subgroup P).lowerCentralSeries (j + 1)⁆ := by
                      calc
                        ⁅⁅(⊤ : Subgroup P),
                            (⊤ : Subgroup P).lowerCentralSeries j⁆,
                            (⊤ : Subgroup P).lowerCentralSeries i⁆ =
                            ⁅⁅(⊤ : Subgroup P).lowerCentralSeries j,
                              (⊤ : Subgroup P)⁆,
                              (⊤ : Subgroup P).lowerCentralSeries i⁆ := by
                          rw [Subgroup.commutator_comm
                            (⊤ : Subgroup P)
                            ((⊤ : Subgroup P).lowerCentralSeries j)]
                        _ = ⁅(⊤ : Subgroup P).lowerCentralSeries (j + 1),
                              (⊤ : Subgroup P).lowerCentralSeries i⁆ := by
                          rfl
                        _ = ⁅(⊤ : Subgroup P).lowerCentralSeries i,
                              (⊤ : Subgroup P).lowerCentralSeries (j + 1)⁆ :=
                          Subgroup.commutator_comm _ _
                    _ ≤ N := by
                      change
                        ⁅(⊤ : Subgroup P).lowerCentralSeries i,
                          (⊤ : Subgroup P).lowerCentralSeries (j + 1)⁆ ≤
                            (⊤ : Subgroup P).lowerCentralSeries
                              (i.succ + j + 1)
                      rw [show i.succ + j + 1 =
                        i + (j + 1) + 1 by omega]
                      exact ih (j + 1)
            · calc
                ⁅⁅((⊤ : Subgroup P).lowerCentralSeries j).map q,
                    ((⊤ : Subgroup P).lowerCentralSeries i).map q⁆,
                    (⊤ : Subgroup (P ⧸ N))⁆ =
                    (⁅⁅(⊤ : Subgroup P).lowerCentralSeries j,
                        (⊤ : Subgroup P).lowerCentralSeries i⁆,
                      (⊤ : Subgroup P)⁆).map q := by
                  rw [Subgroup.map_commutator,
                    Subgroup.map_commutator, htop_map]
                _ = ⊥ := by
                  apply
                    (Subgroup.map_eq_bot_iff
                      (⁅⁅(⊤ : Subgroup P).lowerCentralSeries j,
                          (⊤ : Subgroup P).lowerCentralSeries i⁆,
                        (⊤ : Subgroup P)⁆)).mpr
                  rw [QuotientGroup.ker_mk']
                  calc
                    ⁅⁅(⊤ : Subgroup P).lowerCentralSeries j,
                        (⊤ : Subgroup P).lowerCentralSeries i⁆,
                        (⊤ : Subgroup P)⁆ ≤
                        ⁅(⊤ : Subgroup P).lowerCentralSeries (i + j + 1),
                          (⊤ : Subgroup P)⁆ := by
                      apply Subgroup.commutator_mono ?_ le_rfl
                      rw [Subgroup.commutator_comm
                        ((⊤ : Subgroup P).lowerCentralSeries j)
                        ((⊤ : Subgroup P).lowerCentralSeries i)]
                      exact ih j
                    _ = (⊤ : Subgroup P).lowerCentralSeries
                        ((i + j + 1) + 1) :=
                      (Subgroup.lowerCentralSeries_succ
                        (⊤ : Subgroup P) (i + j + 1)).symm
                    _ = N := by
                      change
                        (⊤ : Subgroup P).lowerCentralSeries
                            ((i + j + 1) + 1) =
                          (⊤ : Subgroup P).lowerCentralSeries
                            (i.succ + j + 1)
                      congr 1
                      omega
      have hlower_X (n : ℕ) :
          IsXInvariantSubgroup X ((⊤ : Subgroup P).lowerCentralSeries n) := by
        have hforward :
            ∀ x : X, ∀ p : P, p ∈ (⊤ : Subgroup P).lowerCentralSeries n →
              x • p ∈ (⊤ : Subgroup P).lowerCentralSeries n := by
          intro x p hp
          exact
            (Subgroup.characteristic_iff_le_comap.mp inferInstance
              (MulDistribMulAction.toMulAut X P x)) hp
        intro x p
        constructor
        · exact hforward x p
        · intro hp
          have hpinv := hforward x⁻¹ (x • p) hp
          simpa [smul_smul] using hpinv
      have hab_of_self_commutator_bot (K : Subgroup P)
          (hK_comm : ⁅K, K⁆ = ⊥) : IsMulCommutative K := by
        refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
        apply Subtype.ext
        have hmem : ⁅(x : P), (y : P)⁆ ∈ ⁅K, K⁆ :=
          Subgroup.commutator_mem_commutator x.property y.property
        rw [hK_comm] at hmem
        have hcomm_one : ⁅(x : P), (y : P)⁆ = 1 := by
          simpa using hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_one
      apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr
      let c := Group.nilpotencyClass P
      by_contra hc_not
      have hc_gt : 2 < c := by
        omega
      let K := (⊤ : Subgroup P).lowerCentralSeries (c - 2)
      let L := (⊤ : Subgroup P).lowerCentralSeries (c - 1)
      have hc_bot : (⊤ : Subgroup P).lowerCentralSeries c = ⊥ := by
        dsimp [c]
        exact Subgroup.lowerCentralSeries_nilpotencyClass
      have hK_ne : K ≠ ⊥ := by
        intro hK_bot
        have hc_le : c ≤ c - 2 :=
          Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
            (by simpa [K] using hK_bot)
        omega
      have hL_ne : L ≠ ⊥ := by
        intro hL_bot
        have hc_le : c ≤ c - 1 :=
          Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
            (by simpa [L] using hL_bot)
        omega
      have hK_comm_bot : ⁅K, K⁆ = ⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          ⁅K, K⁆ ≤
              (⊤ : Subgroup P).lowerCentralSeries
                ((c - 2) + (c - 2) + 1) := by
            simpa [K] using hlower_weight (c - 2) (c - 2)
          _ ≤ (⊤ : Subgroup P).lowerCentralSeries c :=
            (⊤ : Subgroup P).lowerCentralSeries_antitone (by omega)
          _ = ⊥ := hc_bot
      have hL_comm_bot : ⁅L, L⁆ = ⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          ⁅L, L⁆ ≤
              (⊤ : Subgroup P).lowerCentralSeries
                ((c - 1) + (c - 1) + 1) := by
            simpa [L] using hlower_weight (c - 1) (c - 1)
          _ ≤ (⊤ : Subgroup P).lowerCentralSeries c :=
            (⊤ : Subgroup P).lowerCentralSeries_antitone (by omega)
          _ = ⊥ := hc_bot
      have hK_ne_L : K ≠ L := by
        intro hKL
        apply hL_ne
        dsimp [K, L] at hKL ⊢
        calc
          (⊤ : Subgroup P).lowerCentralSeries (c - 1) =
              (⊤ : Subgroup P).lowerCentralSeries ((c - 2) + 1) := by
            congr 1
            omega
          _ = ⁅(⊤ : Subgroup P).lowerCentralSeries (c - 2),
                (⊤ : Subgroup P)⁆ :=
            Subgroup.lowerCentralSeries_succ (⊤ : Subgroup P) (c - 2)
          _ = ⁅(⊤ : Subgroup P).lowerCentralSeries (c - 1),
                (⊤ : Subgroup P)⁆ := by
            rw [hKL]
          _ = (⊤ : Subgroup P).lowerCentralSeries ((c - 1) + 1) :=
            (Subgroup.lowerCentralSeries_succ
              (⊤ : Subgroup P) (c - 1)).symm
          _ = (⊤ : Subgroup P).lowerCentralSeries c := by
            congr 1
            omega
          _ = ⊥ := hc_bot
      have hK_eq_A : K = A :=
        hnontrivial_abelian_unique K hK_ne (by infer_instance)
          (hab_of_self_commutator_bot K hK_comm_bot) (hlower_X (c - 2))
      have hL_eq_A : L = A :=
        hnontrivial_abelian_unique L hL_ne (by infer_instance)
          (hab_of_self_commutator_bot L hL_comm_bot) (hlower_X (c - 1))
      exact hK_ne_L (hK_eq_A.trans hL_eq_A.symm)
    have hquot_two : ∀ q : P ⧸ A, q ^ 2 = 1 := by
      have hcomm_le_center : commutator P ≤ Subgroup.center P := by
        have hclass := hclass_two
        rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
          Subgroup.top_lowerCentralSeries_one] at hclass
        change ⁅commutator P, (⊤ : Subgroup P)⁆ = ⊥ at hclass
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hclass
        simpa [← Subgroup.centralizer_univ, ← Subgroup.coe_top] using hclass
      have hsquare_mem_A : ∀ g : P, g ^ 2 ∈ A := by
        intro g
        rw [hA_eq_center, Subgroup.mem_center_iff]
        intro h
        have hcomm_mem : ⁅g, h⁆ ∈ commutator P := by
          change ⁅g, h⁆ ∈ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆
          exact Subgroup.commutator_mem_commutator
            (Subgroup.mem_top g) (Subgroup.mem_top h)
        have hcomm_center : ⁅g, h⁆ ∈ Subgroup.center P :=
          hcomm_le_center hcomm_mem
        have hcomm_mem_A : ⁅g, h⁆ ∈ A := by
          rw [hA_eq_center]
          exact hcomm_center
        have hcomm_sq : ⁅g, h⁆ ^ 2 = 1 := by
          let c : A := ⟨⁅g, h⁆, hcomm_mem_A⟩
          have hc := congrArg A.subtype (hA_two c)
          simpa [c] using hc
        have hnested : ⁅g, ⁅g, h⁆⁆ = 1 := by
          apply commutatorElement_eq_one_iff_mul_comm.mpr
          exact Subgroup.mem_center_iff.mp hcomm_center g
        have hsq_comm :
            ⁅g ^ 2, h⁆ = ⁅g, ⁅g, h⁆⁆ * ⁅g, h⁆ ^ 2 := by
          simp only [commutatorElement_def, pow_two]
          group
        have hone : ⁅g ^ 2, h⁆ = 1 := by
          rw [hsq_comm, hnested, hcomm_sq]
          simp
        exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A q
      have hmk :
          QuotientGroup.mk' A (g ^ 2) = 1 :=
        (QuotientGroup.eq_one_iff (N := A) (g ^ 2)).2
          (hsquare_mem_A g)
      simpa only [map_pow] using hmk
    have hPhi_of_quot_two :
        (∀ q : P ⧸ A, q ^ 2 = 1) → PhiP ≤ A := by
      intro hquot
      have hsquare_mem_A : ∀ g : P, g ^ 2 ∈ A := by
        intro g
        have hq := hquot (QuotientGroup.mk' A g)
        have hmk : QuotientGroup.mk' A (g ^ 2) = 1 := by
          simpa only [map_pow] using hq
        exact (QuotientGroup.eq_one_iff (N := A) (g ^ 2)).1 hmk
      have hcomm_le_A_top :
          commutator (⊤ : Subgroup P) ≤
            A.comap (⊤ : Subgroup P).subtype := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro x _hx y _hy
        change ⁅(x : P), (y : P)⁆ ∈ A
        have hx2 : (x : P) ^ 2 ∈ A :=
          hsquare_mem_A (x : P)
        have hxy2 : ((x : P)⁻¹ * (y : P)) ^ 2 ∈ A :=
          hsquare_mem_A ((x : P)⁻¹ * (y : P))
        have hy2inv : ((y : P) ^ 2)⁻¹ ∈ A :=
          A.inv_mem (hsquare_mem_A (y : P))
        rw [show ⁅(x : P), (y : P)⁆ =
            (x : P) ^ 2 * ((x : P)⁻¹ * (y : P)) ^ 2 *
              ((y : P) ^ 2)⁻¹ by
          simp only [commutatorElement_def, pow_two]
          group]
        exact A.mul_mem (A.mul_mem hx2 hxy2) hy2inv
      have hPhi_top_le :
          frattini (⊤ : Subgroup P) ≤
            A.comap (⊤ : Subgroup P).subtype := by
        letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        haveI : Fact (IsPGroup 2 (⊤ : Subgroup P)) :=
          ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup ⊤⟩
        rw [frattini_eq_closure_commutator_union_powers
          (R := (⊤ : Subgroup P)) (p := 2), Subgroup.closure_le]
        intro z hz
        rcases hz with hz | ⟨x, rfl⟩
        · exact hcomm_le_A_top hz
        · change (x : P) ^ 2 ∈ A
          exact hsquare_mem_A (x : P)
      rintro _ ⟨z, hz, rfl⟩
      exact hPhi_top_le hz
    exact hPhi_not_le (hPhi_of_quot_two hquot_two)
  exact ⟨hA_exp4, hPhi_le_A⟩
/-- A minimal nontrivial normal `X`-invariant subgroup of a Higman Suzuki
`2`-group is elementary abelian. -/
public theorem lemma9_minimal_invariant_abelian_exponent_two
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P) {B : Subgroup P}
    (hB_normal : B.Normal) (hB_X : IsXInvariantSubgroup X B)
    (hB_ne : B ≠ ⊥)
    (hB_min : ∀ D : Subgroup P, D.Normal → IsXInvariantSubgroup X D →
      D ≤ B → D = ⊥ ∨ D = B) :
    IsMulCommutative B ∧ ∀ x : B, x ^ 2 = 1 := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Group.IsNilpotent P :=
    IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup hP)
  have hB_abelian : IsMulCommutative B := by
    letI : B.Normal := hB_normal
    let D : Subgroup P := (commutator B).map B.subtype
    have hD_lt : D < B := by
      rw [show D = ⁅B, B⁆ by exact B.map_subtype_commutator]
      exact IsSolvable.commutator_lt_of_ne_bot hB_ne
    have hD_normal : D.Normal := by
      dsimp [D]
      infer_instance
    have hD_X : IsXInvariantSubgroup X D := by
      letI : IsInvariant X P B := ⟨hB_X⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨b, hb, rfl⟩
        refine ⟨x • b, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (show (commutator B).Characteristic from inferInstance)
            (MulDistribMulAction.toMulAut X B x)) hb
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_bot : D = ⊥ := by
      rcases hB_min D hD_normal hD_X hD_lt.le with hbot | htop
      · exact hbot
      · exact False.elim (hD_lt.ne htop)
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    apply Subtype.ext
    have hmem : ⁅(x : P), (y : P)⁆ ∈ D := by
      rw [show D = ⁅B, B⁆ by exact B.map_subtype_commutator]
      exact Subgroup.commutator_mem_commutator x.property y.property
    rw [hD_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using hmem)
  have hB_exponent_two : ∀ x : B, x ^ 2 = 1 := by
    letI : B.Normal := hB_normal
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fact (IsPGroup 2 B) :=
      ⟨(isPGroup_of_isSuzukiTwoGroup hP).to_subgroup B⟩
    let S : Subgroup B := squaresSubgroup B
    have hS_le_frattini : S ≤ frattini B := by
      change squaresSubgroup B ≤ frattini B
      rw [squaresSubgroup, Subgroup.closure_le]
      rintro _ ⟨z, rfl⟩
      rw [frattini_eq_closure_commutator_union_powers
        (R := B) (p := 2)]
      exact Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
    have hfrattini_ne_top : frattini B ≠ ⊤ := by
      intro htop
      have hbot_top : (⊥ : Subgroup B) = ⊤ :=
        frattini_nongenerating (G := B) (K := ⊥) (by simp [htop])
      apply hB_ne
      apply le_antisymm
      · intro b hb
        let bB : B := ⟨b, hb⟩
        have hbBot : bB ∈ (⊥ : Subgroup B) := by
          rw [hbot_top]
          trivial
        have hbOne : bB = 1 := by simpa using hbBot
        simpa [bB] using congrArg (fun z : B => (z : P)) hbOne
      · exact bot_le
    have hS_lt_top : S < ⊤ :=
      lt_of_le_of_lt hS_le_frattini
        (lt_top_iff_ne_top.mpr hfrattini_ne_top)
    let D : Subgroup P := S.map B.subtype
    have hD_normal : D.Normal := by
      dsimp [D, S]
      infer_instance
    have hD_X : IsXInvariantSubgroup X D := by
      letI : IsInvariant X P B := ⟨hB_X⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨b, hb, rfl⟩
        refine ⟨x • b, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (squaresSubgroupCharacteristic B)
            (MulDistribMulAction.toMulAut X B x)) hb
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_lt_B : D < B := by
      have hD_le : D ≤ B := by
        rintro _ ⟨b, _hb, rfl⟩
        exact b.property
      refine lt_of_le_of_ne hD_le ?_
      intro hDB
      have htopmap : (⊤ : Subgroup B).map B.subtype = B := by
        apply le_antisymm
        · rintro _ ⟨b, _hb, rfl⟩
          exact b.property
        · intro b hb
          exact ⟨⟨b, hb⟩, trivial, rfl⟩
      apply hS_lt_top.ne
      apply Subgroup.map_injective B.subtype_injective
      rw [htopmap]
      exact hDB
    have hD_bot : D = ⊥ := by
      rcases hB_min D hD_normal hD_X hD_lt_B.le with hbot | htop
      · exact hbot
      · exact False.elim (hD_lt_B.ne htop)
    have hS_bot : S = ⊥ := by
      apply Subgroup.map_injective B.subtype_injective
      rw [Subgroup.map_bot]
      exact hD_bot
    intro x
    have hx : x ^ 2 ∈ S := Subgroup.subset_closure ⟨x, rfl⟩
    rw [hS_bot] at hx
    simpa using hx
  exact ⟨hB_abelian, hB_exponent_two⟩
/-- The Frattini subgroup of a Higman Suzuki `2`-group is abelian and has
exponent at most four. This packages the common first step in the concluding
length computations. -/
public theorem lemma9_frattini_abelian_exponent_four
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXcyclic : IsCyclic X) (hXfaithful : FaithfulSMul X P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x) :
    let PhiTop : Subgroup P :=
      (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype
    IsMulCommutative PhiTop ∧ ∀ x : PhiTop, x ^ 4 = 1 := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Fintype (Subgroup P) := Fintype.ofFinite _
  let PhiTop : Subgroup P :=
    (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype
  let S : Finset (Subgroup P) :=
    Finset.univ.filter fun M =>
      M.Normal ∧ IsMulCommutative M ∧ IsXInvariantSubgroup X M
  have hbot_abelian : IsMulCommutative (⊥ : Subgroup P) := by
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    exact Subsingleton.elim _ _
  have hbot_X : IsXInvariantSubgroup X (⊥ : Subgroup P) := by
    intro x a
    constructor
    · intro ha
      rw [Subgroup.mem_bot.mp ha]
      simp
    · intro ha
      have h := congrArg (fun t : P => x⁻¹ • t) (Subgroup.mem_bot.mp ha)
      apply Subgroup.mem_bot.mpr
      simpa [smul_smul] using h
  have hbot_mem : (⊥ : Subgroup P) ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, inferInstance, hbot_abelian, hbot_X⟩
  obtain ⟨M, hMmax⟩ := Finset.exists_maximal (s := S) ⟨⊥, hbot_mem⟩
  have hMdata := (Finset.mem_filter.mp hMmax.1).2
  have hM_max : ∀ C : Subgroup P, C.Normal → IsMulCommutative C →
      IsXInvariantSubgroup X C → M < C → False := by
    intro C hCnormal hCcomm hCX hMC
    have hCmem : C ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hCnormal, hCcomm, hCX⟩
    exact hMC.2 (hMmax.2 hCmem hMC.le)
  have hM_result := lemma9_maximal_abelian_contains_frattini
    hP hXcyclic hXfaithful hXtrans hMdata.1 hMdata.2.1
      hMdata.2.2 hM_max
  have hPhi_le_M : PhiTop ≤ M := hM_result.2
  refine ⟨?_, ?_⟩
  · letI : IsMulCommutative M := hMdata.2.1
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    let mx : M := ⟨x, hPhi_le_M x.property⟩
    let my : M := ⟨y, hPhi_le_M y.property⟩
    apply Subtype.ext
    simpa [mx, my] using congrArg Subtype.val (mul_comm mx my)
  · intro x
    let mx : M := ⟨x, hPhi_le_M x.property⟩
    have hx := congrArg M.subtype (hM_result.1 mx)
    apply Subtype.ext
    simpa [mx] using hx
end Higman
end External
end CFSG.BenderSuzuki
