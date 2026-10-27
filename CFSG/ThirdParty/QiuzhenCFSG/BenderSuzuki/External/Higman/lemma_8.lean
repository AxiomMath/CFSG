module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import Mathlib.LinearAlgebra.FixedSubmodule

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 8
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped commutatorElement

universe u

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Higman Lemma 8: if the commutator subgroup of a normal `X`-invariant cover
lies below the abelian subgroup, then that abelian subgroup has exponent at most
two. -/
public theorem lemma8_cover_commutator_case_exponent_two
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A C : Subgroup P} (_hA_normal : A.Normal)
    (_hA_abelian : IsMulCommutative A) (_hA_X : IsXInvariantSubgroup X A)
    (_hC_normal : C.Normal) (_hC_X : IsXInvariantSubgroup X C)
    (_hAC : A < C)
    (_hcover : ∀ B : Subgroup P, B.Normal → IsXInvariantSubgroup X B →
      A < B → B < C → False)
    (_hcomm : (commutator C).map C.subtype = A) :
    ∀ x : A, x ^ 2 = 1 := by
  classical
  let : Finite P := finite_of_isSuzukiTwoGroup _hP
  let : Finite C := inferInstance
  let : FaithfulSMul X P := _hXfaithful
  let : Finite X := Finite.of_injective
    (MulDistribMulAction.toMulAut X P) (by
      intro x y hxy
      apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
      intro p
      exact congrArg (fun f : MulAut P => f p) hxy)
  by_contra hA_exponent
  have hC_two : IsPGroup 2 C :=
    (isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup C
  have hC_nonabelian : ¬ IsMulCommutative C := by
    intro hC_comm
    let : IsMulCommutative C := hC_comm
    let : CommGroup C := IsMulCommutative.instCommGroup
    have hcomm_bot : commutator C = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact CommGroup.center_eq_top
    have hA_bot : A = ⊥ := by
      rw [← _hcomm, hcomm_bot, Subgroup.map_bot]
    apply hA_exponent
    intro x
    have hx : x = 1 := by
      apply Subtype.ext
      simpa [hA_bot] using x.property
    simp [hx]
  let : Fact (IsPGroup 2 C) := ⟨hC_two⟩
  let : IsInvariant X P C := ⟨_hC_X⟩
  let : IsCyclic X := _hXcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  let tau : MulAut C := MulDistribMulAction.toMulAut X C g
  obtain ⟨k, m, hm_odd, htau_order⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos tau).ne'
  let xi : MulAut C := tau ^ (2 ^ k)
  have hxi_odd : Odd (orderOf xi) := by
    have hk_dvd : 2 ^ k ∣ orderOf tau := by
      rw [htau_order]
      exact dvd_mul_right (2 ^ k) m
    have horder : orderOf (tau ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity : 2 ^ k ≠ 0) hk_dvd,
        htau_order]
      exact Nat.mul_div_cancel_left m (by positivity)
    change Odd (orderOf (tau ^ (2 ^ k)))
    rw [horder]
    exact hm_odd
  have hfrattini : A = (frattini C).map C.subtype := by
    let Phi : Subgroup P := (frattini C).map C.subtype
    change A = Phi
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hA_le_Phi : A ≤ Phi := by
      intro a ha
      rw [← _hcomm] at ha
      rcases ha with ⟨c, hc, rfl⟩
      exact ⟨c, commutator_le_frattini_of_isPGroup (R := C) (p := 2) hc, rfl⟩
    have hPhi_le_C : Phi ≤ C := by
      rintro _ ⟨c, _hc, rfl⟩
      exact c.property
    have hPhi_normal : Phi.Normal := by
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
    have hPhi_X : IsXInvariantSubgroup X Phi := by
      have hforward : ∀ x : X, ∀ p : P, p ∈ Phi → x • p ∈ Phi := by
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
    have hC_ne_bot : C ≠ ⊥ :=
      ne_of_gt (lt_of_le_of_lt bot_le _hAC)
    have hfrattini_ne_top : frattini C ≠ ⊤ := by
      intro htop
      have hbot_top : (⊥ : Subgroup C) = ⊤ :=
        frattini_nongenerating (G := C) (K := ⊥) (by simp [htop])
      apply hC_ne_bot
      apply le_antisymm
      · intro c hc
        let cC : C := ⟨c, hc⟩
        have hcBot : cC ∈ (⊥ : Subgroup C) := by
          rw [hbot_top]
          trivial
        have hcOne : cC = 1 := by simpa using hcBot
        simpa [cC] using congrArg (fun z : C => (z : P)) hcOne
      · exact bot_le
    have htopmap : (⊤ : Subgroup C).map C.subtype = C := by
      apply le_antisymm
      · rintro _ ⟨c, _hc, rfl⟩
        exact c.property
      · intro c hc
        exact ⟨⟨c, hc⟩, trivial, rfl⟩
    have hPhi_ne_C : Phi ≠ C := by
      intro hPhi
      apply hfrattini_ne_top
      apply Subgroup.map_injective C.subtype_injective
      rw [htopmap]
      exact hPhi
    have hPhi_lt_C : Phi < C :=
      lt_of_le_of_ne hPhi_le_C hPhi_ne_C
    by_cases hEq : A = Phi
    · exact hEq
    · exact False.elim
        (_hcover Phi hPhi_normal hPhi_X
          (lt_of_le_of_ne hA_le_Phi hEq) hPhi_lt_C)
  have hC_L1 : higmanLowerCentralSeries C 1 = commutator C := by
    change (⊤ : Subgroup C).lowerCentralSeries 1 = commutator C
    exact Subgroup.top_lowerCentralSeries_one
  have hC_square : squaresSubgroup C ≤ higmanLowerCentralSeries C 1 := by
    have hsquares_le_phi : squaresSubgroup C ≤ frattini C := by
      rw [squaresSubgroup, Subgroup.closure_le]
      rintro _ ⟨z, rfl⟩
      rw [frattini_eq_closure_commutator_union_powers
        (R := C) (p := 2)]
      exact Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
    rw [hC_L1]
    intro x hx
    have hxA : (x : P) ∈ A := by
      rw [hfrattini]
      exact ⟨x, hsquares_le_phi hx, rfl⟩
    rw [← _hcomm] at hxA
    rcases hxA with ⟨y, hy, hyx⟩
    have hyx' : y = x := C.subtype_injective hyx
    simpa [hyx'] using hy
  have hL1_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor C 0)),
        (∀ v : Additive (LowerCentralFactor C 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    have hPCcomm_le_A : ⁅(⊤ : Subgroup P), C⁆ ≤ A := by
      let K : Subgroup P := ⁅(⊤ : Subgroup P), C⁆
      have hcomm_proper : K < C := by
        refine lt_of_le_of_ne (by
          simpa [K] using
            (Subgroup.commutator_le_right (⊤ : Subgroup P) C)) ?_
        intro hKC
        have hC_ne_bot : C ≠ ⊥ :=
          ne_of_gt (lt_of_le_of_lt bot_le _hAC)
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hnil : Group.IsNilpotent P :=
          IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup _hP)
        obtain ⟨n, hn⟩ :=
          Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
        have hC_le : ∀ i : ℕ, C ≤ higmanLowerCentralSeries P i := by
          intro i
          induction i with
          | zero => simp
          | succ i ih =>
              change C ≤ (⊤ : Subgroup P).lowerCentralSeries (i + 1)
              rw [Subgroup.lowerCentralSeries_succ]
              change C ≤ ⁅higmanLowerCentralSeries P i, (⊤ : Subgroup P)⁆
              calc
                C = ⁅(⊤ : Subgroup P), C⁆ := by
                  simpa [K] using hKC.symm
                _ = ⁅C, (⊤ : Subgroup P)⁆ :=
                  Subgroup.commutator_comm _ _
                _ ≤ ⁅higmanLowerCentralSeries P i, (⊤ : Subgroup P)⁆ :=
                  Subgroup.commutator_mono ih le_rfl
        have hbot : C ≤ ⊥ := by
          rw [← hn]
          exact hC_le n
        exact hC_ne_bot (bot_unique hbot)
      have hcomm_X : IsXInvariantSubgroup X K := by
        have hmap (x : X) :
            K.map (MulDistribMulAction.toMulAut X P x).toMonoidHom = K := by
          have hCmap :
              C.map (MulDistribMulAction.toMulAut X P x).toMonoidHom = C := by
            apply le_antisymm
            · rintro y ⟨z, hz, rfl⟩
              exact (_hC_X x z).mp hz
            · intro y hy
              refine ⟨x⁻¹ • y, (_hC_X x⁻¹ y).mp hy, ?_⟩
              simp [MulDistribMulAction.toMulAut_apply, smul_smul]
          have htopmap :
              (⊤ : Subgroup P).map
                  (MulDistribMulAction.toMulAut X P x).toMonoidHom = ⊤ :=
            Subgroup.map_top_of_surjective _
              (MulDistribMulAction.toMulAut X P x).surjective
          change ⁅(⊤ : Subgroup P), C⁆.map
              (MulDistribMulAction.toMulAut X P x).toMonoidHom =
            ⁅(⊤ : Subgroup P), C⁆
          rw [Subgroup.map_commutator, htopmap, hCmap]
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
      have hsup_lt : A ⊔ K < C := by
        refine lt_of_le_of_ne (sup_le _hAC.le hcomm_proper.le) ?_
        intro hEq
        let Kc : Subgroup C := K.subgroupOf C
        have hKcmap : Kc.map C.subtype = K := by
          exact Subgroup.map_subgroupOf_eq_of_le hcomm_proper.le
        have htopmap : (⊤ : Subgroup C).map C.subtype = C := by
          apply le_antisymm
          · rintro y ⟨z, _hz, rfl⟩
            exact z.property
          · intro y hy
            exact ⟨⟨y, hy⟩, trivial, rfl⟩
        have hinside : frattini C ⊔ Kc = ⊤ := by
          apply Subgroup.map_injective C.subtype_injective
          rw [Subgroup.map_sup, ← hfrattini, hKcmap, htopmap]
          exact hEq
        have hKc_top : Kc = ⊤ :=
          frattini_nongenerating (by
            simpa [sup_comm] using hinside)
        have hKC : K = C := by
          rw [← hKcmap, hKc_top, htopmap]
        exact hcomm_proper.ne hKC
      by_contra hK
      have hA_lt : A < A ⊔ K := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro hEq
        have hle : K ≤ A :=
          le_trans le_sup_right (le_of_eq hEq.symm)
        exact hK hle
      have hsup_X : IsXInvariantSubgroup X (A ⊔ K) := by
        have hmap (x : X) :
            (A ⊔ K).map
                (MulDistribMulAction.toMulAut X P x).toMonoidHom = A ⊔ K := by
          have hAmap :
              A.map (MulDistribMulAction.toMulAut X P x).toMonoidHom = A := by
            apply le_antisymm
            · rintro y ⟨z, hz, rfl⟩
              exact (_hA_X x z).mp hz
            · intro y hy
              refine ⟨x⁻¹ • y, (_hA_X x⁻¹ y).mp hy, ?_⟩
              simp [MulDistribMulAction.toMulAut_apply, smul_smul]
          have hKmap :
              K.map (MulDistribMulAction.toMulAut X P x).toMonoidHom = K := by
            apply le_antisymm
            · rintro y ⟨z, hz, rfl⟩
              exact (hcomm_X x z).mp hz
            · intro y hy
              refine ⟨x⁻¹ • y, (hcomm_X x⁻¹ y).mp hy, ?_⟩
              simp [MulDistribMulAction.toMulAut_apply, smul_smul]
          rw [Subgroup.map_sup, hAmap, hKmap]
        intro x a
        constructor
        · intro ha
          have hmem :
              (MulDistribMulAction.toMulAut X P x) a ∈
                (A ⊔ K).map
                  (MulDistribMulAction.toMulAut X P x).toMonoidHom :=
            ⟨a, ha, rfl⟩
          rw [hmap x] at hmem
          simpa [MulDistribMulAction.toMulAut_apply] using hmem
        · intro ha
          have hmem :
              (MulDistribMulAction.toMulAut X P x⁻¹) (x • a) ∈
                (A ⊔ K).map
                  (MulDistribMulAction.toMulAut X P x⁻¹).toMonoidHom :=
            ⟨x • a, ha, rfl⟩
          rw [hmap x⁻¹] at hmem
          simpa [MulDistribMulAction.toMulAut_apply, smul_smul] using hmem
      exact _hcover (A ⊔ K) (by infer_instance) hsup_X hA_lt hsup_lt
    have htau_irreducible :
        ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor C 0)),
          (∀ v : Additive (LowerCentralFactor C 0), v ∈ W →
            lowerCentralFactorLinearAut tau 0 v ∈ W) →
          W = ⊥ ∨ W = ⊤ := by
      have hkernel_map_frattini :
          (lowerCentralFactorKernel C 0).map
              (higmanLowerCentralSeries C 0).subtype = frattini C := by
        have hsquares_map :
            (squaresSubgroup (higmanLowerCentralSeries C 0)).map
                (higmanLowerCentralSeries C 0).subtype = squaresSubgroup C := by
          apply le_antisymm
          · rw [squaresSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
            rintro y ⟨z, hz, rfl⟩
            rcases hz with ⟨w, rfl⟩
            exact Subgroup.subset_closure ⟨(w : C), rfl⟩
          · rw [squaresSubgroup, Subgroup.closure_le]
            rintro _ ⟨c, rfl⟩
            let c0 : higmanLowerCentralSeries C 0 := ⟨c, by simp⟩
            refine ⟨c0 ^ 2, Subgroup.subset_closure ⟨c0, rfl⟩, ?_⟩
            rfl
        have hnext_map :
            ((higmanLowerCentralSeries C 1).subgroupOf
                (higmanLowerCentralSeries C 0)).map
              (higmanLowerCentralSeries C 0).subtype =
                higmanLowerCentralSeries C 1 :=
          Subgroup.map_subgroupOf_eq_of_le
            ((⊤ : Subgroup C).lowerCentralSeries_antitone
              (by omega : 0 ≤ 1))
        rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map,
          hnext_map, hC_L1,
          frattini_eq_closure_commutator_union_powers (R := C) (p := 2)]
        apply le_antisymm
        · apply sup_le
          · rw [squaresSubgroup, Subgroup.closure_le]
            rintro _ ⟨c, rfl⟩
            exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
          · intro z hz
            exact Subgroup.subset_closure (Or.inl hz)
        · rw [Subgroup.closure_le]
          intro z hz
          rcases hz with hz | hz
          · exact (le_sup_right : commutator C ≤ squaresSubgroup C ⊔ commutator C) hz
          · exact (le_sup_left : squaresSubgroup C ≤ squaresSubgroup C ⊔ commutator C)
              (Subgroup.subset_closure hz)
      intro W hW
      let Wsub : Subgroup (LowerCentralFactor C 0) :=
        AddSubgroup.toSubgroup' W.toAddSubgroup
      let qC : C →* LowerCentralFactor C 0 :=
        (QuotientGroup.mk' (lowerCentralFactorKernel C 0)).comp
          Subgroup.topEquiv.symm.toMonoidHom
      have hqker : qC.ker = frattini C := by
        ext c
        change
          (QuotientGroup.mk' (lowerCentralFactorKernel C 0)
            (Subgroup.topEquiv.symm c) = 1) ↔ c ∈ frattini C
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          ← hkernel_map_frattini]
        constructor
        · intro hc
          exact ⟨Subgroup.topEquiv.symm c, hc, rfl⟩
        · rintro ⟨z, hz, hzc⟩
          have hz_eq : z = Subgroup.topEquiv.symm c := by
            apply Subtype.ext
            exact hzc
          rw [← hz_eq]
          exact hz
      let Bc : Subgroup C := Wsub.comap qC
      let B : Subgroup P := Bc.map C.subtype
      have hqC_equivariant (x : X) (c : C) :
          Additive.ofMul (qC (x • c)) =
            lowerCentralFactorLinearAut
              (MulDistribMulAction.toMulAut X C x) 0
              (Additive.ofMul (qC c)) := by
        change
          Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel C 0)
                (Subgroup.topEquiv.symm (x • c))) =
            lowerCentralFactorLinearAut
              (MulDistribMulAction.toMulAut X C x) 0
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel C 0)
                  (Subgroup.topEquiv.symm c)))
        rw [lowerCentralFactorLinearAut_ofMul_mk]
        apply Additive.toMul.injective
        apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel C 0))
        apply Subtype.ext
        rfl
      have hA_le_B : A ≤ B := by
        intro a ha
        rw [hfrattini] at ha
        rcases ha with ⟨c, hc, rfl⟩
        refine ⟨c, ?_, rfl⟩
        change qC c ∈ Wsub
        have hcKer : c ∈ qC.ker := by
          rw [hqker]
          exact hc
        rw [MonoidHom.mem_ker.mp hcKer]
        exact Wsub.one_mem
      have hB_le_C : B ≤ C := by
        rintro _ ⟨c, _hc, rfl⟩
        exact c.property
      have hB_normal : B.Normal := by
        constructor
        intro b hb p
        have hbC : b ∈ C := hB_le_C hb
        have hcommK : ⁅p, b⁆ ∈ ⁅(⊤ : Subgroup P), C⁆ :=
          Subgroup.commutator_mem_commutator trivial hbC
        have hcommB : ⁅p, b⁆ ∈ B :=
          hA_le_B (hPCcomm_le_A hcommK)
        have hprod := B.mul_mem hcommB hb
        convert hprod using 1
        all_goals simp [commutatorElement_def]
      have hB_X : IsXInvariantSubgroup X B := by
        have hWpow : ∀ n : ℕ,
            ∀ v : Additive (LowerCentralFactor C 0), v ∈ W →
              (lowerCentralFactorLinearAut tau 0 ^ n) v ∈ W := by
          intro n v hv
          induction n with
          | zero => simpa using hv
          | succ n ih =>
              rw [pow_succ', LinearEquiv.mul_apply]
              exact hW _ ih
        have hforward : ∀ x : X, ∀ p : P, p ∈ B → x • p ∈ B := by
          intro x p hp
          rcases hp with ⟨c, hc, rfl⟩
          obtain ⟨n, rfl⟩ :=
            mem_powers_iff_mem_zpowers.mpr (hg x)
          refine ⟨g ^ n • c, ?_, rfl⟩
          change qC (g ^ n • c) ∈ Wsub
          change qC c ∈ Wsub at hc
          have hcW : Additive.ofMul (qC c) ∈ W := by
            simpa [Wsub] using hc
          have hactW :
              lowerCentralFactorLinearAut
                  (MulDistribMulAction.toMulAut X C (g ^ n)) 0
                  (Additive.ofMul (qC c)) ∈ W := by
            rw [map_pow, lowerCentralFactorLinearAut_pow]
            simpa [tau] using hWpow n _ hcW
          have hout : Additive.ofMul (qC (g ^ n • c)) ∈ W := by
            rw [hqC_equivariant]
            exact hactW
          simpa [Wsub] using hout
        intro x p
        constructor
        · exact hforward x p
        · intro hp
          have hpinv := hforward x⁻¹ (x • p) hp
          simpa [smul_smul] using hpinv
      by_cases hWbot : W = ⊥
      · exact Or.inl hWbot
      · right
        have hqC_surj : Function.Surjective qC := by
          intro v
          obtain ⟨z, rfl⟩ :=
            QuotientGroup.mk'_surjective (lowerCentralFactorKernel C 0) v
          refine ⟨Subgroup.topEquiv z, ?_⟩
          exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel C 0))
            (Subgroup.topEquiv.symm_apply_apply z)
        have hbot_lt : (⊥ : Submodule (ZMod 2)
            (Additive (LowerCentralFactor C 0))) < W :=
          bot_lt_iff_ne_bot.mpr hWbot
        obtain ⟨v, hvW, hv0⟩ := SetLike.exists_of_lt hbot_lt
        have hv_ne : v ≠ 0 := by simpa using hv0
        obtain ⟨c, hcval⟩ := hqC_surj v.toMul
        have hcBc : c ∈ Bc := by
          change qC c ∈ Wsub
          rw [hcval]
          simpa [Wsub] using hvW
        have hcB : (c : P) ∈ B := ⟨c, hcBc, rfl⟩
        have hcA : (c : P) ∉ A := by
          intro hcA
          rw [hfrattini] at hcA
          rcases hcA with ⟨d, hd, hdc⟩
          have hdc' : d = c := C.subtype_injective hdc
          subst d
          have hcKer : c ∈ qC.ker := by
            rw [hqker]
            exact hd
          have hqone : qC c = 1 := MonoidHom.mem_ker.mp hcKer
          apply hv_ne
          apply Additive.toMul.injective
          simp [← hcval, hqone]
        have hA_lt_B : A < B := by
          refine lt_of_le_of_ne hA_le_B ?_
          intro hEq
          have : (c : P) ∈ A := by
            rw [hEq]
            exact hcB
          exact hcA this
        have hB_eq_C : B = C := by
          by_cases hEq : B = C
          · exact hEq
          · exact False.elim
              (_hcover B hB_normal hB_X hA_lt_B
                (lt_of_le_of_ne hB_le_C hEq))
        apply eq_top_iff.mpr
        intro v _hv
        obtain ⟨c, hcval⟩ := hqC_surj v.toMul
        have hcB : (c : P) ∈ B := by
          rw [hB_eq_C]
          exact c.property
        rcases hcB with ⟨d, hd, hdc⟩
        have hdc' : d = c := C.subtype_injective hdc
        subst d
        change qC c ∈ Wsub at hd
        rw [hcval] at hd
        simpa [Wsub] using hd
    have htau_power_on_L1 :
        ∃ r : ℕ, lowerCentralFactorLinearAut tau 0 =
          (lowerCentralFactorLinearAut xi 0) ^ r := by
      have hT_odd :
          Odd (orderOf (lowerCentralFactorLinearAut tau 0)) := by
        rw [← Nat.not_even_iff_odd]
        intro hEven
        let T := lowerCentralFactorLinearAut tau 0
        have hT_finite : IsOfFinOrder T := by
          rw [isOfFinOrder_iff_pow_eq_one]
          refine ⟨orderOf tau, orderOf_pos tau, ?_⟩
          change (lowerCentralFactorLinearAut tau 0) ^ orderOf tau = 1
          rw [← lowerCentralFactorLinearAut_pow, pow_orderOf_eq_one]
          exact map_one (lowerCentralFactorLinearAutHom (H := C) 0)
        obtain ⟨d, hd⟩ := hEven
        have hord : orderOf T = 2 * d := by
          change orderOf T = d + d at hd
          omega
        have hord_pos : 0 < orderOf T :=
          orderOf_pos_iff.mpr hT_finite
        have hd_pos : 0 < d := by omega
        let U := T ^ d
        have hU_sq : U ^ 2 = 1 := by
          change (T ^ d) ^ 2 = 1
          rw [← pow_mul, Nat.mul_comm, ← hord, pow_orderOf_eq_one]
        have hU_ne : U ≠ 1 := by
          intro hU
          have hle : orderOf T ≤ d :=
            orderOf_le_of_pow_eq_one hd_pos (by simpa [U] using hU)
          omega
        have hfixed_ne_top : U.fixedSubmodule ≠ ⊤ := by
          intro htop
          have hU_refl : U = LinearEquiv.refl (ZMod 2)
              (Additive (LowerCentralFactor C 0)) :=
            LinearEquiv.fixedSubmodule_eq_top_iff.mp htop
          apply hU_ne
          rw [hU_refl]
          apply LinearEquiv.ext
          intro v
          rfl
        obtain ⟨v, hv⟩ :
            ∃ v : Additive (LowerCentralFactor C 0), U v ≠ v := by
          by_contra h
          push Not at h
          apply hU_ne
          ext v
          simpa using h v
        let w := U v - v
        have hw_ne : w ≠ 0 := by
          simpa [w] using sub_ne_zero.mpr hv
        have hU_apply_apply : U (U v) = v := by
          calc
            U (U v) = (U * U) v := by
              rw [LinearEquiv.mul_apply]
            _ = v := by
              rw [← pow_two, hU_sq]
              rfl
        have hw_fixed : U w = w := by
          dsimp [w]
          rw [map_sub, hU_apply_apply]
          simp only [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
        have hw_mem : w ∈ U.fixedSubmodule := by
          rw [LinearMap.mem_fixedSubmodule_iff]
          exact hw_fixed
        have hfixed_ne_bot : U.fixedSubmodule ≠ ⊥ := by
          intro hbot
          have hw_bot : w ∈
              (⊥ : Submodule (ZMod 2)
                (Additive (LowerCentralFactor C 0))) := by
            rw [← hbot]
            exact hw_mem
          exact hw_ne (by simpa using hw_bot)
        have hfixed_T :
            ∀ z : Additive (LowerCentralFactor C 0),
              z ∈ U.fixedSubmodule → T z ∈ U.fixedSubmodule := by
          intro z hz
          rw [LinearMap.mem_fixedSubmodule_iff] at hz ⊢
          change U z = z at hz
          change U (T z) = T z
          calc
            U (T z) = (U * T) z := rfl
            _ = (T * U) z := by
              change (T ^ d * T) z = (T * T ^ d) z
              rw [← pow_succ, pow_succ']
            _ = T (U z) := rfl
            _ = T z := by rw [hz]
        rcases htau_irreducible U.fixedSubmodule hfixed_T with hbot | htop
        · exact hfixed_ne_bot hbot
        · exact hfixed_ne_top htop
      have hcoprime :
          Nat.Coprime (2 ^ k)
            (orderOf (lowerCentralFactorLinearAut tau 0)) :=
        Nat.Coprime.pow_left k hT_odd.coprime_two_left
      obtain ⟨r, hr⟩ :=
        exists_pow_eq_self_of_coprime
          (x := lowerCentralFactorLinearAut tau 0) hcoprime
      refine ⟨r, ?_⟩
      simpa [xi, lowerCentralFactorLinearAut_pow] using hr.symm
    intro W hW
    apply htau_irreducible W
    obtain ⟨r, hr⟩ := htau_power_on_L1
    intro v hv
    rw [hr]
    have hpow_mem : ∀ j : ℕ,
        (lowerCentralFactorLinearAut xi 0 ^ j) v ∈ W := by
      intro j
      induction j with
      | zero => simpa using hv
      | succ j ih =>
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hW _ ih
    exact hpow_mem r

  obtain ⟨e, r, ⟨hAcoord⟩, hApowers⟩ :=
    lemma1_abelian_invariant_homocyclic
      _hP _hXtrans _hA_abelian _hA_X
  have hA_ne : A ≠ ⊥ := by
    intro hA
    apply hA_exponent
    intro x
    have hx : x = 1 := by
      apply Subtype.ext
      simpa [hA] using x.property
    simp [hx]
  have he : 2 ≤ e := by
    by_contra he'
    have he_le : e ≤ 1 := by omega
    apply hA_exponent
    intro x
    have hpow := lemma1_pow_eq_one_of_homocyclic hAcoord x
    interval_cases e
    · simp at hpow
      simp [hpow]
    · simpa using hpow
  have hr : 2 ≤ r := by
    obtain ⟨x, y, hx, hy, hxy⟩ := _hP.2.2.1
    have hxA_mem :=
      lemma1_involutions_mem_of_nontrivial_invariant
        _hP _hXtrans _hA_X hA_ne x hx
    have hyA_mem :=
      lemma1_involutions_mem_of_nontrivial_invariant
        _hP _hXtrans _hA_X hA_ne y hy
    let xA : A := ⟨x, hxA_mem⟩
    let yA : A := ⟨y, hyA_mem⟩
    have hxA_sq : xA ^ 2 = 1 := by
      apply Subtype.ext
      simpa [xA] using hx.sq_eq_one
    have hyA_sq : yA ^ 2 = 1 := by
      apply Subtype.ext
      simpa [yA] using hy.sq_eq_one
    let T := {z : A // z ^ 2 = 1}
    let oneT : T := ⟨1, by simp⟩
    let xT : T := ⟨xA, hxA_sq⟩
    let yT : T := ⟨yA, hyA_sq⟩
    have hxT : xT ≠ oneT := by
      intro h
      apply hx.ne_one
      exact congrArg (fun z : T => ((z.1 : A) : P)) h
    have hyT : yT ≠ oneT := by
      intro h
      apply hy.ne_one
      exact congrArg (fun z : T => ((z.1 : A) : P)) h
    have hxyT : xT ≠ yT := by
      intro h
      apply hxy
      exact congrArg (fun z : T => ((z.1 : A) : P)) h
    let : Fintype T := Fintype.ofFinite T
    have hthree : ({oneT, xT, yT} : Finset T).card = 3 := by
      have hone : oneT ∉ ({xT, yT} : Finset T) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        intro h
        rcases h with h | h
        · exact hxT h.symm
        · exact hyT h.symm
      rw [Finset.card_insert_of_notMem hone]
      have hxnot : xT ∉ ({yT} : Finset T) := by
        simp [hxyT]
      rw [Finset.card_insert_of_notMem hxnot]
      simp
    have hle : 3 ≤ Nat.card T := by
      rw [Nat.card_eq_fintype_card, ← hthree]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hcard : Nat.card T = 2 ^ r :=
      lemma1_twoTorsion_card_of_homocyclic (by omega) hAcoord
    rw [hcard] at hle
    by_contra hr'
    have hrle : r ≤ 1 := by omega
    interval_cases r <;> norm_num at hle
  let : IsInvariant X P A := ⟨_hA_X⟩
  let : IsMulCommutative A := _hA_abelian
  let : CommGroup A := IsMulCommutative.instCommGroup
  let Asq : Subgroup A := (powMonoidHom 2 : A →* A).range
  let AQ := A ⧸ Asq
  have hAQ_two : ∀ q : AQ, q ^ 2 = 1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro a
    change ((a ^ 2 : A) : AQ) = 1
    rw [QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr
      ⟨a, by simp [powMonoidHom]⟩
  let : Module (ZMod 2) (Additive AQ) :=
    AddCommGroup.zmodModule <| by
      intro q
      apply Additive.toMul.injective
      simp only [toMul_nsmul, toMul_zero]
      exact hAQ_two q.toMul
  have hAQ_card : Nat.card AQ = 2 ^ r := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hcardA : Nat.card A = (2 ^ (d + 1)) ^ r := by
      calc
        Nat.card A =
            Nat.card (Multiplicative (Fin r → ZMod (2 ^ (d + 1)))) :=
          Nat.card_congr hAcoord.toEquiv
        _ = Nat.card (Fin r → ZMod (2 ^ (d + 1))) :=
          Nat.card_congr Multiplicative.toAdd
        _ = ∏ _i : Fin r, Nat.card (ZMod (2 ^ (d + 1))) := Nat.card_pi
        _ = (2 ^ (d + 1)) ^ r := by simp
    have hclosure :
        Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} =
          Asq.map A.subtype := by
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
    have hcardClosure :
        Nat.card (Subgroup.closure
          {x : P | ∃ a : A, (a : P) ^ 2 = x}) = (2 ^ d) ^ r := by
      simpa using
        (lemma1_power_closure_card _hA_abelian
          (e := d + 1) (r := r) (f := d) (by omega) hAcoord)
    have hcardAsq : Nat.card Asq = (2 ^ d) ^ r := by
      calc
        Nat.card Asq = Nat.card (Asq.map A.subtype) :=
          Nat.card_congr
            (Subgroup.equivMapOfInjective Asq A.subtype
              A.subtype_injective).toEquiv
        _ = Nat.card (Subgroup.closure
            {x : P | ∃ a : A, (a : P) ^ 2 = x}) := by rw [hclosure]
        _ = (2 ^ d) ^ r := hcardClosure
    have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup Asq
    change Nat.card A = Nat.card AQ * Nat.card Asq at hquot
    rw [hcardA, hcardAsq, pow_succ, mul_pow] at hquot
    have hpos : 0 < (2 ^ d) ^ r := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      Nat.card AQ * (2 ^ d) ^ r = (2 ^ d) ^ r * 2 ^ r := hquot.symm
      _ = 2 ^ r * (2 ^ d) ^ r := Nat.mul_comm _ _
  have hAsq_X : IsInvariant X A Asq := by
    constructor
    intro x a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨x • b, by simp [powMonoidHom]⟩
    · rintro ⟨b, hb⟩
      refine ⟨x⁻¹ • b, ?_⟩
      have h := congrArg (fun z : A => x⁻¹ • z) hb
      simpa [Asq, powMonoidHom, smul_smul] using h
  let : IsInvariant X A Asq := hAsq_X
  let : MulAction.QuotientAction X Asq :=
    quotientAction_of_isInvariant (A := X) (G := A) Asq hAsq_X
  let : MulDistribMulAction X AQ :=
    quotientMulDistribMulAction (A := X) (G := A) Asq (by infer_instance)
  let Ttau : Additive AQ ≃ₗ[ZMod 2] Additive AQ :=
    { (MulDistribMulAction.toMulAut X AQ g).toAdditive with
      map_smul' := fun c x => ZMod.map_smul
        (MulDistribMulAction.toMulAut X AQ g).toAdditive.toAddMonoidHom c x }
  let Txi : Additive AQ ≃ₗ[ZMod 2] Additive AQ := Ttau ^ (2 ^ k)
  have hAQ_transitive :
      ∀ x : Additive AQ, x ≠ 0 →
        ∀ y : Additive AQ, y ≠ 0 →
          ∃ j : ℕ, (Txi ^ j) x = y := by
    have hTxi_pow : Txi = Ttau ^ (2 ^ k) := rfl
    have hTtau_pow :
        ∀ j : ℕ, ∀ q : AQ,
          (Ttau ^ j) (Additive.ofMul q) =
            Additive.ofMul ((g ^ j) • q) := by
      intro j
      induction j with
      | zero =>
          intro q
          simp
      | succ j ih =>
          intro q
          rw [pow_succ', LinearEquiv.mul_apply, ih]
          apply Additive.toMul.injective
          simp [Ttau, MulDistribMulAction.toMulAut_apply, pow_succ', smul_smul]
    have hAQ_tau_transitive :
        ∀ x : Additive AQ, x ≠ 0 →
          ∀ y : Additive AQ, y ≠ 0 →
            ∃ j : ℕ, (Ttau ^ j) x = y := by
      intro x hx y hy
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Asq x.toMul
      obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective Asq y.toMul
      have ha_ne : (a : AQ) ≠ 1 := by
        intro ha1
        apply hx
        apply Additive.toMul.injective
        change x.toMul = 1
        rw [← ha]
        exact ha1
      have hb_ne : (b : AQ) ≠ 1 := by
        intro hb1
        apply hy
        apply Additive.toMul.injective
        change y.toMul = 1
        rw [← hb]
        exact hb1
      have hpow_ne (c : A) (hc : (c : AQ) ≠ 1) :
          c ^ (2 ^ (e - 1)) ≠ 1 := by
        intro hkill
        obtain ⟨z, hz⟩ :=
          lemma1_exists_power_root_of_homocyclic
            (e := e) (f := e - 1) (Nat.sub_le e 1) hAcoord hkill
        apply hc
        rw [QuotientGroup.eq_one_iff]
        refine MonoidHom.mem_range.mpr ⟨z, ?_⟩
        simpa [Asq, powMonoidHom,
          show e - (e - 1) = 1 by omega] using hz
      have hexp : 2 ^ (e - 1) * 2 = 2 ^ e := by
        rw [← pow_succ]
        congr 1
        omega
      have hpow_sq (c : A) : (c ^ (2 ^ (e - 1))) ^ 2 = 1 := by
        calc
          (c ^ (2 ^ (e - 1))) ^ 2 =
              c ^ (2 ^ (e - 1) * 2) := by rw [pow_mul]
          _ = c ^ (2 ^ e) := by rw [hexp]
          _ = 1 := lemma1_pow_eq_one_of_homocyclic hAcoord c
      have haInv : (a : P) ^ (2 ^ (e - 1)) ∈ involutions P := by
        refine ⟨?_, ?_⟩
        · intro ha1
          apply hpow_ne a ha_ne
          apply Subtype.ext
          simpa using ha1
        · simpa using congrArg A.subtype (hpow_sq a)
      have hbInv : (b : P) ^ (2 ^ (e - 1)) ∈ involutions P := by
        refine ⟨?_, ?_⟩
        · intro hb1
          apply hpow_ne b hb_ne
          apply Subtype.ext
          simpa using hb1
        · simpa using congrArg A.subtype (hpow_sq b)
      obtain ⟨z, hz⟩ := _hXtrans _ haInv _ hbInv
      let za : A := z • a
      have hpows : b ^ (2 ^ (e - 1)) = za ^ (2 ^ (e - 1)) := by
        apply Subtype.ext
        calc
          (b : P) ^ (2 ^ (e - 1)) =
              z • ((a : P) ^ (2 ^ (e - 1))) := hz
          _ = (z • (a : P)) ^ (2 ^ (e - 1)) :=
            smul_pow' z (a : P) (2 ^ (e - 1))
          _ = (za : P) ^ (2 ^ (e - 1)) := rfl
      have hkill : (b / za) ^ (2 ^ (e - 1)) = 1 := by
        calc
          (b / za) ^ (2 ^ (e - 1)) =
              b ^ (2 ^ (e - 1)) / za ^ (2 ^ (e - 1)) := div_pow b za _
          _ = 1 := by simp [hpows]
      obtain ⟨w, hw⟩ :=
        lemma1_exists_power_root_of_homocyclic
          (e := e) (f := e - 1) (Nat.sub_le e 1) hAcoord hkill
      have hactor : (b : AQ) = z • (a : AQ) := by
        apply (QuotientGroup.eq_iff_div_mem (N := Asq)).2
        refine MonoidHom.mem_range.mpr ⟨w, ?_⟩
        simpa [za, Asq, powMonoidHom,
          show e - (e - 1) = 1 by omega] using hw
      obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg z)
      refine ⟨j, ?_⟩
      rw [show x = Additive.ofMul x.toMul by rfl, hTtau_pow]
      apply Additive.toMul.injective
      rw [← ha, ← hb]
      exact hactor.symm
    have horder : orderOf Ttau = 2 ^ r - 1 :=
      lemma4_transitive_linearAut_order
        Ttau hAQ_tau_transitive r hr hAQ_card
    have hodd : Odd (orderOf Ttau) := by
      rw [horder]
      obtain ⟨d, hd⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      subst r
      refine ⟨2 ^ d - 1, ?_⟩
      rw [pow_succ]
      have hpow_pos : 0 < 2 ^ d := by positivity
      omega
    have hcoprime : Nat.Coprime (2 ^ k) (orderOf Ttau) :=
      Nat.Coprime.pow_left k hodd.coprime_two_left
    obtain ⟨u, hu⟩ :=
      exists_pow_eq_self_of_coprime (x := Ttau) hcoprime
    have hrecover : Ttau = Txi ^ u := by
      simpa [hTxi_pow] using hu.symm
    intro x hx y hy
    obtain ⟨j, hj⟩ := hAQ_tau_transitive x hx y hy
    refine ⟨u * j, ?_⟩
    simpa [pow_mul, ← hrecover] using hj
  have hL2_equiv :
      ∃ q : Additive AQ ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor C 1),
        ∀ v : Additive AQ,
          q (Txi v) =
            lowerCentralFactorLinearAut xi 1 (q v) := by
    have hTxi_pow : Txi = Ttau ^ (2 ^ k) := rfl
    have hTtau_pow :
        ∀ j : ℕ, ∀ q : AQ,
          (Ttau ^ j) (Additive.ofMul q) =
            Additive.ofMul ((g ^ j) • q) := by
      intro j
      induction j with
      | zero =>
          intro q
          simp
      | succ j ih =>
          intro q
          rw [pow_succ', LinearEquiv.mul_apply, ih]
          apply Additive.toMul.injective
          simp [Ttau, MulDistribMulAction.toMulAut_apply, pow_succ', smul_smul]
    let D : Subgroup P := (commutator C).map C.subtype
    have hD_le_A : D ≤ A := by
      simpa [D] using le_of_eq _hcomm
    have hD_ne : D ≠ ⊥ := by
      intro hD
      have hcomm_bot : commutator C = ⊥ := by
        apply Subgroup.map_injective C.subtype_injective
        simpa [D] using hD
      apply hC_nonabelian
      have hcenter : Subgroup.center C = ⊤ := by
        rw [← commutator_eq_bot_iff_center_eq_top]
        exact hcomm_bot
      refine ⟨⟨?_⟩⟩
      intro x y
      have hx : x ∈ Subgroup.center C := by
        rw [hcenter]
        trivial
      exact (Subgroup.mem_center_iff.mp hx y).symm
    have hD_X : IsXInvariantSubgroup X D := by
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨c, hc, rfl⟩
        refine ⟨x • c, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp inferInstance
            (MulDistribMulAction.toMulAut X C x)) hc
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    obtain ⟨s, hs, hD_power⟩ := hApowers D hD_le_A hD_X
    have hL2_nontrivial : Nontrivial (LowerCentralFactor C 1) := by
      have hH1_ne : higmanLowerCentralSeries C 1 ≠ ⊥ := by
        intro hH1
        apply hD_ne
        apply le_antisymm
        · rintro x ⟨c, hc, rfl⟩
          have hc' : c ∈ higmanLowerCentralSeries C 1 := by
            rw [hC_L1]
            exact hc
          rw [hH1] at hc'
          simpa using hc'
        · exact bot_le
      have hnext_lt :
          higmanLowerCentralSeries C 2 < higmanLowerCentralSeries C 1 := by
        refine lt_of_le_of_ne
          ((⊤ : Subgroup C).lowerCentralSeries_antitone (by omega)) ?_
        intro heq
        have hle : ∀ i : ℕ,
            higmanLowerCentralSeries C 1 ≤ higmanLowerCentralSeries C i := by
          intro i
          induction i with
          | zero => simp
          | succ i ih =>
              change higmanLowerCentralSeries C 1 ≤
                ⁅higmanLowerCentralSeries C i, (⊤ : Subgroup C)⁆
              calc
                higmanLowerCentralSeries C 1 =
                    higmanLowerCentralSeries C 2 := heq.symm
                _ = ⁅higmanLowerCentralSeries C 1,
                    (⊤ : Subgroup C)⁆ := by rfl
                _ ≤ ⁅higmanLowerCentralSeries C i, (⊤ : Subgroup C)⁆ :=
                  Subgroup.commutator_mono ih le_rfl
        have hnil : Group.IsNilpotent C :=
          IsPGroup.isNilpotent hC_two
        obtain ⟨i, hi⟩ :=
          Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
        apply hH1_ne
        apply bot_unique
        rw [← hi]
        exact hle i
      let H1 := higmanLowerCentralSeries C 1
      let H2 : Subgroup H1 :=
        (higmanLowerCentralSeries C 2).subgroupOf
          (higmanLowerCentralSeries C 1)
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let : Fact (IsPGroup 2 H1) :=
        ⟨hC_two.to_subgroup (higmanLowerCentralSeries C 1)⟩
      have hsquares_le_phi : squaresSubgroup H1 ≤ frattini H1 := by
        rw [squaresSubgroup, Subgroup.closure_le]
        rintro _ ⟨z, rfl⟩
        rw [frattini_eq_closure_commutator_union_powers
          (R := H1) (p := 2)]
        exact Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
      have hkernel_ne_top : lowerCentralFactorKernel C 1 ≠ ⊤ := by
        intro hkernel
        have hphi_sup : frattini H1 ⊔ H2 = ⊤ := by
          apply top_unique
          rw [← hkernel]
          change squaresSubgroup H1 ⊔ H2 ≤ frattini H1 ⊔ H2
          exact sup_le_sup hsquares_le_phi le_rfl
        have hH2_top : H2 = ⊤ :=
          frattini_nongenerating (by simpa [sup_comm] using hphi_sup)
        have hreverse :
            higmanLowerCentralSeries C 1 ≤ higmanLowerCentralSeries C 2 := by
          intro z hz
          have hzTop : (⟨z, hz⟩ : H1) ∈ (⊤ : Subgroup H1) := trivial
          rw [← hH2_top] at hzTop
          exact hzTop
        exact (not_le_of_gt hnext_lt) hreverse
      have hkernel_lt : lowerCentralFactorKernel C 1 < ⊤ :=
        lt_top_iff_ne_top.mpr hkernel_ne_top
      obtain ⟨z, _hzTop, hzker⟩ := SetLike.exists_of_lt hkernel_lt
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply hzker
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    have hpower_map :
        ∃ f : Additive AQ →ₗ[ZMod 2]
            Additive (LowerCentralFactor C 1),
          Function.Surjective f ∧
            ∀ v : Additive AQ,
              f (Txi v) = lowerCentralFactorLinearAut xi 1 (f v) := by
      have hpow_mem (a : A) :
          (⟨(a : P) ^ (2 ^ s), _hAC.le (A.pow_mem a.property (2 ^ s))⟩ : C) ∈
            higmanLowerCentralSeries C 1 := by
        have hpD : (a : P) ^ (2 ^ s) ∈ D := by
          rw [hD_power]
          exact Subgroup.subset_closure ⟨a, rfl⟩
        rcases hpD with ⟨c, hc, hcval⟩
        have hceq :
            (⟨(a : P) ^ (2 ^ s),
              _hAC.le (A.pow_mem a.property (2 ^ s))⟩ : C) = c := by
          apply Subtype.ext
          exact hcval.symm
        rw [hceq, hC_L1]
        exact hc
      let powerToH1 : A →* higmanLowerCentralSeries C 1 :=
        { toFun := fun a =>
            ⟨⟨(a : P) ^ (2 ^ s),
                _hAC.le (A.pow_mem a.property (2 ^ s))⟩,
              hpow_mem a⟩
          map_one' := by
            apply Subtype.ext
            apply Subtype.ext
            simp
          map_mul' := by
            intro a b
            apply Subtype.ext
            apply Subtype.ext
            change ((a * b : A) : P) ^ (2 ^ s) =
              (a : P) ^ (2 ^ s) * (b : P) ^ (2 ^ s)
            exact congrArg Subtype.val
              (map_mul (powMonoidHom (2 ^ s) : A →* A) a b) }
      let powerQ : A →* LowerCentralFactor C 1 :=
        (QuotientGroup.mk' (lowerCentralFactorKernel C 1)).comp powerToH1
      have hAsq_ker : Asq ≤ powerQ.ker := by
        rintro a ⟨b, rfl⟩
        rw [MonoidHom.mem_ker]
        change
          QuotientGroup.mk' (lowerCentralFactorKernel C 1)
            (powerToH1 (b ^ 2)) = 1
        rw [map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact (le_sup_left :
          squaresSubgroup (higmanLowerCentralSeries C 1) ≤
            lowerCentralFactorKernel C 1)
          (Subgroup.subset_closure ⟨powerToH1 b, rfl⟩)
      let powerMul : AQ →* LowerCentralFactor C 1 :=
        QuotientGroup.lift Asq powerQ
          (fun a ha => MonoidHom.mem_ker.mp (hAsq_ker ha))
      let powerMap : Additive AQ →ₗ[ZMod 2]
          Additive (LowerCentralFactor C 1) :=
        { powerMul.toAdditive with
          map_smul' := fun c v => ZMod.map_smul
            powerMul.toAdditive c v }
      have hclosure :
          Subgroup.closure
              {x : P | ∃ a : A, (a : P) ^ (2 ^ s) = x} =
            (powMonoidHom (2 ^ s) : A →* A).range.map A.subtype := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro x ⟨a, rfl⟩
          exact Subgroup.mem_map.mpr
            ⟨a ^ (2 ^ s), MonoidHom.mem_range.mpr
              ⟨a, by simp [powMonoidHom]⟩, rfl⟩
        · rintro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
          exact Subgroup.subset_closure ⟨a, by simp [powMonoidHom]⟩
      have hpowerToH1_surj : Function.Surjective powerToH1 := by
        intro z
        have hzD : (((z : higmanLowerCentralSeries C 1) : C) : P) ∈ D := by
          refine ⟨(z : C), ?_, rfl⟩
          exact hC_L1.le z.property
        have hzrange :
            (((z : higmanLowerCentralSeries C 1) : C) : P) ∈
              (powMonoidHom (2 ^ s) : A →* A).range.map A.subtype := by
          rw [← hclosure, ← hD_power]
          exact hzD
        rcases Subgroup.mem_map.mp hzrange with ⟨y, hy, hyz⟩
        rcases MonoidHom.mem_range.mp hy with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change (a : P) ^ (2 ^ s) = (z : P)
        calc
          (a : P) ^ (2 ^ s) = (y : P) := by
            simpa [powMonoidHom] using congrArg Subtype.val ha
          _ = (z : P) := hyz
      have hpower_surj : Function.Surjective powerMap := by
        intro y
        obtain ⟨z, hz⟩ :=
          QuotientGroup.mk'_surjective
            (lowerCentralFactorKernel C 1) y.toMul
        obtain ⟨a, ha⟩ := hpowerToH1_surj z
        refine ⟨Additive.ofMul (a : AQ), ?_⟩
        apply Additive.toMul.injective
        change powerMul (a : AQ) = y.toMul
        rw [← hz]
        change QuotientGroup.mk' (lowerCentralFactorKernel C 1)
          (powerToH1 a) =
            QuotientGroup.mk' (lowerCentralFactorKernel C 1) z
        rw [ha]
      have hpower_tau_equivariant :
          ∀ v : Additive AQ,
            powerMap (Ttau v) =
              lowerCentralFactorLinearAut tau 1 (powerMap v) := by
        intro v
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Asq v.toMul
        have hv : v = Additive.ofMul (a : AQ) := by
          apply Additive.toMul.injective
          exact ha.symm
        rw [hv]
        have hT :
            Ttau (Additive.ofMul (a : AQ)) =
              Additive.ofMul (g • (a : AQ)) := by
          simpa only [pow_one] using hTtau_pow 1 (a : AQ)
        rw [hT]
        change
          Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel C 1)
                (powerToH1 (g • a))) =
            lowerCentralFactorLinearAut tau 1
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel C 1)
                  (powerToH1 a)))
        rw [lowerCentralFactorLinearAut_ofMul_mk]
        apply congrArg Additive.ofMul
        apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel C 1))
        apply Subtype.ext
        apply Subtype.ext
        change (g • (a : P)) ^ (2 ^ s) = g • ((a : P) ^ (2 ^ s))
        exact (smul_pow' g (a : P) (2 ^ s)).symm
      have hpower_pow_equivariant :
          ∀ j : ℕ, ∀ v : Additive AQ,
            powerMap ((Ttau ^ j) v) =
              (lowerCentralFactorLinearAut tau 1 ^ j) (powerMap v) := by
        intro j
        induction j with
        | zero =>
            intro v
            simp
        | succ j ih =>
            intro v
            rw [pow_succ', LinearEquiv.mul_apply, hpower_tau_equivariant,
              ih, pow_succ', LinearEquiv.mul_apply]
      refine ⟨powerMap, hpower_surj, ?_⟩
      intro v
      rw [hTxi_pow, hpower_pow_equivariant, ← lowerCentralFactorLinearAut_pow]
    obtain ⟨powerMap, hpower_surj, hpower_equivariant⟩ := hpower_map
    have hpower_inj : Function.Injective powerMap := by
      have hpower_pow :
          ∀ j : ℕ, ∀ v : Additive AQ,
            powerMap ((Txi ^ j) v) =
              (lowerCentralFactorLinearAut xi 1 ^ j) (powerMap v) := by
        intro j
        induction j with
        | zero =>
            intro v
            simp
        | succ j ih =>
            intro v
            rw [pow_succ', LinearEquiv.mul_apply, hpower_equivariant,
              ih, pow_succ', LinearEquiv.mul_apply]
      intro x y hxy
      apply sub_eq_zero.mp
      by_contra hd
      have hker : powerMap (x - y) = 0 := by
        rw [map_sub, hxy]
        simp
      let : Nontrivial (Additive (LowerCentralFactor C 1)) := inferInstance
      obtain ⟨w, hw⟩ :=
        exists_ne (0 : Additive (LowerCentralFactor C 1))
      obtain ⟨v, hv⟩ := hpower_surj w
      have hv_ne : v ≠ 0 := by
        intro hv0
        apply hw
        rw [← hv, hv0, map_zero]
      obtain ⟨j, hj⟩ := hAQ_transitive (x - y) hd v hv_ne
      apply hw
      calc
        w = powerMap v := hv.symm
        _ = powerMap ((Txi ^ j) (x - y)) := by rw [hj]
        _ = (lowerCentralFactorLinearAut xi 1 ^ j)
            (powerMap (x - y)) := hpower_pow j (x - y)
        _ = 0 := by rw [hker]; simp
    let powerEquiv :
        Additive AQ ≃ₗ[ZMod 2] Additive (LowerCentralFactor C 1) :=
      LinearEquiv.ofBijective powerMap ⟨hpower_inj, hpower_surj⟩
    have hpowerEquiv_equivariant :
        ∀ v : Additive AQ,
          powerEquiv (Txi v) =
            lowerCentralFactorLinearAut xi 1 (powerEquiv v) := by
      intro v
      exact hpower_equivariant v
    exact ⟨powerEquiv, hpowerEquiv_equivariant⟩

  obtain ⟨qL2, hqL2⟩ := hL2_equiv
  have hL2_transitive :
      ∀ x : Additive (LowerCentralFactor C 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor C 1), y ≠ 0 →
          ∃ j : ℕ, (lowerCentralFactorLinearAut xi 1 ^ j) x = y := by
    have hqL2_pow :
        ∀ j : ℕ, ∀ v : Additive AQ,
          qL2 ((Txi ^ j) v) =
            (lowerCentralFactorLinearAut xi 1 ^ j) (qL2 v) := by
      intro j
      induction j with
      | zero =>
          intro v
          simp
      | succ j ih =>
          intro v
          rw [pow_succ', LinearEquiv.mul_apply, hqL2,
            ih, pow_succ', LinearEquiv.mul_apply]
    intro x hx y hy
    let x0 : Additive AQ := qL2.symm x
    let y0 : Additive AQ := qL2.symm y
    have hx0 : x0 ≠ 0 := by
      intro hx0
      apply hx
      calc
        x = qL2 x0 := by simp [x0]
        _ = 0 := by rw [hx0, map_zero]
    have hy0 : y0 ≠ 0 := by
      intro hy0
      apply hy
      calc
        y = qL2 y0 := by simp [y0]
        _ = 0 := by rw [hy0, map_zero]
    obtain ⟨j, hj⟩ := hAQ_transitive x0 hx0 y0 hy0
    refine ⟨j, ?_⟩
    calc
      (lowerCentralFactorLinearAut xi 1 ^ j) x =
          (lowerCentralFactorLinearAut xi 1 ^ j) (qL2 x0) := by
            simp [x0]
      _ = qL2 ((Txi ^ j) x0) := (hqL2_pow j x0).symm
      _ = qL2 y0 := by rw [hj]
      _ = y := by simp [y0]
  have hL2_card :
      Nat.card (LowerCentralFactor C 1) = 2 ^ r := by
    rw [← hAQ_card]
    exact Nat.card_congr qL2.toEquiv.symm
  have hL2_L3_equiv :
      ∃ q : Additive (LowerCentralFactor C 1) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor C 2),
        ∀ v : Additive (LowerCentralFactor C 1),
          q (lowerCentralFactorLinearAut xi 1 v) =
            lowerCentralFactorLinearAut xi 2 (q v) := by
    have hsq0 :
        squaresSubgroup (higmanLowerCentralSeries C 0) ≤
          (higmanLowerCentralSeries C 1).subgroupOf
            (higmanLowerCentralSeries C 0) := by
      rw [squaresSubgroup, Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      change (x : C) ^ 2 ∈ higmanLowerCentralSeries C 1
      exact hC_square (Subgroup.subset_closure ⟨(x : C), rfl⟩)
    have hsq1 :
        squaresSubgroup (higmanLowerCentralSeries C 1) ≤
          (higmanLowerCentralSeries C 2).subgroupOf
            (higmanLowerCentralSeries C 1) := by
      simpa using
        BenderSuzuki.External.Higman.lemma6_squares_lowerCentralSeries_succ
          (H := C) 0 hsq0
    let D : Subgroup P := (higmanLowerCentralSeries C 2).map C.subtype
    have hD_le_A : D ≤ A := by
      rintro _ ⟨c, hc, rfl⟩
      have hc1 : (c : C) ∈ higmanLowerCentralSeries C 1 :=
        (⊤ : Subgroup C).lowerCentralSeries_antitone
          (by omega : 1 ≤ 2) hc
      rw [hC_L1] at hc1
      rw [← _hcomm]
      exact ⟨c, hc1, rfl⟩
    have hD_ne : D ≠ ⊥ := by
      intro hD
      apply hA_exponent
      intro a
      have haComm : (a : P) ∈ (commutator C).map C.subtype := by
        rw [_hcomm]
        exact a.property
      rcases haComm with ⟨c, hc, hca⟩
      let c1 : higmanLowerCentralSeries C 1 :=
        ⟨c, by rw [hC_L1]; exact hc⟩
      have hcSq : c1 ^ 2 ∈
          (higmanLowerCentralSeries C 2).subgroupOf
            (higmanLowerCentralSeries C 1) :=
        hsq1 (Subgroup.subset_closure ⟨c1, rfl⟩)
      have hcSqD : ((c : C) : P) ^ 2 ∈ D := by
        refine ⟨(c : C) ^ 2, ?_, rfl⟩
        exact hcSq
      rw [hD] at hcSqD
      have hcSqOne : ((c : C) : P) ^ 2 = 1 := by
        simpa using hcSqD
      apply Subtype.ext
      change (a : P) ^ 2 = 1
      calc
        (a : P) ^ 2 = ((c : C) : P) ^ 2 :=
          congrArg (fun z : P => z ^ 2) hca.symm
        _ = 1 := hcSqOne
    have hD_X : IsXInvariantSubgroup X D := by
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨c, hc, rfl⟩
        refine ⟨x • c, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp inferInstance
            (MulDistribMulAction.toMulAut X C x)) hc
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hTxi_pow : Txi = Ttau ^ (2 ^ k) := rfl
    have hTtau_pow :
        ∀ j : ℕ, ∀ q : AQ,
          (Ttau ^ j) (Additive.ofMul q) =
            Additive.ofMul ((g ^ j) • q) := by
      intro j
      induction j with
      | zero =>
          intro q
          simp
      | succ j ih =>
          intro q
          rw [pow_succ', LinearEquiv.mul_apply, ih]
          apply Additive.toMul.injective
          simp [Ttau, MulDistribMulAction.toMulAut_apply, pow_succ', smul_smul]
    have hAQ_L3_equiv :
        ∃ q : Additive AQ ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor C 2),
          ∀ v : Additive AQ,
            q (Txi v) =
              lowerCentralFactorLinearAut xi 2 (q v) := by
      obtain ⟨s, hs, hD_power⟩ := hApowers D hD_le_A hD_X
      have hL3_nontrivial : Nontrivial (LowerCentralFactor C 2) := by
        have hH1_ne : higmanLowerCentralSeries C 2 ≠ ⊥ := by
          intro hH1
          apply hD_ne
          apply le_antisymm
          · rintro x ⟨c, hc, rfl⟩
            have hc' : c ∈ higmanLowerCentralSeries C 2 := by
              exact hc
            rw [hH1] at hc'
            simpa using hc'
          · exact bot_le
        have hnext_lt :
            higmanLowerCentralSeries C 3 < higmanLowerCentralSeries C 2 := by
          refine lt_of_le_of_ne
            ((⊤ : Subgroup C).lowerCentralSeries_antitone (by omega)) ?_
          intro heq
          have hle : ∀ i : ℕ,
              higmanLowerCentralSeries C 2 ≤ higmanLowerCentralSeries C i := by
            intro i
            induction i with
            | zero => simp
            | succ i ih =>
                change higmanLowerCentralSeries C 2 ≤
                  ⁅higmanLowerCentralSeries C i, (⊤ : Subgroup C)⁆
                calc
                  higmanLowerCentralSeries C 2 =
                      higmanLowerCentralSeries C 3 := heq.symm
                  _ = ⁅higmanLowerCentralSeries C 2,
                      (⊤ : Subgroup C)⁆ := by rfl
                  _ ≤ ⁅higmanLowerCentralSeries C i,
                      (⊤ : Subgroup C)⁆ :=
                    Subgroup.commutator_mono ih le_rfl
          have hnil : Group.IsNilpotent C :=
            IsPGroup.isNilpotent hC_two
          obtain ⟨i, hi⟩ :=
            Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
          apply hH1_ne
          apply bot_unique
          rw [← hi]
          exact hle i
        let H1 := higmanLowerCentralSeries C 2
        let H2 : Subgroup H1 :=
          (higmanLowerCentralSeries C 3).subgroupOf
            (higmanLowerCentralSeries C 2)
        let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        let : Fact (IsPGroup 2 H1) :=
          ⟨hC_two.to_subgroup (higmanLowerCentralSeries C 2)⟩
        have hsquares_le_phi : squaresSubgroup H1 ≤ frattini H1 := by
          rw [squaresSubgroup, Subgroup.closure_le]
          rintro _ ⟨z, rfl⟩
          rw [frattini_eq_closure_commutator_union_powers
            (R := H1) (p := 2)]
          exact Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
        have hkernel_ne_top : lowerCentralFactorKernel C 2 ≠ ⊤ := by
          intro hkernel
          have hphi_sup : frattini H1 ⊔ H2 = ⊤ := by
            apply top_unique
            rw [← hkernel]
            change squaresSubgroup H1 ⊔ H2 ≤ frattini H1 ⊔ H2
            exact sup_le_sup hsquares_le_phi le_rfl
          have hH2_top : H2 = ⊤ :=
            frattini_nongenerating (by simpa [sup_comm] using hphi_sup)
          have hreverse :
              higmanLowerCentralSeries C 2 ≤
                higmanLowerCentralSeries C 3 := by
            intro z hz
            have hzTop : (⟨z, hz⟩ : H1) ∈ (⊤ : Subgroup H1) := trivial
            rw [← hH2_top] at hzTop
            exact hzTop
          exact (not_le_of_gt hnext_lt) hreverse
        have hkernel_lt : lowerCentralFactorKernel C 2 < ⊤ :=
          lt_top_iff_ne_top.mpr hkernel_ne_top
        obtain ⟨z, _hzTop, hzker⟩ := SetLike.exists_of_lt hkernel_lt
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        apply hzker
        rw [← QuotientGroup.eq_one_iff]
        exact Subsingleton.elim _ _
      have hpower_map :
          ∃ f : Additive AQ →ₗ[ZMod 2]
              Additive (LowerCentralFactor C 2),
            Function.Surjective f ∧
              ∀ v : Additive AQ,
                f (Txi v) = lowerCentralFactorLinearAut xi 2 (f v) := by
        have hpow_mem (a : A) :
            (⟨(a : P) ^ (2 ^ s), _hAC.le (A.pow_mem a.property (2 ^ s))⟩ : C) ∈
              higmanLowerCentralSeries C 2 := by
          have hpD : (a : P) ^ (2 ^ s) ∈ D := by
            rw [hD_power]
            exact Subgroup.subset_closure ⟨a, rfl⟩
          rcases hpD with ⟨c, hc, hcval⟩
          have hceq :
              (⟨(a : P) ^ (2 ^ s),
                _hAC.le (A.pow_mem a.property (2 ^ s))⟩ : C) = c := by
            apply Subtype.ext
            exact hcval.symm
          rw [hceq]
          exact hc
        let powerToH1 : A →* higmanLowerCentralSeries C 2 :=
          { toFun := fun a =>
              ⟨⟨(a : P) ^ (2 ^ s),
                  _hAC.le (A.pow_mem a.property (2 ^ s))⟩,
                hpow_mem a⟩
            map_one' := by
              apply Subtype.ext
              apply Subtype.ext
              simp
            map_mul' := by
              intro a b
              apply Subtype.ext
              apply Subtype.ext
              change ((a * b : A) : P) ^ (2 ^ s) =
                (a : P) ^ (2 ^ s) * (b : P) ^ (2 ^ s)
              exact congrArg Subtype.val
                (map_mul (powMonoidHom (2 ^ s) : A →* A) a b) }
        let powerQ : A →* LowerCentralFactor C 2 :=
          (QuotientGroup.mk' (lowerCentralFactorKernel C 2)).comp powerToH1
        have hAsq_ker : Asq ≤ powerQ.ker := by
          rintro a ⟨b, rfl⟩
          rw [MonoidHom.mem_ker]
          change
            QuotientGroup.mk' (lowerCentralFactorKernel C 2)
              (powerToH1 (b ^ 2)) = 1
          rw [map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact (le_sup_left :
            squaresSubgroup (higmanLowerCentralSeries C 2) ≤
              lowerCentralFactorKernel C 2)
            (Subgroup.subset_closure ⟨powerToH1 b, rfl⟩)
        let powerMul : AQ →* LowerCentralFactor C 2 :=
          QuotientGroup.lift Asq powerQ
            (fun a ha => MonoidHom.mem_ker.mp (hAsq_ker ha))
        let powerMap : Additive AQ →ₗ[ZMod 2]
            Additive (LowerCentralFactor C 2) :=
          { powerMul.toAdditive with
            map_smul' := fun c v => ZMod.map_smul
              powerMul.toAdditive c v }
        have hclosure :
            Subgroup.closure
                {x : P | ∃ a : A, (a : P) ^ (2 ^ s) = x} =
              (powMonoidHom (2 ^ s) : A →* A).range.map A.subtype := by
          apply le_antisymm
          · rw [Subgroup.closure_le]
            rintro x ⟨a, rfl⟩
            exact Subgroup.mem_map.mpr
              ⟨a ^ (2 ^ s), MonoidHom.mem_range.mpr
                ⟨a, by simp [powMonoidHom]⟩, rfl⟩
          · rintro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
            exact Subgroup.subset_closure ⟨a, by simp [powMonoidHom]⟩
        have hpowerToH1_surj : Function.Surjective powerToH1 := by
          intro z
          have hzD :
              (((z : higmanLowerCentralSeries C 2) : C) : P) ∈ D := by
            refine ⟨(z : C), ?_, rfl⟩
            exact z.property
          have hzrange :
              (((z : higmanLowerCentralSeries C 2) : C) : P) ∈
                (powMonoidHom (2 ^ s) : A →* A).range.map A.subtype := by
            rw [← hclosure, ← hD_power]
            exact hzD
          rcases Subgroup.mem_map.mp hzrange with ⟨y, hy, hyz⟩
          rcases MonoidHom.mem_range.mp hy with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          apply Subtype.ext
          apply Subtype.ext
          change (a : P) ^ (2 ^ s) = (z : P)
          calc
            (a : P) ^ (2 ^ s) = (y : P) := by
              simpa [powMonoidHom] using congrArg Subtype.val ha
            _ = (z : P) := hyz
        have hpower_surj : Function.Surjective powerMap := by
          intro y
          obtain ⟨z, hz⟩ :=
            QuotientGroup.mk'_surjective
              (lowerCentralFactorKernel C 2) y.toMul
          obtain ⟨a, ha⟩ := hpowerToH1_surj z
          refine ⟨Additive.ofMul (a : AQ), ?_⟩
          apply Additive.toMul.injective
          change powerMul (a : AQ) = y.toMul
          rw [← hz]
          change QuotientGroup.mk' (lowerCentralFactorKernel C 2)
            (powerToH1 a) =
              QuotientGroup.mk' (lowerCentralFactorKernel C 2) z
          rw [ha]
        have hpower_tau_equivariant :
            ∀ v : Additive AQ,
              powerMap (Ttau v) =
                lowerCentralFactorLinearAut tau 2 (powerMap v) := by
          intro v
          obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Asq v.toMul
          have hv : v = Additive.ofMul (a : AQ) := by
            apply Additive.toMul.injective
            exact ha.symm
          rw [hv]
          have hT :
              Ttau (Additive.ofMul (a : AQ)) =
              Additive.ofMul (g • (a : AQ)) := by
            simpa only [pow_one] using hTtau_pow 1 (a : AQ)
          rw [hT]
          change
            Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel C 2)
                  (powerToH1 (g • a))) =
              lowerCentralFactorLinearAut tau 2
                (Additive.ofMul
                  (QuotientGroup.mk' (lowerCentralFactorKernel C 2)
                    (powerToH1 a)))
          rw [lowerCentralFactorLinearAut_ofMul_mk]
          apply congrArg Additive.ofMul
          apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel C 2))
          apply Subtype.ext
          apply Subtype.ext
          change (g • (a : P)) ^ (2 ^ s) = g • ((a : P) ^ (2 ^ s))
          exact (smul_pow' g (a : P) (2 ^ s)).symm
        have hpower_pow_equivariant :
            ∀ j : ℕ, ∀ v : Additive AQ,
              powerMap ((Ttau ^ j) v) =
                (lowerCentralFactorLinearAut tau 2 ^ j) (powerMap v) := by
          intro j
          induction j with
          | zero =>
              intro v
              simp
          | succ j ih =>
              intro v
              rw [pow_succ', LinearEquiv.mul_apply, hpower_tau_equivariant,
                ih, pow_succ', LinearEquiv.mul_apply]
        refine ⟨powerMap, hpower_surj, ?_⟩
        intro v
        rw [hTxi_pow, hpower_pow_equivariant, ← lowerCentralFactorLinearAut_pow]
      obtain ⟨powerMap, hpower_surj, hpower_equivariant⟩ := hpower_map
      have hpower_inj : Function.Injective powerMap := by
        have hpower_pow :
            ∀ j : ℕ, ∀ v : Additive AQ,
              powerMap ((Txi ^ j) v) =
                (lowerCentralFactorLinearAut xi 2 ^ j) (powerMap v) := by
          intro j
          induction j with
          | zero =>
              intro v
              simp
          | succ j ih =>
              intro v
              rw [pow_succ', LinearEquiv.mul_apply, hpower_equivariant,
                ih, pow_succ', LinearEquiv.mul_apply]
        intro x y hxy
        apply sub_eq_zero.mp
        by_contra hd
        have hker : powerMap (x - y) = 0 := by
          rw [map_sub, hxy]
          simp
        let : Nontrivial (Additive (LowerCentralFactor C 2)) := inferInstance
        obtain ⟨w, hw⟩ :=
          exists_ne (0 : Additive (LowerCentralFactor C 2))
        obtain ⟨v, hv⟩ := hpower_surj w
        have hv_ne : v ≠ 0 := by
          intro hv0
          apply hw
          rw [← hv, hv0, map_zero]
        obtain ⟨j, hj⟩ := hAQ_transitive (x - y) hd v hv_ne
        apply hw
        calc
          w = powerMap v := hv.symm
          _ = powerMap ((Txi ^ j) (x - y)) := by rw [hj]
          _ = (lowerCentralFactorLinearAut xi 2 ^ j)
              (powerMap (x - y)) := hpower_pow j (x - y)
          _ = 0 := by rw [hker]; simp
      let powerEquiv :
          Additive AQ ≃ₗ[ZMod 2] Additive (LowerCentralFactor C 2) :=
        LinearEquiv.ofBijective powerMap ⟨hpower_inj, hpower_surj⟩
      have hpowerEquiv_equivariant :
          ∀ v : Additive AQ,
            powerEquiv (Txi v) =
              lowerCentralFactorLinearAut xi 2 (powerEquiv v) := by
        intro v
        exact hpower_equivariant v
      exact ⟨powerEquiv, hpowerEquiv_equivariant⟩
    obtain ⟨qAQ_L3, hqAQ_L3⟩ := hAQ_L3_equiv
    let q : Additive (LowerCentralFactor C 1) ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor C 2) :=
      qL2.symm.trans qAQ_L3
    refine ⟨q, ?_⟩
    intro v
    have hqL2_symm :
        qL2.symm (lowerCentralFactorLinearAut xi 1 v) =
          Txi (qL2.symm v) := by
      simpa using congrArg qL2.symm (hqL2 (qL2.symm v)).symm
    rw [show q (lowerCentralFactorLinearAut xi 1 v) =
        qAQ_L3 (qL2.symm (lowerCentralFactorLinearAut xi 1 v)) by rfl,
      hqL2_symm, hqAQ_L3]
    rfl
  obtain ⟨qL3, hqL3⟩ := hL2_L3_equiv
  have hL3_L2_equiv :
      ∃ q : Additive (LowerCentralFactor C 2) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor C 1),
        ∀ v : Additive (LowerCentralFactor C 2),
          q (lowerCentralFactorLinearAut xi 2 v) =
            lowerCentralFactorLinearAut xi 1 (q v) := by
    refine ⟨qL3.symm, ?_⟩
    intro v
    simpa using congrArg qL3.symm (hqL3 (qL3.symm v)).symm
  exact (lemma6_third_factor_nonisomorphic
    hC_two hC_nonabelian xi hxi_odd hL1_irreducible hL2_transitive
      r hr hL2_card hC_square) hL3_L2_equiv
end Higman
end External
end CFSG.BenderSuzuki
