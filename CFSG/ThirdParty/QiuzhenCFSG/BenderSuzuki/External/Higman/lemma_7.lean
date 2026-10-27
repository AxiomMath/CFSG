module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import Mathlib.LinearAlgebra.FixedSubmodule

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 7
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped commutatorElement
open scoped IsMulCommutative

universe u

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Higman Lemma 7: if a normal `X`-invariant cover has Frattini subgroup below
`A` and commutator subgroup properly below `A`, then the cover is abelian. -/
public theorem lemma7_cover_commutator_case_abelian
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
    (_hfrattini : A = (frattini C).map C.subtype)
    (_hcomm : (commutator C).map C.subtype ≤
      Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x}) :
    IsMulCommutative C := by
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
  by_contra hC_nonabelian
  have hC_two : IsPGroup 2 C :=
    (isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup C
  let : Fact (IsPGroup 2 C) := ⟨hC_two⟩
  let : IsInvariant X P C := ⟨_hC_X⟩
  let : IsCyclic X := _hXcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  let tau : MulAut C := MulDistribMulAction.toMulAut X C g
  obtain ⟨k, m, hm_odd, htau_order⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos tau).ne'
  let xi : MulAut C := tau ^ (2 ^ k)
  have hxi_data : Odd (orderOf xi) := by
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
  have hxi_odd := hxi_data
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
        obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
        have hC_le : ∀ i : ℕ, C ≤ higmanLowerCentralSeries P i := by
          intro i
          induction i with
          | zero => simp [higmanLowerCentralSeries]
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
          rw [Subgroup.map_sup, ← _hfrattini, hKcmap, htopmap]
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
              (higmanLowerCentralSeries C 0).subtype = higmanLowerCentralSeries C 1 :=
          Subgroup.map_subgroupOf_eq_of_le
            ((⊤ : Subgroup C).lowerCentralSeries_antitone (by omega : 0 ≤ 1))
        rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map, hnext_map]
        change squaresSubgroup C ⊔ commutator C = frattini C
        rw [frattini_eq_closure_commutator_union_powers (R := C) (p := 2)]
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
        rw [_hfrattini] at ha
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
        simpa [commutatorElement_def] using hprod
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
          rw [_hfrattini] at hcA
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
          ext v
          simp [hU_refl]
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
  have hA_ne : A ≠ ⊥ := by
    intro hA
    have hpow_bot :
        Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} = ⊥ := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x ⟨a, rfl⟩
        have ha : a = 1 := by
          apply Subtype.ext
          simpa [hA] using a.property
        subst a
        simp
      · exact bot_le
    have hcomm_map_bot : (commutator C).map C.subtype = ⊥ := by
      apply bot_unique
      rw [← hpow_bot]
      exact _hcomm
    have hcomm_bot : commutator C = ⊥ := by
      apply Subgroup.map_injective C.subtype_injective
      simpa using hcomm_map_bot
    apply hC_nonabelian
    refine ⟨⟨?_⟩⟩
    intro x y
    have hcenter : Subgroup.center C = ⊤ := by
      rw [← commutator_eq_bot_iff_center_eq_top]
      exact hcomm_bot
    have hx : x ∈ Subgroup.center C := by
      rw [hcenter]
      trivial
    exact (Subgroup.mem_center_iff.mp hx y).symm
  obtain ⟨e, r, ⟨hAcoord⟩, hApowers⟩ :=
    lemma1_abelian_invariant_homocyclic
      _hP _hXtrans _hA_abelian _hA_X
  have he : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro he0
    subst e
    let : Subsingleton (ZMod (2 ^ 0)) :=
      ZMod.subsingleton_iff.mpr (by simp)
    apply hA_ne
    apply le_antisymm
    · intro a ha
      let aA : A := ⟨a, ha⟩
      have haA : aA = 1 := by
        apply hAcoord.injective
        apply Multiplicative.toAdd.injective
        ext i
        exact Subsingleton.elim _ _
      simpa [aA] using congrArg Subtype.val haA
    · exact bot_le
  let : IsInvariant X P A := ⟨_hA_X⟩
  let : IsMulCommutative A := _hA_abelian
  let Asq : Subgroup A := (powMonoidHom 2 : A →* A).range
  let AQ := A ⧸ Asq
  have hAQ_two : ∀ q : AQ, q ^ 2 = 1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro a
    change ((a ^ 2 : A) : AQ) = 1
    rw [QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨a, by simp [powMonoidHom]⟩
  let : Module (ZMod 2) (Additive AQ) :=
    AddCommGroup.zmodModule <| by
      intro q
      apply Additive.toMul.injective
      simp only [toMul_nsmul, toMul_zero]
      exact hAQ_two q.toMul
  have hAQ_card : Nat.card AQ = 2 ^ r := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
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
      lemma1_twoTorsion_card_of_homocyclic he hAcoord
    rw [hcard] at hle
    by_contra hr'
    have hrle : r ≤ 1 := by omega
    interval_cases r <;> norm_num at hle
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
      simpa [Asq, powMonoidHom, show e - (e - 1) = 1 by omega] using hz
    have hexp : 2 ^ (e - 1) * 2 = 2 ^ e := by
      rw [← pow_succ]
      congr 1
      omega
    have hpow_sq (c : A) : (c ^ (2 ^ (e - 1))) ^ 2 = 1 := by
      calc
        (c ^ (2 ^ (e - 1))) ^ 2 = c ^ (2 ^ (e - 1) * 2) := by
          rw [pow_mul]
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
      change (b : P) ^ (2 ^ (e - 1)) =
        ((z • a : A) : P) ^ (2 ^ (e - 1))
      rw [show ((z • a : A) : P) = z • (a : P) by rfl]
      simpa using hz
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
  have hAQ_transitive :
      ∀ x : Additive AQ, x ≠ 0 →
        ∀ y : Additive AQ, y ≠ 0 →
          ∃ j : ℕ, (Txi ^ j) x = y := by
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
  let D : Subgroup P := (commutator C).map C.subtype
  have hD_le_A : D ≤ A := by
    calc
      D ≤ Subgroup.closure
          {x : P | ∃ a : A, (a : P) ^ 2 = x} := _hcomm
      _ ≤ A := by
        rw [Subgroup.closure_le]
        rintro x ⟨a, rfl⟩
        exact A.pow_mem a.property 2
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
          change c ∈ commutator C
          exact hc
        rw [hH1] at hc'
        simpa using hc'
      · exact bot_le
    have hnext_lt : higmanLowerCentralSeries C 2 < higmanLowerCentralSeries C 1 := by
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
              higmanLowerCentralSeries C 1 = higmanLowerCentralSeries C 2 := heq.symm
              _ = ⁅higmanLowerCentralSeries C 1, (⊤ : Subgroup C)⁆ := by rfl
              _ ≤ ⁅higmanLowerCentralSeries C i, (⊤ : Subgroup C)⁆ :=
                Subgroup.commutator_mono ih le_rfl
      have hnil : Group.IsNilpotent C :=
        IsPGroup.isNilpotent hC_two
      obtain ⟨i, hi⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
      apply hH1_ne
      apply bot_unique
      rw [← hi]
      exact hle i
    let H1 := higmanLowerCentralSeries C 1
    let H2 : Subgroup H1 :=
      (higmanLowerCentralSeries C 2).subgroupOf (higmanLowerCentralSeries C 1)
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
      rw [hceq]
      change c ∈ commutator C
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
        change (z : C) ∈ commutator C
        exact z.property
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
  have hsquare_map :
      ∃ f : Additive (LowerCentralFactor C 0) →ₗ[ZMod 2] Additive AQ,
        Function.Surjective f ∧
          ∀ v : Additive (LowerCentralFactor C 0),
            f (lowerCentralFactorLinearAut xi 0 v) = Txi (f v) := by
    have hAsq_map :
        Asq.map A.subtype =
          Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} := by
      symm
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
    have hsquare_mem_A (c : C) : (c : P) ^ 2 ∈ A := by
      rw [_hfrattini]
      refine ⟨c ^ 2, ?_, rfl⟩
      rw [frattini_eq_closure_commutator_union_powers
        (R := C) (p := 2)]
      exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
    let squareA (c : C) : A := ⟨(c : P) ^ 2, hsquare_mem_A c⟩
    have hmul_diff_Asq (x y : C) :
        squareA (x * y) / (squareA x * squareA y) ∈ Asq := by
      let : IsMulCommutative (C ⧸ commutator C) :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 le_rfl
      have hdiff_comm :
          (x * y) ^ 2 / (x ^ 2 * y ^ 2) ∈ commutator C := by
        apply (QuotientGroup.eq_iff_div_mem
          (N := commutator C)).1
        simp [mul_pow]
      have hdiffD :
          (((x * y) ^ 2 / (x ^ 2 * y ^ 2) : C) : P) ∈ D :=
        ⟨(x * y) ^ 2 / (x ^ 2 * y ^ 2), hdiff_comm, rfl⟩
      have hdiffMap :
          (((x * y) ^ 2 / (x ^ 2 * y ^ 2) : C) : P) ∈
            Asq.map A.subtype := by
        rw [hAsq_map]
        exact _hcomm hdiffD
      rcases Subgroup.mem_map.mp hdiffMap with ⟨a, ha, haval⟩
      have heq :
          squareA (x * y) / (squareA x * squareA y) = a := by
        apply Subtype.ext
        exact haval.symm
      rw [heq]
      exact ha
    let squareQ0 : C →* AQ :=
      { toFun := fun c => (squareA c : AQ)
        map_one' := by
          have hsq_one : squareA (1 : C) = 1 := by
            apply Subtype.ext
            simp [squareA]
          rw [hsq_one]
          exact QuotientGroup.mk_one (G := A) (N := Asq)
        map_mul' := by
          intro x y
          apply (QuotientGroup.eq_iff_div_mem (N := Asq)).2
          exact hmul_diff_Asq x y }
    let squareTop : higmanLowerCentralSeries C 0 →* AQ :=
      squareQ0.comp Subgroup.topEquiv.toMonoidHom
    have hkernel_square :
        lowerCentralFactorKernel C 0 ≤ squareTop.ker := by
      rw [lowerCentralFactorKernel]
      apply sup_le
      · rw [squaresSubgroup, Subgroup.closure_le]
        rintro _ ⟨z, rfl⟩
        change squareTop (z ^ 2) = 1
        rw [map_pow]
        exact hAQ_two (squareTop z)
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hzcomm : (z : C) ∈ commutator C := by
          change (z : C) ∈ commutator C at hz
          exact hz
        have hzD : ((z : C) : P) ∈ D := ⟨z, hzcomm, rfl⟩
        let a : A := ⟨((z : C) : P), hD_le_A hzD⟩
        change ((squareA (z : C) : A) : AQ) = 1
        rw [QuotientGroup.eq_one_iff]
        refine MonoidHom.mem_range.mpr ⟨a, ?_⟩
        apply Subtype.ext
        rfl
    let squareMul : LowerCentralFactor C 0 →* AQ :=
      QuotientGroup.lift (lowerCentralFactorKernel C 0) squareTop
        (fun z hz => MonoidHom.mem_ker.mp (hkernel_square hz))
    let squareMap : Additive (LowerCentralFactor C 0) →ₗ[ZMod 2]
        Additive AQ :=
      { squareMul.toAdditive with
        map_smul' := fun c v => ZMod.map_smul squareMul.toAdditive c v }
    have hsquare_tau_equivariant :
        ∀ v : Additive (LowerCentralFactor C 0),
          squareMap (lowerCentralFactorLinearAut tau 0 v) =
            Ttau (squareMap v) := by
      intro v
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective
        (lowerCentralFactorKernel C 0) v.toMul
      have hv : v = Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel C 0) c) := by
        apply Additive.toMul.injective
        exact hc.symm
      rw [hv, lowerCentralFactorLinearAut_ofMul_mk]
      have hT :
          Ttau (Additive.ofMul ((squareA (c : C) : A) : AQ)) =
            Additive.ofMul (g • ((squareA (c : C) : A) : AQ)) := by
        simpa only [pow_one] using
          hTtau_pow 1 ((squareA (c : C) : A) : AQ)
      change
        Additive.ofMul
            ((squareA ((lowerCentralSeriesMulAut tau 0) c : C) : A) : AQ) =
          Ttau (Additive.ofMul ((squareA (c : C) : A) : AQ))
      rw [hT]
      have hsquare_smul :
          squareA ((lowerCentralSeriesMulAut tau 0) c : C) =
            g • squareA (c : C) := by
        apply Subtype.ext
        change (g • ((c : C) : P)) ^ 2 = g • (((c : C) : P) ^ 2)
        exact (smul_pow' g ((c : C) : P) 2).symm
      apply Additive.toMul.injective
      rw [hsquare_smul]
      exact (MulAction.Quotient.smul_coe
        (H := Asq) g (squareA (c : C))).symm
    have hsquare_pow_equivariant :
        ∀ j : ℕ, ∀ v : Additive (LowerCentralFactor C 0),
          squareMap ((lowerCentralFactorLinearAut tau 0 ^ j) v) =
            (Ttau ^ j) (squareMap v) := by
      intro j
      induction j with
      | zero =>
          intro v
          simp
      | succ j ih =>
          intro v
          rw [pow_succ', LinearEquiv.mul_apply, hsquare_tau_equivariant,
            ih, pow_succ', LinearEquiv.mul_apply]
    have hsquare_xi_equivariant :
        ∀ v : Additive (LowerCentralFactor C 0),
          squareMap (lowerCentralFactorLinearAut xi 0 v) =
            Txi (squareMap v) := by
      intro v
      rw [show xi = tau ^ 2 ^ k from rfl,
        lowerCentralFactorLinearAut_pow,
        show Txi = Ttau ^ 2 ^ k from rfl]
      exact hsquare_pow_equivariant (2 ^ k) v
    have hsquare_xi_pow_equivariant :
        ∀ j : ℕ, ∀ v : Additive (LowerCentralFactor C 0),
          squareMap ((lowerCentralFactorLinearAut xi 0 ^ j) v) =
            (Txi ^ j) (squareMap v) := by
      intro j
      induction j with
      | zero =>
          intro v
          simp
      | succ j ih =>
          intro v
          rw [pow_succ', LinearEquiv.mul_apply, hsquare_xi_equivariant,
            ih, pow_succ', LinearEquiv.mul_apply]
    have hsquare_ne : squareMap ≠ 0 := by
      intro hzero
      have hsquare_le (c : C) :
          ((c : C) : P) ^ 2 ∈ Asq.map A.subtype := by
        let c0 : higmanLowerCentralSeries C 0 := ⟨c, by simp⟩
        have hz :
            squareMap
                (Additive.ofMul
                  (QuotientGroup.mk' (lowerCentralFactorKernel C 0) c0)) =
              0 := by
          rw [hzero]
          rfl
        apply Additive.toMul.injective at hz
        change ((squareA c : A) : AQ) = 1 at hz
        have hcAsq : squareA c ∈ Asq :=
          (QuotientGroup.eq_one_iff (N := Asq) (squareA c)).1 hz
        exact ⟨squareA c, hcAsq, rfl⟩
      have hcomm_le :
          Subgroup.map C.subtype (commutator C) ≤ Asq.map A.subtype := by
        rw [hAsq_map]
        exact _hcomm
      have hPhi_le :
          frattini C ≤ (Asq.map A.subtype).comap C.subtype := by
        rw [frattini_eq_closure_commutator_union_powers
          (R := C) (p := 2), Subgroup.closure_le]
        intro z hz
        rcases hz with hz | ⟨c, rfl⟩
        · exact hcomm_le ⟨z, hz, rfl⟩
        · exact hsquare_le c
      have hA_le : A ≤ Asq.map A.subtype := by
        calc
          A = Subgroup.map C.subtype (frattini C) := _hfrattini
          _ ≤ Asq.map A.subtype :=
            (Subgroup.map_le_iff_le_comap).2 hPhi_le
      have hAsq_top : Asq = ⊤ := by
        apply top_unique
        intro a _ha
        have ha_map : (a : P) ∈ Asq.map A.subtype := hA_le a.property
        rcases ha_map with ⟨b, hb, hba⟩
        have hba' : b = a := A.subtype_injective hba
        simpa [hba'] using hb
      have hAQ_card_gt : 1 < Nat.card AQ := by
        rw [hAQ_card]
        exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
      let : Nontrivial AQ :=
        Finite.one_lt_card_iff_nontrivial.mp hAQ_card_gt
      obtain ⟨q, hq⟩ := exists_ne (1 : AQ)
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Asq q
      apply hq
      apply (QuotientGroup.eq_one_iff (N := Asq) a).2
      rw [hAsq_top]
      trivial
    have hsquare_surj : Function.Surjective squareMap := by
      have hex : ∃ v : Additive (LowerCentralFactor C 0),
          squareMap v ≠ 0 := by
        by_contra h
        push Not at h
        apply hsquare_ne
        ext v
        simpa using h v
      obtain ⟨v, hv⟩ := hex
      intro y
      by_cases hy : y = 0
      · refine ⟨0, ?_⟩
        simp [hy]
      · obtain ⟨j, hj⟩ := hAQ_transitive (squareMap v) hv y hy
        refine ⟨(lowerCentralFactorLinearAut xi 0 ^ j) v, ?_⟩
        exact (hsquare_xi_pow_equivariant j v).trans hj
    exact ⟨squareMap, hsquare_surj, hsquare_xi_equivariant⟩
  obtain ⟨squareMap, hsquare_surj, hsquare_equivariant⟩ := hsquare_map
  have hsquare_inj : Function.Injective squareMap := by
    have hker_invariant :
        ∀ v : Additive (LowerCentralFactor C 0),
          v ∈ squareMap.ker →
            lowerCentralFactorLinearAut xi 0 v ∈ squareMap.ker := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hsquare_equivariant, hv, map_zero]
    have hsquare_ne : squareMap ≠ 0 := by
      intro hzero
      have hAQ_card_gt : 1 < Nat.card AQ := by
        rw [hAQ_card]
        exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
      let : Nontrivial AQ :=
        Finite.one_lt_card_iff_nontrivial.mp hAQ_card_gt
      let : Nontrivial (Additive AQ) := inferInstance
      obtain ⟨y, hy⟩ := exists_ne (0 : Additive AQ)
      obtain ⟨v, hv⟩ := hsquare_surj y
      apply hy
      rw [← hv, hzero]
      rfl
    have hker_ne_top : squareMap.ker ≠ ⊤ := by
      intro htop
      apply hsquare_ne
      exact LinearMap.ker_eq_top.mp htop
    have hker_bot : squareMap.ker = ⊥ := by
      rcases hL1_irreducible squareMap.ker hker_invariant with hbot | htop
      · exact hbot
      · exact (hker_ne_top htop).elim
    exact LinearMap.ker_eq_bot.mp hker_bot
  let squareEquiv :
      Additive (LowerCentralFactor C 0) ≃ₗ[ZMod 2] Additive AQ :=
    LinearEquiv.ofBijective squareMap ⟨hsquare_inj, hsquare_surj⟩
  have hsquareEquiv_equivariant :
      ∀ v : Additive (LowerCentralFactor C 0),
        squareEquiv (lowerCentralFactorLinearAut xi 0 v) =
          Txi (squareEquiv v) := by
    intro v
    exact hsquare_equivariant v
  have hL2_transitive :
      ∀ x : Additive (LowerCentralFactor C 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor C 1), y ≠ 0 →
          ∃ j : ℕ, (lowerCentralFactorLinearAut xi 1 ^ j) x = y := by
    have hpowerEquiv_pow :
        ∀ j : ℕ, ∀ v : Additive AQ,
          powerEquiv ((Txi ^ j) v) =
            (lowerCentralFactorLinearAut xi 1 ^ j) (powerEquiv v) := by
      intro j
      induction j with
      | zero =>
          intro v
          simp
      | succ j ih =>
          intro v
          rw [pow_succ', LinearEquiv.mul_apply, hpowerEquiv_equivariant,
            ih, pow_succ', LinearEquiv.mul_apply]
    intro x hx y hy
    let x0 : Additive AQ := powerEquiv.symm x
    let y0 : Additive AQ := powerEquiv.symm y
    have hx0 : x0 ≠ 0 := by
      intro hx0
      apply hx
      calc
        x = powerEquiv x0 := by simp [x0]
        _ = 0 := by rw [hx0, map_zero]
    have hy0 : y0 ≠ 0 := by
      intro hy0
      apply hy
      calc
        y = powerEquiv y0 := by simp [y0]
        _ = 0 := by rw [hy0, map_zero]
    obtain ⟨j, hj⟩ := hAQ_transitive x0 hx0 y0 hy0
    refine ⟨j, ?_⟩
    calc
      (lowerCentralFactorLinearAut xi 1 ^ j) x =
          (lowerCentralFactorLinearAut xi 1 ^ j) (powerEquiv x0) := by
            simp [x0]
      _ = powerEquiv ((Txi ^ j) x0) := (hpowerEquiv_pow j x0).symm
      _ = powerEquiv y0 := by rw [hj]
      _ = y := by simp [y0]
  have hL2_card :
      Nat.card (LowerCentralFactor C 1) = 2 ^ r := by
    rw [← hAQ_card]
    exact Nat.card_congr powerEquiv.toEquiv.symm
  have hfactor_iso :
      ∃ e : Additive (LowerCentralFactor C 0) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor C 1),
        ∀ v : Additive (LowerCentralFactor C 0),
          e (lowerCentralFactorLinearAut xi 0 v) =
            lowerCentralFactorLinearAut xi 1 (e v) := by
    refine ⟨squareEquiv.trans powerEquiv, ?_⟩
    intro v
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      hsquareEquiv_equivariant, hpowerEquiv_equivariant]
  exact (lemma4_gorenstein_thompson_nonisomorphic_factors
    hC_two hC_nonabelian xi hxi_odd hL1_irreducible
      hL2_transitive r hr hL2_card) hfactor_iso

end Higman
end External
end CFSG.BenderSuzuki
