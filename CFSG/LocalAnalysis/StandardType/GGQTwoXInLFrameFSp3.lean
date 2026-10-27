module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSp2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSp4
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCentFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLayer
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.ComponentInitial Polynomial Multiplicative

theorem exists_traceFrame_of_cfg_sp {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} {E : Subgroup ↥(CFSG.Open.StatedSp m K)}
    {x : ↥(CFSG.Open.StatedSp m K)} {L D J : Subgroup ↥(CFSG.Open.StatedSp m K)}
    (hC : GGQTwoFRCfg E x L D J) :
    ∃ (n : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra K M) (τ : M ≃+* M)
      (U : Type) (_ : AddCommGroup U) (_ : Module K U)
      (Φ : ((Fin n → M) × U) ≃ₗ[K] (Fin m ⊕ Fin m → K)) (c : M),
      Nat.card M = 4 ∧ (∀ y, τ y = y ^ 2) ∧ c ^ 2 ≠ c ∧
      (∀ d d' w w', CFSG.RankThree.Classical.spForm m K (Φ (d, w)) (Φ (d', w')) =
        ∑ i, Algebra.trace K M (τ (d i) * d' i) +
          CFSG.RankThree.Classical.spForm m K (Φ (0, w)) (Φ (0, w'))) ∧
      (∀ d w, CFSG.RankThree.Classical.spEnd x (Φ (d, w)) = Φ (c • d, w)) ∧
      (∀ e ∈ E, ∃ a : Fin n → M, (∀ i, a i ^ 3 = 1) ∧
        ∀ d w, CFSG.RankThree.Classical.spEnd e (Φ (d, w)) =
          Φ (fun i => a i * d i, w)) ∧
      ∀ a : Fin n → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ E,
        ∀ d w, CFSG.RankThree.Classical.spEnd e (Φ (d, w)) =
          Φ (fun i => a i * d i, w) := by
  classical
  have hCcopy := hC
  obtain ⟨hEel, hEcard, hsc, hxE, hx1, hxL, hLcomp, hEnorm, hCE, hDE, hDcard, hxD,
    hJcomp, hCJ⟩ := hC
  let V := Fin m ⊕ Fin m → K
  let B : LinearMap.BilinForm K V := CFSG.RankThree.Classical.spForm m K
  let e₂ : ↥(CFSG.Open.StatedSp m K) ≃* ↥(sesqUnitaryGroup B) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin)
  let E' : Subgroup ↥(sesqUnitaryGroup B) := E.map e₂.toMonoidHom
  have hE'el : IsElemAbelian 3 E' := TableB.isElemAbelian_map hEel _
  have hsc' : ∀ Z : ↥(sesqUnitaryGroup B), (∀ Y ∈ E', Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E' := by
    intro Z hZ hZ3
    obtain ⟨z, rfl⟩ := e₂.surjective Z
    refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
    refine hsc z ?_ ?_
    · intro Y hY
      apply e₂.injective
      rw [map_mul, map_mul]
      exact (hZ (e₂ Y) (Subgroup.mem_map.mpr ⟨Y, hY, rfl⟩)).symm
    · apply e₂.injective
      rw [map_pow, hZ3, map_one]
  let F : CFSG.StandardType.SpNS.FrameData K V B E' :=
    Classical.choice (CFSG.StandardType.SpNS.exists_frame_data hK
      CFSG.RankThree.Classical.spForm_isAlt CFSG.RankThree.Classical.spForm_nondegenerate
      E' hE'el)
  have hκ : IsEmpty F.κ := CFSG.StandardType.SpNS.kappa_empty F
    CFSG.RankThree.Classical.spForm_isAlt CFSG.RankThree.Classical.spForm_nondegenerate hsc'
  obtain ⟨hEτ, hτE⟩ := CFSG.StandardType.SpNS.torus_range F hsc'
  let M := AdjoinRoot F.g
  have hfact : Fact (Irreducible F.g) := ⟨F.hg⟩
  have : Fact (Irreducible F.g) := hfact
  have hMmod : Module.Finite K M := (AdjoinRoot.powerBasis F.hg.ne_zero).finite
  have : Module.Finite K M := hMmod
  have : Finite M := Module.finite_of_finite K
  have hM : Nat.card M = 4 := QTwoSpFrame.natCard_adjoinRoot_eq_four F.b hK
  have hcharM : CharP M 2 := charP_of_injective_algebraMap (algebraMap K M).injective 2
  have : CharP M 2 := hcharM
  let τ : M ≃+* M := frobeniusEquiv M 2
  have hτ2 : ∀ y, τ y = y ^ 2 := fun y => frobeniusEquiv_apply M 2 y
  have hτ : ∀ y, τ (τ y) = y := fun y => TraceFrame.frobeniusEquiv_two_involutive hM y
  have hx3 : x ^ 3 = 1 := hEel.2 x hxE
  have hxE' : e₂ x ∈ E' := Subgroup.mem_map.mpr ⟨x, hxE, rfl⟩
  obtain ⟨k, hk⟩ := F.hact (e₂ x) hxE'
  have hspx : ((e₂ x : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) =
      CFSG.RankThree.Classical.spLin m K x := by
    rfl
  have hxk : ∀ d w, CFSG.RankThree.Classical.spEnd x (F.Φ (d, w)) =
      F.Φ (fun i => F.ζ ^ k i * d i, w) := by
    intro d w
    have h := hk d w
    simpa only [CFSG.RankThree.Classical.spEnd, hspx] using h
  let c : Fin F.s → M := fun i => F.ζ ^ k i
  have hc3 : ∀ i, c i ^ 3 = 1 := by
    intro i
    dsimp [c]
    rw [← pow_mul, mul_comm, pow_mul, F.hζp, one_pow]
  have hx_ne_one_coord : ∃ j, c j ≠ 1 := by
    by_contra h
    push Not at h
    dsimp [c] at h
    have hsp : CFSG.RankThree.Classical.spEnd x = 1 := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective v
      rw [hxk, Module.End.one_apply]
      congr 2
      funext i
      rw [h i, one_mul]
    have he2 : e₂ x = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa [hspx] using hsp
    exact hx1 (e₂.injective (by rw [he2, map_one]))
  have hm1 : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    subst hm0
    have hcard : Nat.card ↥(CFSG.Open.StatedSp 0 K) = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
      simp
    have hle : Nat.card E ≤ Nat.card ↥(CFSG.Open.StatedSp 0 K) :=
      Subgroup.card_le_card_group (H := E)
    rw [hcard] at hle
    omega
  have hLcompO : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set _)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hLcomp
  have hL_or := CFSG.LocalAnalysis.GLTheoremA.T173O.eq_or_of_isComponentOf_centralizer
    hK hm1 hx3 hx1 hLcompO
  have hno_fix : ∀ i, c i ≠ 1 := by
    simpa [c] using QTwoSpFrame.no_fixed_coordinate (K := K) (m := m) (E := E) (x := x)
      (L := L) (D := D) (J := J) (e₂ := e₂) (E' := E') (F := F)
      hK hCcopy rfl hτE (k := k) (fun _ => rfl) hspx hxk
  have hc_cases : ∀ i, c i = F.ζ ∨ c i = F.ζ ^ 2 := by
    intro i
    have hred : c i = F.ζ ^ (k i % 3) := by
      dsimp [c]
      conv_lhs => rw [← Nat.div_add_mod (k i) 3]
      rw [pow_add, pow_mul, F.hζp, one_pow, one_mul]
    have hk3 : k i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : k i % 3
    · exfalso
      exact hno_fix i (by simp [hred])
    · left; simp [hred]
    · right; simp [hred]
  have hτ_smul : ∀ (a : K) (y : M), τ (a • y) = a • τ y := by
    intro a y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact CFSG.StandardType.TraceFrame.tau_algebraMap hK τ a
  let τLin : M →ₗ[K] M :=
    { toFun := τ
      map_add' := fun x y => τ.map_add x y
      map_smul' := hτ_smul }
  let τL : M ≃ₗ[K] M := LinearEquiv.ofBijective τLin τ.bijective
  have τL_apply : ∀ y, τL y = τ y := fun y => rfl
  let swapAt : Fin F.s → (M ≃ₗ[K] M) := fun i =>
    if c i = F.ζ then LinearEquiv.refl K M else τL
  let ψ : (Fin F.s → M) ≃ₗ[K] Fin F.s → M := LinearEquiv.piCongrRight swapAt
  have ψ_apply : ∀ (d : Fin F.s → M) (i : Fin F.s),
      ψ d i = if c i = F.ζ then d i else τ (d i) := by
    intro d i
    rw [show ψ d i = swapAt i (d i) from LinearEquiv.piCongrRight_apply _ _ _]
    by_cases h : c i = F.ζ
    · simp [swapAt, h]
    · simp [swapAt, h, τL_apply]
  let U := F.κ → K
  let Φ' : ((Fin F.s → M) × U) ≃ₗ[K] V :=
    (ψ.prodCongr (LinearEquiv.refl K U)).trans F.Φ
  have Φ'_apply : ∀ (d : Fin F.s → M) (w : U), Φ' (d, w) = F.Φ (ψ d, w) :=
    fun d w => rfl
  have hx_Φ' : ∀ (d : Fin F.s → M) (w : U),
      CFSG.RankThree.Classical.spEnd x (Φ' (d, w)) = Φ' (fun i => F.ζ * d i, w) := by
    intro d w
    rw [Φ'_apply, hxk, Φ'_apply]
    congr 1
    apply Prod.ext
    · funext i
      change F.ζ ^ k i * ψ d i = ψ (fun i => F.ζ * d i) i
      rw [ψ_apply, ψ_apply]
      by_cases hci : c i = F.ζ
      · rw [if_pos hci, if_pos hci]
        have hci' : F.ζ ^ k i = F.ζ := by simpa [c] using hci
        rw [hci']
      · rw [if_neg hci, if_neg hci]
        have hci2 : F.ζ ^ k i = F.ζ ^ 2 := by
          have h := (hc_cases i).resolve_left hci
          simpa [c] using h
        rw [hci2, map_mul, hτ2 F.ζ]
    · rfl
  obtain ⟨j, hcj⟩ := hx_ne_one_coord
  have hβ_alt : F.β.IsAlt := by
    intro a
    have h0 : B (F.Φ (Pi.single j a, 0)) (F.Φ (Pi.single j a, 0)) = 0 :=
      CFSG.RankThree.Classical.spForm_isAlt _
    have h := F.hdec (Pi.single j a) (Pi.single j a) (0 : F.κ → K) 0
    have hB00 : B (F.Φ (0, (0 : F.κ → K))) (F.Φ (0, 0)) = 0 := by
      change B (F.Φ (0 : (Fin F.s → AdjoinRoot F.g) × (F.κ → K)))
        (F.Φ (0 : (Fin F.s → AdjoinRoot F.g) × (F.κ → K))) = 0
      rw [map_zero, map_zero]
    rw [h0, hB00, add_zero] at h
    have hsum' : ∑ l, F.β ((Pi.single j a : Fin F.s → AdjoinRoot F.g) l)
        ((Pi.single j a : Fin F.s → AdjoinRoot F.g) l) =
        F.β ((Pi.single j a : Fin F.s → AdjoinRoot F.g) j)
          ((Pi.single j a : Fin F.s → AdjoinRoot F.g) j) := by
      refine Finset.sum_eq_single (s := Finset.univ) j ?_ ?_
      · intro b _ hbj
        simp [Pi.single_eq_of_ne hbj]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hsum : ∑ l, F.β ((Pi.single j a : Fin F.s → AdjoinRoot F.g) l)
        ((Pi.single j a : Fin F.s → AdjoinRoot F.g) l) = F.β a a := by
      simpa using hsum'
    rw [hsum] at h
    exact h.symm
  have hβ_nd : F.β.Nondegenerate := by
    constructor
    · intro a ha
      have h0 : F.Φ (Pi.single j a, 0) = 0 := by
        refine CFSG.RankThree.Classical.spForm_nondegenerate.1 _ ?_
        intro y
        obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective y
        rw [F.hdec]
        have hB0 : B (F.Φ (0, (0 : F.κ → K))) (F.Φ (0, w)) = 0 := by
          change B (F.Φ (0 : (Fin F.s → AdjoinRoot F.g) × (F.κ → K))) (F.Φ (0, w)) = 0
          rw [map_zero]
          simp
        rw [hB0, add_zero]
        have hsum' : ∑ l, F.β ((Pi.single j a : Fin F.s → AdjoinRoot F.g) l) (d l) =
            F.β ((Pi.single j a : Fin F.s → AdjoinRoot F.g) j) (d j) := by
          refine Finset.sum_eq_single (s := Finset.univ) j ?_ ?_
          · intro b _ hbj; simp [Pi.single_eq_of_ne hbj]
          · intro hj; exact absurd (Finset.mem_univ j) hj
        have hsum : ∑ l, F.β ((Pi.single j a : Fin F.s → AdjoinRoot F.g) l) (d l) =
            F.β a (d j) := by simpa using hsum'
        rw [hsum, ha (d j)]
      have hpairs : ((Pi.single j a, (0 : F.κ → K)) :
          (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) = 0 :=
        F.Φ.injective (by simpa using h0)
      have h := congrFun (congrArg Prod.fst hpairs) j
      simpa [Pi.single_eq_same] using h
    · intro b hb
      have h0 : F.Φ (Pi.single j b, 0) = 0 := by
        refine CFSG.RankThree.Classical.spForm_nondegenerate.2 _ ?_
        intro y
        obtain ⟨⟨d, w⟩, rfl⟩ := F.Φ.surjective y
        rw [F.hdec]
        have hB0 : B (F.Φ (0, w)) (F.Φ (0, (0 : F.κ → K))) = 0 := by
          change B (F.Φ (0, w)) (F.Φ (0 : (Fin F.s → AdjoinRoot F.g) × (F.κ → K))) = 0
          rw [map_zero]
          simp
        rw [hB0, add_zero]
        have hsum' : ∑ l, F.β (d l) ((Pi.single j b : Fin F.s → AdjoinRoot F.g) l) =
            F.β (d j) ((Pi.single j b : Fin F.s → AdjoinRoot F.g) j) := by
          refine Finset.sum_eq_single (s := Finset.univ) j ?_ ?_
          · intro c _ hcj'; simp [Pi.single_eq_of_ne hcj']
          · intro hj; exact absurd (Finset.mem_univ j) hj
        have hsum : ∑ l, F.β (d l) ((Pi.single j b : Fin F.s → AdjoinRoot F.g) l) =
            F.β (d j) b := by simpa using hsum'
        rw [hsum, hb (d j)]
      have hpairs : ((Pi.single j b, (0 : F.κ → K)) :
          (Fin F.s → AdjoinRoot F.g) × (F.κ → K)) = 0 :=
        F.Φ.injective (by simpa using h0)
      have h := congrFun (congrArg Prod.fst hpairs) j
      simpa [Pi.single_eq_same] using h
  have hfr : Module.finrank K M = 2 := by
    rw [Module.finrank_eq_card_basis (R := K) (M := M) F.b]
    norm_num
  have τLin_apply : ∀ y, τLin y = τ y := fun y => rfl
  let T : LinearMap.BilinForm K M :=
    (Algebra.traceForm K M).compl₁₂ τLin LinearMap.id
  have T_apply : ∀ a b, T a b = Algebra.trace K M (τ a * b) := by
    intro a b
    simp [T, Algebra.traceForm_apply, τLin_apply]
  have T_alt : T.IsAlt := by
    intro a
    rw [T_apply, hτ2]
    rw [show a ^ 2 * a = a ^ 3 from by ring]
    by_cases ha : a = 0
    · simp [ha]
    · have ha3 : a ^ 3 = 1 := by
        have h := @FiniteField.pow_card_sub_one_eq_one M _ (Fintype.ofFinite M) a ha
        rw [Fintype.card_eq_nat_card, hM] at h
        norm_num at h
        exact h
      rw [ha3]
      have htr1 : Algebra.trace K M (1 : M) = 0 := by
        have h : Algebra.trace K M (1 : M) = Module.finrank K M • (1 : K) := by
          simpa using Algebra.trace_algebraMap (R := K) (S := M) (1 : K)
        rw [h, hfr]
        rw [two_nsmul, CharTwo.add_self_eq_zero]
      exact htr1
  have T_nd : T.Nondegenerate := by
    constructor
    · intro a ha
      have hta : τ a = 0 := by
        refine (traceForm_nondegenerate K M).1 (τ a) ?_
        intro b
        rw [Algebra.traceForm_apply]
        have h := ha b
        rwa [T_apply] at h
      exact τ.injective (by rw [hta, map_zero])
    · intro b hb
      refine (traceForm_nondegenerate K M).2 b ?_
      intro x
      rw [Algebra.traceForm_apply]
      have h := hb (τ.symm x)
      rw [T_apply, τ.apply_symm_apply] at h
      exact h
  have T_tau_tau : ∀ a b, T (τ a) (τ b) = T a b := by
    intro a b
    rw [T_apply, T_apply, hτ]
    have h := CFSG.StandardType.TraceFrame.trace_tau (K := K) (M := M) hK (τ := τ) (τ a * b)
    rw [map_mul, hτ] at h
    exact h
  have hT_pair : T (F.b 0) (F.b 1) ≠ 0 :=
    CFSG.StandardType.SpNS.alt_two_ne_zero F.b T_alt T_nd.1
  have hβ_pair : F.β (F.b 0) (F.b 1) ≠ 0 :=
    CFSG.StandardType.SpNS.alt_two_ne_zero F.b hβ_alt hβ_nd.1
  have hprop := CFSG.StandardType.SpNS.alt_two_eq_smul F.b hβ_alt T_alt hT_pair
  let cc := F.β (F.b 0) (F.b 1) / T (F.b 0) (F.b 1)
  have hcc0 : cc ≠ 0 := by
    dsimp [cc]
    exact div_ne_zero hβ_pair hT_pair
  have hcc1 : cc = 1 := by
    rcases CFSG.StandardType.ChoiceTwo.eq_zero_or_eq_one hK cc with h | h
    · exact absurd h hcc0
    · exact h
  have hβT : F.β = T := by
    rw [show F.β = (F.β (F.b 0) (F.b 1) / T (F.b 0) (F.b 1)) • T from hprop]
    rw [show F.β (F.b 0) (F.b 1) / T (F.b 0) (F.b 1) = cc from rfl, hcc1, one_smul]
  have hB' : ∀ (d d' : Fin F.s → M) (w w' : U),
      B (Φ' (d, w)) (Φ' (d', w')) =
        ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ' (0, w)) (Φ' (0, w')) := by
    intro d d' w w'
    rw [Φ'_apply, Φ'_apply, F.hdec, hβT, Φ'_apply, Φ'_apply]
    simp only [map_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ψ_apply, ψ_apply]
    by_cases hci : c i = F.ζ
    · rw [if_pos hci, if_pos hci, T_apply]
    · rw [if_neg hci, if_neg hci, T_tau_tau, T_apply]
  have hζ2ζ : F.ζ ^ 2 ≠ F.ζ := by
    intro h
    have h0 : F.ζ * (F.ζ - 1) = 0 := by
      rw [mul_sub, mul_one, ← sq, h, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · have h1' : F.ζ ^ 3 = 1 := F.hζp
      rw [h1] at h1'
      norm_num at h1'
    · exact F.hζ1 (sub_eq_zero.mp h1)
  refine ⟨F.s, M, inferInstance, inferInstance, inferInstance, τ, U,
    inferInstance, inferInstance, Φ', F.ζ, hM, hτ2, hζ2ζ, hB', ?_, ?_, ?_⟩
  · intro d w
    exact hx_Φ' d w
  · intro e he
    have he' : e₂ e ∈ E' := Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨f, hf_eq⟩ := hEτ (e₂ e) he'
    let aa : Fin F.s → M := fun i =>
      if c i = F.ζ then F.ζ ^ (toAdd (f i)).val
      else F.ζ ^ (2 * (toAdd (f i)).val)
    have haa3 : ∀ i, aa i ^ 3 = 1 := by
      intro i
      dsimp [aa]
      split
      · rw [← pow_mul, mul_comm, pow_mul, F.hζp, one_pow]
      · rw [← pow_mul, show 2 * (toAdd (f i)).val * 3 =
            3 * (2 * (toAdd (f i)).val) by ring, pow_mul, F.hζp, one_pow]
    have hFτ_act : ∀ (d' : Fin F.s → M) (w : U),
        (((F.τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
          V →ₗ[K] V) (Φ' (d', w)) = Φ' (fun i => aa i * d' i, w) := by
      intro d' w
      rw [Φ'_apply, F.hτapp, Φ'_apply]
      congr 1
      apply Prod.ext
      · funext i
        let gfun : Fin F.s → M := fun j =>
          (if c j = F.ζ then F.ζ ^ (toAdd (f j)).val
           else F.ζ ^ (2 * (toAdd (f j)).val)) * d' j
        change F.ζ ^ (toAdd (f i)).val * (ψ d') i = (ψ gfun) i
        simp only [ψ_apply]
        by_cases hci : c i = F.ζ
        · simp [gfun, hci]
        · simp [gfun, hci]
          left
          rw [hτ2 F.ζ, ← pow_mul,
            show 2 * (2 * (toAdd (f i)).val) = 4 * (toAdd (f i)).val by ring]
          rw [pow_eq_pow_mod (toAdd (f i)).val F.hζp,
            pow_eq_pow_mod (4 * (toAdd (f i)).val) F.hζp]
          congr 1
          have hmod : (4 * (toAdd (f i)).val) % 3 = (toAdd (f i)).val % 3 := by
            rw [show 4 * (toAdd (f i)).val =
                (toAdd (f i)).val + 3 * (toAdd (f i)).val by ring,
              Nat.add_mul_mod_self_left]
          exact hmod.symm
      · rfl
    refine ⟨aa, haa3, ?_⟩
    intro d w
    change (((e₂ e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ' (d, w)) = Φ' (fun i => aa i * d i, w)
    rw [← hf_eq]
    exact hFτ_act d w
  · intro a ha3
    have hcases : ∀ i, a i = 1 ∨ a i = F.ζ ∨ a i = F.ζ ^ 2 :=
      fun i => QTwoFrameTorus.frame_eq_one_or_eq_or_sq hM F.hζp F.hζ1 (ha3 i)
    have hτcases : ∀ i, τ (a i) = 1 ∨ τ (a i) = F.ζ ∨ τ (a i) = F.ζ ^ 2 := by
      intro i
      rcases hcases i with h | h | h
      · left; rw [h, map_one]
      · right; right; rw [h, hτ2 F.ζ]
      · right; left
        rw [h, map_pow, hτ2 F.ζ, ← pow_mul, show 2 * 2 = 4 by norm_num,
          show (4 : ℕ) = 3 + 1 by norm_num, pow_add, F.hζp, one_mul, pow_one]
    let ee : Fin F.s → ZMod 3 := fun i =>
      if c i = F.ζ then
        Classical.choose (QTwoFrameTorus.frame_exists_zmod3_pow_eq (hcases i))
      else
        Classical.choose (QTwoFrameTorus.frame_exists_zmod3_pow_eq (hτcases i))
    have hee : ∀ i, F.ζ ^ (ee i).val = if c i = F.ζ then a i else τ (a i) := by
      intro i
      dsimp [ee]
      split
      · exact Classical.choose_spec
          (QTwoFrameTorus.frame_exists_zmod3_pow_eq (hcases i))
      · exact Classical.choose_spec
          (QTwoFrameTorus.frame_exists_zmod3_pow_eq (hτcases i))
    let f : Fin F.s → Multiplicative (ZMod 3) := fun i => ofAdd (ee i)
    have hFτ_act : ∀ (d' : Fin F.s → M) (w : U),
        (((F.τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
          V →ₗ[K] V) (Φ' (d', w)) = Φ' (fun i => a i * d' i, w) := by
      intro d' w
      rw [Φ'_apply, F.hτapp, Φ'_apply]
      congr 1
      apply Prod.ext
      · funext i
        let gfun : Fin F.s → M := fun j => a j * d' j
        change F.ζ ^ (toAdd (f i)).val * (ψ d') i = (ψ gfun) i
        simp only [ψ_apply]
        have hfval : (toAdd (f i)).val = (ee i).val := rfl
        by_cases hci : c i = F.ζ
        · have hei : F.ζ ^ (ee i).val = a i := by
            rw [hee i, if_pos hci]
          rw [if_pos hci, if_pos hci]
          simp [gfun, hei, hfval]
        · have hei : F.ζ ^ (ee i).val = τ (a i) := by
            rw [hee i, if_neg hci]
          rw [if_neg hci, if_neg hci]
          simp [gfun, hei, hfval, map_mul]
      · rfl
    refine ⟨e₂.symm (F.τ f), ?_, ?_⟩
    · have hmem : F.τ f ∈ E.map e₂.toMonoidHom := hτE f
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
      have hye : e₂.symm (F.τ f) = y := by
        have h1 : e₂ y = F.τ f := hyeq
        have h2 : e₂.symm (e₂ y) = e₂.symm (F.τ f) := congrArg e₂.symm h1
        simpa using h2.symm
      rw [hye]
      exact hy
    · intro d w
      change (((e₂ (e₂.symm (F.τ f)) : ↥(sesqUnitaryGroup B)) :
        LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ' (d, w)) =
        Φ' (fun i => a i * d i, w)
      rw [e₂.apply_symm_apply]
      exact hFτ_act d w

end CFSG.StandardType

end
