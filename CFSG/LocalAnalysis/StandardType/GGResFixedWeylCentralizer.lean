module

public import CFSG.LocalAnalysis.StandardType.GGK2E6E6OriginalSpanTwo

public import CFSG.LocalAnalysis.StandardType.GGIntCartanDet

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove

public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrFix
public import CFSG.LocalAnalysis.StandardType.GGTBTorCor
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6Three
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinear
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def ggTypLADvd (p : ℕ) {Λ Λ' : Type} (ML : CoxeterMatrix Λ)
    (_ : CoxeterMatrix Λ') : Prop :=
  GGIsTypeA ML ∧ p ∣ Nat.card Λ + 1

theorem ggTypLADvd_or_E6_of_cartan_singular
    {p : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
        ∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
      (p = 3 ∧ ∃ e : Fin 6 ≃ Λ,
        ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)) :
    (GGIsTypeA M ∧ p ∣ Nat.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M) := by
  rcases h with ⟨n, e, hn, hpd, he⟩ | ⟨hp3, e, he⟩
  · left
    have hCeq : C = fun i j => CartanMatrix.A n (e.symm i) (e.symm j) := by
      ext i j
      simpa using he (e.symm i) (e.symm j)
    have hAint : GGIntCartan ((CoxeterMatrix.A n).reindex e) C := by
      rw [hCeq]
      exact l05nBL_intCartan_reindex (ggIntCartan_A n) e.symm
    have hMeq : M = (CoxeterMatrix.A n).reindex e := ggIntCartan_coxeter_eq hC hAint
    refine ⟨⟨n, e, hn, hMeq⟩, ?_⟩
    have hcard : Fintype.card Λ = n := by
      simpa using Fintype.card_congr e.symm
    simpa [hcard] using hpd
  · right
    refine ⟨hp3, ?_⟩
    exact ⟨e, ggIntCartan_E6_coxeter_reindex hC e he⟩

theorem ggFixedSubmodule_pi_ker {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {S : Finset Λ} {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive E ≃+ V)
    (φ : {i : Λ // i ∉ S} → MulAut E) (h : {i : Λ // i ∉ S} → V)
    (α : {i : Λ // i ∉ S} → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hdiag : ∀ i, α i (h i) = 2) (hp2 : p ≠ 2)
    (N : Subgroup (MulAut E)) (hgen : N = Subgroup.closure (Set.range φ)) :
    (LinearMap.pi α).ker = ggFixedSubmodule (p := p) ι N := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hh : ∀ i, h i ≠ 0 := by
    intro i hi
    apply h2
    rw [← hdiag i, hi, map_zero]
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hvα : ∀ i, α i v = 0 := by
      intro i
      have := congrFun hv i
      simpa using this
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    rw [hgen] at hψ
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hψ
    · rintro _ ⟨i, rfl⟩
      rw [hlin, hvα i, zero_smul, sub_zero]
    · simp
    · intro x y _ _ hx hy
      rw [map_mul]
      change ggLin (p := p) ι x (ggLin (p := p) ι y v) = v
      rw [hy, hx]
    · intro x _ hx
      calc
        ggLin (p := p) ι x⁻¹ v =
            ggLin (p := p) ι x⁻¹ (ggLin (p := p) ι x v) := by rw [hx]
        _ = (ggLin (p := p) ι x⁻¹ * ggLin (p := p) ι x) v := rfl
        _ = ggLin (p := p) ι (x⁻¹ * x) v := by rw [map_mul]
        _ = ggLin (p := p) ι 1 v := by rw [inv_mul_cancel]
        _ = v := by simp
  · intro hv
    rw [mem_ggFixedSubmodule_iff] at hv
    rw [LinearMap.mem_ker]
    funext i
    have hfix : ggLin (p := p) ι (φ i) v = v := by
      apply hv
      rw [hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hzero : α i v • h i = 0 := by
      have h' : v - α i v • h i = v := by
        rw [← hlin i v, hfix]
      exact sub_eq_self.mp h'
    exact (smul_eq_zero.mp hzero).resolve_right (hh i)

theorem e6_exact_two_survivor_det_ne_zero {S : Finset (Fin 6)}
    (hS : S.card = 2) (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S) :
    (Matrix.of fun i j : {i : Fin 6 // i ∉ S} =>
      (CartanMatrix.E 6 i.val j.val : ZMod 3)).det ≠ 0 := by
  rcases ggDeletedConnectedS_E6_exact_two hS hc with rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

section E6DeletedExtension

open Module

set_option maxHeartbeats 800000

private theorem exists_deleted_extension_of_surviving_independent
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : ι → V) (J S : Finset ι)
    (hdisj : Disjoint J S) (hunion : J ∪ S = Finset.univ)
    (hJ : LinearIndepOn K h (J : Set ι))
    (hJcard : J.card = 4)
    (hHfin : Module.finrank K (Submodule.span K (Set.range h)) = 5) :
    ∃ s ∈ S, LinearIndepOn K h (insert s (J : Set ι)) := by
  classical
  let W : Submodule K V := Submodule.span K (h '' (J : Set ι))
  have hWfin : Module.finrank K W = 4 := by
    have hspan : (h '' (J : Set ι)) = Set.range (fun i : J => h i) := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
    have hWeq : W = Submodule.span K (Set.range (fun i : J => h i)) := by
      dsimp only [W]
      rw [hspan]
    have hJ' : LinearIndependent K (fun i : J => h i) := hJ
    rw [hWeq, finrank_span_eq_card hJ', Fintype.card_coe, hJcard]
  by_contra hnone
  have hSsub : ∀ s ∈ S, h s ∈ W := by
    intro s hs
    by_contra hout
    have hsJ : s ∉ (J : Set ι) := by
      intro hsJ
      exact Finset.disjoint_left.mp hdisj hsJ hs
    have hins : LinearIndepOn K h (insert s (J : Set ι)) := by
      rw [linearIndepOn_insert hsJ]
      exact ⟨hJ, by simpa [W] using hout⟩
    exact hnone ⟨s, hs, hins⟩
  have hrange : Set.range h ⊆ W := by
    rintro v ⟨i, rfl⟩
    by_cases hi : i ∈ J
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · have hiS : i ∈ S := by
        have hmem : i ∈ J ∪ S := by simpa [hunion] using Finset.mem_univ i
        exact (Finset.mem_union.mp hmem).resolve_left hi
      exact hSsub i hiS
  have hle : Submodule.span K (Set.range h) ≤ W := Submodule.span_le.mpr hrange
  have hmono := Submodule.finrank_mono hle
  omega

theorem e6_survivor_linearIndependent
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V]
    {h : Λ → V} {α : Λ → Module.Dual (ZMod 3) V}
    (hCL : GGIntCartan ML CL) (e6 : Fin 6 ≃ Λ)
    (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hpair : ∀ i j : Λ, α i (h j) = (CL i j : ZMod 3))
    (hS2 : S.card = 2) (hconn : GGDeletedConnectedS ML S) :
    LinearIndependent (ZMod 3) (fun i : {i : Λ // i ∉ S} => h i) := by
  classical
  let hL : Fin 6 → V := fun i => h (e6 i)
  let αL : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (e6 i)
  have hpairE6 : ∀ i j : Fin 6, αL i (hL j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair, e6Cartan_reindex e6 hCL hMLeq]
  let S0 : Finset (Fin 6) := S.map e6.symm.toEmbedding
  have hS0 : S0.card = 2 := by simpa [S0] using hS2
  have hconn' : GGDeletedConnectedS (CoxeterMatrix.E₆.reindex e6) S := by
    simpa [hMLeq] using hconn
  have hconn0 : GGDeletedConnectedS CoxeterMatrix.E₆ S0 :=
    GGDeletedConnectedS.of_reindex e6 hconn'
  let I0 : Type := {i : Fin 6 // i ∉ S0}
  let I : Type := {i : Λ // i ∉ S}
  let eT : I0 ≃ I :=
    { toFun := fun i =>
        ⟨e6 i.1, by
          intro hmem
          apply i.2
          exact Finset.mem_map.mpr ⟨e6 i.1, hmem, by simp⟩⟩
      invFun := fun i =>
        ⟨e6.symm i.1, by
          intro hmem
          obtain ⟨a, haS, haeq⟩ := Finset.mem_map.mp hmem
          apply i.2
          have : a = i.1 := by simpa using congrArg e6 haeq
          simpa [this] using haS⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simp
      right_inv := by
        intro i
        apply Subtype.ext
        simp }
  have hdet : (Matrix.of fun i j : I0 => αL i.1 (hL j.1)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : I0 => αL i.1 (hL j.1)) =
        (Matrix.of fun i j : I0 =>
          (CartanMatrix.E 6 i.1 j.1 : ZMod 3)) := by
      ext i j
      exact hpairE6 i.1 j.1
    rw [hmat]
    exact e6_exact_two_survivor_det_ne_zero hS0 hconn0
  have hLI0 : LinearIndependent (ZMod 3) (fun i : I0 => hL i.1) :=
    linearIndependent_of_det_ne_zero (fun i : I0 => hL i.1)
      (fun i : I0 => αL i.1) hdet
  have hLI : LinearIndependent (ZMod 3) (fun i : I => h i.1) := by
    have hcomp := hLI0.comp eT.symm eT.symm.injective
    simpa [Function.comp_def, eT, I, I0, hL] using hcomp
  simpa [I] using hLI

theorem e6_dependent_spanH_finrank_five
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    Module.finrank (ZMod 3) (E6QTwo.spanH h) = 5 := by
  haveI : FiniteDimensional (ZMod 3) V := Module.Finite.of_finite
  have hScard := E6QTwo.dependent_e6_span_card hpair hdep
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := E6QTwo.spanH h)
  rw [Nat.card_zmod, hScard] at hc
  exact Nat.pow_right_injective (by norm_num) hc.symm

theorem e6_exists_deleted_extension
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Λ → V} {α : Λ → Module.Dual (ZMod 3) V}
    (hCL : GGIntCartan ML CL) (e6 : Fin 6 ≃ Λ)
    (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hpair : ∀ i j : Λ, α i (h j) = (CL i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h)
    (hS2 : S.card = 2) (hconn : GGDeletedConnectedS ML S) :
    ∃ s ∈ S, LinearIndepOn (ZMod 3) h
      (insert s ((Finset.univ.filter (fun i : Λ => i ∉ S) : Finset Λ) : Set Λ)) := by
  classical
  let J : Finset Λ := Finset.univ.filter (fun i => i ∉ S)
  have hcardΛ : Fintype.card Λ = 6 := by
    simpa using (Fintype.card_congr e6).symm
  have hJcard : J.card = 4 := by
    have hcardI : Fintype.card {i : Λ // i ∉ S} = 4 := by
      rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S)]
      have hcardS : Fintype.card {i : Λ // i ∈ S} = 2 := by
        rw [Fintype.card_coe]
        exact hS2
      omega
    rw [← Fintype.card_coe]
    simpa [J] using hcardI
  have hJset : (J : Set Λ) = {i : Λ | i ∉ S} := by
    ext i
    simp [J]
  have hJLI : LinearIndepOn (ZMod 3) h (J : Set Λ) := by
    have hraw := e6_survivor_linearIndependent hCL e6 hMLeq hpair hS2 hconn
    rw [hJset]
    exact hraw
  have hpairE6 : ∀ i j : Fin 6, α (e6 i) (h (e6 j)) =
      (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair, e6Cartan_reindex e6 hCL hMLeq]
  have hdepE6 : ¬ LinearIndependent (ZMod 3) (fun i : Fin 6 => h (e6 i)) := by
    intro hli
    apply hdep
    have hcomp := hli.comp e6.symm (fun a b hab => e6.symm.injective hab)
    simpa [Function.comp_def] using hcomp
  have hHfin : Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun i : Fin 6 => h (e6 i)))) = 5 := by
    have h := e6_dependent_spanH_finrank_five hpairE6 hdepE6
    simpa [E6QTwo.spanH] using h
  have hdisj : Disjoint J S := by
    rw [Finset.disjoint_left]
    intro i hiJ hiS
    exact (Finset.mem_filter.mp hiJ).2 hiS
  have hunion : J ∪ S = Finset.univ := by
    ext i
    by_cases hi : i ∈ S <;> simp [J, hi]
  have hspanAll : Submodule.span (ZMod 3) (Set.range (fun i : Fin 6 => h (e6 i))) =
      Submodule.span (ZMod 3) (Set.range h) := by
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e6 i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e6.symm i, by simp⟩
  have hHfin' : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 5 := by
    rw [← hspanAll]
    exact hHfin
  obtain ⟨s, hs, hins⟩ := exists_deleted_extension_of_surviving_independent
    h J S hdisj hunion hJLI hJcard hHfin'
  exact ⟨s, hs, hins⟩

theorem e6_outside_six_family
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {H : Λ ⊕ Λa → V} {α : Λ → Module.Dual (ZMod 3) V}
    (hCL : GGIntCartan ML CL) (e6 : Fin 6 ≃ Λ)
    (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hpair : ∀ i j : Λ, α i (H (Sum.inl j)) = (CL i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) (fun i : Λ => H (Sum.inl i)))
    (hS2 : S.card = 2) (hconn : GGDeletedConnectedS ML S)
    (a : Λa)
    (hout : H (Sum.inr a) ∉ E6QTwo.spanH (fun i : Fin 6 => H (Sum.inl (e6 i)))) :
    ∃ s ∈ S,
      let T : Finset (Λ ⊕ Λa) :=
        (insert s (Finset.univ.filter (fun i : Λ => i ∉ S))).image Sum.inl ∪ {Sum.inr a}
      T.card = 6 ∧ LinearIndepOn (ZMod 3) H (T : Set (Λ ⊕ Λa)) := by
  classical
  let J : Finset Λ := Finset.univ.filter (fun i => i ∉ S)
  have hpairE6 : ∀ i j : Fin 6, α (e6 i) (H (Sum.inl (e6 j))) =
      (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair, e6Cartan_reindex e6 hCL hMLeq]
  have hdepE6 : ¬ LinearIndependent (ZMod 3)
      (fun i : Fin 6 => H (Sum.inl (e6 i))) := by
    intro hli
    apply hdep
    have hcomp := hli.comp e6.symm (fun a b hab => e6.symm.injective hab)
    simpa [Function.comp_def] using hcomp
  have hHfin : Module.finrank (ZMod 3)
      (E6QTwo.spanH (fun i : Fin 6 => H (Sum.inl (e6 i)))) = 5 :=
    e6_dependent_spanH_finrank_five hpairE6 hdepE6
  obtain ⟨s, hs, hins⟩ :=
    e6_exists_deleted_extension hCL e6 hMLeq hpair hdep hS2 hconn
  let T5 : Finset Λ := insert s J
  let T : Finset (Λ ⊕ Λa) := T5.image Sum.inl ∪ {Sum.inr a}
  have hcardΛ : Fintype.card Λ = 6 := by
    simpa using (Fintype.card_congr e6).symm
  have hJcard : J.card = 4 := by
    have hcardI : Fintype.card {i : Λ // i ∉ S} = 4 := by
      rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S)]
      have hcardS : Fintype.card {i : Λ // i ∈ S} = 2 := by
        rw [Fintype.card_coe]
        exact hS2
      omega
    rw [← Fintype.card_coe]
    simpa [J] using hcardI
  have hsJ : s ∉ J := by
    have hdisj : Disjoint J S := by
      rw [Finset.disjoint_left]
      intro i hiJ hiS
      exact (Finset.mem_filter.mp hiJ).2 hiS
    intro hsJ
    exact Finset.disjoint_left.mp hdisj hsJ hs
  have hT5card : T5.card = 5 := by
    dsimp [T5]
    rw [Finset.card_insert_of_notMem hsJ, hJcard]
  have hJset : (J : Set Λ) = {i : Λ | i ∉ S} := by
    ext i
    simp [J]
  have hT5LI : LinearIndepOn (ZMod 3) H (Sum.inl '' (T5 : Set Λ)) := by
    have h := hins.image_of_comp Sum.inl H
    simpa [T5, hJset, Set.image_insert_eq] using h
  let H5 : Submodule (ZMod 3) V :=
    E6QTwo.spanH (fun i : Fin 6 => H (Sum.inl (e6 i)))
  let S5 : Submodule (ZMod 3) V :=
    Submodule.span (ZMod 3) (H '' (Sum.inl '' (T5 : Set Λ)))
  have hS5le : S5 ≤ H5 := by
    rw [Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hi
    exact Submodule.subset_span ⟨e6.symm j, by simp [H5]⟩
  have hT5cardSet : Fintype.card (T5 : Set Λ) = 5 :=
    (Fintype.card_coe T5).trans hT5card
  have hT5imgCard : Fintype.card (Sum.inl '' (T5 : Set Λ) : Set (Λ ⊕ Λa)) = 5 := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_image_of_injective _ Sum.inl_injective,
      ← Set.fintypeCard_eq_ncard, hT5cardSet]
  have hspanEq : Submodule.span (ZMod 3)
      (Set.range (fun x : (Sum.inl '' (T5 : Set Λ) : Set (Λ ⊕ Λa)) => H x)) = S5 := by
    dsimp only [S5]
    congr 1
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hS5fin : Module.finrank (ZMod 3) S5 = 5 := by
    rw [← hspanEq, finrank_span_eq_card hT5LI, hT5imgCard]
  have hS5eq : S5 = H5 :=
    Submodule.eq_of_le_of_finrank_eq hS5le (by rw [hS5fin, hHfin])
  have houtSpan : H (Sum.inr a) ∉ S5 := by
    rw [hS5eq]
    exact hout
  have hinr : Sum.inr a ∉ Sum.inl '' (T5 : Set Λ) := by
    rintro ⟨i, hi, hEq⟩
    exact Sum.inr_ne_inl hEq.symm
  have hT6LI : LinearIndepOn (ZMod 3) H
      (insert (Sum.inr a) (Sum.inl '' (T5 : Set Λ))) := by
    rw [linearIndepOn_insert hinr]
    exact ⟨hT5LI, houtSpan⟩
  have hTcard : T.card = 6 := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ Sum.inl_injective, hT5card]
      simp
    · simp [Finset.disjoint_singleton_right, hinr]
  refine ⟨s, hs, hTcard, ?_⟩
  simpa [T, T5, J, Finset.coe_union, Finset.coe_image, Finset.coe_singleton,
    Set.insert_comm] using hT6LI

end E6DeletedExtension

theorem e6_exact_two_kernel_finrank_add_four
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    {S : Finset (Fin 6)} (hS : S.card = 2)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S) :
    Module.finrank (ZMod 3) (LinearMap.pi (fun i : {i : Fin 6 // i ∉ S} => α i)).ker + 4 =
      Module.finrank (ZMod 3) V := by
  classical
  let I := {i : Fin 6 // i ∉ S}
  let F : V →ₗ[ZMod 3] (I → ZMod 3) := LinearMap.pi (fun i : I => α i)
  let h' : I → F.range := fun i => ⟨F (h i), ⟨h i, rfl⟩⟩
  let α' : I → Module.Dual (ZMod 3) F.range :=
    fun i => (LinearMap.proj i).comp F.range.subtype
  have hmat : (Matrix.of fun i j : I => α' i (h' j)) =
      Matrix.of fun i j : I => (CartanMatrix.E 6 i.val j.val : ZMod 3) := by
    ext i j
    exact hpair i j
  have hdet : (Matrix.of fun i j : I => α' i (h' j)).det ≠ 0 := by
    rw [hmat]
    exact e6_exact_two_survivor_det_ne_zero hS hc
  have hli : LinearIndependent (ZMod 3) h' :=
    linearIndependent_of_det_ne_zero h' α' hdet
  have hcard : Fintype.card I = 4 := by
    have hmem : Fintype.card {i : Fin 6 // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    dsimp only [I]
    rw [Fintype.card_subtype_compl (fun i : Fin 6 => i ∈ S), hmem, hS]
    decide
  have hlo : 4 ≤ Module.finrank (ZMod 3) F.range := by
    simpa only [hcard] using hli.fintype_card_le_finrank
  have hhi : Module.finrank (ZMod 3) F.range ≤ 4 := by
    simpa only [Module.finrank_pi, hcard] using Submodule.finrank_le F.range
  have hrank := F.finrank_range_add_finrank_ker
  have hfour : Module.finrank (ZMod 3) F.range = 4 := le_antisymm hhi hlo
  rw [hfour] at hrank
  simpa only [F, add_comm] using hrank

theorem ggRes_iOne_of_fixed_finrank_two
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  classical
  let C := Bs ⊓ Subgroup.centralizer (J : Set G)
  let W := ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)
  let f : C → W := fun b => ⟨ι (Additive.ofMul (⟨b, b.2.1⟩ : Bs)), by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [← ggLin_fix_iff]
    obtain ⟨g, hgJ, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hgφ]
    have hcomm := Subgroup.mem_centralizer_iff.mp b.2.2 g hgJ
    change g * (b : G) * g⁻¹ = (b : G)
    rw [hcomm]
    group⟩
  have hf : Function.Injective f := by
    intro a b hab
    have heq := ι.injective (congrArg Subtype.val hab)
    have heq' : (⟨a, a.2.1⟩ : Bs) = ⟨b, b.2.1⟩ := Additive.ofMul.injective heq
    exact Subtype.ext (congrArg (fun b : Bs => (b : G)) heq')
  have hcardW : Nat.card W = p ^ 2 := by
    haveI : Module.Finite (ZMod p) W := Module.Finite.of_finite
    simpa only [Nat.card_zmod, W, hfix] using
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := W)
  have hle : Nat.card C ≤ p ^ 2 := by
    rw [← hcardW]
    exact Nat.card_le_card_of_injective f hf
  have hDle : D ≤ C := by
    rw [hH.1.2.2.1.2.2.2.2.2.2]
    exact inf_le_inf_right _ hH.1.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hCD : C = D := (Subgroup.eq_of_le_of_card_ge hDle (by omega)).symm
  exact hCD

theorem ggFixedSubmodule_e6_exact_two_finrank_add_four
    {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (ι : Additive E ≃+ V)
    (φ : Fin 6 → MulAut E) (h : Fin 6 → V)
    (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    {S : Finset (Fin 6)} (hS : S.card = 2)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S)
    (N : Subgroup (MulAut E))
    (hgen : N = Subgroup.closure (Set.range (fun i : {i : Fin 6 // i ∉ S} => φ i))) :
    Module.finrank (ZMod 3) (ggFixedSubmodule (p := 3) ι N) + 4 =
      Module.finrank (ZMod 3) V := by
  have hdiag : ∀ i : Fin 6, (CartanMatrix.E 6 i i : ZMod 3) = 2 := by
    decide +kernel
  have hker := ggFixedSubmodule_pi_ker (p := 3) ι
    (fun i : {i : Fin 6 // i ∉ S} => φ i) (fun i => h i) (fun i => α i)
    (fun i => hlin i) (fun i => (hpair i i).trans (hdiag i)) (by decide) N hgen
  rw [← hker]
  exact e6_exact_two_kernel_finrank_add_four h α hpair hS hc

theorem ggRes_iOne_of_e6_exact_two_finrank_six
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hdim : Module.finrank (ZMod 3) V = 6)
    (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V)
    (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    {S : Finset (Fin 6)} (hS : S.card = 2)
    (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S)
    (hgen : ggAutomizer J Bs = Subgroup.closure
      (Set.range (fun i : {i : Fin 6 // i ∉ S} => φ i))) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hf := ggFixedSubmodule_e6_exact_two_finrank_add_four ι φ h α hlin hpair
    hS hc (ggAutomizer J Bs) hgen
  exact ggRes_iOne_of_fixed_finrank_two hH ι (by omega)

theorem ggIntCartan_E6_entries_of_type
    {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e) :
    ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j := by
  have hstd : GGIntCartan M (fun i j => CartanMatrix.E 6 (e.symm i) (e.symm j)) := by
    rw [hM]
    exact l05nBL_intCartan_reindex ggIntCartan_E₆ e.symm
  have hthree : ∀ i j, i ≠ j → M i j ≤ 3 := by
    intro i j hij
    rw [hM]
    change CoxeterMatrix.E₆ (e.symm i) (e.symm j) ≤ 3
    have he6 : ∀ a b : Fin 6, CoxeterMatrix.E₆ a b ≤ 3 := by
      intro a b
      fin_cases a <;> fin_cases b <;> decide +kernel
    exact he6 _ _
  have heq : C = (fun i j => CartanMatrix.E 6 (e.symm i) (e.symm j)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      exact (hC.1 i).trans (hstd.1 i).symm
    · exact ((hC.pair hstd hij).2 (hthree i j hij)).1
  intro i j
  rw [heq]
  simp

theorem ggFixedSubmodule_e6_exact_two_finrank_add_four_reindex
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e)
    {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (ι : Additive E ≃+ V)
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    {S : Finset Λ} (hS : S.card = 2) (hc : GGDeletedConnectedS M S)
    (N : Subgroup (MulAut E))
    (hgen : N = Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φ i))) :
    Module.finrank (ZMod 3) (ggFixedSubmodule (p := 3) ι N) + 4 =
      Module.finrank (ZMod 3) V := by
  classical
  let S0 := S.map e.symm.toEmbedding
  have hS0 : S0.card = 2 := by simpa [S0] using hS
  let eT : {i : Fin 6 // i ∉ S0} ≃ {i : Λ // i ∉ S} :=
    { toFun := fun i => ⟨e i, by simpa [S0] using i.2⟩
      invFun := fun i => ⟨e.symm i, by simpa [S0] using i.2⟩
      left_inv := fun i => by ext; simp
      right_inv := fun i => by ext; simp }
  have hc0 : GGDeletedConnectedS CoxeterMatrix.E₆ S0 := by
    intro i j
    have hp := l05nBL_rtg_map
      (r := fun u v : {i : Λ // i ∉ S} => u ≠ v ∧ M.M u v ≠ 2)
      (p := fun u v : {i : Fin 6 // i ∉ S0} => u ≠ v ∧ CoxeterMatrix.E₆.M u v ≠ 2)
      eT.symm (fun u v huv => by
        refine ⟨fun h => huv.1 (eT.symm.injective h), ?_⟩
        simpa [hM, CoxeterMatrix.reindex_apply, eT] using huv.2)
      (hc (eT i) (eT j))
    simpa using hp
  have hpair0 : ∀ i j : Fin 6, α (e i) (h (e j)) =
      (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair, ggIntCartan_E6_entries_of_type hC e hM]
  have hgen0 : N = Subgroup.closure
      (Set.range (fun i : {i : Fin 6 // i ∉ S0} => φ (e i))) := by
    rw [hgen]
    congr 1
    ext ψ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨eT.symm i, by simp [eT]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨eT i, rfl⟩
  exact ggFixedSubmodule_e6_exact_two_finrank_add_four ι (fun i => φ (e i))
    (fun i => h (e i)) (fun i => α (e i)) (fun i => hlin (e i)) hpair0 hS0 hc0 N hgen0

theorem ggResLeviDatumExact2_E6_iOne_of_card_six
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X Y : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcard : Nat.card Bs = 3 ^ 6)
    (hD : GGResLeviDatumExact2 3 Bs X J Y ggSelAny ggTypLE6) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, ha1, ha3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, hfull, hother, hgenX, hgenY, hc, hgenJ⟩
  letI := i1
  letI := i2
  letI := i5
  letI := i6
  letI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨e, he⟩ := htyp
  have hf := ggFixedSubmodule_e6_exact_two_finrank_add_four_reindex hCL e he ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    (fun i => hlin (Sum.inl i)) hpair hS hc (ggAutomizer J Bs) hgenJ
  have hcardV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcard
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hv := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hv
    exact Nat.pow_right_injective (by omega : 2 ≤ 3) hv.symm
  exact ggRes_iOne_of_fixed_finrank_two hH ι (by omega)

theorem finrank_le_card_add_finrank_ker_pi {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {S : Finset Λ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (α : {i : Λ // i ∉ S} → Module.Dual (ZMod p) V) :
    Module.finrank (ZMod p) V ≤
      Fintype.card {i : Λ // i ∉ S} +
        Module.finrank (ZMod p) (LinearMap.pi α).ker := by
  let : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let hMod : Module (ZMod p) ({i : Λ // i ∉ S} → ZMod p) :=
    Pi.module ({i : Λ // i ∉ S}) (fun _ => ZMod p) (ZMod p)
  let := hMod
  let π : V →ₗ[ZMod p] ({i : Λ // i ∉ S} → ZMod p) := LinearMap.pi α
  have h := @LinearMap.finrank_range_add_finrank_ker (ZMod p) V _ _ _
    ({i : Λ // i ∉ S} → ZMod p)
    (inferInstance : AddCommGroup ({i : Λ // i ∉ S} → ZMod p)) hMod _ π
  have hcod : Module.finrank (ZMod p) ({i : Λ // i ∉ S} → ZMod p) =
      Fintype.card {i : Λ // i ∉ S} := by
    simp
  have hrange : Module.finrank (ZMod p) π.range ≤ Fintype.card {i : Λ // i ∉ S} := by
    rw [← hcod]
    exact Submodule.finrank_le _
  change Module.finrank (ZMod p) V ≤
    Fintype.card {i : Λ // i ∉ S} + Module.finrank (ZMod p) π.ker
  rw [← h]
  exact Nat.add_le_add_right hrange _

theorem fix_mem_centralizer_of_pointwise_noFix {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hT : ∀ a ∈ (ggGamma X hBsN).range,
      (∀ n : X, GGTorusWeylElt p (ggGamma X hBsN).range n →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1) :
    ∀ b : Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  classical
  have := Fact.mk hp
  intro b hb
  set γ := ggGamma X hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBs3 b,
      fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  rw [← ggGamma_eq_one_iff X hBsN]
  refine hT (γ b) ⟨b, rfl⟩ ?_
  intro n hn
  have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨htp, htA⟩ := hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ =
        ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB w hw)
    simpa using Subgroup.inv_mem _ h
  have hφ : Bs.normalizerMonoidHom ⟨n, hnN⟩ ∈ ggAutomizer X Bs :=
    Subgroup.subset_closure ⟨(n : G), n.2, hnN, fun _ => rfl⟩
  have hnb : (n : G) * b * (n : G)⁻¹ = b := congrArg Subtype.val (hb _ hφ)
  have hc := ggGamma_conj X hBsN n b (hWB b b.2)
  rw [← hγ] at hc
  rw [← hc]
  congr 1
  exact Subtype.ext hnb

theorem ggResFix_automizer_J_eq_centralizer_of_image_card {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hJperf : commutator ↥J = ⊤ := hpre.2.2.2.2.2.1.2.2.1
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p (ggGamma J hN).range :=
    isElemAbelian_range hBc hBp (ggGamma J hN)
  have hAI : ∀ a ∈ (ggGamma J hN).range, ∃ φ ∈ I,
      ∀ l : J, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBs3 b,
      fun l => ggBeta_ggQuotHom J hN θ b l⟩
  have hr : p ^ r ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
  have hSCJ : GGTorusSelfCent p (ggGamma J hN).range :=
    GGResHyp.gamma_J_selfCent hH
  have hTB : GGTorusTBGroup p r R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hJperf, hA, hAI, hr, h3, hSCJ⟩
  have hTfix : ∀ a ∈ (ggGamma J hN).range,
      (∀ n : J, GGTorusWeylElt p (ggGamma J hN).range n →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1 :=
    ggTorusNoFixTB_of_torW hnb hTorW J (ggQuotHom θ) (ggGamma J hN).range hTB
  intro b
  constructor
  · intro hb
    exact fix_mem_centralizer_of_pointwise_noFix hp hBs hSC θ hN hBs3 hTfix b hb
  · intro hb
    have hJC : J ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : g = (b : G) := by simpa using hg
      subst g
      exact (Subgroup.mem_centralizer_iff.mp hb j hj).symm
    exact ggResI_automizer_fix b.2 hJC

theorem ggResFix_automizer_J_eq_centralizer_of_A_chart {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResXDatumA p Bs J n) (hn : 3 ≤ n)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1) :
    ∀ b : Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  exact ggResFix_automizer_J_eq_centralizer_of_image_card hH θ hBs3 hLift hTorW hnb
    (hD.card_gamma_ge_pow_three hH.1.1.2.2.2.2.2.1.2.1 hH.1.2.1.2.1
      hH.Bs_le_normalizer_J hn)

theorem ggResFix_automizer_J_eq_centralizer {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r) :
    ∀ b : Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range :=
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hr3).trans
      (hH.pow_le_card_range_gamma_J_of_torusLift θ hLift)
  exact ggResFix_automizer_J_eq_centralizer_of_image_card hH θ hBs3 hLift hTorW hnb h3

theorem ggResFix_automizer_J_eq_D {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r) :
    ∀ b : Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ (b : G) ∈ D := by
  intro b
  constructor
  · intro hb
    have hbC := (ggResFix_automizer_J_eq_centralizer hH θ hBs3 hLift hTorW hnb hr3 b).mp hb
    have hb' : (b : G) ∈ Bs ⊓ Subgroup.centralizer (J : Set G) := ⟨b.2, hbC⟩
    rwa [hI1] at hb'
  · intro hb
    have hb' : (b : G) ∈ Bs ⊓ Subgroup.centralizer (J : Set G) := by
      rwa [hI1]
    exact (ggResFix_automizer_J_eq_centralizer hH θ hBs3 hLift hTorW hnb hr3 b).mpr
      (Subgroup.mem_inf.mp hb').2


theorem ggResFix_automizer_J_fixedSet_eq_D {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r) :
    {b : Bs | ∀ φ ∈ ggAutomizer J Bs, φ b = b} = (D.subgroupOf Bs : Set Bs) := by
  ext b
  rw [Set.mem_setOf_eq]
  change (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ (b : G) ∈ D
  exact ggResFix_automizer_J_eq_D hH hI1 θ hBs3 hLift hTorW hnb hr3 b


theorem finrank_fixedSubmodule_eq_two_of_fix_eq_D
    {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V]
    (ι : Additive E ≃+ V) (A : Subgroup (MulAut E)) (D : Subgroup E)
    (hfix : ∀ b : E, (∀ φ ∈ A, φ b = b) ↔ b ∈ D)
    (hDcard : Nat.card D = p ^ 2) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι A) = 2 := by
  classical
  let f : D → ↥(ggFixedSubmodule (p := p) ι A) := fun d =>
    ⟨ι (Additive.ofMul (d : E)), by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      rw [ggLin_apply_ofMul]
      rw [((hfix (d : E)).mpr d.2) φ hφ]⟩
  have hf_inj : Function.Injective f := by
    intro d1 d2 h
    apply Subtype.ext
    apply Additive.ofMul.injective
    apply ι.injective
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro v
    let b : E := Additive.toMul (ι.symm v.1)
    have hbD : b ∈ D := by
      apply (hfix b).mp
      intro φ hφ
      have hv := (mem_ggFixedSubmodule_iff.mp v.2) φ hφ
      have hv_eq : v.1 = ι (Additive.ofMul b) := by simp [b]
      rw [hv_eq, ggLin_apply_ofMul] at hv
      exact Additive.ofMul.injective (ι.injective hv)
    refine ⟨⟨b, hbD⟩, ?_⟩
    apply Subtype.ext
    simp [f, b]
  let e := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hcard : Nat.card ↥(ggFixedSubmodule (p := p) ι A) = Nat.card D :=
    (Nat.card_congr e).symm
  have hfixedpow : Nat.card ↥(ggFixedSubmodule (p := p) ι A) =
      p ^ Module.finrank (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) := by
    let : Module.Finite (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := ↥(ggFixedSubmodule (p := p) ι A))
    simpa using h
  have hEq : p ^ Module.finrank (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) = p ^ 2 := by
    calc
      p ^ Module.finrank (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) =
          Nat.card ↥(ggFixedSubmodule (p := p) ι A) := hfixedpow.symm
      _ = Nat.card D := hcard
      _ = p ^ 2 := hDcard
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hEq


theorem ggResExact2_finrank_le_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ := by
  classical
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, αL i (hL i) = 2 := by
    intro i
    rw [hpairL i i, hCL.1 i]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) (E := ↥Bs) (V := V)
    ι (fun i : {i : Λ // i ∉ S} => φL i) (fun i => hL i) (fun i => αL i)
    (fun i w => hlinL i w) hdiagJ hp2 (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => αL i)
  rw [hker] at hle
  rw [hfix] at hle
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  have hcard : Fintype.card {i : Λ // i ∉ S} + 2 = Fintype.card Λ := by
    rw [hcomp, hS]
    omega
  calc
    Module.finrank (ZMod p) V ≤ Fintype.card {i : Λ // i ∉ S} + 2 := hle
    _ = Fintype.card Λ := hcard

theorem ggResExact2_cartan_singular
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have haxis := ggResL_rank_core_add_one hH hlinL hpairL hCL.1 hgenL
  have hdimΛ : Module.finrank (ZMod p) V ≤ Fintype.card Λ :=
    ggResExact2_finrank_le_card hp2 ι hCL φL hL αL hlinL hpairL hS hgenJ hfix
  have hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) < Fintype.card Λ := by
    omega
  exact ggIntCartan_A_or_E6_of_rank_lt hML hCL hp2 hrank


theorem ggResExact2_cartan_singular_K_base
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, CK (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have haxis := ggResK_rank_core_add_one hH hlinK hpairK hCK.1 hgenK
  have hdim : Module.finrank (ZMod p) V ≤ Fintype.card Λ :=
    ggResExact2_finrank_le_card hp2 ι hCK φK hK αK hlinK hpairK hS hgenJ hfix
  have hrank : Matrix.rank (CK.map (Int.castRingHom (ZMod p))) < Fintype.card Λ := by
    omega
  exact ggIntCartan_A_or_E6_of_rank_lt hMK hCK hp2 hrank

theorem ggResExact2_cartan_singular_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (φK : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs)
    (hK : ({i : Λ // i ∉ S} ⊕ Λa) → V)
    (αK : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod p) V)
    (hlinK : ∀ o w, ggLin (p := p) ι (φK o) w = w - αK o w • hK o)
    (hpairK : ∀ o o', αK o (hK o') = (CK o o' : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hΛa : 2 ≤ Nat.card Λa)
    (hdimL : Module.finrank (ZMod p) V ≤ Fintype.card Λ) :
    (∃ (n : ℕ) (e : Fin n ≃ {i : Λ // i ∉ S} ⊕ Λa), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, CK (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
      ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have haxis := ggResK_rank_core_add_one hH hlinK hpairK hCK.1 hgenK
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  have hcardMK : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) =
      Fintype.card Λ - 2 + Fintype.card Λa := by
    rw [Fintype.card_sum, hcomp, hS]
  have hleMK : Fintype.card Λ ≤ Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) := by
    rw [hcardMK]
    have : 2 ≤ Fintype.card Λa := by simpa [Nat.card_eq_fintype_card] using hΛa
    omega
  have hrank : Matrix.rank (CK.map (Int.castRingHom (ZMod p))) <
      Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) := by
    omega
  exact ggIntCartan_A_or_E6_of_rank_lt hMK hCK hp2 hrank

theorem ggResExact2_cartan_singular_K_of_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2)
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (hMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (φK : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs)
    (hK : ({i : Λ // i ∉ S} ⊕ Λa) → V)
    (αK : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod p) V)
    (hlinK : ∀ o w, ggLin (p := p) ι (φK o) w = w - αK o w • hK o)
    (hpairK : ∀ o o', αK o (hK o') = (CK o o' : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hΛa : 2 ≤ Nat.card Λa) :
    (∃ (n : ℕ) (e : Fin n ≃ {i : Λ // i ∉ S} ⊕ Λa), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, CK (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
      ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdimL : Module.finrank (ZMod p) V ≤ Fintype.card Λ :=
    ggResExact2_finrank_le_card hp2 ι hCL φL hL αL hlinL hpairL hS hgenJ hfix
  exact ggResExact2_cartan_singular_K (hH := hH) (Λ := Λ) (S := S) (Λa := Λa)
    (V := V) (ι := ι) (hMK := hMK) (hCK := hCK) (φK := φK) (hK := hK)
    (αK := αK) (hlinK := hlinK) (hpairK := hpairK) (hgenK := hgenK)
    (hS := hS) (hΛa := hΛa) (hdimL := hdimL)

theorem ggResExact2_fix_eq_two_of_fix_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2 := by
  have hDle : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  have hfixD : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ b ∈ D.subgroupOf Bs := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    rw [hfixJ b, ← hI1]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hDcard' : Nat.card (D.subgroupOf Bs) = p ^ 2 := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
  exact finrank_fixedSubmodule_eq_two_of_fix_eq_D ι (ggAutomizer J Bs)
    (D.subgroupOf Bs) hfixD hDcard'

theorem ggResExact2_fix_eq_two
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2 :=
  ggResExact2_fix_eq_two_of_fix_centralizer hH hI1
    (fun b => ggResFix_automizer_J_eq_centralizer hH θ hBs3 hLift hTorW hnb hr3 b) ι

theorem ggResExact2_cartan_singular_of_I1
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i))) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  have hfix := ggResExact2_fix_eq_two hH hI1 θ hBs3 hLift hTorW hnb hr3 ι
  exact ggResExact2_cartan_singular (hH := hH) (Λ := Λ) (S := S) (V := V) (ι := ι)
    (hML := hML) (hCL := hCL) (φL := φL) (hL := hL) (αL := αL)
    (hlinL := hlinL) (hpairL := hpairL) (hgenL := hgenL) (hS := hS)
    (hgenJ := hgenJ) (hfix := hfix)

theorem ggResExact2_cartan_singular_K_base_of_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φL : Λ → MulAut ↥Bs) (hL : Λ → V)
      (αL : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      (∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i) ∧
      (∀ i, GGIsReflection p (φL i)) ∧
      (∀ i j, αL i (hL j) = (CL i j : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer K Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i) ∧
      ggAutomizer K Bs = Subgroup.closure (Set.range φL) ∧
      ((∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
        ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
      (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j)) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, hML, hCL, -, -, -, hlin, hrefl, hpair, -, -, ⟨fL, hfL⟩, -, hclosL, -, -, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hfix := ggResExact2_fix_eq_two hH hI1 θ hBs3 hLift hTorW hnb hr3 ι
  refine ⟨Λ, i1, i2, ML, CL, V, i5, i6, ι,
    (fun i => φ (Sum.inl i)), (fun i => h (Sum.inl i)), (fun i => α (Sum.inl i)),
    hML, hCL, (fun i w => hlin (Sum.inl i) w), (fun i => hrefl (Sum.inl i)),
    hpair, ⟨fL, hfL⟩, hclosL, ?_⟩
  exact ggResExact2_cartan_singular_K_base (hH := hH) (Λ := Λ) (S := S) (V := V) (ι := ι)
    (hMK := hML) (hCK := hCL) (φK := fun i => φ (Sum.inl i))
    (hK := fun i => h (Sum.inl i)) (αK := fun i => α (Sum.inl i))
    (hlinK := fun i w => hlin (Sum.inl i) w) (hpairK := hpair)
    (hgenK := hclosL) (hS := hS) (hgenJ := hclosJ) (hfix := hfix)

theorem ggResExact2_cartan_singular_of_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φL : Λ → MulAut ↥Bs) (hL : Λ → V)
      (αL : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      (∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i) ∧
      (∀ i, GGIsReflection p (φL i)) ∧
      (∀ i j, αL i (hL j) = (CL i j : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φL) ∧
      ((∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
        ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
      (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j)) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, hML, hCL, -, -, -, hlin, hrefl, hpair, -, -, ⟨fL, hfL⟩, -, hclosL, -, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  refine ⟨Λ, i1, i2, ML, CL, V, i5, i6, ι,
    (fun i => φ (Sum.inl i)), (fun i => h (Sum.inl i)), (fun i => α (Sum.inl i)),
    hML, hCL, (fun i w => hlin (Sum.inl i) w), (fun i => hrefl (Sum.inl i)),
    hpair, ⟨fL, hfL⟩, hclosL, ?_⟩
  exact ggResExact2_cartan_singular_of_I1 (hH := hH) (hI1 := hI1)
    (θ := θ) (hBs3 := hBs3) (hLift := hLift) (hTorW := hTorW) (hnb := hnb) (hr3 := hr3)
    (Λ := Λ) (S := S) (V := V) (ι := ι) (hML := hML) (hCL := hCL)
    (φL := fun i => φ (Sum.inl i)) (hL := fun i => h (Sum.inl i))
    (αL := fun i => α (Sum.inl i))
    (hlinL := fun i w => hlin (Sum.inl i) w) (hpairL := hpair)
    (hgenL := hclosL) (hS := hS)
    (hgenJ := hclosJ)

theorem ggResExact2_typed_dichotomy_L_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    GGResLeviDatumCard 2 p Bs L J K ggSelAny (ggTypLADvd p) ∨
    (p = 3 ∧ GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypLE6) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hfix := ggResExact2_fix_eq_two_of_fix_centralizer hH hI1 hfixJ ι
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumCard 2 p Bs L J K ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  have hsing := ggResExact2_cartan_singular (hH := hH) (Λ := Λ) (S := S) (V := V) (ι := ι)
    (hML := hML) (hCL := hCL) (φL := fun i => φ (Sum.inl i))
    (hL := fun i => h (Sum.inl i)) (αL := fun i => α (Sum.inl i))
    (hlinL := fun i w => hlin (Sum.inl i) w) (hpairL := hpair)
    (hgenL := hclosL) (hS := hS) (hgenJ := hclosJ) (hfix := hfix)
  rcases ggTypLADvd_or_E6_of_cartan_singular hCL hsing with ⟨hA, hpdiv⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p) ⟨hA, hpdiv⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩

theorem ggResExact2_typed_dichotomy_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    GGResLeviDatumCard 2 p Bs L J K ggSelAny (ggTypLADvd p) ∨
    (p = 3 ∧ GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypLE6) :=
  ggResExact2_typed_dichotomy_L_of_fixed hH hI1
    (fun b => ggResFix_automizer_J_eq_centralizer hH θ hBs3 hLift hTorW hnb hr3 b) hD

theorem ggResExact2_typed_dichotomy_K_base_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypAny) :
    GGResLeviDatumCard 2 p Bs K J L ggSelAny (ggTypLADvd p) ∨
    (p = 3 ∧ GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypLE6) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hfix := ggResExact2_fix_eq_two_of_fix_centralizer hH hI1 hfixJ ι
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumCard 2 p Bs K J L ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  have hsing := ggResExact2_cartan_singular_K_base (hH := hH) (Λ := Λ) (S := S)
    (V := V) (ι := ι) (hMK := hML) (hCK := hCL)
    (φK := fun i => φ (Sum.inl i)) (hK := fun i => h (Sum.inl i))
    (αK := fun i => α (Sum.inl i)) (hlinK := fun i w => hlin (Sum.inl i) w)
    (hpairK := hpair) (hgenK := hclosL) (hS := hS) (hgenJ := hclosJ) (hfix := hfix)
  rcases ggTypLADvd_or_E6_of_cartan_singular hCL hsing with ⟨hA, hpdiv⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p) ⟨hA, hpdiv⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩

theorem ggResExact2_typed_dichotomy_K_base
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypAny) :
    GGResLeviDatumCard 2 p Bs K J L ggSelAny (ggTypLADvd p) ∨
    (p = 3 ∧ GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypLE6) :=
  ggResExact2_typed_dichotomy_K_base_of_fixed hH hI1
    (fun b => ggResFix_automizer_J_eq_centralizer hH θ hBs3 hLift hTorW hnb hr3 b) hD

theorem ggResExact2_cartan_singular_K_of_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
      (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
      (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
      (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V)
      (φK : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs)
      (hK : ({i : Λ // i ∉ S} ⊕ Λa) → V)
      (αK : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod p) V),
      GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ o w, ggLin (p := p) ι (φK o) w = w - αK o w • hK o) ∧
      (∀ o, GGIsReflection p (φK o)) ∧
      (∀ o o', αK o (hK o') = (CK o o' : ZMod p)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φK o) ∧
      ggAutomizer K Bs = Subgroup.closure (Set.range φK) ∧
      (2 ≤ Nat.card Λa →
        ((∃ (n : ℕ) (e : Fin n ≃ ({i : Λ // i ∉ S} ⊕ Λa)), 1 ≤ n ∧ p ∣ n + 1 ∧
          ∀ i j, CK (e i) (e j) = CartanMatrix.A n i j) ∨
        (p = 3 ∧ ∃ e : Fin 6 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
          ∀ i j, CK (e i) (e j) = CartanMatrix.E 6 i j))) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, -, -, -, hCL, hMK, hCK, -, hlin, hrefl, hpair, hpairK, -, -,
    ⟨fK, hfK⟩, -, hclosK, -, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hclosK' : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id))) := by
    rw [hclosK, Sum.range_eq]
    rfl
  have hfix := ggResExact2_fix_eq_two hH hI1 θ hBs3 hLift hTorW hnb hr3 ι
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdimL : Module.finrank (ZMod p) V ≤ Fintype.card Λ :=
    ggResExact2_finrank_le_card hp2 ι hCL (fun i => φ (Sum.inl i))
      (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
      (fun i w => hlin (Sum.inl i) w) hpair hS hclosJ hfix
  refine ⟨Λ, i1, i2, S, Λa, i3, i4, MK, CK, V, i5, i6, ι,
    (fun o => φ (o.map Subtype.val id)), (fun o => h (o.map Subtype.val id)),
    (fun o => α (o.map Subtype.val id)),
    hMK, hCK, (fun o w => hlin (o.map Subtype.val id) w),
    (fun o => hrefl (o.map Subtype.val id)), hpairK, ⟨fK, hfK⟩, hclosK', ?_⟩
  intro hΛa
  exact ggResExact2_cartan_singular_K (hH := hH) (Λ := Λ) (S := S) (Λa := Λa)
    (V := V) (ι := ι) (hMK := hMK) (hCK := hCK)
    (φK := fun o => φ (o.map Subtype.val id))
    (hK := fun o => h (o.map Subtype.val id))
    (αK := fun o => α (o.map Subtype.val id))
    (hlinK := fun o w => hlin (o.map Subtype.val id) w)
    (hpairK := hpairK) (hgenK := hclosK') (hS := hS) (hΛa := hΛa)
    (hdimL := hdimL)

section E6


theorem ggResFix_automizer_J_eq_centralizer_E6_three
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hInner : GGInnerDiagOn Bs J)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J))
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    ∀ b : Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM := ggInnerDiagOn_relabel hRig hInner hlab hhas
  have hM1 := largeEvenMarking_and_labelAll
    (S := fun l => l = lab)
    (P' := fun R _ _ _ => GGTorusLift 3 5 R)
    (fun l _ hl => by subst l; exact largeEvenLabelAll_torusLift_E6_three htag h3)
    (fun _ _ _ _ _ _ h => h.1) hM
  have h3M : 3 ∣ ggTorM lab := by simpa [ggTorM, htag] using h3
  have hM2 := largeEvenMarking_and_labelAll
    (S := fun l => l = lab)
    (P' := fun R _ I _ => GGTorusTorW 3 5 (ggTorM lab) 6
      CartanMatrix.E₆ CoxeterMatrix.E₆ R I)
    (fun l _ hl => by subst l; exact ggTBTorE6_holds lab hlab htag h3M)
    (fun _ _ _ _ _ _ h => h.1.1) hM1
  obtain ⟨_,l,hl,hraw⟩ := hM2
  obtain ⟨R,iR,I,F,hQ⟩ := largeEvenRawDatum_exists hraw
  let := iR
  obtain ⟨_,_,θ,⟨⟨hlEq,hN,hBs3⟩,hLift⟩,hTorW⟩ := hQ
  exact ggResFix_automizer_J_eq_centralizer hH θ hBs3 hLift hTorW
    (by decide +kernel) (by omega)

theorem ggResFix_automizer_J_eq_centralizer_E6_three_of_selected
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel S2MathAs51642Interfaces.E6Three 3 Bs L)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J))
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    ∀ b : Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
  ggResFix_automizer_J_eq_centralizer_E6_three hH hRig
    (q1E6Three_holds G 3 B Bs x L D J hH.1 hM) hlab hhas htag h3

end E6

theorem card_fixedSubmodule_eq_card_of_fix_eq {p : ℕ} [Fact p.Prime]
    {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive E ≃+ V) (A : Subgroup (MulAut E)) (D : Subgroup E)
    (hfix : ∀ b : E, (∀ φ ∈ A, φ b = b) ↔ b ∈ D) :
    Nat.card ↥(ggFixedSubmodule (p := p) ι A) = Nat.card D := by
  classical
  let f : D → ↥(ggFixedSubmodule (p := p) ι A) := fun d =>
    ⟨ι (Additive.ofMul (d : E)), by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      rw [ggLin_apply_ofMul]
      rw [((hfix (d : E)).mpr d.2) φ hφ]⟩
  have hf_inj : Function.Injective f := by
    intro d1 d2 h
    apply Subtype.ext
    apply Additive.ofMul.injective
    apply ι.injective
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro v
    let b : E := Additive.toMul (ι.symm v.1)
    have hbD : b ∈ D := by
      apply (hfix b).mp
      intro φ hφ
      have hv := (mem_ggFixedSubmodule_iff.mp v.2) φ hφ
      have hv_eq : v.1 = ι (Additive.ofMul b) := by simp [b]
      rw [hv_eq, ggLin_apply_ofMul] at hv
      exact Additive.ofMul.injective (ι.injective hv)
    refine ⟨⟨b, hbD⟩, ?_⟩
    apply Subtype.ext
    simp [f, b]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

theorem finrank_fixedSubmodule_le_three_of_fix_eq_of_card_le {p : ℕ} [Fact p.Prime]
    {E : Type} [Group E] [Finite E] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive E ≃+ V) (A : Subgroup (MulAut E)) (D : Subgroup E)
    (hfix : ∀ b : E, (∀ φ ∈ A, φ b = b) ↔ b ∈ D)
    (hcard : Nat.card D ≤ p ^ 3) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι A) ≤ 3 := by
  classical
  let W := ggFixedSubmodule (p := p) ι A
  let : Finite V := Finite.of_equiv (Additive E) ι.toEquiv
  have hcardW : Nat.card ↥W = Nat.card D :=
    card_fixedSubmodule_eq_card_of_fix_eq ι A D hfix
  have hpow : Nat.card ↥W = p ^ Module.finrank (ZMod p) ↥W := by
    let : Module.Finite (ZMod p) ↥W := Module.Finite.of_finite
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥W))
  have hle : p ^ Module.finrank (ZMod p) ↥W ≤ p ^ 3 := by
    rw [← hpow, hcardW]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle


theorem ggResExact2_fix_le_three {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) ≤ 3 := by
  classical
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  let D' : Subgroup ↥Bs := C.subgroupOf Bs
  have hfixC : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ b ∈ D' := by
    intro b
    rw [hfixJ b, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hcardC : Nat.card C ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hcardD' : Nat.card D' ≤ p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcardC
  exact finrank_fixedSubmodule_le_three_of_fix_eq_of_card_le ι (ggAutomizer J Bs) D' hfixC hcardD'

theorem ggResExact2_finrank_le_card_add_one {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) ≤ 3) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
  classical
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, αL i (hL i) = 2 := by
    intro i
    rw [hpairL i i, hCL.1 i]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) (E := ↥Bs) (V := V)
    ι (fun i : {i : Λ // i ∉ S} => φL i) (fun i => hL i) (fun i => αL i)
    (fun i w => hlinL i w) hdiagJ hp2 (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => αL i)
  rw [hker] at hle
  have hle' : Module.finrank (ZMod p) V ≤ Fintype.card {i : Λ // i ∉ S} + 3 :=
    hle.trans (Nat.add_le_add_left hfix _)
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  calc
    Module.finrank (ZMod p) V ≤ Fintype.card {i : Λ // i ∉ S} + 3 := hle'
    _ = (Fintype.card Λ - S.card) + 3 := by rw [hcomp]
    _ = Fintype.card Λ + 1 := by rw [hS]; omega

theorem ggResExact2_fix_eq_three_of_finrank_eq_card_add_one {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G} (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1)
    (hfixle : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) ≤ 3) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 := by
  classical
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, αL i (hL i) = 2 := by
    intro i
    rw [hpairL i i, hCL.1 i]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) (E := ↥Bs) (V := V)
    ι (fun i : {i : Λ // i ∉ S} => φL i) (fun i => hL i) (fun i => αL i)
    (fun i w => hlinL i w) hdiagJ hp2 (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => αL i)
  rw [hker] at hle
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  rw [hcomp, hS] at hle
  omega

theorem ggResExact2_finrank_eq_card_add_one_of_L {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hfixle := ggResExact2_fix_le_three hH hfixJ ι
  have hdimle := ggResExact2_finrank_le_card_add_one hp2 ι hCL φL hL αL hlinL hpairL
    hS hgenJ hfixle
  have haxis := ggResL_rank_core_add_one hH hlinL hpairL hCL.1 hgenL
  rw [hrank] at haxis
  omega

theorem ggResExact2_finrank_eq_card_add_one_of_K_base {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CK.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hfixle := ggResExact2_fix_le_three hH hfixJ ι
  have hdimle := ggResExact2_finrank_le_card_add_one hp2 ι hCK φK hK αK hlinK hpairK
    hS hgenJ hfixle
  have haxis := ggResK_rank_core_add_one hH hlinK hpairK hCK.1 hgenK
  rw [hrank] at haxis
  omega

theorem ggResExact2_fix_eq_three_of_L {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdim := ggResExact2_finrank_eq_card_add_one_of_L hH ι hCL φL hL αL hlinL hpairL
    hgenL hS hgenJ hfixJ hrank
  exact ggResExact2_fix_eq_three_of_finrank_eq_card_add_one hp2 ι hCL φL hL αL hlinL hpairL
    hS hgenJ hdim (ggResExact2_fix_le_three hH hfixJ ι)

theorem ggResExact2_fix_eq_three_of_K_base {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CK.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdim := ggResExact2_finrank_eq_card_add_one_of_K_base hH ι hCK φK hK αK hlinK hpairK
    hgenK hS hgenJ hfixJ hrank
  exact ggResExact2_fix_eq_three_of_finrank_eq_card_add_one hp2 ι hCK φK hK αK hlinK hpairK
    hS hgenJ hdim (ggResExact2_fix_le_three hH hfixJ ι)

theorem ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (hfix3 : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  let D' : Subgroup ↥Bs := C.subgroupOf Bs
  have hfixC : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ b ∈ D' := by
    intro b
    rw [hfixJ b, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hcardW : Nat.card ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = Nat.card D' :=
    card_fixedSubmodule_eq_card_of_fix_eq ι (ggAutomizer J Bs) D' hfixC
  have hpow : Nat.card ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) =
      p ^ Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) := by
    let : Module.Finite (ZMod p) ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) :=
      Module.Finite.of_finite
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs))))
  have hcardD' : Nat.card D' = p ^ 3 := by
    rw [← hcardW, hpow, hfix3]
  have hcardC : Nat.card C = Nat.card D' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [hcardC, hcardD']

theorem ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3) :
    D < Bs ⊓ Subgroup.centralizer (J : Set G) := by
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hle : D ≤ C := by
    rw [hD]
    exact inf_le_inf hBBs le_rfl
  have hcardD : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hlt : Nat.card D < Nat.card C := by
    rw [hcardD, hcardC]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
  exact lt_of_le_of_ne hle
    (fun h => (ne_of_lt hlt) (congrArg (fun H : Subgroup G => Nat.card ↥H) h))


theorem rank_map_eq_card_of_det_ne_zero {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {C : Matrix Λ Λ ℤ} (hdet : (C.det : ZMod p) ≠ 0) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
  apply Matrix.rank_of_det_ne_zero
  simpa [Int.cast_det] using hdet

theorem ggResExact2_finrank_eq_card_add_one_of_L_of_det {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CL.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 :=
  ggResExact2_finrank_eq_card_add_one_of_L hH ι hCL φL hL αL hlinL hpairL hgenL hS hgenJ
    hfixJ (rank_map_eq_card_of_det_ne_zero hdet)

theorem ggResExact2_finrank_eq_card_add_one_of_K_base_of_det {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CK.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 :=
  ggResExact2_finrank_eq_card_add_one_of_K_base hH ι hCK φK hK αK hlinK hpairK hgenK hS hgenJ
    hfixJ (rank_map_eq_card_of_det_ne_zero hdet)

theorem ggResExact2_nonI1_L_of_det {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CL.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 ∧
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
      D < Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hdim := ggResExact2_finrank_eq_card_add_one_of_L_of_det hH ι hCL φL hL αL hlinL hpairL
    hgenL hS hgenJ hfixJ hdet
  have hfix3 := ggResExact2_fix_eq_three_of_L hH ι hCL φL hL αL hlinL hpairL hgenL hS hgenJ
    hfixJ (rank_map_eq_card_of_det_ne_zero hdet)
  have hcard := ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three hfixJ ι hfix3
  exact ⟨hdim, hfix3, hcard,
    ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three hH hcard⟩

theorem ggResExact2_nonI1_K_base_of_det {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CK.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 ∧
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
      D < Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hdim := ggResExact2_finrank_eq_card_add_one_of_K_base_of_det hH ι hCK φK hK αK hlinK
    hpairK hgenK hS hgenJ hfixJ hdet
  have hfix3 := ggResExact2_fix_eq_three_of_K_base hH ι hCK φK hK αK hlinK hpairK hgenK hS
    hgenJ hfixJ (rank_map_eq_card_of_det_ne_zero hdet)
  have hcard := ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three hfixJ ι hfix3
  exact ⟨hdim, hfix3, hcard,
    ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three hH hcard⟩


theorem ggResExact2_nonI1_L_of_datum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
      (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
      (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
      (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
      (S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧
        GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
        ggTypAny ML MK ∧
        (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
        (∀ o, GGIsReflection p (φ o)) ∧
        (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
        (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
          α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
        ggSelAny (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i))
          (LinearIndependent (ZMod p) h) ∧
        (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
          ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
        (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
          ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
        ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
        ggAutomizer K Bs = Subgroup.closure
          (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
            Set.range fun a : Λa => φ (Sum.inr a)) ∧
        GGDeletedConnectedS ML S ∧
        ggAutomizer J Bs = Subgroup.closure
          (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))) ∧
      ((CL.det : ZMod p) ≠ 0 →
        Module.finrank (ZMod p) V = Fintype.card Λ + 1 ∧
        Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 ∧
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
        D < Bs ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    fL, fK, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  refine ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    ⟨hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      fL, fK, hclosL, hclosK, hconn, hclosJ⟩, ?_⟩
  intro hdet
  exact ggResExact2_nonI1_L_of_det hH ι hCL (fun i => φ (Sum.inl i))
    (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    (fun i w => hlin (Sum.inl i) w) hpair hclosL hS hclosJ hfixJ hdet


theorem ggResExact2_nonI1_K_base_of_datum {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumCard 2 p Bs K J L ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ)
      (Λa : Type) (_ : Fintype Λa) (_ : DecidableEq Λa)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
      (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
      (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
      (S.card = 2 ∧ 1 ≤ Nat.card Λa ∧ Nat.card Λa ≤ 3 ∧
        GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
        ggTypAny ML MK ∧
        (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
        (∀ o, GGIsReflection p (φ o)) ∧
        (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
        (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
          α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
        ggSelAny (LinearIndependent (ZMod p) fun i : Λ => h (Sum.inl i))
          (LinearIndependent (ZMod p) h) ∧
        (∃ fL : ML.Group ≃* ↥(ggAutomizer K Bs),
          ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
        (∃ fK : MK.Group ≃* ↥(ggAutomizer L Bs),
          ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
        ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
        ggAutomizer L Bs = Subgroup.closure
          (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
            Set.range fun a : Λa => φ (Sum.inr a)) ∧
        GGDeletedConnectedS ML S ∧
        ggAutomizer J Bs = Subgroup.closure
          (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))) ∧
      ((CL.det : ZMod p) ≠ 0 →
        Module.finrank (ZMod p) V = Fintype.card Λ + 1 ∧
        Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 ∧
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
        D < Bs ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    fL, fK, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  refine ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    ⟨hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      fL, fK, hclosL, hclosK, hconn, hclosJ⟩, ?_⟩
  intro hdet
  exact ggResExact2_nonI1_K_base_of_det hH ι hCL (fun i => φ (Sum.inl i))
    (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    (fun i w => hlin (Sum.inl i) w) hpair hclosL hS hclosJ hfixJ hdet



theorem ggResExact3_typed_dichotomy_L_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    (GGResLeviDatumExact3 p Bs L J K ggSelAny (ggTypLADvd p) ∨
      (p = 3 ∧ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypLE6)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have haxis := ggResL_rank_core_add_one hH
    (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  obtain ⟨-, -, -, hsing, hcent, -⟩ := ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
    haxis S hS3 hclosJ hfwd
  refine ⟨?_, hcent⟩
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumExact3 p Bs L J K ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
  rcases hsing with ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p)
      ⟨hA, by simpa [Nat.card_eq_fintype_card] using hpd⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩

theorem ggResExact3_typed_dichotomy_K_base_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    (GGResLeviDatumExact3 p Bs K J L ggSelAny (ggTypLADvd p) ∨
      (p = 3 ∧ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypLE6)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have haxis := ggResK_rank_core_add_one hH
    (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  obtain ⟨-, -, -, hsing, hcent, -⟩ := ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
    haxis S hS3 hclosJ hfwd
  refine ⟨?_, hcent⟩
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumExact3 p Bs K J L ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
  rcases hsing with ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p)
      ⟨hA, by simpa [Nat.card_eq_fintype_card] using hpd⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩


theorem ggResLeviDatumExact3_E6_card_bstar_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X Y : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumExact3 p Bs X J Y ggSelAny ggTypLE6) :
    Nat.card Bs = p ^ 6 := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have haxis : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) + 1 ≤
      Module.finrank (ZMod p) V := by
    rcases hX with hX | hX
    · subst X
      exact ggResL_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w)
        hpairL hCLL.1 hclosL
    · subst X
      exact ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w)
        hpairL hCLL.1 hclosL
  obtain ⟨hdim, -, -, -, -, -⟩ := ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
    haxis S hS3 hclosJ hfwd
  obtain ⟨e, he⟩ := htyp
  have hΛ : Fintype.card Λ = 6 := by
    simpa using Fintype.card_congr e.symm
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V, hdim, hΛ]


theorem GGConfig.centralizer_inter_eq_D_of_typeA_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  have hBle : B ≤ Bs := hcfg.2.1.1
  have hmark : LargeEvenMarking L (fun lab R _ I F θ =>
      GGTypeASplitLabel p lab ∧ LargeEvenSplit p lab ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) := by
    refine ⟨hperf, lab, hlab, ?_⟩
    apply largeEvenRawDatum_mono (Q' := fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          GGTypeASplitLabel p lab ∧ LargeEvenSplit p lab ∧
            B ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) ?_ hraw
    rintro R _ I F hq
    obtain ⟨hsimple, hnab, θ, hP⟩ := hq
    obtain ⟨hA, hN, hact⟩ := hP
    obtain ⟨htag, hpn⟩ := hA
    have hsplit : LargeEvenSplit p lab := by
      refine Or.inl ⟨?_, hpn⟩
      rw [htag]
      trivial
    have htype : GGTypeASplitLabel p lab := by
      by_cases hdvd : p ∣ lab.rank + 1
      · exact Or.inr ⟨htag, hpn, hdvd⟩
      · exact Or.inl (Or.inl ⟨htag, hpn, hdvd⟩)
    refine ⟨hsimple, hnab, θ, ?_⟩
    refine ⟨htype, hsplit, hBle.trans hN, ?_⟩
    intro b hb
    exact hact b (hBle hb)
  exact (GGStdSubFixedJOn_typeA_split G p B Bs x L D J hcfg hmark).1

theorem GGResHyp.fix_mem_centralizer_J_of_typeA_split_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, _, _, θ, hpred, _, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag, hpq⟩ := hpred
  have hlabeq : lab = ⟨.A, lab.rank, lab.n⟩ := by
    cases lab
    simp_all
  have hmark : GGInnerDiagOnLabel
      (fun _ lab' => lab' = ⟨.A, lab.rank, lab.n⟩) p Bs L := by
    refine ⟨hperf, lab, hlab, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨hs, hn, θ, _, hN, hact⟩ := hq
      exact ⟨hs, hn, θ, hlabeq, hN, hact⟩) hraw
  exact hH.fix_mem_centralizer_J_of_typeA_marking hpq hmark

theorem ggResExactThree_absurd_of_typeA_split_L_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  have hfwd := hH.fix_mem_centralizer_J_of_typeA_split_marking hL
  have hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
    rcases hD with hD | hD
    · exact (ggResExact3_typed_dichotomy_L_of_fixed hH hfwd hD).2
    · exact (ggResExact3_typed_dichotomy_K_base_of_fixed hH hfwd hD).2
  have hEq := hH.1.centralizer_inter_eq_D_of_typeA_marking hL
  have hDcard : Nat.card ↥D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hEq, hDcard] at hcent
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
  omega


theorem GGResLeviDatumCard.dependent_A_or_E6
    {G : Type} [Group G] {p k : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hp2 : p ≠ 2)
    (hD : GGResLeviDatumCard k p Bs L J K ggSelDep typ) :
    GGResLeviDatumCard k p Bs L J K ggSelDep
        (fun ML MK => typ ML MK ∧ ggTypLADvd p ML MK) ∨
      (p = 3 ∧ GGResLeviDatumCard k p Bs L J K ggSelDep
        (fun ML MK => typ ML MK ∧ ggTypLE6 ML MK)) := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  obtain ⟨κ, hrel, o, ho⟩ := Fintype.not_linearIndependent_iff.mp hsel
  have hker : ∃ κ : Λ → ZMod p, κ ≠ 0 ∧
      ∀ i, ∑ j, (CL i j : ZMod p) * κ j = 0 := by
    refine ⟨κ, ?_, ?_⟩
    · intro hz
      exact ho (congrFun hz o)
    · intro i
      have hv := congrArg (α (Sum.inl i)) hrel
      simpa only [map_sum, map_smul, map_zero, hpair, smul_eq_mul, mul_comm] using hv
  have htypes := ggTypLADvd_or_E6_of_cartan_singular hCL
    (ggIntCartan_A_or_E6_of_nonzero_kernel hML hCL hp2 hker)
  let pack (typ' : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop)
      (ht : typ' ML MK) : GGResLeviDatumCard k p Bs L J K ggSelDep typ' :=
    ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hA1, hA3, hML, hCL, hMK, hCK, ht, hlin, hrefl, hpair, hpairK,
      hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩
  rcases htypes with ⟨hA, hdiv⟩ | ⟨hp3, hE⟩
  · exact Or.inl (pack (fun ML MK => typ ML MK ∧ ggTypLADvd p ML MK)
      ⟨htyp, hA, hdiv⟩)
  · exact Or.inr ⟨hp3, pack (fun ML MK => typ ML MK ∧ ggTypLE6 ML MK)
      ⟨htyp, hE⟩⟩

private lemma zmod3_two_ne_zero : ((2 : ℤ) : ZMod 3) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  norm_num at h

private lemma zmod3_four_ne_zero : ((4 : ℤ) : ZMod 3) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  norm_num at h


theorem alpha_y_eq_zero_of_fixed
    {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} {y : G}
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hclos : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hy : y ∈ Bs)
    (hyfix : ∀ ψ ∈ ggAutomizer K Bs,
      ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩) :
    ∀ i, α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
  intro i
  have hφmem : φ i ∈ ggAutomizer K Bs := by
    rw [hclos]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hfixV : ggLin (p := 3) ι (φ i)
      (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
      ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) :=
    (ggLin_fix_iff (p := 3) ι (φ i) (⟨y, hy⟩ : ↥Bs)).mp (hyfix (φ i) hφmem)
  have hsl := hlin i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))
  rw [hfixV] at hsl
  have hzero : α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) • h i = 0 :=
    sub_eq_self.mp hsl.symm
  have hh : h i ≠ 0 := by
    intro h0
    have hp := hpair i i
    rw [h0, map_zero, hCKK.1 i] at hp
    exact zmod3_two_ne_zero hp.symm
  exact (smul_eq_zero.mp hzero).resolve_right hh

theorem K_fixedLine_of_rankFive_nondegenerate
    {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} {y : G}
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK)
    (hcardIdx : Fintype.card Idx = 5)
    (hdet : (CK.map (Int.castRingHom (ZMod 3))).det ≠ 0)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hclos : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hy : y ∈ Bs) (hy1 : y ≠ 1)
    (hαy : ∀ i, α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0)
    (hcardV : Module.finrank (ZMod 3) V = 6) :
    ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y := by
  classical
  let yB : ↥Bs := ⟨y, hy⟩
  let yV : V := ι (Additive.ofMul yB)
  have hyV : yV ≠ 0 := by
    intro h0
    have h1 : yB = 1 := by
      apply Additive.ofMul.injective
      apply ι.injective
      simpa [yV, yB] using h0
    exact hy1 (by simpa [yB] using Subtype.ext_iff.mp h1)
  let F : V →ₗ[ZMod 3] (Idx → ZMod 3) := LinearMap.pi α
  let ev : Idx → Module.Dual (ZMod 3) (Idx → ZMod 3) := fun i =>
    { toFun := fun v => v i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hliF : LinearIndependent (ZMod 3) (fun j : Idx => F (h j)) := by
    apply linearIndependent_of_det_ne_zero
      (h := fun j : Idx => F (h j)) (α := ev)
    have hmat : (Matrix.of fun i j : Idx => ev i (F (h j))) =
        CK.map (Int.castRingHom (ZMod 3)) := by
      ext i j
      simp [ev, F, hpair]
    rw [hmat]
    exact hdet
  have hspan_le : Submodule.span (ZMod 3) (Set.range fun j : Idx => F (h j)) ≤ F.range := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨h j, rfl⟩
  have hrange_ge : 5 ≤ Module.finrank (ZMod 3) F.range := by
    have hmono := Submodule.finrank_mono hspan_le
    rw [finrank_span_eq_card hliF, hcardIdx] at hmono
    exact hmono
  have hrange_le : Module.finrank (ZMod 3) F.range ≤ 5 := by
    have h := Submodule.finrank_le F.range
    rw [Module.finrank_pi, hcardIdx] at h
    exact h
  have hrange : Module.finrank (ZMod 3) F.range = 5 := le_antisymm hrange_le hrange_ge
  have hkerdim : Module.finrank (ZMod 3) F.ker = 1 := by
    have hrank := F.finrank_range_add_finrank_ker
    omega
  have hspan_ker : Submodule.span (ZMod 3) ({yV} : Set V) ≤ F.ker := by
    rw [Submodule.span_le]
    rintro _ rfl
    exact LinearMap.mem_ker.mpr (by
      ext i
      simpa [F] using hαy i)
  have hspan_fin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({yV} : Set V)) = 1 :=
    finrank_span_singleton hyV
  have hker_eq : F.ker = Submodule.span (ZMod 3) ({yV} : Set V) := by
    refine (Submodule.eq_of_le_of_finrank_eq hspan_ker ?_).symm
    rw [hspan_fin, hkerdim]
  intro b hbfix
  have hbV : ι (Additive.ofMul b) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    ext i
    have hφmem : φ i ∈ ggAutomizer K Bs := by
      rw [hclos]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfixb : φ i b = b := hbfix (φ i) hφmem
    have hfixV : ggLin (p := 3) ι (φ i) (ι (Additive.ofMul b)) =
        ι (Additive.ofMul b) := by
      rw [ggLin_apply_ofMul, hfixb]
    have hsl := hlin i (ι (Additive.ofMul b))
    rw [hfixV] at hsl
    have hzero : α i (ι (Additive.ofMul b)) • h i = 0 :=
      sub_eq_self.mp hsl.symm
    have hh : h i ≠ 0 := by
      intro h0
      have hp := hpair i i
      rw [h0, map_zero, hCKK.1 i] at hp
      exact zmod3_two_ne_zero hp.symm
    have hαb : α i (ι (Additive.ofMul b)) = 0 :=
      (smul_eq_zero.mp hzero).resolve_right hh
    simpa [F] using hαb
  rw [hker_eq] at hbV
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbV
  let k : ℤ := ZMod.cast c
  have hk : ((k : ℤ) : ZMod 3) = c := by
    simpa [k] using ZMod.intCast_zmod_cast c
  have hc' : ((k : ZMod 3) • yV) = ι (Additive.ofMul b) := by
    simpa [hk] using hc
  have hc_int : k • yV = ι (Additive.ofMul b) := by
    simpa [Int.cast_smul_eq_zsmul] using hc'
  have hmap : k • yV = ι (k • Additive.ofMul yB) := by
    change k • ι (Additive.ofMul yB) = ι (k • Additive.ofMul yB)
    rw [← map_zsmul]
  have hpow : k • Additive.ofMul yB = Additive.ofMul (yB ^ k) :=
    (ofMul_zpow k yB).symm
  have hbEq : b = yB ^ k := by
    apply Additive.ofMul.injective
    apply ι.injective
    calc
      ι (Additive.ofMul b) = k • yV := hc_int.symm
      _ = ι (k • Additive.ofMul yB) := hmap
      _ = ι (Additive.ofMul (yB ^ k)) := by rw [hpow]
  have hbG : (b : G) = y ^ k := by
    have h := congrArg (fun z : ↥Bs => (z : G)) hbEq
    simpa [yB] using h
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hbG.symm⟩

private theorem det_reindex_map
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] (e : Fin 5 ≃ Idx)
    (M : Matrix (Fin 5) (Fin 5) ℤ) :
    ((Matrix.reindex e e M).map (Int.castRingHom (ZMod 3))).det =
      ((M.det : ℤ) : ZMod 3) := by
  calc
    ((Matrix.reindex e e M).map (Int.castRingHom (ZMod 3))).det
        = ((M.map (Int.castRingHom (ZMod 3))).det) := by
          rw [show (Matrix.reindex e e M).map (Int.castRingHom (ZMod 3)) =
              Matrix.reindex e e (M.map (Int.castRingHom (ZMod 3))) from rfl,
            Matrix.det_reindex_self]
    _ = ((M.det : ℤ) : ZMod 3) := by
          simpa using (Int.cast_det (R := ZMod 3) M).symm

private theorem det_reindex_transpose_map
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] (e : Fin 5 ≃ Idx)
    (M : Matrix (Fin 5) (Fin 5) ℤ) :
    (((Matrix.reindex e e M).transpose).map (Int.castRingHom (ZMod 3))).det =
      ((M.det : ℤ) : ZMod 3) := by
  calc
    (((Matrix.reindex e e M).transpose).map (Int.castRingHom (ZMod 3))).det
        = (((Matrix.reindex e e M).map (Int.castRingHom (ZMod 3))).transpose).det := by
          rw [Matrix.transpose_map]
    _ = ((Matrix.reindex e e M).map (Int.castRingHom (ZMod 3))).det := by
          rw [Matrix.det_transpose]
    _ = ((M.det : ℤ) : ZMod 3) := det_reindex_map e M

theorem det_B5_reindex_ne_zero
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hC : GGIntCartan MK CK) (e : Fin 5 ≃ Idx)
    (hM : MK = (CoxeterMatrix.B 5).reindex e) :
    (CK.map (Int.castRingHom (ZMod 3))).det ≠ 0 := by
  subst hM
  have hC' : GGIntCartan ((CoxeterMatrix.B 5).reindex e) CK := hC
  have hbase : ((CartanMatrix.B 5).det : ZMod 3) ≠ 0 := by
    rw [CartanMatrix.B_det (by norm_num)]
    exact zmod3_two_ne_zero
  rcases hC'.eq_or_eq_transpose ((ggIntCartan_B 5).reindex e)
      ((ggAtMostOneMultipleEdge_B 5).reindex e) with h | h
  · rw [h, det_reindex_map e (CartanMatrix.B 5)]
    exact hbase
  · rw [h, det_reindex_transpose_map e (CartanMatrix.B 5)]
    exact hbase

theorem det_D5_reindex_ne_zero
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hC : GGIntCartan MK CK) (e : Fin 5 ≃ Idx)
    (hM : MK = (ggCoxeterMatrixD 5).reindex e) :
    (CK.map (Int.castRingHom (ZMod 3))).det ≠ 0 := by
  subst hM
  have hC' : GGIntCartan ((ggCoxeterMatrixD 5).reindex e) CK := hC
  have hbase : ((CartanMatrix.D 5).det : ZMod 3) ≠ 0 := by
    rw [CartanMatrix.D_det (by norm_num)]
    exact zmod3_four_ne_zero
  rcases hC'.eq_or_eq_transpose ((ggIntCartan_D 5).reindex e)
      ((ggAtMostOneMultipleEdge_D 5).reindex e) with h | h
  · rw [h, det_reindex_map e (CartanMatrix.D 5)]
    exact hbase
  · rw [h, det_reindex_transpose_map e (CartanMatrix.D 5)]
    exact hbase


theorem K_fixedLine_of_B5_card_six
    {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} {y : G}
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK) (e : Fin 5 ≃ Idx)
    (hM : MK = (CoxeterMatrix.B 5).reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hclos : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hy : y ∈ Bs) (hy1 : y ≠ 1)
    (hyfix : ∀ ψ ∈ ggAutomizer K Bs,
      ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩)
    (hcard : Nat.card Bs = 3 ^ 6) :
    ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y :=
  K_fixedLine_of_rankFive_nondegenerate hCKK
    (by simpa using (Fintype.card_congr e).symm) hdet
    ι φ h α hlin hpair hclos hy hy1
    (alpha_y_eq_zero_of_fixed hCKK ι φ h α hlin hpair hclos hy hyfix)
    (finrank_six_of_card ι hcard)
where
  hdet : (CK.map (Int.castRingHom (ZMod 3))).det ≠ 0 :=
    det_B5_reindex_ne_zero hCKK e hM

theorem K_fixedLine_of_D5_card_six
    {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} {y : G}
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK) (e : Fin 5 ≃ Idx)
    (hM : MK = (ggCoxeterMatrixD 5).reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hclos : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hy : y ∈ Bs) (hy1 : y ≠ 1)
    (hyfix : ∀ ψ ∈ ggAutomizer K Bs,
      ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩)
    (hcard : Nat.card Bs = 3 ^ 6) :
    ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y :=
  K_fixedLine_of_rankFive_nondegenerate hCKK
    (by simpa using (Fintype.card_congr e).symm) hdet
    ι φ h α hlin hpair hclos hy hy1
    (alpha_y_eq_zero_of_fixed hCKK ι φ h α hlin hpair hclos hy hyfix)
    (finrank_six_of_card ι hcard)
where
  hdet : (CK.map (Int.castRingHom (ZMod 3))).det ≠ 0 :=
    det_D5_reindex_ne_zero hCKK e hM

theorem GGResHyp.K_moving_of_B5_card_six
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK) (e : Fin 5 ≃ Idx)
    (hM : MK = (CoxeterMatrix.B 5).reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hclos : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hy : y ∈ Bs) (hy1 : y ≠ 1)
    (hyfix : ∀ ψ ∈ ggAutomizer K Bs,
      ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩)
    (hcard : Nat.card Bs = 3 ^ 6) :
    ∃ t ∈ ggAutomizer K Bs, GGIsReflection 3 t ∧
      t ⟨x, hx⟩ ≠ ⟨x, hx⟩ :=
  ggIndep_moving_K_of_fixedLine hH hx
    (K_fixedLine_of_B5_card_six hCKK e hM ι φ h α hlin hpair hclos
      hy hy1 hyfix hcard)

theorem GGResHyp.K_moving_of_D5_card_six
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hx : x ∈ Bs)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {MK : CoxeterMatrix Idx} {CK : Matrix Idx Idx ℤ}
    (hCKK : GGIntCartan MK CK) (e : Fin 5 ≃ Idx)
    (hM : MK = (ggCoxeterMatrixD 5).reindex e)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Idx → MulAut ↥Bs) (h : Idx → V)
    (α : Idx → Module.Dual (ZMod 3) V)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod 3))
    (hclos : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hy : y ∈ Bs) (hy1 : y ≠ 1)
    (hyfix : ∀ ψ ∈ ggAutomizer K Bs,
      ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩)
    (hcard : Nat.card Bs = 3 ^ 6) :
    ∃ t ∈ ggAutomizer K Bs, GGIsReflection 3 t ∧
      t ⟨x, hx⟩ ≠ ⟨x, hx⟩ :=
  ggIndep_moving_K_of_fixedLine hH hx
    (K_fixedLine_of_D5_card_six hCKK e hM ι φ h α hlin hpair hclos
      hy hy1 hyfix hcard)

theorem false_of_all_added_inside_B5D5_raw
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (hcard : Nat.card Bs = 3 ^ 6)
    (e6 : Fin 6 ≃ Λ) (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hKcase : (∃ e : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
        MK = (CoxeterMatrix.B 5).reindex e) ∨
      (∃ e : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
        MK = (ggCoxeterMatrixD 5).reindex e))
    (hinsAll : ∀ a : Λa,
      h (Sum.inr a) ∈ E6QTwo.spanH (fun i : Fin 6 => h (Sum.inl (e6 i)))) :
    False := by
  classical
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let φK : ({i : Λ // i ∉ S} ⊕ Λa) → MulAut ↥Bs :=
    fun o => φ (o.map Subtype.val id)
  let hK : ({i : Λ // i ∉ S} ⊕ Λa) → V := fun o => h (o.map Subtype.val id)
  let αK : ({i : Λ // i ∉ S} ⊕ Λa) → Module.Dual (ZMod 3) V :=
    fun o => α (o.map Subtype.val id)
  have hlinK : ∀ o w, ggLin (p := 3) ι (φK o) w = w - αK o w • hK o := by
    intro o w
    exact hlin (o.map Subtype.val id) w
  have hpairK' : ∀ o o', αK o (hK o') = (CK o o' : ZMod 3) := by
    intro o o'
    exact hpairK o o'
  have hclosK' : ggAutomizer K Bs = Subgroup.closure (Set.range φK) := by
    rw [hclosK]
    congr 1
    ext z
    constructor
    · intro hz
      rw [Set.mem_union] at hz
      rcases hz with ⟨j, rfl⟩ | ⟨a, rfl⟩
      · exact Set.mem_range.mpr ⟨Sum.inl j, rfl⟩
      · exact Set.mem_range.mpr ⟨Sum.inr a, rfl⟩
    · intro hz
      rw [Set.mem_range] at hz
      obtain ⟨o, rfl⟩ := hz
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
  have hNbr : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hNbr.1.2.1
  have hy1 : y ≠ 1 := hNbr.1.2.2.1
  have hyfix : ∀ ψ ∈ ggAutomizer K Bs,
      ψ (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggResI_automizer_fix hy hNbr.1.2.2.2.1
  have hmove : ∃ t ∈ ggAutomizer K Bs,
      t (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩ := by
    rcases hKcase with ⟨e, hM⟩ | ⟨e, hM⟩
    · obtain ⟨t, ht, -, hne⟩ :=
        GGResHyp.K_moving_of_B5_card_six hH hH.1.tableB_facts.2.2.1 hCK e hM
          ι φK hK αK hlinK hpairK' hclosK' hy hy1 hyfix hcard
      exact ⟨t, ht, hne⟩
    · obtain ⟨t, ht, -, hne⟩ :=
        GGResHyp.K_moving_of_D5_card_six hH hH.1.tableB_facts.2.2.1 hCK e hM
          ι φK hK αK hlinK hpairK' hclosK' hy hy1 hyfix hcard
      exact ⟨t, ht, hne⟩
  exact false_of_all_added_inside hH ι φ h α hCL hlin hpairL hpairK hCK hclosL
    hclosK hsel hcard e6 hMLeq hinsAll hmove


theorem exists_added_coroot_outside_B5D5_raw
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (hcard : Nat.card Bs = 3 ^ 6)
    (e6 : Fin 6 ≃ Λ) (hMLeq : ML = CoxeterMatrix.E₆.reindex e6)
    (hKcase : (∃ e : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
        MK = (CoxeterMatrix.B 5).reindex e) ∨
      (∃ e : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa),
        MK = (ggCoxeterMatrixD 5).reindex e)) :
    ∃ a : Λa,
      h (Sum.inr a) ∉ E6QTwo.spanH (fun i : Fin 6 => h (Sum.inl (e6 i))) := by
  by_contra hnone
  have hAll : ∀ a : Λa,
      h (Sum.inr a) ∈ E6QTwo.spanH (fun i : Fin 6 => h (Sum.inl (e6 i))) := by
    intro a
    by_contra hout
    exact hnone ⟨a, hout⟩
  exact false_of_all_added_inside_B5D5_raw hH ι φ h α hCL hlin hpairL hpairK hCK
    hclosL hclosK hsel hcard e6 hMLeq hKcase hAll

end CFSG.StandardType

end
