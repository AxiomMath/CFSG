module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXRes
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Dispatch
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemmaA
public import CFSG.LocalAnalysis.StandardType.GGQTwoScalarStable
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishD
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoF4
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormModelA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2gx_gamma_of_normalizer_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (u : ↥Bs)
    (h : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)) :
    GGGammaAt p B Bs x L D J u := by
  intro φ hφ _
  rw [mem_ggAutomizer_iff] at hφ ⊢
  obtain ⟨g, -, hgN, hg⟩ := hφ
  exact ⟨g, h hgN, hgN, hg⟩

private theorem ggQ2gx_alpha_xV {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (e : D.ι)
    (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ e}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV}) :
    ∀ j : {k // k ≠ e}, D.root j xV = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    haveI : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  intro j
  have hxV : xV ∈ Submodule.span (ZMod p) {xV} := Submodule.mem_span_singleton_self xV
  have hmem : D.simpleRefl j ∈ D.parab {k | k ≠ e} :=
    Subgroup.subset_closure ⟨j.1, j.2, rfl⟩
  have hfixj : D.simpleRefl j xV = xV := (hfix xV).mpr hxV _ hmem
  have happ : D.simpleRefl j xV = xV - D.root j xV • D.coroot j :=
    Module.reflection_apply (h := D.root_coroot_self j) xV
  have hsmul : D.root j xV • D.coroot j = 0 := by
    rw [happ] at hfixj
    exact sub_eq_self.mp hfixj
  rcases smul_eq_zero.mp hsmul with h | h
  · exact h
  · exfalso
    exact h2ne (by
      calc (2 : ZMod p) = D.root j (D.coroot j) := (D.root_coroot_self j).symm
        _ = D.root j 0 := by rw [h]
        _ = 0 := map_zero (D.root j))

private theorem ggQ2gx_g1_stable {G : Type} [Group G] {Bs : Subgroup G} {x : G} (hx : x ∈ Bs)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) {φ : MulAut ↥Bs}
    (hφu : φ u ∈ Subgroup.zpowers u) :
    φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hφu
  have hxmem : x ∈ Subgroup.zpowers (u : G) := by
    rw [hu]
    exact Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hux : (⟨x, hx⟩ : ↥Bs) = u ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hk]
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨r, ?_⟩
  calc (⟨x, hx⟩ : ↥Bs) ^ r = (u ^ k) ^ r := by rw [hux]
    _ = u ^ (k * r) := (zpow_mul u k r).symm
    _ = u ^ (r * k) := by rw [mul_comm]
    _ = (u ^ r) ^ k := zpow_mul u r k
    _ = (φ u) ^ k := by rw [hr]
    _ = φ (u ^ k) := (map_zpow φ u k).symm
    _ = φ ⟨x, hx⟩ := by rw [← hux]

private lemma ggQ2gx_zsmul_model {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (n : ℤ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_zsmul n (Additive.ofMul b)

private lemma ggQ2gx_model_mem_span {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (c d : ↥Bs) (h : c ∈ Subgroup.zpowers d) :
    M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← hm, ofMul_zpow, ggQ2gx_zsmul_model M m d]
  rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma ggQ2gx_kernel_eq_zero {p : ℕ} [Fact p.Prime] {Γ : Type} [Fintype Γ]
    [DecidableEq Γ] (N : Matrix Γ Γ (ZMod p)) (hdet : N.det ≠ 0) (κ : Γ → ZMod p)
    (hκ : ∀ i, ∑ j, N i j * κ j = 0) : κ = 0 := by
  have h0 : N.mulVec κ = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    exact hκ i
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h0

private lemma ggQ2gx_F4_coxeter {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : CoxeterMatrix ι) (C : Matrix ι ι ℤ) (h : GGIntCartan N C)
    (a : ι) (e : Fin 4 ≃ {k // k ≠ a})
    (hC : (∀ i j : Fin 4, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
          (∀ i j : Fin 4, C (e i) (e j) = CartanMatrix.F₄ j i)) :
    ∀ i j : Fin 4, N (e i) (e j) = CoxeterMatrix.F₄ i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    exact (CoxeterMatrix.diagonal N (e i)).trans
      (CoxeterMatrix.diagonal CoxeterMatrix.F₄ i).symm
  · have hne : (e i : ι) ≠ (e j : ι) := fun hh => hij (e.injective (Subtype.ext hh))
    have h2 := h.2 (e i) (e j) hne
    rcases hC with hC | hC <;>
      (fin_cases i <;> fin_cases j <;>
        (rcases h2 with ⟨hm, hcond⟩ | ⟨hm, hcond⟩ | ⟨hm, hcond⟩ | ⟨hm, hcond⟩ <;>
          first
            | (rw [hm]; decide +kernel)
            | (exfalso; simp only [hC] at hcond; revert hcond; decide +kernel)))

theorem ggQ2_gammaX_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1 : GGQTwoModelInput) (h1b : GGQTwoNoTwoNodeIndInput) (h5 : GGQTwoCentralizerInput)
    (hnode : GGQ2TwoNodeInput)
    (hgraph : GGQ2GammaXGraphInput) (hpos : GGQ2GammaXPosInput) : GGQ2GammaXInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL u hu
  haveI : Fact p.Prime := ⟨hS.1.1.tableB_facts.1⟩
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  by_cases hrow : ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ((GGQTwoTwoNodeRowAt 3 L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt 3 K J ∧ y ∉ K))
  · obtain ⟨y, K, hnb, h⟩ := hrow
    exact ggQ2gx_gamma_of_normalizer_le u (hnode rfl hS hI1 hnb h)
  have hnr : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ¬ (GGQTwoTwoNodeRowAt 3 L J ∨ GGQTwoTwoNodeRowAt 3 K J) := by
    intro y K hnb h
    obtain ⟨hL, hK⟩ := h1b G 3 B Bs x L D J hS hI1 y K hnb
    rcases h with h | h
    · exact hrow ⟨y, K, hnb, Or.inl ⟨h, hL h⟩⟩
    · exact hrow ⟨y, K, hnb, Or.inr ⟨h, hK h⟩⟩
  have hcases : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      Nonempty (GGQTwoModel 3 Bs x y D L J K) ∨
        (GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∧
          GGReflGenerated 3 (ggAutomizer K Bs)) := by
    intro y K hnb
    rcases h1 G 3 B Bs x L D J hS hI1 y K hnb with h | h | hM | hW
    · exact absurd (Or.inl h) (hnr y K hnb)
    · exact absurd (Or.inr h) (hnr y K hnb)
    · exact Or.inl hM
    · exact Or.inr hW
  have hRG : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      GGReflGenerated 3 (ggAutomizer K Bs) := by
    intro y K hnb
    rcases hcases y K hnb with hM | ⟨-, hrg⟩
    · obtain ⟨M⟩ := hM
      exact ggQ2_reflGenerated_of_model M
    · exact hrg
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  by_cases hcov : GGQ2XCovered 3 B Bs x L D J
  · obtain ⟨y, K, hnb, M, hdet, hV⟩ := hcov
    intro φ hφ hφu
    have hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
      ggQ2gx_g1_stable M.hx hu hφu
    have hφxV : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV} := by
      have h1 : ggLin (p := 3) M.model φ M.xV =
          M.model (Additive.ofMul (φ ⟨x, M.hx⟩)) := by
        rw [GGQTwoModel.xV, ggLin_apply_ofMul]
      rw [h1]
      exact ggQ2gx_model_mem_span M (φ ⟨x, M.hx⟩) ⟨x, M.hx⟩ hφx
    have hfix1 := (ggQ2_fixed_lin M).1
    have hfix2 := (ggQ2_fixed_lin M).2
    have hxα : ∀ j : {k // k ≠ M.a}, M.root j M.xV = 0 :=
      ggQ2gx_alpha_xV rfl M.toLin M.a M.xV hfix1
    have hyα : ∀ j : {k // k ≠ M.b}, M.root j M.yV = 0 :=
      ggQ2gx_alpha_xV rfl M.toLin M.b M.yV hfix2
    have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
    have hx0 : M.xV ≠ 0 := by
      intro h
      have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
        M.model.injective (by rw [map_zero]; exact h)
      have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 :=
        Additive.ofMul.injective (by simpa using h0)
      exact hxne (Subtype.ext_iff.mp h1)
    have hxs : M.xV ∉ Submodule.span (ZMod 3)
        (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
      intro hmem
      rw [Submodule.mem_span_range_iff_exists_fun] at hmem
      obtain ⟨κ, hκsum⟩ := hmem
      have hκ0 : ∀ i : {k // k ≠ M.a},
          ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0 := by
        intro i
        have h := congrArg (M.root i) hκsum
        have hzero : ∑ j : {k // k ≠ M.a}, κ j * (M.cartan i j : ZMod 3) = 0 := by
          simpa only [map_sum, map_smul, smul_eq_mul, M.pairing, hxα i] using h
        calc ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j
            = ∑ j : {k // k ≠ M.a}, κ j * (M.cartan i j : ZMod 3) :=
              Finset.sum_congr rfl fun j _ => mul_comm _ _
          _ = 0 := hzero
      have hdet' : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)).det ≠ 0 := by
        have hmap : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3))
            = (Int.castRingHom (ZMod 3)).mapMatrix
                (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
                  (fun i : {k // k ≠ M.a} => (i : M.ι))) := rfl
        rw [hmap, ← RingHom.map_det]
        exact hdet
      have hκzero : κ = 0 := ggQ2gx_kernel_eq_zero _ hdet' κ hκ0
      apply hx0
      have hzero : ∑ j : {k // k ≠ M.a}, κ j • M.coroot j = 0 := by
        rw [hκzero]; simp
      rw [← hκsum, hzero]
    obtain ⟨π, μ, c, hc0, hμ, hcomp, w, hw, hT⟩ :=
      ggQ2_tbwNorm_at_a hLB hP h5 hS rfl M (M.toLin.linearIndependent_compl_of_det M.a hdet) M.xV
        hfix1 hxs hφ hφxV
    have hScaled : M.toLin.ScaledAut M.a π μ := ⟨hμ, hcomp⟩
    let T : M.V →ₗ[ZMod 3] M.V :=
      (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
    by_cases hπb : π ⟨M.b, M.a_ne_b.symm⟩ = ⟨M.b, M.a_ne_b.symm⟩
    · obtain ⟨w', hw', hstab⟩ :=
        ggQ2_lemmaA M.toLin M.xV M.yV hxα hyα hV hdet hScaled hπb hw hT hφxV
      obtain ⟨ψ, hψ, hD⟩ := ggQ2_xBridge M hnb.2.1 ⟨w', hw', hstab⟩
      exact ggQ2_finishD hLB hP hS hAJS hK1 hnb hφ hψ hD
    · by_cases hsm : M.toLin.ScalarModW M.a π μ
      · obtain ⟨w', hw', ε, hε⟩ :=
          ggQ2_scalarStable M.toLin M.xV hxα hV hsm hw hT hφxV
        have hstab : ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
            w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV} := by
          intro v hv
          obtain ⟨s, hs⟩ := hε v
          have hs' : w' (ggLin (p := 3) M.model φ v) = ε • v + s • M.xV := hs
          rw [hs']
          have h1 : ε • v ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
            Submodule.smul_mem _ ε hv
          have hx : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
            Submodule.subset_span (by simp)
          have h2 : s • M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
            Submodule.smul_mem _ s hx
          exact Submodule.add_mem _ h1 h2
        obtain ⟨ψ, hψ, hD⟩ := ggQ2_xBridge M hnb.2.1 ⟨w', hw', hstab⟩
        exact ggQ2_finishD hLB hP hS hAJS hK1 hnb hφ hψ hD
      · have hdim : Module.finrank (ZMod 3) M.V ≤ Fintype.card {k // k ≠ M.a} + 1 := by
          have hrange : Set.range (fun o : Option {k // k ≠ M.a} =>
              Option.elim o M.xV (fun i => M.coroot i))
              = insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
            ext v
            constructor
            · rintro ⟨o, rfl⟩
              cases o with
              | none => exact Set.mem_insert _ _
              | some i => exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
            · intro hv
              rw [Set.mem_insert_iff] at hv
              rcases hv with rfl | ⟨i, rfl⟩
              · exact ⟨none, rfl⟩
              · exact ⟨some i, rfl⟩
          have htop : Module.finrank (ZMod 3) M.V
              ≤ Fintype.card (Option {k // k ≠ M.a}) :=
            finrank_le_of_span_eq_top (R := ZMod 3)
              (v := fun o : Option {k // k ≠ M.a} => Option.elim o M.xV (fun i => M.coroot i))
              (by rw [hrange]; exact hV)
          rwa [Fintype.card_option] at htop
        haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
        have hcard_bs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
          calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
            _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
            _ = 3 ^ Module.finrank (ZMod 3) M.V :=
              (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
        have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
          have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
          have hp1 : 1 < 3 := by norm_num
          rw [hcard_bs] at hp4
          exact (Nat.pow_le_pow_iff_right hp1).mp hp4
        have hcard : 3 ≤ Fintype.card {k // k ≠ M.a} := by omega
        rcases ggQ2s5_classify M.toLin hcard hScaled with hsm' | hgl
        · exact absurd hsm' hsm
        · rcases hgl with ⟨k, hk, f, hf⟩ | ⟨f, hf | hf⟩
          · exact hgraph hS rfl hI1 hxL hnb M ⟨k, hk, f, hf⟩ hV φ hφ hφxV π μ c w
              hScaled hw hT hπb hsm
          · obtain ⟨i, j, hij⟩ := ggQ2_no_F4_leaf M.coxeter M.isWeyl M.a f
            exact absurd (ggQ2gx_F4_coxeter M.coxeter M.cartan M.isCartan M.a f
              (Or.inl hf) i j) hij
          · obtain ⟨i, j, hij⟩ := ggQ2_no_F4_leaf M.coxeter M.isWeyl M.a f
            exact absurd (ggQ2gx_F4_coxeter M.coxeter M.cartan M.isCartan M.a f
              (Or.inr hf) i j) hij
  · exact hpos hS rfl hI1 hxL hrow hcov hu

end CFSG.StandardType

end
