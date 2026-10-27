module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraph
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbInner
import CFSG.LocalAnalysis.StandardType.GGQTwoDLeafNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDFourLeafNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbResEvenD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def GGQ2AmbModelInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
    ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∃ M : GGQTwoAmbModel p Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
        ((M.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
        ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
          (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0

@[expose] def GGQTwoTBWNormAmbInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → ∀ [Fact p.Prime] (y : G) (K : Subgroup G),
      GGNbr p B x D J y K → ∀ M : GGQTwoAmbModel p Bs x y L (L ⊔ K), ∀ u : M.V,
        (∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
          v ∈ Submodule.span (ZMod p) {u}) →
        u ∉ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) →
        ∀ φ ∈ ggAutomizer ⊤ Bs,
          ggLin (p := p) M.model φ u ∈ Submodule.span (ZMod p) {u} →
          ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p),
            c ≠ 0 ∧ (∀ i, μ i ≠ 0) ∧
            (∀ i j : {k // k ≠ M.a},
              μ i * (M.cartan i j : ZMod p) = μ j * (M.cartan (π i) (π j) : ZMod p)) ∧
            ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
              ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i))

@[expose] def GGQ2GammaXGraphD5AmbInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
    ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ∀ M : GGQTwoAmbModel p Bs x y L (L ⊔ K), ∀ e : Fin 5 ≃ M.ι,
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) → M.a = e 0 →
      Submodule.span (ZMod p) (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV} →
      ∀ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p)
        (w : M.V ≃ₗ[ZMod p] M.V),
        M.toLin.ScaledAut M.a π μ → w ∈ M.toLin.parab {k | k ≠ M.a} →
        (∀ i : {k // k ≠ M.a},
          ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i))) →
        π ⟨M.b, M.a_ne_b.symm⟩ ≠ ⟨M.b, M.a_ne_b.symm⟩ →
        (∀ i : {k // k ≠ M.a}, (i : M.ι) = e 1 → ((π i : {k // k ≠ M.a}) : M.ι) ≠ e 1) →
        φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs

theorem ggQ2xa_x_stable {G : Type} [Group G] {Bs : Subgroup G} {x : G} (hx : x ∈ Bs)
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

lemma ggQ2xa_model_mem_span {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (c d : ↥Bs) (h : c ∈ Subgroup.zpowers d) :
    M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hz : M.model (m • Additive.ofMul d) = m • M.model (Additive.ofMul d) :=
    (M.model.toAddMonoidHom).map_zsmul m (Additive.ofMul d)
  rw [← hm, ofMul_zpow, hz, ← Int.cast_smul_eq_zsmul (R := ZMod p)]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem ggQ2xa_bridge {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {L H' : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H') {D : Subgroup G}
    (hDxy : D = Subgroup.closure {x, y}) {S : Set M.ι} {H : Subgroup G}
    (hH : M.parabL S ≤ (ggAutomizer H Bs).map (ggLin (p := p) M.model)) {φ : MulAut ↥Bs}
    (h : ∃ w' ∈ M.parabL S, ∀ v ∈ Submodule.span (ZMod p) {M.xV, M.yV},
      w' (ggLin (p := p) M.model φ v) ∈ Submodule.span (ZMod p) {M.xV, M.yV}) :
    ∃ ψ ∈ ggAutomizer H Bs, ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D := by
  obtain ⟨w', hw'S, hw'⟩ := h
  obtain ⟨ψ, hψ, hψw⟩ := Subgroup.mem_map.mp (hH hw'S)
  refine ⟨ψ, hψ, fun b hbD => ?_⟩
  have hbspan : M.model (Additive.ofMul b) ∈ Submodule.span (ZMod p) {M.xV, M.yV} :=
    (M.mem_closure_iff b).mp (by rw [← hDxy]; exact hbD)
  have hspan' : M.model (Additive.ofMul ((ψ * φ) b)) ∈
      Submodule.span (ZMod p) {M.xV, M.yV} := by
    have heq : M.model (Additive.ofMul ((ψ * φ) b)) =
        w' (ggLin (p := p) M.model φ (M.model (Additive.ofMul b))) := by
      rw [← ggLin_apply_ofMul (p := p) M.model (ψ * φ) b, map_mul,
        LinearEquiv.mul_apply, hψw]
    rw [heq]
    exact hw' _ hbspan
  rw [hDxy]
  exact (M.mem_closure_iff ((ψ * φ) b)).mpr hspan'

private lemma ggQ2xa_F4_coxeter {ι : Type} [Fintype ι] [DecidableEq ι]
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

lemma ggQ2xa_D_succ_succ {k : ℕ} (hk : 2 ≤ k) (i j : Fin (2 * k)) :
    CartanMatrix.D (2 * k + 1) i.succ j.succ = CartanMatrix.D (2 * k) i j := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  rw [if_congr (show i.succ = j.succ ↔ i = j from
    ⟨fun h => Fin.succ_injective (2 * k) h, fun h => by rw [h]⟩) rfl ?_]
  rw [if_neg (by omega : ¬ 2 * k + 1 ≤ 2), if_neg (by omega : ¬ 2 * k ≤ 2)]
  have hsi : (i.succ : Fin (2 * k + 1)).val = i.val + 1 := rfl
  have hsj : (j.succ : Fin (2 * k + 1)).val = j.val + 1 := rfl
  have h1 : (i.succ.val + 1 = j.succ.val ∧ j.succ.val + 2 < 2 * k + 1) ↔
      (i.val + 1 = j.val ∧ j.val + 2 < 2 * k) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  have h2 : (j.succ.val + 1 = i.succ.val ∧ i.succ.val + 2 < 2 * k + 1) ↔
      (j.val + 1 = i.val ∧ i.val + 2 < 2 * k) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  have h3 : (i.succ.val + 3 = 2 * k + 1 ∧
      (j.succ.val + 2 = 2 * k + 1 ∨ j.succ.val + 1 = 2 * k + 1)) ↔
      (i.val + 3 = 2 * k ∧ (j.val + 2 = 2 * k ∨ j.val + 1 = 2 * k)) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  have h4 : (j.succ.val + 3 = 2 * k + 1 ∧
      (i.succ.val + 2 = 2 * k + 1 ∨ i.succ.val + 1 = 2 * k + 1)) ↔
      (j.val + 3 = 2 * k ∧ (i.val + 2 = 2 * k ∨ i.val + 1 = 2 * k)) := by
    rw [hsi, hsj]
    constructor <;> intro h <;> omega
  rw [if_congr h1 rfl (if_congr h2 rfl (if_congr h3 rfl (if_congr h4 rfl rfl)))]

private lemma ggQ2xa_fin4_perm (π : Equiv.Perm (Fin 4)) (h0 : π 0 = 0) (h1 : π 1 = 1) :
    π = 1 ∨ π = Equiv.swap (2 : Fin 4) 3 := by
  revert π
  decide +kernel

private lemma ggQ2xa_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

private lemma ggQ2xa_neg_one : (-1 : ZMod 3) = 2 := by decide

lemma ggQ2xa_tau_swap : ∀ i : Fin 6,
    (![6, 5, 4, 3, 1, 2] : Fin 6 → Fin 7)
      (Equiv.swap (⟨6 - 2, by omega⟩ : Fin 6) ⟨6 - 1, by omega⟩ i) =
    ggg7_tau ((![6, 5, 4, 3, 1, 2] : Fin 6 → Fin 7) i) := by
  decide

lemma ggQ2xa_tau_surj : ∀ t : Fin 7, t ≠ 0 →
    ∃ j : Fin 6, (![6, 5, 4, 3, 1, 2] : Fin 6 → Fin 7) j = t := by
  decide

theorem ggQ2_gammaX_of_noNbr (hLN : GGLNoncyclicInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hno : ∀ (y : G) (K : Subgroup G), ¬ GGNbr p B x D J y K) {u : ↥Bs}
    (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) : GGGammaAt p B Bs x L D J u := by
  intro φ hφ hφu
  have hG0 : ggG0 p B x L D J = L :=
    le_antisymm (sup_le le_rfl (iSup_le fun y => iSup_le fun K => iSup_le fun h =>
      absurd h (hno y K))) le_sup_left
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hI : GGThmIHyp p B x L := hS.1.1.1
  have hx : x ∈ Bs := by
    have hxu : x ∈ Subgroup.zpowers (u : G) := by
      rw [hu]
      exact Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr u.2) hxu
  have hφx : φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := ggQ2xa_x_stable hx hu hφu
  have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 := congrArg Subtype.val hk
    rw [hφg] at h1
    simpa using h1
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_sstar' hI.2.2.2.2.2.2.1 (hLN G p B x L hI)
      (CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem hgx)
  refine mem_ggAutomizer_iff.mpr ⟨g, ?_, hgN, hφg⟩
  rw [hG0]
  exact hgL

theorem ggQ2_gammaX_of_ambModelRes (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hga : GGQ2GammaXGraphD5AmbInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hI1 : GGQTwoI1 Bs D J) (hxL : x ∉ L)
    [Fact p.Prime]
    (hrow : ¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K)))
    (hno : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K))
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (M : GGQTwoAmbModel p Bs x y L (L ⊔ K))
    (hbas : GGQTwoAmbBasis M) (hnd : ((M.cartan.det : ℤ) : ZMod p) ≠ 0)
    (hdet : ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
      (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) :
    GGGammaAt p B Bs x L D J u := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  have hG0L : L ≤ ggG0 3 B x L D J := le_ggG0_left _ _ _ _ _ _
  have hG0LK : L ⊔ (L ⊔ K) ≤ ggG0 3 B x L D J :=
    sup_le hG0L (sup_le hG0L (le_ggG0_of_ggNbr hnb))
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : FiniteDimensional (ZMod 3) M.V := Module.Finite.of_finite
  intro φ hφ hφu
  have finL : (∃ w' ∈ M.parabL {k | k ≠ M.a}, ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
      w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV}) →
      φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
    intro h
    obtain ⟨ψ, hψ, hD⟩ := ggQ2xa_bridge M hnb.2.1 (le_of_eq M.parabL_L) h
    exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb hG0L hφ hψ hD
  have finW : (∃ w' ∈ M.toLin.weyl, ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
      w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV}) →
      φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
    intro h
    obtain ⟨ψ, hψ, hD⟩ := ggQ2xa_bridge (S := Set.univ) M hnb.2.1 M.weyl_le h
    exact ggQ2_finish_of_le hLB hP hS hAJS hK1 hnb hG0LK hφ hψ hD
  have hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := ggQ2xa_x_stable M.hx hu hφu
  have hφxV : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV} := by
    have h1 : ggLin (p := 3) M.model φ M.xV = M.model (Additive.ofMul (φ ⟨x, M.hx⟩)) := by
      rw [GGQTwoAmbModel.xV, ggLin_apply_ofMul]
    rw [h1]
    exact ggQ2xa_model_mem_span M (φ ⟨x, M.hx⟩) ⟨x, M.hx⟩ hφx
  have hfix1 : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := M.fixed_lin
  have hxα : ∀ j : {k // k ≠ M.a}, M.root j M.xV = 0 :=
    ggQ2g_alpha_fixed rfl M.toLin M.a M.xV hfix1
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0)
    exact hxne (Subtype.ext_iff.mp h1)
  have hdet' : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j : {k // k ≠ M.a} => (M.cartan i j : ZMod 3)) =
        (Int.castRingHom (ZMod 3)).mapMatrix
          (M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
            (fun i : {k // k ≠ M.a} => (i : M.ι))) := rfl
    rw [hmap, ← RingHom.map_det]
    exact hdet
  have hker0 : ∀ κ : {k // k ≠ M.a} → ZMod 3,
      (∀ i : {k // k ≠ M.a}, ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0) →
        κ = 0 := by
    intro κ hκ
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet' (funext fun i => ?_)
    simpa [Matrix.mulVec, dotProduct] using hκ i
  have hxs : M.xV ∉
      Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
    intro hmem
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hmem
    have hκk : ∀ i : {k // k ≠ M.a},
        ∑ j : {k // k ≠ M.a}, (M.cartan i j : ZMod 3) * κ j = 0 := by
      intro i
      have h := hxα i
      rw [← hκ, map_sum] at h
      simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using h
    apply hx0
    rw [← hκ, hker0 κ hκk]
    simp
  have hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ M.a} => M.coroot i) :=
    hbas.1.comp (fun i : {k // k ≠ M.a} => (i : M.ι)) Subtype.val_injective
  have hcardΛ : Fintype.card {k // k ≠ M.a} = Fintype.card M.ι - 1 := Set.card_ne_eq M.a
  have hcardι : 0 < Fintype.card M.ι := Fintype.card_pos_iff.mpr ⟨M.a⟩
  have hdimeq : Module.finrank (ZMod 3) M.V = Fintype.card {k // k ≠ M.a} + 1 := by
    rw [← hbas.2, hcardΛ]
    omega
  have hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ := by
    have hspan := (hind.option hxs).span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_option, hdimeq])
    rw [Option.range_eq] at hspan
    exact hspan
  have h6 : ∀ ψ ∈ ggAutomizer ⊤ Bs,
      ggLin (p := 3) M.model ψ M.xV ∈ Submodule.span (ZMod 3) {M.xV} →
      ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod 3) (c : ZMod 3),
        c ≠ 0 ∧ (∀ i, μ i ≠ 0) ∧
        (∀ i j : {k // k ≠ M.a},
          μ i * (M.cartan i j : ZMod 3) = μ j * (M.cartan (π i) (π j) : ZMod 3)) ∧
        ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
          ggLin (p := 3) M.model ψ (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
    intro ψ hψ hψx
    by_cases hin : M.toLin.WeylInnerLeaf M.a
    · obtain ⟨c, hc0, w, hw, hTw⟩ :=
        ggQ2_tbwNormAmb_of_weylInnerLeaf hLB hP h5 hS rfl M hbas hin hψ hψx
      refine ⟨Equiv.refl _, fun _ => 1, c, hc0, fun _ => ggQ2xa_one_ne_zero, fun i j => rfl, w, hw,
        fun i => ?_⟩
      simp only [Equiv.refl_apply, one_smul]
      exact hTw i
    · obtain ⟨n, f, hn4, -, hf⟩ := ggQ2_evenDLeaf_of_not_weylInnerLeaf hS rfl M hin M.xV hfix1
      have hD : ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (c : ZMod 3), c ≠ 0 ∧
          (∀ i j : {k // k ≠ M.a}, M.cartan (π i) (π j) = M.cartan i j) ∧
          ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
            ggLin (p := 3) M.model ψ (M.coroot i) = c • w (M.coroot (π i)) := by
        rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
        · exact ggQ2_tbwNormAmb_of_dFourLeaf hLB hP h5 hS rfl M hind f hf hψ hψx
        · exact ggQ2_tbwNormAmb_of_dLeaf hLB hP h5 hS rfl M hind hn5 f hf hψ hψx
      obtain ⟨π, c, hc0, hπ, w, hw, hTw⟩ := hD
      refine ⟨π, fun _ => 1, c, hc0, fun _ => ggQ2xa_one_ne_zero, fun i j => by rw [hπ i j], w, hw,
        fun i => ?_⟩
      rw [one_smul]
      exact hTw i
  obtain ⟨π, μ, c, hc0, hμ, hcomp, w, hw, hT⟩ :=
    h6 φ hφ hφxV
  have hScaled : M.toLin.ScaledAut M.a π μ := ⟨hμ, hcomp⟩
  by_cases hπb : π ⟨M.b, M.a_ne_b.symm⟩ = ⟨M.b, M.a_ne_b.symm⟩
  ·
    have hxa : M.root M.a M.xV ≠ 0 := by
      intro h0
      apply hx0
      have hall : ∀ i : M.ι, M.root i M.xV = 0 := by
        intro i
        by_cases hi : i = M.a
        · rw [hi]
          exact h0
        · exact hxα ⟨i, hi⟩
      have hspanι : Submodule.span (ZMod 3) (Set.range M.coroot) = ⊤ :=
        hbas.1.span_eq_top_of_card_eq_finrank' hbas.2
      have hmem : M.xV ∈ Submodule.span (ZMod 3) (Set.range M.coroot) := by
        rw [hspanι]
        exact Submodule.mem_top
      obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hmem
      have hκk : ∀ i : M.ι, ∑ j : M.ι, (M.cartan i j : ZMod 3) * κ j = 0 := by
        intro i
        have h := hall i
        rw [← hκ, map_sum] at h
        simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using h
      have hdetι : (Matrix.of fun i j : M.ι => (M.cartan i j : ZMod 3)).det ≠ 0 := by
        have hmap : (Matrix.of fun i j : M.ι => (M.cartan i j : ZMod 3)) =
            (Int.castRingHom (ZMod 3)).mapMatrix M.cartan := rfl
        rw [hmap, ← RingHom.map_det]
        exact hnd
      have hκ0 : κ = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetι
        (funext fun i => by simpa [Matrix.mulVec, dotProduct] using hκk i)
      rw [← hκ, hκ0]
      simp
    obtain ⟨t, ht⟩ : ∃ t : ZMod 3, t = M.root M.a M.yV * (M.root M.a M.xV)⁻¹ := ⟨_, rfl⟩
    have hyα' : ∀ j : {k // k ≠ M.b}, M.root j (M.yV - t • M.xV) = 0 := by
      rintro ⟨j, hjb⟩
      rw [map_sub, map_smul, smul_eq_mul]
      by_cases hja : j = M.a
      · subst hja
        show M.root M.a M.yV - t * M.root M.a M.xV = 0
        rw [ht, mul_assoc, inv_mul_cancel₀ hxa, mul_one, sub_self]
      · have h1 : M.root j M.yV = 0 := M.root_yV rfl j hja hjb
        have h2 : M.root j M.xV = 0 := hxα ⟨j, hja⟩
        show M.root j M.yV - t * M.root j M.xV = 0
        rw [h1, h2]
        ring
    obtain ⟨w', hw', hstab⟩ :=
      ggQ2_lemmaA M.toLin M.xV (M.yV - t • M.xV) hxα hyα' hV hdet hScaled hπb hw hT hφxV
    have hspan_eq : Submodule.span (ZMod 3) {M.xV, M.yV - t • M.xV} =
        Submodule.span (ZMod 3) {M.xV, M.yV} := by
      have hx1 : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
        Submodule.subset_span (by simp)
      have hy1 : M.yV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
        Submodule.subset_span (by simp)
      have hx2 : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV - t • M.xV} : Set M.V) :=
        Submodule.subset_span (by simp)
      have hy2 : M.yV - t • M.xV ∈
          Submodule.span (ZMod 3) ({M.xV, M.yV - t • M.xV} : Set M.V) :=
        Submodule.subset_span (by simp)
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact hx1
        · exact Submodule.sub_mem _ hy1 (Submodule.smul_mem _ _ hx1)
      · rw [Submodule.span_le]
        rintro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact hx2
        · have hmem : (M.yV - t • M.xV) + t • M.xV ∈
              Submodule.span (ZMod 3) ({M.xV, M.yV - t • M.xV} : Set M.V) :=
            Submodule.add_mem _ hy2 (Submodule.smul_mem _ _ hx2)
          rwa [sub_add_cancel] at hmem
    refine finL ⟨w', hw', fun v hv => ?_⟩
    rw [← hspan_eq] at hv ⊢
    exact hstab v hv
  · by_cases hsm : M.toLin.ScalarModW M.a π μ
    ·
      obtain ⟨w', hw', ε, hε⟩ := ggQ2_scalarStable M.toLin M.xV hxα hV hsm hw hT hφxV
      have hstab : ∀ v ∈ Submodule.span (ZMod 3) {M.xV, M.yV},
          w' (ggLin (p := 3) M.model φ v) ∈ Submodule.span (ZMod 3) {M.xV, M.yV} := by
        intro v hv
        obtain ⟨s', hs⟩ := hε v
        have hs' : w' (ggLin (p := 3) M.model φ v) = ε • v + s' • M.xV := hs
        rw [hs']
        have hx : M.xV ∈ Submodule.span (ZMod 3) ({M.xV, M.yV} : Set M.V) :=
          Submodule.subset_span (by simp)
        exact Submodule.add_mem _ (Submodule.smul_mem _ ε hv) (Submodule.smul_mem _ s' hx)
      exact finL ⟨w', hw', hstab⟩
    ·
      have hcard_bs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
        calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
          _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
          _ = 3 ^ Module.finrank (ZMod 3) M.V := (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
      have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
        have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
        rw [hcard_bs] at hp4
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hp4
      have hcard : 3 ≤ Fintype.card {k // k ≠ M.a} := by omega
      rcases ggQ2s5_classify M.toLin hcard hScaled with hsm' | hgl
      · exact absurd hsm' hsm
      · rcases hgl with ⟨k, hk, f, hf⟩ | ⟨f, hf | hf⟩
        · obtain ⟨c₀, hc₀a, hc₀l⟩ := ggQ2g_second_leaf M.toLin hk f hf
          rcases ggQ2g_classify M.toLin M.a c₀ hc₀a hc₀l hk f hf with
            ⟨e, hecart, hcox, he0, -⟩ | ⟨rfl, e, hecart, he0, -⟩
          ·
            let e' : Fin (2 * k + 1) ≃ M.ι := e
            have hecart' : ∀ i j : Fin (2 * k + 1),
                M.cartan (e' i) (e' j) = CartanMatrix.D (2 * k + 1) i j := hecart
            have hcox' : M.toLin.coxeter = (ggCoxeterMatrixD (2 * k + 1)).reindex e' := hcox
            have he0' : M.a = e' ⟨0, by omega⟩ := he0
            let σf : Fin (2 * k) → {i : M.ι // i ≠ M.a} := fun i =>
              ⟨e' i.succ, by
                rw [he0']
                intro h
                exact Fin.succ_ne_zero i (e'.injective h)⟩
            have hσf_bij : Function.Bijective σf := by
              constructor
              · intro a b hab
                have h1 : e' a.succ = e' b.succ := congrArg Subtype.val hab
                exact Fin.succ_injective (2 * k) (e'.injective h1)
              · rintro ⟨i, hi⟩
                obtain ⟨t, rfl⟩ := e'.surjective i
                have ht : t ≠ 0 := by
                  intro h
                  exact hi (by rw [h]; exact he0'.symm)
                obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero ht
                have hσfj : (σf j : M.ι) = e' j.succ := rfl
                exact ⟨j, Subtype.ext (by rw [hσfj, hj])⟩
            let σ : Fin (2 * k) ≃ {i : M.ι // i ≠ M.a} := Equiv.ofBijective σf hσf_bij
            have hσ : ∀ i j, M.cartan (σ i) (σ j) = CartanMatrix.D (2 * k) i j := by
              intro i j
              have h1 := hecart' i.succ j.succ
              change M.cartan (e' i.succ) (e' j.succ) = CartanMatrix.D (2 * k) i j
              rw [h1, ggQ2xa_D_succ_succ hk i j]
            obtain ⟨π', μ', hμ'0, hrel, hπσ, hμσ⟩ := ggQ2g_transport M.toLin M.a σ hσ hScaled
            have hπσv : ∀ i, ((π (σ i) : {k // k ≠ M.a}) : M.ι) =
                ((σ (π' i) : {k // k ≠ M.a}) : M.ι) := fun i => congrArg Subtype.val (hπσ i)
            have hπ'ne : π' ≠ 1 := by
              intro h1
              apply hπb
              have hi : σ (σ.symm (⟨M.b, M.a_ne_b.symm⟩ : {i // i ≠ M.a})) =
                  ⟨M.b, M.a_ne_b.symm⟩ := σ.apply_symm_apply _
              calc π ⟨M.b, M.a_ne_b.symm⟩
                  = π (σ (σ.symm ⟨M.b, M.a_ne_b.symm⟩)) := by rw [hi]
                _ = σ (π' (σ.symm ⟨M.b, M.a_ne_b.symm⟩)) := hπσ _
                _ = σ (σ.symm ⟨M.b, M.a_ne_b.symm⟩) := by rw [h1, Equiv.Perm.one_apply]
                _ = ⟨M.b, M.a_ne_b.symm⟩ := hi
            have finishD (hμc : ∀ i, μ' i = μ' ⟨0, by omega⟩)
                (hπ' : π' = Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
                  ⟨2 * k - 1, by omega⟩) :
                φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs := by
              let μ₀ : ZMod 3 := μ' ⟨0, by omega⟩
              let T : M.V →ₗ[ZMod 3] M.V :=
                (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
              have hT' : ∀ i : M.ι, i ≠ M.a →
                  T (M.coroot i) = c • μ₀ • w (M.coroot (Equiv.swap
                    (e' ⟨2 * k + 1 - 2, by omega⟩) (e' ⟨2 * k + 1 - 1, by omega⟩) i)) := by
                intro i hi
                let j : Fin (2 * k) := σ.symm ⟨i, hi⟩
                have hj : (σ j : M.ι) = i := congrArg Subtype.val (σ.apply_symm_apply ⟨i, hi⟩)
                have h1 := hT (σ j)
                rw [hj] at h1
                simp only [hπσv j, hπ'] at h1
                have hσj : (σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
                    ⟨2 * k - 1, by omega⟩ j) : M.ι) =
                    Equiv.swap (e' ⟨2 * k + 1 - 2, by omega⟩)
                      (e' ⟨2 * k + 1 - 1, by omega⟩) i := by
                  have hsa : (⟨2 * k + 1 - 2, by omega⟩ : Fin (2 * k + 1)) =
                      (⟨2 * k - 2, by omega⟩ : Fin (2 * k)).succ := by
                    apply Fin.ext
                    simp only [Fin.val_succ]
                    omega
                  have hsb : (⟨2 * k + 1 - 1, by omega⟩ : Fin (2 * k + 1)) =
                      (⟨2 * k - 1, by omega⟩ : Fin (2 * k)).succ := by
                    apply Fin.ext
                    simp only [Fin.val_succ]
                    omega
                  rw [hsa, hsb]
                  have hσa : (σ (Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
                      ⟨2 * k - 1, by omega⟩ j) : M.ι) =
                      e' ((Equiv.swap (⟨2 * k - 2, by omega⟩ : Fin (2 * k))
                        ⟨2 * k - 1, by omega⟩ j).succ) := rfl
                  rw [hσa]
                  rw [← Function.Injective.swap_apply (Fin.succ_injective (2 * k))
                    (⟨2 * k - 2, by omega⟩) (⟨2 * k - 1, by omega⟩) j]
                  rw [← show e' j.succ = i from hj]
                  exact (Function.Injective.swap_apply e'.injective
                    (⟨2 * k - 2, by omega⟩ : Fin (2 * k)).succ
                    (⟨2 * k - 1, by omega⟩ : Fin (2 * k)).succ j.succ).symm
                rw [hσj] at h1
                change ((ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V).toLinearMap
                    (M.coroot i)) = c • μ' ⟨0, by omega⟩ • w (M.coroot (Equiv.swap
                      (e' ⟨2 * k + 1 - 2, by omega⟩) (e' ⟨2 * k + 1 - 1, by omega⟩) i))
                rw [show μ' ⟨0, by omega⟩ = μ (σ j) from (hμc j).symm.trans (hμσ j).symm]
                exact h1
              have hbas' : M.toLin.Basis := hbas
              obtain ⟨w', hw'weyl, hstab⟩ :=
                ggQ2g_swap_stable (p := 3) (by decide) M.toLin hbas' (m := 2 * k + 1) (by omega)
                  e' hcox' he0' M.xV hfix1 hV hw hT' hφxV
              exact finW ⟨w', hw'weyl, fun v hv => hstab M.yV v hv⟩
            by_cases hk3 : 3 ≤ k
            · obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD (2 * k) (by omega) π' μ' hμ'0 hrel
              exact finishD hμc (hπc.resolve_left hπ'ne)
            · have hk2 : k = 2 := by omega
              subst hk2
              obtain ⟨hμc, hπ1⟩ := ggQ2g_scaledD4 π' μ' hμ'0 hrel
              by_cases hπ0 : π' 0 = 0
              · have hperm := ggQ2xa_fin4_perm π' hπ0 hπ1
                have hπ' : π' = Equiv.swap (⟨2, by omega⟩ : Fin 4) ⟨3, by omega⟩ := by
                  rcases hperm with h | h
                  · exact absurd h hπ'ne
                  · rw [h]
                    rfl
                exact finishD hμc hπ'
              · have hmove : ∀ i : {i : M.ι // i ≠ M.a}, (i : M.ι) = e' 1 →
                    ((π i : {i : M.ι // i ≠ M.a}) : M.ι) ≠ e' 1 := by
                  rintro ⟨i, hi⟩ hie
                  let j : Fin 4 := σ.symm ⟨i, hi⟩
                  have hj : (σ j : M.ι) = i := congrArg Subtype.val (σ.apply_symm_apply ⟨i, hi⟩)
                  have hjs : j = 0 := by
                    apply Fin.succ_injective 4
                    apply e'.injective
                    have h1 : e' j.succ = i := hj
                    have h2 : i = e' ((0 : Fin 4).succ) := hie
                    exact h1.trans h2
                  intro hcontra
                  have hπi : π ⟨i, hi⟩ = σ (π' j) := by
                    have h := hπσ j
                    have hσj : σ j = ⟨i, hi⟩ := σ.apply_symm_apply ⟨i, hi⟩
                    calc π ⟨i, hi⟩ = π (σ j) := congrArg π hσj.symm
                      _ = σ (π' j) := h
                  have h1 : (σ (π' j) : M.ι) = e' 1 := by
                    rw [← hπi]
                    exact hcontra
                  have h2 : e' ((π' j).succ) = e' 1 := h1
                  have h4 : π' j = 0 := by
                    apply Fin.succ_injective 4
                    apply e'.injective
                    rw [h2]
                    rfl
                  exact hπ0 (by rwa [hjs] at h4)
                exact hga hS rfl hI1 hxL hrow hno hnb M (e' : Fin 5 ≃ M.ι) hecart' he0' hV φ hφ
                  hφxV π μ c w hScaled hw hT hπb hmove
          ·
            exfalso
            let e' : Fin 7 ≃ M.ι := e
            have hecart' : ∀ i j, M.cartan (e' i) (e' j) = CartanMatrix.E 7 i j := hecart
            have he0' : M.a = e' 0 := he0
            let w₁ : M.V ≃ₗ[ZMod 3] M.V := w
            have hw₁ : w₁ ∈ M.toLin.parab {k | k ≠ M.a} := hw
            have hT₁ : ∀ i : {k // k ≠ M.a},
                ggLin (p := 3) M.model φ (M.coroot i) = c • μ i • w₁ (M.coroot (π i)) := hT
            obtain ⟨σ, hσ, hσc⟩ := ggQ2g_E7_sigma M.cartan e' M.a he0' hecart'
            obtain ⟨π', μ', hμ'0, hrel, hπσ₀, hμσ₀⟩ := ggQ2g_transport M.toLin M.a σ hσc hScaled
            have hπσ : ∀ i, π (σ i) = σ (π' i) := fun i => hπσ₀ i
            have hμσ : ∀ i, μ (σ i) = μ' i := fun i => hμσ₀ i
            obtain ⟨hμc, hπc⟩ := ggQ2g_scaledD 6 (by norm_num) π' μ' hμ'0 hrel
            have hbas' : M.toLin.Basis := hbas
            obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (M.V ≃ₗ[ZMod 3] M.V),
                A = (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model) := ⟨_, rfl⟩
            have hWA : M.toLin.weyl ≤ A := by
              rw [hAdef]
              exact M.weyl_le.trans (Subgroup.map_mono (ggAutomizer_mono Bs le_top))
            have hnorm : ∀ g ∈ A, g M.xV ∈ Submodule.span (ZMod 3) {M.xV} →
                ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod 3)
                  (c : ZMod 3), ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
                    g (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
              intro g hg hgx
              rw [hAdef, Subgroup.mem_map] at hg
              obtain ⟨φ', hφ', rfl⟩ := hg
              obtain ⟨π, μ, c, -, -, -, w, hw, h⟩ :=
                h6 φ' hφ' hgx
              exact ⟨π, μ, c, w, hw, h⟩
            obtain ⟨Φ, hΦ⟩ : ∃ Φ : M.V ≃ₗ[ZMod 3] M.V, Φ = ggLin (p := 3) M.model φ := ⟨_, rfl⟩
            have hΦA : Φ ∈ A := by
              rw [hΦ, hAdef]
              exact Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
            rw [← hΦ] at hT₁ hφxV
            have hww : w₁ ∈ M.toLin.weyl :=
              Subgroup.closure_mono (Set.image_mono (Set.subset_univ _)) hw₁
            have hwA : w₁ ∈ A := hWA hww
            have hΨA : w₁⁻¹ * Φ ∈ A := A.mul_mem (A.inv_mem hwA) hΦA
            have hinv : ∀ v, w₁⁻¹ (w₁ v) = v := fun v => w₁.symm_apply_apply v
            obtain ⟨t, htΦ⟩ := Submodule.mem_span_singleton.mp hφxV
            have ht0 : t ≠ 0 := by
              rintro rfl
              apply hx0
              apply Φ.injective
              rw [← htΦ, zero_smul, map_zero]
            have hw₁L : w₁ ∈ M.parabL {k | k ≠ M.a} := hw
            have hwy : w₁⁻¹ M.xV = M.xV :=
              (M.fixed_lin M.xV).mpr (Submodule.mem_span_singleton_self _) w₁⁻¹
                (Subgroup.inv_mem _ hw₁L)
            have hΨx : (w₁⁻¹ * Φ) M.xV = t • M.xV := by
              show w₁⁻¹ (Φ M.xV) = _
              rw [← htΦ, map_smul, hwy]
            have hscalar : ∀ s : ZMod 3, s ≠ 0 → s = 1 ∨ s = 2 := by
              intro s hs
              rcases CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one s hs with h | h
              · exact Or.inl h
              · exact Or.inr (by rw [h]; exact ggQ2xa_neg_one)
            have hs0 : c * μ' ⟨0, by norm_num⟩ ≠ 0 := mul_ne_zero hc0 (hμ'0 _)
            have hs : c * μ' ⟨0, by norm_num⟩ = 1 ∨ c * μ' ⟨0, by norm_num⟩ = 2 := hscalar _ hs0
            have ht : t = 1 ∨ t = 2 := hscalar t ht0
            obtain ⟨i, hi⟩ := σ.surjective ⟨M.b, M.a_ne_b.symm⟩
            have hπ'ne : π' ≠ 1 := by
              intro h1
              exact hπb (by rw [← hi, hπσ i, h1, Equiv.Perm.one_apply])
            have hπ' : π' = Equiv.swap (⟨6 - 2, by omega⟩ : Fin 6) ⟨6 - 1, by omega⟩ :=
              hπc.resolve_left hπ'ne
            have hΨσ : ∀ i : Fin 6, (w₁⁻¹ * Φ) (M.coroot (σ i : M.ι)) =
                (c * μ' ⟨0, by norm_num⟩) • M.coroot (σ (π' i) : M.ι) := by
              intro i
              have h1 := hT₁ (σ i)
              rw [hπσ i, hμσ i, hμc i] at h1
              show w₁⁻¹ (Φ (M.coroot (σ i : M.ι))) = _
              rw [h1, map_smul, map_smul, hinv, smul_smul]
            refine ggQ2g_E7_false M.toLin e' hecart' hbas' A hWA M.xV M.a he0' hV hfix1 hnorm
              (w₁⁻¹ * Φ) hΨA _ t hs ht hΨx ?_
            intro j hj
            obtain ⟨i, hi⟩ := ggQ2xa_tau_surj j hj
            have hσi : (σ i : M.ι) = e' j := by rw [hσ i, hi]
            have hσπ : (σ (π' i) : M.ι) = e' (ggg7_tau j) := by
              rw [hσ, hπ', ggQ2xa_tau_swap i, hi]
            show (w₁⁻¹ * Φ) (M.coroot (e' j)) =
              (c * μ' ⟨0, by norm_num⟩) • M.coroot (e' (ggg7_tau j))
            rw [← hσi, hΨσ i, hσπ]
        · obtain ⟨i, j, hij⟩ := ggQ2_no_F4_leaf M.coxeter M.isWeyl M.a f
          exact absurd (ggQ2xa_F4_coxeter M.coxeter M.cartan M.isCartan M.a f
            (Or.inl hf) i j) hij
        · obtain ⟨i, j, hij⟩ := ggQ2_no_F4_leaf M.coxeter M.isWeyl M.a f
          exact absurd (ggQ2xa_F4_coxeter M.coxeter M.cartan M.isCartan M.a f
            (Or.inr hf) i j) hij

theorem ggQ2_gammaXPosNoModel_of_ambRes (hLN : GGLNoncyclicInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h1 : GGQTwoModelInput) (h1b : GGQTwoNoTwoNodeIndInput)
    (h5 : GGQTwoCentralizerInput) (hamb : GGQ2AmbModelInput)
    (hga : GGQ2GammaXGraphD5AmbInput) : GGQ2GammaXPosNoModelInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ hrow hno u hu
  by_cases hex : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K
  · obtain ⟨y, K, hnb⟩ := hex
    obtain ⟨hL, hK⟩ := h1b G p B Bs x L D J hS hI1 y K hnb
    have hL' : ¬ GGQTwoTwoNodeRowAt p L J := fun h => hrow ⟨y, K, hnb, Or.inl ⟨h, hL h⟩⟩
    have hK' : ¬ GGQTwoTwoNodeRowAt p K J := fun h => hrow ⟨y, K, hnb, Or.inr ⟨h, hK h⟩⟩
    have hW : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
      rcases h1 G p B Bs x L D J hS hI1 y K hnb with h | h | hM | hW
      · exact absurd h hL'
      · exact absurd h hK'
      · exact absurd hM (hno y K hnb)
      · exact hW.1
    obtain ⟨M, hbas, hnd, hdet⟩ := hamb hS hp hI1 hxL hrow hno hnb hL' hK' hW
    exact ggQ2_gammaX_of_ambModelRes hLB hP h5 hga hS hp hI1 hxL hrow hno hnb M hbas hnd hdet hu
  · exact ggQ2_gammaX_of_noNbr hLN hS (fun y K hnb => hex ⟨y, K, hnb⟩) hu

end CFSG.StandardType

end
