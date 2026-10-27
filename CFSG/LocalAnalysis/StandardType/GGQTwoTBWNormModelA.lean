module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbInner
import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbResEvenD
import CFSG.LocalAnalysis.StandardType.GGQTwoDFourLeafNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDForkNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl
import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
import CFSG.LocalAnalysis.StandardType.GGQTwoSwapAB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGQ2Lin.linearIndependent_compl_of_det {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : D.ι)
    (hdet : ((D.cartan.submatrix (fun i : {k // k ≠ e} => (i : D.ι))
      (fun i : {k // k ≠ e} => (i : D.ι))).det : ZMod p) ≠ 0) :
    LinearIndependent (ZMod p) (fun i : {k // k ≠ e} => D.coroot i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro κ hκ i
  have hmat : ((Int.castRingHom (ZMod p)).mapMatrix (D.cartan.submatrix
      (fun i : {k // k ≠ e} => (i : D.ι)) (fun i : {k // k ≠ e} => (i : D.ι)))).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdet
  have h0 : ((Int.castRingHom (ZMod p)).mapMatrix (D.cartan.submatrix
      (fun i : {k // k ≠ e} => (i : D.ι)) (fun i : {k // k ≠ e} => (i : D.ι)))).mulVec κ = 0 := by
    funext j
    have h := congrArg (D.root (j : D.ι)) hκ
    simp only [map_sum, map_smul, smul_eq_mul, D.pairing, map_zero] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hmat h0) i

theorem ggQ2_uniqueNbr_of_equiv {ι : Type*} (C : Matrix ι ι ℤ) {n : ℕ}
    (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ ι) (hC : ∀ i j, C (e i) (e j) = C₀ i j)
    (k : Fin n) (hk : ∃! j, j ≠ k ∧ C₀ k j ≠ 0) : ∃! c, c ≠ e k ∧ C (e k) c ≠ 0 := by
  obtain ⟨j, ⟨hjk, hj⟩, huniq⟩ := hk
  refine ⟨e j, ⟨fun h => hjk (e.injective h), by rwa [hC]⟩, ?_⟩
  rintro c ⟨hc, hc'⟩
  obtain ⟨i, rfl⟩ := e.surjective c
  rw [huniq i ⟨fun h => hc (by rw [h]), by rwa [← hC]⟩]

theorem GGQ2Lin.innerNormal_of_normalizer (D : GGQ2Lin 3) (xV : D.V)
    (hfix : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {xV})
    (hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i))
    (hdim : Module.finrank (ZMod 3) D.V ≤ Fintype.card {k // k ≠ D.a} + 1)
    (hTF : TransvectionFree (D.parab {k | k ≠ D.a})) (hin : D.WeylInnerLeaf D.a)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ c : ZMod 3, c ≠ 0 ∧ ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : {k // k ≠ D.a},
      T (D.coroot i) = c • w (D.coroot i) := by
  classical
  obtain ⟨n, C, f, hC, hW⟩ := hin
  obtain ⟨w, hw, hconj⟩ := GGQ2Lin.inner_of_transport D C f hC hind hdim hTF hW T hT
  set S : D.V ≃ₗ[ZMod 3] D.V := w⁻¹ * T with hSdef
  have hcommS : ∀ g ∈ D.parab {k | k ≠ D.a}, S * g = g * S := by
    intro g hg
    have h1 : S * g * S⁻¹ = g := by
      rw [hSdef]
      calc (w⁻¹ * T) * g * (w⁻¹ * T)⁻¹ = w⁻¹ * (T * g * T⁻¹) * w := by group
        _ = w⁻¹ * (w * g * w⁻¹) * w := by rw [hconj g hg]
        _ = g := by group
    calc S * g = (S * g * S⁻¹) * S := by group
      _ = g * S := by rw [h1]
  have hcommS' : ∀ g ∈ D.parab {k | k ≠ D.a}, ∀ v : D.V, S (g v) = g (S v) := by
    intro g hg v
    have h := congrArg (fun e : D.V ≃ₗ[ZMod 3] D.V => e v) (hcommS g hg)
    simpa only [LinearEquiv.mul_apply] using h
  obtain ⟨c, hc⟩ := GGQ2Lin.exists_scalar_of_commute rfl D xV hfix
    (GGQ2Lin.reflTransGen_compl_leaf rfl D) (S : D.V →ₗ[ZMod 3] D.V) (fun g hg v => by
      let g₁ : D.V ≃ₗ[ZMod 3] D.V := g
      let v₁ : D.V := v
      have h' : (S : D.V →ₗ[ZMod 3] D.V) (g₁ v₁) = g₁ ((S : D.V →ₗ[ZMod 3] D.V) v₁) :=
        hcommS' g₁ hg v₁
      show (S : D.V →ₗ[ZMod 3] D.V) (g₁ v₁) - g₁ ((S : D.V →ₗ[ZMod 3] D.V) v₁) ∈
        Submodule.span (ZMod 3) {xV}
      rw [h', sub_self]
      exact Submodule.zero_mem _)
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hSh : ∀ i : {k // k ≠ D.a}, S (D.coroot i) = c • D.coroot i := by
    intro i
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hc (D.coroot i))
    let r : D.V ≃ₗ[ZMod 3] D.V := D.simpleRefl (i : D.ι)
    have hri : r ∈ D.parab {k | k ≠ D.a} := Subgroup.subset_closure ⟨(i : D.ι), i.2, rfl⟩
    have hrx : r xV = xV := (hfix xV).mpr (Submodule.mem_span_singleton_self _) r hri
    have hrh : r (D.coroot i) = -D.coroot i := by
      have h := ggQ2xKDt_simpleRefl_apply D (i : D.ι) (D.coroot i)
      have h2' : D.root (i : D.ι) (D.coroot (i : D.ι)) = 2 := D.root_coroot_self (i : D.ι)
      change r (D.coroot i) = D.coroot i - D.root (i : D.ι) (D.coroot i) • D.coroot i at h
      rw [h]
      change D.coroot i - D.root (i : D.ι) (D.coroot (i : D.ι)) • D.coroot i = -D.coroot i
      rw [h2']
      module
    have hSi : S (D.coroot i) = c • D.coroot i + t • xV := by
      have h' : (S : D.V →ₗ[ZMod 3] D.V) (D.coroot i) - c • D.coroot i = t • xV := ht.symm
      rw [← h']
      simp
    have hcom := hcommS' r hri (D.coroot i)
    rw [hrh, map_neg, hSi, map_add, map_smul, map_smul, hrh, hrx] at hcom
    have htx : t • xV = 0 := by
      have h3 : (2 * t) • xV = 0 := by
        have h4 : (2 * t) • xV = (c • -D.coroot i + t • xV) - -(c • D.coroot i + t • xV) := by
          module
        rw [h4, ← hcom, sub_self]
      rw [mul_smul] at h3
      exact (smul_eq_zero.mp h3).resolve_left h2
    rw [hSi, htx, add_zero]
  have hc0 : c ≠ 0 := by
    intro hc0
    let ib : {k // k ≠ D.a} := ⟨D.b, D.a_ne_b.symm⟩
    have h0 : S (D.coroot ib) = 0 := by rw [hSh ib, hc0, zero_smul]
    have hb0 : D.coroot ib = 0 := by
      have h' := congrArg S.symm h0
      rwa [S.symm_apply_apply, map_zero] at h'
    have hroot : D.root (ib : D.ι) (D.coroot (ib : D.ι)) = 2 := D.root_coroot_self (ib : D.ι)
    rw [hb0, map_zero] at hroot
    exact h2 hroot.symm
  refine ⟨c, hc0, w, hw, fun i => ?_⟩
  have hT' : T = w * S := by
    rw [hSdef, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hT', LinearEquiv.mul_apply, hSh i, map_smul]

theorem GGQ2Lin.normalForm_of_normalizer (D : GGQ2Lin 3) [Module.Finite (ZMod 3) D.V]
    (h4 : 4 ≤ Module.finrank (ZMod 3) D.V) (xV : D.V)
    (hfix : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {xV})
    (hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i))
    (hTF : TransvectionFree (D.parab {k | k ≠ D.a})) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ (π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}) (c : ZMod 3), c ≠ 0 ∧
      (∀ i j : {k // k ≠ D.a}, D.cartan (π i) (π j) = D.cartan i j) ∧
      ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : {k // k ≠ D.a},
        T (D.coroot i) = c • w (D.coroot (π i)) := by
  classical
  have hdim := D.finrank_le_card_compl_add_one xV hfix
  by_cases hin : D.WeylInnerLeaf D.a
  · obtain ⟨c, hc0, w, hw, hTw⟩ := D.innerNormal_of_normalizer xV hfix hind hdim hTF hin T hT
    exact ⟨Equiv.refl _, c, hc0, fun i j => rfl, w, hw, fun i => hTw i⟩
  · obtain ⟨n, f, hn4, -, hf⟩ := D.evenDLeaf_of_not_weylInnerLeaf (by omega) hin
    rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
    · exact GGQ2Lin.diag_of_transport D (CartanMatrix.D 4) f hf hind ggQ2WeylDiag_D4 T hT
    · exact ggQ2_dNormal_of_normalizer D hn5 f hf hind T hT

private lemma ggQ2ma_lin_simple {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {D L J K : Subgroup G} (M : GGQTwoModel 3 Bs x y D L J K) (k : M.ι) :
    ggLin (p := 3) M.model (M.simple k) = M.toLin.simpleRefl k :=
  ggLin_eq_reflection (p := 3) M.model (M.toLin.root_coroot_self k) (M.simple_apply k)

private lemma ggQ2ma_map_automizer_L {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {D L J K : Subgroup G} (M : GGQTwoModel 3 Bs x y D L J K) :
    (ggAutomizer L Bs).map (ggLin (p := 3) M.model) = M.parabL {k | k ≠ M.a} := by
  rw [M.automizer_L, MonoidHom.map_closure]
  unfold GGQTwoModel.parabL GGQ2Lin.parab
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (ggQ2ma_lin_simple M k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨M.simple k, ⟨k, hk, rfl⟩, ggQ2ma_lin_simple M k⟩

theorem ggQ2_tbwNorm_at_a (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) [Fact p.Prime]
    {y : G} {K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i)) (u : M.V)
    (hfix : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u})
    (hu : u ∉ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i))
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφu : ggLin (p := p) M.model φ u ∈ Submodule.span (ZMod p) {u}) :
    ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p),
      c ≠ 0 ∧ (∀ i, μ i ≠ 0) ∧
      (∀ i j : {k // k ≠ M.a},
        μ i * (M.cartan i j : ZMod p) = μ j * (M.cartan (π i) (π j) : ZMod p)) ∧
      ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
        ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
    have hcard : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
      calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
        _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
        _ = 3 ^ Module.finrank (ZMod 3) M.V := (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
    have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard] at hp4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp4
  have hfixx : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := (ggQ2_fixed_lin M).1
  have hux : u ∈ Submodule.span (ZMod 3) {M.xV} :=
    (hfixx u).mp ((hfix u).mpr (Submodule.mem_span_singleton_self u))
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hux
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hu
    rw [← ht, zero_smul]
    exact Submodule.zero_mem _
  have hφx : ggLin (p := 3) M.model φ M.xV ∈ Submodule.span (ZMod 3) {M.xV} := by
    have hxu : M.xV = t⁻¹ • u := by
      rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hφu
    refine Submodule.mem_span_singleton.mpr ⟨s, ?_⟩
    rw [hxu, map_smul, ← hs, ← ht, smul_comm]
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφx
  have hφxg : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hx c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hH hAJS M.hx hφ hφxg
  have hTnorm : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [← ggQ2ma_map_automizer_L M]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model) (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hTF : TransvectionFree (M.parabL {k | k ≠ M.a}) := by
    intro g hg
    refine ggQ2_transvectionFree M hH.2.2.2.1 g ?_
    rw [← ggQ2ma_map_automizer_L M] at hg
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
    exact Subgroup.mem_map.mpr ⟨ψ, ggAutomizer_mono Bs le_top hψ, rfl⟩
  have : Module.Finite (ZMod 3) M.toLin.V := (inferInstance : Module.Finite (ZMod 3) M.V)
  obtain ⟨π, c, hc0, hπ, w, hw, hTw⟩ : ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (c : ZMod 3),
      c ≠ 0 ∧ (∀ i j : {k // k ≠ M.a}, M.cartan (π i) (π j) = M.cartan i j) ∧
      ∃ w ∈ M.parabL {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
        ggLin (p := 3) M.model φ (M.coroot i) = c • w (M.coroot (π i)) :=
    M.toLin.normalForm_of_normalizer h4 M.xV hfixx hind hTF _ hTnorm
  refine ⟨π, fun _ => 1, c, hc0, fun _ => one_ne_zero, fun i j => by rw [hπ i j], w, hw,
    fun i => ?_⟩
  rw [one_smul]
  exact hTw i

private lemma ggQ2ma_map_automizer_K {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {D L J K : Subgroup G} (M : GGQTwoModel 3 Bs x y D L J K) :
    (ggAutomizer K Bs).map (ggLin (p := 3) M.model) = M.parabL {k | k ≠ M.b} := by
  rw [M.automizer_K, MonoidHom.map_closure]
  unfold GGQTwoModel.parabL GGQ2Lin.parab
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (ggQ2ma_lin_simple M k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨M.simple k, ⟨k, hk, rfl⟩, ggQ2ma_lin_simple M k⟩

theorem ggQ2_linNbrLineStab_normalizes (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hK1 : GGQTwoK1 3 B Bs x D J) (M : GGQTwoModel 3 Bs x y D L J K)
    {g : M.V ≃ₗ[ZMod 3] M.V} (hg : g ∈ M.linGroup)
    (hgy : g M.yV ∈ Submodule.span (ZMod 3) {M.yV}) :
    g ∈ Subgroup.normalizer (M.parabL {k | k ≠ M.b} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
  rw [GGQTwoModel.linGroup, Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hgy
  have hφyg : φ ⟨y, M.hy⟩ ∈ Subgroup.zpowers (⟨y, M.hy⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hy c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    ggQ2_nbrLineStab_normalizes hLB hP hS.1 (ggQ2_ajOfSetting hP h5 hS) hK1 hnb M.hy hφ hφyg
  rw [← ggQ2ma_map_automizer_K M]
  exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model) (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)

theorem ggQ2_tbwNorm_at_b (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) [Fact p.Prime]
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK1 : GGQTwoK1 p B Bs x D J)
    (M : GGQTwoModel p Bs x y D L J K) (hb : ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0)
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.b} => M.coroot i)) (u : M.V)
    (hfix : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u})
    (hu : u ∉ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.b} => M.coroot i))
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφu : ggLin (p := p) M.model φ u ∈ Submodule.span (ZMod p) {u}) :
    ∃ (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (μ : {k // k ≠ M.b} → ZMod p) (c : ZMod p),
      c ≠ 0 ∧ (∀ i, μ i ≠ 0) ∧
      (∀ i j : {k // k ≠ M.b},
        μ i * (M.cartan i j : ZMod p) = μ j * (M.cartan (π i) (π j) : ZMod p)) ∧
      ∃ w ∈ M.toLin.parab {k | k ≠ M.b}, ∀ i : {k // k ≠ M.b},
        ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
    have hcard : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
      calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
        _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
        _ = 3 ^ Module.finrank (ZMod 3) M.V := (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
    have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard] at hp4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp4
  have hfixy : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.yV} := (ggQ2_fixed_lin M).2
  have huy : u ∈ Submodule.span (ZMod 3) {M.yV} :=
    (hfixy u).mp ((hfix u).mpr (Submodule.mem_span_singleton_self u))
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp huy
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hu
    rw [← ht, zero_smul]
    exact Submodule.zero_mem _
  have hφy : ggLin (p := 3) M.model φ M.yV ∈ Submodule.span (ZMod 3) {M.yV} := by
    have hyu : M.yV = t⁻¹ • u := by
      rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hφu
    refine Submodule.mem_span_singleton.mpr ⟨s, ?_⟩
    rw [hyu, map_smul, ← hs, ← ht, smul_comm]
  have hTnorm : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.b} : Set (M.V ≃ₗ[ZMod 3] M.V)) :=
    ggQ2_linNbrLineStab_normalizes hLB hP h5 hS hnb hK1 M (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩) hφy
  have hTF : TransvectionFree (M.parabL {k | k ≠ M.b}) := by
    intro g hg
    refine ggQ2_transvectionFree M hH.2.2.2.1 g ?_
    rw [← ggQ2ma_map_automizer_K M] at hg
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
    exact Subgroup.mem_map.mpr ⟨ψ, ggAutomizer_mono Bs le_top hψ, rfl⟩
  let D' : GGQ2Lin 3 := M.toLin.swapAB hb
  have : Module.Finite (ZMod 3) D'.V := (inferInstance : Module.Finite (ZMod 3) M.V)
  obtain ⟨π, c, hc0, hπ, w, hw, hTw⟩ : ∃ (π : {k // k ≠ M.b} ≃ {k // k ≠ M.b}) (c : ZMod 3),
      c ≠ 0 ∧ (∀ i j : {k // k ≠ M.b}, M.cartan (π i) (π j) = M.cartan i j) ∧
      ∃ w ∈ M.parabL {k | k ≠ M.b}, ∀ i : {k // k ≠ M.b},
        ggLin (p := 3) M.model φ (M.coroot i) = c • w (M.coroot (π i)) :=
    D'.normalForm_of_normalizer h4 M.yV hfixy hind hTF _ hTnorm
  refine ⟨π, fun _ => 1, c, hc0, fun _ => one_ne_zero, fun i j => by rw [hπ i j], w, hw,
    fun i => ?_⟩
  rw [one_smul]
  exact hTw i

end CFSG.StandardType

end
