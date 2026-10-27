module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual
public import CFSG.LocalAnalysis.StandardType.GGIntCartanTwoLeafKer
public import CFSG.LocalAnalysis.StandardType.GGQTwoSwapAB
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphCommon
public import CFSG.LocalAnalysis.StandardType.GGIntCartanLeafKer

public section

namespace CFSG.StandardType

open CFSG Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def GGQ2Lin.dualTranspose {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    GGQ2Lin p where
  ι := D.ι
  coxeter := D.coxeter
  cartan := D.cartan.transpose
  V := Module.Dual (ZMod p) D.V
  coroot := D.root
  root := fun k => Module.Dual.eval (ZMod p) D.V (D.coroot k)
  a := D.a
  b := D.b
  a_ne_b := D.a_ne_b
  a_leaf := by
    obtain ⟨c, ⟨hca, hac⟩, huniq⟩ := D.a_leaf
    refine ⟨c, ⟨hca, ?_⟩, fun d ⟨hda, had⟩ => huniq d ⟨hda, ?_⟩⟩
    · intro h0
      exact hac (D.isCartan.eq_zero_symm hca.symm h0)
    · intro h0
      exact had (D.isCartan.eq_zero_symm hda h0)
  isWeyl := D.isWeyl
  isCartan := by
    refine ⟨fun i => by simpa using D.isCartan.1 i, fun i j hij => ?_⟩
    simp only [Matrix.transpose_apply]
    rcases D.isCartan.2 i j hij with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ |
        ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h3, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))
  pairing := fun i j => by
    simp [D.pairing]

theorem ggContra_simpleRefl_dualTranspose {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    ggContra (D.simpleRefl k) = D.dualTranspose.simpleRefl k := by
  have h_ours : (Dual.eval (ZMod p) D.V) (D.coroot k) (D.root k) = 2 := by
    simpa using D.root_coroot_self k
  ext f v
  rw [ggContra_apply]
  change f ((Module.reflection (D.root_coroot_self k)).symm v) =
    (Module.reflection h_ours) f v
  rw [Module.reflection_symm (D.root_coroot_self k),
    Module.reflection_apply v (D.root_coroot_self k), Module.reflection_apply f h_ours]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Dual.eval_apply,
    smul_eq_mul]
  ring

theorem ggContra_parab_dualTranspose {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (S : Set D.ι) :
    (D.parab S).map ggContra = D.dualTranspose.parab S := by
  change (Subgroup.closure (D.simpleRefl '' S)).map ggContra =
    Subgroup.closure (D.dualTranspose.simpleRefl '' S)
  rw [MonoidHom.map_closure, Set.image_image]
  congr 1
  exact Set.image_congr (fun k _ => ggContra_simpleRefl_dualTranspose D k)

theorem GGQ2Lin.ker_pi_root_le {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u}) :
    LinearMap.ker (LinearMap.pi fun i : {k // k ≠ D.a} => D.root i) ≤
      Submodule.span (ZMod p) {u} := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [← hfix v]
  intro g hg
  have hv0 : ∀ i : {k // k ≠ D.a}, D.root i v = 0 := fun i => congrFun hv i
  have hg' : g ∈ Subgroup.closure (D.simpleRefl '' {k | k ≠ D.a}) := hg
  refine Subgroup.closure_induction (p := fun g _ => g v = v) ?_ ?_ ?_ ?_ hg'
  · rintro g ⟨k, hk, rfl⟩
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply, hv0 ⟨k, hk⟩, zero_smul, sub_zero]
  · rfl
  · intro g h _ _ hg hh
    rw [LinearEquiv.mul_apply, hh, hg]
  · intro g _ hg
    have h1 : g.symm (g v) = v := g.symm_apply_apply v
    rw [hg] at h1
    exact h1

theorem GGQ2Lin.finrank_le_card_add_one_of_fix {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u}) :
    Module.finrank (ZMod p) D.V ≤ Fintype.card {k // k ≠ D.a} + 1 := by
  classical
  by_cases hfd : FiniteDimensional (ZMod p) D.V
  swap
  · rw [Module.finrank_of_not_finite hfd]
    omega
  let Φ : D.V →ₗ[ZMod p] ({k // k ≠ D.a} → ZMod p) := LinearMap.pi fun i => D.root i
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hr : Module.finrank (ZMod p) (LinearMap.range Φ) ≤ Fintype.card {k // k ≠ D.a} := by
    have h := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hsp : Module.finrank (ZMod p) (Submodule.span (ZMod p) {u}) ≤ 1 := by
    by_cases h0 : u = 0
    · rw [h0, Submodule.span_zero_singleton, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton h0]
  have hk : Module.finrank (ZMod p) (LinearMap.ker Φ) ≤ 1 :=
    (Submodule.finrank_mono (GGQ2Lin.ker_pi_root_le D u hfix)).trans hsp
  omega

theorem GGQ2Lin.root_linearIndependent_of_finrank {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (D : GGQ2Lin p) (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {u})
    (hdim : Module.finrank (ZMod p) D.V = Fintype.card {k // k ≠ D.a} + 1) :
    LinearIndependent (ZMod p) (fun i : {k // k ≠ D.a} => D.root i) := by
  classical
  have : FiniteDimensional (ZMod p) D.V := Module.finite_of_finrank_pos (by omega)
  let Φ : D.V →ₗ[ZMod p] ({k // k ≠ D.a} → ZMod p) := LinearMap.pi fun i => D.root i
  have hker : LinearMap.ker Φ = Submodule.span (ZMod p) {u} := by
    refine le_antisymm (GGQ2Lin.ker_pi_root_le D u hfix) fun v hv => ?_
    rw [LinearMap.mem_ker]
    rw [← hfix v] at hv
    funext i
    have h1 : D.simpleRefl i v = v := hv _ (Subgroup.subset_closure ⟨i.1, i.2, rfl⟩)
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply] at h1
    have h2 : D.root i v • D.coroot i = 0 := sub_eq_self.mp h1
    have hc : D.coroot i ≠ 0 := by
      intro h0
      have h3 := D.root_coroot_self i
      rw [h0, map_zero] at h3
      exact zmod_two_ne_zero hp h3.symm
    exact (smul_eq_zero.mp h2).resolve_right hc
  have hrange : LinearMap.range Φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hker, finrank_span_singleton hu0, hdim] at hrn
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨v, hv⟩ : ∃ v, Φ v = Pi.single j 1 := by
    have : Pi.single j (1 : ZMod p) ∈ LinearMap.range Φ := by rw [hrange]; trivial
    exact this
  have h1 := congrArg (fun f : Module.Dual (ZMod p) D.V => f v) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at h1
  have hvi : ∀ i : {k // k ≠ D.a},
      D.root i v = (Pi.single j (1 : ZMod p) : {k // k ≠ D.a} → ZMod p) i :=
    fun i => congrFun hv i
  simp only [hvi, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  exact h1

theorem GGQ2Lin.inner_of_ker (D : GGQ2Lin 3) (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {u})
    (hker : ∃ κ : {k // k ≠ D.a} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ D.a}, ∑ j : {k // k ≠ D.a}, (D.cartan i j : ZMod 3) * κ j = 0)
    (hdim : Module.finrank (ZMod 3) D.V ≤ Fintype.card {k // k ≠ D.a} + 1)
    (h4 : 4 ≤ Module.finrank (ZMod 3) D.V)
    (hTF : TransvectionFree (D.parab {k | k ≠ D.a}))
    (hpos : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i) ∨
      Module.finrank (ZMod 3) D.V = Fintype.card {k // k ≠ D.a} + 1)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ g ∈ D.parab {k | k ≠ D.a}, T * g * T⁻¹ = w * g * w⁻¹ := by
  classical
  have hcard : 3 ≤ Fintype.card {k // k ≠ D.a} := by omega
  obtain ⟨n, C₀, e, hC, hsymm, hW⟩ : ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ)
      (e : Fin n ≃ {k // k ≠ D.a}), (∀ i j, D.cartan (e i) (e j) = C₀ i j) ∧
        (∀ i j, C₀ i j = C₀ j i) ∧ GGQ2WeylInner n C₀ := by
    rcases GGQ2Lin.compl_leaf_A_or_E6_of_ker D hker hcard with ⟨k, hk, e, he⟩ | ⟨e, he⟩
    · refine ⟨3 * k - 1, CartanMatrix.A (3 * k - 1), e, he, fun i j => ?_,
        ggQ2WeylInner_A (by omega)⟩
      exact congrFun (congrFun (CartanMatrix.A_transpose (3 * k - 1)) j) i
    · refine ⟨6, CartanMatrix.E 6, e, he, fun i j => ?_, ggQ2WeylInner_E6⟩
      exact congrFun (congrFun (CartanMatrix.E_transpose 6) j) i
  rcases hpos with hind | hdimeq
  · exact GGQ2Lin.inner_of_transport D C₀ e hC hind hdim hTF hW T hT
  have : FiniteDimensional (ZMod 3) D.V := Module.finite_of_finrank_pos (by omega)
  let Wd : Subgroup (Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Module.Dual (ZMod 3) D.V) :=
    (D.parab {k | k ≠ D.a}).map ggContra
  have hpar : Wd = D.dualTranspose.parab {k | k ≠ D.dualTranspose.a} :=
    ggContra_parab_dualTranspose D _
  have hC' : ∀ i j, D.dualTranspose.cartan (e i).1 (e j).1 = C₀ i j := fun i j => by
    change D.cartan (e j).1 (e i).1 = C₀ i j
    rw [hC, hsymm]
  have hind' : LinearIndependent (ZMod 3)
      (fun i : {k // k ≠ D.dualTranspose.a} => D.dualTranspose.coroot i) :=
    GGQ2Lin.root_linearIndependent_of_finrank (by decide) D u hu0 hfix hdimeq
  have hdim' : Module.finrank (ZMod 3) D.dualTranspose.V ≤
      Fintype.card {k // k ≠ D.dualTranspose.a} + 1 := by
    change Module.finrank (ZMod 3) (Module.Dual (ZMod 3) D.V) ≤ Fintype.card {k // k ≠ D.a} + 1
    rw [Subspace.dual_finrank_eq]
    exact hdim
  have hTFd : TransvectionFree Wd := ggContra_transvectionFree hTF
  have hTd : ggContra T ∈ Subgroup.normalizer (Wd : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g'
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨T * g * T⁻¹, (Subgroup.mem_normalizer_iff.mp hT g).mp hg, ?_⟩
      simp only [map_mul, map_inv]
    · rintro ⟨g, hg, hgg⟩
      refine ⟨T⁻¹ * g * T, ?_, ?_⟩
      · have h2 : T * (T⁻¹ * g * T) * T⁻¹ = g := by group
        exact (Subgroup.mem_normalizer_iff.mp hT (T⁻¹ * g * T)).mpr (by rw [h2]; exact hg)
      · have h3 : ggContra (T⁻¹ * g * T) = (ggContra T)⁻¹ * ggContra g * ggContra T := by
          rw [map_mul, map_mul, map_inv]
        rw [h3, hgg]
        group
  obtain ⟨w', hw', hconj'⟩ :=
    GGQ2Lin.inner_of_transport D.dualTranspose C₀ e hC' hind' hdim' (hpar ▸ hTFd) hW (ggContra T)
      (hpar ▸ hTd)
  have hw'd : w' ∈ Wd := hpar ▸ hw'
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'd
  refine ⟨w, hw, fun g hg => ggContra_injective ?_⟩
  have hgd : ggContra g ∈ D.dualTranspose.parab {k | k ≠ D.dualTranspose.a} :=
    hpar ▸ Subgroup.mem_map_of_mem _ hg
  have h := hconj' (ggContra g) hgd
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  exact h

theorem GGQ2Lin.pmW_of_ker (D : GGQ2Lin 3) (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {u})
    (hker : ∃ κ : {k // k ≠ D.a} → ZMod 3, κ ≠ 0 ∧
      ∀ i : {k // k ≠ D.a}, ∑ j : {k // k ≠ D.a}, (D.cartan i j : ZMod 3) * κ j = 0)
    (hdim : Module.finrank (ZMod 3) D.V ≤ Fintype.card {k // k ≠ D.a} + 1)
    (h4 : 4 ≤ Module.finrank (ZMod 3) D.V)
    (hTF : TransvectionFree (D.parab {k | k ≠ D.a}))
    (hpos : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i) ∨
      Module.finrank (ZMod 3) D.V = Fintype.card {k // k ≠ D.a} + 1)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u} :=
  GGQ2Lin.pmW_of_inner rfl D u hfix T
    (GGQ2Lin.inner_of_ker D u hu0 hfix hker hdim h4 hTF hpos T hT)

private theorem ggQ2pw_root_not_linearIndependent {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    [FiniteDimensional (ZMod p) D.V] (c : D.ι) {u : D.V} (hu : u ≠ 0)
    (hα : ∀ j : {k // k ≠ c}, D.root j u = 0)
    (hdim : Module.finrank (ZMod p) D.V ≤ Fintype.card {k // k ≠ c}) :
    ¬ LinearIndependent (ZMod p) (fun j : {k // k ≠ c} => D.root j) := by
  intro hind
  have hle : Submodule.span (ZMod p) (Set.range fun j : {k // k ≠ c} => D.root j) ≤
      (Submodule.span (ZMod p) {u}).dualAnnihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro w hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hα j, smul_zero]
  have h1 := finrank_span_eq_card hind
  have h2 := Submodule.finrank_mono hle
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span (ZMod p) {u})
  rw [finrank_span_singleton hu] at h3
  omega

theorem GGQ2Lin.card_le_finrank (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hb : ∃! c, c ≠ D.b ∧ D.cartan D.b c ≠ 0) {ua ub : D.V} (hua : ua ≠ 0) (hub : ub ≠ 0)
    (hfixa : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ua})
    (hfixb : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ub}) :
    Fintype.card D.ι ≤ Module.finrank (ZMod 3) D.V := by
  classical
  by_contra hlt
  have hcard : ∀ c : D.ι, Fintype.card D.ι = 1 + Fintype.card {k // k ≠ c} := fun c => by
    rw [Fintype.card_eq_sum_ones, Fintype.card_eq_sum_ones (α := {k // k ≠ c}),
      Fintype.sum_eq_add_sum_subtype_ne _ c]
  have hαa : ∀ j : {k // k ≠ D.a}, D.root j ua = 0 := GGQ2Lin.root_eq_zero_of_fix rfl D ua hfixa
  have hαb : ∀ j : {k // k ≠ D.b}, D.root j ub = 0 :=
    GGQ2Lin.root_eq_zero_of_fix rfl (D.swapAB hb) ub hfixb
  have hda := ggQ2pw_root_not_linearIndependent D D.a hua hαa (by have := hcard D.a; omega)
  have hdb := ggQ2pw_root_not_linearIndependent D D.b hub hαb (by have := hcard D.b; omega)
  have hext : ∀ (c : D.ι) (r : {k // k ≠ c} → ZMod 3), ∑ j, r j • D.root j = 0 →
      ∀ i, ∑ j, (D.cartan.transpose i j : ZMod 3) *
        (fun k => if h : k = c then (0 : ZMod 3) else r ⟨k, h⟩) j = 0 := by
    intro c r hr i
    have h1 := congrArg (fun f : Module.Dual (ZMod 3) D.V => f (D.coroot i)) hr
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, D.pairing,
      LinearMap.zero_apply] at h1
    rw [Fintype.sum_eq_add_sum_subtype_ne _ c]
    simp only [Matrix.transpose_apply, dite_true, mul_zero, zero_add]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
    rw [dif_neg j.2, mul_comm]
  have hbT : ∃! c, c ≠ D.b ∧ D.cartan.transpose D.b c ≠ 0 := by
    obtain ⟨c, ⟨hcb, hbc⟩, huniq⟩ := hb
    refine ⟨c, ⟨hcb, ?_⟩, fun d ⟨hdb, hbd⟩ => huniq d ⟨hdb, ?_⟩⟩
    · intro h0
      exact hbc (D.isCartan.eq_zero_symm hcb.symm h0)
    · intro h0
      exact hbd (D.isCartan.eq_zero_symm hdb h0)
  obtain ⟨ra, hra, ia, hia⟩ := Fintype.not_linearIndependent_iff.mp hda
  obtain ⟨rb, hrb, ib, hib⟩ := Fintype.not_linearIndependent_iff.mp hdb
  rcases ggIntCartan_twoLeaf_ker D.isWeyl
      (D.dualTranspose.isCartan : GGIntCartan D.coxeter D.cartan.transpose) D.a_ne_b
      (D.dualTranspose.a_leaf : ∃! c, c ≠ D.a ∧ D.cartan.transpose D.a c ≠ 0) hbT (by decide)
      (hext D.a ra hra) (by simp) (hext D.b rb hrb) (by simp) with h | h
  · exact hia (by simpa [ia.2] using congrFun h ia.1)
  · exact hib (by simpa [ib.2] using congrFun h ib.1)

theorem GGQ2Lin.finrank_eq_card_compl_add_one (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hb : ∃! c, c ≠ D.b ∧ D.cartan D.b c ≠ 0) {ua ub : D.V} (hua : ua ≠ 0) (hub : ub ≠ 0)
    (hfixa : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ua})
    (hfixb : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ub}) (c : D.ι) :
    Module.finrank (ZMod 3) D.V = Fintype.card {k // k ≠ c} + 1 := by
  classical
  have hcard : ∀ c : D.ι, Fintype.card D.ι = 1 + Fintype.card {k // k ≠ c} := fun c => by
    rw [Fintype.card_eq_sum_ones, Fintype.card_eq_sum_ones (α := {k // k ≠ c}),
      Fintype.sum_eq_add_sum_subtype_ne _ c]
  have h1 := GGQ2Lin.card_le_finrank D hb hua hub hfixa hfixb
  have h2 := GGQ2Lin.finrank_le_card_add_one_of_fix D ua hfixa
  have h3 := hcard c
  have h4 := hcard D.a
  omega

@[expose] def GGQ2Lin.E6Branch {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Prop :=
  ∃ e : Fin 6 ≃ D.ι, (∀ i j, D.cartan (e i) (e j) = CartanMatrix.E 6 i j) ∧ e 1 = D.a ∧ e 3 = D.b

theorem GGQ2Lin.card_le_finrank_of_not_e6Branch (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hE : ¬ D.E6Branch) {ua ub : D.V} (hua : ua ≠ 0) (hub : ub ≠ 0)
    (hfixa : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ua})
    (hfixb : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ub}) :
    Fintype.card D.ι ≤ Module.finrank (ZMod 3) D.V := by
  classical
  by_contra hlt
  have hcard : ∀ c : D.ι, Fintype.card D.ι = 1 + Fintype.card {k // k ≠ c} := fun c => by
    rw [Fintype.card_eq_sum_ones, Fintype.card_eq_sum_ones (α := {k // k ≠ c}),
      Fintype.sum_eq_add_sum_subtype_ne _ c]
  have hαa : ∀ j : {k // k ≠ D.a}, D.root j ua = 0 := GGQ2Lin.root_eq_zero_of_fix rfl D ua hfixa
  have hαb : ∀ j : {k // k ≠ D.b}, D.root j ub = 0 := ggQ2g_alpha_fixed rfl D D.b ub hfixb
  have hda := ggQ2pw_root_not_linearIndependent D D.a hua hαa (by have := hcard D.a; omega)
  have hdb := ggQ2pw_root_not_linearIndependent D D.b hub hαb (by have := hcard D.b; omega)
  have hext : ∀ (c : D.ι) (r : {k // k ≠ c} → ZMod 3), ∑ j, r j • D.root j = 0 →
      ∀ i, ∑ j, (D.cartan.transpose i j : ZMod 3) *
        (fun k => if h : k = c then (0 : ZMod 3) else r ⟨k, h⟩) j = 0 := by
    intro c r hr i
    have h1 := congrArg (fun f : Module.Dual (ZMod 3) D.V => f (D.coroot i)) hr
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, D.pairing,
      LinearMap.zero_apply] at h1
    rw [Fintype.sum_eq_add_sum_subtype_ne _ c]
    simp only [Matrix.transpose_apply, dite_true, mul_zero, zero_add]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
    rw [dif_neg j.2, mul_comm]
  obtain ⟨ra, hra, ia, hia⟩ := Fintype.not_linearIndependent_iff.mp hda
  obtain ⟨rb, hrb, ib, hib⟩ := Fintype.not_linearIndependent_iff.mp hdb
  obtain ⟨-, e, he, he1, he3⟩ := ggIntCartan_leaf_ker_branch D.isWeyl
    (D.dualTranspose.isCartan : GGIntCartan D.coxeter D.cartan.transpose) D.a_ne_b
    (D.dualTranspose.a_leaf : ∃! c, c ≠ D.a ∧ D.cartan.transpose D.a c ≠ 0) (by decide)
    (hext D.a ra hra) (by simp) (fun h => hia (by simpa [ia.2] using congrFun h ia.1))
    (hext D.b rb hrb) (by simp) (fun h => hib (by simpa [ib.2] using congrFun h ib.1))
  refine hE ⟨e, fun i j => ?_, he1, he3⟩
  have hsym : CartanMatrix.E 6 j i = CartanMatrix.E 6 i j :=
    congrFun (congrFun (CartanMatrix.E_transpose 6) i) j
  exact (he j i).trans hsym

@[expose] def GGQ2Lin.E6Heart {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Prop :=
  D.E6Branch ∧ Module.finrank (ZMod p) D.V < Fintype.card D.ι

theorem GGQ2Lin.card_le_finrank_of_not_e6Heart (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hH : ¬ D.E6Heart) {ua ub : D.V} (hua : ua ≠ 0) (hub : ub ≠ 0)
    (hfixa : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ua})
    (hfixb : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {ub}) :
    Fintype.card D.ι ≤ Module.finrank (ZMod 3) D.V := by
  by_contra hlt
  exact hH ⟨by_contra fun hE => hlt (D.card_le_finrank_of_not_e6Branch hE hua hub hfixa hfixb),
    by omega⟩

end CFSG.StandardType

end
