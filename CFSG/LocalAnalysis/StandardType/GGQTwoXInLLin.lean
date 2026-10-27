module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLDatum
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggIntCartan_compl_leaf_ker {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) {a : ι}
    (ha : ∃! c, c ≠ a ∧ C a c ≠ 0) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {c d : {k // k ≠ a} → ZMod p}
    (hc : ∀ k : {k // k ≠ a}, ∑ j : {k // k ≠ a}, (C k.1 j.1 : ZMod p) * c j = 0)
    (hd : ∀ k : {k // k ≠ a}, ∑ j : {k // k ≠ a}, (C k.1 j.1 : ZMod p) * d j = 0)
    (hc0 : c ≠ 0) :
    ∃ t : ZMod p, d = t • c := by
  classical
  have hp2 : 2 < p := (Fact.out : p.Prime).two_le.lt_of_ne (Ne.symm hp)
  set A : Matrix {k : ι // k ≠ a} {k : ι // k ≠ a} ℤ :=
    C.transpose.submatrix (Subtype.val : {k : ι // k ≠ a} → ι) Subtype.val with hA
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (hM : GGIsWeylMatrixFixed M) hC
  have hFTA : TauCeti.IsFiniteType A := by
    rw [hA]
    exact hFT.transpose.submatrix Subtype.val_injective
  obtain ⟨b, hb, huniq⟩ := ha
  have hnb : (TauCeti.diagramGraph C).neighborSet a = {b} := by
    ext c
    simp only [SimpleGraph.mem_neighborSet, TauCeti.diagramGraph_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hac, hCab, -⟩
      exact huniq c ⟨hac.symm, hCab⟩
    · rintro rfl
      exact ⟨hb.1.symm, hb.2, fun h0 => hb.2 (hC.eq_zero_symm hb.1.symm h0)⟩
  have hdeg : (TauCeti.diagramGraph C).degree a = 1 := by
    rw [← SimpleGraph.ncard_neighborSet, hnb, Set.ncard_singleton]
  have hconnC := connected_diagramGraph_of_ggIsWeylMatrix (hM : GGIsWeylMatrixFixed M) hC
  have hconn' : ((TauCeti.diagramGraph C).induce ({a}ᶜ : Set ι)).Connected :=
    hconnC.induce_compl_singleton_of_degree_eq_one hdeg
  have hgraph : TauCeti.diagramGraph A =
      (TauCeti.diagramGraph C).induce ({a}ᶜ : Set ι) := by
    rw [hA, TauCeti.diagramGraph_submatrix Subtype.val_injective,
      diagramGraph_transpose]
    ext u v
    exact Iff.rfl
  have hconnA : (TauCeti.diagramGraph A).Connected := by
    rw [hgraph]
    exact hconn'
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := hFTA.existsUnique_dynkinType hconnA
  obtain ⟨i₀, hi₀⟩ := LayerCycRoot.exists_kerDetect hp2 ht
  let k₀ : {k : ι // k ≠ a} := e.symm i₀
  have hkdet : LayerCycRoot.KerDetect A p k₀ :=
    LayerCycRoot.kerDetect_of_equiv e he hi₀
  have hT : ∀ v : {k : ι // k ≠ a} → ZMod p,
      (∀ k : {k // k ≠ a}, ∑ j : {k // k ≠ a}, (C k.1 j.1 : ZMod p) * v j = 0) →
      ∀ j : {k : ι // k ≠ a}, ∑ i : {k : ι // k ≠ a}, v i * (A i j : ZMod p) = 0 := by
    intro v hv j
    rw [← hv j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA]
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
    exact mul_comm _ _
  have hcA := hT c hc
  have hdA := hT d hd
  have hck₀ : c k₀ ≠ 0 := fun h0 => hc0 (funext fun i => hkdet c hcA h0 i)
  refine ⟨d k₀ / c k₀, ?_⟩
  have key : ∀ w : {k : ι // k ≠ a} → ZMod p, ∑ i, c i * w i = 0 → ∑ i, d i * w i = 0 →
      ∑ i, (d - (d k₀ / c k₀) • c) i * w i = 0 := by
    intro w h1 h2
    calc ∑ i, (d - (d k₀ / c k₀) • c) i * w i
        = ∑ i, (d i * w i - d k₀ / c k₀ * (c i * w i)) :=
          Finset.sum_congr rfl fun i _ => by
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            ring
      _ = ∑ i, d i * w i - ∑ i, d k₀ / c k₀ * (c i * w i) :=
          Finset.sum_sub_distrib (fun i => d i * w i) (fun i => d k₀ / c k₀ * (c i * w i))
      _ = ∑ i, d i * w i - d k₀ / c k₀ * ∑ i, c i * w i := by rw [Finset.mul_sum]
      _ = 0 := by rw [h1, h2]; ring
  have hker : ∀ j : {k : ι // k ≠ a},
      ∑ i : {k : ι // k ≠ a}, (d - (d k₀ / c k₀) • c) i * (A i j : ZMod p) = 0 :=
    fun j => key (fun i => (A i j : ZMod p)) (hcA j) (hdA j)
  have hk₀0 : (d - (d k₀ / c k₀) • c) k₀ = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ (d k₀) hck₀, sub_self]
  funext i
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero] using
    hkdet (d - (d k₀ / c k₀) • c) hker hk₀0 i

namespace GGQTwoModel

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
  {D L J K : Subgroup G}

theorem finrank_le_card_add_one (M : GGQTwoModel p Bs x y D L J K) :
    Module.finrank (ZMod p) M.V ≤ Fintype.card {k // k ≠ M.a} + 1 := by
  classical
  let φ : M.V →ₗ[ZMod p] ({k // k ≠ M.a} → ZMod p) := LinearMap.pi fun k => M.root k
  have hrn : Module.rank (ZMod p) (LinearMap.range φ) +
      Module.rank (ZMod p) (LinearMap.ker φ) = Module.rank (ZMod p) M.V :=
    @LinearMap.rank_range_add_rank_ker (ZMod p) M.V ({k // k ≠ M.a} → ZMod p)
      _ _ _ _ (inferInstance : Module (ZMod p) ({k // k ≠ M.a} → ZMod p)) _ φ
  have hker : LinearMap.ker φ ≤ Submodule.span (ZMod p) {M.xV} := by
    intro v hv
    have hfix : ∀ g ∈ ggAutomizer L Bs, ggLin (p := p) M.model g v = v := by
      have hgen : ∀ k : {k // k ≠ M.a}, ggLin (p := p) M.model (M.simple k) v = v := by
        intro k
        have h0 : M.root k v = 0 := by
          simpa [φ] using congrFun hv k
        rw [M.simple_apply, h0, zero_smul, sub_zero]
      intro g hg
      rw [M.automizer_L] at hg
      refine Subgroup.closure_induction
        (p := fun g _ => ggLin (p := p) M.model g v = v) ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨k, hk, rfl⟩
        exact hgen ⟨k, hk⟩
      · simp
      · intro a b _ _ ha hb
        rw [map_mul, LinearEquiv.mul_apply, hb, ha]
      · intro a _ ha
        rw [map_inv]
        calc (ggLin (p := p) M.model a).symm v
            = (ggLin (p := p) M.model a).symm (ggLin (p := p) M.model a v) := by rw [ha]
          _ = v := (ggLin (p := p) M.model a).symm_apply_apply v
    have hm : v ∈ ggFixedSubmodule (p := p) M.model (ggAutomizer L Bs) :=
      mem_ggFixedSubmodule_iff.mpr hfix
    rw [M.fixed_x] at hm
    exact hm
  have hrange : Module.rank (ZMod p) (LinearMap.range φ) ≤
      (Fintype.card {k // k ≠ M.a} : Cardinal) := by
    calc Module.rank (ZMod p) (LinearMap.range φ)
        ≤ Module.rank (ZMod p) ({k // k ≠ M.a} → ZMod p) := Submodule.rank_le _
      _ = (Fintype.card {k // k ≠ M.a} : Cardinal) :=
          rank_eq_card_basis (Pi.basisFun (ZMod p) {k // k ≠ M.a})
  haveI : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) {M.xV}) :=
    FiniteDimensional.span_singleton (ZMod p) M.xV
  have hspanfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) {M.xV}) ≤ 1 := by
    by_cases h0 : M.xV = 0
    · rw [h0, Submodule.span_zero_singleton, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton h0]
  have hkerrank : Module.rank (ZMod p) (LinearMap.ker φ) ≤ 1 := by
    calc Module.rank (ZMod p) (LinearMap.ker φ)
        ≤ Module.rank (ZMod p) (Submodule.span (ZMod p) {M.xV}) := Submodule.rank_mono hker
      _ = (Module.finrank (ZMod p) (Submodule.span (ZMod p) {M.xV}) : Cardinal) :=
          (Module.finrank_eq_rank (R := ZMod p) (M := Submodule.span (ZMod p) {M.xV})).symm
      _ ≤ (1 : Cardinal) := by exact_mod_cast hspanfin
      _ = 1 := by norm_num
  have hrank : Module.rank (ZMod p) M.V ≤ ((Fintype.card {k // k ≠ M.a} + 1 : ℕ) : Cardinal) := by
    calc Module.rank (ZMod p) M.V
        = Module.rank (ZMod p) (LinearMap.range φ) +
            Module.rank (ZMod p) (LinearMap.ker φ) :=
          hrn.symm
      _ ≤ (Fintype.card {k // k ≠ M.a} : Cardinal) + 1 := add_le_add hrange hkerrank
      _ = ((Fintype.card {k // k ≠ M.a} + 1 : ℕ) : Cardinal) := by rw [Nat.cast_add, Nat.cast_one]
  exact Module.finrank_le_of_rank_le hrank

theorem root_xV_eq_zero (M : GGQTwoModel p Bs x y D L J K) (hp : p ≠ 2)
    (k : {k // k ≠ M.a}) : M.root k M.xV = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp
  have hgen : M.simple k ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨k.1, k.2, rfl⟩
  have hfix : ggLin (p := p) M.model (M.simple k) M.xV = M.xV := by
    have hmem : M.xV ∈ ggFixedSubmodule (p := p) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.mem_span_singleton_self M.xV
    exact (mem_ggFixedSubmodule_iff.mp hmem) (M.simple k) hgen
  rw [M.simple_apply] at hfix
  have hsmul : M.root k M.xV • M.coroot k = 0 := sub_eq_self.mp hfix
  rcases smul_eq_zero.mp hsmul with h | h
  · exact h
  · exfalso
    have hpair : M.root k (M.coroot k) = 2 := by
      rw [M.pairing, M.isCartan.1]
      norm_num
    have hzero : M.root k (M.coroot k) = 0 := by rw [h, map_zero]
    exact h2 (hpair.symm.trans hzero)

open scoped commutatorElement

private lemma model_commutator_eq {M : GGQTwoModel p Bs x y D L J K} {b n : G}
    (hb : b ∈ Bs) (hnN : n ∈ Subgroup.normalizer (Bs : Set G))
    (hc : Bracket.bracket b n ∈ Bs) :
    M.model (Additive.ofMul ⟨Bracket.bracket b n, hc⟩) =
      M.model (Additive.ofMul ⟨b, hb⟩) -
        ggLin (p := p) M.model (ggConjAut Bs hnN) (M.model (Additive.ofMul ⟨b, hb⟩)) := by
  have hbs : n * b⁻¹ * n⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hnN b⁻¹).mp (Bs.inv_mem hb)
  have hsplit : Bracket.bracket b n = b * (n * b⁻¹ * n⁻¹) := by
    rw [commutatorElement_def]
    group
  have hsub : Additive.ofMul (⟨Bracket.bracket b n, hc⟩ : ↥Bs) =
      Additive.ofMul ((⟨b, hb⟩ : ↥Bs) * ⟨n * b⁻¹ * n⁻¹, hbs⟩) := by
    rw [show (⟨Bracket.bracket b n, hc⟩ : ↥Bs) = (⟨b, hb⟩ : ↥Bs) * ⟨n * b⁻¹ * n⁻¹, hbs⟩ by
      apply Subtype.ext
      exact hsplit]
  have hgn : M.model (Additive.ofMul ⟨n * b⁻¹ * n⁻¹, hbs⟩) =
      - ggLin (p := p) M.model (ggConjAut Bs hnN) (M.model (Additive.ofMul ⟨b, hb⟩)) := by
    have hof : Additive.ofMul (⟨b⁻¹, Bs.inv_mem hb⟩ : ↥Bs) =
        - Additive.ofMul (⟨b, hb⟩ : ↥Bs) := by
      rw [show (⟨b⁻¹, Bs.inv_mem hb⟩ : ↥Bs) = (⟨b, hb⟩ : ↥Bs)⁻¹ from rfl]
      exact ofMul_inv _
    have hcn : ggConjAut Bs hnN ⟨b⁻¹, Bs.inv_mem hb⟩ = ⟨n * b⁻¹ * n⁻¹, hbs⟩ := by
      apply Subtype.ext
      rw [ggConjAut_apply]
    calc M.model (Additive.ofMul ⟨n * b⁻¹ * n⁻¹, hbs⟩)
        = M.model (Additive.ofMul ((ggConjAut Bs hnN) ⟨b⁻¹, Bs.inv_mem hb⟩)) := by rw [hcn]
      _ = ggLin (p := p) M.model (ggConjAut Bs hnN)
            (M.model (Additive.ofMul ⟨b⁻¹, Bs.inv_mem hb⟩)) :=
          (ggLin_apply_ofMul (p := p) M.model (ggConjAut Bs hnN) ⟨b⁻¹, Bs.inv_mem hb⟩).symm
      _ = ggLin (p := p) M.model (ggConjAut Bs hnN)
            (-M.model (Additive.ofMul ⟨b, hb⟩)) := by rw [hof, map_neg]
      _ = - ggLin (p := p) M.model (ggConjAut Bs hnN)
            (M.model (Additive.ofMul ⟨b, hb⟩)) :=
          (ggLin (p := p) M.model (ggConjAut Bs hnN)).map_neg _
  rw [hsub, ofMul_mul, map_add, hgn]
  abel

private lemma sub_ggLin_mem_span_coroot (M : GGQTwoModel p Bs x y D L J K) {g : MulAut ↥Bs}
    (hg : g ∈ ggAutomizer L Bs) (w : M.V) :
    w - ggLin (p := p) M.model g w ∈
      Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
  rw [M.automizer_L] at hg
  induction hg using Subgroup.closure_induction generalizing w with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := hg
    rw [M.simple_apply, sub_sub_cancel]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (⟨k, hk⟩ : {k // k ≠ M.a})))
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul, LinearEquiv.mul_apply, ← sub_add_sub_cancel w (ggLin (p := p) M.model b w)]
    exact Submodule.add_mem _ (hb w) (ha _)
  | inv a _ ha =>
    have h := Submodule.neg_mem _ (ha ((ggLin (p := p) M.model a).symm w))
    rw [LinearEquiv.apply_symm_apply, neg_sub] at h
    rw [map_inv]
    exact h

private lemma model_mem_span_coroot_of_mem_commutator (M : GGQTwoModel p Bs x y D L J K)
    {g : G} (hg : g ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆) (hgB : g ∈ Bs) :
    M.model (Additive.ofMul ⟨g, hgB⟩) ∈
      Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) := by
  have hle : ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ ≤ Bs :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp inf_le_right
  rw [Subgroup.commutator_def] at hg hle
  refine Subgroup.closure_induction (p := fun g _ => ∀ hgB : g ∈ Bs,
      M.model (Additive.ofMul ⟨g, hgB⟩) ∈
        Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i))
    ?_ ?_ ?_ ?_ hg hgB
  · rintro _ ⟨b, hb, n, hn, rfl⟩ hc
    rw [model_commutator_eq (M := M) hb (Subgroup.mem_inf.mp hn).2 hc]
    exact sub_ggLin_mem_span_coroot M
      (ggConjAut_mem_ggAutomizer (Subgroup.mem_inf.mp hn).1 (Subgroup.mem_inf.mp hn).2) _
  · intro h1
    change M.model (Additive.ofMul (1 : ↥Bs)) ∈ _
    rw [ofMul_one, map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb iha ihb hab
    change M.model (Additive.ofMul ((⟨a, hle ha⟩ : ↥Bs) * ⟨b, hle hb⟩)) ∈ _
    rw [ofMul_mul, map_add]
    exact Submodule.add_mem _ (iha (hle ha)) (ihb (hle hb))
  · intro a ha iha hai
    change M.model (Additive.ofMul ((⟨a, hle ha⟩ : ↥Bs)⁻¹)) ∈ _
    rw [ofMul_inv, map_neg]
    exact Submodule.neg_mem _ (iha (hle ha))

private lemma exists_mem_commutator_model_eq_two_smul (M : GGQTwoModel p Bs x y D L J K)
    (k : {k // k ≠ M.a}) :
    ∃ g ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆, ∃ hg : g ∈ Bs,
      M.model (Additive.ofMul ⟨g, hg⟩) = (2 : ZMod p) • M.coroot k := by
  let b0 : Additive ↥Bs := M.model.symm (M.coroot k)
  let b : ↥Bs := Additive.toMul b0
  have hb : M.model (Additive.ofMul b) = M.coroot k := by
    show M.model (Additive.ofMul (Additive.toMul b0)) = M.coroot k
    rw [ofMul_toMul]
    exact M.model.apply_symm_apply (M.coroot k)
  have hrk : M.simple k ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨k.1, k.2, rfl⟩
  obtain ⟨n, hnL, hnN, hn⟩ := mem_ggAutomizer_iff.mp hrk
  have hcC : Bracket.bracket (b : G) n ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ :=
    Subgroup.commutator_mem_commutator b.2 (Subgroup.mem_inf.mpr ⟨hnL, hnN⟩)
  have hcB : Bracket.bracket (b : G) n ∈ Bs :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp inf_le_right hcC
  have hcn : ggConjAut Bs hnN = M.simple k := by
    ext z
    rw [ggConjAut_apply, hn z]
  have hval := model_commutator_eq (M := M) (b := (b : G)) b.2 hnN hcB
  rw [hcn, hb, M.simple_apply, M.pairing, M.isCartan.1] at hval
  norm_num at hval
  exact ⟨_, hcC, hcB, by rw [hval]⟩

private lemma exists_mem_commutator_of_mem_span (M : GGQTwoModel p Bs x y D L J K) (hp : p ≠ 2)
    {w : M.V}
    (hw : w ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) :
    ∃ g ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆, ∃ hg : g ∈ Bs,
      w = M.model (Additive.ofMul ⟨g, hg⟩) := by
  let W : Submodule (ZMod p) M.V := AddSubgroup.toZModSubmodule p
    (AddSubgroup.map M.model.toAddMonoidHom (Subgroup.toAddSubgroup
      ((⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆).subgroupOf Bs)))
  have mem_W : ∀ w : M.V, w ∈ W ↔ ∃ g ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆,
      ∃ hg : g ∈ Bs, w = M.model (Additive.ofMul ⟨g, hg⟩) := by
    intro w
    change w ∈ AddSubgroup.toZModSubmodule p (AddSubgroup.map M.model.toAddMonoidHom
      (Subgroup.toAddSubgroup ((⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆).subgroupOf Bs))) ↔ _
    rw [AddSubgroup.mem_toZModSubmodule, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : Additive.toMul a ∈ (⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆).subgroupOf Bs := by
        simpa [Additive.mem_toAddSubgroup] using ha
      exact ⟨_, Subgroup.mem_subgroupOf.mp ha', (Additive.toMul a).2,
        congrArg M.model (ofMul_toMul a).symm⟩
    · rintro ⟨g, hg, hgB, rfl⟩
      refine ⟨Additive.ofMul ⟨g, hgB⟩, ?_, rfl⟩
      rw [Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf]
      exact hg
  have hk : ∀ k : {k // k ≠ M.a}, M.coroot k ∈ W := by
    intro k
    obtain ⟨g, hgC, hgB, hg⟩ := exists_mem_commutator_model_eq_two_smul M k
    have heq : M.coroot k = (2 : ZMod p)⁻¹ • M.model (Additive.ofMul ⟨g, hgB⟩) := by
      rw [hg, smul_smul, inv_mul_cancel₀ (zmod_two_ne_zero hp), one_smul]
    rw [heq]
    exact W.smul_mem _ ((mem_W _).mpr ⟨g, hgC, hgB, rfl⟩)
  refine (mem_W w).mp (Submodule.span_le.mpr ?_ hw)
  rintro _ ⟨k, rfl⟩
  exact hk k

theorem xV_mem_span_iff_mem_commutator (M : GGQTwoModel p Bs x y D L J K) (hp : p ≠ 2) :
    M.xV ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i) ↔
      x ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ := by
  refine ⟨fun h => ?_, fun h => model_mem_span_coroot_of_mem_commutator M h M.hx⟩
  obtain ⟨g, hg, hgB, hgx⟩ := exists_mem_commutator_of_mem_span M hp h
  obtain rfl : x = g := congrArg Subtype.val (Additive.ofMul.injective (M.model.injective hgx))
  exact hg

theorem linearIndependent_coroot_of_xV_mem_span (M : GGQTwoModel p Bs x y D L J K)
    (hp : p ≠ 2) (hx1 : x ≠ 1)
    (h : M.xV ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) :
    LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i) := by
  classical
  have hx0 : M.xV ≠ 0 := by
    intro h0
    have h0' : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 := by
      apply M.model.injective
      rw [map_zero]
      exact h0
    have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h0')
    exact hx1 (Subtype.ext_iff.mp h1)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p)).mp h
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hx0
    rw [← hc, hc0]
    simp
  have hker : ∀ k : {k // k ≠ M.a},
      ∑ j : {k // k ≠ M.a}, (M.cartan k.1 j.1 : ZMod p) * c j = 0 := by
    intro k
    have hk := root_xV_eq_zero M hp k
    rw [← hc, map_sum] at hk
    simpa only [map_smul, smul_eq_mul, M.pairing, mul_comm] using hk
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hgker : ∀ k : {k // k ≠ M.a},
      ∑ j : {k // k ≠ M.a}, (M.cartan k.1 j.1 : ZMod p) * g j = 0 := by
    intro k
    have hk := congrArg (M.root k) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero, M.pairing] at hk
    simpa only [mul_comm] using hk
  obtain ⟨t, ht⟩ :=
    ggIntCartan_compl_leaf_ker M.isWeyl M.isCartan M.a_leaf hp hker hgker hc0
  have ht0 : t = 0 := by
    have htx : t • M.xV = 0 := by
      rw [← hc]
      calc t • ∑ j : {k // k ≠ M.a}, c j • M.coroot j
          = ∑ j : {k // k ≠ M.a}, (t * c j) • M.coroot j := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
        _ = ∑ j : {k // k ≠ M.a}, g j • M.coroot j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [ht]
              rfl
        _ = 0 := hg
    rcases smul_eq_zero.mp htx with h | h
    · exact h
    · exact absurd h hx0
  intro j
  rw [ht, ht0]
  simp

end GGQTwoModel

theorem ggQTwoXInLDatum_of_span (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G), GGQTwoSetting p B Bs x L D J → x ∈ L → ∀ [Fact p.Prime] (y : G) (K
    : Subgroup G), GGNbr p B x D J y K → ∀ M : GGQTwoModel p Bs x y D L J K, M.xV ∈ Submodule.span
    (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) : GGQTwoXInLDatum := by
  intro G _ _ p B Bs x L D J hS hxL hpFact y K hnb M
  haveI : Fact p.Prime := hpFact
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  have hx1 : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hspan := h G p B Bs x L D J hS hxL y K hnb M
  exact ⟨GGQTwoModel.linearIndependent_coroot_of_xV_mem_span M hp2 hx1 hspan, hspan,
    GGQTwoModel.finrank_le_card_add_one M⟩

end CFSG.StandardType

end
