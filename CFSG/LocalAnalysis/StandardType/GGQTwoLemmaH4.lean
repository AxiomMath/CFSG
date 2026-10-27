module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2MovesLine {G : Type} [Group G] (Bs : Subgroup G) (x : G) (φ : MulAut ↥Bs) :
    Prop :=
  ∃ b : ↥Bs, (b : G) ∈ Subgroup.zpowers x ∧ ((φ b : ↥Bs) : G) ∉ Subgroup.zpowers x

private theorem ggQ2h4_mem_zpowers_subtype {G : Type*} [Group G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) {b : ↥Bs} (hb : (b : G) ∈ Subgroup.zpowers x) :
    b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩

private theorem ggQ2h4_zpow_mem_span {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {Bs : Subgroup G} {x : G} (hx : x ∈ Bs) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {b : ↥Bs} (hb : b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    ι (Additive.ofMul b) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} : Set V) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hk, ofMul_zpow, map_zsmul]
  exact Submodule.mem_span_singleton.mpr ⟨(k : ZMod p), Int.cast_smul_eq_zsmul (R := ZMod p) k _⟩

private theorem ggQ2h4_mem_span_of_reflection_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {x w : V}
    {f : Module.Dual (ZMod p) V} (hfx : f x = 2) (h : reflection hfx w = -w) :
    w ∈ Submodule.span (ZMod p) ({x} : Set V) := by
  have h2 := zmod_two_ne_zero hp2
  have hw : w = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • w) := by
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  have h2w : (2 : ZMod p) • w = f w • x := by
    rw [Module.reflection_apply w hfx] at h
    rw [two_smul]
    calc w + w = (w - f w • x) + f w • x + w := by abel
      _ = -w + f w • x + w := by rw [h]
      _ = f w • x := by abel
  rw [hw, h2w]
  exact Submodule.smul_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x)))

private theorem ggQ2h4_isReflection_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {φ ψ : MulAut ↥Bs} (h : GGIsReflection p φ) : GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

private theorem ggQ2h4_involution_eq_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {u : V} (hu : u ≠ 0)
    {T : V ≃ₗ[ZMod p] V} (hT : T * T = 1)
    (hspan : T u ∈ Submodule.span (ZMod p) ({u} : Set V)) (hne : T u ≠ u) : T u = -u := by
  have h2 := zmod_two_ne_zero hp2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hTu : T (T u) = u := by
    have h := congrArg (fun S : V ≃ₗ[ZMod p] V => S u) hT
    simpa using h
  have hc2 : c * c = 1 := by
    have hcc : (c * c) • u = u := by
      rw [← smul_smul, hc, ← map_smul, hc, hTu]
    have h' : (c * c - 1) • u = 0 := by rw [sub_smul, hcc, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hu)
  have hc1 : c ≠ 1 := fun h => hne (by rw [← hc, h, one_smul])
  have hcases : c = 1 ∨ c = -1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
  rcases hcases with h | h
  · exact absurd h hc1
  · rw [← hc, h]
    exact neg_one_smul (R := ZMod p) (x := u)

private theorem ggQ2h4_unique_refl_moving {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type}
    [Group G] {Bs : Subgroup G} (hNT : GGNoTransvection p Bs) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (ι : Additive ↥Bs ≃+ V) {u : V} (hu : u ≠ 0)
    {φ ψ : MulAut ↥Bs} (hφA : φ ∈ ggInduced ⊤ Bs) (hψA : ψ ∈ ggInduced ⊤ Bs)
    (hφr : GGIsReflection p φ) (hψr : GGIsReflection p ψ)
    (hφu : ggLin (p := p) ι φ u = -u) (hψu : ggLin (p := p) ι ψ u = -u) : φ = ψ := by
  by_contra hne
  obtain ⟨x, f, hfx, hφf⟩ := exists_of_ggIsReflection ι hφr
  obtain ⟨y, g, hgy, hψf⟩ := exists_of_ggIsReflection ι hψr
  have hφR : ggLin (p := p) ι φ = reflection hfx := ggLin_eq_reflection ι hfx hφf
  have hψR : ggLin (p := p) ι ψ = reflection hgy := ggLin_eq_reflection ι hgy hψf
  have hxu : u ∈ Submodule.span (ZMod p) ({x} : Set V) :=
    ggQ2h4_mem_span_of_reflection_neg hp2 hfx (by rw [← hφR, hφu])
  have hyu : u ∈ Submodule.span (ZMod p) ({y} : Set V) :=
    ggQ2h4_mem_span_of_reflection_neg hp2 hgy (by rw [← hψR, hψu])
  have hxy : LinearIndependent (ZMod p) ![x, y] :=
    (ggReflection_linearIndependent_of_noTransvection hp2 hNT ι hφA hψA hne hfx hgy hφR hψR).1
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxu
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hyu
  have hb0 : b ≠ 0 := fun h => hu (by rw [← hb, h, zero_smul])
  have hx0 : x ≠ 0 := (ne_zero_of_apply_eq_two hp2 hfx).1
  have hy_eq : y = (b⁻¹ * a) • x := by
    calc y = b⁻¹ • (b • y) := by rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
      _ = b⁻¹ • u := by rw [hb]
      _ = b⁻¹ • (a • x) := by rw [ha]
      _ = (b⁻¹ * a) • x := by rw [smul_smul]
  exact (LinearIndependent.pair_iff' hx0).mp hxy (b⁻¹ * a) hy_eq.symm

private theorem ggQ2h4_comm_reflection_apply_eq {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {x y : V} {f g : Module.Dual (ZMod p) V}
    (hfx : f x = 2) (hgy : g y = 2)
    (hcomm : reflection hfx * reflection hgy = reflection hgy * reflection hfx) (v : V) :
    (f y * g v) • x = (g x * f v) • y := by
  have h := congrArg (fun T : V ≃ₗ[ZMod p] V => T v) hcomm
  rw [reflection_mul_reflection_apply' hfx hgy, reflection_mul_reflection_apply' hgy hfx] at h
  have key : (f y * g v) • x - (g x * f v) • y = 0 := by
    have h' : (v - g v • y - (f v - f y * g v) • x) -
        (v - f v • x - (g v - g x * f v) • y) = 0 := sub_eq_zero.mpr h
    convert h' using 1
    module
  exact sub_eq_zero.mp key

private theorem ggQ2h4_dichotomy {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {x y : V} {f g : Module.Dual (ZMod p) V}
    (hfx : f x = 2) (hgy : g y = 2)
    (hcomm : reflection hfx * reflection hgy = reflection hgy * reflection hfx) :
    (f y = 0 → g x = 0) ∧
      (f y ≠ 0 → x ∈ Submodule.span (ZMod p) ({y} : Set V)) := by
  have h2 := zmod_two_ne_zero hp2
  have hy : y ≠ 0 := (ne_zero_of_apply_eq_two hp2 hgy).1
  refine ⟨fun hfy => ?_, fun hfy => ?_⟩
  · have h := ggQ2h4_comm_reflection_apply_eq hfx hgy hcomm x
    rw [hfy, zero_mul, zero_smul] at h
    have hgx2 : g x * 2 = 0 := by
      have hgxf : g x * f x = 0 := (smul_eq_zero.mp h.symm).resolve_right hy
      rwa [hfx] at hgxf
    exact (mul_eq_zero.mp hgx2).resolve_right h2
  · have h := ggQ2h4_comm_reflection_apply_eq hfx hgy hcomm y
    rw [hgy] at h
    have hx_eq : x = ((f y * 2)⁻¹ * (g x * f y)) • y := by
      rw [← smul_smul, ← h, smul_smul, inv_mul_cancel₀ (mul_ne_zero hfy h2), one_smul]
    exact Submodule.mem_span_singleton.mpr ⟨_, hx_eq.symm⟩

private theorem ggQ2h4_conj_neg {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {u : V} (hu : u ≠ 0) {T U : V ≃ₗ[ZMod p] V}
    (hT : T u = -u) (hU2 : U * U = 1)
    (hUu : U u ∈ Submodule.span (ZMod p) ({u} : Set V)) :
    (U * T * U⁻¹) u = -u := by
  have hUinv : U⁻¹ = U := (eq_inv_of_mul_eq_one_right hU2).symm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hUu
  have hc2 : c * c = 1 := by
    have hUU : U (U u) = u := by
      have h := congrArg (fun S : V ≃ₗ[ZMod p] V => S u) hU2
      simpa using h
    have hcc : (c * c) • u = u := by
      rw [← smul_smul, hc, ← map_smul, hc, hUU]
    have h' : (c * c - 1) • u = 0 := by rw [sub_smul, hcc, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hu)
  have key : U (T (U u)) = -u := by
    rw [← hc, map_smul, hT, smul_neg, map_neg, map_smul, ← hc, smul_smul, hc2, one_smul]
  rw [hUinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact key

private theorem ggQ2h4_exists_not_adj {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) (h3 : 3 ≤ Fintype.card Λ) :
    ∃ j k : Λ, j ≠ k ∧ C j k = 0 := by
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (hM : GGIsWeylMatrixFixed M) hC
  obtain ⟨v⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := Λ) (by simpa using h3)
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, C (v k) (v (k + 1)) = 0 :=
    hFT.exists_apply_succ_eq_zero (m := 3) (by norm_num) v.injective
  refine ⟨v k, v (k + 1), fun h => ?_, hk⟩
  have hkne : k ≠ (k + 1 : Fin 3) := by fin_cases k <;> decide
  exact hkne (v.injective h)

private theorem ggQ2h4_mem_ggInduced_top {G : Type} [Group G] {H Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : φ ∈ ggAutomizer H Bs) : φ ∈ ggInduced ⊤ Bs := by
  obtain ⟨g, -, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp h
  exact ⟨g, Subgroup.mem_top g, hgN, hgφ⟩

theorem ggQ2_lemmaH4 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p = 3)
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hnb : GGNbr p B x D J y K) (M : GGQ2NbrDatum p Bs K) (h3 : 3 ≤ Fintype.card M.Λ) :
    ∃ φ ∈ ggAutomizer K Bs, GGIsReflection p φ ∧ GGQ2MovesLine Bs x φ := by
  have hT1 : GGNoTransvection p Bs := hS.1.2.2.2.1
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hp2 : p ≠ 2 := by rw [hp]; norm_num
  have hx : x ∈ Bs := ggQ2_x_mem_Bs hS
  set xV : M.V := M.model (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) with hxV
  have hbar : x ∉ ggBarCentralizer p Bs K := fun h => hnb.2.2.2 h.2.2
  have hA : xV ∉ ggFixedSubmodule (p := p) M.model (ggAutomizer K Bs) := by
    intro h
    exact hbar ((M.fixed_ZK (⟨x, hx⟩ : ↥Bs)).mp (by rwa [hxV] at h))
  have hxV_ne : xV ≠ 0 := by
    intro h
    exact hA (by rw [h]; exact Submodule.zero_mem _)
  have hpair : ∀ i, M.root i (M.coroot i) = 2 := by
    intro i
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  have hsi_refl : ∀ i, GGIsReflection p (M.simple i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 M.model (hpair i)
      (ggLin_eq_reflection M.model (hpair i) (M.simple_apply i))
  have hsi_mem : ∀ i, M.simple i ∈ ggAutomizer K Bs := fun i =>
    M.automizer_K ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hsi_lin : ∀ i, ggLin (p := p) M.model (M.simple i) = reflection (hpair i) := fun i =>
    ggLin_eq_reflection M.model (hpair i) (M.simple_apply i)
  have hB : ∃ i, ggLin (p := p) M.model (M.simple i) xV ≠ xV := by
    by_contra h
    push Not at h
    have : xV ∈ ggFixedSubmodule (p := p) M.model (ggAutomizer K Bs) := by
      rw [M.automizer_K, mem_ggFixedSubmodule_iff]
      intro φ hφ
      refine Subgroup.closure_induction
        (p := fun (φ : MulAut ↥Bs) (_ : φ ∈ Subgroup.closure (Set.range M.simple)) =>
          ggLin (p := p) M.model φ xV = xV) ?_ ?_ ?_ ?_ hφ
      · rintro φ ⟨i, rfl⟩
        exact h i
      · rw [map_one]; rfl
      · intro a b ha hb ha' hb'
        rw [map_mul, LinearEquiv.mul_apply, hb', ha']
      · intro a ha ha'
        rw [map_inv]
        change (ggLin (p := p) M.model a).symm xV = xV
        exact (LinearEquiv.symm_apply_eq (e := ggLin (p := p) M.model a)).mpr ha'.symm
    exact hA this
  obtain ⟨i₀, hi₀⟩ := hB
  have hmain : ∃ φ ∈ ggAutomizer K Bs, GGIsReflection p φ ∧
      ggLin (p := p) M.model φ xV ∉ Submodule.span (ZMod p) ({xV} : Set M.V) := by
    by_contra hno
    push Not at hno
    have hinv : ∀ φ ∈ ggAutomizer K Bs, GGIsReflection p φ →
        ggLin (p := p) M.model φ xV ≠ xV → ggLin (p := p) M.model φ xV = -xV := by
      intro φ hφ hrefl hne
      refine ggQ2h4_involution_eq_neg hp2 hxV_ne ?_ (hno φ hφ hrefl) hne
      rw [← map_mul, show φ * φ = φ ^ 2 from (pow_two φ).symm, hrefl.1, map_one]
    have hi₀neg : ggLin (p := p) M.model (M.simple i₀) xV = -xV :=
      hinv _ (hsi_mem i₀) (hsi_refl i₀) hi₀
    have huniq : ∀ φ ∈ ggAutomizer K Bs, GGIsReflection p φ →
        ggLin (p := p) M.model φ xV = -xV → φ = M.simple i₀ := by
      intro φ hφ hrefl hneg
      exact ggQ2h4_unique_refl_moving hp2 hT1 M.model hxV_ne
        (ggQ2h4_mem_ggInduced_top hφ) (ggQ2h4_mem_ggInduced_top (hsi_mem i₀))
        hrefl (hsi_refl i₀) hneg hi₀neg
    have hcomm_gen : ∀ j, M.simple j * M.simple i₀ = M.simple i₀ * M.simple j := by
      intro j
      have hψmem : M.simple j * M.simple i₀ * (M.simple j)⁻¹ ∈ ggAutomizer K Bs :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsi_mem j) (hsi_mem i₀))
          (Subgroup.inv_mem _ (hsi_mem j))
      have hψrefl : GGIsReflection p (M.simple j * M.simple i₀ * (M.simple j)⁻¹) :=
        ggQ2h4_isReflection_conj (hsi_refl i₀)
      have hψneg : ggLin (p := p) M.model (M.simple j * M.simple i₀ * (M.simple j)⁻¹) xV =
          -xV := by
        rw [map_mul, map_mul, map_inv]
        refine ggQ2h4_conj_neg hxV_ne hi₀neg ?_ (hno (M.simple j) (hsi_mem j) (hsi_refl j))
        rw [← map_mul, show M.simple j * M.simple j = (M.simple j) ^ 2 from (pow_two _).symm,
          (hsi_refl j).1, map_one]
      have hψ := huniq _ hψmem hψrefl hψneg
      calc M.simple j * M.simple i₀
          = (M.simple j * M.simple i₀ * (M.simple j)⁻¹) * M.simple j := by group
        _ = M.simple i₀ * M.simple j := by rw [hψ]
    obtain ⟨z₀, fτ, hfτ, hτform⟩ := exists_of_ggIsReflection M.model (hsi_refl i₀)
    have hτR : ggLin (p := p) M.model (M.simple i₀) = reflection hfτ :=
      ggLin_eq_reflection M.model hfτ hτform
    have hdich : ∀ j, (fτ (M.coroot j) = 0 → M.root j z₀ = 0) ∧
        (fτ (M.coroot j) ≠ 0 → z₀ ∈ Submodule.span (ZMod p) ({M.coroot j} : Set M.V)) := by
      intro j
      have hcommL : reflection hfτ * reflection (hpair j) =
          reflection (hpair j) * reflection hfτ := by
        rw [← hτR, ← hsi_lin j, ← map_mul, ← map_mul, hcomm_gen j]
      exact ggQ2h4_dichotomy hp2 hfτ (hpair j) hcommL
    have hz₀_span : xV ∈ Submodule.span (ZMod p) ({z₀} : Set M.V) :=
      ggQ2h4_mem_span_of_reflection_neg hp2 hfτ (by rw [← hτR, hi₀neg])
    have hz₀_ne : z₀ ≠ 0 := (ne_zero_of_apply_eq_two hp2 hfτ).1
    have hseed : z₀ ∈ Submodule.span (ZMod p) ({M.coroot i₀} : Set M.V) := by
      by_contra hnot
      have hfy0 : fτ (M.coroot i₀) = 0 := by
        by_contra hfy
        exact hnot ((hdich i₀).2 hfy)
      have hαz : M.root i₀ z₀ = 0 := (hdich i₀).1 hfy0
      have hαx : M.root i₀ xV = 0 := by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz₀_span
        rw [← hc, map_smul, hαz, smul_zero]
      have : ggLin (p := p) M.model (M.simple i₀) xV = xV := by
        rw [M.simple_apply i₀, hαx, zero_smul, sub_zero]
      exact hi₀ this
    have hprop : ∀ k ∈ {k : M.Λ | z₀ ∈ Submodule.span (ZMod p) ({M.coroot k} : Set M.V)},
        ∀ j, (M.cartan j k : ZMod p) ≠ 0 →
          j ∈ {k : M.Λ | z₀ ∈ Submodule.span (ZMod p) ({M.coroot k} : Set M.V)} := by
      intro k hk j hjk
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hk
      have hc0 : c ≠ 0 := fun h => hz₀_ne (by rw [← hc, h, zero_smul])
      have hαz : M.root j z₀ ≠ 0 := by
        rw [← hc, map_smul, smul_eq_mul, M.pairing j k]
        exact mul_ne_zero hc0 hjk
      have hfy : fτ (M.coroot j) ≠ 0 := fun h0 => hαz ((hdich j).1 h0)
      exact (hdich j).2 hfy
    have hSuniv : {k : M.Λ | z₀ ∈ Submodule.span (ZMod p) ({M.coroot k} : Set M.V)} =
        Set.univ := ggCartan_closed_eq_univ hp2 M.isWeyl M.isCartan h3 ⟨i₀, hseed⟩ hprop
    obtain ⟨j, k, hjk, hCjk⟩ := ggQ2h4_exists_not_adj M.isWeyl M.isCartan h3
    have hCkj : M.cartan k j = 0 := M.isCartan.eq_zero_symm hjk.symm hCjk
    have hjS : z₀ ∈ Submodule.span (ZMod p) ({M.coroot j} : Set M.V) := by
      change j ∈ ({k : M.Λ | z₀ ∈ Submodule.span (ZMod p) ({M.coroot k} : Set M.V)} : Set M.Λ)
      rw [hSuniv]
      exact Set.mem_univ j
    have hkS : z₀ ∈ Submodule.span (ZMod p) ({M.coroot k} : Set M.V) := by
      change k ∈ ({k : M.Λ | z₀ ∈ Submodule.span (ZMod p) ({M.coroot k} : Set M.V)} : Set M.Λ)
      rw [hSuniv]
      exact Set.mem_univ k
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hjS
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hkS
    have ha0 : a ≠ 0 := fun h => hz₀_ne (by rw [← ha, h, zero_smul])
    have hjeq : M.coroot j = (a⁻¹ * b) • M.coroot k := by
      calc M.coroot j = a⁻¹ • (a • M.coroot j) := by
              rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
        _ = a⁻¹ • z₀ := by rw [ha]
        _ = a⁻¹ • (b • M.coroot k) := by rw [hb]
        _ = (a⁻¹ * b) • M.coroot k := by rw [smul_smul]
    have hckj0 : M.root k (M.coroot j) = 0 := by rw [M.pairing k j, hCkj, Int.cast_zero]
    have hmul : (a⁻¹ * b) * 2 = 0 := by
      have h2 : (M.cartan k k : ZMod p) = 2 := by rw [M.isCartan.1 k]; norm_num
      have h := congrArg (M.root k) hjeq
      rw [map_smul, smul_eq_mul, hckj0, M.pairing k k, h2] at h
      exact h.symm
    have hab0 : a⁻¹ * b = 0 := (mul_eq_zero.mp hmul).resolve_right (zmod_two_ne_zero hp2)
    exact (ne_zero_of_apply_eq_two hp2 (hpair j)).1 (by rw [hjeq, hab0, zero_smul])
  obtain ⟨φ, hφmem, hφrefl, hφmove⟩ := hmain
  refine ⟨φ, hφmem, hφrefl, ⟨⟨x, hx⟩, Subgroup.mem_zpowers x, ?_⟩⟩
  intro hmem
  exact hφmove (by
    rw [hxV, ggLin_apply_ofMul]
    exact ggQ2h4_zpow_mem_span hx M.model (ggQ2h4_mem_zpowers_subtype hx hmem))

end CFSG.StandardType

end
