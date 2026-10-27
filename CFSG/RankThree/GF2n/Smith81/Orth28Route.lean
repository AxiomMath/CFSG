module

public import CFSG.RankThree.GF2n.Smith81.OrthCountAct
public import CFSG.RankThree.GF2n.Smith81.LinOddBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G]

structure OrthCtx (M Q Z B : Subgroup G) where
  K : Type
  [field : Field K]
  [fin : Finite K]
  [char2 : CharP K 2]
  γ : G → K
  M₀ : Tim79.QuadModel Q Z K γ
  hD : GlobalModelData M Q Z γ M₀
  ι : Type
  [fintypeι : Fintype ι]
  [deceqι : DecidableEq ι]
  qU : QuadraticForm K (ι → K)
  φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)
  hF : OrthFrame Q Z M₀ qU φ
  hA : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))

attribute [instance] OrthCtx.field OrthCtx.fin OrthCtx.char2 OrthCtx.fintypeι OrthCtx.deceqι

theorem exists_orthCtx (h : Smith24ActStatement) {M Q Z B : Subgroup G} [Finite G]
    (hc : SmithOrthCfg M Q Z B) : Nonempty (OrthCtx M Q Z B) := by
  obtain ⟨K, hK, hKf, hK2, γ, M₀, hD, ι, hι, hιd, qU, φ, hF, hA⟩ := h G M Q Z B hc
  exact ⟨⟨K, γ, M₀, hD, ι, qU, φ, hF, hA⟩⟩

@[expose] def Orth212C4CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
      ∀ z' ∈ Z, IsConj x (x * z') → z' = 1

@[expose] def Orth212C7CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
      ∀ (h q : G), q ∈ Q → h * x * h⁻¹ = x * q → ∃ q' ∈ Q, h * x * h⁻¹ = q' * x * q'⁻¹

@[expose] def Orth212C5CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
      (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z

section Assemble212

theorem smith212OrthCore_of_cond (h28 : Smith28OrthStatement) (c4 : Orth212C4CondStatement)
    (c5 : Orth212C5CondStatement) (c7 : Orth212C7CondStatement) : Smith212OrthCoreStatement := by
  intro G _ _ M Q Z B hc z hz hz1 x hxM hxQ hxc
  obtain ⟨g, hg⟩ := isConj_iff.mp hxc
  have hs : Sit M Q Z (conjSubgroup g Z) x := by
    have := Sit.of_conj hc.ctx.hyp hz hz1 (by rw [hg]; exact hxM) (by rw [hg]; exact hxQ)
    rwa [hg] at this
  have hne : Q ⊓ QB (conjSubgroup g Z) ≠ ⊥ := by
    obtain ⟨v, hv, hvQ, hvX⟩ := h28 G M Q Z B hc _ x hs
    intro h
    have hm : v ∈ Q ⊓ QB (conjSubgroup g Z) := ⟨hvQ, hvX⟩
    rw [h, Subgroup.mem_bot] at hm
    exact ne_one_of_isConj_Z hs.ne_one hv hm
  have hxz : IsConj z x := hxc
  refine ⟨?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨hy, ⟨z', hz', rfl⟩⟩
      have h1 : IsConj x (x * z') := hxz.symm.trans hy
      have := c4 G M Q Z B hc _ x hs hne z' hz' h1
      subst this
      simp
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hxz, 1, Z.one_mem, by simp⟩
  · ext y
    constructor
    · rintro ⟨hy, ⟨q, hq, rfl⟩⟩
      obtain ⟨h, hh⟩ := isConj_iff.mp hy
      obtain ⟨q', hq', e⟩ := c7 G M Q Z B hc _ x hs hne h q hq hh
      exact ⟨q', hq', hh.symm.trans e⟩
    · rintro ⟨s, hs', rfl⟩
      refine ⟨isConj_iff.mpr ⟨s, rfl⟩, x⁻¹ * s * x * s⁻¹, ?_, by group⟩
      have h1 := conj_mem_Q hc.ctx.hyp (M.inv_mem hxM) hs'
      have : x⁻¹ * s * x * s⁻¹ = (x⁻¹ * s * (x⁻¹)⁻¹) * s⁻¹ := by group
      rw [this]
      exact Q.mul_mem h1 (Q.inv_mem hs')
  · intro X' hX' hxX'
    have hXe : conjSubgroup g Z = X' :=
      IsZConjugate.eq_of_mem hc.ctx.hyp ⟨g, rfl⟩ hX' hs.ne_one hs.mem hxX'
    subst hXe
    exact c5 G M Q Z B hc _ x hs hne

end Assemble212

@[expose] def Orth213Concl (z : G) (x y : G) : Prop :=
  (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
    (orderOf (x * y) = 4 → IsConj z ((x * y) ^ 2))

@[expose] def Orth213ElemStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ x y : G, x ∈ M → y ∈ M → IsConj z x → IsConj z y →
      (x ∈ Q ∨ y ∈ Q ∨ x * y ∈ Q) → Orth213Concl z x y

@[expose] def Orth213OutsideStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ x y : G, x ∈ M → y ∈ M → IsConj z x → IsConj z y →
      x ∉ Q → y ∉ Q → x * y ∉ Q → Orth213Concl z x y

theorem smith213Orth_of_parts (h1 : Orth213ElemStatement)
    (h2 : Orth213OutsideStatement) : Smith213OrthStatement := by
  intro G _ _ M Q Z B hc z hz hz1
  have hH := hc.ctx.hyp
  have hconcl : ∀ x y : G, x ∈ M → y ∈ M → IsConj z x → IsConj z y → Orth213Concl z x y := by
    intro x y hxM hyM hx hy
    by_cases hcase : x ∈ Q ∨ y ∈ Q ∨ x * y ∈ Q
    · exact h1 G M Q Z B hc z hz hz1 x y hxM hyM hx hy hcase
    · push Not at hcase
      exact h2 G M Q Z B hc z hz hz1 x y hxM hyM hx hy hcase.1 hcase.2.1 hcase.2.2
  refine ⟨?_, ?_, ?_⟩
  · rintro d ⟨hd, -⟩
    have h2d : d * d = 1 := mul_self_eq_one_of_isConj_Z hH hz hd
    have hd1 : d ≠ 1 := ne_one_of_isConj_Z hz1 hd
    exact orderOf_eq_prime (by rw [pow_two]; exact h2d) hd1
  · rintro d ⟨hd, hdM⟩ e ⟨he, heM⟩
    exact (hconcl d e hdM heM hd he).1
  · rintro d ⟨hd, hdM⟩ e ⟨he, heM⟩ h4
    exact ⟨(hconcl d e hdM heM hd he).2 h4, M.pow_mem (M.mul_mem hdM heM) 2⟩

section Unified

variable [Finite G]

@[expose] def OrthValid (M Q Z : Subgroup G) (x q' : G) : Prop :=
  q' ∈ Q ∧ IsConj x q' ∧ IsConj x ⁅q', x⁆ ∧
    ∀ C₀ : Subgroup G, IsZConjugate Z C₀ → ⁅q', x⁆ ∈ C₀ → q' ∈ QB C₀

@[expose] def OrthEpsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
      (∃ q', OrthValid M Q Z x q') ∨ ∃ v ∈ Jx Q X x, v ≠ 1 ∧ IsConj x v

@[expose] def OrthWitnessStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∀ q' ∈ Q, IsConj x q' → ⁅q', x⁆ ∈ Z → ⁅q', x⁆ ≠ 1 →
        ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z'

@[expose] def OrthDTStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
      ∀ q', OrthValid M Q Z x q' → ∀ g : G, ⁅q', x⁆ ∈ conjSubgroup g Z →
        x ∉ QB (conjSubgroup g Z) → g⁻¹ * x * g ∈ Lgen M (LB M Q B)

@[expose] def OrthNoCaseIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
      (∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z') → False

theorem commute_comm_of_sq {x q' : G} (hx2 : x * x = 1) (hc2 : ⁅q', x⁆ * ⁅q', x⁆ = 1) :
    x * ⁅q', x⁆ = ⁅q', x⁆ * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h1 : x * ⁅q', x⁆ * x⁻¹ = ⁅q', x⁆⁻¹ := by
    rw [hxi]
    simp only [commutatorElement_def, hxi, mul_inv_rev, inv_inv]
    calc x * (q' * x * q'⁻¹ * x) * x = x * q' * x * q'⁻¹ * (x * x) := by group
      _ = x * q' * x * q'⁻¹ := by rw [hx2, mul_one]
      _ = x * (q' * (x * q'⁻¹)) := by group
  have h2 : ⁅q', x⁆⁻¹ = ⁅q', x⁆ := inv_eq_of_mul_eq_one_right hc2
  rw [h2] at h1
  calc x * ⁅q', x⁆ = x * ⁅q', x⁆ * x⁻¹ * x := by group
    _ = ⁅q', x⁆ * x := by rw [h1]

theorem orth28Valid_of_components (hwit : OrthWitnessStatement) (hdt : OrthDTStatement)
    (hnc : OrthNoCaseIStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
      ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
        ∀ q', OrthValid M Q Z x q' → ⁅q', x⁆ ∈ Jx Q X x ∧ ⁅q', x⁆ ≠ 1 ∧ IsConj x ⁅q', x⁆ := by
  intro G _ _ M Q Z B hcfg X x hs hxL q' hval
  have H := hcfg.ctx.hyp
  obtain ⟨hq'Q, hq'c, hcc, hq'QB⟩ := hval
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have hz₀ : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (hg₀ ▸ hs.mem)
  have hz₀x : IsConj (g₀⁻¹ * x * g₀) x := isConj_iff.mpr ⟨g₀, by group⟩
  have hz₀c : IsConj (g₀⁻¹ * x * g₀) ⁅q', x⁆ := hz₀x.trans hcc
  have hc1 : ⁅q', x⁆ ≠ 1 := ne_one_of_isConj_Z hs.ne_one hcc
  have hcQ : ⁅q', x⁆ ∈ Q := comm_mem_Q H hs.memM hq'Q
  have hc2 : ⁅q', x⁆ * ⁅q', x⁆ = 1 := mul_self_eq_one_of_isConj_Z H hz₀ hz₀c
  have hxc : x * ⁅q', x⁆ = ⁅q', x⁆ * x := commute_comm_of_sq hs.x_sq hc2
  obtain ⟨C₀, hC₀, hcC₀⟩ := exists_isZConjugate_mem hz₀ hz₀c
  have hxN : x ∈ Subgroup.normalizer (C₀ : Set G) :=
    hC₀.mem_normalizer_of_commute H hc1 hcC₀ hxc
  have hJ : ⁅q', x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ :=
    Subgroup.commutator_mem_commutator hq'Q (Subgroup.mem_zpowers x)
  by_cases hxQ : x ∈ QB C₀
  · have hXle : X ≤ QB C₀ := IsZConjugate.le_QB_of_mem H hC₀ hs.conj hs.ne_one hs.mem hxQ
    have hC₀X : C₀ ≤ QB X := (IsZConjugate.le_QB_iff H hC₀ hs.conj).mp hXle
    exact ⟨Subgroup.mem_inf.mpr ⟨hJ, hC₀X hcC₀⟩, hc1, hcc⟩
  · exfalso
    obtain ⟨g, rfl⟩ := hC₀
    have hs'' := sit_conj_back H hs.conj hs.mem hs.ne_one hxN hxQ
    have hQ' : QB (conjSubgroup g Z) = conjSubgroup g Q := QB_conj_eq H g
    have hq'' : g⁻¹ * q' * g ∈ Q := by
      have := hq'QB (conjSubgroup g Z) ⟨g, rfl⟩ hcC₀
      rw [hQ'] at this
      exact mem_conjSubgroup.mp this
    have hcomm : ⁅g⁻¹ * q' * g, g⁻¹ * x * g⁆ = g⁻¹ * ⁅q', x⁆ * g := by
      simp only [commutatorElement_def]; group
    have hcZ : ⁅g⁻¹ * q' * g, g⁻¹ * x * g⁆ ∈ Z := by
      rw [hcomm]; exact mem_conjSubgroup.mp hcC₀
    have hcZ1 : ⁅g⁻¹ * q' * g, g⁻¹ * x * g⁆ ≠ 1 := by
      rw [hcomm]
      intro h
      apply hc1
      have : ⁅q', x⁆ = g * (g⁻¹ * ⁅q', x⁆ * g) * g⁻¹ := by group
      rw [this, h]; group
    have hconj : IsConj (g⁻¹ * x * g) (g⁻¹ * q' * g) := by
      obtain ⟨k, hk⟩ := isConj_iff.mp hq'c
      exact isConj_iff.mpr ⟨g⁻¹ * k * g, by
        rw [← hk]; group⟩
    have hxL'' : g⁻¹ * x * g ∈ Lgen M (LB M Q B) :=
      hdt G M Q Z B hcfg X x hs hxL q' ⟨hq'Q, hq'c, hcc, hq'QB⟩ g hcC₀ hxQ
    exact hnc G M Q Z B hcfg _ _ hs'' hxL''
      (hwit G M Q Z B hcfg _ _ hs'' _ hq'' hconj hcZ hcZ1)

@[expose] def OrthR0Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ x₀ ∈ X, x₀ ≠ 1 ∧ x₀ ∈ Lgen M (LB M Q B)

@[expose] def Orth28StrongStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
      ∃ v ∈ Jx Q X x, v ≠ 1 ∧ IsConj x v

theorem orth28Strong_of_eps (heps : OrthEpsStatement) (hwit : OrthWitnessStatement)
    (hdt : OrthDTStatement) (hnc : OrthNoCaseIStatement) : Orth28StrongStatement := by
  intro G _ _ M Q Z B hcfg X x hs hxL
  rcases heps G M Q Z B hcfg X x hs hxL with ⟨q', hval⟩ | hdir
  · obtain ⟨hJ, hc1, hcc⟩ :=
      orth28Valid_of_components hwit hdt hnc G M Q Z B hcfg X x hs hxL q' hval
    exact ⟨_, hJ, hc1, hcc⟩
  · exact hdir

theorem smith28Orth_of_strong (hR0 : OrthR0Statement) (h : Orth28StrongStatement) :
    Smith28OrthStatement := by
  intro G _ _ M Q Z B hc X x hs
  obtain ⟨x₀, hx₀X, hx₀1, hx₀L⟩ := hR0 G M Q Z B hc X x hs
  have hs₀ : Sit M Q Z X x₀ := by
    refine ⟨hs.hyp, hs.conj, hx₀X, hx₀1, (Lgen_le hc.ctx.LB_le_M) hx₀L, fun hQ => hx₀1 ?_⟩
    have : x₀ ∈ X ⊓ Q := ⟨hx₀X, hQ⟩
    rw [hs.X_inf_Q, Subgroup.mem_bot] at this
    exact this
  obtain ⟨v, hvJ, -, hvc⟩ := h G M Q Z B hc X x₀ hs₀ hx₀L
  obtain ⟨g, hg⟩ := hs.conj
  have hx : g⁻¹ * x * g ∈ Z := mem_conjSubgroup.mp (hg ▸ hs.mem)
  have hx₀' : g⁻¹ * x₀ * g ∈ Z := mem_conjSubgroup.mp (hg ▸ hx₀X)
  have hxne : g⁻¹ * x * g ≠ 1 := by
    intro h; apply hs.ne_one
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group
  have hx₀ne : g⁻¹ * x₀ * g ≠ 1 := by
    intro h; apply hx₀1
    have : x₀ = g * (g⁻¹ * x₀ * g) * g⁻¹ := by group
    rw [this, h]; group
  obtain ⟨m, -, hm⟩ := Z_isConj hc.ctx.hyp hx hxne hx₀' hx₀ne
  have hzz : IsConj (g⁻¹ * x * g) (g⁻¹ * x₀ * g) := isConj_iff.mpr ⟨m, hm⟩
  have hxz : IsConj x (g⁻¹ * x * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hz₀x₀ : IsConj (g⁻¹ * x₀ * g) x₀ := isConj_iff.mpr ⟨g, by group⟩
  exact ⟨v, hxz.trans (hzz.trans (hz₀x₀.trans hvc)), Jx_le_Q hs₀ hvJ,
    (Subgroup.mem_inf.mp hvJ).2⟩

theorem smith28aOrth_of_28 (h : Smith28OrthStatement) : Smith28aOrthStatement := by
  intro G _ _ M Q Z B hc X x hs hbot
  obtain ⟨v, hvc, hvQ, hvX⟩ := h G M Q Z B hc X x hs
  have hv : v ∈ Q ⊓ QB X := ⟨hvQ, hvX⟩
  rw [hbot, Subgroup.mem_bot] at hv
  exact ne_one_of_isConj_Z hs.ne_one hvc hv

end Unified

section Leaves

variable [Finite G]

@[expose] def OrthRootInP (M Q Z X : Subgroup G) (x : G) : Prop :=
  ∃ v : G, v ≠ 1 ∧ IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

@[expose] def Orth212C4RootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → OrthRootInP M Q Z X x →
      ∀ z' ∈ Z, IsConj x (x * z') → z' = 1

@[expose] def OrthCaseIPBotStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
      (∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z') → Q ⊓ QB X = ⊥ → False

@[expose] def OrthCaseIRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
      (∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z') → Q ⊓ QB X ≠ ⊥ → OrthRootInP M Q Z X x

theorem orthNoCaseI_of_leaves (hP : OrthCaseIPBotStatement) (hR : OrthCaseIRootStatement)
    (h4 : Orth212C4RootStatement) : OrthNoCaseIStatement := by
  intro G _ _ M Q Z B hcfg X x hs hxL hI
  have H := hcfg.ctx.hyp
  by_cases hbot : Q ⊓ QB X = ⊥
  · exact hP G M Q Z B hcfg X x hs hxL hI hbot
  · have hroot := hR G M Q Z B hcfg X x hs hxL hI hbot
    have hZne : Z ≠ ⊥ := by
      intro h
      have h4' := H.q4
      rw [h, Subgroup.card_bot] at h4'
      omega
    obtain ⟨z', hz'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    have hz'1' : (z' : G) ≠ 1 := fun h => hz'1 (Subtype.ext h)
    obtain ⟨q, hq, hqx⟩ := hI z' z'.2
    have hconj : IsConj x (x * z') := isConj_iff.mpr ⟨q⁻¹, by simpa using hqx⟩
    exact hz'1' (h4 G M Q Z B hcfg X x hs hroot z' z'.2 hconj)

theorem orth212C4Cond_of_root (h4 : Orth212C4RootStatement) (h28 : Smith28OrthStatement) :
    Orth212C4CondStatement := by
  intro G _ _ M Q Z B hc X x hs _ z' hz' h
  obtain ⟨v, hvc, hvQ, hvX⟩ := h28 G M Q Z B hc X x hs
  exact h4 G M Q Z B hc X x hs ⟨v, ne_one_of_isConj_Z hs.ne_one hvc, hvc, hvQ, hvX⟩ z' hz' h

end Leaves

end CFSG.RankThree.GF2n.Smith81
