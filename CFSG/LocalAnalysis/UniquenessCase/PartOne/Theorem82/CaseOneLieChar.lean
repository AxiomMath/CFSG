module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneMechanisms
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneAbar
import CFSG.GroupTheory.PGroup.LiftCoprimeQuotient
import CFSG.GroupTheory.SubgroupConjBasic
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem signed_point_reps :
    ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
      ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
        ((∀ i, ε i * v (σ i) = ![1, 0, 0] i) ∨
         (∀ i, ε i * v (σ i) = ![1, 1, 0] i) ∨
         (∀ i, ε i * v (σ i) = ![1, 1, 1] i)) := by
  decide

theorem sumZero_point_reps :
    ∀ v : Fin 4 → ZMod 3, (¬ ∃ d : ZMod 3, v = fun _ => d) →
      ∃ (σ : Equiv.Perm (Fin 4)) (t d : ZMod 3), t ≠ 0 ∧
        ((∀ i, v (σ i) = t * ![1, 1, -1, -1] i + d) ∨
         (∀ i, v (σ i) = t * ![1, -1, 0, 0] i + d) ∨
         (∀ i, v (σ i) = t * ![2, 0, 2, 2] i + d)) := by
  decide

theorem sumZero_target_add :
    (![2, 0, 2, 2] : Fin 4 → ZMod 3) = ![1, 1, -1, -1] + ![1, -1, 0, 0] := by
  decide

namespace Case811Sylow

variable {c : Counterexample4 G}

lemma exists_conj_of_coords {V : Type*} [Group V] (h : Case811Sylow c)
    {c₀ : V →* c.Lbar} (a : V →* ↥c.L)
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hXinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp (h.A.subgroupOf c.L).subtype))
    (φ : V → V) {n : c.Lbar}
    (hn : n ∈ Subgroup.normalizer
      ((((h.A.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) :
        Subgroup c.Lbar) : Set c.Lbar))
    (hform : ∀ v, n * c₀ v * n⁻¹ = c₀ (φ v)) :
    ∃ g : ↥c.L, (g : G) ∈ Subgroup.normalizer (h.A : Set G) ∧
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) g = n ∧
      ∀ v, (g : G) * ((a v : ↥c.L) : G) * (g : G)⁻¹ = ((a (φ v) : ↥c.L) : G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  obtain ⟨g, hgN, hgπ⟩ :=
    Counterexample4.exists_mem_normalizer_of_mem_normalizer_lbar
      c (q := 3) (by norm_num) (h.A_le.trans h.P_le_L) (h.elemAbelian.isPGroup) hn
  have hgNX : g ∈ Subgroup.normalizer ((h.A.subgroupOf c.L) : Set ↥c.L) := by
    have hgSub : g ∈ (Subgroup.normalizer (h.A : Set G)).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hgN
    rwa [Subgroup.subgroupOf_normalizer_eq (h.A_le.trans h.P_le_L)] at hgSub
  refine ⟨g, hgN, hgπ, ?_⟩
  intro v
  have havX : a v ∈ h.A.subgroupOf c.L := by
    have h : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at h
  let x : ↥c.L := g * a v * g⁻¹
  have hxX : x ∈ h.A.subgroupOf c.L :=
    (Subgroup.mem_normalizer_iff.mp hgNX (a v)).mp havX
  have hφX : a (φ v) ∈ h.A.subgroupOf c.L := by
    have h : a (φ v) ∈ a.range := MonoidHom.mem_range.mpr ⟨φ v, rfl⟩
    rwa [ha_range] at h
  have himg : π x = π (a (φ v)) := by
    show π (g * a v * g⁻¹) = π (a (φ v))
    rw [map_mul, map_mul, map_inv, hgπ, ha_apply, hform, ha_apply]
  have hxeq : x = a (φ v) := by
    have hsub : (⟨x, hxX⟩ : h.A.subgroupOf c.L) =
        ⟨a (φ v), hφX⟩ := hXinj (by simpa [π] using himg)
    exact congrArg Subtype.val hsub
  have := congrArg (fun z : ↥c.L => (z : G)) hxeq
  simpa [x] using this

variable {c : Counterexample4 G} (h : Case811Sylow c)

theorem false_of_forall_normalizer_le {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (hN : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      Subgroup.normalizer (X : Set G) ≤ c.S.M ∧ p ∣ Nat.card (Subgroup.normalizer (X : Set G))) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  exact h.not_rankThreeGamma_le
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le
      (p := p) (q := 3) (M := c.S.M) (A := h.A)
      (c.isStronglyPEmbedded_of_mem_sigma hp) h.elemAbelian.isPGroup hN)

theorem normalizer_le_of_le_of_isElemAbelian {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {E : Subgroup G} (hEA : E ≤ h.A) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9)
    (hcent : 0 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)))
    (hN : ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)))
    {X : Subgroup G} (hXE : X ≤ E) (hX : Nat.card X = 3) :
    Subgroup.normalizer (X : Set G) ≤ c.S.M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hEM : E ≤ c.S.M := hEA.trans (h.A_le.trans (h.P_le_L.trans c.hyp81.1))
  have hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ c.S.M :=
    h76 3 (by norm_num) E hEM hE (by rw [hEcard]; norm_num) hcent hN
  have hNX_le_Γ : Subgroup.normalizer (X : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 E := by
    have hXab : CFSG.Open.IsElemAbelian 3 X := hE.mono hXE
    have h1 : 1 ≤ CFSG.Open.pRank 3 X :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl X) hXab
        (by rw [hX]; norm_num)
    have hcore := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
      (p := 3) (k := 1) (P := E) (Q := X) hXE h1
    simpa [CFSG.Open.rankThreeGamma] using hcore
  exact hNX_le_Γ.trans hΓ

theorem mem_normalizer_of_coords (h : Case811Sylow c) {V : Type*} [Group V] {c₀ : V →* c.Lbar}
    (hc₀range : c₀.range = h.Abar) {n : c.Lbar} {φ : V → V}
    (hform : ∀ v, n * c₀ v * n⁻¹ = c₀ (φ v)) :
    n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) := by
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  rw [← hc₀range] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  exact ⟨φ v, (hform v).symm⟩

private lemma exists_gen_coords {c : Counterexample4 G} (h : Case811Sylow c) {V : Type*}
    [Group V] {a : V →* ↥c.L} (ha_range : a.range = h.A.subgroupOf c.L)
    {X : Subgroup G} (hXA : X ≤ h.A) (hXcard : Nat.card X = 3) :
    ∃ v : V, ((a v : ↥c.L) : G) ∈ X ∧ ((a v : ↥c.L) : G) ≠ 1 ∧ v ≠ 1 ∧
      orderOf ((a v : ↥c.L) : G) = 3 ∧ X = Subgroup.zpowers ((a v : ↥c.L) : G) := by
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hXcard
    omega
  obtain ⟨x, hxX, hxne⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hXne ((Subgroup.eq_bot_iff_forall X).mpr (fun y hy => by
      by_contra hy1
      exact hy1 (h y hy)))
  have hxord : orderOf x = 3 :=
    orderOf_eq_prime (h.elemAbelian.2 x (hXA hxX)) hxne
  have hxL : x ∈ c.L := (hXA.trans (h.A_le.trans h.P_le_L)) hxX
  have hxrange : (⟨x, hxL⟩ : ↥c.L) ∈ a.range := by
    rw [ha_range]
    exact Subgroup.mem_subgroupOf.mpr (hXA hxX)
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hxrange
  have hvG : ((a v : ↥c.L) : G) = x := congrArg (fun z : ↥c.L => (z : G)) hv
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvG]; exact hxX
  · rw [hvG]; exact hxne
  · intro hv1
    exact hxne (by rw [← hvG, hv1, map_one]; rfl)
  · rw [hvG]; exact hxord
  · rw [hvG]
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
      (by rw [Nat.card_zpowers, hxord, hXcard])).symm

private lemma pRank_centralizer_pos_of_zpowers {c : Counterexample4 G} (h : Case811Sylow c)
    {r : ℕ} (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M) (hr2 : r ≠ 2)
    {V : Type*} [Group V] {c₀ : V →* c.Lbar} {a : V →* ↥c.L} {v₁ v₂ : V}
    (hmem₁ : ((a v₁ : ↥c.L) : G) ∈ h.A) (hmem₂ : ((a v₂ : ↥c.L) : G) ∈ h.A)
    (h₁ : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v₁) = c₀ v₁)
    (h₂ : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v₂) = c₀ v₂)
    (hrank : 1 ≤ CFSG.Open.pRank r (Subgroup.centralizer ({c₀ v₁, c₀ v₂} : Set c.Lbar))) :
    0 < CFSG.Open.pRank r (c.S.M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
        Subgroup.zpowers ((a v₂ : ↥c.L) : G) : Subgroup G) : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hEA : Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G) ≤ h.A :=
    sup_le (Subgroup.zpowers_le.mpr hmem₁) (Subgroup.zpowers_le.mpr hmem₂)
  have hEab : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G)) := h.elemAbelian.mono hEA
  have hEsub : (Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G)).subgroupOf c.L =
      Subgroup.zpowers (a v₁) ⊔ Subgroup.zpowers (a v₂) := by
    rw [Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr (a v₁).2)
      (Subgroup.zpowers_le.mpr (a v₂).2),
      CFSG.GroupTheory.zpowers_coe_subgroupOf, CFSG.GroupTheory.zpowers_coe_subgroupOf]
  have himg : ((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G)).subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) =
      Subgroup.zpowers (c₀ v₁) ⊔ Subgroup.zpowers (c₀ v₂) := by
    rw [hEsub, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, h₁, h₂]
  have heq : Subgroup.centralizer ((((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G)).subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) : Subgroup c.Lbar) : Set c.Lbar) =
      Subgroup.centralizer ({c₀ v₁, c₀ v₂} : Set c.Lbar) := by
    rw [himg, CFSG.GroupTheory.centralizer_zpowers_sup_zpowers]
  have htrans := c.pRank_centralizer_lbar (q := 3) (by norm_num) (p := r) hr2
    (hEA.trans (h.A_le.trans h.P_le_L)) hEab.isPGroup
  have hrankL : 1 ≤ CFSG.Open.pRank r (c.L ⊓ Subgroup.centralizer
      ((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
        Subgroup.zpowers ((a v₂ : ↥c.L) : G) : Subgroup G) : Set G)) := by
    rw [htrans, heq]
    exact hrank
  have hmono : CFSG.Open.pRank r (c.L ⊓ Subgroup.centralizer
      ((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
        Subgroup.zpowers ((a v₂ : ↥c.L) : G) : Subgroup G) : Set G)) ≤
      CFSG.Open.pRank r (c.S.M ⊓ Subgroup.centralizer
        ((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a v₂ : ↥c.L) : G) : Subgroup G) : Set G)) :=
    CFSG.SectionRank.pRank_mono hr.1.1.one_lt (inf_le_inf c.hyp81.1 le_rfl)
  omega

private lemma plane_point_pRank {c : Counterexample4 G} (h : Case811Sylow c) {r : ℕ}
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M) (hr2 : r ≠ 2)
    (hrank2 : ∀ Y : Subgroup c.Lbar, Y ≤ h.Abar → Nat.card Y = 3 →
      2 ≤ CFSG.pRank r ↥(Subgroup.centralizer (Y : Set c.Lbar)))
    {E : Subgroup G} (hEA : E ≤ h.A) (hEab : CFSG.Open.IsElemAbelian 3 E) :
    ∀ Y : Subgroup G, Y ≤ E → Nat.card Y = 3 →
      1 < CFSG.Open.pRank r (c.S.M ⊓ Subgroup.normalizer (Y : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  intro Y hYE hYcard
  have hY3 : IsPGroup 3 Y := hEab.isPGroup.to_le hYE
  have hYL : Y ≤ c.L := hYE.trans (hEA.trans (h.A_le.trans h.P_le_L))
  have htrans := c.pRank_centralizer_lbar (q := 3) (by norm_num) (p := r) hr2 hYL hY3
  have hYbar_card : Nat.card ((Y.subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) = 3 := by
    rw [h.card_map_of_le_A (hYE.trans hEA), hYcard]
  have hrank : 2 ≤ CFSG.Open.pRank r (Subgroup.centralizer
      (((Y.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) :
        Subgroup c.Lbar) : Set c.Lbar)) := by
    have h := hrank2 _ (h.map_le_Abar (hYE.trans hEA)) hYbar_card
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h
  have hrankL : 2 ≤ CFSG.Open.pRank r (c.L ⊓ Subgroup.centralizer (Y : Set G)) := by
    rw [htrans]
    exact hrank
  have hmono : CFSG.Open.pRank r (c.L ⊓ Subgroup.centralizer (Y : Set G)) ≤
      CFSG.Open.pRank r (c.S.M ⊓ Subgroup.normalizer (Y : Set G)) :=
    CFSG.SectionRank.pRank_mono hr.1.1.one_lt
      (inf_le_inf c.hyp81.1 (Subgroup.centralizer_le_normalizer (Y : Set G)))
  omega

private lemma plane_facts_of_zpowers {c : Counterexample4 G} (h : Case811Sylow c) {r : ℕ}
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M r)
    (hr2 : r ≠ 2)
    (hrank2 : ∀ Y : Subgroup c.Lbar, Y ≤ h.Abar → Nat.card Y = 3 →
      2 ≤ CFSG.pRank r ↥(Subgroup.centralizer (Y : Set c.Lbar)))
    {V : Type*} [Group V] {c₀ : V →* c.Lbar} {a : V →* ↥c.L}
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    {v₁ v₂ : V} (hmem₁ : ((a v₁ : ↥c.L) : G) ∈ h.A)
    (hmem₂ : ((a v₂ : ↥c.L) : G) ∈ h.A)
    (hord₁ : orderOf ((a v₁ : ↥c.L) : G) = 3)
    (hord₂ : orderOf ((a v₂ : ↥c.L) : G) = 3)
    (hnot : ((a v₂ : ↥c.L) : G) ∉ Subgroup.zpowers ((a v₁ : ↥c.L) : G))
    (hcent : 1 ≤ CFSG.Open.pRank r (Subgroup.centralizer ({c₀ v₁, c₀ v₂} : Set c.Lbar))) :
    ∀ X : Subgroup G,
      X ≤ Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔ Subgroup.zpowers ((a v₂ : ↥c.L) : G) →
      Nat.card X = 3 →
      Subgroup.normalizer (X : Set G) ≤ c.S.M ∧
        r ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hEA : Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G) ≤ h.A :=
    sup_le (Subgroup.zpowers_le.mpr hmem₁) (Subgroup.zpowers_le.mpr hmem₂)
  have hEab : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G)) := h.elemAbelian.mono hEA
  have hEcard : Nat.card (Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a v₂ : ↥c.L) : G) : Subgroup G) = 9 := by
    have h := (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_mem_isElemAbelian h.elemAbelian
      hmem₁ hmem₂ hord₁ hord₂ hnot).2
    simpa using h
  have hcentpos : 0 < CFSG.Open.pRank r (c.S.M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers ((a v₁ : ↥c.L) : G) ⊔
        Subgroup.zpowers ((a v₂ : ↥c.L) : G) : Subgroup G) : Set G)) :=
    pRank_centralizer_pos_of_zpowers h hr hr2 hmem₁ hmem₂ (ha_apply v₁) (ha_apply v₂) hcent
  have hN := plane_point_pRank h hr hr2 hrank2 hEA hEab
  intro X hXE hXcard
  refine ⟨h.normalizer_le_of_le_of_isElemAbelian hr h76 hEA hEab hEcard hcentpos hN hXE hXcard, ?_⟩
  exact (CFSG.GroupTheory.dvd_card_of_one_le_pRank hr.1.1
    (le_of_lt (hN X hXE hXcard))).trans (Subgroup.card_dvd_of_le inf_le_right)

private lemma normalizer_facts_of_map_conj_eq {c : Counterexample4 G} {r : ℕ} {X Z : Subgroup G}
    {g : G} (hgM : g ∈ c.S.M) (hXZ : X.map (MulAut.conj g).toMonoidHom = Z)
    (hZ : Subgroup.normalizer (Z : Set G) ≤ c.S.M ∧
      r ∣ Nat.card (Subgroup.normalizer (Z : Set G))) :
    Subgroup.normalizer (X : Set G) ≤ c.S.M ∧
      r ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
  refine ⟨CFSG.GroupTheory.normalizer_le_of_map_conj_le hgM ?_, ?_⟩
  · rw [hXZ]
    exact hZ.1
  · have hcard := Subgroup.card_map_of_injective
      (f := (MulAut.conj g).toMonoidHom) (K := Subgroup.normalizer (X : Set G))
      (MulAut.conj g).injective
    rw [Subgroup.map_equiv_normalizer_eq, hXZ] at hcard
    rw [← hcard]
    exact hZ.2

private lemma ofAdd_pow_three {n : ℕ} (v : Fin n → ZMod 3) :
    (Multiplicative.ofAdd v : Multiplicative (Fin n → ZMod 3)) ^ 3 = 1 := by
  rw [← ofAdd_nsmul]
  have hzero : (3 : ℕ) • v = 0 := by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    have h3 : (↑(3 : ℕ) : ZMod 3) = 0 := by rfl
    rw [h3, zero_mul]
  rw [hzero, ofAdd_zero]

theorem exists_coords_lift {c : Counterexample4 G} (h : Case811Sylow c) {V : Type*}
    [Group V] {c₀ : V →* c.Lbar} (hrange : c₀.range = h.Abar) :
    ∃ a : V →* ↥c.L,
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
        (h.A.subgroupOf c.L).subtype) ∧
      (∀ v, (a v : G) ∈ h.A) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  have hN3 : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hX3 : IsPGroup 3 (h.A.subgroupOf c.L) := h.elemAbelian.isPGroup.comap_subtype (K := c.L)
  have hXinj : Function.Injective (π.comp (h.A.subgroupOf c.L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := N)
      (Q := h.A.subgroupOf c.L) hN3 hX3
  obtain ⟨a, ha_range, ha_apply⟩ :=
    CFSG.GroupTheory.exists_lift_of_isPGroup_of_not_dvd_card (N := N) hN3 hX3
      (X := h.A.subgroupOf c.L) (Xbar := h.Abar) rfl c₀ hrange
  have ha_memX : ∀ v, a v ∈ h.A.subgroupOf c.L := by
    intro v
    have hv : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hv
  have ha_memA : ∀ v, (a v : G) ∈ h.A := by
    intro v
    have hmem : (a v : G) ∈ (h.A.subgroupOf c.L).map c.L.subtype :=
      Subgroup.mem_map_of_mem c.L.subtype (ha_memX v)
    rwa [Subgroup.map_subgroupOf_eq_of_le (h.A_le.trans h.P_le_L)] at hmem
  exact ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩

theorem signed_coords_setup {c : Counterexample4 G} (h : Case811Sylow c) (hK6c : K6c)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f) (hfam : fam ≠ .l4) :
    ∃ (c₀ : Multiplicative (Fin 3 → ZMod 3) →* c.Lbar)
      (a : Multiplicative (Fin 3 → ZMod 3) →* ↥c.L),
      IsSignedCoords h.Abar c₀ ∧
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
        (h.A.subgroupOf c.L).subtype) ∧
      Function.Injective a ∧
      (∀ v, (a v : G) ∈ h.A) ∧
      (∀ v : Fin 3 → ZMod 3, v ≠ 0 →
        orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, hc₀⟩ := (hK6c c.Lbar fam r f hlie h.Abar h.isElemAbelian_Abar h.card_Abar).2 hfam
  obtain ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩ := exists_coords_lift h hc₀.2.1
  have ha_inj : Function.Injective a := by
    intro u v huv
    apply hc₀.1
    have h : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a u) =
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) := congrArg _ huv
    rwa [ha_apply u, ha_apply v] at h
  have ha_order : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
      orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3 := by
    intro v hv
    have hvne : (Multiplicative.ofAdd v : Multiplicative (Fin 3 → ZMod 3)) ≠ 1 := by
      intro hone
      exact hv (ofAdd_eq_one.mp hone)
    rw [Subgroup.orderOf_coe, orderOf_injective a ha_inj, orderOf_eq_prime (ofAdd_pow_three v) hvne]
  exact ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_inj, ha_memA, ha_order⟩

private lemma signed_not_mem_zpowers {c : Counterexample4 G}
    {a : Multiplicative (Fin 3 → ZMod 3) →* ↥c.L} (ha_inj : Function.Injective a)
    {v w : Fin 3 → ZMod 3} {i j : Fin 3} (hij : v i * w j ≠ v j * w i) :
    ((a (Multiplicative.ofAdd v) : ↥c.L) : G) ∉
      Subgroup.zpowers ((a (Multiplicative.ofAdd w) : ↥c.L) : G) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkL : a (Multiplicative.ofAdd v) = (a (Multiplicative.ofAdd w)) ^ k := by
    apply Subtype.ext
    simpa using hk.symm
  have hk'' : a (Multiplicative.ofAdd v) = a ((Multiplicative.ofAdd w) ^ k) := by
    rw [map_zpow]
    exact hkL
  have hv : Multiplicative.ofAdd v = (Multiplicative.ofAdd w) ^ k := ha_inj hk''
  rw [← ofAdd_zsmul] at hv
  have hv' : v = k • w := by
    have := congrArg Multiplicative.toAdd hv
    simpa using this
  have hvi : v i = k * w i := by simpa using congrFun hv' i
  have hvj : v j = k * w j := by simpa using congrFun hv' j
  exact hij (by rw [hvi, hvj]; ring)

private lemma signed_target_facts {c : Counterexample4 G}
    {a : Multiplicative (Fin 3 → ZMod 3) →* ↥c.L}
    (ha_order : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
      orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3)
    {w : Fin 3 → ZMod 3} (hw : w = ![1, 0, 0] ∨ w = ![1, 1, 0] ∨ w = ![1, 1, 1]) :
    (Subgroup.zpowers ((a (Multiplicative.ofAdd w) : ↥c.L) : G) ≤
        Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 0, 0]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![0, 1, 0]) : ↥c.L) : G) ∨
      Subgroup.zpowers ((a (Multiplicative.ofAdd w) : ↥c.L) : G) ≤
        Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, 1]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![0, 0, 1]) : ↥c.L) : G)) ∧
      Nat.card (Subgroup.zpowers ((a (Multiplicative.ofAdd w) : ↥c.L) : G)) = 3 := by
  rcases hw with rfl | rfl | rfl
  · refine ⟨Or.inl le_sup_left, ?_⟩
    rw [Nat.card_zpowers]
    exact ha_order ![1, 0, 0] (by intro hv; have := congrFun hv 0; simp at this)
  · refine ⟨Or.inl ?_, ?_⟩
    · rw [show (![1, 1, 0] : Fin 3 → ZMod 3) = ![1, 0, 0] + ![0, 1, 0] from by
        funext i; fin_cases i <;> rfl, ofAdd_add, map_mul]
      exact Subgroup.zpowers_le.mpr (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    · rw [Nat.card_zpowers]
      exact ha_order ![1, 1, 0] (by intro hv; have := congrFun hv 0; simp at this)
  · refine ⟨Or.inr le_sup_left, ?_⟩
    rw [Nat.card_zpowers]
    exact ha_order ![1, 1, 1] (by intro hv; have := congrFun hv 0; simp at this)

private lemma signed_point_in_plane {c : Counterexample4 G} (h : Case811Sylow c)
    {c₀ : Multiplicative (Fin 3 → ZMod 3) →* c.Lbar}
    {a : Multiplicative (Fin 3 → ZMod 3) →* ↥c.L}
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hXinj : Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
      (h.A.subgroupOf c.L).subtype))
    (hc₀ : IsSignedCoords h.Abar c₀)
    (ha_order : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
      orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3)
    {X : Subgroup G} (hXA : X ≤ h.A) (hXcard : Nat.card X = 3) :
    ∃ (g : G) (Z : Subgroup G), g ∈ c.S.M ∧ X.map (MulAut.conj g).toMonoidHom = Z ∧
      (Z ≤ Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 0, 0]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![0, 1, 0]) : ↥c.L) : G) ∨
        Z ≤ Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, 1]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![0, 0, 1]) : ↥c.L) : G)) ∧
      Nat.card Z = 3 := by
  obtain ⟨v, -, havne, hvne, -, hXgen⟩ := exists_gen_coords h ha_range hXA hXcard
  obtain ⟨σ, ε, hε, hclass⟩ := signed_point_reps (Multiplicative.toAdd v)
    (by simpa [toAdd_eq_zero] using hvne)
  let φ : Multiplicative (Fin 3 → ZMod 3) → Multiplicative (Fin 3 → ZMod 3) :=
    fun w => Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd w (σ i)
  obtain ⟨n, hnform⟩ := hc₀.2.2.2 σ ε hε
  obtain ⟨g, -, -, hconj⟩ := exists_conj_of_coords h a ha_range ha_apply hXinj φ
    (h.mem_normalizer_of_coords hc₀.2.1 hnform) hnform
  have hconjX : X.map (MulAut.conj (g : G)).toMonoidHom =
      Subgroup.zpowers ((a (φ v) : ↥c.L) : G) := by
    rw [hXgen, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (by simpa [MulAut.conj_apply] using hconj v)
  have hw : (fun i => ε i * Multiplicative.toAdd v (σ i)) = ![1, 0, 0] ∨
      (fun i => ε i * Multiplicative.toAdd v (σ i)) = ![1, 1, 0] ∨
      (fun i => ε i * Multiplicative.toAdd v (σ i)) = ![1, 1, 1] := by
    rcases hclass with h | h | h
    · left; funext i; exact h i
    · right; left; funext i; exact h i
    · right; right; funext i; exact h i
  have hφw : φ v = Multiplicative.ofAdd (fun i => ε i * Multiplicative.toAdd v (σ i)) := rfl
  obtain ⟨htarget_le, htarget_card⟩ := signed_target_facts ha_order hw
  refine ⟨(g : G), Subgroup.zpowers ((a (φ v) : ↥c.L) : G), c.hyp81.1 g.2, hconjX, ?_, ?_⟩
  · rw [hφw]; exact htarget_le
  · rw [hφw]; exact htarget_card

private lemma false_of_signedCoords {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) (hK6r : K6r) {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (hfam : fam ≠ .l4)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M r) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hr2 : r ≠ 2 := by omega
  obtain ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_inj, ha_memA, ha_order⟩ :=
    signed_coords_setup h hK6c hlie hfam
  have hK6r' := hK6r c.Lbar fam r f hlie hr5 (by
    intro hconj
    exact hfam hconj.1) h.Abar h.isElemAbelian_Abar h.card_Abar
  have hdetA : (![0, 1, 0] : Fin 3 → ZMod 3) 1 * (![1, 0, 0] : Fin 3 → ZMod 3) 0 ≠
      (![0, 1, 0] : Fin 3 → ZMod 3) 0 * (![1, 0, 0] : Fin 3 → ZMod 3) 1 := by simp
  have hdetB : (![0, 0, 1] : Fin 3 → ZMod 3) 2 * (![1, 1, 1] : Fin 3 → ZMod 3) 0 ≠
      (![0, 0, 1] : Fin 3 → ZMod 3) 0 * (![1, 1, 1] : Fin 3 → ZMod 3) 2 := by simp
  have hEa_pts := plane_facts_of_zpowers h hr h76 hr2 hK6r'.1 ha_apply
    (v₁ := Multiplicative.ofAdd ![1, 0, 0]) (v₂ := Multiplicative.ofAdd ![0, 1, 0])
    (ha_memA _) (ha_memA _)
    (ha_order ![1, 0, 0] (by intro hv; have := congrFun hv 0; simp at this))
    (ha_order ![0, 1, 0] (by intro hv; have := congrFun hv 1; simp at this))
    (signed_not_mem_zpowers ha_inj (v := ![0, 1, 0]) (w := ![1, 0, 0]) (i := 1) (j := 0) hdetA)
    (by simpa only [CFSG.SectionRank.pRank_coe_eq_openPRank] using
      (hK6r'.2.1 hfam c₀ hc₀).1)
  have hEb_pts := plane_facts_of_zpowers h hr h76 hr2 hK6r'.1 ha_apply
    (v₁ := Multiplicative.ofAdd ![1, 1, 1]) (v₂ := Multiplicative.ofAdd ![0, 0, 1])
    (ha_memA _) (ha_memA _)
    (ha_order ![1, 1, 1] (by intro hv; have := congrFun hv 0; simp at this))
    (ha_order ![0, 0, 1] (by intro hv; have := congrFun hv 2; simp at this))
    (signed_not_mem_zpowers ha_inj (v := ![0, 0, 1]) (w := ![1, 1, 1]) (i := 2) (j := 0) hdetB)
    (by simpa only [CFSG.SectionRank.pRank_coe_eq_openPRank] using
      (hK6r'.2.1 hfam c₀ hc₀).2)
  refine h.false_of_forall_normalizer_le hr ?_
  intro X hXA hXcard
  obtain ⟨g, Z, hgM, hXZ, hZle | hZle, hZcard⟩ :=
    signed_point_in_plane h ha_range ha_apply hXinj hc₀ ha_order hXA hXcard
  · exact normalizer_facts_of_map_conj_eq hgM hXZ (hEa_pts Z hZle hZcard)
  · exact normalizer_facts_of_map_conj_eq hgM hXZ (hEb_pts Z hZle hZcard)

theorem sumZero_coords_setup {c : Counterexample4 G} (h : Case811Sylow c) (hK6c : K6c)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f) (hfam : fam = .l4) :
    ∃ (c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar)
      (a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L),
      IsSumZeroCoords h.Abar c₀ ∧
      a.range = h.A.subgroupOf c.L ∧
      (∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v) ∧
      Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
        (h.A.subgroupOf c.L).subtype) ∧
      (∀ v, a v = 1 ↔ c₀ v = 1) ∧
      (∀ v, (a v : G) ∈ h.A) ∧
      (∀ v : Fin 4 → ZMod 3, (¬ ∃ d : ZMod 3, v = fun _ => d) →
        orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, hc₀⟩ := (hK6c c.Lbar fam r f hlie h.Abar h.isElemAbelian_Abar h.card_Abar).1 hfam
  obtain ⟨a, ha_range, ha_apply, hXinj, ha_memA⟩ := exists_coords_lift h hc₀.1
  have ha_memX : ∀ v, a v ∈ h.A.subgroupOf c.L := by
    intro v
    have hv : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hv
  have ha_eq_one_iff : ∀ v, a v = 1 ↔ c₀ v = 1 := by
    intro v
    constructor
    · intro hv
      rw [← ha_apply v, hv, map_one]
    · intro hv
      have h : (⟨a v, ha_memX v⟩ : h.A.subgroupOf c.L) =
          ⟨1, (h.A.subgroupOf c.L).one_mem⟩ := hXinj (by
        show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) =
          QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (1 : ↥c.L)
        rw [ha_apply v, hv, map_one])
      exact congrArg Subtype.val h
  have ha_order : ∀ v : Fin 4 → ZMod 3, (¬ ∃ d : ZMod 3, v = fun _ => d) →
      orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3 := by
    intro v hv
    have hvne : (Multiplicative.ofAdd v : Multiplicative (Fin 4 → ZMod 3)) ≠ 1 := by
      intro hone
      apply hv
      have h1 : c₀ (Multiplicative.ofAdd v) = 1 := by
        rw [← ha_apply (Multiplicative.ofAdd v), hone]
        simp
      exact (hc₀.2.1 (Multiplicative.ofAdd v)).mp h1
    refine orderOf_eq_prime ?_ ?_
    · have h : ((a (Multiplicative.ofAdd v) : ↥c.L) : G) ^ 3 =
          ((a ((Multiplicative.ofAdd v) ^ 3) : ↥c.L) : G) := by
        rw [map_pow]
        rfl
      rw [h, ofAdd_pow_three v, map_one]
      rfl
    · intro h1
      exact hv ((hc₀.2.1 (Multiplicative.ofAdd v)).mp
        ((ha_eq_one_iff (Multiplicative.ofAdd v)).mp (Subtype.ext h1)))
  exact ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_eq_one_iff, ha_memA, ha_order⟩

private lemma sumZero_not_mem_zpowers {c : Counterexample4 G} (h : Case811Sylow c)
    {c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar}
    {a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L}
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hc₀ : IsSumZeroCoords h.Abar c₀) :
    ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) ∉
      Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkL : a (Multiplicative.ofAdd ![1, -1, 0, 0]) =
      (a (Multiplicative.ofAdd ![1, 1, -1, -1])) ^ k := by
    apply Subtype.ext
    simpa using hk.symm
  have haeq : a (Multiplicative.ofAdd ![1, -1, 0, 0]) =
      a (Multiplicative.ofAdd (k • ![1, 1, -1, -1])) := by
    rw [ofAdd_zsmul, map_zpow]
    exact hkL
  have hc : c₀ (Multiplicative.ofAdd ![1, -1, 0, 0]) =
      c₀ (Multiplicative.ofAdd (k • ![1, 1, -1, -1])) := by
    rw [← ha_apply (Multiplicative.ofAdd ![1, -1, 0, 0]),
      ← ha_apply (Multiplicative.ofAdd (k • ![1, 1, -1, -1])), haeq]
  have hc1 : c₀ (Multiplicative.ofAdd ![1, -1, 0, 0] /
      Multiplicative.ofAdd (k • ![1, 1, -1, -1])) = 1 := by
    rw [map_div, hc]
    exact div_self' _
  obtain ⟨d, hd⟩ := (hc₀.2.1 (Multiplicative.ofAdd ![1, -1, 0, 0] /
    Multiplicative.ofAdd (k • ![1, 1, -1, -1]))).mp hc1
  rw [toAdd_div, toAdd_ofAdd, toAdd_ofAdd, zsmul_eq_mul] at hd
  have h0 := congrFun hd 0
  have h1 := congrFun hd 1
  simp at h0 h1
  have hk' : (1 : ZMod 3) = -1 := by
    calc (1 : ZMod 3) = (1 - (k : ZMod 3)) + (k : ZMod 3) := by ring
      _ = (-1 - (k : ZMod 3)) + (k : ZMod 3) := by rw [h0.trans h1.symm]
      _ = -1 := by ring
  exact (of_decide_eq_true rfl : (1 : ZMod 3) ≠ -1) hk'

private lemma sumZero_target_mem {c : Counterexample4 G}
    {a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L}
    (ha_const_one : ∀ d : ZMod 3, a (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1)
    {t : ZMod 3} (ht : t ≠ 0) {w : Fin 4 → ZMod 3}
    (hw : w = ![1, 1, -1, -1] ∨ w = ![1, -1, 0, 0] ∨ w = ![2, 0, 2, 2]) (d : ZMod 3) :
    ((a (Multiplicative.ofAdd (fun i => t * w i + d)) : ↥c.L) : G) ∈
      Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) ⊔
        Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) := by
  have hz3_eq : (![2, 0, 2, 2] : Fin 4 → ZMod 3) = ![1, 1, -1, -1] + ![1, -1, 0, 0] :=
    sumZero_target_add
  have hzmem : ∀ w : Fin 4 → ZMod 3, w = ![1, 1, -1, -1] ∨ w = ![1, -1, 0, 0] ∨
      w = ![2, 0, 2, 2] →
      ((a (Multiplicative.ofAdd w) : ↥c.L) : G) ∈
        Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [hz3_eq, ofAdd_add, map_mul]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have ha_at : ∀ w : Fin 4 → ZMod 3, (w = ![1, 1, -1, -1] ∨ w = ![1, -1, 0, 0] ∨
      w = ![2, 0, 2, 2]) →
      ((a (Multiplicative.ofAdd (t • w)) : ↥c.L) : G) ∈
        Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) := by
    intro w hw
    have ht12 : t = 1 ∨ t = 2 := by
      fin_cases t
      · exact absurd rfl ht
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ht12 with rfl | rfl
    · simpa using hzmem w hw
    · have h2 : (2 : ZMod 3) • w = w + w := by
        funext i; rw [Pi.smul_apply, Pi.add_apply, two_smul]
      rw [h2, ofAdd_add, map_mul]
      exact Subgroup.mul_mem _ (hzmem w hw) (hzmem w hw)
  have hdec : (fun i : Fin 4 => t * w i + d) = t • w + fun _ : Fin 4 => d := by
    funext i
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hdec, ofAdd_add, map_mul, ha_const_one d, mul_one]
  exact ha_at w hw

private lemma sumZero_target_le {c : Counterexample4 G}
    {a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L}
    (ha_const_one : ∀ d : ZMod 3, a (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1)
    {v : Fin 4 → ZMod 3} {σ : Equiv.Perm (Fin 4)} {t d : ZMod 3} (ht : t ≠ 0)
    (hclass : (∀ i, Multiplicative.toAdd v (σ i) = t * ![1, 1, -1, -1] i + d) ∨
      (∀ i, Multiplicative.toAdd v (σ i) = t * ![1, -1, 0, 0] i + d) ∨
      (∀ i, Multiplicative.toAdd v (σ i) = t * ![2, 0, 2, 2] i + d)) :
    Subgroup.zpowers ((a (Multiplicative.ofAdd (fun i => Multiplicative.toAdd v (σ i))) :
        ↥c.L) : G) ≤
      Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) ⊔
        Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) := by
  rcases hclass with h | h | h
  · rw [show Multiplicative.ofAdd (fun i => Multiplicative.toAdd v (σ i)) =
        Multiplicative.ofAdd (fun i => t * ![1, 1, -1, -1] i + d) from
      congrArg Multiplicative.ofAdd (funext h)]
    exact Subgroup.zpowers_le.mpr (sumZero_target_mem ha_const_one ht (Or.inl rfl) d)
  · rw [show Multiplicative.ofAdd (fun i => Multiplicative.toAdd v (σ i)) =
        Multiplicative.ofAdd (fun i => t * ![1, -1, 0, 0] i + d) from
      congrArg Multiplicative.ofAdd (funext h)]
    exact Subgroup.zpowers_le.mpr (sumZero_target_mem ha_const_one ht (Or.inr (Or.inl rfl)) d)
  · rw [show Multiplicative.ofAdd (fun i => Multiplicative.toAdd v (σ i)) =
        Multiplicative.ofAdd (fun i => t * ![2, 0, 2, 2] i + d) from
      congrArg Multiplicative.ofAdd (funext h)]
    exact Subgroup.zpowers_le.mpr
      (sumZero_target_mem ha_const_one ht (Or.inr (Or.inr rfl)) d)

private lemma sumZero_point_in_plane {c : Counterexample4 G} (h : Case811Sylow c)
    {c₀ : Multiplicative (Fin 4 → ZMod 3) →* c.Lbar}
    {a : Multiplicative (Fin 4 → ZMod 3) →* ↥c.L}
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hXinj : Function.Injective ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
      (h.A.subgroupOf c.L).subtype))
    (hc₀ : IsSumZeroCoords h.Abar c₀)
    (ha_eq_one_iff : ∀ v, a v = 1 ↔ c₀ v = 1)
    (ha_memA : ∀ v, (a v : G) ∈ h.A)
    {X : Subgroup G} (hXA : X ≤ h.A) (hXcard : Nat.card X = 3) :
    ∃ (g : G) (Z : Subgroup G), g ∈ c.S.M ∧ X.map (MulAut.conj g).toMonoidHom = Z ∧
      Z ≤ Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) ⊔
          Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) ∧
      Nat.card Z = 3 := by
  obtain ⟨v, -, havne, hvne, -, hXgen⟩ := exists_gen_coords h ha_range hXA hXcard
  have hvnc : ¬ ∃ d : ZMod 3, Multiplicative.toAdd v = fun _ => d := by
    rintro ⟨d, hd⟩
    apply havne
    have hav : a v = 1 := by
      rw [ha_eq_one_iff, ← ofAdd_toAdd v, hd]
      exact (hc₀.2.1 (Multiplicative.ofAdd (fun _ : Fin 4 => d))).2 ⟨d, rfl⟩
    exact congrArg (fun z : ↥c.L => (z : G)) hav
  obtain ⟨σ, t, d, ht, hclass⟩ := sumZero_point_reps (Multiplicative.toAdd v) hvnc
  let φ : Multiplicative (Fin 4 → ZMod 3) → Multiplicative (Fin 4 → ZMod 3) :=
    fun w => Multiplicative.ofAdd fun i => Multiplicative.toAdd w (σ i)
  obtain ⟨n, hnform⟩ := hc₀.2.2.2 σ
  obtain ⟨g, -, -, hconj⟩ := exists_conj_of_coords h a ha_range ha_apply hXinj φ
    (h.mem_normalizer_of_coords hc₀.1 hnform) hnform
  have hconjX : X.map (MulAut.conj (g : G)).toMonoidHom =
      Subgroup.zpowers ((a (φ v) : ↥c.L) : G) := by
    rw [hXgen, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (by simpa [MulAut.conj_apply] using hconj v)
  have ha_const_one : ∀ d : ZMod 3, a (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1 := by
    intro d
    rw [ha_eq_one_iff]
    exact (hc₀.2.1 (Multiplicative.ofAdd (fun _ : Fin 4 => d))).2 ⟨d, rfl⟩
  have htarget_le := sumZero_target_le ha_const_one ht hclass
  have htarget_ne : ((a (φ v) : ↥c.L) : G) ≠ 1 := by
    intro h1
    apply havne
    have h := hconj v
    rw [h1] at h
    calc ((a v : ↥c.L) : G) = (g : G)⁻¹ *
          ((g : G) * ((a v : ↥c.L) : G) * (g : G)⁻¹) * (g : G) := by group
      _ = 1 := by rw [h]; group
  have hEcA : Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, 1, -1, -1]) : ↥c.L) : G) ⊔
      Subgroup.zpowers ((a (Multiplicative.ofAdd ![1, -1, 0, 0]) : ↥c.L) : G) ≤ h.A :=
    sup_le (Subgroup.zpowers_le.mpr (ha_memA _)) (Subgroup.zpowers_le.mpr (ha_memA _))
  have htarget_card : Nat.card (Subgroup.zpowers ((a (φ v) : ↥c.L) : G)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h.elemAbelian.2 _ (hEcA (htarget_le (Subgroup.mem_zpowers _))))
      htarget_ne
  exact ⟨(g : G), Subgroup.zpowers ((a (φ v) : ↥c.L) : G), c.hyp81.1 g.2, hconjX,
    htarget_le, htarget_card⟩

private lemma false_of_sumZeroCoords {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) (hK6r : K6r) {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (hfam : fam = .l4) (hf : f ≠ 1)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M r) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hr2 : r ≠ 2 := by omega
  obtain ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_eq_one_iff, ha_memA, ha_order⟩ :=
    sumZero_coords_setup h hK6c hlie hfam
  have hK6r' := hK6r c.Lbar fam r f hlie hr5 (by
    intro hconj
    exact hf hconj.2) h.Abar h.isElemAbelian_Abar h.card_Abar
  have hz1 : ¬ ∃ d : ZMod 3, (![1, 1, -1, -1] : Fin 4 → ZMod 3) = fun _ => d := by
    rintro ⟨d, hd⟩
    have h0 := congrFun hd 0
    have h2 := congrFun hd 2
    exact (of_decide_eq_true rfl : (1 : ZMod 3) ≠ -1) (h0.trans h2.symm)
  have hz2 : ¬ ∃ d : ZMod 3, (![1, -1, 0, 0] : Fin 4 → ZMod 3) = fun _ => d := by
    rintro ⟨d, hd⟩
    have h0 := congrFun hd 0
    have h1 := congrFun hd 1
    exact (of_decide_eq_true rfl : (1 : ZMod 3) ≠ -1) (h0.trans h1.symm)
  have hEc_pts := plane_facts_of_zpowers h hr h76 hr2 hK6r'.1 ha_apply
    (v₁ := Multiplicative.ofAdd ![1, 1, -1, -1]) (v₂ := Multiplicative.ofAdd ![1, -1, 0, 0])
    (ha_memA _) (ha_memA _) (ha_order ![1, 1, -1, -1] hz1) (ha_order ![1, -1, 0, 0] hz2)
    (sumZero_not_mem_zpowers h ha_apply hc₀)
    (by simpa only [CFSG.SectionRank.pRank_coe_eq_openPRank] using hK6r'.2.2 hfam c₀ hc₀)
  refine h.false_of_forall_normalizer_le hr ?_
  intro X hXA hXcard
  obtain ⟨g, Z, hgM, hXZ, hZle, hZcard⟩ :=
    sumZero_point_in_plane h ha_range ha_apply hXinj hc₀ ha_eq_one_iff ha_memA hXA hXcard
  exact normalizer_facts_of_map_conj_eq hgM hXZ (hEc_pts Z hZle hZcard)


private lemma l4_not_mem_L {c : Counterexample4 G} {r : ℕ}
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (hZr : ¬ r ∣ Nat.card (Subgroup.center c.Lbar)) {y : G} (hyM : y ∈ c.S.M)
    (hyord : orderOf y = r)
    (hyC : y ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) : y ∉ c.L := by
  classical
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  intro hyLmem
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hyC
  have hφy : CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L ⟨y, hyM⟩ = 1 := by
    rw [show (⟨y, hyM⟩ : ↥c.S.M) = a from Subtype.ext hay.symm]
    exact MonoidHom.mem_ker.mp ha
  let z : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨y, hyLmem⟩
  have hconj : MulAut.conj z =
      CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L ⟨y, hyM⟩ := by
    rw [show z = QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨y, hyLmem⟩ from rfl]
    exact (CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L c.S.M c.le_normalizer_L
      hyM hyLmem).symm
  have hz1 : MulAut.conj z = 1 := hconj.trans hφy
  have hz_center : z ∈ Subgroup.center c.Lbar := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h := congrArg (fun f : MulAut c.Lbar => f w) hz1
    simp only [MulAut.one_apply, MulAut.conj_apply] at h
    calc w * z = (z * w * z⁻¹) * z := by rw [h]
      _ = z * w := by group
  have hz_pow : z ^ r = 1 := by
    change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨y, hyLmem⟩) ^ r = 1
    rw [← map_pow]
    have hyr : (⟨y, hyLmem⟩ : ↥c.L) ^ r = 1 := by
      apply Subtype.ext
      rw [← hyord]
      exact pow_orderOf_eq_one y
    rw [hyr, map_one]
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hmemO : (⟨y, hyLmem⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_one_iff]
      exact hz1
    have hdvdO : r ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) := by
      have hord : orderOf (⟨y, hyLmem⟩ : ↥c.L) = r := by
        rw [Subgroup.orderOf_mk, hyord]
      have h := orderOf_dvd_natCard
        (⟨⟨y, hyLmem⟩, hmemO⟩ : ↥(CFSG.Open.pCore 2 ↥c.L))
      rw [Subgroup.orderOf_mk, hord] at h
      exact h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (p := 2) (q := r) (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
      hr.1.1 (by omega) hdvdO
  have hz_ord : orderOf z = r := orderOf_eq_prime hz_pow hz_ne
  have hdvd : r ∣ Nat.card (Subgroup.center c.Lbar) := by
    have h : Nat.card (Subgroup.zpowers z) ∣ Nat.card (Subgroup.center c.Lbar) :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz_center)
    rwa [Nat.card_zpowers, hz_ord] at h
  exact hZr hdvd

private lemma l4_commutator_le_pCore {c : Counterexample4 G} {y : G}
    (hyC : y ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) :
    ⁅c.L, Subgroup.zpowers y⁆ ≤ CFSG.Open.pCoreOf 2 c.L := by
  classical
  have hRM : Subgroup.zpowers y ≤ c.S.M :=
    (Subgroup.zpowers_le.mpr hyC).trans (Subgroup.map_subtype_le _)
  exact (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L c.S.M
    (Subgroup.zpowers y) c.le_normalizer_L hRM).mp (Subgroup.zpowers_le.mpr hyC)

private lemma l4_normalizes_sup_pCore {c : Counterexample4 G} (h : Case811Sylow c) {y : G}
    (hyM : y ∈ c.S.M)
    (hyC : y ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) :
    y ∈ Subgroup.normalizer ((h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G) : Set G) := by
  classical
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let D : Subgroup G := h.A ⊔ O
  have hO_le_L : O ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hOD : O ≤ D := le_sup_right
  have hcommLR : ⁅c.L, Subgroup.zpowers y⁆ ≤ O := l4_commutator_le_pCore hyC
  have hyNO : y ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L (c.le_normalizer_L hyM)
  have hmapA : h.A.map (MulAut.conj y).toMonoidHom ≤ D := by
    rintro _ ⟨a, ha, rfl⟩
    have hcomm : ⁅y, a⁆ ∈ O := by
      have hcl := (Subgroup.commutator_le.mp
        (Subgroup.commutator_comm (H₁ := Subgroup.zpowers y) (H₂ := c.L) ▸ hcommLR))
      exact hcl y (Subgroup.mem_zpowers y) a (h.A_le.trans h.P_le_L ha)
    have hya : y * a * y⁻¹ = ⁅y, a⁆ * a := by
      rw [commutatorElement_def]; group
    change y * a * y⁻¹ ∈ D
    rw [hya]
    exact D.mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left ha)
  rw [show (h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G) = D from rfl,
    Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [show D = h.A ⊔ O from rfl, Subgroup.map_sup]
    exact sup_le hmapA (by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hyNO]; exact hOD)
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]

private lemma l4_isSylow_A_sup_pCore {c : Counterexample4 G} (h : Case811Sylow c) :
    CFSG.ABGLocalTools.IsSylowOf 3 h.A (h.A ⊔ CFSG.Open.pCoreOf 2 c.L) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let D : Subgroup G := h.A ⊔ O
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hAnormO : h.A ≤ Subgroup.normalizer (O : Set G) :=
    (h.A_le.trans h.P_le_L).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L)
  have hdisjAO : Disjoint h.A O :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) h.A O h.elemAbelian.isPGroup hO2
  have hAD : h.A ≤ D := le_sup_left
  have hDcard' : Nat.card ↥(O ⊔ h.A : Subgroup G) = Nat.card O * Nat.card h.A :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O h.A hAnormO hdisjAO.symm
  have hDcard : Nat.card D = Nat.card h.A * Nat.card O := by
    rw [show D = h.A ⊔ O from rfl, sup_comm, hDcard', mul_comm]
  rw [show (h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G) = D from rfl,
    CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hAD, h.elemAbelian.isPGroup, ?_⟩
  have hrel : h.A.relIndex D = Nat.card O := by
    have hrel := Subgroup.relIndex_mul_card h.A D
    rw [inf_eq_left.mpr hAD, h.card_A] at hrel
    rw [hDcard, h.card_A] at hrel
    have hrel' : 27 * h.A.relIndex D = 27 * Nat.card O := by
      rw [mul_comm 27, hrel, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hrel'
  rw [hrel]
  exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2 Nat.prime_three (by norm_num)

private lemma l4_not_dvd_card_sup_pCore {c : Counterexample4 G} (h : Case811Sylow c) {r : ℕ}
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M) :
    ¬ r ∣ Nat.card (h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G) := by
  classical
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let D : Subgroup G := h.A ⊔ O
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hAnormO : h.A ≤ Subgroup.normalizer (O : Set G) :=
    (h.A_le.trans h.P_le_L).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L)
  have hdisjAO : Disjoint h.A O :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) h.A O h.elemAbelian.isPGroup hO2
  have hDcard' : Nat.card ↥(O ⊔ h.A : Subgroup G) = Nat.card O * Nat.card h.A :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O h.A hAnormO hdisjAO.symm
  have hDcard : Nat.card D = Nat.card h.A * Nat.card O := by
    rw [show D = h.A ⊔ O from rfl, sup_comm, hDcard', mul_comm]
  have h27 : ¬ r ∣ Nat.card h.A := by
    rw [h.card_A]
    intro hdvd
    have hdvd' : r ∣ 3 ^ 3 := by simpa using hdvd
    have h3 : r ∣ 3 := hr.1.1.dvd_of_dvd_pow hdvd'
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hOnot : ¬ r ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2 hr.1.1 (by omega)
  rw [show (h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G) = D from rfl, hDcard]
  exact fun hdvd => (hr.1.1.dvd_mul.mp hdvd).elim h27 hOnot

private lemma l4_exists_sylow_conj {c : Counterexample4 G} (h : Case811Sylow c) {r : ℕ}
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M) {y : G} (hyord : orderOf y = r)
    (hyND : y ∈ Subgroup.normalizer ((h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G) : Set G)) :
    ∃ (S : Sylow 3 ↥(h.A ⊔ CFSG.Open.pCoreOf 2 c.L)) (d : G),
      d ∈ h.A ⊔ CFSG.Open.pCoreOf 2 c.L ∧
      ((S : Subgroup ↥(h.A ⊔ CFSG.Open.pCoreOf 2 c.L)).map
        (h.A ⊔ CFSG.Open.pCoreOf 2 c.L).subtype : Subgroup G) =
        h.A.map (MulAut.conj d).toMonoidHom ∧
      y ∈ Subgroup.normalizer ((((S : Subgroup ↥(h.A ⊔ CFSG.Open.pCoreOf 2 c.L)).map
        (h.A ⊔ CFSG.Open.pCoreOf 2 c.L).subtype : Subgroup G)) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  let D : Subgroup G := h.A ⊔ CFSG.Open.pCoreOf 2 c.L
  have hRy : IsPGroup r (Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hyord]
    exact ⟨1, by rw [pow_one]⟩
  have hDnot : ¬ r ∣ Nat.card D := l4_not_dvd_card_sup_pCore h hr
  obtain ⟨S, hS_norm⟩ :=
    CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup
      hr.1.1 Nat.prime_three hRy (Subgroup.zpowers_le.mpr hyND) hDnot
  let Ssub : Subgroup G := (S : Subgroup ↥D).map D.subtype
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 Ssub D := ⟨S, rfl⟩
  obtain ⟨d, hdD, hdconj⟩ := (l4_isSylow_A_sup_pCore h).exists_mem_conj hS_sylow
  have hS_eq : Ssub = h.A.map (MulAut.conj d).toMonoidHom := by
    ext x
    rw [hdconj x]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨d⁻¹ * x * d, hx, by
        simp [MulAut.conj_apply]; group⟩
    · rintro ⟨a, ha, rfl⟩
      have h : d⁻¹ * (MulAut.conj d).toMonoidHom a * d = a := by
        simpa [MulAut.conj_apply] using (by group : d⁻¹ * (d * a * d⁻¹) * d = a)
      rwa [h]
  exact ⟨S, d, hdD, hS_eq, by simpa [Ssub] using hS_norm (Subgroup.mem_zpowers y)⟩

private lemma l4_decompose_sylow_conj {c : Counterexample4 G} (h : Case811Sylow c)
    {d : G} (hdD : d ∈ (h.A ⊔ CFSG.Open.pCoreOf 2 c.L : Subgroup G)) :
    ∃ o : ↥c.L, (o : G) ∈ CFSG.Open.pCoreOf 2 c.L ∧
      h.A.map (MulAut.conj d).toMonoidHom =
        h.A.map (MulAut.conj (o : G)).toMonoidHom := by
  classical
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  let D : Subgroup G := h.A ⊔ O
  have hO_le_L : O ≤ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  have hDL : D ≤ c.L := sup_le (h.A_le.trans h.P_le_L) hO_le_L
  let AL : Subgroup ↥c.L := h.A.subgroupOf c.L
  let OL : Subgroup ↥c.L := O.subgroupOf c.L
  have hdL : d ∈ c.L := hDL hdD
  have hDsub : D.subgroupOf c.L = AL ⊔ OL := by
    rw [show D = h.A ⊔ O from rfl,
      Subgroup.subgroupOf_sup (h.A_le.trans h.P_le_L) hO_le_L]
  haveI : OL.Normal := by
    change (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L |>.Normal
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  have hdmem : (⟨d, hdL⟩ : ↥c.L) ∈ OL ⊔ AL := by
    rw [sup_comm, ← hDsub]
    exact Subgroup.mem_subgroupOf.mpr hdD
  obtain ⟨oL, hoL, aL, haL, hdecomp⟩ := Subgroup.mem_sup_of_normal_left.mp hdmem
  have haA : (aL : G) ∈ h.A := Subgroup.mem_subgroupOf.mp haL
  have hoO : (oL : G) ∈ O := Subgroup.mem_subgroupOf.mp hoL
  have hdecompG : (oL : G) * (aL : G) = d := congrArg (fun z : ↥c.L => (z : G)) hdecomp
  refine ⟨oL, hoO, ?_⟩
  rw [← hdecompG, map_mul]
  change Subgroup.map ((MulAut.conj (oL : G)).toMonoidHom.comp
    (MulAut.conj (aL : G)).toMonoidHom) h.A =
    Subgroup.map (MulAut.conj (oL : G)).toMonoidHom h.A
  rw [← Subgroup.map_map]
  congr 1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haA)

private lemma l4_y'_props {c : Counterexample4 G} {r : ℕ}
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M) {y o y' : G} (hyM : y ∈ c.S.M)
    (hyord : orderOf y = r) (hyL : y ∉ c.L) (hoL : o ∈ c.L) (hy' : y' = o⁻¹ * y * o)
    (hyC : y ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) :
    y' ∈ c.S.M ∧ orderOf y' = r ∧ y' ∉ c.L ∧
      y' ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype := by
  classical
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hy'M : y' ∈ c.S.M := by
    rw [hy']
    exact c.S.M.mul_mem (c.S.M.mul_mem (c.S.M.inv_mem (c.hyp81.1 hoL)) hyM) (c.hyp81.1 hoL)
  have hy'ord : orderOf y' = r := by
    have h := (MulAut.conj o⁻¹).orderOf_eq y
    rw [hy']
    simpa [MulAut.conj_apply] using h.trans hyord
  have hy'L : y' ∉ c.L := by
    intro hy'Lmem
    apply hyL
    have h : y = o * y' * o⁻¹ := by rw [hy']; group
    rw [h]
    exact c.L.mul_mem (c.L.mul_mem hoL hy'Lmem) (c.L.inv_mem hoL)
  have hy'C : y' ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype := by
    rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L c.S.M c.le_normalizer_L]
    refine ⟨hy'M, ?_⟩
    intro x hxL
    have hycomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L c.S.M
      c.le_normalizer_L).mp hyC
    have hx' : o * x * o⁻¹ ∈ c.L := c.L.mul_mem (c.L.mul_mem hoL hxL) (c.L.inv_mem hoL)
    have hmem := hycomm.2 (o * x * o⁻¹) hx'
    have hconj : y' * x * y'⁻¹ * x⁻¹ =
        o⁻¹ * (y * (o * x * o⁻¹) * y⁻¹ * (o * x * o⁻¹)⁻¹) * o := by
      rw [hy']; group
    rw [hconj]
    have hoNO : o ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
        (c.le_normalizer_L (c.hyp81.1 hoL))
    simpa using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 c.L : Set G)).inv_mem hoNO) _).mp hmem
  exact ⟨hy'M, hy'ord, hy'L, hy'C⟩

private lemma l4_y'_centralizes_A {c : Counterexample4 G} (h : Case811Sylow c)
    {o y y' : G} (hy' : y' = o⁻¹ * y * o)
    (hyNS : y ∈ Subgroup.normalizer
      ((h.A.map (MulAut.conj o).toMonoidHom : Subgroup G) : Set G))
    (hy'C : y' ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) :
    y' ∈ Subgroup.centralizer (h.A : Set G) := by
  classical
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hdisjAO : Disjoint h.A O :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) h.A O h.elemAbelian.isPGroup hO2
  have hy'NA : y' ∈ Subgroup.normalizer (h.A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      have hoa : o * a * o⁻¹ ∈ h.A.map (MulAut.conj o).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hyoa := (Subgroup.mem_normalizer_iff.mp hyNS _).mp hoa
      obtain ⟨b, hb, hb_eq⟩ := Subgroup.mem_map.mp hyoa
      have heq : y' * a * y'⁻¹ = b := by
        rw [hy']
        calc o⁻¹ * y * o * a * (o⁻¹ * y * o)⁻¹
            = o⁻¹ * (y * (o * a * o⁻¹) * y⁻¹) * o := by group
          _ = o⁻¹ * (o * b * o⁻¹) * o := by rw [← hb_eq]; simp [MulAut.conj_apply]
          _ = b := by group
      change y' * a * y'⁻¹ ∈ h.A
      rw [heq]
      exact hb
    · rw [Subgroup.card_map_of_injective (MulAut.conj y').injective]
  have hy'A_comm : ∀ a ∈ h.A, y' * a * y'⁻¹ * a⁻¹ ∈ h.A := by
    intro a ha
    exact h.A.mul_mem ((Subgroup.mem_normalizer_iff.mp hy'NA a).mp ha) (h.A.inv_mem ha)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hcO : y' * a * y'⁻¹ * a⁻¹ ∈ O :=
    ((CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L c.S.M c.le_normalizer_L).mp
      hy'C).2 a (h.A_le.trans h.P_le_L ha)
  have hcA := hy'A_comm a ha
  have hcbot : y' * a * y'⁻¹ * a⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hdisjAO.eq_bot]
    exact ⟨hcA, hcO⟩
  have hc1 : y' * a * y'⁻¹ * a⁻¹ = 1 := by simpa using hcbot
  have h : y' * a * y'⁻¹ = a := by
    calc y' * a * y'⁻¹ = (y' * a * y'⁻¹ * a⁻¹) * a := by group
      _ = a := by rw [hc1, one_mul]
  calc a * y' = (y' * a * y'⁻¹) * y' := by rw [h]
    _ = y' * a := by group

private lemma l4_dvd_centralizer {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) (hK6L4 : K6L4) {r : ℕ} (hlie : IsLie811 c.Lbar .l4 r 1)
    (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M) (hr2 : r ≠ 2) :
    ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      r ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr5 : 5 ≤ r := c.five_le_of_mem_sigma hr
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  obtain ⟨c₀, hc₀⟩ := (hK6c c.Lbar .l4 r 1 hlie h.Abar h.isElemAbelian_Abar h.card_Abar).1 rfl
  have hdiv := (hK6L4 c.Lbar r hlie hr5).2 h.Abar h.isElemAbelian_Abar h.card_Abar c₀ hc₀
  intro X hXA hXcard
  have hX3 : IsPGroup 3 X := h.elemAbelian.isPGroup.to_le hXA
  have hXL : X ≤ c.L := hXA.trans (h.A_le.trans h.P_le_L)
  have hXbar_le : (X.subgroupOf c.L).map π ≤ h.Abar := h.map_le_Abar hXA
  have hXbar_card : Nat.card ((X.subgroupOf c.L).map π) = 3 := by
    rw [h.card_map_of_le_A hXA, hXcard]
  have hdvdbar : r ∣ Nat.card (Subgroup.centralizer
      (((X.subgroupOf c.L).map π : Subgroup c.Lbar) : Set c.Lbar)) :=
    hdiv.1 ((X.subgroupOf c.L).map π) hXbar_le hXbar_card
  exact (c.dvd_card_centralizer_lbar_iff (q := 3) (by norm_num) (p := r) hr2 hXL hX3).mpr hdvdbar

theorem false_of_l4_of_one_le_pRank_ker {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) (hK6L4 : K6L4) {r : ℕ}
    (hlie : IsLie811 c.Lbar .l4 r 1) (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M r)
    (hZr : ¬ r ∣ Nat.card (Subgroup.center c.Lbar))
    (hC : 1 ≤ CFSG.Open.pRank r
      ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype)) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact r.Prime := ⟨hr.1.1⟩
  have hr2 : r ≠ 2 := by
    have := c.five_le_of_mem_sigma hr
    omega
  obtain ⟨y, hyC, hyord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hr.1.1 hC
  have hyM : y ∈ c.S.M := Subgroup.map_subtype_le _ hyC
  have hyL : y ∉ c.L := l4_not_mem_L hr hZr hyM hyord hyC
  obtain ⟨S, d, hdD, hS_eq, hyNS⟩ := l4_exists_sylow_conj h hr hyord
    (l4_normalizes_sup_pCore h hyM hyC)
  obtain ⟨o, hoO, hmap_o⟩ := l4_decompose_sylow_conj h hdD
  have hoL : (o : G) ∈ c.L := CFSG.LieType.BorelTits.pCoreOf_le 2 c.L hoO
  let y' : G := (o : G)⁻¹ * y * (o : G)
  obtain ⟨hy'M, hy'ord, hy'L, hy'C⟩ := l4_y'_props hr hyM hyord hyL hoL rfl hyC
  have hyNAo : y ∈ Subgroup.normalizer
      ((h.A.map (MulAut.conj (o : G)).toMonoidHom : Subgroup G) : Set G) := by
    rw [← hmap_o, ← hS_eq]
    exact hyNS
  have hy'A : y' ∈ Subgroup.centralizer (h.A : Set G) :=
    l4_y'_centralizes_A h rfl hyNAo hy'C
  exact h.false_of_pElement_not_mem_L hr h76 hy'M hy'A hy'ord hy'L
    (l4_dvd_centralizer h hK6c hK6L4 hlie hr hr2)


theorem false_of_eq_char {c : Counterexample4 G} (h : Case811Sylow c) (hK6c : K6c) (hK6r : K6r)
    {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) (hr : r ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M r)
    (hl4 : ¬ (fam = .l4 ∧ f = 1)) : False := by
  by_cases hfam : fam = .l4
  · have hf : f ≠ 1 := by
      intro hf
      exact hl4 ⟨hfam, hf⟩
    exact false_of_sumZeroCoords h hK6c hK6r hlie hr hfam hf h76
  · exact false_of_signedCoords h hK6c hK6r hlie hr hfam h76

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
