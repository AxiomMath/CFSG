module

public import CFSG.RankThree.GF2n.Stroth80.Sec114
public import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.RankThree.GF2n.Stroth80.Sec112Kernel
import CFSG.RankThree.GF2n.Stroth80.Sec112Class
import CFSG.RankThree.GF2n.Stroth80.Sec112Model
import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line
public import CFSG.Timmesfeld.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (IsRootInvolutionSet)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private def conjClass {A : Type*} [Group A] (X : Subgroup A) (t : A) : Set A :=
  {y | ∃ x ∈ X, x * t * x⁻¹ = y}

private def EbarClassGen (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (t : Mbar M Q) : Subgroup (Mbar M Q) :=
  Subgroup.closure (Ebar M Q Z B \ conjClass (Xbar M Q Z B) t)

private noncomputable def fixingSubgroup [(Q.subgroupOf M).Normal]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (t : Mbar M Q) :
    Subgroup (Mbar M Q) where
  carrier := {k | k ∈ bar M Q (H0 M Z) ∧
    ∀ w ∈ commSpace (liftF φ t), liftF φ k w = w}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, fun w _ => ?_⟩
    rw [liftF_one hφker]
    rfl
  mul_mem' := by
    rintro k₁ k₂ ⟨h₁, hf₁⟩ ⟨h₂, hf₂⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, fun w hw => ?_⟩
    rw [liftF_mul hφker (mem_bar_H0_iff.mp h₁) (mem_bar_H0_iff.mp h₂)]
    simp only [LinearEquiv.mul_apply]
    rw [hf₂ w hw, hf₁ w hw]
  inv_mem' := by
    rintro k ⟨h, hf⟩
    refine ⟨Subgroup.inv_mem _ h, fun w hw => ?_⟩
    have h2 : liftF φ k * liftF φ k⁻¹ = 1 := liftF_mul_inv hφker h
    have e : liftF φ k (liftF φ k⁻¹ w) = w := by
      simpa using congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f w) h2
    exact (liftF φ k).injective (by rw [e, hf w hw])

omit [Finite K] in
private theorem mem_fixingSubgroup [(Q.subgroupOf M).Normal] {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    {hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q} {t k : Mbar M Q} :
    k ∈ fixingSubgroup φ hφker t ↔ k ∈ bar M Q (H0 M Z) ∧
      ∀ w ∈ commSpace (liftF φ t), liftF φ k w = w :=
  Iff.rfl

omit [Finite K] in
private theorem Ctx.map_commSpace_eq_of_commute [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c t : Mbar M Q}
    (hcH : c ∈ bar M Q (H0 M Z)) (htH : t ∈ bar M Q (H0 M Z)) (hct : c * t * c⁻¹ = t) :
    (commSpace (liftF φ t)).map (liftF φ c : M₀.E →ₗ[K] M₀.E) =
      commSpace (liftF φ t) := by
  rw [← commSpace_liftF_conj hφker hcH htH, hct]

omit [Finite K] in
private theorem Ctx.mem_commSpace_apply_of_commute [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c t : Mbar M Q}
    (hcH : c ∈ bar M Q (H0 M Z)) (htH : t ∈ bar M Q (H0 M Z)) (hct : c * t * c⁻¹ = t)
    {w : M₀.E} (hw : w ∈ commSpace (liftF φ t)) :
    liftF φ c w ∈ commSpace (liftF φ t) := by
  rw [← Ctx.map_commSpace_eq_of_commute hφker hcH htH hct]
  exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩

omit [Finite K] in
private theorem Ctx.mem_normalizer_fixingSubgroup_of_commute [(Q.subgroupOf M).Normal]
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c t : Mbar M Q}
    (hcH : c ∈ bar M Q (H0 M Z)) (htH : t ∈ bar M Q (H0 M Z)) (hct : c * t * c⁻¹ = t) :
    c ∈ Subgroup.normalizer (fixingSubgroup φ hφker t : Set (Mbar M Q)) := by
  classical
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hcinv : c⁻¹ ∈ bar M Q (H0 M Z) := (bar M Q (H0 M Z)).inv_mem hcH
  have hct' : c⁻¹ * t * (c⁻¹)⁻¹ = t := by
    rw [inv_inv]
    have h1 : c * t = t * c := by
      simpa using congrArg (fun x => x * c) hct
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [← h1]
      _ = t := by group
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  change k ∈ fixingSubgroup φ hφker t at hk
  change c * k * c⁻¹ ∈ fixingSubgroup φ hφker t
  rw [mem_fixingSubgroup] at hk ⊢
  refine ⟨(bar M Q (H0 M Z)).mul_mem ((bar M Q (H0 M Z)).mul_mem hcH hk.1)
    ((bar M Q (H0 M Z)).inv_mem hcH), ?_⟩
  intro w hw
  have hw' : liftF φ c⁻¹ w ∈ commSpace (liftF φ t) :=
    Ctx.mem_commSpace_apply_of_commute hφker hcinv htH hct' hw
  have e : liftF φ (c * k * c⁻¹) = liftF φ c * liftF φ k * liftF φ c⁻¹ := by
    rw [liftF_mul hφker
        (mem_bar_H0_iff.mp ((bar M Q (H0 M Z)).mul_mem hcH hk.1))
        (mem_bar_H0_iff.mp ((bar M Q (H0 M Z)).inv_mem hcH)),
      liftF_mul hφker (mem_bar_H0_iff.mp hcH) (mem_bar_H0_iff.mp hk.1)]
  rw [e]
  show liftF φ c (liftF φ k (liftF φ c⁻¹ w)) = w
  rw [hk.2 (liftF φ c⁻¹ w) hw']
  have h2 : liftF φ c * liftF φ c⁻¹ = 1 := liftF_mul_inv hφker hcH
  simpa using congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f w) h2

private theorem Ctx.mem_normalizer_EbarClassGen [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {l t : Mbar M Q}
    (hlt : l * t * l⁻¹ = t) :
    l ∈ Subgroup.normalizer (EbarClassGen M Q Z B t : Set (Mbar M Q)) := by
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  refine Subgroup.normalizer_le_normalizer_closure
    (Ebar M Q Z B \ conjClass (Xbar M Q Z B) t) (Subgroup.mem_normalizer_fintype ?_)
  intro d hd
  refine ⟨hc.Ebar_conj hd.1 l, ?_⟩
  rintro ⟨x, hx, hxd⟩
  apply hd.2
  refine ⟨l⁻¹ * x * l, ?_, ?_⟩
  · simpa using hc.Xbar_normal.conj_mem x hx l⁻¹
  · have hdt : l⁻¹ * (x * t * x⁻¹) * l = d := by rw [hxd]; group
    rw [← hdt]
    rw [show (l⁻¹ * x * l) * t * (l⁻¹ * x * l)⁻¹ =
      l⁻¹ * x * (l * t * l⁻¹) * x⁻¹ * l by group, hlt]
    group

private theorem Ctx.mem_centralizer_EbarClassGen [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))))
    {e t : Mbar M Q} (he : e ∈ Ebar M Q Z B) (heC : e ∈ conjClass (Xbar M Q Z B) t) :
    e ∈ Subgroup.centralizer (EbarClassGen M Q Z B t : Set (Mbar M Q)) := by
  classical
  have hle : EbarClassGen M Q Z B t ≤ Subgroup.centralizer ({e} : Set (Mbar M Q)) := by
    unfold EbarClassGen
    refine (Subgroup.closure_le _).mpr ?_
    rintro d ⟨hd, hdC⟩
    change d ∈ Subgroup.centralizer ({e} : Set (Mbar M Q))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    refine (hc.commute_of_not_conj hD hd he ?_).symm
    intro y hy hyde
    apply hdC
    obtain ⟨z, hz, hze⟩ := heC
    refine ⟨y⁻¹ * z, (Xbar M Q Z B).mul_mem ((Xbar M Q Z B).inv_mem hy) hz, ?_⟩
    calc y⁻¹ * z * t * (y⁻¹ * z)⁻¹ = y⁻¹ * (z * t * z⁻¹) * y := by group
      _ = y⁻¹ * e * y := by rw [hze]
      _ = d := by rw [← hyde]; group
  refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (hle hd)) e (Set.mem_singleton e)).symm

omit [Finite K] in
private theorem Ctx.Xbar_le_normalizer_Kbar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))))
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {t : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) :
    Xbar M Q Z B ≤ Subgroup.normalizer
      ((EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) := by
  classical
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  unfold Xbar
  refine (Subgroup.closure_le _).mpr ?_
  intro e he
  by_cases heC : e ∈ conjClass (Xbar M Q Z B) t
  · have hcen := hc.mem_centralizer_EbarClassGen hD he heC
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have hke : k * e = e * k := Subgroup.mem_centralizer_iff.mp hcen k hk.1
    rw [show e * k * e⁻¹ = k by rw [← hke]; group]
    exact hk
  · have heF : e ∈ EbarClassGen M Q Z B t := Subgroup.subset_closure ⟨he, heC⟩
    have hne : ∀ x ∈ Xbar M Q Z B, x * e * x⁻¹ ≠ t := by
      intro x hx hxe
      apply heC
      have h2 : x⁻¹ * t * (x⁻¹)⁻¹ = x⁻¹ * (x * e * x⁻¹) * x := by
        rw [hxe]; group
      refine ⟨x⁻¹, (Xbar M Q Z B).inv_mem hx, ?_⟩
      rw [h2]; group
    have het : e * t * e⁻¹ = t := by
      have h1 := hc.commute_of_not_conj hD he ht hne
      rw [h1]; group
    have hF : e ∈ Subgroup.normalizer (EbarClassGen M Q Z B t : Set (Mbar M Q)) :=
      Subgroup.mem_normalizer_fintype fun k hk =>
        (EbarClassGen M Q Z B t).mul_mem ((EbarClassGen M Q Z B t).mul_mem heF hk)
          ((EbarClassGen M Q Z B t).inv_mem heF)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hF, Ctx.mem_normalizer_fixingSubgroup_of_commute hφker (hc.Ebar_subset_H he)
        (hc.Ebar_subset_H ht) het⟩

omit [Finite K] in
private theorem Ctx.bar_LB_le_normalizer_Kbar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {B' : Subgroup G}
    (hc' : Ctx M Q Z B') {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {t : Mbar M Q}
    (htB' : t ∈ bar M Q (LB M Q B')) :
    bar M Q (LB M Q B') ≤ Subgroup.normalizer
      ((EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)) := by
  classical
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  intro l hl
  have hlt : l * t * l⁻¹ = t := by
    have hcomm : l * t = t * l := congrArg Subtype.val
      (hc'.isElemAbelian_bar_LB.1.is_comm.comm ⟨l, hl⟩ ⟨t, htB'⟩)
    rw [hcomm]; group
  have hlH : l ∈ bar M Q (H0 M Z) :=
    (Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        (Subgroup.subgroupOf_mono M hc'.LB_le_H0)) hl
  have htH : t ∈ bar M Q (H0 M Z) :=
    (Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        (Subgroup.subgroupOf_mono M hc'.LB_le_H0)) htB'
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hc.mem_normalizer_EbarClassGen hlt,
      Ctx.mem_normalizer_fixingSubgroup_of_commute hφker hlH htH hlt⟩

omit [Finite K] in
private theorem Ctx.commSpace_liftF_eq [(Q.subgroupOf M).Normal] {B' : Subgroup G}
    (hc' : Ctx M Q Z B') {a : ↥M}
    (ha : (a : G) ∈ LB M Q B') {t : Mbar M Q} (haMbar : (a : Mbar M Q) = t)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) :
    commSpace (liftF φ t) = commSpace (φ ⟨(a : G), hc'.LB_le_H0 ha⟩) := by
  have hsub : Subgroup.inclusion (H0_le_M : H0 M Z ≤ M)
      ⟨(a : G), hc'.LB_le_H0 ha⟩ = a := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion]
  have hmkH : mkH M Q Z ⟨(a : G), hc'.LB_le_H0 ha⟩ = (a : Mbar M Q) := by
    rw [mkH, MonoidHom.comp_apply, hsub]
    rfl
  rw [← haMbar, ← hmkH, liftF_mkH hφker]

private theorem Ctx.eq_bot_Kbar [(Q.subgroupOf M).Normal] [CharP K 2] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) {B' : Subgroup G} (hc' : Ctx M Q Z B') {a : G}
    (ha : a ∈ LB M Q B') (hline : B' ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z)
    (htB' : t ∈ bar M Q (LB M Q B'))
    (hT : commSpace (liftF φ t) = commSpace (φ ⟨a, hc'.LB_le_H0 ha⟩)) :
    EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t = ⊥ := by
  have hD := isRootInvolutionSet_A2Set_inter hc h hφπ hφker hφiso
  have hXK := hc.Xbar_le_normalizer_Kbar hD φ hφker ht
  have hLK := hc.bar_LB_le_normalizer_Kbar hc' hφker htB'
  have hKX : EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t ≤ Xbar M Q Z B :=
    fun k hk => Subgroup.closure_mono (Set.diff_subset) hk.1
  have hKH : EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t ≤ bar M Q (H0 M Z) :=
    fun k hk => (mem_fixingSubgroup.mp hk.2).1
  have hfix : ∀ z ∈ EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t,
      ∀ w ∈ commSpace (φ ⟨a, hc'.LB_le_H0 ha⟩), liftF φ z w = w := by
    intro z hz w hw
    rw [← hT] at hw
    exact (mem_fixingSubgroup.mp hz.2).2 w hw
  exact hc'.eq_bot_of_fix_commSpace hw hn h hφπ hφker ha hline hKX hXK hc.Xbar_normal hKH
    hfix hLK

omit [Finite K] in
private theorem Ctx.exists_moved_of_Kbar_eq_bot [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {t f : Mbar M Q}
    (hf : f ∈ Ebar M Q Z B)
    (hft : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ f)
    (hbot : EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t = ⊥) :
    ∃ w ∈ commSpace (liftF φ t), liftF φ f w ≠ w := by
  have hfC : f ∉ conjClass (Xbar M Q Z B) t := by
    rintro ⟨x, hx, hxf⟩
    exact hft x hx hxf
  have hfFb : f ∈ EbarClassGen M Q Z B t := Subgroup.subset_closure ⟨hf, hfC⟩
  have hfne : f ≠ 1 := by
    have h2 := Ctx.orderOf_eq_two_of_mem_Ebar hf
    intro h1
    rw [h1, orderOf_one] at h2
    omega
  have hfS : f ∉ fixingSubgroup φ hφker t := fun hS => by
    have hmem : f ∈ EbarClassGen M Q Z B t ⊓ fixingSubgroup φ hφker t := ⟨hfFb, hS⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hfne hmem
  have h : ¬ ∀ w ∈ commSpace (liftF φ t), liftF φ f w = w := by
    intro hw
    exact hfS ((mem_fixingSubgroup).mpr ⟨hc.Ebar_subset_H hf, hw⟩)
  push Not at h
  exact h

theorem Ctx.exists_moved_of_not_conj [(Q.subgroupOf M).Normal] [CharP K 2] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t f : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (hft : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ f) :
    ∃ w ∈ commSpace (liftF φ t), liftF φ f w ≠ w := by
  classical
  obtain ⟨m, hm, a, ha, hA, haMbar⟩ := hc.exists_conj_LB_lift ht
  have hc' : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hline : conjSubgroup m B ≤ ⁅Q, Subgroup.zpowers (a : G)⁆ ⊔ Z :=
    strothA2Line_holds G M Q Z (conjSubgroup m B) hc' n hw hn (a : G) ha hA
  have htB' : t ∈ bar M Q (LB M Q (conjSubgroup m B)) := by
    rw [← haMbar]
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hT := Ctx.commSpace_liftF_eq hc' ha haMbar hφker
  exact hc.exists_moved_of_Kbar_eq_bot hφker hf hft
    (hc.eq_bot_Kbar hw hn h hφπ hφker hφiso ht hc' ha hline htB' hT)

end CFSG.RankThree.GF2n.Stroth80
