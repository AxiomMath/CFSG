module

public import CFSG.RankThree.GF2n.Stroth80.Sec79OmegaFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec78HypFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.F2Fixed
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement Matrix

namespace Om10

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem mem_LomGL_iff_eichler (E : ElemMatrixIso Q' X) {u : ι → K} {A : GL ι K} :
    A ∈ E.LomGL u ↔ A ∈ X ∧ ∃ w : ι → K, polar Q' u w = 0 ∧
      ∀ v, (A : Matrix ι ι K) *ᵥ v = eichler Q' u w v := by
  unfold ElemMatrixIso.LomGL
  rw [mem_matrixOf_iff]
  constructor
  · rintro ⟨hA, h⟩
    obtain ⟨w, hw, he⟩ := mem_rootGroup.mp (mem_Lom.mp h)
    refine ⟨hA, w, hw, fun v => ?_⟩
    rw [← E.app ⟨A, hA⟩ v, he]
    rfl
  · rintro ⟨hA, w, hw, he⟩
    refine ⟨hA, mem_Lom.mpr (mem_rootGroup.mpr ⟨w, hw, LinearEquiv.ext fun v => ?_⟩)⟩
    rw [← he v, ← E.app ⟨A, hA⟩ v]
    rfl

theorem exists_LomGL_eichler (E : ElemMatrixIso Q' X) {u w : ι → K}
    (hw : polar Q' u w = 0) :
    ∃ A ∈ E.LomGL u, ∀ v, (A : Matrix ι ι K) *ᵥ v = eichler Q' u w v := by
  set A : X := E.equiv.symm ⟨eichler Q' u w, eichler_mem_elementaryGroup Q' u w⟩ with hAdef
  have happ : ∀ v, ((A : GL ι K) : Matrix ι ι K) *ᵥ v = eichler Q' u w v := by
    intro v
    rw [← E.app A v, hAdef, MulEquiv.apply_symm_apply]
    rfl
  exact ⟨A, (mem_LomGL_iff_eichler E).mpr ⟨A.2, w, hw, happ⟩, happ⟩

end Matrix

variable {G : Type} [Group G]

section Frame

variable [Finite G] {M Q Z B : Subgroup G}

theorem opp_of_frame (h52b : Stroth52bStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {h r : G} (hh : h ∈ Rt M (LB M Q B) t)
    (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z (conjSubgroup h B) (conjSubgroup r (conjSubgroup h B)) t) :
    IsOppDecomp (Wt Q (Vt M (LB M Q B) B Z t)) (Vt M (LB M Q B) B Z t)
      (conjSubgroup h (LB M Q B)) (conjSubgroup (r * h) (LB M Q B))
      ((QB (conjSubgroup h B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
      ((QB (conjSubgroup r (conjSubgroup h B)) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t) := by
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hsL : t ∈ LB M Q (conjSubgroup h B) := by
    rw [hc.LB_conj hhM, mem_conjSubgroup]
    have e : h⁻¹ * t * h = ⁅h⁻¹, t⁆ * t := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hq : ⁅h⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hh)
    exact (LB M Q B).mul_mem (Subgroup.mem_sup_left hq) ht
  have hs' : Sec7Hyp (hc.conj_of_mem hhM) n t :=
    sec7ctr_hyp_frame hc hs hhM hsL hs.toSec5.notQ rfl rfl
  have hV : Vt M (LB M Q (conjSubgroup h B)) (conjSubgroup h B) Z t =
      Vt M (LB M Q B) B Z t := by
    rw [hc.LB_conj hhM]
    exact sec7ctr_Vt_conj_frame hhM t
  have hrR' : r ∈ Rt M (LB M Q (conjSubgroup h B)) t := by
    rw [hc.LB_conj hhM, sec7ctr_Rt_conj_frame hhM t]
    exact hr
  have hd := h52b G M Q Z (conjSubgroup h B) (hc.conj_of_mem hhM) n t hs'.toSec5 hs'.omegaNat r
    hrR' hplane (conjSubgroup r (conjSubgroup h B)) (LB M Q (conjSubgroup h B))
    (LB M Q (conjSubgroup r (conjSubgroup h B)))
    (Vt M (LB M Q (conjSubgroup h B)) (conjSubgroup h B) Z t)
    (Wt Q (Vt M (LB M Q (conjSubgroup h B)) (conjSubgroup h B) Z t)) rfl rfl rfl rfl rfl
  have hL₁ : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hhM
  have hL₂ : LB M Q (conjSubgroup r (conjSubgroup h B)) = conjSubgroup (r * h) (LB M Q B) := by
    rw [← conjSubgroup_mul, hc.LB_conj (M.mul_mem hrM hhM)]
  rw [hV, hL₁, hL₂] at hd
  exact hd

end Frame

theorem mul_comm_of_mem_Wt {Q V : Subgroup G} {w v : G} (hw : w ∈ Wt Q V) (hv : v ∈ V) :
    w * v = v * w :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 v hv).symm

theorem fixSec_mul_aux {Q V : Subgroup G} {x a b : G} (ha : a ∈ Wt Q V) (hax : ⁅x, a⁆ ∈ V)
    (hb : b ∈ Wt Q V) (hbx : ⁅x, b⁆ ∈ V) : a * b ∈ Wt Q V ∧ ⁅x, a * b⁆ ∈ V := by
  refine ⟨(Wt Q V).mul_mem ha hb, ?_⟩
  have hc : a * ⁅x, b⁆ = ⁅x, b⁆ * a := mul_comm_of_mem_Wt ha hbx
  have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, hc, mul_inv_cancel_right]
  exact V.mul_mem hax hbx

theorem fixSec_inv_aux {Q V : Subgroup G} {x a : G} (ha : a ∈ Wt Q V) (hax : ⁅x, a⁆ ∈ V) :
    a⁻¹ ∈ Wt Q V ∧ ⁅x, a⁻¹⁆ ∈ V := by
  refine ⟨(Wt Q V).inv_mem ha, ?_⟩
  have hc : a⁻¹ * ⁅x, a⁆⁻¹ = ⁅x, a⁆⁻¹ * a⁻¹ :=
    mul_comm_of_mem_Wt ((Wt Q V).inv_mem ha) (V.inv_mem hax)
  have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
    simp only [commutatorElement_def]
    group
  rw [e, hc, inv_mul_cancel_right]
  exact V.inv_mem hax

@[expose] def fixSec (Q V : Subgroup G) (x : G) : Subgroup G where
  carrier := {w | w ∈ Wt Q V ∧ ⁅x, w⁆ ∈ V}
  mul_mem' := fun {_ _} ha hb => fixSec_mul_aux ha.1 ha.2 hb.1 hb.2
  one_mem' := ⟨(Wt Q V).one_mem, by
    rw [commutatorElement_one_right]
    exact V.one_mem⟩
  inv_mem' := fun {_} ha => fixSec_inv_aux ha.1 ha.2

theorem fixSec_le_Wt (Q V : Subgroup G) (x : G) : fixSec Q V x ≤ Wt Q V := fun _ h => h.1

theorem isOppDecomp_fixSec {Q V L₁ L₂ A₁ A₂ L₁' L₂' : Subgroup G} {x : G}
    (hd : IsOppDecomp (Wt Q V) V L₁ L₂ A₁ A₂) (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hxA₁ : ∀ a ∈ A₁, x * a * x⁻¹ ∈ A₁) (hxA₂ : ∀ a ∈ A₂, x * a * x⁻¹ ∈ A₂)
    (h₁ : L₁' ≤ L₁) (h₂ : L₂' ≤ L₂)
    (hfix₁ : ∀ y ∈ fixSec Q V x, (∀ l ∈ L₁', ⁅l, y⁆ ∈ V) → y ∈ A₁)
    (hfix₂ : ∀ y ∈ fixSec Q V x, (∀ l ∈ L₂', ⁅l, y⁆ ∈ V) → y ∈ A₂) :
    IsOppDecomp (fixSec Q V x) V L₁' L₂' (A₁ ⊓ fixSec Q V x) (A₂ ⊓ fixSec Q V x) := by
  obtain ⟨hVA₁, hA₁W, hVA₂, hA₂W, hsup, hinf, hcomm, hsq, hfA₁, hfA₂⟩ := hd
  have hVP : V ≤ fixSec Q V x := by
    intro v hv
    refine ⟨hA₁W (hVA₁ hv), ?_⟩
    have e : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact V.mul_mem (hxV v hv) (V.inv_mem hv)
  have hcommx : ∀ {A : Subgroup G}, (∀ a ∈ A, x * a * x⁻¹ ∈ A) → ∀ a ∈ A, ⁅x, a⁆ ∈ A := by
    intro A hA a ha
    have e : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact A.mul_mem (hA a ha) (A.inv_mem ha)
  refine ⟨le_inf hVA₁ hVP, inf_le_right, le_inf hVA₂ hVP, inf_le_right, ?_, ?_,
    fun a ha b hb => hcomm a ha.1 b hb.1, fun a ha => hsq a ha.1, ?_, ?_⟩
  · refine le_antisymm (sup_le inf_le_right inf_le_right) (fun p hp => ?_)
    have hpW : p ∈ A₁ ⊔ A₂ := by rw [hsup]; exact hp.1
    have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set G) := by
      refine Subgroup.le_normalizer_iff.mpr fun a ha b hb => ?_
      have hcb : ⁅a, b⁆ ∈ A₂ := hVA₂ (hcomm a (hA₁W ha) b (hA₂W hb))
      have key : a * b * a⁻¹ = ⁅a, b⁆ * b := by
        rw [commutatorElement_def]
        group
      rw [key]
      exact A₂.mul_mem hcb hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hpW
    have hc₁ : ⁅x, a₁⁆ ∈ A₁ := hcommx hxA₁ a₁ ha₁
    have hc₂ : a₁ * ⁅x, a₂⁆ * a₁⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp (hnorm ha₁) _).mp (hcommx hxA₂ a₂ ha₂)
    have e : ⁅x, a₁ * a₂⁆ = ⁅x, a₁⁆ * (a₁ * ⁅x, a₂⁆ * a₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hprod : ⁅x, a₁⁆ * (a₁ * ⁅x, a₂⁆ * a₁⁻¹) ∈ V := by rw [← e]; exact hp.2
    have hc₁A₂ : ⁅x, a₁⁆ ∈ A₂ := by
      have e' : ⁅x, a₁⁆ = (⁅x, a₁⁆ * (a₁ * ⁅x, a₂⁆ * a₁⁻¹)) * (a₁ * ⁅x, a₂⁆ * a₁⁻¹)⁻¹ := by
        group
      rw [e']
      exact A₂.mul_mem (hVA₂ hprod) (A₂.inv_mem hc₂)
    have hc₁V : ⁅x, a₁⁆ ∈ V := by
      rw [← hinf]
      exact ⟨hc₁, hc₁A₂⟩
    have ha₁P : a₁ ∈ fixSec Q V x := ⟨hA₁W ha₁, hc₁V⟩
    have ha₂P : a₂ ∈ fixSec Q V x := by
      have e2 : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
      rw [e2]
      exact (fixSec Q V x).mul_mem ((fixSec Q V x).inv_mem ha₁P) hp
    exact Subgroup.mul_mem_sup ⟨ha₁, ha₁P⟩ ⟨ha₂, ha₂P⟩
  · rw [inf_inf_inf_comm, inf_idem, hinf]
    exact inf_eq_left.mpr hVP
  · intro y hy
    constructor
    · rintro ⟨hyA, -⟩ l hl
      exact (hfA₁ y hy.1).mp hyA l (h₁ hl)
    · exact fun h => ⟨hfix₁ y hy h, hy⟩
  · intro y hy
    constructor
    · rintro ⟨hyA, -⟩ l hl
      exact (hfA₂ y hy.1).mp hyA l (h₂ hl)
    · exact fun h => ⟨hfix₂ y hy h, hy⟩

section NonA2

variable [Finite G] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} {R N P I L₁ L₂ A₁ A₂ : Subgroup G}

theorem mem_of_comm_nonA2 (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : ι → K} (hu : Q' u = 0) (hu' : Q' u' = 0) (huu' : polar Q' u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u')
    {y : ↥R} (hy : (y : G) ∈ L₂)
    (hn : ∃ v : ι → K, polar Q' v ((φ y : Matrix ι ι K) *ᵥ v) ≠ 0)
    {w : G} (hw : w ∈ P) (hfix : ⁅(y : G), w⁆ ∈ I) : w ∈ A₂ := by
  classical
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨Md, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite Md := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  obtain ⟨hy1, -, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu hu' huu' hL₁
    hL₂ hdec h4 (Subgroup.mem_subgroupOf.mpr hy) hn
  obtain ⟨-, e₂⟩ := fixedSub_eq_secSub_of_isOppDecomp hP hκ hd h₁ h₂
  have hmem : Multiplicative.toAdd (κ ⟨w, hw⟩) ∈ fixedSub Md ({y} : Set ↥R) := by
    rw [mem_fixedSub]
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    have hact := hκ.act r ⟨w, hw⟩ ⟨(r : G) * w * (r : G)⁻¹, hP r r.2 w hw⟩ rfl
    have heq : κ ⟨(r : G) * w * (r : G)⁻¹, hP r r.2 w hw⟩ = κ ⟨w, hw⟩ := by
      rw [hκ.eq_iff]
      have e : (r : G) * w * (r : G)⁻¹ * w⁻¹ = ⁅(r : G), w⁆ := by
        rw [commutatorElement_def]
      rw [e]
      exact hfix
    rw [heq] at hact
    have := congrArg Multiplicative.toAdd hact
    rw [toAdd_ofAdd] at this
    exact this.symm
  rw [hy1, e₂] at hmem
  exact (toAdd_mem_secSub_iff hκ hd.2.2.1 ⟨w, hw⟩).mp hmem

end NonA2

end Om10

end CFSG.RankThree.GF2n.Stroth80
