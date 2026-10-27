module

public import CFSG.Timmesfeld.ARS.Sec8Field
public import CFSG.Timmesfeld.ARS.CaseHField

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Setup

variable (S : Setup R A A₀ P P')

include S

theorem P_le_M : P ≤ M R A := QD.le_M S.hP.1

theorem P'_le_M : P' ≤ M R A := QD.le_M S.hP'.1

omit S in
theorem U5_le_M : shortRoot R P' ⁅A₀, P⁆ A ≤ M R A := inf_le_right

omit S in
theorem U3_le_M : shortRoot R P ⁅A₀, P'⁆ A ≤ M R A := inf_le_right

theorem eq_one_of_mul_mem_A {p u u' p' : G} (hp : p ∈ P) (hu : u ∈ shortRoot R P' ⁅A₀, P⁆ A)
    (hu' : u' ∈ shortRoot R P ⁅A₀, P'⁆ A) (hp' : p' ∈ P') (h : p * u * u' * p' ∈ A) :
    p = 1 ∧ u = 1 ∧ u' = 1 ∧ p' = 1 := by
  have hh := S.hyp
  have := hh.finite
  have hR := hh.root
  have hPR : P ∈ R := S.hP.2.1
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, ⟨hsPP', -⟩, -, ⟨hsAQ', hcAQ'⟩, -, hQ'Ω, -⟩ :=
    apartment hh S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  obtain ⟨hK, -, -, -, -, -⟩ := S.facts
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hU3P', -, -⟩ :=
    positive_relations hh S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  have hAK : ∀ x ∈ A, x ∈ M R A ⊓ M R P' := fun x hx => by
    rw [hK]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
  have hP'K : ∀ x ∈ P', x ∈ M R A ⊓ M R P' := fun x hx => by
    rw [hK]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
  have hU3K : ∀ x ∈ shortRoot R P ⁅A₀, P'⁆ A, x ∈ M R A ⊓ M R P' := fun x hx => by
    rw [hK]; exact Subgroup.mem_sup_right hx
  have hKH : ∀ x ∈ M R A ⊓ M R P', x ∈ M R A ⊓ Subgroup.normalizer (P' : Set G) :=
    fun x hx => ⟨hx.1, (isPGroup_M hR hP'R).2.1 hx.2⟩
  have hU5H : ∀ x ∈ shortRoot R P' ⁅A₀, P⁆ A, x ∈ M R A ⊓ Subgroup.normalizer (P' : Set G) :=
    fun x hx => ⟨hx.2, conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun y hy =>
      commuting_shortRoot_left P' _ A x hx y hy)⟩
  set H := M R A ⊓ Subgroup.normalizer (P' : Set G)
  set K := M R A ⊓ M R P'
  have hp1 : p = 1 := by
    have hpH : p ∈ H := by
      have := H.mul_mem (hKH _ (hAK _ h)) (H.inv_mem (H.mul_mem (H.mul_mem (hU5H u hu)
        (hKH _ (hU3K u' hu'))) (hKH _ (hP'K p' hp'))))
      rwa [show p * u * u' * p' * (u * u' * p')⁻¹ = p by group] at this
    by_contra hne
    exact Sec3.conjSub_ne_of_special hR hh.noIsolated hPR hP'R hsPP' hp hne
      (conjSub_eq_self_iff.2 hpH.2)
  subst hp1
  rw [one_mul] at h
  have hu1 : u = 1 := by
    have huK : u ∈ K := by
      have := K.mul_mem (hAK _ h) (K.inv_mem (K.mul_mem (hU3K u' hu') (hP'K p' hp')))
      rwa [show u * u' * p' * (u' * p')⁻¹ = u by group] at this
    exact eq_one_of_mem_U5_of_mem_M hh S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP' hu huK.2
  subst hu1
  rw [one_mul] at h
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm S.hA S.hP.1, S.hA, hsAQ'.symm⟩
  have heq : ⁅⁅A₀, P'⁆, A⁆ = P' := by rw [Subgroup.commutator_comm, hcAQ']
  have hinj := injective_mul_shortRoot hh S.hH S.hT hPR hQ'Ω hAs
  have hp'' : p' ∈ ⁅⁅A₀, P'⁆, A⁆ := by rw [heq]; exact hp'
  have e : ((⟨(u' * p')⁻¹, A.inv_mem h⟩ : ↥A) : G) * ((⟨p', hp''⟩ : ↥⁅⁅A₀, P'⁆, A⁆) : G) *
      ((⟨u', hu'⟩ : ↥(shortRoot R P ⁅A₀, P'⁆ A)) : G) =
      ((1 : ↥A) : G) * ((1 : ↥⁅⁅A₀, P'⁆, A⁆) : G) * ((1 : ↥(shortRoot R P ⁅A₀, P'⁆ A)) : G) := by
    simp only [OneMemClass.coe_one, mul_one]
    rw [(hU3P' u' hu' p' hp').eq]
    group
  have := @hinj (⟨_, A.inv_mem h⟩, ⟨p', hp''⟩, ⟨u', hu'⟩) 1 e
  exact ⟨rfl, rfl, congrArg (fun x => (x.2.2 : G)) this, congrArg (fun x => (x.2.1 : G)) this⟩

omit S in
@[expose] noncomputable def toQuot {X : Subgroup G} (hX : X ≤ M R A) : ↥X →* MQuot R A :=
  (QuotientGroup.mk' (A.subgroupOf (M R A))).comp (Subgroup.inclusion hX)

omit S in
theorem toQuot_apply {X : Subgroup G} (hX : X ≤ M R A) (x : ↥X) :
    toQuot hX x = (QuotientGroup.mk (Subgroup.inclusion hX x) : MQuot R A) := rfl

@[expose] noncomputable def prodHom :
    (↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) × ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P') →* MQuot R A where
  toFun x := toQuot S.P_le_M x.1 * toQuot U5_le_M x.2.1 * toQuot U3_le_M x.2.2.1 *
    toQuot S.P'_le_M x.2.2.2
  map_one' := by simp
  map_mul' x y := by
    let _ : CommGroup (MQuot R A) := commGroupMQuot S.hyp S.hA
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

theorem prodHom_injective : Function.Injective S.prodHom := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  change toQuot S.P_le_M x.1 * toQuot U5_le_M x.2.1 * toQuot U3_le_M x.2.2.1 *
    toQuot S.P'_le_M x.2.2.2 = 1 at hx
  simp only [toQuot_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inclusion] at hx
  obtain ⟨h1, h2, h3, h4⟩ := S.eq_one_of_mul_mem_A x.1.2 x.2.1.2 x.2.2.1.2 x.2.2.2.2 hx
  exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Prod.ext (Subtype.ext h3)
    (Subtype.ext h4)))

theorem card_prod_le :
    Nat.card (MQuot R A) ≤
      Nat.card (↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) × ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P') := by
  have hh := S.hyp
  have := hh.finite
  have hR := hh.root
  have hPR : P ∈ R := S.hP.2.1
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, -, ⟨hsAQ, -⟩, ⟨hsAQ', -⟩, -, hQ'Ω, hQΩ⟩ :=
    apartment hh S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm S.hA S.hP.1, S.hA, hsAQ'.symm⟩
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm S.hA S.hP'.1, S.hA, hsAQ.symm⟩
  have hM := card_M_eq hh S.hT S.hA
  rw [ncard_omegaSet hh S.hH S.hA rfl rfl,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (M R A)),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe QD.le_M_self).toEquiv] at hM
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hR.card_eq hPR S.hA, hR.card_eq hP'R S.hA,
    card_shortRoot hh S.hH S.hT hP'R hQΩ hAs', card_shortRoot hh S.hH S.hT hPR hQ'Ω hAs,
    ncard_linesThrough_eq hh S.hA hP'R, ncard_linesThrough_eq hh S.hA hPR]
  have hq : 0 < Nat.card A := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right (le_of_eq ?_) hq
  rw [hM]
  ring

@[expose] noncomputable def prodEquiv :
    (↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) × ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P') ≃* MQuot R A :=
  have := S.hyp.finite
  MulEquiv.ofBijective S.prodHom (S.prodHom_injective.bijective_of_nat_card_le S.card_prod_le)

@[expose] noncomputable def proj :
    ↥(M R A) →* (↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) × ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P') :=
  S.prodEquiv.symm.toMonoidHom.comp (QuotientGroup.mk' _)

theorem proj_eq_iff (m : ↥(M R A))
    (x : ↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) × ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P') :
    S.proj m = x ↔ S.prodHom x = QuotientGroup.mk m := by
  change S.prodEquiv.symm (QuotientGroup.mk m) = x ↔ _
  rw [MulEquiv.symm_apply_eq]
  exact eq_comm

theorem proj_P {x : G} (hx : x ∈ P) : S.proj ⟨x, S.P_le_M hx⟩ = (⟨x, hx⟩, 1, 1, 1) := by
  rw [proj_eq_iff]
  change toQuot S.P_le_M ⟨x, hx⟩ * toQuot U5_le_M 1 * toQuot U3_le_M 1 *
    toQuot S.P'_le_M 1 = _
  simp only [map_one, mul_one]
  rfl

theorem proj_U5 {x : G} (hx : x ∈ shortRoot R P' ⁅A₀, P⁆ A) :
    S.proj ⟨x, U5_le_M hx⟩ = (1, ⟨x, hx⟩, 1, 1) := by
  rw [proj_eq_iff]
  change toQuot S.P_le_M 1 * toQuot U5_le_M ⟨x, hx⟩ * toQuot U3_le_M 1 *
    toQuot S.P'_le_M 1 = _
  simp only [map_one, mul_one, one_mul]
  rfl

theorem proj_U3 {x : G} (hx : x ∈ shortRoot R P ⁅A₀, P'⁆ A) :
    S.proj ⟨x, U3_le_M hx⟩ = (1, 1, ⟨x, hx⟩, 1) := by
  rw [proj_eq_iff]
  change toQuot S.P_le_M 1 * toQuot U5_le_M 1 * toQuot U3_le_M ⟨x, hx⟩ *
    toQuot S.P'_le_M 1 = _
  simp only [map_one, mul_one, one_mul]
  rfl

theorem proj_P' {x : G} (hx : x ∈ P') : S.proj ⟨x, S.P'_le_M hx⟩ = (1, 1, 1, ⟨x, hx⟩) := by
  rw [proj_eq_iff]
  change toQuot S.P_le_M 1 * toQuot U5_le_M 1 * toQuot U3_le_M 1 *
    toQuot S.P'_le_M ⟨x, hx⟩ = _
  simp only [map_one, one_mul]
  rfl

theorem proj_A {x : G} (hx : x ∈ A) : S.proj ⟨x, QD.le_M_self hx⟩ = 1 := by
  rw [proj_eq_iff, map_one, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hx

theorem exists_eq_mul (g : ↥(M R A)) :
    ∃ a ∈ A, (g : G) = ((S.proj g).1 : G) * (S.proj g).2.1 * (S.proj g).2.2.1 *
      (S.proj g).2.2.2 * a := by
  have h := (S.proj_eq_iff g (S.proj g)).1 rfl
  change toQuot S.P_le_M (S.proj g).1 * toQuot U5_le_M (S.proj g).2.1 *
    toQuot U3_le_M (S.proj g).2.2.1 * toQuot S.P'_le_M (S.proj g).2.2.2 = _ at h
  simp only [toQuot_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at h
  exact ⟨_, h, by group⟩

theorem proj_conj {h₀ : G} (hh₀ : h₀ ∈ Subgroup.normalizer (A : Set G)) (g : ↥(M R A)) :
    S.proj ⟨h₀ * g * h₀⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hh₀ g.2⟩ =
      S.proj ⟨h₀ * (S.proj g).1 * h₀⁻¹,
        conj_mem_M_of_mem_normalizer S.hyp.root hh₀ (S.P_le_M (S.proj g).1.2)⟩ *
      S.proj ⟨h₀ * (S.proj g).2.1 * h₀⁻¹,
        conj_mem_M_of_mem_normalizer S.hyp.root hh₀ (U5_le_M (S.proj g).2.1.2)⟩ *
      S.proj ⟨h₀ * (S.proj g).2.2.1 * h₀⁻¹,
        conj_mem_M_of_mem_normalizer S.hyp.root hh₀ (U3_le_M (S.proj g).2.2.1.2)⟩ *
      S.proj ⟨h₀ * (S.proj g).2.2.2 * h₀⁻¹,
        conj_mem_M_of_mem_normalizer S.hyp.root hh₀ (S.P'_le_M (S.proj g).2.2.2.2)⟩ := by
  obtain ⟨a, ha, hg⟩ := S.exists_eq_mul g
  have hA' : h₀ * a * h₀⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hh₀ a).1 ha
  simp only [← map_mul]
  have e : (⟨h₀ * g * h₀⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hh₀ g.2⟩ : ↥(M R A)) =
      ⟨h₀ * (S.proj g).1 * h₀⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hh₀
          (S.P_le_M (S.proj g).1.2)⟩ *
        ⟨h₀ * (S.proj g).2.1 * h₀⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hh₀
          (U5_le_M (S.proj g).2.1.2)⟩ *
        ⟨h₀ * (S.proj g).2.2.1 * h₀⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hh₀
          (U3_le_M (S.proj g).2.2.1.2)⟩ *
        ⟨h₀ * (S.proj g).2.2.2 * h₀⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hh₀
          (S.P'_le_M (S.proj g).2.2.2.2)⟩ *
        ⟨h₀ * a * h₀⁻¹, QD.le_M_self hA'⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hg]
    group
  rw [e, map_mul, S.proj_A hA', mul_one]

theorem proj_K {k : G} (hk : k ∈ M R A ⊓ M R P') :
    (S.proj ⟨k, hk.1⟩).1 = 1 ∧ (S.proj ⟨k, hk.1⟩).2.1 = 1 := by
  have hh := S.hyp
  have hPR : P ∈ R := S.hP.2.1
  obtain ⟨-, -, -, -, -, -, ⟨hsAQ', hcAQ'⟩, -, hQ'Ω, -⟩ :=
    apartment hh S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm S.hA S.hP.1, S.hA, hsAQ'.symm⟩
  have heq : ⁅⁅A₀, P'⁆, A⁆ = P' := by rw [Subgroup.commutator_comm, hcAQ']
  have hL : 3 ≤ (linesThrough R P).ncard := (ncard_linesThrough_eq hh S.hA hPR) ▸ S.h3
  have hk' : k ∈ M R A ⊓ M R ⁅⁅A₀, P'⁆, A⁆ := by rwa [heq]
  obtain ⟨⟨a, p', u⟩, hkdec⟩ := M_inf_M hh S.hH S.hT hPR hL hQ'Ω hAs hk'
  have hp' : (p' : G) ∈ P' := heq.le p'.2
  have e : (⟨k, hk.1⟩ : ↥(M R A)) = ⟨a, QD.le_M_self a.2⟩ * ⟨p', S.P'_le_M hp'⟩ *
      ⟨u, U3_le_M u.2⟩ := Subtype.ext hkdec.symm
  rw [e, map_mul, map_mul, S.proj_A a.2, S.proj_P' hp', S.proj_U3 u.2]
  exact ⟨by simp, by simp⟩

theorem proj_H {g : G} (hg : g ∈ M R A ⊓ Subgroup.normalizer (P' : Set G)) :
    (S.proj ⟨g, hg.1⟩).1 = 1 ∧ ((S.proj ⟨g, hg.1⟩).2.1 : G) = comp5 S g := by
  obtain ⟨h5, hk⟩ := comp5_spec S hg
  obtain ⟨hk1, hk2⟩ := S.proj_K hk
  have e : (⟨g, hg.1⟩ : ↥(M R A)) = ⟨g * (comp5 S g)⁻¹, hk.1⟩ * ⟨comp5 S g, U5_le_M h5⟩ :=
    Subtype.ext (by simp)
  rw [e, map_mul, S.proj_U5 h5]
  refine ⟨?_, ?_⟩
  · simp [hk1]
  · simp [hk2]

end Setup

end CaseH

end CFSG.Timmesfeld.ARS
