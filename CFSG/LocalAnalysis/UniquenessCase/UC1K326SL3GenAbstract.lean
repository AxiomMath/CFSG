module

public import TauCeti.GroupTheory.FixedSubgroup
public import CFSG.GroupTheory.ThompsonIsomorphism
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

namespace SL3G

section Abstract

variable {G G' : Type*} [Group G] [Group G']

abbrev fixSub (α : MulAut G) : Subgroup G := TauCeti.fixedSubgroup α.toMonoidHom

theorem mem_fixSub {α : MulAut G} {x : G} : x ∈ fixSub α ↔ α x = x := Iff.rfl

structure ModelHyp (α : MulAut G) (T : Subgroup G) : Prop where
  cube : α ^ 3 = 1
  pgroup : IsPGroup 3 T
  maximal : ∀ S : Subgroup G, IsPGroup 3 S → T ≤ S → S = T
  stable : ∀ t ∈ T, α t ∈ T
  nonabelian : ¬ IsMulCommutative ↥T
  moves : ∃ t ∈ T, t * (α t)⁻¹ ∉ Subgroup.center G
  index : (fixSub α).relIndex T = 3
  abelian : IsMulCommutative ↥(T ⊓ fixSub α)

@[expose] def ModelGen (G : Type*) [Group G] : Prop :=
  ∀ (α : MulAut G) (T : Subgroup G), ModelHyp α T → T ⊔ fixSub α = ⊤

private theorem aut_cube_apply {α : MulAut G} (hα : α ^ 3 = 1) (x : G) :
    α (α (α x)) = x := by
  have := congrArg (fun β : MulAut G => β x) hα
  simpa [pow_succ] using this

private def autRestrict {α : MulAut G} {T : Subgroup G} (hTα : ∀ t ∈ T, α t ∈ T) (t : ↥T) :
    ↥T := ⟨α t, hTα t t.2⟩

private theorem autRestrict_maps_subgroupOf {α : MulAut G} {T : Subgroup G}
    (hTα : ∀ t ∈ T, α t ∈ T) :
    ∀ a b : ↥T, a⁻¹ * b ∈ (fixSub α).subgroupOf T →
      (autRestrict hTα a)⁻¹ * autRestrict hTα b ∈ (fixSub α).subgroupOf T := by
  intro a b hab
  rw [Subgroup.mem_subgroupOf] at hab ⊢
  have e : (((autRestrict hTα a)⁻¹ * autRestrict hTα b : ↥T) : G) =
      α ((a⁻¹ * b : ↥T) : G) := by
    simp [autRestrict]
  rw [e]
  have h1 : α ((a⁻¹ * b : ↥T) : G) = ((a⁻¹ * b : ↥T) : G) := hab
  rw [h1]
  exact hab

private theorem eq_of_pow_three_eq_one_of_card_three {X : Type*} [Fintype X] (f : Function.End X)
    (hcard : Fintype.card X = 3) (hf : f ^ 3 = 1) (x : X) (hx : f x = x) : ∀ y, f y = y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by simpa using hf)
  have hcard_eq : Fintype.card {z : X // f z = z} = Fintype.card ↑(Function.fixedPoints f) :=
    Fintype.card_congr (Equiv.refl _)
  have hmod' : Nat.ModEq 3 (Fintype.card X) (Fintype.card {z : X // f z = z}) := by
    rw [hcard_eq]
    exact hmod
  have hpos : 0 < Fintype.card {z : X // f z = z} := Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  intro y
  by_contra hy
  have hlt := Fintype.card_subtype_lt (p := fun z : X => f z = z) hy
  rw [hcard] at hmod'
  unfold Nat.ModEq at hmod'
  have hzero : Fintype.card {z : X // f z = z} % 3 = 0 := by
    rw [← hmod']
  rw [Nat.mod_eq_of_lt (by simpa [hcard] using hlt)] at hzero
  omega

private theorem autRestrict_quot_eq {α : MulAut G} {T : Subgroup G} (hα : α ^ 3 = 1)
    (hTα : ∀ t ∈ T, α t ∈ T) (hidx : (fixSub α).relIndex T = 3) (t : ↥T) :
    (QuotientGroup.mk t : ↥T ⧸ (fixSub α).subgroupOf T) =
      QuotientGroup.mk (autRestrict hTα t) := by
  classical
  have hcard : Nat.card (↥T ⧸ (fixSub α).subgroupOf T) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  haveI : Finite (↥T ⧸ (fixSub α).subgroupOf T) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype (↥T ⧸ (fixSub α).subgroupOf T) := Fintype.ofFinite _
  have hcomp := autRestrict_maps_subgroupOf (α := α) hTα
  let f : Function.End (↥T ⧸ (fixSub α).subgroupOf T) :=
    Quotient.map' (autRestrict hTα) (fun a b hab =>
      QuotientGroup.leftRel_apply.mpr (hcomp a b (QuotientGroup.leftRel_apply.mp hab)))
  have hf3 : f ^ 3 = 1 := by
    funext c
    induction c using Quotient.inductionOn' with
    | _ s =>
      have e : autRestrict hTα (autRestrict hTα (autRestrict hTα s)) = s :=
        Subtype.ext (aut_cube_apply hα s)
      show f (f (f (Quotient.mk'' s))) = Quotient.mk'' s
      rw [show f (Quotient.mk'' s) = Quotient.mk'' (autRestrict hTα s) from rfl,
        show f (Quotient.mk'' (autRestrict hTα s)) =
          Quotient.mk'' (autRestrict hTα (autRestrict hTα s)) from rfl,
        show f (Quotient.mk'' (autRestrict hTα (autRestrict hTα s))) =
          Quotient.mk'' (autRestrict hTα (autRestrict hTα (autRestrict hTα s))) from rfl, e]
  have hX : Fintype.card (↥T ⧸ (fixSub α).subgroupOf T) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hbase : f ((1 : ↥T) : ↥T ⧸ (fixSub α).subgroupOf T) =
      ((1 : ↥T) : ↥T ⧸ (fixSub α).subgroupOf T) := by
    have h1 : autRestrict hTα 1 = 1 := Subtype.ext (map_one α)
    show ((autRestrict hTα 1 : ↥T) : ↥T ⧸ (fixSub α).subgroupOf T) = _
    rw [h1]
  have hfix := eq_of_pow_three_eq_one_of_card_three f hX hf3
    (((1 : ↥T) : ↥T ⧸ (fixSub α).subgroupOf T)) hbase
  have hthis := hfix (QuotientGroup.mk t)
  show QuotientGroup.mk t = QuotientGroup.mk (autRestrict hTα t)
  rw [← hthis]
  rfl

theorem coset_fixed {α : MulAut G} {T : Subgroup G} (hα : α ^ 3 = 1) (hTα : ∀ t ∈ T, α t ∈ T)
    (hidx : (fixSub α).relIndex T = 3) : ∀ t ∈ T, t⁻¹ * α t ∈ fixSub α := by
  intro t ht
  have h := autRestrict_quot_eq hα hTα hidx ⟨t, ht⟩
  have hmem := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [autRestrict] using hmem

theorem fix_normal {α : MulAut G} {T : Subgroup G} (hTα : ∀ t ∈ T, α t ∈ T)
    (hcos : ∀ t ∈ T, t⁻¹ * α t ∈ fixSub α) (hab : IsMulCommutative ↥(T ⊓ fixSub α)) :
    ∀ s ∈ T, ∀ x ∈ T ⊓ fixSub α, s * x * s⁻¹ ∈ T ⊓ fixSub α := by
  intro s hs x hx
  refine ⟨T.mul_mem (T.mul_mem hs hx.1) (T.inv_mem hs), ?_⟩
  set f := s⁻¹ * α s with hf
  have hfT : f ∈ T := T.mul_mem (T.inv_mem hs) (hTα s hs)
  have hfF : f ∈ fixSub α := hcos s hs
  have hcomm : f * x = x * f := by
    have := hab.is_comm.comm (⟨f, ⟨hfT, hfF⟩⟩ : ↥(T ⊓ fixSub α)) ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hαs : α s = s * f := by rw [hf]; group
  show α (s * x * s⁻¹) = s * x * s⁻¹
  rw [map_mul, map_mul, map_inv, hαs, mem_fixSub.mp hx.2]
  calc s * f * x * (s * f)⁻¹ = s * (f * x) * f⁻¹ * s⁻¹ := by group
    _ = s * (x * f) * f⁻¹ * s⁻¹ := by rw [hcomm]
    _ = s * x * s⁻¹ := by group

theorem commutator_fixed {α : MulAut G} {T : Subgroup G} (hH : ModelHyp α T) {t : G} (ht : t ∈ T) :
    t * (α t)⁻¹ ∈ T ⊓ fixSub α ∧ (t * (α t)⁻¹) ^ 3 = 1 := by
  have hcos := coset_fixed hH.cube hH.stable hH.index
  set f := t⁻¹ * α t with hf
  have hfT : f ∈ T := T.mul_mem (T.inv_mem ht) (hH.stable t ht)
  have hfF : f ∈ fixSub α := hcos t ht
  have hαf : α f = f := mem_fixSub.mp hfF
  have hαt : α t = t * f := by rw [hf]; group
  have h3 : ∀ x, α (α (α x)) = x := aut_cube_apply hH.cube
  have hu : t * (α t)⁻¹ = t * f⁻¹ * t⁻¹ := by rw [hαt]; group
  refine ⟨?_, ?_⟩
  · rw [hu]
    exact fix_normal hH.stable hcos hH.abelian t ht f⁻¹ ⟨T.inv_mem hfT, (fixSub α).inv_mem hfF⟩
  · have e1 : α (α t) = t * f * f := by rw [hαt, map_mul, hαf, hαt]
    have e2 : α (α (α t)) = t * f * f * f := by rw [e1, map_mul, map_mul, hαt, hαf]
    have h4 : t * (f * f * f) = t * 1 := by
      calc t * (f * f * f) = t * f * f * f := by group
        _ = t * 1 := by rw [← e2, h3 t, mul_one]
    have hf3 : f ^ 3 = 1 := by
      calc f ^ 3 = f * f * f := pow_three' f
        _ = 1 := mul_left_cancel h4
    rw [hu, conj_pow, inv_pow, hf3, inv_one, mul_one, mul_inv_cancel]

theorem fixSub_congr (e : G ≃* G') (α : MulAut G) :
    fixSub (MulAut.congr e α) = (fixSub α).map e.toMonoidHom := by
  symm
  refine TauCeti.map_fixedSubgroup_eq e ?_
  ext x
  simp [MulAut.congr_apply]

theorem ModelHyp.congr (e : G ≃* G') {α : MulAut G} {T : Subgroup G} (h : ModelHyp α T) :
    ModelHyp (MulAut.congr e α) (T.map e.toMonoidHom) := by
  have hcongr : ∀ x : G, (MulAut.congr e α) (e x) = e (α x) := by
    intro x
    simp [MulAut.congr_apply]
  refine
    { cube := by rw [← map_pow, h.cube, map_one]
      pgroup := h.pgroup.map e.toMonoidHom
      maximal := ?_
      stable := ?_
      nonabelian := fun hc => h.nonabelian ((CFSG.isMulCommutative_map_mulEquiv_iff e T).mp hc)
      moves := ?_
      index := ?_
      abelian := ?_ }
  · intro S hS hTS
    have hS0 : IsPGroup 3 ↥(S.map e.symm.toMonoidHom) := hS.map e.symm.toMonoidHom
    have hTS0 : T ≤ S.map e.symm.toMonoidHom := by
      intro x hx
      exact ⟨e x, hTS ⟨x, hx, rfl⟩, by simp⟩
    have h0 := h.maximal _ hS0 hTS0
    have : S = (S.map e.symm.toMonoidHom).map e.toMonoidHom := by
      ext x
      simp [Subgroup.mem_map]
    rw [this, h0]
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨α t, h.stable t ht, (hcongr t).symm⟩
  · obtain ⟨t, ht, hmv⟩ := h.moves
    refine ⟨e t, ⟨t, ht, rfl⟩, fun hc => hmv ?_⟩
    rw [hcongr, ← map_inv, ← map_mul] at hc
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    simpa only [map_mul] using hc (e g)
  · rw [fixSub_congr, Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact h.index
  · rw [fixSub_congr, ← Subgroup.map_inf_eq _ _ _ e.injective]
    exact (CFSG.isMulCommutative_map_mulEquiv_iff e (T ⊓ fixSub α)).mpr h.abelian

theorem sup_fixSub_congr (e : G ≃* G') (α : MulAut G) (T : Subgroup G) :
    (T.map e.toMonoidHom ⊔ fixSub (MulAut.congr e α) = ⊤) ↔ T ⊔ fixSub α = ⊤ := by
  rw [fixSub_congr, ← Subgroup.map_sup]
  constructor
  · intro h
    rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
    exact Subgroup.map_injective e.injective h
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ e.surjective

theorem ModelGen.congr (e : G ≃* G') (h : ModelGen G) : ModelGen G' :=
  fun α' T' hH' => (sup_fixSub_congr e.symm α' T').mp (h _ _ (ModelHyp.congr e.symm hH'))

end Abstract

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
