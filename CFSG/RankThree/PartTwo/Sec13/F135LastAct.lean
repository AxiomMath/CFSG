module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Subgroup

@[expose] noncomputable def centerQuotMulAut (H : Type*) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun σ := QuotientGroup.congr _ _ σ
    (Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center H).Characteristic) σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def actS {M' : Type*} [Group M'] (J : Subgroup M') :
    Subgroup.normalizer (J : Set M') →* MulAut (J ⧸ Subgroup.center J) :=
  (centerQuotMulAut J).comp J.normalizerMonoidHom

theorem actS_mk {M' : Type*} [Group M'] (J : Subgroup M') (n : Subgroup.normalizer (J : Set M'))
    (x : J) : actS J n (x : J ⧸ Subgroup.center J) =
      ((⟨(n : M') * x * (n : M')⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩ : J) :
        J ⧸ Subgroup.center J) :=
  rfl

theorem act_conj_central {G : Type*} [Group G] {p : G} (hp : ∀ x : G, x * p = p * x) (g y : G) :
    g * p * y * (g * p)⁻¹ = g * y * g⁻¹ := by
  have h1 : p * y = y * p := (hp y).symm
  calc g * p * y * (g * p)⁻¹ = g * (p * y) * p⁻¹ * g⁻¹ := by group
    _ = g * (y * p) * p⁻¹ * g⁻¹ := by rw [h1]
    _ = g * y * g⁻¹ := by group

open scoped commutatorElement in
theorem act_comm_central {G : Type*} [Group G] {p q : G} (hp : ∀ x : G, x * p = p * x)
    (hq : ∀ x : G, x * q = q * x) (a b : G) : ⁅a * p, b * q⁆ = ⁅a, b⁆ := by
  calc ⁅a * p, b * q⁆ = (a * p) * (b * q) * (a * p)⁻¹ * (b * q)⁻¹ := by
        rw [commutatorElement_def]
    _ = a * (b * q) * a⁻¹ * (b * q)⁻¹ := by rw [act_conj_central hp]
    _ = a * ((b * q) * a⁻¹ * (b * q)⁻¹) := by group
    _ = a * (b * a⁻¹ * b⁻¹) := by rw [act_conj_central hq]
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group

open scoped commutatorElement in
theorem act_eq_of_perfect {G : Type*} [Group G] (hG : Group.IsPerfect G) (σ : MulAut G)
    (h : ∀ x : G, ∃ p ∈ Subgroup.center G, σ x = x * p) : ∀ x : G, σ x = x := by
  have hcomm : ∀ a b : G, σ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨p, hp, hpa⟩ := h a
    obtain ⟨q, hq, hqb⟩ := h b
    rw [map_commutatorElement, hpa, hqb]
    exact act_comm_central (Subgroup.mem_center_iff.mp hp) (Subgroup.mem_center_iff.mp hq) a b
  let S : Subgroup G :=
    { carrier := {x | σ x = x}
      mul_mem' := fun {a b} ha hb => by
        show σ (a * b) = a * b
        rw [map_mul, show σ a = a from ha, show σ b = b from hb]
      one_mem' := by
        show σ 1 = 1
        exact map_one σ
      inv_mem' := fun {a} ha => by
        show σ a⁻¹ = a⁻¹
        rw [map_inv, show σ a = a from ha] }
  have hS : _root_.commutator G ≤ S := Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  rw [hG.commutator_eq_top] at hS
  intro x
  exact hS (Subgroup.mem_top x)

theorem actS_eq_one_iff {M' : Type*} [Group M'] {J : Subgroup M'} (hJ : Group.IsPerfect J)
    (n : Subgroup.normalizer (J : Set M')) :
    actS J n = 1 ↔ (n : M') ∈ Subgroup.centralizer (J : Set M') := by
  constructor
  · intro h
    have hz : ∀ x : J, ∃ p ∈ Subgroup.center J, J.normalizerMonoidHom n x = x * p := by
      intro x
      have hx : actS J n (x : J ⧸ Subgroup.center J) = (x : J ⧸ Subgroup.center J) := by
        rw [h, MulAut.one_apply]
      have hx' : ((J.normalizerMonoidHom n x : J) : J ⧸ Subgroup.center J) =
          (x : J ⧸ Subgroup.center J) := hx
      have hc : (J.normalizerMonoidHom n x)⁻¹ * x ∈ Subgroup.center J := QuotientGroup.eq.mp hx'
      exact ⟨((J.normalizerMonoidHom n x)⁻¹ * x)⁻¹, inv_mem hc, by group⟩
    have hfix := act_eq_of_perfect hJ (J.normalizerMonoidHom n) hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hfix' : J.normalizerMonoidHom n ⟨g, hg⟩ = ⟨g, hg⟩ := hfix ⟨g, hg⟩
    have e : (n : M') * g * (n : M')⁻¹ = g := congrArg Subtype.val hfix'
    calc g * (n : M') = ((n : M') * g * (n : M')⁻¹) * (n : M') := by rw [e]
      _ = (n : M') * g := by group
  · intro hn
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      have hx : (⟨(n : M') * (x : M') * (n : M')⁻¹,
          (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩ : J) = x := by
        apply Subtype.ext
        have hc : (x : M') * (n : M') = (n : M') * (x : M') :=
          Subgroup.mem_centralizer_iff.mp hn (x : M') x.2
        show (n : M') * (x : M') * (n : M')⁻¹ = (x : M')
        rw [← hc]
        group
      rw [actS_mk, hx, MulAut.one_apply]

end CFSG.RankThree.PartTwo.Sec13.F135Last
