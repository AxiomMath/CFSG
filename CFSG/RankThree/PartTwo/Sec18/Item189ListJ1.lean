module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListBasic
public import CFSG.RankThree.PartTwo.Sec18.Item189ListJ1Local
public import CFSG.GH74.Generic.BProg.B3.LocBalJ1

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Open (walterJ1)

section Abstract

variable {Y : Type} [Group Y] {X Q : Subgroup Y} {Γ : Subgroup (MulAut Y)} {x : Y}

theorem ListData189.eq_top_of_inner (h : ListData189 X Q Γ x)
    (hinn : ∀ φ : MulAut ↥X, ∃ g : ↥X, φ = MulAut.conj g) : X = ⊤ := by
  haveI := h.normal
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, hg⟩ := hinn (MulAut.conjNormal y)
  exact h.mem_of_conjNormal_inner hg

theorem ListData189.mem_normalizer_self [Finite Y] (h : ListData189 X Q Γ x) :
    x ∈ Subgroup.normalizer (Q : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have := h.inv _ h.conj_mem t ht
    simpa [MulAut.conj_apply] using this
  · intro ht
    have := h.inv _ (Γ.inv_mem h.conj_mem) _ ht
    simpa [MulAut.conj_apply, mul_assoc] using this

end Abstract

theorem J1_exists_invariant_sylow_of_equiv {Y : Type} [Group Y]
    (e : Y ≃* walterJ1) {x : Y} (hx3 : orderOf x = 3) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hxT : x ∈ Subgroup.normalizer (T : Set Y)) :
    ∃ S : Subgroup Y, T ≤ S ∧ IsPGroup 2 S ∧ x ∈ Subgroup.normalizer (S : Set Y) ∧
      Nat.card S = 8 := by
  obtain ⟨S', hTS', hS'2, hxS', hS'8⟩ := J1_exists_invariant_sylow (x := e x)
    (by rw [MulEquiv.orderOf_eq]; exact hx3) (T := T.map e.toMonoidHom) (hT.map _)
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective])
    (Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hxT))
  refine ⟨S'.map e.symm.toMonoidHom, fun t ht => ⟨e t, hTS' ⟨t, ht, rfl⟩, by simp⟩, hS'2.map _, ?_,
    by rw [Subgroup.card_map_of_injective e.symm.injective, hS'8]⟩
  have := Subgroup.le_normalizer_map e.symm.toMonoidHom (Subgroup.mem_map_of_mem _ hxS')
  simpa using this

theorem ListData189.gammaInv_of_normalizer_J1 {Y : Type} [Group Y]
    {X Q : Subgroup Y} {Γ : Subgroup (MulAut Y)} {x : Y} (h : ListData189 X Q Γ x)
    (e : Y ≃* walterJ1) (hinn : ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g) {S : Subgroup Y}
    (hxS : x ∈ Subgroup.normalizer (S : Set Y)) : GammaInv189 Γ S := by
  intro γ hγ s hs
  obtain ⟨g, rfl⟩ := hinn γ
  have hgx : g * x = x * g := by
    have := h.apply_x hγ
    rw [MulAut.conj_apply] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hg3 : g ^ 3 = 1 := by
    refine CFSG.GH74.Generic.BProg.B1.PilotS5.center_of_equiv e _ fun y => ?_
    have h3 := h.pow_three _ hγ
    have := congrArg (fun φ : MulAut Y => φ y) h3
    simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hzp : g ∈ Subgroup.zpowers x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (J1_mem_zpowers_of_commute (x := e x) (g := e g)
      (by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq) (by rw [← map_pow, hg3, map_one])
      (by rw [← map_mul, ← map_mul, hgx]))
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective (by rw [map_zpow, hk])⟩
  have hgS : g ∈ Subgroup.normalizer (S : Set Y) := Subgroup.zpowers_le.mpr hxS hzp
  exact (Subgroup.mem_normalizer_iff.mp hgS s).mp hs

theorem isSylowOf_top_of_card_eq_eight_J1 {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (e : Y ≃* walterJ1) (hS : IsPGroup 2 S) (hcard : Nat.card S = 8) :
    CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hS, ?_⟩
  have h1 : Nat.card S * S.index = Nat.card Y := Subgroup.card_mul_index S
  rw [Nat.card_congr e.toEquiv, CFSG.Walter.J1Props.J1_card, hcard] at h1
  rw [Subgroup.relIndex_top_right]
  have : S.index = 21945 := by omega
  rw [this]
  decide

theorem list189J1_of : List189J1 := by
  intro Y _ _ X Q Γ x h ⟨e⟩
  left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : ↥X ≃* walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hXtop : X = ⊤ :=
    h.eq_top_of_inner (CFSG.GH74.Generic.BProg.B3.LocBalJ1.forall_mulAut_inner_of_equiv e')
  let eY : Y ≃* walterJ1 :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hXtop).symm.trans e')
  have hinn := CFSG.GH74.Generic.BProg.B3.LocBalJ1.forall_mulAut_inner_of_equiv eY
  obtain ⟨S, hQS, hS2, hxS, hS8⟩ := J1_exists_invariant_sylow_of_equiv eY h.orderOf_eq
    h.isPGroup h.ne_bot h.mem_normalizer_self
  have hSQ : S = Q := h.maximal S hS2 hQS (h.gammaInv_of_normalizer_J1 eY hinn hxS)
  subst hSQ
  exact isSylowOf_top_of_card_eq_eight_J1 eY hS2 hS8

end CFSG.RankThree.PartTwo.Sec18
