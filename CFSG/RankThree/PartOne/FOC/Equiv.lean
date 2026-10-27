module

public import CFSG.RankThree.PartOne.FOC.Transfer
import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL
import CFSG.RankThree.PartOne.S11c.Sec66TFamily
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut LocalRankLeTwo LocalRankAut)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

section Transport

variable {T T' : Type} [Group T] [Group T']

theorem localRankAut_of_equiv (e : T ≃* T') {p : ℕ} (hp : p.Prime) {β : MulAut T}
    (h : LocalRankAut p T β) : LocalRankAut p T' (MulAut.congr e β) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hβp hβinn R hR hRcard hRfix U hU1 hU2 hUβ hRU
  have hβp' : β ^ p = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, hβp, map_one]
  have hβinn' : β ∉ innerAut T := fun hmem =>
    hβinn ((Sec66T.mem_innerAut_congr e β).mpr hmem)
  have hβapp : ∀ y : T', (MulAut.congr e β) y = e (β (e.symm y)) := fun y => by
    simp [MulAut.congr_apply]
  refine h hβp' hβinn' (R.map e.symm.toMonoidHom)
    (IsElementaryAbelian.map (A := R) e.symm.toMonoidHom) ?_ ?_ (U.map e.symm.toMonoidHom) ?_
    (hU2.map _) ?_ ?_
  · rw [Subgroup.card_map_of_injective e.symm.injective, hRcard]
  · rintro _ ⟨r, hr, rfl⟩
    have h1 := hRfix r hr
    rw [hβapp] at h1
    show β (e.symm r) = e.symm r
    have := congrArg e.symm h1
    simpa using this
  · intro hbot
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.symm.injective).mp hbot)
  · rintro _ ⟨u, hu, rfl⟩
    have h1 := hUβ u hu
    rw [hβapp] at h1
    refine ⟨_, h1, ?_⟩
    simp
  · rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRU hr)) (e x)
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    exact h1

end Transport

section Main

variable {T T' : Type} [Group T] [Finite T] [Group T'] [Finite T']

theorem FieldInnerT.of_mulEquiv (e : T ≃* T') {p : ℕ} (hp : p.Prime) (h : FieldInnerT p T') :
    FieldInnerT p T := by
  intro hLR x β E hxp hβp hβx hβinn hE hxN hxnot hLie
  have hE' := isComponentOf_map_mulEquiv e hE
  rw [← Sec66T.fixSub_congr e β] at hE'
  refine h (Sec66T.localRankLeTwo_of_mulEquiv e hp hLR) (e x) (MulAut.congr e β)
    (E.map e.toMonoidHom) ?_ ?_ ?_ ?_ hE' ?_ ?_ ?_
  · rw [← map_pow, hxp, map_one]
  · rw [← map_pow, hβp, map_one]
  · show e (β (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hβx]
  · intro hnot
    exact localRankAut_of_equiv e hp
      (hβinn fun hmem => hnot ((Sec66T.mem_innerAut_congr e β).mpr hmem))
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨g, rfl⟩ := e.surjective y
    have h1 : e x * e g * (e x)⁻¹ = e (x * g * x⁻¹) := by simp
    rw [h1, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
    exact Subgroup.mem_normalizer_iff.mp hxN g
  · intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := PlaneInner.exists_mul_of_mem_sup_centralizer hmem
    apply hxnot
    have ha' : e.symm a ∈ E := Subgroup.mem_map_equiv.mp ha
    have hb' : e.symm b ∈ Subgroup.centralizer (E : Set T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact Subgroup.mem_centralizer_iff.mp hb (e k) ⟨k, hk, rfl⟩
    have hx : x = e.symm a * e.symm b := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hab
    rw [hx]
    exact Subgroup.mul_mem_sup ha' hb'
  · obtain ⟨t, n, f, hf, hmodel⟩ := hLie
    exact ⟨t, n, f, hf, lieModel_of_mulEquiv
      (Sec66T.centerQuotientCongr (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective))
      hmodel⟩

end Main

end CFSG.RankThree.PartOne.FOC
