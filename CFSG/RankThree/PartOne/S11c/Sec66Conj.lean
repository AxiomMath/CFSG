module

public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

theorem lieModel_fixRes_congr {T T' : Type} [Group T] [Group T'] [Finite T] [Finite T']
    {α : MulAut T} {β : MulAut T'} (e : ↥(fixSub α) ≃* ↥(fixSub β)) {t : StatedLieTag}
    {n f : ℕ} (h : LieModel (↥(fixRes β) ⧸ Subgroup.center ↥(fixRes β)) t n 2 f) :
    LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) t n 2 f := by
  obtain ⟨e'⟩ := nonempty_centerQuotient_perfectResidual_equiv (fixSub α) (fixSub β)
    e.toMonoidHom e.surjective (by
      intro x hx
      have hx1 : e x = 1 := hx
      have : x = 1 := e.injective (by rw [hx1, map_one])
      rw [this]
      exact Subgroup.one_mem _)
  exact lieModel_of_mulEquiv e'.symm h

theorem fixSub_eq_of_zpowers_eq {T : Type} [Group T] {β β' : MulAut T}
    (h : Subgroup.zpowers β = Subgroup.zpowers β') : fixSub β = fixSub β' := by
  have key : ∀ (γ γ' : MulAut T), γ' ∈ Subgroup.zpowers γ → fixSub γ ≤ fixSub γ' := by
    intro γ γ' hγ x hx
    obtain ⟨i, rfl⟩ := hγ
    have hfix : γ x = x := hx
    have hn : ∀ n : ℕ, (γ ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ, MulAut.mul_apply, hfix]
        exact ih
    show (γ ^ i) x = x
    rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]
      exact hn n
    · rw [zpow_neg, zpow_natCast]
      have h1 := hn n
      apply (γ ^ n).injective
      rw [MulAut.apply_inv_self]
      exact h1.symm
  exact le_antisymm (key β β' (h ▸ Subgroup.mem_zpowers β'))
    (key β' β (h.symm ▸ Subgroup.mem_zpowers β))

theorem fieldAutT_of_conj_fix' {T C : Type} [Group T] [Group C] [Finite T] [Finite C]
    {p f f' n : ℕ} {t : StatedLieTag} (e : T ≃* C) (hM : LieModel T t n 2 f) (hff' : f = p * f')
    (hf' : 1 ≤ f') (α : MulAut T) (β ψ : MulAut C)
    (hψ : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β)
    (hfix : LieModel (↥(fixRes β) ⧸ Subgroup.center ↥(fixRes β)) t n 2 f') :
    FieldAutT p α := by
  have e12 : ↥(fixSub α) ≃* ↥(fixSub β) :=
    ((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ)
  refine ⟨t, n, f', hf', ?_, Or.inl (lieModel_fixRes_congr e12 hfix)⟩
  rw [← hff']
  exact hM

theorem fieldAutT_of_conj_fix {T C : Type} [Group T] [Group C] [Finite T] [Finite C]
    {p f f' n : ℕ} {t : StatedLieTag} (e : T ≃* C) (hM : LieModel T t n 2 f) (hff' : f = p * f')
    (hf' : 1 ≤ f') (α : MulAut T) (β ψ : MulAut C) (hψ : ψ * MulAut.congr e α * ψ⁻¹ = β)
    (hfix : LieModel (↥(fixRes β) ⧸ Subgroup.center ↥(fixRes β)) t n 2 f') :
    FieldAutT p α :=
  fieldAutT_of_conj_fix' e hM hff' hf' α β ψ (by rw [hψ]) hfix

end CFSG.RankThree.PartOne.Sec66T
