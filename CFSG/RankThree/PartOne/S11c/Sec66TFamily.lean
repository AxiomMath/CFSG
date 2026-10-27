module

public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.RankThree.PartOne.S11c.Sec66TGroup
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG Subgroup CFSG.Blueprint
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.RankThreeCoreUniqueness.Helpers (finite_perfectResidual_isPerfect)

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem congr_conj (e : G ≃* G') (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  apply MulEquiv.ext
  intro x
  change e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem fixSub_congr (e : G ≃* G') (α : MulAut G) :
    fixSub (MulAut.congr e α) = (fixSub α).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have h : e (α (e.symm x)) = x := hx
    show α (e.symm x) = e.symm x
    have := congrArg e.symm h
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have h : α y = y := hy
    show e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply, h]

noncomputable def fixSubEquiv (e : G ≃* G') (α : MulAut G) :
    ↥(fixSub α) ≃* ↥(fixSub (MulAut.congr e α)) :=
  (Subgroup.equivMapOfInjective (fixSub α) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (fixSub_congr e α).symm)

theorem orderOf_congr (e : G ≃* G') (α : MulAut G) : orderOf (MulAut.congr e α) = orderOf α :=
  MulEquiv.orderOf_eq (MulAut.congr e) α

theorem mem_innerAut_congr (e : G ≃* G') (α : MulAut G) :
    MulAut.congr e α ∈ innerAut G' ↔ α ∈ innerAut G := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e.symm q, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, e.apply_symm_apply]
    exact hq
  · rintro ⟨q, rfl⟩
    exact ⟨e q, (congr_conj e q).symm⟩

theorem congr_self_eq (ψ α : MulAut G) : MulAut.congr (ψ : G ≃* G) α = ψ * α * ψ⁻¹ := rfl

end Transport

section Models

variable {T : Type} [Group T]

theorem isPerfect_of_simple_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Group.IsPerfect X := by
  have hn : (commutator X).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ commutator X := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at h1
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · exact ⟨h⟩

theorem center_eq_bot_of_simple' {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
    exact ((Subgroup.mem_center_iff.mp ha) b).symm

theorem inSubgroup_perfectResidual_eq_of_normal {X : Type*} [Group X] [Finite X]
    {W N : Subgroup X} (hNW : N ≤ W) (hN : (N.subgroupOf W).Normal) (hperf : Group.IsPerfect ↥N)
    (hsolv : Group.IsSolvable (↥W ⧸ N.subgroupOf W)) : inSubgroup perfectResidual W = N := by
  have hres : perfectResidual ↥W ≤ N.subgroupOf W :=
    ((perfect_residual_characterization (G := ↥W)).2.2.2.2.1 (N.subgroupOf W)).mp hsolv
  have hperf' : Group.IsPerfect ↥(N.subgroupOf W) := by
    have := hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hNW).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNW).symm.surjective
  have hsub : N.subgroupOf W ≤ perfectResidual ↥W :=
    (perfect_residual_transport (MonoidHom.id ↥W)).2.2 (N.subgroupOf W) hperf'
  apply le_antisymm
  · exact (Subgroup.map_mono hres).trans (le_of_eq (Subgroup.map_subgroupOf_eq_of_le hNW))
  · rw [← Subgroup.map_subgroupOf_eq_of_le hNW]
    exact Subgroup.map_mono hsub

noncomputable def centerQuotientEquivSelf {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem lieModel_fixRes_of_normal [Finite T] {α : MulAut T} {N : Subgroup T}
    (hNW : N ≤ fixSub α) (hN : (N.subgroupOf (fixSub α)).Normal) (hperf : Group.IsPerfect ↥N)
    (hsolv : Group.IsSolvable (↥(fixSub α) ⧸ N.subgroupOf (fixSub α))) {X : Type} [Group X]
    (e : ↥N ⧸ Subgroup.center ↥N ≃* X) {t : Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (hX : LieModel X t n 2 f) :
    LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) t n 2 f := by
  have h : fixRes α = N := inSubgroup_perfectResidual_eq_of_normal hNW hN hperf hsolv
  exact lieModel_of_mulEquiv
    (((centerQuotientCongr (MulEquiv.subgroupCongr h)).trans e).symm) hX

theorem lieModel_fixRes_of_simple [Finite T] {α : MulAut T} {X : Type} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (e : ↥(fixSub α) ≃* X)
    {t : Assembly.LowTwoRank.StatedLieTag} {n f : ℕ} (hX : LieModel X t n 2 f) :
    LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) t n 2 f := by
  have hsimple : IsSimpleGroup ↥(fixSub α) := e.isSimpleGroup
  have hnab' : ∃ a b : ↥(fixSub α), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hperf : Group.IsPerfect ↥(fixSub α) := isPerfect_of_simple_nonabelian hnab'
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_simple' hnab
  have hN : ((fixSub α).subgroupOf (fixSub α)).Normal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolv : Group.IsSolvable (↥(fixSub α) ⧸ (fixSub α).subgroupOf (fixSub α)) := by
    have : Subsingleton (↥(fixSub α) ⧸ (fixSub α).subgroupOf (fixSub α)) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (x⁻¹ * y).2
    exact inferInstance
  exact lieModel_fixRes_of_normal le_rfl hN hperf hsolv
    ((centerQuotientCongr e).trans (centerQuotientEquivSelf hZ)) hX

end Models

section Plane

variable {T : Type} [Group T]

theorem card_le_of_cyclic_elementaryAbelian {p : ℕ} (hp : p.Prime) {E : Type*} [Group E]
    [Finite E] [IsCyclic E] (hE : IsElementaryAbelian p E) : Nat.card E ≤ p := by
  have h1 : Monoid.exponent E = Nat.card E := IsCyclic.exponent_eq_card
  have h2 : Monoid.exponent E ∣ p := hE.exponent_dvd_p
  rw [h1] at h2
  exact Nat.le_of_dvd hp.pos h2

theorem no_plane_of_cyclic_quotient {p : ℕ} (hp : p.Prime) {Γ : Type*} [Group Γ] [IsCyclic Γ]
    (φ : MulAut T →* Γ) (hφ : ∀ x ∈ φ.ker, x ^ p = 1 → x ∈ innerAut T)
    (E : Subgroup (MulAut T)) (hE : IsElementaryAbelian p ↥E) (hcard : Nat.card E = p ^ 2)
    (hEinn : E ⊓ innerAut T = ⊥) : False := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : φ (x : MulAut T) = 1 := hx
    have hxp : (x : MulAut T) ^ p = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x
      exact congrArg Subtype.val this
    have hinn := hφ (x : MulAut T) (MonoidHom.mem_ker.mpr hx1) hxp
    have hmem : (x : MulAut T) ∈ E ⊓ innerAut T := ⟨x.2, hinn⟩
    rw [hEinn, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hcyc : IsCyclic E := isCyclic_of_injective (φ.comp E.subtype) hinj
  have hle := card_le_of_cyclic_elementaryAbelian hp hE
  rw [hcard] at hle
  have : p < p ^ 2 := by nlinarith [hp.two_le]
  omega

end Plane


end CFSG.RankThree.PartOne.Sec66T
