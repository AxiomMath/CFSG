module

public import CFSG.RankThree.PartOne.LSTD.Center

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.LSTD

theorem exists_hopf_equiv {S X : Type} [Group S] [Finite S] [Group.IsPerfect S] [Group X]
    [Finite X] [Group.IsPerfect X] (p : X →* S) (hp : Function.Surjective p)
    (hC : p.ker ≤ Subgroup.center X) (hcard : Nat.card p.ker = Nat.card (hopfMultiplier S)) :
    ∃ e : HopfCover S ≃* X, ∀ u, p (e u) = hopfCoverMap S u := by
  obtain ⟨-, h, hh, -, hsurj, hmap, -⟩ := perfect_central_kernel_quotient_of_hopf_multiplier
    p hp hC
  have hinjM : Function.Injective (h.comp (hopfMultiplier S).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
    have h1 := Subgroup.card_ker_mul_card_range (h.comp (hopfMultiplier S).subtype)
    have hr : (h.comp (hopfMultiplier S).subtype).range = p.ker := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    rw [hr, Nat.card_congr (Equiv.refl _), ← hcard] at h1
    have hpos : 0 < Nat.card p.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (one_mul _).symm)
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hM : u ∈ hopfMultiplier S := by
      show hopfCoverMap S u = 1
      rw [← hh, MonoidHom.comp_apply, hu, map_one]
    have := hinjM (a₁ := ⟨u, hM⟩) (a₂ := 1) (by simpa using hu)
    exact congrArg Subtype.val this
  refine ⟨MulEquiv.ofBijective h ⟨hinj, hsurj⟩, fun u => ?_⟩
  show p (h u) = _
  rw [← hh]
  rfl

theorem hopf_data_psu_five (hGA : CFSG.Open.GriessAllModelsStatement)
    {S : Type} [Group S] {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) (hmodel : StatedClassicalModel S .PSU 5 2 f) :
    Group.IsPerfect S ∧ Nat.card (hopfMultiplier S) = 5 := by
  have hm : Models.LieModel S .PSU 5 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSU 5 2 f hm
  have : Group.IsPerfect S := ⟨hcomm⟩
  refine ⟨this, ?_⟩
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv,
    card_multiplier_psu_five h5]

theorem exists_iso_of_central_extensions
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {S X Y : Type} [Group S] [Finite S] [Group X] [Finite X] [Group.IsPerfect X] [Group Y]
    [Finite Y] [Group.IsPerfect Y] {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1)
    (hmodel : StatedClassicalModel S .PSU 5 2 f) (p : X →* S) (hp : Function.Surjective p)
    (hpC : p.ker ≤ Subgroup.center X) (hpcard : Nat.card p.ker = 5) (q : Y →* S)
    (hq : Function.Surjective q) (hqC : q.ker ≤ Subgroup.center Y) (hqcard : Nat.card q.ker = 5) :
    ∃ ψ : Y ≃* X, ∀ y, p (ψ y) = q y := by
  obtain ⟨hperf, hM⟩ := hopf_data_psu_five hGA h5 hmodel
  have : Group.IsPerfect S := hperf
  obtain ⟨eX, heX⟩ := exists_hopf_equiv p hp hpC (hpcard.trans hM.symm)
  obtain ⟨eY, heY⟩ := exists_hopf_equiv q hq hqC (hqcard.trans hM.symm)
  refine ⟨eY.symm.trans eX, fun y => ?_⟩
  show p (eX (eY.symm y)) = q y
  rw [heX, ← heY, MulEquiv.apply_symm_apply]

end CFSG.RankThree.PartOne.U5LIFT
