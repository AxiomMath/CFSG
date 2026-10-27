module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

@[expose] def pslRep {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {G : Type} [Group G] (φ : G →* ↥L) :
    Representation (ZMod 2) G (Additive W) :=
  mulAutLinearHom.comp (L.subtype.comp φ)

theorem pslRep_apply {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {G : Type} [Group G] (φ : G →* ↥L) (x : G) :
    pslRep φ x = mulAutLinear ((φ x : ↥L) : MulAut W) :=
  rfl

theorem w135c2_exists_involution_lift {G H : Type} [Group G] [Group H] (φ : G →* H)
    (hker : Odd (Nat.card φ.ker)) {t : H} (ht : orderOf t = 2) (hrange : t ∈ φ.range) :
    ∃ y : G, y * y = 1 ∧ y ≠ 1 ∧ φ y = t := by
  obtain ⟨x, hx⟩ := hrange
  have hpos : Nat.card φ.ker ≠ 0 := hker.pos.ne'
  haveI : Finite φ.ker := Nat.finite_of_card_ne_zero hpos
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hx2 : x ^ 2 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hx, ht2]
  have hc : (⟨x ^ 2, hx2⟩ : φ.ker) ^ Nat.card φ.ker = 1 := pow_card_eq_one'
  have hxc : (x ^ 2) ^ Nat.card φ.ker = 1 := congrArg Subtype.val hc
  have hy2 : x ^ Nat.card φ.ker * x ^ Nat.card φ.ker = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hxc]
  have hphi : φ (x ^ Nat.card φ.ker) = t := by
    obtain ⟨a, ha⟩ := hker
    rw [map_pow, hx, ha, pow_succ, pow_mul, ht2, one_pow, one_mul]
  refine ⟨x ^ Nat.card φ.ker, hy2, fun h1 => ?_, hphi⟩
  have h1' : t = 1 := by rw [← hphi, h1, map_one]
  rw [h1', orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem w135c2_psl_finrank_range {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {L : Subgroup (MulAut W)} {G : Type} [Group G]
    (φ : G →* ↥L) (y : G) :
    Module.finrank (ZMod 2) (LinearMap.range (pslRep φ y - 1)) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers ((φ y : ↥L) : MulAut W))) :=
  (mQuot_fixV_zpowers_eq_finrank_range_sub_one _).symm

end CFSG.LocalAnalysis.WeakClosure81
