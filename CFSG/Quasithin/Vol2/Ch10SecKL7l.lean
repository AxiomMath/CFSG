module

public import CFSG.Quasithin.Vol2.Ch10SecKL7k

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem comm_sub : ∀ (a : ↥L₁) (b : ↥L₂), Commute (L₁.subtype a) (L₂.subtype b) :=
  fun a b => h.comm' a.2 b.2

theorem injective_mul :
    Function.Injective (L₁.subtype.noncommCoprod L₂.subtype h.comm_sub) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hab
  have hab' : (a : MulAut W) * b = 1 := hab
  have ha : (a : MulAut W) ∈ L₁ ⊓ L₂ := ⟨a.2, by
    rw [eq_inv_of_mul_eq_one_left hab']
    exact L₂.inv_mem b.2⟩
  rw [h.inf_L, Subgroup.mem_bot] at ha
  have hb : (b : MulAut W) = 1 := by rw [ha, one_mul] at hab'; exact hab'
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem range_mul :
    (L₁.subtype.noncommCoprod L₂.subtype h.comm_sub).range = L₁ ⊔ L₂ := by
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

variable (hR : RHyp Mb L₁ L₂ R)
include hR

theorem aSet_mQuot_le {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Mb) :
    E3.mQuot A (A ⊓ fixingSubgroup (MulAut W) (W₁ : Set W)) ≤ 2 := by
  obtain ⟨c₁⟩ := h.coord
  have : Finite ↥L₁ := Nat.finite_of_card_ne_zero (by rw [c₁.card_L]; norm_num)
  set μ := L₁.subtype.noncommCoprod L₂.subtype h.comm_sub with hμ
  have hA' : A ≤ μ.range := by
    rw [h.range_mul]
    exact fun a ha => h.aSet_mem_sup hR hA ha
  let e := MonoidHom.ofInjective h.injective_mul
  let f : ↥A →* ↥L₁ :=
    (MonoidHom.fst ↥L₁ ↥L₂).comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hA'))
  have hμf : ∀ x : ↥A, ((f x : ↥L₁) : MulAut W) * ((e.symm (Subgroup.inclusion hA' x)).2 :
      MulAut W) = x := fun x => by
    have := congrArg Subtype.val (e.apply_symm_apply (Subgroup.inclusion hA' x))
    exact this
  have hker : f.ker = (A ⊓ fixingSubgroup (MulAut W) (W₁ : Set W)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_fixingSubgroup_iff]
    have hx := hμf x
    set p₁ := f x
    set p₂ := (e.symm (Subgroup.inclusion hA' x)).2
    have hxw : ∀ w ∈ W₁, (x : MulAut W) w = (p₁ : MulAut W) w := fun w hw => by
      rw [← hx, MulAut.mul_apply, h.fix₂ _ p₂.2 w hw]
    constructor
    · intro h1
      refine ⟨x.2, fun w hw => ?_⟩
      show (x : MulAut W) w = w
      rw [hxw w hw, h1]
      rfl
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      exact h.eq_one_of_fix (fun w hw => by rw [← hxw w hw]; exact h1 w hw)
        (fun w hw => h.fix₁ _ p₁.2 w hw)
  have hidx : (A ⊓ fixingSubgroup (MulAut W) (W₁ : Set W)).relIndex A = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hcard : Nat.card f.range ≤ 4 := by
    rw [← Subgroup.card_map_of_injective (f := c₁.π.symm.toMonoidHom) c₁.π.symm.injective]
    refine card_le_four_of_sq_eq_one _ ?_
    rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (hA.2.2.1.2 _ x.2)
    rw [← map_pow, ← map_pow, hx2, map_one, map_one]
  rw [E3.mQuot, hidx]
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h2 : 2 ^ padicValNat 2 (Nat.card f.range) ≤ 2 ^ 2 :=
    (Nat.le_of_dvd hpos pow_padicValNat_dvd).trans (by omega)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem aSet_three_eq_empty : E3.aSet 3 Mb = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA3
  have hA2 : A ∈ E3.aSet 2 Mb :=
    ⟨hA3.1, hA3.2.1, hA3.2.2.1, fun B hB hlt => hA3.2.2.2 B hB (by omega)⟩
  have h1 := hA3.2.2.2 (A ⊓ fixingSubgroup (MulAut W) (W₁ : Set W)) inf_le_left
    (by have := h.aSet_mQuot_le hR hA2; omega)
  have h2 := hA3.2.2.2 (A ⊓ fixingSubgroup (MulAut W) (W₂ : Set W)) inf_le_left
    (by have := h.swap.aSet_mQuot_le hR.swap hA2; omega)
  apply hA3.2.1
  refine eq_bot_iff.2 fun a ha => h.eq_one_of_fix (fun w hw => ?_) (fun w hw => ?_)
  · have hw' : w ∈ fixV (A ⊓ fixingSubgroup (MulAut W) (W₁ : Set W)) :=
      fun b hb => (mem_fixingSubgroup_iff _).1 hb.2 w hw
    exact (h1 ▸ hw') a ha
  · have hw' : w ∈ fixV (A ⊓ fixingSubgroup (MulAut W) (W₂ : Set W)) :=
      fun b hb => (mem_fixingSubgroup_iff _).1 hb.2 w hw
    exact (h2 ▸ hw') a ha

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
