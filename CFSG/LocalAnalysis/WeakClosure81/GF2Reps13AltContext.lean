module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenPhi
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

theorem odd_card_center_of_o2Trivial {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y) (hLY : L ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) : Odd (Nat.card (Subgroup.center ↥L)) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) fun f g h => MulEquiv.ext (congrFun h)
  let K : Subgroup (MulAut W) :=
    { carrier := {g | g ∈ L ∧ (∀ l ∈ L, g * l = l * g) ∧ g ^ 2 = 1}
      one_mem' := ⟨L.one_mem, fun l _ => by rw [one_mul, mul_one], one_pow 2⟩
      mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, fun l hl =>
        (Commute.mul_left (show Commute a l from ha.2.1 l hl)
          (show Commute b l from hb.2.1 l hl)).eq, by
        rw [Commute.mul_pow (show Commute a b from ha.2.1 b hb.1) 2, ha.2.2, hb.2.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, fun l hl =>
        (Commute.inv_left (show Commute a l from ha.2.1 l hl)).eq, by
        rw [inv_pow, ha.2.2, inv_one]⟩ }
  have hmemK : ∀ g, g ∈ K ↔ g ∈ L ∧ (∀ l ∈ L, g * l = l * g) ∧ g ^ 2 = 1 := fun g => Iff.rfl
  have hKn : (K.subgroupOf Y).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, hmemK] at hn ⊢
    obtain ⟨y, hy⟩ := g
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨hnorm y hy _ hn.1, fun l hl => ?_, by rw [conj_pow, hn.2.2, mul_one, mul_inv_cancel]⟩
    have hl' : y⁻¹ * l * y ∈ L := by simpa using hnorm y⁻¹ (Y.inv_mem hy) l hl
    have hc := hn.2.1 _ hl'
    calc y * ↑n * y⁻¹ * l = y * (↑n * (y⁻¹ * l * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * l * y) * ↑n) * y⁻¹ := by rw [hc]
      _ = l * (y * ↑n * y⁻¹) := by group⟩
  have hK2 : IsPGroup 2 K := fun g => ⟨1, Subtype.ext (by simpa using ((hmemK g).mp g.2).2.2)⟩
  have hKbot : K = ⊥ := hO2 K (fun g hg => hLY hg.1) hKn hK2
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 2
    (even_iff_two_dvd.mp hodd)
  have hzK : ((z : ↥L) : MulAut W) ∈ K := by
    refine (hmemK _).mpr ⟨(z : ↥L).2, fun l hl => ?_, ?_⟩
    · exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩)).symm
    · have h2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
      have := congrArg (fun c : ↥(Subgroup.center ↥L) => ((c : ↥L) : MulAut W)) h2
      simpa using this
  rw [hKbot, Subgroup.mem_bot] at hzK
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hzK)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem isHat_alt6_of_is135Context (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) (hZ : Subgroup.center ↥L ≠ ⊥) {n : ℕ}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n)) :
    IsHat ↥L ↥(alternatingGroup (Fin 6)) ∧ Nat.card W = 2 ^ 6 := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) fun f g h => MulEquiv.ext (congrFun h)
  obtain ⟨-, hO2, hLY, hF, hq, hirr⟩ := hctx
  have hnorm : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl => by
    rw [← hF] at hl ⊢
    exact conj_mem_fstar hy hl
  have : Nontrivial W := Subgroup.nontrivial_iff.mp (nontrivial_of_ne _ _ hirr.1.ne)
  exact isHat_alt6_of_altCover hW (Group.isPerfect_def.mp hq.1)
    (fun U hU => hirr.2.2.2 U hU bot_le le_top) (odd_card_center_of_o2Trivial hO2 hLY hnorm) hZ e
    (fun l hl => hnorm t htY l hl) ht2 hm

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

end
