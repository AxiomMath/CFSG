module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltContext
public import CFSG.Quasithin.Background.SmithB45ExcJ4
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint

theorem w4Thm11_1RowM_J4_holds :
    W4Thm11_1RowM .J4 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  show 50 ≤ E3.mParam Y
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have : Group.IsPerfect ↥L := hq.1
  let π : ↥L →* NativeSporadic.Carrier .J4 :=
    (e : CQ L →* NativeSporadic.Carrier .J4).comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hK : π.ker = Subgroup.center ↥L := by
    ext k
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk k) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hK]
    exact CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt.odd_card_center_of_o2Trivial hO2 le_rfl
      fun y hy l hl => L.mul_mem (L.mul_mem hy hl) (L.inv_mem hy)
  have hπi : Function.Injective π :=
    (MonoidHom.ker_eq_bot_iff π).1 (X1.j4_cover ↥L π hπs hK.le hodd)
  let f : ↥L ≃* NativeSporadic.Carrier .J4 := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let σ : NativeSporadic.Carrier .J4 →* MulAut W := L.subtype.comp f.symm.toMonoidHom
  have hσ : Function.Injective σ := L.subtype_injective.comp f.symm.injective
  have hYL : ∀ t ∈ Y, t * t = 1 → t ∈ L := by
    intro t htY ht2
    refine W4Row.mem_of_actS_inner_of_fstar hLY hF hq.1 hY e htY ?_
    have hφ : ∀ x, X1.actS hY e ⟨t, Subgroup.mem_sup_right htY⟩
        (X1.actS hY e ⟨t, Subgroup.mem_sup_right htY⟩ x) = x := by
      intro x
      rw [← MulAut.mul_apply, ← map_mul,
        show (⟨t, Subgroup.mem_sup_right htY⟩ : ↥(L ⊔ Y)) * ⟨t, Subgroup.mem_sup_right htY⟩ = 1
          from Subtype.ext ht2, map_one, MulAut.one_apply]
    obtain ⟨s, hs⟩ := X1.autInner_of_outer_odd X1.j4OuterOdd _ hφ
    exact ⟨s, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hs x]⟩
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2 : 2 ∣ Nat.card ↥L := by
      rw [Nat.card_congr f.toEquiv]
      change 2 ∣ Nat.card NativeSporadic.J4
      rw [CFSG.Sporadic.J4.card_J4]
      norm_num
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2
    exact ⟨t, hLY t.2, by rwa [Subgroup.orderOf_coe]⟩
  refine W4Row.le_mParam_of_index_sq hW' hY2 fun t htY hto => ?_
  have ht2 : t * t = 1 := by
    rw [← sq, ← hto]
    exact pow_orderOf_eq_one t
  have htL := hYL t htY ht2
  have ht1 : f ⟨t, htL⟩ ≠ 1 := fun h1 => by
    have : (⟨t, htL⟩ : ↥L) = 1 := f.injective (by rw [h1, map_one])
    have ht : t = 1 := congrArg Subtype.val this
    rw [ht, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hf2 : f ⟨t, htL⟩ * f ⟨t, htL⟩ = 1 := by
    rw [← map_mul, show (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 from Subtype.ext ht2, map_one]
  have hσt : σ (f ⟨t, htL⟩) = t := by
    change L.subtype (f.symm (f ⟨t, htL⟩)) = t
    rw [MulEquiv.symm_apply_apply]
    rfl
  have h50 := CFSG.Quasithin.B45Exc.j4MovedRank50 W hW' σ hσ _ ht1 hf2
  rw [hσt] at h50
  calc 2 ^ (2 * 50) = (2 ^ 50) ^ 2 := by rw [← pow_mul, mul_comm]
    _ ≤ _ := Nat.pow_le_pow_left h50 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
