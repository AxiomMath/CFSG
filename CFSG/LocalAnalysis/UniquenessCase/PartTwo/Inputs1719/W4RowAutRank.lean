module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRank
import CFSG.Quasithin.Background.E3AParamCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.Blueprint

theorem W4Row.card_le_of_sq_eq_one_of_fstar {W : Type} [CommGroup W] [Finite W]
    {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L) (hO2 : O2Trivial L) (hAY : A ≤ Y)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {S : Type} [Group S] (e : CQ L ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r) :
    Nat.card A ≤ 2 ^ r := by
  have hA := W4Row.isElemAbelian2_of_sq_eq_one hA2
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hAs : A ≤ L ⊔ Y := hAY.trans le_sup_right
  let f : ↥A →* MulAut S := (actS hY e).comp (Subgroup.inclusion hAs)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, actS_apply] at ha
    have h1 : actionOnCQ (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY)
        (Subgroup.inclusion hAs a) = 1 :=
      (MulAut.congr e).injective (by rw [ha, map_one])
    have h2 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ Y)
      (normal_sup_of_le_normalizer hY) hperf _).1 h1
    have haL : (a : MulAut W) ∈ L :=
      W4Row.mem_of_mem_centralizer_of_fstar_eq hLY hF (hAY a.2) h2
    have hmem : (⟨(a : MulAut W), haL⟩ : ↥L) ∈ A.subgroupOf L ⊓ Subgroup.center ↥L :=
      ⟨Subgroup.mem_subgroupOf.2 a.2, Subgroup.mem_center_iff.2 fun z =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 z z.2)⟩
    rw [W4Row.subgroupOf_inf_center_eq_bot_of_o2Trivial hO2 hA, Subgroup.mem_bot] at hmem
    have h5 : (a : MulAut W) = 1 := congrArg Subtype.val hmem
    exact Subtype.ext h5
  have hcard : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  rw [← hcard]
  refine hr f.range ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : a * b = b * a := Subtype.ext (hA.1 _ a.2 _ b.2)
    rw [← map_mul, hab, map_mul]
  · rintro _ ⟨a, rfl⟩
    have ha : a * a = 1 := Subtype.ext (by simpa [sq] using hA2 _ a.2)
    rw [← map_mul, ha, map_one]

theorem w4Thm11_1RowA_of_autRank {s : TauCeti.SporadicName}
    (hr : ∀ B : Subgroup (MulAut (NativeSporadic.Carrier s)), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ tableA s) :
    W4Thm11_1RowA s := by
  intro W _ _ _ Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  exact E3.aParam_le_of_card_le Y fun A hAY hA2 =>
    W4Row.card_le_of_sq_eq_one_of_fstar hLY hLn hF hq.1 hO2 hAY hA2 e₀ hr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
