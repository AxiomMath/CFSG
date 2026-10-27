module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.SwapO4Plus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4Plus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem commV_eq_top_of_singleton_conjSet {W : Type} [CommGroup W]
    {R Y : Subgroup (MulAut W)}
    (hsum : IsDirSumOver (conjSet R Y) commV) (hR1 : conjSet R Y = {R}) : commV R = ⊤ := by
  rw [eq_top_iff, ← hsum.2]
  refine iSup_le fun X => ?_
  have hX : (X : Subgroup (MulAut W)) = R :=
    Set.mem_singleton_iff.mp ((Set.ext_iff.mp hR1 _).mp X.2)
  rw [hX]

theorem w4Thm13_10_swapping {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L K : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (haL : IsAlt ↥L 5) (haK : IsAlt ↥K 5) (hne : L ≠ K)
    (hXn : ((L ⊔ K).subgroupOf Y).Normal)
    (hsw : ∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) {t : MulAut W}
    (htY : t ∈ Y) (ht2 : orderOf t = 2) (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (htL : L.map (MulAut.conj t).toMonoidHom = K) :
    NatOmegaPlus (L ⊔ K) ⊤ ⊥ 4 2 ∧
      ∀ c ∈ Y, (∀ x ∈ L ⊔ K, c * x = x * c) → c ^ 5 = 1 → c = 1 := by
  classical
  obtain ⟨R, hRY, hsum, hLR, hnat, hR1⟩ :=
    exists_o4Plus_of_swapping hW hO2 hB hcL hcK haL haK hne hXn hsw htY ht2 htm htL
  have hRtop : commV R = ⊤ := commV_eq_top_of_singleton_conjSet hsum hR1
  have hEq : (⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) = ⁅R, R⁆ :=
    Thm14_5.iSup_map_conj_eq_commutator hcL.2.2 hRY hLR hnat hR1
  have hSup : (⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) = L ⊔ K :=
    iSup_conj_eq_of_swap hcL hcK haL haK hne rfl hXn hsw
  have hC : ⁅R, R⁆ = L ⊔ K := hEq.symm.trans hSup
  have hnat' : NatOmegaPlus (L ⊔ K) ⊤ ⊥ 4 2 := by
    have h := (Thm14_5.isOmegaPlus_natOmegaPlus_commutator hnat hRtop).2
    rwa [hC] at h
  refine ⟨hnat', ?_⟩
  have hrk : rk W = 8 := by
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c1610_rk_natOmegaPlus hnat'
    rw [rk_top] at h
    norm_num at h
    exact h
  intro c _ hcX hc5
  by_contra hc1
  have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hcomm : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a :=
    B69.components_mul_comm_of_ne hcK hcL hne.symm
  exact false_of_commute_orderOf_five hW hrk haL haK hcomm hord hcX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
