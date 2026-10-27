module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

omit [Finite G] in
theorem gamma_ker (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (ggGamma L hN).ker = (Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem gamma_card (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggGamma L hN).range = ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index := by
  rw [← Subgroup.index_ker, gamma_ker]

theorem gamma_hyps (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian p (ggGamma L hN).range ∧ GGTorusSelfCent p (ggGamma L hN).range := by
  have hB : IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hcomm : ∀ a b : Bs, a * b = b * a := hB.1.is_comm.comm
  have hexp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (hB.2 b b.property)
  exact ⟨isElemAbelian_range hcomm hexp (ggGamma L hN),
    ggTorusSelfCent_ggGamma hN hS.1.1.2.1.2.2.2⟩

omit [Finite G] in
theorem beta_ker (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (ggBeta L θ hN).ker = (Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h => mem_centralizer_of_ggLAut_eq_one L θ hL h,
    fun h => ggLAut_eq_one_of_mem_centralizer L θ h⟩

omit [Finite G] in
theorem beta_card (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggBeta L θ hN).range = ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index := by
  rw [← Subgroup.index_ker, beta_ker hL θ hN]

theorem beta_image_of_index (hBs : IsElemAbelian p Bs) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {e : ℕ}
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ e) :
    IsElemAbelian p (ggBeta L θ hN).range ∧ Nat.card (ggBeta L θ hN).range = p ^ e := by
  exact ⟨isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
    (fun b => Subtype.ext (hBs.2 b b.property)) (ggBeta L θ hN),
    (beta_card hL θ hN).trans hidx⟩

end CFSG.StandardType.QTwoCav

end
