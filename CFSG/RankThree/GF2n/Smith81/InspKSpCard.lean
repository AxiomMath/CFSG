module

public import CFSG.RankThree.GF2n.Smith81.InspKSpBase
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotClassOrders
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp.KFact

open Subgroup CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.SymplecticPilot
  CFSG.LieType.Universal.Symplectic CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.StandardType.KGSp

theorem card_centralizer_mulEquiv {P Y : Type*} [Group P] [Group Y] (e : P ≃* Y) (x : P) :
    Nat.card (Subgroup.centralizer ({e x} : Set Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set P)) := by
  have h1 : Subgroup.centralizer ({e x} : Set Y) =
      (Subgroup.centralizer ({x} : Set P)).map e.toMonoidHom := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Subgroup.mem_map,
      MulEquiv.coe_toMonoidHom]
    constructor
    · intro hg
      refine ⟨e.symm g, ?_, by simp⟩
      apply e.injective
      simpa using hg
    · rintro ⟨h, hh, rfl⟩
      simpa using congrArg e hh
  rw [h1]
  exact (Nat.card_congr ((Subgroup.centralizer ({x} : Set P)).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv).symm

theorem card_statedSp_eq_ordBC {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (r : ℕ) :
    Nat.card (StatedSp r K) = CFSG.Open.ordBC r (2 ^ f) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
  unfold CFSG.Open.ordBC
  have hodd : Odd (2 ^ f - 1) := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [pow_succ]
    exact ⟨2 ^ g - 1, by have := Nat.one_le_two_pow (n := g); omega⟩
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [hg, Nat.div_one, sq]


open CFSG.StandardType in
theorem ggRCSOmSummand_spCompl12_of_four_le {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hK : 4 ≤ Nat.card F) : RCSTOm.GGRCSOmSummand (spCompl12 F m) := by
  set T := spCompl12 F m with hT
  have eT : T ≃* StatedSp (m + 1) F := (spCompl12Equiv F m).symm
  have hZ : Subgroup.center T = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eT.symm,
      center_statedSp_eq_bot, Subgroup.map_bot]
  have hq : CFSG.IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (spCompl12Equiv F m)
      (CFSG.LieType.Universal.Symplectic.isQuasisimple (m + 1) F (by omega)
        (Or.inl (Or.inr hK)))
  exact RCSTOm.ggRCSOmSummand_of_isQuasisimple hq hZ

open CFSG.StandardType in
theorem pCoreOf_centralizer_twoCentralElt_of_four_le {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : 4 ≤ Nat.card F) :
    pCoreOf 2 (Subgroup.centralizer
      ({twoCentralElt (m + 3) 1 2 (0 : F) 1} : Set (StatedSp (m + 3) F))) =
      wRadical F (1 : Fin (m + 3)) 2 := by
  obtain ⟨hC, hSQ, hTQ, hST⟩ := RCSTSp.centralizer_a2_facts (F := F) (n := m)
  have hX : Subgroup.centralizer ({twoCentralElt (m + 3) 1 2 (0 : F) 1} :
      Set (StatedSp (m + 3) F)) =
      wRadical F (1 : Fin (m + 3)) 2 ⊔
        ((shortBlock F (one_ne_two_fin (n := m))).range ⊔ spCompl12 F m ⊔ ⊥) := by
    rw [hC, sup_bot_eq]
  have hcentbot : Subgroup.centralizer ((⊥ : Subgroup (StatedSp (m + 3) F)) :
      Set (StatedSp (m + 3) F)) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  exact RCSTOm.pCoreOf_eq_of_three_summands hX (isPGroup_wRadical one_ne_two_fin) hSQ hTQ
    bot_le hST (by rw [hcentbot]; exact le_top) (by rw [hcentbot]; exact le_top)
    (ggRCSOmSummand_shortBlock (F := F) (n := m) (Or.inr hF))
    (ggRCSOmSummand_spCompl12_of_four_le hF) RCSTOm.ggRCSOmSummand_bot


open CFSG.StandardType in
theorem card_centralizer_twoCentralElt {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} :
    Nat.card (Subgroup.centralizer
      ({twoCentralElt (m + 3) 1 2 (0 : F) 1} : Set (StatedSp (m + 3) F))) =
      Nat.card (wRadical F (1 : Fin (m + 3)) 2) *
        (Nat.card (StatedSp 1 F) * Nat.card (StatedSp (m + 1) F)) := by
  have h12 := one_ne_two_fin (n := m)
  have hML : a2Levi F m ≤ (leviHom h12 0 (one_ne_zero (α := F))).range :=
    sup_le (range_shortBlock_le_range_leviHom one_ne_zero)
      (spCompl12_le_range_leviHom one_ne_zero)
  have hnorm : a2Levi F m ≤
      normalizer (wRadical F (1 : Fin (m + 3)) 2 : Set (StatedSp (m + 3) F)) :=
    hML.trans (range_leviHom_le_normalizer_wRadical h12 one_ne_zero)
  have hdisj : Disjoint (wRadical F (1 : Fin (m + 3)) 2) (a2Levi F m) :=
    (disjoint_wRadical_range_leviHom h12 one_ne_zero).mono_right hML
  rw [(RCSTSp.centralizer_a2_facts (F := F) (n := m)).1]
  change Nat.card (wRadical F (1 : Fin (m + 3)) 2 ⊔ a2Levi F m :
    Subgroup (StatedSp (m + 3) F)) = _
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    card_a2Levi]

end CFSG.RankThree.GF2n.Smith81.Insp.KFact
