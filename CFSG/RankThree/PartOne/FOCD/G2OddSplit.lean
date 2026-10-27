module

public import CFSG.RankThree.PartOne.FOCD.CompQuasi
public import CFSG.RankThree.PartOne.FOCD.G2OddCommon
import CFSG.RankThree.Chevalley.G2CyclotomicTori
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem pRankLeTwo_G2_oddsplit (hK : Odd (Nat.card K)) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) : PRankLeTwo p (adjointGroup .G2 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨hconj, ⟨φ⟩, -⟩ := odd_G2_split_prime_toral_Sylow_and_centralizers K hK hp hp3 hpq
  exact pRankLeTwo_of_conj_cyclic2 hp (H := (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K))
    (G₁ := Kˣ) (G₂ := Kˣ)
    ((Subgroup.subgroupOfEquivOfLe torusGroup_le_adjointGroup_G2).trans
      (φ.symm.trans (piFinTwoMulEquiv Kˣ))) hconj

theorem compGoodZAt_G2_oddsplit (hK : Odd (Nat.card K)) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) (b : adjointGroup .G2 K) (hb1 : b ≠ 1) (hbp : b ^ p = 1) :
    CompGoodZAt p b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨hconj, ⟨φ⟩, hmem, huniq, hcases⟩ :=
    odd_G2_split_prime_toral_Sylow_and_centralizers K hK hp hp3 hpq
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hbP : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbord, pow_one])
  obtain ⟨g, hg⟩ := hconj _ hbP
  have hb'mem : ((g * b * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈ torusGroup .G2 K := by
    have h1 : (MulAut.conj g) b ∈ (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers b)
    have h2 := Subgroup.mem_subgroupOf.1 (hg h1)
    simpa [MulAut.conj_apply] using h2
  refine compGoodZAt_conj g ?_
  set b' : adjointGroup .G2 K := g * b * g⁻¹ with hb'
  have hb'ord : orderOf b' = p := by
    rw [hb', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hbord
  obtain ⟨a, ha, -⟩ := huniq _ hb'mem
  have hdord : orderOf (rootDiagUnit .G2 a) = p := by
    rw [ha, Subgroup.orderOf_coe]
    exact hb'ord
  have hbeq : b' = (⟨rootDiagUnit .G2 a, ha ▸ b'.2⟩ : adjointGroup .G2 K) := Subtype.ext ha.symm
  have hJd : rootDiagUnit .G2 a ∈ adjointGroup .G2 K := ha ▸ b'.2
  have hHcomm : ∀ x ∈ torusGroup .G2 K, ∀ y ∈ torusGroup .G2 K, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu⟩ : ∃ u, φ u = ⟨x, hx⟩ := ⟨φ.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨v, hv⟩ : ∃ v, φ v = ⟨y, hy⟩ := ⟨φ.symm ⟨y, hy⟩, by simp⟩
    have := congrArg Subtype.val
      (show φ u * φ v = φ v * φ u by rw [← map_mul, ← map_mul, mul_comm])
    rw [hu, hv] at this
    exact this
  rw [hbeq]
  rcases hcases a hdord with ⟨⟨-, hD, -⟩, -⟩ |
    ⟨⟨α, hα, -, hD, -, ⟨e⟩, hqs, hcomm, -, -, -⟩, -⟩
  ·
    refine compGoodZAt_of_comm fun x hx y hy => ?_
    have hx' : (x : ModGL .G2 K) ∈ toralCentralizer .G2 K a :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    have hy' : (y : ModGL .G2 K) ∈ toralCentralizer .G2 K a :=
      ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))⟩
    rw [hD] at hx' hy'
    exact Subtype.ext (hHcomm _ hx' _ hy')
  ·
    have hQD : rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ≤
        adjointGroup .G2 K ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K)) := by
      show _ ≤ toralCentralizer .G2 K a
      rw [hD]
      exact le_sup_right
    have hDQ : ⁅adjointGroup .G2 K ⊓ Subgroup.centralizer
        ({rootDiagUnit .G2 a} : Set (ModGL .G2 K)),
        adjointGroup .G2 K ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K))⁆ ≤
        rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) := le_of_eq hcomm
    have hpQ : p ∣ Nat.card (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
        Subgroup (ModGL .G2 K)) := by
      rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      exact Dvd.dvd.mul_left (hpq.trans (by
        rw [show Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) by
          obtain ⟨w, hw⟩ : ∃ w, Nat.card K = w + 1 := ⟨Nat.card K - 1, by
            have := Nat.card_pos (α := K); omega⟩
          rw [hw]; simp only [Nat.add_sub_cancel]; ring_nf; omega]
        exact Dvd.intro _ rfl)) _
    exact compGoodZAt_of_quasisimple_layer hJd hqs hQD hDQ hpQ (hZ_of_equiv_sl2 hpodd e)

end CFSG.RankThree.PartOne.FOCD
