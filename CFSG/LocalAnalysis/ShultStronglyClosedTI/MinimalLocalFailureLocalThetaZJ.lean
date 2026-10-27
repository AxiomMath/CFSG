module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStabilityReduction
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ZJCharacteristic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableSelfCentralizingCore
import all CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import all CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonCanonical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.BenderSuzuki
open CFSG.RankThreeEvenClassification.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem gorenstein_maximum_family_top_eq :
    CFSG.thompsonAbelianSubgroups (⊤ : Subgroup G) = maxOrderAbelianFamily G :=
  CFSG.thompsonAbelianSubgroups_top_eq

theorem gorenstein_thompson_top_eq :
    CFSG.thompsonSubgroup (⊤ : Subgroup G) = orderThompson G :=
  CFSG.thompsonSubgroup_top_eq

theorem gorenstein_zj_eq (Q : Subgroup G) :
    CFSG.thompsonCenter Q = (orderZJ Q).map Q.subtype :=
  CFSG.thompsonCenter_eq_ambientOrderZJ Q

omit [Finite G] in
theorem indexed_order_thompson_eq : thompsonOrderSubgroup G = orderThompson G :=
  thompsonOrderSubgroup_eq_orderThompson G

omit [Finite G] in
theorem indexed_order_zj_eq : thompsonOrderCenter G = orderZJ G :=
  thompsonOrderCenter_eq_orderZJ G

omit [Finite G] in
theorem native_prime_complement_core_eq {p : ℕ} (hp : p.Prime) :
    CFSG.pPrimeCore p G = primeComplementCore G p := by
  unfold CFSG.pPrimeCore primeComplementCore
  congr 1
  ext A
  change (A.Normal ∧ Nat.Coprime p (Nat.card A)) ↔
    (A.Normal ∧ ¬ p ∣ Nat.card A)
  rw [hp.coprime_iff_not_dvd]

theorem solvable_trivial_complement_characteristic_p {p : ℕ} (hp : p.Prime)
    [Group.IsSolvable G] (hcore : CFSG.pPrimeCore p G = ⊥) :
    IsCharacteristicP p G := by
  change Subgroup.centralizer (CFSG.pCore p G : Set G) ≤ CFSG.pCore p G
  apply solvable_trivial_primeComplementCore_self_centralizing p hp
  rw [← native_prime_complement_core_eq hp]
  exact hcore

theorem solvable_complement_quotient_characteristic_p {p : ℕ} (hp : p.Prime)
    [Group.IsSolvable G] : IsCharacteristicP p (G ⧸ CFSG.pPrimeCore p G) := by
  let : Fact p.Prime := ⟨hp⟩
  apply solvable_trivial_complement_characteristic_p (G := G ⧸ CFSG.pPrimeCore p G) hp
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p)

theorem solvable_abelian_sylow_two_orderZJ_characteristic {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) [Group.IsSolvable G]
    (hSylow : HasAbelianSylow 2 G) (hcore : CFSG.pPrimeCore p G = ⊥)
    (Q : Sylow p G) : ((orderZJ (Q : Subgroup G)).map (Q : Subgroup G).subtype).Characteristic := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hchar := solvable_trivial_complement_characteristic_p hp hcore
  have hcent : Subgroup.centralizer (CFSG.pCore p G : Set G) ≤ CFSG.pCore p G := hchar
  have hop := CFSG.Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G) p hcore
  have hconstrained : CFSG.PConstrainedGroup (G := G) p := by
    intro A _ hA
    rw [hcore, bot_sup_eq, hop] at hA
    rw [hA, hop]
    exact hcent
  by_cases hOp : CFSG.pCore p G = ⊥
  · have htopbot : (⊤ : Subgroup G) = ⊥ := by
      apply le_antisymm _ bot_le
      intro a _
      have ha : a ∈ CFSG.pCore p G := hcent (by
        apply Subgroup.mem_centralizer_iff.mpr
        intro b hb
        change b ∈ CFSG.pCore p G at hb
        rw [hOp] at hb
        have hb1 : b = 1 := Subgroup.mem_bot.mp hb
        rw [hb1, one_mul, mul_one])
      rwa [hOp] at ha
    let : Subsingleton G := by
      apply subsingleton_iff.mpr
      intro a b
      have ha : a = 1 := Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top b)
      exact ha.trans hb.symm
    rw [Subgroup.eq_bot_of_subsingleton
      ((orderZJ (Q : Subgroup G)).map (Q : Subgroup G).subtype)]
    infer_instance
  · have hnormal : (CFSG.thompsonCenter (Q : Subgroup G)).Normal := by
      have h := CFSG.G_theorem_8_2_11 (p := p)
        (by intro hp2; subst p; exact (by decide : ¬ Odd 2) hpodd)
        hOp hconstrained (pStableGroup'_of_solvable_abelianSylowTwo inferInstance hSylow hpodd) Q
      simpa [hcore] using h
    have hindexed : thompsonCenterOf (Q : Subgroup G) =
        (orderZJ (Q : Subgroup G)).map (Q : Subgroup G).subtype :=
      rfl
    have : (thompsonCenterOf (Q : Subgroup G)).Normal := by
      rw [hindexed, ← gorenstein_zj_eq]
      exact hnormal
    have h := thompsonCenterOf_characteristic_of_normal p Q
    rwa [hindexed] at h

theorem solvable_abelian_sylow_two_orderZJ_ne_bot {p : ℕ} (hp : p.Prime)
    (Q : Sylow p G) (hQ : (Q : Subgroup G) ≠ ⊥) :
    (orderZJ (Q : Subgroup G)).map (Q : Subgroup G).subtype ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial (Q : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hQ
  have hne := primeComplementGrowth_order_zj_ne_bot p Q.isPGroup'
  intro hbot
  apply hne
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Q : Subgroup G).subtype_injective).mp hbot

end CFSG.ShultStronglyClosedTI.LocalTheta
