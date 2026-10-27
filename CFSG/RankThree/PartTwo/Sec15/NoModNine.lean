module

public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1519Small
import CFSG.RankThree.PartTwo.Sec15.NoModNineTools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec16.Item16Tail15
import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_modNine_of_inner {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h138 : Item138N) (hK : KFacts.KSL3PiOrder3TypeC) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) := by
  intro h9
  have hp : p.Prime := Fact.out
  obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := exists_projImage_model he hiso
  have hq2 : 2 < p ^ e := by
    have : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
    omega
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ (center_projImage_slPi hKf hq hq2)
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data hZ
  have h9AL : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) hprod.some
  have hAle : A ≤ Subgroup.zpowers c ⊔ L := Sec16.le_sup_of_card_inf h hcL h9AL
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt hl)
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨p, e, inferInstance, he, hiso⟩
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hLc))
  obtain ⟨f₀, hf₀AL, hf₀1⟩ : ∃ f₀ ∈ A ⊓ L, f₀ ≠ 1 := by
    have hne : A ⊓ L ≠ ⊥ := fun hbot => by
      rw [hbot, Subgroup.card_bot] at h9AL
      omega
    obtain ⟨⟨f₀, hf₀⟩, hf₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨f₀, hf₀, fun h1 => hf₀1 (Subtype.ext h1)⟩
  have hE : ∀ a ∈ A, ∃ E : Subgroup G, c ∈ E ∧ a ∈ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 27 ∧ E ≤ Subgroup.normalizer (L : Set G) ∧
      Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧ Sec4.IsTypeCOn E L := by
    intro a ha
    have ha' : a ∈ (Subgroup.zpowers c : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN]
      exact hAle ha
    obtain ⟨_, hw, l, hl, rfl⟩ := ha'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hlA : l ∈ A := by
      have : l = (c ^ k)⁻¹ * (c ^ k * l) := by group
      rw [this]
      exact A.mul_mem (A.inv_mem (A.zpow_mem h.mem_A k)) ha
    by_cases hl1 : l = 1
    · obtain ⟨E, hcE, -, hEe, hE27, hEN, hEsec, hEC⟩ := exists_typeC_E27 hK hKf hq h9 φ hZ hLc
        hc3 hcL hf₀AL.2 (h.isElemAbelian.2 f₀ hf₀AL.1) hf₀1
      refine ⟨E, hcE, ?_, hEe, hE27, hEN, hEsec, hEC⟩
      simp only [hl1, mul_one]
      exact E.zpow_mem hcE k
    · obtain ⟨E, hcE, hlE, hEe, hE27, hEN, hEsec, hEC⟩ := exists_typeC_E27 hK hKf hq h9 φ hZ
        hLc hc3 hcL hl (h.isElemAbelian.2 l hlA) hl1
      exact ⟨E, hcE, E.mul_mem (E.zpow_mem hcE k) hlE, hEe, hE27, hEN, hEsec, hEC⟩
  have hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (Sec16.thetaCen ({a} : Set G))) := by
    intro a ha _
    obtain ⟨E, hcE, haE, hEe, hE27, hEN, hEsec, hEC⟩ := hE a ha
    by_contra hev
    have hEC' : E ≤ Subgroup.centralizer ({a} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa using congrArg Subtype.val (hEe.1.is_comm.comm ⟨y, hy⟩ ⟨a, haE⟩))
    have hE𝓔 : E ∈ partTwoE G := Sec16.mem_partTwoE_of_thetaCen hEe hE27 hEC' hev
    have hreach : E ∈ reachE A := ⟨hE𝓔, Relation.ReflTransGen.single
      ⟨h.toSec13Data.mem_partTwoE, hE𝓔,
        ⟨Subgroup.zpowers c, h.zpowers_mem_omegaA, Subgroup.zpowers_le.mpr hcE⟩⟩⟩
    have hTE : HypT E := hypT_of_mem_reachE h.toTheoremFourHyp h.partTwoS_eq h.hypR hreach
    obtain ⟨-, hmod, -⟩ := h138 G A c L h.toSec13Data hL3 E hcE hEe hE27 hEN hEsec
      (Or.inr hTE) hEC
    exact hmod p e he hiso h9
  have hS := Sec16.mem_partTwoS_of_odd h.toSec13Data hodd
  rw [h.partTwoS_eq] at hS
  simp at hS

theorem step1519U38_of (h138 : Item138N) (hK : KFacts.KSL3PiOrder3TypeC) : Step1519U38 := by
  intro G _ _ A c L h Y hctx hiso
  obtain ⟨-, -, -, -, -, hprod, -, -, -⟩ := hctx.concl1515
  exact not_modNine_of_inner h h138 hK (p := 2) (e := 3) (by norm_num) hiso hprod (by norm_num)

theorem two_pow_mod_nine_of_three_dvd {m : ℕ} (hm : 3 ∣ m) : 2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_mul]
  norm_num
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem not_three_dvd_of_concl1515 {A : Subgroup G} {c : G} {L Y : Subgroup G}
    (h : Sec15R G A c L) (h138 : Item138N) (hK : KFacts.KSL3PiOrder3TypeC)
    (hc : Concl1515 A c L Y) {m : ℕ} (hm : 1 ≤ m)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m) :
    ¬ 3 ∣ m ∧ ∀ n f : ℕ, m = n * f → ¬ 3 ∣ f := by
  obtain ⟨-, -, -, -, -, hprod, -, -, -⟩ := hc
  have h3 : ¬ 3 ∣ m := fun h3 =>
    not_modNine_of_inner h h138 hK hm hiso hprod (two_pow_mod_nine_of_three_dvd h3)
  exact ⟨h3, fun n f hnf h3f => h3 (hnf ▸ Dvd.dvd.mul_left h3f n)⟩

theorem step1519Small_of_noModNine (h1510 : Item1510R) (hbr : Sec16.Step169TwoBridge)
    (h138 : Item138N) (hK : KFacts.KSL3PiOrder3TypeC) : Step1519Small :=
  step1519Small_of h1510 hbr (step1519U38_of h138 hK)

theorem step1519Small_of_item138N (h1510 : Item1510R) (hbr : Sec16.Step169TwoBridge)
    (h138 : Item138N) : Step1519Small :=
  step1519Small_of_noModNine h1510 hbr h138 KFacts.kSL3PiOrder3TypeC

end CFSG.RankThree.PartTwo.Sec15
