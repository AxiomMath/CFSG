module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2F1
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def TriD4OuterThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 7 ≤ p →
    LieModel X .trialityD4 0 p 1 → ∀ α : MulAut X, orderOf α = 3 →
      α ∉ (MulAut.conj : X →* MulAut X).range →
        2 ≤ Open.pRank p (signalizerFixedSubgroup α)

@[expose] def TriD4OuterThreeSection : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 7 ≤ p →
    LieModel X .trialityD4 0 p 1 → ∀ α : MulAut X, orderOf α = 3 →
      α ∉ (MulAut.conj : X →* MulAut X).range →
        ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup α ∧
          ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧ ¬ Group.IsSolvable S ∧
            ∃ g : ↥Y →* S, Function.Surjective g ∧ p ∣ Nat.card S

variable {G : Type} [Group G] [Finite G]


theorem uc22s2112r34_false_d4_outer (hRk : TriD4OuterThreeRank)
    (hSec : TriD4OuterThreeSection) {D : Data G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hH : H1930 D) {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hadm : StatedLieAdmissible .trialityD4 0 p 1)
    (hX : LieModel (BarInf L) .trialityD4 0 p 1) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hπN : ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {b : G} (hb : b ∈ c.B0)
    (hout : inducedBarInfAutHom L ⟨b, hBN hb⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  classical
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  let φ : ↥c.B0 →* MulAut (BarInf L) :=
    (inducedBarInfAutHom L).comp (Subgroup.inclusion hBN)
  have hφ : ∀ x : ↥c.B0, φ x = inducedBarInfAutHom L ⟨(x : G), hBN x.2⟩ := fun _ => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hfaith x x.2
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN x.2) hx))
  have hordφ : ∀ x : ↥c.B0, orderOf (φ x) = orderOf (x : G) := fun x =>
    (orderOf_injective φ hφinj x).trans (Subgroup.orderOf_coe x).symm
  set N := orderOf b with hN
  have hNodd : Odd N := Odd.of_dvd_nat (ch214_odd_card c.hpi) (Subgroup.orderOf_dvd_natCard c.B0 hb)
  have hNsq : Squarefree N := Ctx23L.orderOf_squarefree_of_mem_calB1 c.hB0 hb
  have hordb : orderOf (φ ⟨b, hb⟩) = N := hordφ ⟨b, hb⟩
  have hordθ : orderOf (inducedBarInfAutHom L ⟨b, hBN hb⟩) = N := hordφ ⟨b, hb⟩
  have hexc : ∀ {β : MulAut (BarInf L)}, Odd (orderOf β) → Squarefree (orderOf β) →
      ¬ 3 ∣ orderOf β → β ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range :=
    fun hβo hβs hβ3 => uc22s2112r34_inner_of_squarefree_f1_exc hadm hX
      (Or.inr (Or.inr (Or.inr rfl))) hβo hβs (fun _ => hβ3)
  have h3N : 3 ∣ N := by
    by_contra h3
    exact hout (hexc (by rw [hordθ]; exact hNodd) (by rw [hordθ]; exact hNsq)
      (by rw [hordθ]; exact h3))
  obtain ⟨m, hm⟩ := h3N
  have hN0 : N ≠ 0 := (orderOf_pos_iff.mpr (isOfFinOrder_of_finite b)).ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [hm, mul_zero])
  have hm3 : ¬ 3 ∣ m := by
    rintro ⟨k, rfl⟩
    have h9 : 3 * 3 ∣ N := ⟨k, by rw [hm, mul_assoc]⟩
    exact absurd (hNsq 3 h9) (by decide)
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3
  have hb' : b ^ m ∈ c.B0 := c.B0.pow_mem hb m
  have hordb' : orderOf (b ^ m) = 3 := by
    rw [orderOf_pow_of_dvd hm0 ⟨3, by rw [← hN, hm, mul_comm]⟩, ← hN, hm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  set α : MulAut (BarInf L) := inducedBarInfAutHom L ⟨b ^ m, hBN hb'⟩ with hαdef
  have hαφ : α = φ ⟨b, hb⟩ ^ m := by
    rw [← map_pow]
    rfl
  have hα3 : orderOf α = 3 := by
    rw [show α = φ ⟨b ^ m, hb'⟩ from rfl, hordφ]
    exact hordb'
  have hαout : α ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
    intro hαin
    set β := φ ⟨b, hb⟩ with hβ
    have hβ3o : orderOf (β ^ 3) = m := by
      rw [orderOf_pow_of_dvd (by norm_num) ⟨m, by rw [hordb, hm]⟩, hordb, hm,
        Nat.mul_div_cancel_left _ (by norm_num)]
    have hβ3in : β ^ 3 ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
      refine hexc ?_ ?_ ?_ <;> rw [hβ3o]
      · exact Odd.of_dvd_nat hNodd ⟨3, by rw [hm, mul_comm]⟩
      · exact Squarefree.squarefree_of_dvd ⟨3, by rw [hm, mul_comm]⟩ hNsq
      · exact hm3
    have hbez := Nat.gcd_eq_gcd_ab 3 m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
    have hβeq : β = (β ^ 3) ^ (Nat.gcdA 3 m) * (β ^ m) ^ (Nat.gcdB 3 m) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
        zpow_one]
    apply hout
    rw [show inducedBarInfAutHom L ⟨b, hBN hb⟩ = β from rfl, hβeq]
    exact mul_mem (zpow_mem hβ3in _) (zpow_mem (by rw [← hαφ]; exact hαin) _)
  have hrank := hRk (BarInf L) p hp hp7 hX α hα3 hαout
  obtain ⟨Y, hY, S, _, hS, hSns, g, hg, hpS⟩ := hSec (BarInf L) p hp hp7 hX α hα3 hαout
  have h3B : 3 ∣ Nat.card c.B0 := by
    rw [← hordb']
    exact Subgroup.orderOf_dvd_natCard c.B0 hb'
  exact uc22s2112r34_false_of_fixed hKF7 hH c hL.1.le hpσ hMs hb' (hBN hb')
    (by rw [hordb']; exact Nat.prime_three) (by rw [hordb']; exact hπN 3 Nat.prime_three h3B)
    hpN hrank hY hSns g hg hpS (fun h5 => absurd h5 (by omega))

end CFSG.LocalAnalysis.UniquenessCase.UC22
