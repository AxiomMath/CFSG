module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddGlue
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddL2
import CFSG.RankThree.PartTwo.KFacts.K72FixL2
import CFSG.RankThree.SubgroupLists.LinearTwoFamily

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GorensteinWalter
  CFSG.GH74.GLS
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)

theorem l2_ident {X : Type} [Group X] [Finite X] {P : Subgroup (MulAut X)} {K₀ : Subgroup X}
    (hKs : IsSimpleGroup ↥K₀) (hinv : ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀)
    (hfaith : ∀ σ ∈ P, (∀ k ∈ K₀, σ k = k) → σ = 1) (hP9 : Nat.card P = 9)
    (hP3 : ∀ σ ∈ P, σ ^ 3 = 1)
    (hsolv : ∀ σ ∈ P, σ ≠ 1 → Group.IsSolvable (Sec4.autFix σ))
    (h3X : ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (hM : StatedClassicalModel ↥K₀ .PSL 2 r k) : r = 3 ∧ k = 2 := by
  classical
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hM
  set e : ↥K₀ ≃* PSL2 F := SubgroupLists.toPSL2 e₀ with he
  have : Fact r.Prime := ⟨hr⟩
  have : CharP F r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfaith' : ∀ ε ∈ P, ε ≠ 1 → ¬ K₀ ≤ Sec4.autFix ε := fun ε hε hε1 hle =>
    hε1 (hfaith ε hε fun k hk => Sec4.mem_autFix.mp (hle hk))
  have hinj := restrictAut_injective hinv hfaith'
  set E := (restrictAut hinv).range with hE
  have hE9 : Nat.card E = 9 := by
    rw [← hP9]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hE3 : ∀ ε ∈ E, ε ^ 3 = 1 := by
    rintro _ ⟨ε, rfl⟩
    rw [← map_pow, show ε ^ 3 = 1 from Subtype.ext (hP3 ε ε.2), map_one]
  by_cases hr3 : r = 3
  · subst hr3
    refine ⟨rfl, ?_⟩
    by_contra hk2
    by_cases hk3 : 3 ≤ k
    ·
      have hP := h3X (((SubgroupLists.rootGroupPSL2 F).map e.symm.toMonoidHom).map K₀.subtype)
        (isElemAbelian_map_subtype ?_)
      · rw [Subgroup.card_map_of_injective K₀.subtype_injective,
          Subgroup.card_map_of_injective e.symm.injective, SubgroupLists.card_rootGroupPSL2,
          hF] at hP
        have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        omega
      · refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
        · obtain ⟨_, a, ha, rfl⟩ := x
          obtain ⟨_, b, hb, rfl⟩ := y
          apply Subtype.ext
          change e.symm a * e.symm b = e.symm b * e.symm a
          rw [← map_mul, ← map_mul, SubgroupLists.rootGroupPSL2_comm ha hb]
        · rintro _ ⟨a, ha, rfl⟩
          change (e.symm a) ^ 3 = 1
          rw [← map_pow, SubgroupLists.rootGroupPSL2_pow ha, map_one]
    ·
      have hk1 : k = 1 := by omega
      subst hk1
      exact hadm.2.2.2.2 rfl
  · exfalso
    have hr5 : 5 ≤ r := by
      have h2 := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    have h3F : ringChar F ≠ 3 := by
      rw [ringChar.eq F r]
      exact hr3
    have h4F : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 ≤ r := by omega
        _ ≤ r ^ k := Nat.le_self_pow (by omega) r
    have hout : ∃ ε ∈ E, ¬ IsInnerAut ε := by
      by_contra hall
      push Not at hall
      obtain ⟨⟨ε₀, hε₀⟩, hε₀1⟩ : ∃ x : E, x ≠ 1 := by
        have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
        exact exists_ne 1
      have hε₀1' : ε₀ ≠ 1 := fun h => hε₀1 (Subtype.ext h)
      have hsub : E ≤ Subgroup.zpowers ε₀ := fun ε hε =>
        mem_zpowers_of_isInnerAut e h3F h4F hE9 hE3 hε₀ hε₀1' (hall ε₀ hε₀) hε (hall ε hε)
      have h1 := Subgroup.card_le_of_le hsub
      rw [hE9, Nat.card_zpowers, orderOf_eq_prime (hE3 ε₀ hε₀) hε₀1'] at h1
      omega
    obtain ⟨_, ⟨σ, rfl⟩, hσout⟩ := hout
    set α := restrictAut hinv σ with hα
    have hα3 : α ^ 3 = 1 := hE3 α ⟨σ, rfl⟩
    set β := MulAut.congr e α with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
    have hβout : ¬ IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
    obtain ⟨τ, hτ3, -⟩ := KFacts.exists_fixed_iff_of_isField
      (KFacts.isField_of_pow_three_of_not_inner hβ3 hβout) hβ3
    set q₀ := Nat.card (GH74.GLS.IVK.fixedField τ) with hq₀def
    have hK : Nat.card F = q₀ ^ 3 := by
      have h := GH74.GLS.IVK.fixedField_card_pow τ
      rw [hτ3] at h
      exact h.symm
    have hq₀ : 4 ≤ q₀ := by
      have hdvd : q₀ ∣ r ^ k := by
        rw [← hF, hK]
        exact dvd_pow_self q₀ (by norm_num)
      obtain ⟨j, -, hq⟩ := (Nat.dvd_prime_pow hr).mp hdvd
      rcases j with _ | j
      · exfalso
        rw [pow_zero] at hq
        rw [hq, one_pow] at hK
        have : 1 < Nat.card F := Finite.one_lt_card
        omega
      · rw [hq]
        calc 4 ≤ r := by omega
          _ ≤ r ^ (j + 1) := Nat.le_self_pow (by omega) r
    obtain ⟨-, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 e hq₀ hK hα3 hσout
    have hσ1 : (σ : MulAut X) ≠ 1 := by
      intro h
      apply hσout
      have : σ = 1 := Subtype.ext h
      rw [hα, this, map_one]
      exact ⟨1, map_one _⟩
    have hsol := hsolv σ σ.2 hσ1
    have hmap := map_autFix_restrictAut hinv σ
    have hle : (Sec4.autFix α).map K₀.subtype ≤ Sec4.autFix (σ : MulAut X) := by
      rw [hα, hmap]
      exact inf_le_right
    haveI := hsol
    have hsolα : Group.IsSolvable (Sec4.autFix α) := by
      have hs2 : Group.IsSolvable ((Sec4.autFix α).map K₀.subtype) :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
      exact Group.isSolvable_of_isSolvable_injective (f :=
        ((Sec4.autFix α).equivMapOfInjective K₀.subtype K₀.subtype_injective).toMonoidHom)
        (MulEquiv.injective _)
    rw [autFix_eq_eqLocus] at hsolα
    haveI := hsolα
    haveI := hQ.1
    have : Nontrivial (α.toMonoidHom.eqLocus (MonoidHom.id ↥K₀)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact Group.IsPerfect.not_isSolvable _ hsolα

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
