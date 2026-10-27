module

public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.Foundations.Basic
import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item422Proof

open CFSG
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_range_conj_eq {K : Type*} [Group K] [Finite K] :
    Nat.card (MulAut.conj : K →* MulAut K).range = Nat.card (K ⧸ Subgroup.center K) := by
  have hker : (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have := congrArg (fun σ : MulAut K => σ x) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    · intro h
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← h x]
      group
  rw [← hker]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv.symm

theorem false_of_elemAbelian_nine_le_mulAut (hSz : KFacts.KPSz)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hcat : CFSG.Assembly.InCatalog (K ⧸ Subgroup.center K))
    (h3 : ¬ 3 ∣ Nat.card (K ⧸ Subgroup.center K)) (E : Subgroup (MulAut K))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hcard : Nat.card E = 9) : False := by
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hK
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hsimple
  have : Group.IsPerfect K := hperf
  obtain ⟨f, hf⟩ := hSz (K ⧸ Subgroup.center K) ⟨a, b, hab⟩ hcat h3
  have hcyc : IsCyclic (Outer K) :=
    ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity
      (K ⧸ Subgroup.center K) 2 f hf).2 K ⟨MulEquiv.refl _⟩).1
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner K with hI
  have hdisj : Disjoint E I := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hcard, hI, CFSG.ComponentClassification.OuterAutomorphisms.inner, card_range_conj_eq,
      show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  set π : E →* Outer K := (QuotientGroup.mk' I).comp E.subtype with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hmem : (x : MulAut K) ∈ E ⊓ I := ⟨x.2, hx⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  have : IsCyclic E := isCyclic_of_injective π hπinj
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 g g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg, hcard] at hdvd
  norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec4.Item422Proof
