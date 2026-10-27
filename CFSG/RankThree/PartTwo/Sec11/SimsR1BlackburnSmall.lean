module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_11

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn

variable {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]

theorem groupRank_le_two (hP : IsPGroup p P)
    (hE : ∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2) :
    CFSG.groupRank P ≤ 2 := by
  refine CFSG.groupRank_le_two_of_primeRank_le_two_of_isPGroup hP ?_
  refine csSup_le' ?_
  rintro n ⟨A, hAp, hAcomm, hn⟩
  haveI : IsMulCommutative A := hAcomm
  haveI : Fact (IsPGroup p A) := ⟨hAp⟩
  have hcard : Nat.card (CFSG.omega₁ (G := A) (p := p)) = p ^ CFSG.generatorRank A :=
    CFSG.omega₁_card_eq_pow_generatorRank_of_commutative_pgroup (p := p) A
  have hΩelem : CFSG.IsElementaryAbelian p (CFSG.omega₁ (G := A) (p := p)) :=
    CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative A
  let E : Subgroup P := (CFSG.omega₁ (G := A) (p := p)).map A.subtype
  have hEcomm : IsMulCommutative E := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, -, hb⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : P) * y = y * x
    rw [← ha, ← hb]
    simpa using congrArg A.subtype ((IsMulCommutative.is_comm (M := A)).comm a b)
  have hEpow : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p)
      (A := CFSG.omega₁ (G := A) (p := p)) a ha
    simpa using congrArg A.subtype this
  have hEcard : Nat.card E = Nat.card (CFSG.omega₁ (G := A) (p := p)) :=
    Subgroup.card_map_of_injective A.subtype_injective
  have hle : p ^ CFSG.generatorRank A ≤ p ^ 2 := by
    rw [← hcard, ← hEcard]
    exact hE E ⟨hEcomm, hEpow⟩
  have hgen : CFSG.generatorRank A ≤ 2 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle
  exact hn.trans hgen

theorem exists_two_generators_of_isMetacyclic (hM : CFSG.IsMetacyclic P) :
    ∃ s : Finset P, s.card ≤ 2 ∧ Subgroup.closure (s : Set P) = ⊤ := by
  classical
  obtain ⟨N, hN, hNc, hQc⟩ := hM
  obtain ⟨n, hn⟩ := hNc.exists_generator
  obtain ⟨q, hq⟩ := hQc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨{(n : P), g}, Finset.card_le_two, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hq (x : P ⧸ N))
  have hm : (g ^ k)⁻¹ * x ∈ N := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
    exact hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hn ⟨_, hm⟩)
  have hj' : (n : P) ^ j = (g ^ k)⁻¹ * x := congrArg Subtype.val hj
  have hx : x = g ^ k * (n : P) ^ j := by rw [hj']; group
  rw [hx]
  exact Subgroup.mul_mem _
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem blackburn_small (hp : 5 ≤ p) (hP : IsPGroup p P)
    (hΩ : Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    ∃ s : Finset P, s.card ≤ 2 ∧ Subgroup.closure (s : Set P) = ⊤ := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  exact exists_two_generators_of_isMetacyclic (CFSG.proposition_4_11 (by omega) hΩ)

end CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn
