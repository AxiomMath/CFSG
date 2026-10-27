module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrWeyl
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNamedInputs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

theorem eq_one_of_fix_join' (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J) {y : G}
    {K : Subgroup G} (hN : GGNbr p B x D J y K) (b : Bs)
    (hb : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ b = b) : b = 1 := by
  have hc := hR.1
  haveI : Fact p.Prime := ⟨hc.1.2.2.2.2.2.1.1⟩
  have hS : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hc.2.1.1 hS.2.1
  have hpow : ∀ g ∈ Bs, g ^ p = 1 := hc.2.1.2.1.2
  have hbL : ∀ φ ∈ ggAutomizer L Bs, φ b = b :=
    fun φ hφ => hb φ (le_sup_left (a := ggAutomizer L Bs) hφ)
  have hbx : (b : G) ∈ Subgroup.zpowers x :=
    hTBF G p B Bs x L D J hc hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hN (hW y K hN) (Or.inr hW) b hbL
  obtain ⟨φ, hφ, hφx⟩ := exists_automizer_moves_x_of_innerWeyl hWI hc hR.2.2.1 hN hxBs
  have hφb : φ b = b := hb φ (le_sup_right (b := ggAutomizer K Bs) hφ)
  by_contra hb1
  apply hφx
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hφx (map_one φ)
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have heq : Subgroup.zpowers (b : G) = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hpow _ b.2) hb1',
      orderOf_eq_prime (hpow _ hxBs) hx1]
  have hxb : x ∈ Subgroup.zpowers (b : G) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxb
  have hxm : (⟨x, hxBs⟩ : Bs) = b ^ m := Subtype.ext (by rw [SubgroupClass.coe_zpow, hm])
  rw [hxm, map_zpow, hφb]

theorem eq_one_of_fix_join (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J) {y : G}
    {K : Subgroup G} (hN : GGNbr 3 B x D J y K) (b : Bs)
    (hb : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ b = b) : b = 1 :=
  eq_one_of_fix_join' hTBF hWI hR hW.2 hN b hb

theorem bstar_eq_of_weylAt_four (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ι : Type}
    [Fintype ι] {M : CoxeterMatrix ι} (hι : Fintype.card ι = 4)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hAt : GGSecFiveWeylAt p B Bs x L D J M) :
    Nat.card Bs = p ^ 4 ∧ B = Bs ∧ twoLocalPrimeRank p G = 4 := by
  obtain ⟨⟨-, -, -, -, -, hβ, hS, -⟩, hBs, -⟩ := hR.1
  obtain ⟨y, K, hN, hM⟩ := hAt
  have hup : Nat.card Bs ≤ p ^ 4 := by
    have h := SpJoinRefl.card_le_pow_of_weylOfType hM (eq_one_of_fix_join' hTBF hWI hR hW hN)
    rwa [hι] at h
  have hB : Nat.card B = p ^ twoLocalPrimeRank p G := hS.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  have hle : p ^ twoLocalPrimeRank p G ≤ p ^ 4 := by
    rw [← hB]
    exact hBBs.trans hup
  have ht : twoLocalPrimeRank p G = 4 :=
    le_antisymm ((Nat.pow_le_pow_iff_right hβ.1.one_lt).mp hle) hβ.2.2.2
  have hcard : Nat.card Bs = p ^ 4 := le_antisymm hup (by rw [← ht, ← hB]; exact hBBs)
  refine ⟨hcard, Subgroup.eq_of_le_of_card_ge hBs.1 (hcard.trans ?_).le, ht⟩
  rw [hB, ht]

theorem bstar_eq_of_weylAt_F4 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hAt : GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.F₄) :
    Nat.card Bs = p ^ 4 ∧ B = Bs ∧ twoLocalPrimeRank p G = 4 :=
  bstar_eq_of_weylAt_four hTBF hWI (by simp) hR hW hAt

theorem ggFrameBstarCardInput_of {ι : Type} [Fintype ι] {M : CoxeterMatrix ι} {n : ℕ}
    (hn : Fintype.card ι = n) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hlow : GGFrameBstarLowerInput M n) : GGFrameBstarCardInput M n := by
  intro G _ _ B Bs x L D J hR hW hAt hq
  refine le_antisymm ?_ (hlow G B Bs x L D J hR hW hAt hq)
  obtain ⟨y, K, hN, hM⟩ := hAt
  rw [← hn]
  exact SpJoinRefl.card_le_pow_of_weylOfType hM (eq_one_of_fix_join hTBF hWI hR hW hN)

theorem ggFrameBstarCardInput_E7 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGFrameBstarCardInput CoxeterMatrix.E₇ 7 :=
  ggFrameBstarCardInput_of (by simp) hTBF hWI ggFrameBstarLowerInput_E7

theorem ggFrameBstarCardInput_E8 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGFrameBstarCardInput CoxeterMatrix.E₈ 8 :=
  ggFrameBstarCardInput_of (by simp) hTBF hWI ggFrameBstarLowerInput_E8

end CFSG.StandardType.FrameRoute

end
