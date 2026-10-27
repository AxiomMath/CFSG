module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagProof
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

section Certs

private theorem a11_exists_diagLift {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hMp : GGInnerDiagMpInput) (hcfg : GGConfig 7 B Bs x L D J)
    (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3) :
    ∃ φ : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G, φ.range = L ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3)) ∧
      ∀ b ∈ Bs, GGActsDiag φ b := by
  have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
  obtain ⟨φ, hrange, hker⟩ := exists_slLift_of_classicalModel (n := 3) (f := 3)
    (by norm_num) (by norm_num) (by norm_num) hperf hmod
  have hA := exists_mem_ggInducedPairs_of_innerDiagOn hMp (n := 3) (f := 3) (by norm_num)
    hmod.1 hInnL hker hrange
  have hbig : 7 ^ ((3 + 1) / 7 + 3) ≤ Nat.card Bs := by
    have h34 : 7 ^ 3 ≤ 7 ^ 4 := by norm_num
    have h43 : (3 + 1) / 7 + 3 = 3 := by norm_num
    rw [h43]
    exact h34.trans hcfg.tableB_facts.2.2.2.2
  exact exists_lift_actsDiag_of_bstar (p := 7) (n := 3) (f := 3) (M := L) (z := x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcfg.2.1.2.1
    (GGConfig.bstar_inf_centralizer_L hcfg) hbig hker hrange hA

private theorem a11_x_comm_of_mem_L {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J) :
    ∀ l ∈ L, x * l = l * x := by
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcfg.tableB_facts.2.2.2.1 hl)).symm

private theorem a11_not_y_comm_L {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 7 B x D J y K) : ¬ ∀ l ∈ L, y * l = l * y := by
  intro hcomm
  have hyB : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hyzx : y ∈ Subgroup.zpowers x := by
    rw [← hcfg.bstar_inf_centralizer_L]
    exact ⟨hyB, Subgroup.mem_centralizer_iff.mpr (fun l hl => (hcomm l hl).symm)⟩
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hnb.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · exact hyzx
  have hcardD : Nat.card D = 7 ^ 2 := hcfg.2.2.1.2.2.1
  have hcardx : Nat.card (Subgroup.zpowers x) = 7 := by
    rw [Nat.card_zpowers, hcfg.orderOf_x]
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
  rw [hcardD, hcardx] at hle
  norm_num at hle

private theorem a11_bstar_inf_centralizer_J_le {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hMp : GGInnerDiagMpInput) (hcfg : GGConfig 7 B Bs x L D J)
    (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3) {y : G} {K : Subgroup G}
    (hnb : GGNbr 7 B x D J y K) : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  obtain ⟨φ, hrange, hker, hdiag⟩ := a11_exists_diagLift hMp hcfg hInnL hmod
  have hxB : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hyB : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  obtain ⟨dx, hdx⟩ := hdiag x hxB
  obtain ⟨dy, hdy⟩ := hdiag y hyB
  have hb : ∀ k : Fin 2, (![x, y] k, InnerDiagA.diagGL (![dx, dy] k)) ∈
      LinFusion.ggInducedPairs φ := by
    intro k
    fin_cases k
    · exact ggActsVec_iff_mem_ggInducedPairs.1 hdx
    · exact ggActsVec_iff_mem_ggInducedPairs.1 hdy
  have hrng : Set.range ![x, y] = {x, y} := by
    ext g
    simp [Fin.exists_fin_two, eq_comm]
    tauto
  have hDc : Subgroup.centralizer (D : Set G) = Subgroup.centralizer (Set.range ![x, y]) := by
    rw [hnb.2.1, Subgroup.centralizer_closure, hrng]
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (Set.range ![x, y])) := by
    rw [hrange, ← hDc]
    exact hcfg.2.2.1.2.2.2.2.2.1
  obtain ⟨i, hI, h22, hJi⟩ := (LinSemisimple.isComponentOf_iff_exists_eq_map_blockSpecialLinear
    hker hb).1 hJc
  obtain ⟨T, hT1, hT2, hTJ, hBT⟩ := exists_twoSubgroup_le_map_blockSpecialLinear hker
    (fun b hb' => hdiag b (hcfg.2.1.1 hb')) hI
  exact ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨T, hT1, hT2, hJi ▸ hTJ, hBT⟩

theorem GGSecFiveA11Config.exists_lift_lowerBlock (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hA : GGSecFiveA11ConfigWide p B Bs x L D J) :
    ∃ φ : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G, φ.range = L ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3)) ∧
      (∀ b ∈ Bs, GGActsDiag φ b) ∧
      (φ.comp (slLowerBlockHom 3 (GaloisField 2 3))).range = J := by
  obtain rfl : p = 7 := hA.1
  obtain ⟨y, K, hnb, -⟩ := hA.2.2
  have hcfg : GGConfig 7 B Bs x L D J := hHyp.1
  have hInnL : GGInnerDiagOn Bs L := hHyp.2.2.1.1
  have hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 := hA.2.1
  obtain ⟨φ, hrange, hker, hdiag⟩ := a11_exists_diagLift hMp hcfg hInnL hmod
  have hCJ := a11_bstar_inf_centralizer_J_le hMp hcfg hInnL hmod hnb
  have h2 : (2 : GaloisField 2 3) = 0 := CharP.cast_eq_zero (GaloisField 2 3) 2
  have hpF : 7 ∣ Nat.card (GaloisField 2 3)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hfull : 7 ∣ 3 + 1 → 7 ^ (3 + 1) ≤ Nat.card Bs := by
    intro hdvd
    exact absurd hdvd (by norm_num)
  have hDiagVec : ∀ r : Fin (3 + 1), ∃ g ∈ Bs, ∃ τ : (GaloisField 2 3)ˣ, τ ≠ 1 ∧
      GGActsVec φ g (diagAt r τ) := fun r =>
    exists_actsVec_diagAt_of_bstar (p := 7) (n := 3) (F := GaloisField 2 3) h2
      (by norm_num) hpF hcfg.2.1.2.1 hcfg.2.1.2.2.2 hker hdiag
      (by rw [hrange]; exact (GGConfig.card_bstar_inf_centralizer_L hcfg).le) hfull r
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]
    exact hcfg.2.2.1.2.2.2.2.2.1
  obtain ⟨r, hr⟩ := exists_eq_map_blockSpecialLinear_erase (p := 7) (n := 3) (by norm_num)
    hcfg.2.1.2.1 hker hdiag hDiagVec hcfg.tableB_facts.2.2.1 (hcfg.2.1.1 hnb.1.2.1)
    (fun s => a11_x_comm_of_mem_L hcfg (φ s) (hrange ▸ ⟨s, rfl⟩))
    (fun h => a11_not_y_comm_L hcfg hnb fun l hl => by
      rw [← hrange] at hl
      obtain ⟨s, rfl⟩ := hl
      exact h s)
    hnb.2.1 hJc hCJ
  obtain ⟨φ', hr', hk', hd', hJ'⟩ := exists_lift_lowerBlock_eq (F := GaloisField 2 3) (n := 3)
    h2 hker hdiag r
  exact ⟨φ', hr'.trans hrange, hk', hd', hJ'.trans hr.symm⟩

end Certs

end CFSG.StandardType

end
