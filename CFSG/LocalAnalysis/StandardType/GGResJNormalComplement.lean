module

public import CFSG.Mathlib.GroupTheory.ElementarySelfCentralizingComplement
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.GroupTheory.QuasisimplePSolvable

public section

namespace CFSG.StandardType

open CFSG CFSG.Open
open scoped Pointwise

theorem ggAutomizer_sup_of_le_normalizer
    {G : Type} [Group G] {p : ℕ} {J Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G)) :
    ggAutomizer (J ⊔ Bs) Bs = ggAutomizer J Bs := by
  refine le_antisymm ?_ ?_
  · change Subgroup.closure (ggInduced (J ⊔ Bs) Bs) ≤ ggAutomizer J Bs
    rw [Subgroup.closure_le]
    rintro φ ⟨h, hhH, hhN, hφ⟩
    have hhH' : h ∈ Bs ⊔ J := by
      rwa [sup_comm] at hhH
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right Bs J hBJ
    have hmem : h ∈ (Bs : Set G) * (J : Set G) := by
      rw [← hset]
      exact hhH'
    obtain ⟨b, hbB, j, hjJ, rfl⟩ := Set.mem_mul.mp hmem
    have hbN : b ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.le_normalizer hbB
    have hjN : j ∈ Subgroup.normalizer (Bs : Set G) := by
      have hbInv : b⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
        Subgroup.inv_mem _ hbN
      have h := Subgroup.mul_mem (Subgroup.normalizer (Bs : Set G)) hbInv hhN
      simpa using h
    have hφeq : φ = ggConjAut Bs hjN := by
      ext x
      rw [hφ x, ggConjAut_apply]
      have hxJ : j * (x : G) * j⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hjN x).mp x.2
      have hbcomm : b * (j * (x : G) * j⁻¹) =
          (j * (x : G) * j⁻¹) * b := by
        exact congrArg (fun y : ↥Bs => (y : G))
          ((@IsMulCommutative.is_comm ↥Bs _ hBs.1).comm ⟨b, hbB⟩
            ⟨j * (x : G) * j⁻¹, hxJ⟩)
      calc
        (b * j) * (x : G) * (b * j)⁻¹
            = b * (j * (x : G) * j⁻¹) * b⁻¹ := by group
        _ = j * (x : G) * j⁻¹ := by rw [hbcomm]; group
    rw [hφeq]
    exact ggConjAut_mem_ggAutomizer hjJ hjN
  · exact ggAutomizer_mono Bs le_sup_left

theorem normalizer_eq_centralizer_of_automizer_bot
    {G : Type} [Group G] {p : ℕ} {J Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hAJ : ggAutomizer J Bs = ⊥) :
    Subgroup.normalizer (Bs.subgroupOf (J ⊔ Bs) : Set ↥(J ⊔ Bs)) =
      Subgroup.centralizer (Bs.subgroupOf (J ⊔ Bs) : Set ↥(J ⊔ Bs)) := by
  set H : Subgroup G := J ⊔ Bs with hHdef
  have hBH : Bs ≤ H := by
    rw [hHdef]
    exact le_sup_right
  have hAH : ggAutomizer H Bs = ⊥ := by
    rw [hHdef, ggAutomizer_sup_of_le_normalizer hBs hBJ, hAJ]
  refine le_antisymm ?_ ?_
  · intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hnSub : n ∈ (Subgroup.normalizer (Bs : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hBH]
      exact hn
    have hnG : ((n : H) : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mem_subgroupOf.mp hnSub
    let φ : MulAut ↥Bs := ggConjAut Bs hnG
    have hφmem : φ ∈ ggAutomizer H Bs :=
      ggConjAut_mem_ggAutomizer n.2 hnG
    have hφ1 : φ = 1 := by
      have hbot : φ ∈ (⊥ : Subgroup (MulAut ↥Bs)) := by
        simpa [hAH] using hφmem
      simpa using hbot
    have heG : (e : G) ∈ Bs := Subgroup.mem_subgroupOf.mp he
    let b : ↥Bs := ⟨(e : G), heG⟩
    have hb : ((φ b : ↥Bs) : G) = (b : G) := by
      have h := congrArg (fun ψ : MulAut ↥Bs => ((ψ b : ↥Bs) : G)) hφ1
      simpa using h
    have hcoe : ((n : H) : G) * ((e : H) : G) * ((n : H) : G)⁻¹ = ((e : H) : G) := by
      simpa [φ, b, ggConjAut_apply] using hb
    have hcommG : ((n : H) : G) * ((e : H) : G) =
        ((e : H) : G) * ((n : H) : G) := by
      calc
        ((n : H) : G) * ((e : H) : G)
            = (((n : H) : G) * ((e : H) : G) * ((n : H) : G)⁻¹) *
                ((n : H) : G) := by group
        _ = ((e : H) : G) * ((n : H) : G) := by rw [hcoe]
    exact Subtype.ext hcommG.symm
  · exact Subgroup.centralizer_le_normalizer _

theorem centralizer_subgroupOf_orderP_mem
    {G : Type} [Group G] {p : ℕ} {E H : Subgroup G} (hEH : E ≤ H)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ p = 1 → g ∈ E) :
    ∀ x ∈ Subgroup.centralizer (E.subgroupOf H : Set H), x ^ p = 1 →
      x ∈ E.subgroupOf H := by
  intro x hx hxp
  rw [Subgroup.mem_subgroupOf]
  apply hSC ((x : H) : G)
  · rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro e he
    have heH : e ∈ H := hEH he
    have he' : (⟨e, heH⟩ : H) ∈ E.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact he
    have hxe := hx ⟨e, heH⟩ he'
    simpa using congrArg (fun y : H => (y : G)) hxe
  · simpa using congrArg (fun y : H => (y : G)) hxp

theorem false_of_hasNormalPComplement_of_perfect_pdiv
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {J H : Subgroup G} (hJH : J ≤ H)
    (hJperf : commutator ↥J = ⊤)
    (hNP : CFSG.HasNormalPComplement p ↥H)
    (hpJ : p ∣ Nat.card J) : False := by
  have hJNP : CFSG.HasNormalPComplement p ↥J :=
    CFSG.hasNormalPComplement_of_le p hJH hNP
  letI : Group.IsPerfect ↥J := ⟨hJperf⟩
  have hcop : Nat.Coprime p (Nat.card J) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect hJNP
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcop hpJ

theorem GGResHyp.automizerJ_ne_bot_of_prime_dvd_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hpJ : p ∣ Nat.card J) :
    ggAutomizer J Bs ≠ ⊥ := by
  classical
  intro hAJ
  obtain ⟨-, -, -, -, -, hBeta, -, -⟩ := hH.1.1
  have hp2 : p ≠ 2 := hBeta.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGResHyp.Bs_le_normalizer_J hH
  have hJperf : commutator ↥J = ⊤ :=
    hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  let H : Subgroup G := J ⊔ Bs
  have hBH : Bs ≤ H := by
    dsimp [H]
    exact le_sup_right
  have hJH : J ≤ H := by
    dsimp [H]
    exact le_sup_left
  have hNP : HasNormalPComplement p ↥H := by
    apply CFSG.hasNormalPComplement_of_elementary_selfcentralizing
      (H := ↥H) (p := p) hp2 (Bs.subgroupOf H)
    · exact CFSG.Open.IsElemAbelian.subgroupOf hBs H
    · exact CFSG.StandardType.centralizer_subgroupOf_orderP_mem
        (E := Bs) (H := H) hBH hSC
    · exact CFSG.StandardType.normalizer_eq_centralizer_of_automizer_bot
        (J := J) (Bs := Bs) hBs hBJ hAJ
  exact CFSG.StandardType.false_of_hasNormalPComplement_of_perfect_pdiv
    (J := J) (H := H) hJH hJperf hNP hpJ

section Certificates

theorem GGResHyp.automizerJ_ne_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    ggAutomizer J Bs ≠ ⊥ :=
  hH.automizerJ_ne_bot_of_prime_dvd_card hH.prime_dvd_card_J

end Certificates

end CFSG.StandardType
