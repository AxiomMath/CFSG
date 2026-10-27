module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeKG
public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspD4
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Chevalley (torusTorsion)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggNbrG2Off_conj_torsion
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h6 : 6 ∣ n) (σ : K ≃+* K) (hσ : orderOf σ = 3) {E : Subgroup (adjointGroup Tag.G2 K)}
    (hE : IsElemAbelian 3 E) (hfix : ∀ y ∈ E, g2FieldHom K σ y = y) :
    ∃ g : adjointGroup Tag.G2 K, g2FieldHom K σ g = g ∧
      ∀ y ∈ E, ((g * y * g⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ torusTorsion K 3 := by
  classical
  have hring : ringChar K = 2 := by
    haveI : CharP K 2 := charP_two_of_card hK
    exact ringChar.eq K 2
  obtain ⟨m, rfl⟩ := h6
  have hpow : Nat.card ↥(fixSubfield σ) ^ 3 = 2 ^ (6 * m) := by
    rw [← hσ, card_fixSubfield_pow σ, hK]
  have hcard : Nat.card ↥(fixSubfield σ) = 2 ^ (2 * m) := by
    have h1 : Nat.card ↥(fixSubfield σ) ^ 3 = (2 ^ (2 * m)) ^ 3 := by
      rw [hpow, ← pow_mul]
      exact congrArg (fun e => (2 : ℕ) ^ e) (by ring)
    exact Nat.pow_left_injective (by norm_num) h1
  have h31 : 3 ∣ Nat.card ↥(fixSubfield σ) - 1 := by
    have h42 : (2 : ℕ) ^ (2 * m) = 4 ^ m := by
      rw [pow_mul]
      norm_num
    rw [hcard, h42]
    simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := m)
  let E₀ : Subgroup (adjointGroup Tag.G2 ↥(fixSubfield σ)) := E.comap (g2Incl σ)
  have hEcomm : ∀ a b : E, a * b = b * a := by
    intro a b
    haveI : IsMulCommutative E := hE.1
    exact mul_comm' a b
  have hE0_3 : ∀ x ∈ E₀, x ^ 3 = 1 := by
    intro x hx
    apply g2Incl_injective σ
    rw [map_pow, map_one]
    exact hE.2 (g2Incl σ x) hx
  have hE0c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    intro x hx y hy
    apply g2Incl_injective σ
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hEcomm ⟨g2Incl σ x, hx⟩ ⟨g2Incl σ y, hy⟩)
  obtain ⟨g₀, hg₀⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_conj_mem_torusTorsion_three
      (K := ↥(fixSubfield σ)) h31 E₀ hE0_3 hE0c
  refine ⟨g2Incl σ g₀, ?_, ?_⟩
  · exact (mem_range_g2Incl_iff hring σ (g2Incl σ g₀)).mp ⟨g₀, rfl⟩
  · intro y hy
    obtain ⟨y₀, hy₀⟩ := (mem_range_g2Incl_iff hring σ y).mpr (hfix y hy)
    have hy₀E : y₀ ∈ E₀ := by
      change g2Incl σ y₀ ∈ E
      rw [hy₀]
      exact hy
    have hz := hg₀ y₀ hy₀E
    obtain ⟨hH, -⟩ :=
      (CFSG.RankThree.Chevalley.mem_torusTorsion_iff (L := ↥(fixSubfield σ)) (n := 3)).1 hz
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
    have hc3 : c ^ 3 = 1 := by
      refine (CFSG.RankThree.Chevalley.rootDiagUnit_mem_torusTorsion_iff
        (L := ↥(fixSubfield σ)) 3 c).1 ?_
      rw [← hc]
      exact hz
    have hconj : (g2Incl σ g₀ * y * (g2Incl σ g₀)⁻¹ : adjointGroup Tag.G2 K)
        = g2Incl σ (g₀ * y₀ * g₀⁻¹) := by
      rw [← hy₀, map_mul, map_mul, map_inv]
    rw [hconj, coe_g2Incl, hc, baseChangeGL_rootDiagUnit]
    refine (CFSG.RankThree.Chevalley.rootDiagUnit_mem_torusTorsion_iff (L := K) 3 _).2 ?_
    funext i
    show (Units.map (fixSubfield σ).subtype.toMonoidHom (c i)) ^ 3 = 1
    have hci : c i ^ 3 = 1 := by simpa using congrFun hc3 i
    rw [← map_pow, hci, map_one]

end CFSG.StandardType

end
