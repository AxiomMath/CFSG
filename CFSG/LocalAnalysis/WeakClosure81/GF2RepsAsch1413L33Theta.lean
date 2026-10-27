module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Aut
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Emb
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases
public import CFSG.GH74.KGroups.PSLN
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Blueprint (LieModel)

private theorem a1413L33Theta_conj_mem_inner_iff (c α : MulAut L33P) :
    c * α * c⁻¹ ∈ inner L33P ↔ α ∈ inner L33P := by
  have hnorm : (inner L33P).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L33P
  constructor
  · intro hmem
    have h := hnorm.conj_mem (c * α * c⁻¹) hmem c⁻¹
    simpa [mul_assoc] using h
  · intro hmem
    exact hnorm.conj_mem α hmem c

private theorem a1413L33Theta_mul_mem_inner_of_not_mem {α β : MulAut L33P}
    (hα : α ∉ inner L33P) (hβ : β ∉ inner L33P) : α * β ∈ inner L33P := by
  have hαδ : α * dualAut 3 (ZMod 3) ∈ inner L33P := by
    rcases l33_aut_cases α with h | h
    · exact absurd h hα
    · exact h
  have hβδ : β * dualAut 3 (ZMod 3) ∈ inner L33P := by
    rcases l33_aut_cases β with h | h
    · exact absurd h hβ
    · exact h
  have hδδ : dualAut 3 (ZMod 3) * dualAut 3 (ZMod 3) = 1 :=
    (standard_automorphism_transport (K := ZMod 3) (n := 3)).2.2.2.1
  have hnorm : (inner L33P).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L33P
  have hδβ : dualAut 3 (ZMod 3) * β ∈ inner L33P := by
    have h := hnorm.conj_mem (β * dualAut 3 (ZMod 3)) hβδ (dualAut 3 (ZMod 3))
    simpa [mul_assoc] using h
  have hprod : (α * dualAut 3 (ZMod 3)) * (dualAut 3 (ZMod 3) * β) ∈ inner L33P :=
    mul_mem hαδ hδβ
  have hEq : (α * dualAut 3 (ZMod 3)) * (dualAut 3 (ZMod 3) * β) = α * β := by
    rw [mul_assoc, ← mul_assoc (dualAut 3 (ZMod 3)) (dualAut 3 (ZMod 3)) β, hδδ, one_mul]
  rwa [hEq] at hprod

private theorem a1413L33Theta_eq_one_of_conj_eq_one {u : L33P}
    (hZ : Subgroup.center L33P = ⊥) (h : MulAut.conj u = 1) : u = 1 := by
  have hu : u ∈ Subgroup.center L33P := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut L33P => f x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * u = (u * x * u⁻¹) * u := by rw [hx]
      _ = u * x := by group
  rwa [hZ, Subgroup.mem_bot] at hu

private theorem a1413L33Theta_center : Subgroup.center L33P = ⊥ :=
  CFSG.ComponentClassification.OddSelector.center_projectiveSL_eq_bot (k := ZMod 3) (n := 3)
    (by norm_num)

theorem l33_theta0 {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hF : genFittingFStar Q = L) (hmodel : LieModel ↥L .PSL 3 3 1) :
    ∃ θ : Q →* MulAut L33P, Function.Injective θ ∧ (∀ q : Q, q ∈ L ↔ θ q ∈ inner L33P) ∧
      inner L33P ≤ θ.range := by
  have hLsub : CFSG.ComponentClassification.GeneralizedFitting.subgroup Q = L := hF
  haveI hLn : L.Normal := hLsub ▸ CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hc : Subgroup.centralizer (L : Set Q) ≤ L :=
    hLsub ▸ CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Q
  obtain ⟨ePSL⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1
    (by norm_num) (by norm_num : Nat.card (ZMod 3) = 3 ^ 1) hmodel
  let e : ↥L ≃* L33P :=
    ePSL.trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 (ZMod 3))).symm
  obtain ⟨θ, hθ, -, -, hinner, hrange⟩ :=
    a1413_embedding hLn hc e a1413L33Theta_center
  exact ⟨θ, hθ, hinner, hrange⟩

theorem l33_exists_inner {Q : Type} [Group Q] {L A : Subgroup Q} (θ : Q →* MulAut L33P)
    (hθ : Function.Injective θ) (hL : ∀ q : Q, q ∈ L ↔ θ q ∈ inner L33P)
    (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A) : ∃ z ∈ A, z ≠ 1 ∧ z ∈ L := by
  classical
  haveI hfinA : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  letI : Fintype ↥A := Fintype.ofFinite ↥A
  have hcardA : Fintype.card ↥A = 4 := by
    rw [← Nat.card_eq_fintype_card, hA]
  have h1lt : 1 < Fintype.card ↥A := by rw [hcardA]; norm_num
  obtain ⟨a, ha1⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : ↥A)
  have haMem : (a : Q) ∈ A := a.2
  have haQ1 : (a : Q) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : (a : Q) * (a : Q) = 1 := by
    have := hAe.2 (a : Q) a.2
    simpa [pow_two] using this
  have hpair_card : ({1, a} : Finset ↥A).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]
    exact fun h => ha1 h.symm
  have hlt : ({1, a} : Finset ↥A).card < (Finset.univ : Finset ↥A).card := by
    rw [hpair_card, Finset.card_univ, hcardA]
    norm_num
  obtain ⟨b, -, hbnotmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hb1 : b ≠ 1 := by
    intro h
    exact hbnotmem (by rw [h]; exact Finset.mem_insert_self _ _)
  have hba : b ≠ a := by
    intro h
    exact hbnotmem (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hbMem : (b : Q) ∈ A := b.2
  have hbQ1 : (b : Q) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : (b : Q) * (b : Q) = 1 := by
    have := hAe.2 (b : Q) b.2
    simpa [pow_two] using this
  have hab1 : (a : Q) * (b : Q) ≠ 1 := by
    intro h
    have h' : (a : Q) = (b : Q) := by
      have := congrArg (fun x : Q => (a : Q) * x) h
      rw [← mul_assoc, ha2, one_mul, mul_one] at this
      exact this.symm
    exact hba (Subtype.ext h').symm
  by_cases ha : θ (a : Q) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L33P
  · exact ⟨(a : Q), haMem, haQ1, (hL (a : Q)).2 ha⟩
  by_cases hb : θ (b : Q) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L33P
  · exact ⟨(b : Q), hbMem, hbQ1, (hL (b : Q)).2 hb⟩
  have hprod : θ ((a : Q) * (b : Q)) ∈ inner L33P := by
    rw [map_mul]
    exact a1413L33Theta_mul_mem_inner_of_not_mem ha hb
  exact ⟨(a : Q) * (b : Q), A.mul_mem haMem hbMem, hab1, (hL _).2 hprod⟩

theorem l33_theta_norm {Q : Type} [Group Q] {L : Subgroup Q} (θ₀ : Q →* MulAut L33P)
    (hθ : Function.Injective θ₀) (hL : ∀ q : Q, q ∈ L ↔ θ₀ q ∈ inner L33P)
    (hr : inner L33P ≤ θ₀.range) {z : Q} (hzL : z ∈ L) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ θ : Q →* MulAut L33P, Function.Injective θ ∧ θ z = MulAut.conj (tInv : L33P) ∧
      (∀ q : Q, q ∈ L ↔ θ q ∈ inner L33P) ∧ inner L33P ≤ θ.range := by
  classical
  obtain ⟨h, hh⟩ := (hL z).1 hzL
  have hθzz : θ₀ z * θ₀ z = 1 := by
    rw [← map_mul, hz2, map_one]
  have hhsq : h * h = 1 := by
    apply a1413L33Theta_eq_one_of_conj_eq_one a1413L33Theta_center
    rw [map_mul, hh]
    exact hθzz
  have hhne : h ≠ 1 := by
    intro h1
    apply hz1
    apply hθ
    rw [← hh, h1, map_one, map_one]
  obtain ⟨g, hg⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.singleInv_projectiveSL_fl3
    (F := ZMod 3) (by decide) h tInv hhsq hhne tInv_mul_self (tInv_ne_one (by decide))
  let cg : MulAut L33P := MulAut.conj g
  let θ : Q →* MulAut L33P := (MulAut.conj cg).toMonoidHom.comp θ₀
  have hθinj : Function.Injective θ := (MulAut.conj cg).injective.comp hθ
  have hzθ : θ z = MulAut.conj (tInv : L33P) := by
    show MulAut.conj cg (θ₀ z) = MulAut.conj (tInv : L33P)
    rw [← hh]
    have hmul : MulAut.conj g * MulAut.conj h = MulAut.conj (g * h) :=
      (map_mul (MulAut.conj) g h).symm
    have hinv : (MulAut.conj g)⁻¹ = MulAut.conj g⁻¹ := (map_inv (MulAut.conj) g).symm
    have hcalc : (MulAut.conj g * MulAut.conj h * (MulAut.conj g)⁻¹ : MulAut L33P) =
        MulAut.conj (tInv : L33P) := by
      calc MulAut.conj g * MulAut.conj h * (MulAut.conj g)⁻¹
          = MulAut.conj (g * h) * (MulAut.conj g)⁻¹ := by rw [hmul]
        _ = MulAut.conj (g * h) * MulAut.conj g⁻¹ := by rw [hinv]
        _ = MulAut.conj ((g * h) * g⁻¹) := by rw [← map_mul]
        _ = MulAut.conj tInv := by rw [hg]
    simpa [cg] using hcalc
  have hinner : ∀ q : Q, q ∈ L ↔
      θ q ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L33P := by
    intro q
    rw [hL q]
    have hiff := a1413L33Theta_conj_mem_inner_iff cg (θ₀ q)
    simpa [θ, MulAut.conj_apply] using hiff.symm
  have hrange : CFSG.ComponentClassification.OuterAutomorphisms.inner L33P ≤ θ.range := by
    rintro x hx
    have hx' : cg⁻¹ * x * cg ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L33P := by
      have h := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L33P).conj_mem
        x hx cg⁻¹
      simpa using h
    obtain ⟨q, hq⟩ := hr hx'
    refine ⟨q, ?_⟩
    have hθq : θ q = cg * θ₀ q * cg⁻¹ := by simp [θ, MulAut.conj_apply]
    rw [hθq, hq]
    group
  exact ⟨θ, hθinj, hzθ, hinner, hrange⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
