module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank
open CFSG.EvenSmallLie.CatalogOrders

private theorem card_projectiveSL_eq_lieOrd {K : Type} [Field K] [Finite K] {n r f : ℕ}
    (hr : r.Prime) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (hn : 3 ≤ n) :
    Nat.card (projectiveSL n K) = lieOrd .PSL n (r ^ f) := by
  have hne2 : (n, r ^ f) ≠ (2, 2) := by
    intro h
    have h1 : n = 2 := congrArg Prod.fst h
    omega
  have hne3 : (n, r ^ f) ≠ (2, 3) := by
    intro h
    have h1 : n = 2 := congrArg Prod.fst h
    omega
  have hmodel : StatedClassicalModel (StatedProj (StatedSL n K)) .PSL n r f :=
    ⟨⟨hr, hf, by omega, hne2, hne3⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  exact (Nat.card_congr ((LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K)).toEquiv).trans
    (card_eq_lieOrd_of_classical hmodel)

theorem fixesSylowOutside_projectiveSL {K : Type} [Field K] [Finite K] {n r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    FixesSylowOutside (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup n K) p := by
  intro α hαp hαD
  have hα1 : α ≠ 1 := fun h => hαD (h ▸ (linearAutGroup n K).one_mem)
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  have : Fact r.Prime := ⟨hr⟩
  have : CharP K r := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hαE : α ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two (by omega)) hαp
  obtain ⟨hpf, σ, -, ⟨δ, -, hδ⟩, hcard⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hr hf hn hK hp hαE hαD hαord
  let k := semilinearFixedSubfield σ
  have hkcard : Nat.card k = r ^ (f / p) := hcard
  have hf0 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  let ι : projectiveSL n k →* projectiveSL n K :=
    δ.toMonoidHom.comp (linearSubfieldInclusion n k)
  have hι : Function.Injective ι :=
    δ.injective.comp (linearSubfieldInclusion_injective (by omega) k)
  have hfix : ∀ y, α (ι y) = ι y := by
    intro y
    change α (δ (linearSubfieldInclusion n k y)) = δ (linearSubfieldInclusion n k y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact congrArg δ (fieldAut_linearSubfieldInclusion (k := k) (σ := σ) (fun c hc => by
      change σ c = c at hc
      exact hc) y)
  have hcardX : Nat.card (projectiveSL n K) = lieOrd .PSL n (r ^ f) :=
    card_projectiveSL_eq_lieOrd hr hf hK hn
  have hcardH : Nat.card (projectiveSL n k) = lieOrd .PSL n (r ^ (f / p)) :=
    card_projectiveSL_eq_lieOrd hr hf0 hkcard hn
  have hpow : r ^ f = (r ^ (f / p)) ^ p := by
    conv_lhs => rw [← Nat.div_mul_cancel hpf]
    rw [pow_mul]
  have hq : Odd (r ^ (f / p)) := (hr.odd_of_ne_two hr2).pow
  have hk : Odd p := hp.odd_of_ne_two (by omega)
  have hfac : (Nat.card (projectiveSL n k)).factorization 2 =
      (Nat.card (projectiveSL n K)).factorization 2 := by
    rw [hcardH, hcardX, hpow]
    exact (factorization_two_lieOrd_pow .PSL n hq hk).symm
  exact exists_isSylowOf_fixed_of_injective ι hι α hfix hfac

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
