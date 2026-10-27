module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixBase
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddSubfield
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.EvenSmallLie.CatalogOrders

theorem fixesSylowOutside_psp {X : Type} [Group X] [Finite X] {n r f : ℕ} (hr2 : r ≠ 2)
    (hX : CFSG.Blueprint.LieModel X .PSp n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    FixesSylowOutside X (inner X) p := by
  intro α hα hout
  have hα1 : α ≠ 1 := fun h => hout (h ▸ (inner X).one_mem)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf α = p := orderOf_eq_prime hα hα1
  obtain ⟨⟨hr, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hθ' : orderOf (MulAut.congr e α) = p :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hord
  have hout' : MulAut.congr e α ∉
      (MulAut.conj : StatedProj (StatedSp n K) →* MulAut (StatedProj (StatedSp n K))).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have h := congrArg (fun β : MulAut (StatedProj (StatedSp n K)) => e.symm (β (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  have hne : NeZero n := ⟨by omega⟩
  have : Fact r.Prime := ⟨hr⟩
  have O := spOuter hr hf hn hK
  have hθE : MulAut.congr e α ∈ spSemilinearAutGroup n K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hθ' ▸ hp.odd_of_ne_two (by omega))
  have hθp : (MulAut.congr e α) ^ p = 1 := hθ' ▸ pow_orderOf_eq_one _
  have hθD : MulAut.congr e α ∉ spLinearAutGroup n K := fun hD =>
    hout' (mem_of_pow_eq_one_of_relIndex_dvd_two
      (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp (by omega) hD hθp)
  obtain ⟨hrf, σ, hσ, δ, -, hδ⟩ := O.descent p hp (MulAut.congr e α) hθE hθD hθ'
  let k := descentField σ
  have hcard : Nat.card k = r ^ (f / p) := (card_semilinearFixedSubfield hr hf hK hσ).2
  have hf0 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hrf) hp.pos
  let ι : StatedProj (StatedSp n k) →* StatedProj (StatedSp n K) :=
    δ.toMonoidHom.comp (subfieldInj σ)
  have hι : Function.Injective ι := δ.injective.comp (subfieldInj_injective σ)
  have hfix : ∀ y, MulAut.congr e α (ι y) = ι y := by
    intro y
    change MulAut.congr e α (δ (subfieldInj σ y)) = δ (subfieldInj σ y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    apply congrArg δ
    obtain ⟨g, rfl⟩ := proj_surjective y
    rw [subfieldInj_proj]
    exact fieldAut_subfieldProj σ g
  let ι' : StatedProj (StatedSp n k) →* X := e.symm.toMonoidHom.comp ι
  have hι' : Function.Injective ι' := e.symm.injective.comp hι
  have hfix' : ∀ y, α (ι' y) = ι' y := by
    intro y
    apply e.injective
    have hy := hfix y
    simpa [ι', MulAut.congr_apply] using hy
  have htmem : .PSp ∈ CFSG.Blueprint.classicalTags := by decide
  have hcardX : Nat.card X = lieOrd .PSp n (r ^ f) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
      (hX.statedClassicalModel htmem)
  have hne2 : (n, r ^ (f / p)) ≠ (2, 2) := by
    intro h
    have h2 : r ^ (f / p) = 2 := congrArg Prod.snd h
    have hodd : Odd (r ^ (f / p)) := (hr.odd_of_ne_two hr2).pow
    exact (by norm_num : ¬ Odd 2) (h2 ▸ hodd)
  have hmodel0 : CFSG.Open.StatedClassicalModel (StatedProj (StatedSp n k)) .PSp n r (f / p) :=
    ⟨⟨hr, hf0, hn, hne2⟩, k, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩
  have hcardH : Nat.card (StatedProj (StatedSp n k)) = lieOrd .PSp n (r ^ (f / p)) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hmodel0
  have hpow : r ^ f = (r ^ (f / p)) ^ p := by
    conv_lhs => rw [← Nat.div_mul_cancel hrf]
    rw [pow_mul]
  have hq : Odd (r ^ (f / p)) := (hr.odd_of_ne_two hr2).pow
  have hk : Odd p := hp.odd_of_ne_two (by omega)
  have hfac : (Nat.card (StatedProj (StatedSp n k))).factorization 2 =
      (Nat.card X).factorization 2 := by
    rw [hcardH, hcardX, hpow]
    exact (factorization_two_lieOrd_pow .PSp n hq hk).symm
  exact exists_isSylowOf_fixed_of_injective ι' hι' α hfix' hfac

theorem fixesSylowOutside_pomega {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    {t : CFSG.Open.StatedLieTag} {n r f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible t n r f) (hX : CFSG.Blueprint.LieModel X t n r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : FixesSylowOutside X (inner X) p := by
  intro α hα hout
  have hα1 : α ≠ 1 := fun h => hout (h ▸ (inner X).one_mem)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf α = p := orderOf_eq_prime hα hα1
  have : IsSimpleGroup X := hXs
  have hrg : ¬ p ∣ (CFSG.Blueprint.Multiplier.genericOrders t n r f).1 := by
    intro hd
    have h1 : t ≠ .PSL := by rcases ht with rfl | rfl | rfl <;> decide
    have h2 : t ≠ .PSU := by rcases ht with rfl | rfl | rfl <;> decide
    have hle := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_le_four
      h1 h2 n r f
    have hpos := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos hadm
    have hp4 : p ≤ 4 := (Nat.le_of_dvd hpos hd).trans hle
    omega
  obtain ⟨hpf, Y, hY, hmodel⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.fieldAutOdd_remainingClassical_subfield
      (X := X) (t := t) (n := n) (p := r) (f := f) (r := p)
      (Or.inr ht) hadm.1 hr2 hadm hX hp hp5 hrg α hord hout
  have htmem : t ∈ CFSG.Blueprint.classicalTags := by rcases ht with rfl | rfl | rfl <;> decide
  have hcardY : Nat.card Y = lieOrd t n (r ^ (f / p)) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
      (hmodel.statedClassicalModel htmem)
  have hcardX : Nat.card X = lieOrd t n (r ^ f) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
      (hX.statedClassicalModel htmem)
  have hpow : r ^ f = (r ^ (f / p)) ^ p := by
    conv_lhs => rw [← Nat.div_mul_cancel hpf]
    rw [pow_mul]
  have hq : Odd (r ^ (f / p)) := (hadm.1.odd_of_ne_two hr2).pow
  have hk : Odd p := hp.odd_of_ne_two (by omega)
  have hfac : (Nat.card Y).factorization 2 = (Nat.card X).factorization 2 := by
    rw [hcardY, hcardX, hpow]
    exact (factorization_two_lieOrd_pow t n hq hk).symm
  exact exists_isSylowOf_fixed_of_le α hY hfac

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
