module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
import CFSG.RankThree.PartTwo.Sec11.SimsR1L38AutB
public import CFSG.RankThree.PartTwo.KFacts.K72L3Fix

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace L38Aut

theorem pCore_two_eq_bot_of_quasisimple {C : Type*} [Group C] [Finite C]
    (hc : Subgroup.center C = ⊥) (hq : CFSG.IsQuasisimple C) (h3 : 3 ∣ Nat.card C) :
    CFSG.pCore 2 C = ⊥ := by
  have hsimple : IsSimpleGroup C := by
    haveI := hq.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hc).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  haveI := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 C) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (CFSG.pCore 2 C) := CFSG.pCore_isPGroup
    rw [h] at hp
    have hp' : IsPGroup 2 C := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hp'
    rw [hn] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem pCore_two_fixedSub_eq_bot {X : Type} [Group X] [Finite X]
    (hX : Sec8.IsoLThreeMinusPi X 2 3) {σ : MulAut X} (hσ : orderOf σ = 3)
    (hσi : σ ∉ (MulAut.conj : X →* MulAut X).range) :
    CFSG.pCore 2 (Sec11.fixedSub σ) = ⊥ := by
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  obtain ⟨hc, hq, h3⟩ := fixedPoints_facts_of_isoLThreeMinusPi (n := 1) le_rfl hX hσ3 hσi
  exact pCore_two_eq_bot_of_quasisimple hc hq h3

section Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2] [hF8 : Fact (Nat.card F = 8)]

theorem isCyclic_of_equiv {X : Type} [Group X] (e : X ≃* projectiveSL 3 F) :
    ∀ x : X, orderOf x = 3 → ∀ P : Subgroup (MulAut X), IsPGroup 2 P →
      (∀ τ ∈ P, τ x = x) → IsCyclic P := by
  intro x hx P hP hfix
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  let ι := Subgroup.equivMapOfInjective P (MulAut.congr e).toMonoidHom hinj
  have hP' : IsPGroup 2 (P.map (MulAut.congr e).toMonoidHom) := hP.of_equiv ι
  have hx' : orderOf (e x) = 3 := (orderOf_injective e.toMonoidHom e.injective x).trans hx
  have hfix' : ∀ τ ∈ P.map (MulAut.congr e).toMonoidHom, τ (e x) = e x := by
    rintro _ ⟨τ₀, hτ₀, rfl⟩
    simp [MulAut.congr_apply, hfix τ₀ hτ₀]
  exact ι.isCyclic.mpr (isCyclic_of_two_subgroup_fixing hx' _ hP' hfix')

theorem eq_one_of_fixes_fixedSub {X : Type} [Group X] [Finite X] (e : X ≃* projSL 3 F)
    {σ τ : MulAut X} (hσ : orderOf σ = 3) (hσi : σ ∉ (MulAut.conj : X →* MulAut X).range)
    (hτ : ∃ k : ℕ, τ ^ 2 ^ k = 1) (hfix : ∀ x ∈ Sec11.fixedSub σ, τ x = x) : τ = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  obtain ⟨ψ, -, θ, hθ⟩ :=
    exists_congr_eq_fieldAut_of_mulEquiv_projSL (card_mod_three (F := F)) e hσ3 hσi
  obtain ⟨k, hk⟩ := hτ
  have hτ' : (MulAut.congr θ τ) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have key := eq_one_of_fixes_transvections hτ' (fun i j h => by
    obtain ⟨z, hz⟩ : ∃ z, θ z = proj 3 F (tv i j h) := ⟨θ.symm _, θ.apply_symm_apply _⟩
    have hσz : σ z = z := by
      have h1 := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (θ z)) hθ
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      rw [hz, fieldAut_proj_tv, ← hz] at h1
      exact θ.injective h1
    have hτz : τ z = z := hfix z hσz
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [← hz, MulEquiv.symm_apply_apply, hτz])
  exact (map_eq_one_iff _ (MulAut.congr θ).injective).mp key

end Transport

end L38Aut

theorem l38AutFacts_holds : SimsR1L38AutFacts := by
  intro X _ _ hX
  haveI : Fact (Nat.card (GaloisField 2 3) = 8) :=
    ⟨by rw [GaloisField.card 2 3 (by norm_num)]; norm_num⟩
  obtain ⟨e⟩ : Nonempty (X ≃* projSL 3 (GaloisField 2 3)) := by
    rcases hX with ⟨h, -⟩ | ⟨-, he⟩
    · norm_num at h
    · exact he
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 3)
  exact ⟨L38Aut.isCyclic_of_equiv (e.trans φ),
    fun σ hσ hσi => L38Aut.pCore_two_fixedSub_eq_bot hX hσ hσi,
    fun σ τ hσ hσi hτ hfix => L38Aut.eq_one_of_fixes_fixedSub e hσ hσi hτ hfix⟩

end CFSG.RankThree.PartTwo.Sec11.SimsR1
