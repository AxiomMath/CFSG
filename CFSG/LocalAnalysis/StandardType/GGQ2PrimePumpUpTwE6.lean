module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpE6
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpSym3
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Line
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Card
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6A4A1Sym3
import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup comm_mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (twistedE6InndiagConj)
open CFSG.LocalAnalysis.GLTheoremA.S265.TE6 (exists_twE6LineModel_of_glaPComponent
  twE6MatFixDim_eq_28_of_card_u5two exists_sym3_centralizing_of_dim28)
open CFSG.RankThree.PartTwo.Sec4.Ronan148L (glaPComponent_three_of_isComponentOf)

theorem pumpUpTwistedE6Input_holds :
    PumpUpTwistedE6Input := by
  intro K _ _ W Wk ζ ξ Q A h h6
  classical
  obtain ⟨β, hβ⟩ : ∃ β : MulAut (K ⧸ center K),
      ∀ k, QuotientGroup.mk' (center K) (ζ k) = β (QuotientGroup.mk' (center K) k) :=
    ⟨QuotientGroup.congr (center K) (center K) ζ (Subgroup.map_center_eq ζ), fun _ => rfl⟩
  set π : K →* K ⧸ center K := QuotientGroup.mk' (center K) with hπ
  have hker : π.ker ≤ center K := by rw [hπ, QuotientGroup.ker_mk']
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hpow : ∀ (n : ℕ) (k : K), (β ^ n) (π k) = π ((ζ ^ n) k) := by
    intro n
    induction n with
    | zero => intro k; rw [pow_zero, pow_zero, MulAut.one_apply, MulAut.one_apply]
    | succ n ih =>
      intro k
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hβ, ih]
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := hπs x
    rw [hpow, h.ζ_cube, MulAut.one_apply, MulAut.one_apply]
  have hβ1 : β ≠ 1 := by
    intro h1
    have hfix : ∀ k, π k ∈ fixSubgroup β := fun k =>
      mem_fixSubgroup.2 (by rw [h1, MulAut.one_apply])
    have hc : commutator K ≤ fixSubgroup ζ := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      exact fun k₁ _ k₂ _ => comm_mem_fixSubgroup π hker ζ β hβ (hfix k₁) (hfix k₂)
    refine h.ζ_ne (MulEquiv.ext fun k => ?_)
    have hk : k ∈ commutator K := by
      rw [h.quasi.1]
      exact Subgroup.mem_top k
    rw [MulAut.one_apply]
    exact mem_fixSubgroup.1 (hc hk)
  have hWcl : StatedClassicalModel W .PSU 5 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.W_model
    · exact hc
    · omega
  haveI : IsSimpleGroup W := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWcl
  have hWcard : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hWcl
  have hWnp : ¬ (Nat.card W).Prime := by
    rw [hWcard]
    norm_num
  have hπW : Function.Injective (π.comp W.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have hs' : s ∈ center W := mem_center_iff.2 fun b => Subtype.ext (mem_center_iff.1 hs b)
    rwa [CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup hWnp] at hs'
  have hWc : IsComponentOf W (fixSubgroup ζ) := by
    have hAF : autFix ζ = fixSubgroup ζ := Subgroup.ext fun _ => Iff.rfl
    rw [← hAF]
    exact h.W_comp
  have hJ := glaPComponent_map_fixSubgroup π hker ζ β hβ hπs Nat.prime_three
    (glaPComponent_three_of_isComponentOf hWc (by rw [hWcard]; norm_num))
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs (K ⧸ center K)
      CFSG.LocalAnalysis.GLTheoremA.S9.isTE6two := by
    obtain ⟨-, hc | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := h6
    · exact (hc.2 : False).elim
    cases d with
    | twistedE6 q =>
      obtain ⟨hp, hf⟩ := hd
      refine ⟨.lie ⟨.twistedE6 q, hv⟩, ?_, ⟨e⟩⟩
      show q.card = 2
      rw [TauCeti.PrimePower.card_def, hp, hf, pow_one]
    | _ => exact (hd : False).elim
  obtain ⟨K₀, _, _, σ, hK, hσ, e, h₀, hh3, hh1, _D, _i, hβe, -, -, hcomp, -⟩ :=
    exists_twE6LineModel_of_glaPComponent hcat hβ3 hβ1 hJ
  have hmapW : W.map π = (π.comp W.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ : W ≃* ↥((W.map π).map e.toMonoidHom) :=
    ((MonoidHom.ofInjective hπW).trans (MulEquiv.subgroupCongr hmapW.symm)).trans
      ((W.map π).equivMapOfInjective e.toMonoidHom e.injective)
  have hW0 : Nat.card (↥W ⧸ center ↥W) = 13685760 := by
    rw [CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup hWnp, ← hWcard]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  have hc := (Nat.card_congr (QuotientGroup.congr (center W) (center _) ψ
    (Subgroup.map_center_eq ψ)).toEquiv).symm.trans hW0
  obtain ⟨t, ht, m, hm, -, hmJ, hm3, hm1, htm, -⟩ := exists_sym3_centralizing_of_dim28 hK hσ hh3
    hh1 (twE6MatFixDim_eq_28_of_card_u5two hK hσ hh3 hh1 hcomp hc) hcomp
  have hfix : ∀ x, twistedE6InndiagConj K₀ σ h₀ x = x → β (e.symm x) = e.symm x := by
    intro x h1
    rw [← hβe] at h1
    change e (β (e.symm x)) = x at h1
    exact e.injective (h1.trans (e.apply_symm_apply x).symm)
  have hcen : ∀ x ∈ centralizer ((W.map π).map e.toMonoidHom : Set _), ∀ w ∈ W,
      Commute (e.symm x) (π w) := by
    intro x hx w hw
    show e.symm x * π w = π w * e.symm x
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact (mem_centralizer_iff.1 hx _ (mem_map_of_mem e.toMonoidHom (mem_map_of_mem π hw))).symm
  have hm3' : e.symm m ^ 3 = 1 := by
    have h3 := congrArg e.symm hm3
    rwa [map_pow, map_one] at h3
  have htm' : e.symm t * e.symm m * (e.symm t)⁻¹ = (e.symm m)⁻¹ := by
    have h3 := congrArg e.symm htm
    rwa [map_mul, map_mul, map_inv, map_inv] at h3
  exact h.false_of_sym3_lift hβ (hfix t (ht _ (Subgroup.mem_zpowers _)))
    (hfix m (hm _ (Subgroup.mem_zpowers _))) (hcen m hmJ) hm3'
    (fun h1 => hm1 (e.symm.injective (h1.trans (map_one e.symm).symm))) htm'

end CFSG.GGQ2Prime
