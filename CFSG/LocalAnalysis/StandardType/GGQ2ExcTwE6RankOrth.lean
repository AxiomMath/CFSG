module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankUnit
import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrth
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBWNormSmall
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Open (IsElemAbelian)

private theorem gamma_card_eq_ggLAut_range {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {R : Type} [Group R]
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hN).range =
      Nat.card ((ggLAut J θ).comp (Subgroup.inclusion hN)).range := by
  let ψ : ↥Bs →* MulAut R := (ggLAut J θ).comp (Subgroup.inclusion hN)
  have hker : ψ.ker = (ggGamma J hN).ker := by
    ext b
    constructor
    · intro h
      exact (ggGamma_eq_one_iff J hN b).mpr
        (mem_centralizer_of_ggLAut_eq_one J θ hJperf h)
    · intro h
      exact ggLAut_eq_one_of_mem_centralizer J θ ((ggGamma_eq_one_iff J hN b).mp h)
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 := Subgroup.card_ker_mul_card_range (ggGamma J hN)
  rw [hker] at h1
  haveI : Finite ↥(ggGamma J hN).ker := Subtype.finite
  haveI : Finite ↥ψ.ker := Subtype.finite
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)).symm

private theorem false_of_actor_autR_bound_three {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {R : Type} [Group R] {I : Set (MulAut R)}
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I)
    (hBs : IsElemAbelian 3 Bs)
    (hγ3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range)
    (hbound : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 X → Nat.card X < 3 ^ 3) : False := by
  let ψ : ↥Bs →* MulAut R := (ggLAut J θ).comp (Subgroup.inclusion hN)
  have hXsub : ((ψ.range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact hBI b b.2
  have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2)
  have hXab : IsElemAbelian 3 ψ.range := isElemAbelian_range hBc hBp ψ
  have hlt := hbound ψ.range hXsub hXab
  have hEq : Nat.card (ggGamma J hN).range = Nat.card ψ.range := by
    simpa [ψ] using gamma_card_eq_ggLAut_range hJperf θ hN
  rw [hEq] at hγ3
  exact (not_lt_of_ge hγ3) hlt

theorem excTwE6_rank_of_orth
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (hT : lab = ⟨.D, 4, 1⟩ ∨ lab = ⟨.twD, 5, 1⟩ ∨ lab = ⟨.triD4, 0, 1⟩) :
    3 ^ 5 ≤ Nat.card Bs := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hmark : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hS.2.1
  have hmarkRelabel := ggInnerDiagOn_relabel ggLabelRigidInput_holds hmark hΛ hhas
  rcases hT with hl | hl | hl
  ·
    subst hl
    obtain ⟨hperf, lab', hlab', hraw⟩ := hmarkRelabel
    obtain ⟨_, _, _, _, _, _, _, hP⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨hlabel, -, -⟩ := hP
    subst hlabel
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hK, hQ⟩ := hraw
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨-, hBsN, hBsI⟩ := hP
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hγ : 3 ^ 4 ≤ Nat.card (ggGamma L hBsN).range :=
      ggQ2OrthPlus_gamma_lower (m := 4) (θ := θ) hS hK2 (by norm_num) (by norm_num)
        hperf hBsN hBsI
    have hcard := card_range_ggGamma_bstar_mul_three hcfg hBsN
    calc 3 ^ 5 = 3 ^ 4 * 3 := by norm_num
      _ ≤ Nat.card (ggGamma L hBsN).range * 3 := Nat.mul_le_mul_right 3 hγ
      _ = Nat.card Bs := hcard
  ·
    subst hl
    obtain ⟨hperf, lab', hlab', hraw⟩ := hmarkRelabel
    obtain ⟨_, _, _, _, _, _, _, hP⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨hlabel, -, -⟩ := hP
    subst hlabel
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hK, b, c, hbc, hQ⟩ := hraw
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨-, hBsN, hBsI⟩ := hP
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hγ : 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range :=
      ggQ2OrthMinus_gamma_lower (m := 5) (θ := θ) hS hK2 (by norm_num) (by norm_num)
        hbc hperf hBsN hBsI
    have hcard := card_range_ggGamma_bstar_mul_three hcfg hBsN
    calc 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range := hγ
      _ ≤ Nat.card (ggGamma L hBsN).range * 3 := Nat.le_mul_of_pos_right _ (by norm_num)
      _ = Nat.card Bs := hcard
  ·
    subst hl
    have hMarkA := largeEvenMarking_and_labelAll
      (S := fun lab' : LargeEvenLabel => lab' = ⟨.triD4, 0, 1⟩)
      (P' := fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3)
      (fun lab' hlab' hs => by
        subst hs
        exact NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all
          Nat.prime_three (by norm_num) hlab' rfl)
      (fun _ _ _ _ _ _ hP => hP.1) hmarkRelabel
    obtain ⟨hperf, lab', hlab', hraw⟩ := hMarkA
    obtain ⟨R, _, I, F, hsimple, hna, θ, hP, hbound⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, hBsN, hBsI⟩ := hP
    have hBs : IsElemAbelian 3 Bs := (hcfg.tableB_facts).2.1
    have hγ3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
      ggQ2Orth_three_le_card_gamma hS hBsN
    exact (false_of_actor_autR_bound_three hperf θ hBsN
      (fun b hb => ggLAut_mem_of_induces L θ hBsN hBsI hb) hBs hγ3 hbound).elim

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
