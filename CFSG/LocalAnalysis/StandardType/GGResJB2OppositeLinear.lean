module

public import CFSG.LocalAnalysis.StandardType.GGResJPairedRankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankOne
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open Matrix Polynomial CoordSL Multiplicative SpCoord
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.StandardType.ResJPairedBlock.ActualA
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

private theorem false_of_elemAbelian_nine_of_linear_lowRank
    {H : Type} [Group H] [Finite H] {rank n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.A, rank, n⟩ : LargeEvenLabel))
    (hHas : GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel) H)
    (h3n : 3 ∣ 2 ^ n + 1) (hrank : rank ≤ 2)
    {E : Subgroup H} (hEa : IsElemAbelian 3 E) (hEcard : 9 ≤ Nat.card E) : False := by
  classical
  have hΛ' := hΛ
  dsimp only [LargeEvenInLambda2] at hΛ'
  have hrank1 : 1 ≤ rank := hΛ'.2.1
  have hhas' := hHas
  dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas'
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hhas'
  let : Field K := hKfield
  let : Finite K := hKfinite
  obtain ⟨e₀⟩ := hQ
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro hzero
    have h2dvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp hzero
    norm_num at h2dvd
  have hq : 2 ^ n % 3 = 2 := by
    have h0 : (2 ^ n + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3n
    have h1 : (2 ^ n + 1) % 3 = (2 ^ n % 3 + 1) % 3 := by
      simp
    have hlt : 2 ^ n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : 2 ^ n % 3 = 0 ∨ 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2) with h | h | h
    · exfalso
      rw [h] at h1
      norm_num at h1
      omega
    · exfalso
      rw [h] at h1
      norm_num at h1
      omega
    · exact h
  rcases (by omega : rank = 1 ∨ rank = 2) with h1 | h2
  · subst h1
    let eR : LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃*
        StatedProj (StatedSL 2 K) := by
      rw [largeEvenSLGroup_eq_statedSL]
    let e : H ≃* StatedProj (StatedSL 2 K) := e₀.trans eR
    let E' : Subgroup (StatedProj (StatedSL 2 K)) := E.map e.toMonoidHom
    have hE'a : IsElemAbelian 3 E' := hEa.map e.toMonoidHom
    have hE'card : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (K := E) (f := e.toMonoidHom) e.injective
    have hbound := CFSG.HardMathSupport.Malle.E27Lie.card_le_of_statedProj_SL
      (F := K) (n := 2) h3K (by norm_num) E' hE'a
    norm_num at hbound
    omega
  · subst h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let eR : LargeEvenProj (LargeEvenSLGroup (Fin 3) K) ≃*
        StatedProj (StatedSL 3 K) := by
      rw [largeEvenSLGroup_eq_statedSL]
    let e : H ≃* StatedProj (StatedSL 3 K) := e₀.trans eR
    let E' : Subgroup (StatedProj (StatedSL 3 K)) := E.map e.toMonoidHom
    have hE'a : IsElemAbelian 3 E' := hEa.map e.toMonoidHom
    have hE'card : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (K := E) (f := e.toMonoidHom) e.injective
    have hb := pRank_projSL_three_le_one (F := K) (p := 2) (e := n) hKcard hq
    have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le
      (G := StatedProj (StatedSL 3 K))
      Nat.prime_three hb E' hE'a
    norm_num at hbound
    omega

theorem GGResHyp.exists_lineJLabel_of_B2_oppositeLinear
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .B2 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, _, hP₀⟩ := hQ₀
  have htag : tag = .A := hP₀.1.1
  have h3n : 3 ∣ 2 ^ n + 1 := hP₀.1.2
  subst htag
  have hHas : GGHasLabel (⟨.A, rank, n⟩ : LargeEvenLabel)
      (J ⧸ Subgroup.center J) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    intro R' _ I' F' hQ'
    obtain ⟨-, -, θ', -⟩ := hQ'
    exact ⟨θ'⟩
  have hEquot : ∃ E' : Subgroup (J ⧸ Subgroup.center J),
      IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
    obtain ⟨E, hE, hEelem, hEcard, hEbot⟩ := exists_coroot_subgroup_of_B2 hN hD
    have hEJ : E ≤ J := hE.trans inf_le_right
    let H : Subgroup ↥J := E.subgroupOf J
    let π : ↥J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
    have hker : H ⊓ Subgroup.center ↥J = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro z ⟨hzH, hzZ⟩
      have hzE : (z : G) ∈ E := hzH
      have hzC : (z : G) ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hzc := Subgroup.mem_center_iff.mp hzZ (⟨j, hj⟩ : ↥J)
        exact congrArg Subtype.val hzc
      have hmem : (z : G) ∈ E ⊓ Subgroup.centralizer (J : Set G) := ⟨hzE, hzC⟩
      rw [hEbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hinj_on : Set.InjOn π (H : Set ↥J) := by
      intro a ha b hb hab
      have hq : π a = π b := hab
      have hz : a / b ∈ Subgroup.center ↥J := (QuotientGroup.eq_iff_div_mem).mp hq
      have hzH : a / b ∈ H := H.div_mem ha hb
      have hz1 : a / b = 1 := by
        have hmem : a / b ∈ H ⊓ Subgroup.center ↥J := ⟨hzH, hz⟩
        rwa [hker, Subgroup.mem_bot] at hmem
      exact div_eq_one.mp hz1
    let E' : Subgroup (J ⧸ Subgroup.center J) := H.map π
    have hE'card : Nat.card E' = 9 := by
      have h1 : Nat.card E' = Nat.card H := by
        dsimp only [E']
        change Nat.card (π '' (H : Set ↥J)) = Nat.card H
        exact Nat.card_image_of_injOn hinj_on
      calc Nat.card E' = Nat.card H := h1
        _ = Nat.card E := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
        _ = 9 := hEcard
    exact ⟨E', (hEelem.subgroupOf J).map π, hE'card⟩
  have hrank34 : rank = 3 ∨ rank = 4 := by
    rcases Nat.lt_or_ge rank 3 with hlt | hge
    · exfalso
      obtain ⟨E', hE'a, hE'card⟩ := hEquot
      exact false_of_elemAbelian_nine_of_linear_lowRank hΛ hHas h3n (by omega) hE'a
        (by omega)
    · rcases Nat.lt_or_ge rank 5 with hlt5 | hge5
      · omega
      · exfalso
        have hrank5 : 5 ≤ rank := hge5
        have hMarkLab : GGInnerDiagOnLabel
            (fun _ l => l = (⟨.A, rank, n⟩ : LargeEvenLabel)) 3 Bs J := by
          refine ⟨hperfJ, ⟨.A, rank, n⟩, hΛ, ?_⟩
          refine largeEvenRawDatum_mono (lab := (⟨.A, rank, n⟩ : LargeEvenLabel))
            (fun R _ I F hQ => ?_) hraw
          obtain ⟨hs, hna, θ, hP⟩ := hQ
          exact ⟨hs, hna, θ, ⟨rfl, hP.2.1, hP.2.2⟩⟩
        obtain ⟨F, hFfield, hFfinite, hFchar, hFcard, hFsign, φ, hφsurj, hkerφ, hYact,
          _hHas'⟩ := exists_actual_oppositeLinear_cover_of_marking
            (hH := hH) (hMark := hMarkLab) (h3f := h3n) (h5 := by omega)
        let : Field F := hFfield
        let : Finite F := hFfinite
        let : CharP F 2 := hFchar
        let d : ℕ := rank + 1
        have hpK : ¬ 3 ∣ Nat.card F - 1 := hFsign
        have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 := by
          let E : Subgroup G := Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)
          have hEBs : E ≤ Bs := inf_le_left.trans inf_le_left
          have hEJ : E ≤ J := inf_le_left.trans inf_le_right
          have hcenter3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥J) :=
            not_three_dvd_center_J_of_pairedCover (J := J) (n := rank + 1) (K := F)
              φ hφsurj hkerφ (by omega) hpK
          let E' : Subgroup ↥J := E.subgroupOf J
          have hE'le : E' ≤ Subgroup.center ↥J := by
            intro x hx
            rw [Subgroup.mem_center_iff]
            intro y
            apply Subtype.ext
            have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
            have hxC : (x : G) ∈ Subgroup.centralizer (J : Set G) :=
              (Subgroup.mem_inf.mp hxE).2
            exact Subgroup.mem_centralizer_iff.mp hxC (y : G) y.2
          have hE'card : Nat.card E' = Nat.card E :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
          have hcarddvd : Nat.card E ∣ Nat.card (Subgroup.center ↥J) := by
            rw [← hE'card]
            exact Subgroup.card_dvd_of_le hE'le
          have hE3 : IsPGroup 3 E := (hH.1.2.1.2.1.mono hEBs).isPGroup
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
          have hk0 : k = 0 := by
            by_contra hkne
            have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
            have h3dvdE : 3 ∣ Nat.card E := by
              rw [hk]
              exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hkpos)
            exact hcenter3 (h3dvdE.trans hcarddvd)
          have hEcard : Nat.card E = 1 := by
            rw [hk, hk0, pow_zero]
          change Nat.card E ≤ 3
          omega
        obtain ⟨g, hg, hgd⟩ := LineL2.exists_irreducible_factor_cyclotomic_three F
        let : Fact (Irreducible g) := ⟨hg⟩
        have hpq : 3 ∣ Nat.card F + 1 := by rw [hFcard]; exact h3n
        have hp3 : ((3 : ℕ) : F) ≠ 0 :=
          TableBSymp.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num)
        have hC : (CoordSL.rootMat g).det = 1 :=
          CoordSL.det_rootMat Nat.prime_three hpK hp3 hgd
        have hCp : (CoordSL.rootMat g) ^ 3 = 1 :=
          CoordSL.rootMat_pow_eq_one Nat.prime_three hp3 hgd
        have hCardA : 9 ≤ Nat.card (ggGamma J hN).range :=
          card_gamma_nine_of_GGResHyp hN hH
        have hY : ∀ a ∈ (ggGamma J hN).range,
            ∃ Y : Matrix.GeneralLinearGroup (Fin d) F,
              ∀ x : Matrix.SpecialLinearGroup (Fin d) F,
                a (φ x) = φ (CatalogueBHigherLinearAction.slConjugation d F Y x) := by
          rintro a ⟨b, rfl⟩
          obtain ⟨Y, hYb⟩ := hYact b
          refine ⟨Y, fun x => ?_⟩
          apply Subtype.ext
          change (b : G) * ((φ x : ↥J) : G) * (b : G)⁻¹ =
            ((φ (CatalogueBHigherLinearAction.slConjugation d F Y x) : ↥J) : G)
          exact hYb x
        obtain ⟨s, rr, ε, A₀, hs2, hframeA, hr1, Θ, hsp, hsgn, hperm, hcard⟩ :=
          RankTwo.actual_exact_automizer_of_boundary_frame
            (hN := hN) (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2)
            (hNoTr := hH.2.2.2.1) (hZ := hZ)
            (φ := φ) (hφ := hφsurj) (hker := hkerφ) (n := d)
            (hn3 := by omega) (hpK := hpK) (hJperf := hperfJ)
            (g := g) (hC := hC) (hCp := hCp) (hgd := hgd)
            (hCardA := hCardA) (hY := hY)
        have h8 : Nat.card (ggAutomizer J Bs) = 8 :=
          ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
        have hs2' : s = 2 := by
          have hle : s ≤ 2 := by
            by_contra hle
            have h3 : 3 ≤ s := by omega
            have hpow8 : 8 ≤ 2 ^ s := by
              have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
              norm_num at h ⊢
              exact h
            have hfact : 6 ≤ s.factorial := by
              have h := Nat.factorial_le h3
              norm_num at h ⊢
              exact h
            have h48 : 48 ≤ 2 ^ s * s.factorial := Nat.mul_le_mul hpow8 hfact
            have hcard8 : 2 ^ s * s.factorial = 8 := by rw [← hcard, h8]
            omega
          omega
        have hcardε : (CoordSL.rootPB g).dim * s + rr = rank + 1 := by
          have h := Fintype.card_congr ε
          dsimp [d] at h
          simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_sum] at h
          omega
        have hdim : (CoordSL.rootPB g).dim = 2 :=
          SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) hp3 hgd hpq
        have hle5 : rank + 1 ≤ 5 := by
          calc rank + 1 = (CoordSL.rootPB g).dim * s + rr := hcardε.symm
            _ = 2 * 2 + rr := by rw [hdim, hs2']
            _ ≤ 5 := by omega
        omega
  refine ⟨(⟨.A, rank, n⟩ : LargeEvenLabel), hΛ, ?_, hHas⟩
  unfold ggResLineJLabel
  exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, hrank34⟩, h3n⟩))

end CFSG.StandardType

end
