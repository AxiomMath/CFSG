module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2261
public import Certificates.Certificate2269
public import Certificates.Certificate8032
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
import CFSG.LocalAnalysis.StandardType.GGResNonsingF4Three
import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberNoPair
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFourPermExcCoord
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelRows
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem card_ggAutomizer_of_aPermutationFull {G : Type} [Group G] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L : Subgroup G} (hn : n ≠ 0)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    Nat.card ↥(ggAutomizer L Bs) = n.factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨e, -⟩ := ggWeylOfType_A_of_map_eq_aPermutationFull hp2 eta hAut
  rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA m]

section Holds


theorem ggSecFiveBPermLabel_of_res {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBResLabel p lab) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs L := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hNoTr : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hmarkL := hL
  obtain ⟨-, lab, -, hraw⟩ := hmarkL
  obtain ⟨-, -, -, -, -, -, -, hres, -, -⟩ := largeEvenRawDatum_exists hraw
  have hp3 : p = 3 := hres.1
  subst hp3
  have hcardA : Nat.card ↥(ggAutomizer L Bs) = n.factorial :=
    card_ggAutomizer_of_aPermutationFull (by norm_num) (by omega) eta hAut
  have hsplit : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) ∨
        (lab.tag = .E6 ∧ lab.n = 1) ∨ (lab.tag = .F4 ∧ lab.n = 1) ∨
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label
      (S := fun p lab => GGSecFiveBCoordBResLabel p lab) ?_ hL
    intro lab h
    simpa [GGSecFiveBCoordBResLabel] using h
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have h := Subgroup.card_le_of_le hle
    rwa [GGConfig.card_bstar_inf_centralizer_L hcfg] at h
  have hnf : ∀ {c a : ℕ}, a.factorial < c → c < (a + 1).factorial →
      Nat.card ↥(ggAutomizer L Bs) ≠ c := fun h1 h2 hc =>
    factorial_succ_ne_of_between (k := n - 1) h1 h2
      (by rw [Nat.sub_add_cancel (by omega : 1 ≤ n), ← hcardA, hc])
  have hNP : GGNoReflFramePair 3 Bs L :=
    ggNoReflFramePair_of_aPermutationFull Nat.prime_three (by norm_num) eta hAut
  have hF : GGRowFrame (fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) :=
    fun p hp' hp2' lab hlab h =>
      ggNbrFrameInputOne_holds p hp' hp2' lab hlab (Or.inr (Or.inl h))
  rcases GGInnerDiagOnLabel.elim_or hsplit with hA | hRest1
  · have hA' : GGInnerDiagOnLabel
        (fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) 3 Bs L := by
      refine GGInnerDiagOnLabel.mono_label
        (S := fun _ lab => lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) ?_ hA
      intro lab h
      obtain ⟨ht, hr, hn1⟩ := h
      exact ⟨ht, by omega, by rw [hn1]; norm_num⟩
    exact (ggX_row_absurd_of_frame_of_noPair ggLabelRigidInput_holds hF hR (Or.inl rfl)
      hNP hA').elim
  rcases GGInnerDiagOnLabel.elim_or hRest1 with hE6 | hRest2
  · exact (hnf (c := 1152) (a := 6) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) (card_ggAutomizer_of_e6Two hcfg hNoTr hE6)).elim
  rcases GGInnerDiagOnLabel.elim_or hRest2 with hF4 | hRest3
  · have hF4' : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs L := by
      refine GGInnerDiagOnLabel.mono_label
        (S := fun _ lab => lab.tag = .F4 ∧ lab.n = 1) ?_ hF4
      intro lab h
      obtain ⟨ht, hn⟩ := h
      dsimp only [GGF4ThreeLabel]
      exact ⟨ht, rfl, by rw [hn]; norm_num⟩
    exact (hnf (c := 1152) (a := 6) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) (card_ggAutomizer_of_f4Three hcfg hNoTr hF4' hZ)).elim
  rcases GGInnerDiagOnLabel.elim_or hRest3 with hTwE6 | hTwA
  · have hTwE6' : GGInnerDiagOnLabel GGTwE6BadLabel 3 Bs L := by
      refine GGInnerDiagOnLabel.mono_label
        (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ?_ hTwE6
      intro lab h
      obtain ⟨ht, hd⟩ := h
      dsimp only [GGTwE6BadLabel]
      exact ⟨ht, rfl, hd⟩
    obtain ⟨e, -⟩ := ggTwE6Bad_weylOfType hR.1 hTwE6'
    exact (hnf (c := 51840) (a := 8) (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by rw [← Nat.card_congr e.toEquiv, card_coxeterE6_group])).elim
  · have hcardTwA : Nat.card ↥(ggAutomizer L Bs) = 720 :=
      card_ggAutomizer_of_twA5Three hcfg hTwA
    have h720 : (6 : ℕ).factorial = 720 := by norm_num [Nat.factorial]
    have hn6 : n = 6 :=
      (Nat.factorial_inj' (Or.inr (by norm_num : 1 < 6))).mp
        ((hcardA.symm.trans hcardTwA).trans h720.symm)
    subst hn6
    refine GGInnerDiagOnLabel.mono_label
      (S := fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) ?_ hTwA
    intro lab h
    exact Or.inr ⟨h.1, h.2.1, h.2.2⟩


theorem ggSecFiveBPermLabel_core {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs L := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hcardL : Nat.card ↥(ggAutomizer L Bs) = n.factorial :=
    card_ggAutomizer_of_aPermutationFull hp2 (by omega) eta hAut
  have hST : LargeEvenStandardType p B x L := hR.1.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hST.1
  obtain ⟨t, l, f⟩ := lab
  have hfinOf : ∀ {lab' : LargeEvenLabel}, LargeEvenInLambda2 lab' →
      GGHasLabel lab' (↥L ⧸ Subgroup.center ↥L) →
      ∀ {T : ℕ → LargeEvenLabel → Prop}, T p lab' → GGInnerDiagOnLabel T p Bs L := by
    intro lab' hl hh T hTl
    unfold GGInnerDiagOnLabel
    refine largeEvenMarking_mono ?_
      (ggInnerDiagOn_relabel ggLabelRigidInput_holds hR.1.2.2.1.1 hl hh)
    rintro lab'' R _ I F θ ⟨rfl, hQ⟩
    exact ⟨hTl, hQ⟩
  have hfin : ∀ {T : ℕ → LargeEvenLabel → Prop}, T p ⟨t, l, f⟩ → GGInnerDiagOnLabel T p Bs L :=
    hfinOf hlab hhas
  have hS : LargeEvenSplit p ⟨t, l, f⟩ := hP.1
  by_cases hcov : GGTBTorCov p ⟨t, l, f⟩
  · obtain ⟨r, m, N, C, M, hrow⟩ := hcov
    have hrowL : GGInnerDiagOnLabel
        (fun p lab' => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
          (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab' r m N C M ∧
            GGTBTorRowAt p ⟨t, l, f⟩ r m N C M) p Bs L :=
      hfin ⟨r, m, N, C, M, hrow, hrow⟩
    obtain ⟨r', m', N', C', M', hrow', hcardM⟩ :=
      GGConfig.exists_row_card_automizer_L (ggTBTorAll_of_remaining trivial)
        ggTBTorLiftRows_holds hR.1.1 hrowL
    rcases ggTBTorRowAt_perm_of_card hlab hrow' hn (hcardM ▸ hcardL) with
      hperm | ⟨rfl, hrank3, ⟨htD, hdvd⟩ | ⟨httwD, hdvd⟩⟩
    · exact hfin hperm
    · obtain rfl : t = .D := htD
      obtain rfl : l = 3 := hrank3
      exact hfinOf ((Q1DSmall.inLambda2_D3_iff_A3 f).mp hlab)
        (largeEvenRawDatum_of_ggLabelIso (Q1DSmall.labelIso_D3_A3 f) hhas)
        (Or.inl ⟨rfl, rfl, hdvd⟩)
    · obtain rfl : t = .twD := httwD
      obtain rfl : l = 3 := hrank3
      exact hfinOf ((Q1DSmall.inLambda2_twD3_iff_twA3 f).mp hlab)
        (largeEvenRawDatum_of_ggLabelIso (Q1DSmall.labelIso_twD3_twA3 f) hhas)
        (Or.inr ⟨rfl, rfl, hdvd⟩)
  · rcases ggSplit_not_tbTorCov_cases hp hp2 hlab hS hcov with hres | hsm | hsp
    · exact ggSecFiveBPermLabel_of_res hR hn eta hAut (hfin hres)
    · exact (ggL_absurd_of_small_split hR (hfin ⟨hsm, hS⟩)).elim
    · exact (ggX_row_absurd_of_pRank ggRowPRankLeTwo_smallPlus hR (Or.inl rfl) (hfin hsp)).elim

theorem ggSecFiveBPermLabelInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ∀ (n : ℕ), 4 ≤ n → ∀ eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
          (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
            GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermLabel n p lab) p Bs L := by
  intro G _ _ p B Bs x L D J 𝒦 hR n hn eta hAut
  exact ggSecFiveBPermLabel_core hR hn eta hAut

end Holds

end CFSG.StandardType

end
