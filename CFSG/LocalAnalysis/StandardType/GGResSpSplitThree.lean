module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.StandardType.GGTBJSpRankThree
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGResTwoCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem spSplitThree_labelAll {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel}
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (_ : R ≃* LargeEvenProj (LargeEvenSpGroup F 3)),
        Nat.card F = 2 ^ n ∧ GGTorusLift p 3 R ∧ p ∣ Nat.card F - 1 ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨htag, hrank, hpn⟩ := h
  change rank = 3 at hrank
  subst rank
  intro Q hQ
  have key : ∀ (hQ' : LargeEvenRecipeSymplectic 3 (2 ^ n) false Q),
      LargeEvenRecipeSymplectic 3 (2 ^ n) false fun R _ I Fraw => Q R I Fraw ∧
        (∃ (n' : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
          (_ : R ≃* LargeEvenProj (LargeEvenSpGroup F 3)),
          Nat.card F = 2 ^ n' ∧ GGTorusLift p 3 R ∧ p ∣ Nat.card F - 1 ∧
            I ⊆ Set.range (MulAut.conj : R →* MulAut R)) := by
    intro hQ'
    obtain ⟨F, _, _, hF, hQF⟩ := hQ'
    have hch : CharP F 2 := charP_two_of_card hF
    have hpq : p ∣ Nat.card F - 1 := by
      rw [hF]
      exact hpn
    exact ⟨F, inferInstance, inferInstance, hF, hQF, n, F,
      inferInstance, inferInstance, hch, MulEquiv.refl _, hF,
      TableBSymp.ggTorusLift_symplectic hp hp2 hpq (by norm_num), hpq,
      TableBSymp.sp_I_subset_inn⟩
  rcases htag with h | h <;> dsimp only at h <;> subst h <;> exact key hQ

theorem GGResHyp.spSplit_three_model
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup F 3)),
      2 ≤ n ∧ Nat.card F = 2 ^ n ∧ p ∣ Nat.card F - 1 ∧ Subgroup.center ↥L = ⊥ ∧
      GGTorusTBGroup p 3 (LargeEvenProj (LargeEvenSpGroup F 3))
        (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup F 3) →*
          MulAut (LargeEvenProj (LargeEvenSpGroup F 3)))) ↥L ψ (ggGamma L hN).range := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hLc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)
    (fun lab _ hs => nbrC_labelAll_guard (spSplitThree_labelAll hp hp2 hs))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, Fraw, -, -, θ, ⟨-, hN, h3I⟩, n, F, _, _, _, e, hF, hlift,
    hpq, hIinn⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN h3I hb
  have hTB := ggTorusTBGroup_of_L hcfg hLc θ hN hBsI hlift
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup F 3) →*
      MulAut (LargeEvenProj (LargeEvenSpGroup F 3)))) e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hIinn hφ
      exact ⟨e g, by
        ext z
        simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have hn1 : 1 ≤ n := by
    have hcard : 2 ≤ Nat.card F := by
      haveI : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    by_contra h
    have hn : n = 0 := by omega
    rw [hF, hn, pow_zero] at hcard
    omega
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn : n = 1 := by omega
    have hpd : p ∣ 1 := by simpa [hF, hn] using hpq
    exact hp.ne_one (Nat.dvd_one.mp hpd)
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_quot_psp_even hLc hF hn1 (by norm_num) (fun _ => hn2) (θ.trans e)
  exact ⟨n, F, inferInstance, inferInstance, inferInstance, hN,
    e.toMonoidHom.comp (ggQuotHom θ), hn2, hF, hpq, hZ, hTB'⟩

theorem GGResHyp.bstar_eq_of_spSplit_three_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    B = Bs := by
  obtain ⟨_, _, _, _, _, hN, ψ, _, _, hpq, _, hTB⟩ := hH.spSplit_three_model hL
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  exact (ggTBJ_sp_bstar_eq hp hp2 hcfg L hN hpq ψ hTB).symm

theorem GGResHyp.false_of_exact2_L_spSplit_three
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  obtain ⟨n, F, _, _, _, hN, ψ, hn, hF, hpq, hZ, hTB⟩ := hH.spSplit_three_model hL
  exact not_ggResSideDatum_of_ggResLeviDatumExact2
    (ggTBJ_sp3_l_of_model hH hN hpq ψ hTB) hD

theorem ggResMultiNodeRestTwoCellInput_spSplit_three :
    GGResMultiNodeRestTwoCellInput (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hL hD
  exact hH.false_of_exact2_L_spSplit_three hL hD

end CFSG.StandardType
