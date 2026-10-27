module

public import CFSG.LocalAnalysis.StandardType.GGTBJLinearCorank
public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyInputs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem fix_mem_centralizer_J_of_block
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {φ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hφs : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F, TypeANbrDvd.ActsDiag φ a t)
    (S : Finset (Fin (r + 1))) (hS2 : 2 ≤ S.card)
    (hJ : J = (blockSpecialLinear S).map (X.subtype.comp φ)) :
    ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  let e : S ≃ Fin S.card := S.equivFin
  let χ : SpecialLinearGroup (Fin S.card) F →* J :=
    TypeANbrDvd.blockSLCover (F := F) S X φ hJ e
  have hχs : Function.Surjective χ :=
    TypeANbrDvd.blockSLCover_surjective (F := F) S X φ hJ e
  have hχker : ∀ g, χ g = 1 → g ∈ scalars S.card F :=
    TypeANbrDvd.blockSLCover_ker_scalar (F := F) S X φ hJ hker e
  have hχdiag : ∀ a ∈ (ggGamma J hBsJ).range,
      ∃ t : Fin S.card → F, TypeANbrDvd.ActsDiag χ a t := by
    rintro a ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hdiag _ ⟨b, rfl⟩
    exact ⟨fun k => t (e.symm k),
      TypeANbrDvd.blockSLCover_actsDiag (F := F) (S := S) (P := X) (φ := φ)
        hJ hN hBsJ (B := Bs) le_rfl e ht⟩
  exact ResJCubicBlock.ggLinearModel_fix_mem_centralizer hBsJ hBs hSC hχs hχker hS2 hχdiag

theorem exists_block_of_large_linear_K_of_marking_with_card
    (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* K) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        p ^ (r - 1) ≤ Nat.card ↥(ggGamma K hN).range ∧
        2 ≤ S.card ∧ J = (blockSpecialLinear S).map (K.subtype.comp φ) := by
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag, hcard⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking_with_card hH.1 (Or.inr ⟨y, hnb⟩)
      hr hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hdiag' : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  have hcomp' : IsComponentOf J (K ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    hφs hker hdiag' (Subgroup.zpowers_le.mpr hx) hcomp'
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hcard, hS, hJ⟩

theorem inf_centralizer_le_zpowers_of_sHat {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {y : G} {K : Subgroup G} (hS : LargeEvenSHat p B y K) :
    B ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
  intro b hb
  refine (hS.2.2.2.2.2 b).mp ⟨hb.1, ?_, ?_⟩
  · exact Subgroup.centralizer_le_normalizer (K : Set G) hb.2
  · have hbot : ⁅K, Subgroup.zpowers b⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hb.2
    rw [hbot]
    exact bot_le

theorem ggTBJNbr_splitA_of_marking
    (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hcardA, hS2, hJ⟩ :=
    exists_block_of_large_linear_K_of_marking_with_card hI3 hH hr hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hk) y rfl).symm
  have hBsCard : p ^ r ≤ Nat.card Bs := by
    have h1 := card_range_ggGamma_mul_prime_le hp hBs hN hyBs hy1 hyC
    calc p ^ r = p ^ (r - 1) * p := by rw [← pow_succ]; congr 1; omega
      _ ≤ Nat.card ↥(ggGamma K hN).range * p := Nat.mul_le_mul_right _ hcardA
      _ ≤ Nat.card Bs := h1
  have hfix := fix_mem_centralizer_J_of_block hBs hSC hH.Bs_le_normalizer_J hN hφs hker hdiag S
    hS2 hJ
  have hcor : r + 1 - S.card ≤ 3 :=
    ggLinear_corank_le_three_of_block hp2 hpF hr hBs hSC hN hφs hker hdiag hBsCard
      hH.1.card_bstar_inf_centralizer_J_le hfix S hS2 hJ
  have hSle : S.card ≤ r := by
    by_contra hSgt
    have hSr : S.card = r + 1 := by
      have := Finset.card_le_univ S
      simp only [Fintype.card_fin] at this
      omega
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hSr)
    have hJK : J = K := by
      rw [hJ, hSuniv]
      have htop : (blockSpecialLinear (K := F) (Finset.univ : Finset (Fin (r + 1))) :
          Subgroup (SpecialLinearGroup (Fin (r + 1)) F)) = ⊤ := by
        refine eq_top_iff.mpr fun g _ => ?_
        rw [mem_blockSpecialLinear]
        intro i j hij
        rcases hij with h | h <;> simp at h
      rw [htop, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
        MonoidHom.range_eq_top_of_surjective _ hφs, Subgroup.map_top, Subgroup.range_subtype]
    have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
    have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
    rw [hJK] at hD
    have hle : D ≤ Subgroup.zpowers y := by
      rw [hD]
      exact inf_centralizer_le_zpowers_of_sHat hnb.1
    have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 y hyBs) hy1] at h1
    have : 1 < p := hp.one_lt
    nlinarith
  have hc1 : 1 ≤ r + 1 - S.card := by omega
  have hres := ggResSideDatumLE3_of_diagonal_linear_block (c := r + 1 - S.card) hp2 hpF hr hc1
    hcor (by omega) hBs hSC hN hφs hker hdiag S (by omega) hJ
  by_cases hc : r + 1 - S.card = 1
  · exact Or.inl (hres.1 hc)
  · exact Or.inr (hres.2 (by omega))

private theorem ggSplitA_relabel {M : Type} [Group M] {lab : LargeEvenLabel}
    (hAD : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3))
    (hΛ : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab M) :
    LargeEvenInLambda2 (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) M := by
  rcases hAD with htag | ⟨htag, hr3⟩
  · have hlab : lab = ⟨.A, lab.rank, lab.n⟩ := by
      rcases lab with ⟨t, r, n⟩
      simp only at htag
      subst htag
      rfl
    rw [← hlab]
    exact ⟨hΛ, hhas⟩
  · have hlab : lab = ⟨.D, 3, lab.n⟩ := by
      rcases lab with ⟨t, r, n⟩
      simp only at htag hr3
      subst htag
      subst hr3
      rfl
    have hΛ3 : LargeEvenInLambda2 (⟨.D, 3, lab.n⟩ : LargeEvenLabel) := by
      rw [← hlab]
      exact hΛ
    have hhas3 : GGHasLabel (⟨.D, 3, lab.n⟩ : LargeEvenLabel) M := by
      rw [← hlab]
      exact hhas
    rw [hr3]
    exact ⟨⟨hΛ3.1, by norm_num, fun h => absurd h (by norm_num)⟩, ggHasLabel_D3_iff_A3.mp hhas3⟩

theorem ggTBJLeftOn_splitA
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJSplitALabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hAD, hr, hpq⟩ := hP.1
  obtain ⟨hΛ', hhas'⟩ : LargeEvenInLambda2 (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) :=
    ggSplitA_relabel hAD hΛ hhas
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = ⟨.A, lab.rank, lab.n⟩) p Bs L :=
    ggInnerDiagOn_relabel hRig hH.2.2.1.1 hΛ' hhas'
  rcases ggTBJLeft_splitA_of_marking hH hr hpq hmark with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_splitA
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJSplitALabel := by
  intro G _ _ p B Bs x L D J y K hH hp hK _hX
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨hAD, hr, hpq⟩ := hP.1
  obtain ⟨hΛ', hhas'⟩ : LargeEvenInLambda2 (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) ∧
      GGHasLabel (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) :=
    ggSplitA_relabel hAD hΛ hhas
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = ⟨.A, lab.rank, lab.n⟩) p Bs K :=
    ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ' hhas'
  rcases ggTBJNbr_splitA_of_marking hI3 hH hr hpq hmark with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJOrderRest_of_restSplitA
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (h : GGTBJOrderRestSplitAInput) : GGTBJOrderRestInput := by
  have hL := h.1.or (ggTBJLeftOn_splitA hRig)
  have hK := h.2.or (ggTBJNbrOn_splitA hRig hI3)
  refine ⟨hL.mono ?_, hK.mono ?_⟩ <;>
  · intro p lab hP
    by_cases hs : ggTBJSplitALabel p lab
    · exact Or.inr hs
    · exact Or.inl ⟨hP.1.1.1, fun hE => hE.elim hP.1.1.2
        (fun hE' => hE'.elim hP.1.2 (fun hE'' => hE''.elim hP.2 hs))⟩

end CFSG.StandardType

end
