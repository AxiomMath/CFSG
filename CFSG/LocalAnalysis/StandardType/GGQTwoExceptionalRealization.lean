module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavMarking
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcData

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.RecipeExcLang

@[expose] def exceptionalImage {G : Type} [Group G] {Bs L : Subgroup G}
    {τ : Tag} {K : Type} [Field K]
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup τ K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : Subgroup (adjointGroup τ K) :=
  (ggBeta L θ hN).range.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))

theorem exceptionalImage_facts {G : Type} [Group G] {Bs L : Subgroup G} {p : ℕ}
    (hBs : IsElemAbelian p Bs) (hL : commutator L = ⊤) {τ : Tag} {K : Type} [Field K] [Finite K]
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup τ K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : (ggBeta L θ hN).range ≤
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    IsElemAbelian p (exceptionalImage θ hN) ∧
      Nat.card (exceptionalImage θ hN) =
        ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index := by
  let E := (ggBeta L θ hN).range
  let c : adjointGroup τ K →* MulAut (adjointGroup τ K) := MulAut.conj
  have hc : Function.Injective c :=
    mulAut_conj_injective (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
      (τ := τ) (K := K))
  have hE : IsElemAbelian p E :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.property)) (ggBeta L θ hN)
  have hmap : (E.comap c).map c = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hI
  have hel : IsElemAbelian p (E.comap c) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hc ?_)⟩⟩, fun a ha => hc ?_⟩
    · change c ((a : adjointGroup τ K) * b) = c ((b : adjointGroup τ K) * a)
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE a.property b.property
    · rw [map_pow, hE.2 _ ha, map_one]
  refine ⟨hel, ?_⟩
  calc Nat.card (E.comap c) = Nat.card ((E.comap c).map c) :=
      (Subgroup.card_map_of_injective hc).symm
    _ = Nat.card E := by rw [hmap]
    _ = _ := beta_card hL θ hN

theorem exceptional_full_lang {G : Type} [Group G] {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hL : commutator L = ⊤)
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup τ K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : (ggBeta L θ hN).range ≤
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ τ.rank) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (D : LangDatum τ (AlgebraicClosure K)) (w : WeylGroup τ),
      (∀ c, Fr c = c ^ 2) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧ D.q = 2 ∧
      D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
      (∀ u : Fin τ.rank → ℤ, w • u = -u) ∧
      ∀ y : ModGL τ (AlgebraicClosure K), (y ∈ D.torus ∧ y ^ 3 = 1) ↔
        ∃ x ∈ exceptionalImage θ hN,
          D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 = y := by
  obtain ⟨hel, hcard⟩ := exceptionalImage_facts hBs hL θ hN hI
  have horder : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have hdeg : ExcMaxToral.excDegCount τ (orderOf (Nat.card K : ZMod 3)) = τ.rank := by
    rw [hK, horder]
    rcases hτ with rfl | rfl | rfl <;> decide
  have h4 : 4 ≤ ExcMaxToral.excDegCount τ (orderOf (Nat.card K : ZMod 3)) := by
    rw [hdeg]
    rcases hτ with rfl | rfl | rfl <;> decide
  have hcard' : 3 ^ ExcMaxToral.excDegCount τ (orderOf (Nat.card K : ZMod 3)) ≤
      Nat.card (exceptionalImage θ hN) := by
    rw [hcard, hidx, hdeg]
  obtain ⟨Fr, hFr, D, hΦ, hq, ⟨w, hw, hshape⟩, _, htor⟩ :=
    ExcMaxToral.adjointMaxElemToral_of_not_five_four τ K 3 (by norm_num)
      inferInstance inferInstance Nat.prime_three (by norm_num) h4
      (exceptionalImage θ hN) hel hcard'
  refine ⟨Fr, D, w, ?_, hΦ, hq.trans hK, hw, ?_, htor⟩
  · intro c
    rw [hFr c, hK]
  · apply hshape.2.1
    rw [hK, horder]

theorem frobRootMap_congr_fields {τ : Tag} {L : Type} [Field L] {D₁ D₂ : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hΦ : D₁.Φ = D₂.Φ) (hq : D₁.q = D₂.q) (hn : D₁.n = D₂.n)
    (h : FrobRootMap D₂ ρ) : FrobRootMap D₁ ρ := by
  have hstep : D₁.step = D₂.step := by
    simp only [LangDatum.step, hΦ, hn]
  have htor : D₁.torus = D₂.torus := by
    simp only [LangDatum.torus, hΦ, hn]
  refine ⟨h.isRoot_iff, h.neg_eq, h.iform_eq, ?_, ?_⟩
  · intro γ hγ
    rw [hstep]
    exact h.map_rootSubgroup γ hγ
  · intro a ha γ hγ
    rw [htor] at ha
    rw [hq]
    exact h.rootChar_eq a ha γ hγ

theorem excUntw_raw_of_label_with_rank {lab : LargeEvenLabel}
    (htag : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) {Q : CFSG.Assembly.LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K),
      (τ = .F4 ∨ τ = .E7 ∨ τ = .E8) ∧ τ.rank = GGQ2LieRank lab ∧ Nat.card K = 2 ^ lab.n ∧
      Q (LargeEvenCenterQuot (adjointGroup τ K))
        (markIDImage (IsRoot τ) K (adjointGroup τ K))
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with ht | ht | ht <;> subst ht
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.F4, K, instF, instFin, Or.inl rfl, by rfl, hK,
      CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport hQ⟩
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.E7, K, instF, instFin, Or.inr (Or.inl rfl), by rfl, hK,
      CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport hQ⟩
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.E8, K, instF, instFin, Or.inr (Or.inr rfl), by rfl, hK,
      CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport hQ⟩

theorem actual_beta_image_of_marking {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab)
    (htag : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {e : ℕ} (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ e) :
    ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K)
      (θ : L ⧸ Subgroup.center L ≃* adjointGroup τ K),
      (τ = .F4 ∨ τ = .E7 ∨ τ = .E8) ∧ τ.rank = GGQ2LieRank lab ∧ Nat.card K = 2 ∧
      (ggBeta L θ hN).range ≤
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ∧
      IsElemAbelian 3 (ggBeta L θ hN).range ∧
      Nat.card (ggBeta L θ hN).range = 3 ^ e := by
  classical
  have hBs : IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hSS : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hL : commutator L = ⊤ := hSS.2.2.2.1.2.2.1
  unfold GGInnerDiagOnLabel at hmark
  obtain ⟨-, labM, hlab2M, hrawM⟩ := hmark
  let Qmark : CFSG.Assembly.LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* R,
        (labM = lab) ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = (b : G)⁻¹ * l * (b : G)) φ
  obtain ⟨R, _, I, F, hQraw⟩ := CFSG.StandardType.largeEvenRawDatum_exists hrawM
  obtain ⟨-, -, θR, hlabEq, hNR, -⟩ := hQraw
  have htagM : labM.tag = .F4 ∨ labM.tag = .E7 ∨ labM.tag = .E8 := by rw [hlabEq]; exact htag
  have hltM : labM.n < 2 := by rw [hlabEq]; exact hq2
  have hnM : 1 ≤ labM.n := hlab2M.1
  have hn1 : labM.n = 1 := by omega
  have hrawCanon : CFSG.Assembly.LargeEvenRawDatum labM Qmark := by
    obtain ⟨t, l, n⟩ := labM
    rcases htagM with ht | ht | ht <;> subst ht
    all_goals
      dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy,
        CFSG.Assembly.LargeEvenRawDatum] at hrawM ⊢
      exact hrawM
  obtain ⟨τ, K, instF, instFin, hτ, hτrank, hKpow, hQ0⟩ :=
    excUntw_raw_of_label_with_rank (lab := labM) htagM hrawCanon
  obtain ⟨-, -, θ, -, hN', hact⟩ := hQ0
  have hNs : hN' = hN := Subsingleton.elim _ _
  have hK2 : Nat.card K = 2 := by rw [hKpow, hn1]; norm_num
  have hβI : (ggBeta L θ hN).range ≤
      markIDImage (IsRoot τ) K (adjointGroup τ K) := by
    rw [← hNs]
    rintro _ ⟨b, rfl⟩
    simpa only [ggBeta_eq] using
      CFSG.StandardType.ggLAut_mem_of_induces (L := L) (θ := θ) (B := Bs) hN' hact b.2
  haveI : Subsingleton Kˣ :=
    CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK2
  have hID : markIDImage (IsRoot τ) K (adjointGroup τ K) ⊆
      (MulAut.conj : LargeEvenCenterQuot (adjointGroup τ K) →*
        MulAut (LargeEvenCenterQuot (adjointGroup τ K))).range :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport
      (Q := fun (R : Type) [Group R] (I _ : Set (MulAut R)) =>
        I ⊆ (MulAut.conj : R →* MulAut R).range)
      (chevIDImage_subset_inn_of_subsingleton (A := τ.cartan) (K := K)
        (LargeEvenChevH τ.cartan K false))
  let eR := centerQuotEquivOfBot (center_adjointGroup_eq_bot (τ := τ) (K := K))
  let θadj : L ⧸ Subgroup.center L ≃* adjointGroup τ K := θ.trans eR
  have hI : (ggBeta L θadj hN).range ≤
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
    rintro _ ⟨b, rfl⟩
    have hb : ggBeta L θ hN b ∈
        (MulAut.conj : LargeEvenCenterQuot (adjointGroup τ K) →*
          MulAut (LargeEvenCenterQuot (adjointGroup τ K))).range := by
      exact hID (hβI ⟨b, rfl⟩)
    obtain ⟨x, hx⟩ := hb
    refine ⟨eR x, ?_⟩
    have hbconj : (MulAut.congr eR) (ggBeta L θ hN b) = ggBeta L θadj hN b := by
      simpa [θadj] using
        DFunLike.congr_fun (beta_trans θ eR hN) b
    rw [← hbconj, ← hx]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eR x).symm
  have hBs3 : IsElemAbelian 3 Bs := by simpa [hp3] using hBs
  have hidx3 : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ e := by
    rw [hidx, hp3]
  have hβ := QTwoCav.beta_image_of_index hBs3 hL θadj hN hidx3
  refine ⟨τ, K, instF, instFin, θadj, ?_, ?_, ?_, hI, hβ.1, hβ.2⟩
  · exact hτ
  · simpa [hlabEq] using hτrank
  · exact hK2

end CFSG.StandardType.QTwoCav

end
