module

public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Realization
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalComponent
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartWeyl
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public noncomputable section

namespace CFSG.StandardType.QTwoE6

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.NoOffTwE6Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.LieType.Steinberg.Adjoint


variable {K : Type} [Field K] [Finite K]
  (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
  (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)

theorem exists_diagonal_of_mem_langCube {g : ModGL Tag.E6 (AlgebraicClosure K)}
    {a : MulAut ↥(twistedE6RootGroup K σ)}
    (ha : a ∈ TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g) :
    ∃ (b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (w : ↥(RecipeExcLang.twInndiagGroup K σ)),
      (∀ j, b j ^ 3 = 1) ∧
      a = RecipeExcLang.twConj K σ w ∧
      g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (w : ModGL TwistTag.E6.tag K) * g = rootDiagUnit Tag.E6 b := by
  obtain ⟨b, hb, hx, hy⟩ := (TwE6DD2.mem_langCube (n := 1) le_rfl hK σ hσ Fr hFr).mp ha
  let e := twInndiagEquivRgrp (n := 1) le_rfl hK σ hσ Fr hFr
  let w : ↥(RecipeExcLang.twInndiagGroup K σ) := e.symm ⟨_, hx⟩
  have hw : e w = ⟨g * rootDiagUnit Tag.E6 b * g⁻¹, hx⟩ := e.apply_symm_apply _
  have hbase : baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (w : ModGL TwistTag.E6.tag K) = g * rootDiagUnit Tag.E6 b * g⁻¹ := by
    exact (twInndiagEquivRgrp_apply (n := 1) le_rfl hK σ hσ Fr hFr w).symm.trans
      (congrArg Subtype.val hw)
  refine ⟨b, w, hb, ?_, ?_⟩
  · rw [← rgrpConjAut_apply_baseChange (n := 1) le_rfl hK σ hσ Fr hFr w, hw]
    exact hy.symm
  · rw [hbase]
    group

theorem fullThreeTorus_eq_cubeTorus
    (T : LangSetup Tag.E6 (AlgebraicClosure K) 5) (hq : T.D.q = 2)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → T.ρ γ = -γ) :
    QTwoCav.fullThreeTorus T =
      (cubeRootTuples (AlgebraicClosure K)).map
        (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      ((inf_le_left : T.D.torus ≤ torusGroup Tag.E6 (AlgebraicClosure K)) ht.1)
    have hb3 : b ^ 3 = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6)
      rw [← rootDiagUnit_pow, ← hb, ht.2, rootDiagUnit_one]
    exact ⟨b, mem_cubeRootTuples.mpr (fun j => congrFun hb3 j), hb.symm⟩
  · rintro t ⟨b, hb, rfl⟩
    have hb3 : b ^ 3 = 1 := funext fun j => mem_cubeRootTuples.mp hb j
    have hT : rootDiagUnit Tag.E6 b ∈ T.D.torus := by
      apply LangRat.rootDiagUnit_mem_torus_of_rootChar T (Or.inr (Or.inl rfl))
      intro γ hγ
      have hc3 : rootChar b γ ^ 3 = 1 := by
        rw [← CFSG.RankThree.Chevalley.rootChar_pow_tuple, hb3]
        simp [rootChar]
      rw [hρ γ hγ, hq]
      rw [show -γ = 0 - γ by simp, rootChar_sub, rootChar_zero, one_mul]
      calc (rootChar b γ)⁻¹ = (rootChar b γ)⁻¹ * rootChar b γ ^ 3 := by rw [hc3, mul_one]
        _ = rootChar b γ ^ 2 := by group
    refine ⟨hT, ?_⟩
    change rootDiagUnit Tag.E6 b ^ 3 = 1
    rw [rootDiagUnit_pow, hb3, rootDiagUnit_one]

theorem map_langCube_preimage_eq_fullThreeTorus
    (T : LangSetup Tag.E6 (AlgebraicClosure K) 5) (hq : T.D.q = 2)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → T.ρ γ = -γ)
    {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
      TwistedDiag.n0 (AlgebraicClosure K)) :
    ((TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g).comap
      (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr)).map
        ((MulAut.conj g⁻¹).toMonoidHom.comp (TwistedDiag.Rgrp (AlgebraicClosure K) Fr).subtype) =
      QTwoCav.fullThreeTorus T := by
  let C := (cubeRootTuples (AlgebraicClosure K)).map
    (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))
  have hC : C.map (MulAut.conj g).toMonoidHom ≤ TwistedDiag.Rgrp (AlgebraicClosure K) Fr :=
    TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr (by norm_num) hg hgn
  rw [TwE6DD2.langCube, Subgroup.comap_map_eq_self_of_injective
    (rgrpConjAut_injective (n := 1) le_rfl hK σ hσ Fr hFr)]
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hC, Subgroup.map_map]
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (ModGL Tag.E6 (AlgebraicClosure K)) := by
    apply MonoidHom.ext
    intro z
    change g⁻¹ * (g * z * g⁻¹) * g = z
    group
  rw [hc, Subgroup.map_id]
  exact (fullThreeTorus_eq_cubeTorus T hq hρ).symm

theorem card_automizer_twisted_frame_eq
    {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hι : ∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (c : ModGL TwistTag.E6.tag K) * g)
    (H : Subgroup ↥(twistedE6RootGroup K σ))
    (A : Subgroup (MulAut ↥(twistedE6RootGroup K σ)))
    (hA : A ≤ (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr).range) :
    Nat.card (ggAutomizer (H.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _)) A) =
      Nat.card (ggAutomizer (H.map ι) ((A.comap
        (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr)).map
          ((MulAut.conj g⁻¹).toMonoidHom.comp
            (TwistedDiag.Rgrp (AlgebraicClosure K) Fr).subtype))) := by
  let Φ := rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr
  let j : ↥(twistedE6RootGroup K σ) →* ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr) :=
    (twInndiagEquivRgrp (n := 1) le_rfl hK σ hσ Fr hFr).toMonoidHom.comp
      (Subgroup.inclusion (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ))
  let ψ := (MulAut.conj g⁻¹).toMonoidHom.comp
    (TwistedDiag.Rgrp (AlgebraicClosure K) Fr).subtype
  have hΦ : Function.Injective Φ := rgrpConjAut_injective (n := 1) le_rfl hK σ hσ Fr hFr
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp Subtype.val_injective
  have hjΦ : Φ.comp j = (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _) := by
    apply MonoidHom.ext
    intro c
    exact (rgrpConjAut_apply_baseChange (n := 1) le_rfl hK σ hσ Fr hFr
      ⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.property⟩).trans
        (RecipeExcLang.twConj_of_mem_C0 σ c)
  have hjψ : ψ.comp j = ι := by
    apply MonoidHom.ext
    intro c
    change g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (c : ModGL TwistTag.E6.tag K) * g = ι c
    exact (hι c).symm
  have hmapA : (A.comap Φ).map Φ = A := Subgroup.map_comap_eq_self hA
  have hmapH : (H.map j).map Φ = H.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _) := by
    rw [Subgroup.map_map, hjΦ]
  have hmapHψ : (H.map j).map ψ = H.map ι := by rw [Subgroup.map_map, hjψ]
  have hcardΦ : Nat.card (ggAutomizer
      (H.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _)) A) =
      Nat.card (ggAutomizer (H.map j) (A.comap Φ)) := by
    rw [← hmapH, F4AutWeyl.ggAutomizer_map_eq hΦ _ _ hmapA,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  have hcardψ : Nat.card (ggAutomizer ((H.map j).map ψ) ((A.comap Φ).map ψ)) =
      Nat.card (ggAutomizer (H.map j) (A.comap Φ)) := by
    rw [F4AutWeyl.ggAutomizer_map_eq hψ _ _ rfl,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rw [hmapHψ] at hcardψ
  exact hcardΦ.trans hcardψ.symm

theorem map_inner_preimage_eq_range
    {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hι : ∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (c : ModGL TwistTag.E6.tag K) * g) :
    (((MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range).comap
      (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr)).map
        ((MulAut.conj g⁻¹).toMonoidHom.comp
          (TwistedDiag.Rgrp (AlgebraicClosure K) Fr).subtype) = ι.range := by
  let Φ := rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr
  let j : ↥(twistedE6RootGroup K σ) →* ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr) :=
    (twInndiagEquivRgrp (n := 1) le_rfl hK σ hσ Fr hFr).toMonoidHom.comp
      (Subgroup.inclusion (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ))
  let ψ := (MulAut.conj g⁻¹).toMonoidHom.comp
    (TwistedDiag.Rgrp (AlgebraicClosure K) Fr).subtype
  have hjΦ : Φ.comp j = (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _) := by
    apply MonoidHom.ext
    intro c
    exact (rgrpConjAut_apply_baseChange (n := 1) le_rfl hK σ hσ Fr hFr
      ⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.property⟩).trans
        (RecipeExcLang.twConj_of_mem_C0 σ c)
  have hjψ : ψ.comp j = ι := by
    apply MonoidHom.ext
    intro c
    change g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (c : ModGL TwistTag.E6.tag K) * g = ι c
    exact (hι c).symm
  have hinner : (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range =
      j.range.map Φ := by rw [← MonoidHom.range_comp, hjΦ]
  change (((MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range).comap Φ).map ψ = _
  rw [hinner, Subgroup.comap_map_eq_self_of_injective
    (rgrpConjAut_injective (n := 1) le_rfl hK σ hσ Fr hFr), ← MonoidHom.range_comp, hjψ]

theorem map_langCube_inner_preimage_eq
    (T : LangSetup Tag.E6 (AlgebraicClosure K) 5) (hq : T.D.q = 2)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → T.ρ γ = -γ)
    {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
      TwistedDiag.n0 (AlgebraicClosure K))
    (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hι : ∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (c : ModGL TwistTag.E6.tag K) * g) (hrange : ι.range = T.Γ) :
    ((TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g ⊓
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range).comap
        (rgrpConjAut (n := 1) le_rfl hK σ hσ Fr hFr)).map
          ((MulAut.conj g⁻¹).toMonoidHom.comp
            (TwistedDiag.Rgrp (AlgebraicClosure K) Fr).subtype) =
      QTwoCav.fullThreeTorus T ⊓ T.Γ := by
  rw [Subgroup.comap_inf, Subgroup.map_inf _ _ _
    ((MulAut.conj g⁻¹).injective.comp Subtype.val_injective),
    map_langCube_preimage_eq_fullThreeTorus hK σ hσ Fr hFr T hq hρ hg hgn,
    map_inner_preimage_eq_range hK σ hσ Fr hFr ι hι, hrange]

variable {G : Type} [Group G] [Finite G] {p : ℕ}
  {B Bs L D J : Subgroup G} {x : G}

theorem exists_original_rational_component
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    {r : ℕ} (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ r)
    (hr : 5 ≤ r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (hK : Nat.card K = (2 ^ 1) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
      (θ : L ⧸ Subgroup.center L ≃* ↥(twistedE6RootGroup K σ))
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (g : ModGL Tag.E6 (AlgebraicClosure K))
      (T : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
      (b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (i : KernelComponent (rootCharHom b)),
      Function.Injective ι ∧ ι.range = T.Γ ∧ T.D.q = 2 ∧ T.IsAlgebraic ∧
      (∀ γ, IsRoot Tag.E6 γ → T.ρ γ = -γ) ∧
      (∀ j, b j ^ 3 = 1) ∧ rootDiagUnit Tag.E6 b ≠ 1 ∧
      rootDiagUnit Tag.E6 b ∈ T.D.torus ∧
      CFSG.IsQuasisimple (rationalComponent T.ρ T.Γ (rootCharHom b) i) ∧
      ((J.subgroupOf L).map (ggQuotHom θ)).map ι =
        rationalComponent T.ρ T.Γ (rootCharHom b) i ∧
      (∀ c : ↥(twistedE6RootGroup K σ), ι c = g⁻¹ *
        baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g) ∧
      g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧
      g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
        TwistedDiag.n0 (AlgebraicClosure K) ∧
      (ggBeta L θ hN).range ≤ TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g ∧
      Nat.card (ggBeta L θ hN).range = 3 ^ r := by
  obtain ⟨K, instF, instFin, σ, hK1, hσ1, θ₀, hN, S, Fr, hFr, g, hK4, hσ2,
    hSdef, hSEA, hScard, hg, hgn, hSlang, _⟩ :=
    actual_beta_langCube_of_marking hS hp3 hq2 htag hmark hidx hr
  letI : Field K := instF
  letI : Finite K := instFin
  let e := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let θ := θ₀.trans e
  have hbeta : (ggBeta L θ₀ hN).range.map (MulAut.congr e).toMonoidHom =
      (ggBeta L θ hN).range := by
    rw [← MonoidHom.range_comp, QTwoCav.beta_trans θ₀ e hN]
  have hSθ : S = (ggBeta L θ hN).range := hSdef.trans hbeta
  obtain ⟨d, hd1, _, hfixD⟩ := QTwoCav.exists_beta_d_generator θ
    (by rw [hp3]; exact Nat.prime_three) hS hN
  let hDL := QTwoCav.d_le_normalizer hS hN
  let a := ggBeta L θ hDL d
  have haS : a ∈ S := by
    rw [hSθ]
    refine ⟨⟨d, ?_⟩, ?_⟩
    · exact hS.1.1.2.1.1 (hS.1.1.2.2.1.1 d.property)
    · ext z
      rfl
  obtain ⟨b, w, hb, haw, hwb⟩ := exists_diagonal_of_mem_langCube hK1 σ hσ1 Fr hFr
    (hSlang haS)
  haveI : CharP K 2 := charP_two_of_card (m := 2) (by rw [hK4]; norm_num)
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0 :=
    inv_mul_eq_iff_eq_mul.mp hgn
  let v : WeylGroup TwistTag.E6.tag := twE6W0
  have hg' : (show ModGL TwistTag.E6.tag (AlgebraicClosure K) from g) ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := hg
  have hlang' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr
      (show ModGL TwistTag.E6.tag (AlgebraicClosure K) from g) =
      (show ModGL TwistTag.E6.tag (AlgebraicClosure K) from g) *
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := hlang
  let t : ModGL TwistTag.E6.tag K := w
  have ht : t ∈ twistedE6InndiagGL K σ :=
    twInndiagGroup_le_twistedE6InndiagGL σ w.property
  obtain ⟨T, ι, hq, hΦ, hTb, hι, hrange, hact, hιval, hρ, _⟩ :=
    TwE6D5Core.exists_langSetup_of_twE6Frame (K := K) (q := 2) σ hK1 hσ1 hK2 hFr
      (v := v) hg' hlang' ht hwb
  have hact' : ∀ c, ι (a c) = rootDiagUnit Tag.E6 b * ι c * (rootDiagUnit Tag.E6 b)⁻¹ := by
    intro c
    rw [haw]
    exact hact c
  let Kq := (J.subgroupOf L).map (ggQuotHom θ)
  have hcomp : CFSG.Open.IsComponentOf Kq (ggFix a) := by
    have h := QTwoCav.isComponentOf_quotient_image hDL θ hS.1.1.2.2.1.2.2.2.2.2.1
    rw [hfixD] at h
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mp h
  have hfix : (ggFix a).map ι = T.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b} := by
    have h := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.map_fixSubgroup_eq_of_conj
      ι hι a (rootDiagUnit Tag.E6 b) hact'
    have hgg : ggFix a = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup a := by
      ext c
      rfl
    rw [← hgg, hrange] at h
    exact h
  have hcompΓ : CFSG.Open.IsComponentOf (Kq.map ι)
      (T.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) := by
    rw [← hfix]
    exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_map_inj hcomp ι hι
  have hb1 : rootDiagUnit Tag.E6 b ≠ 1 := by
    intro h
    have ha1 : a = 1 := by
      apply MulEquiv.ext
      intro c
      change a c = c
      apply hι
      simpa [h] using hact' c
    exact hd1 ha1
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : (3 : AlgebraicClosure K) ≠ 0 := by
    have h2 : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero _ 2
    have h3 : (3 : AlgebraicClosure K) = 1 := by
      calc (3 : AlgebraicClosure K) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [h3]
    exact one_ne_zero
  obtain ⟨i, hQ, hi⟩ := LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
    T (by decide) Nat.prime_three hpL hTb hb hb1 hcompΓ
  have hAlg : T.IsAlgebraic := LangSetup.isAlgebraic_of_isAlgClosure T K 2
    (by rw [hq, hK4]; norm_num)
  have hρneg : ∀ γ, IsRoot Tag.E6 γ → T.ρ γ = -γ := by
    intro γ hγ
    rw [hρ γ hγ]
    have h := twE6W0_smul (show Fin Tag.E6.rank → ℤ from permLattice TwistTag.E6.perm γ)
    exact h.trans (congrArg Neg.neg (TwistedDiag.permLattice_permLattice' γ))
  exact ⟨K, instF, instFin, σ, hK1, hσ1, Fr, hFr, θ, hN, g, T, ι, b, i,
    hι, hrange, hq, hAlg, hρneg, hb, hb1, hTb, hQ, hi, hιval, hg, hgn,
    hSθ ▸ hSlang, hSθ ▸ hScard⟩

end CFSG.StandardType.QTwoE6

end
