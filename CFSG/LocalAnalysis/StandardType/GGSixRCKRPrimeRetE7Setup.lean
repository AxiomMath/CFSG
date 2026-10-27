module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Frame
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RootSpanMap
import CFSG.RankThree.PartOne.KE.CTLang
import CFSG.RankThree.PartOne.KC.SymplecticInnerActorOdd
import CFSG.LieType.Chevalley.SingleEdgePerfect
import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
import CFSG.LieType.Ree.Endo
import CFSG.LocalAnalysis.StandardType.GGLangRootSym3
import CFSG.Adapters.TauCetiExceptional.BigCellEndgame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem mul_succ_ne_126 {r : ℕ} (h : 2 ≤ r) : r * (r + 1) ≠ 126 := by
  intro he
  have hle : r ≤ 11 := by
    by_contra hlt
    have hlt' : 11 < r := by omega
    have h2 : 12 * 13 ≤ r * (r + 1) := Nat.mul_le_mul hlt' (by omega)
    omega
  interval_cases r <;> norm_num at he

private theorem two_mul_pred_ne_126 {r : ℕ} (h : 4 ≤ r) : 2 * r * (r - 1) ≠ 126 := by
  intro he
  rw [mul_assoc] at he
  have h1 : r * (r - 1) = 63 := by omega
  have hle : r ≤ 8 := by
    by_contra hlt
    have hlt' : 8 < r := by omega
    have h2 : 9 * 8 ≤ r * (r - 1) :=
      Nat.mul_le_mul (by omega : 9 ≤ r) (by omega : 8 ≤ r - 1)
    omega
  interval_cases r <;> norm_num at h1

private theorem not_hasDiagramSymmetryType_E7 :
    ¬ HasDiagramSymmetryType {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} := by
  intro h
  have h126 : {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ}.ncard = 126 := ncard_isRoot_E7
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_succ_ne_126 h1 (by rw [← h2, h126])
  · exact two_mul_pred_ne_126 h1 (by rw [← h2, h126])
  · rw [h126] at h2
    omega

private theorem exists_weyl_of_frame {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ) (hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ) :
    ∃ u : WeylGroup Tag.E7, ∀ δ, IsRoot Tag.E7 δ → F.ι (S.ρ (F.j δ)) = u • δ := by
  classical
  have hj_inj : Function.Injective F.j := fun x y hxy => by
    rw [← F.ι_j x, ← F.ι_j y, hxy]
  have hj_mem : ∀ δ, IsRoot Tag.E7 δ → F.j δ ∈ Ψ := fun δ hδ => F.bijOn.mapsTo hδ
  have hι_root : ∀ γ ∈ Ψ, IsRoot Tag.E7 (F.ι γ) := by
    intro γ hγ
    obtain ⟨δ, hδ, hδγ⟩ := F.bijOn.surjOn hγ
    have h1 : F.j (F.ι γ) = F.j δ := by rw [F.j_ι γ hγ, hδγ]
    have h2 : F.ι γ = δ := hj_inj h1
    rwa [h2]
  set σ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ) :=
    fun δ => F.ι (S.ρ (F.j δ)) with hσdef
  have hσroot : Set.MapsTo σ {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ}
      {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} := by
    intro δ hδ
    exact hι_root _ (hρΨ _ (hj_mem δ hδ))
  have hσinj : Set.InjOn σ {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} := by
    intro a ha b hb hab
    have h1 : S.ρ (F.j a) = S.ρ (F.j b) := by
      have h2 : F.j (F.ι (S.ρ (F.j a))) = F.j (F.ι (S.ρ (F.j b))) := congrArg F.j hab
      simpa only [F.j_ι _ (hρΨ _ (hj_mem a ha)), F.j_ι _ (hρΨ _ (hj_mem b hb))] using h2
    exact hj_inj (S.ρ.injective h1)
  have hσbij : Set.BijOn σ {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ}
      {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} :=
    ((finite_setOf_isRoot Tag.E7).injOn_iff_bijOn_of_mapsTo hσroot).1 hσinj
  have hσform : ∀ γ ∈ {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ},
      ∀ δ ∈ {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ},
      CFSG.LieType.Steinberg.Adjoint.iform (σ γ) (σ δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ := by
    intro γ hγ δ hδ
    have e : CFSG.LieType.Steinberg.Adjoint.iform (F.ι (S.ρ (F.j γ)))
        (F.ι (S.ρ (F.j δ))) =
        CFSG.LieType.Steinberg.Adjoint.iform (S.ρ (F.j γ)) (S.ρ (F.j δ)) := by
      rw [← F.iform_j (F.ι (S.ρ (F.j γ))) (F.ι (S.ρ (F.j δ))),
        F.j_ι _ (hρΨ _ (hj_mem γ hγ)), F.j_ι _ (hρΨ _ (hj_mem δ hδ))]
    rw [e, S.frob.iform_eq, F.iform_j γ δ]
  have hσneg : ∀ γ ∈ {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ}, σ (-γ) = -σ γ := by
    intro γ hγ
    show F.ι (S.ρ (F.j (-γ))) = -F.ι (S.ρ (F.j γ))
    rw [map_neg, S.frob.neg_eq, map_neg]
  have hcomp : IsRootComponent {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} := by
    have hχ : ∀ γ : Fin Tag.E7.rank → ℤ,
        rootCharHom (1 : Fin Tag.E7.rank → GGLˣ) (Multiplicative.ofAdd γ) = 1 := by
      intro γ
      simp [rootCharHom, rootChar]
    have h := isRootComponent_componentRoots (τ := Tag.E7)
      (χ := rootCharHom (1 : Fin Tag.E7.rank → GGLˣ))
      (⟦⟨Pi.single (0 : Fin Tag.E7.rank) 1, isRoot_single Tag.E7 0, hχ _⟩⟧)
    rwa [CFSG.StandardType.TableCRes.famTrivial_componentRoots_eq_univ
      (Or.inr (Or.inl rfl)) _ hχ] at h
  obtain ⟨u, -, hu⟩ := CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds
    Tag.E7 _ hcomp not_hasDiagramSymmetryType_E7
    σ hσbij hσform hσneg
  exact ⟨u, fun δ hδ => hu δ hδ⟩

theorem exists_rckE7Setup {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ) (hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ) {h : ℕ}
    (hq : S.D.q = 2 ^ h) :
    ∃ SK : LangSetup Tag.E7 GGL 5, SK.D.q = S.D.q ∧
      (∀ δ, IsRoot Tag.E7 δ → SK.ρ δ = F.ι (S.ρ (F.j δ))) ∧
      (adjointGroup Tag.E7 GGL).map SK.D.step = adjointGroup Tag.E7 GGL ∧
      (∀ y : adjointGroup Tag.E7 GGL, ∃ hy : SK.D.step y ∈ adjointGroup Tag.E7 GGL,
        (F.ε ⟨SK.D.step y, hy⟩ : ModGL τ GGL) = S.D.step (F.ε y)) ∧
      Group.IsPerfect ↥SK.Γ ∧ Subgroup.center ↥SK.Γ = ⊥ ∧
      ∀ x ∈ SK.D.model, (∃ N : ℕ, Odd N ∧ x ^ N = 1) → x ∈ SK.Γ := by
  classical
  obtain ⟨u, hu⟩ := exists_weyl_of_frame S F hρΨ
  have hh : h ≠ 0 := by
    rintro rfl
    have h1 := S.hqpow.1
    rw [hq, pow_zero] at h1
    exact not_isPrimePow_one h1
  let K := TauCeti.frobeniusFixedSubfield GGL 2 h
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  haveI : CharP (ZMod 2) 2 := inferInstance
  haveI hcharGGL : CharP GGL 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) GGL).injective 2
  haveI hfinK : Finite K := TauCeti.finite_frobeniusFixedSubfield GGL 2 h hh
  have hKcard : Nat.card K = 2 ^ h := TauCeti.card_frobeniusFixedSubfield GGL 2 h hh
  haveI hAlgClos : IsAlgClosure K GGL :=
    CFSG.TauCetiBridge.BigCell.isAlgClosure_frobeniusFixedSubfield (p := 2) (L := GGL) h
  let Fr : GGL →+* GGL := iterateFrobenius GGL 2 h
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hKcard]
    exact iterateFrobenius_def 2 h c
  obtain ⟨g0, hg0C, hg0⟩ :=
    CFSG.RankThree.PartOne.KE.lang_conjugator Tag.E7 (ZMod 2) (ℓ := 2) (f := h) (by omega) GGL u
  have hpq : ¬ 5 ∣ Nat.card K := by
    rw [hKcard]
    intro h5
    have h2 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
    norm_num at h2
  have hperfK : Group.IsPerfect ↥(adjointGroup Tag.E7 K) :=
    ⟨single_edge_perfect Tag.E7 K (by decide)⟩
  obtain ⟨SK, hSKD, hd⟩ := exists_langSetup_untw_of_datum frobeniusOnRoots_proved 2
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) (K := K) (L := GGL) (p := 5) Nat.prime_five (by norm_num)
    hpq hperfK hFr u hg0C hg0
  have hSKq : SK.D.q = Nat.card K := by
    rw [hSKD]
    rfl
  have hqq : S.D.q = SK.D.q := by rw [hq, hSKq, hKcard]
  set ι : ↥(adjointGroup Tag.E7 K) →* ModGL Tag.E7 GGL :=
    (baseChangeGL (algebraMap K GGL)).comp (adjointGroup Tag.E7 K).subtype with hιdef
  have hι_inj : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hρeq : ∀ δ, IsRoot Tag.E7 δ → SK.ρ δ = u • δ := by
    intro δ hδ
    refine SK.rho_eq_smul_of_frob (Fr := Fr) (fun c => ?_) ?_ ?_ hδ
    · rw [hSKq]; exact hFr c
    · rw [hSKD]; rfl
    · rw [hSKD]; rfl
  have hρmap : ∀ δ, IsRoot Tag.E7 δ → SK.ρ δ = F.ι (S.ρ (F.j δ)) := by
    intro δ hδ
    rw [hρeq δ hδ]
    exact (hu δ hδ).symm
  have hmapstep : (adjointGroup Tag.E7 GGL).map SK.D.step = adjointGroup Tag.E7 GGL := by
    have h := SK.frob.map_rootSpan {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}
      (fun γ hγ => hγ)
    have himg : (SK.ρ : (Fin Tag.E7.rank → ℤ) → _) '' {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}
        = {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ} :=
      CFSG.StandardType.TableCRes.famTrivial_image_roots_eq SK.ρ SK.frob.isRoot_iff
    calc (adjointGroup Tag.E7 GGL).map SK.D.step
        = (rootSpan Tag.E7 GGL {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}).map SK.D.step := by
          rw [adjointGroup_eq_rootSpan]
      _ = rootSpan Tag.E7 GGL
            ((SK.ρ : (Fin Tag.E7.rank → ℤ) → _) '' {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}) := h
      _ = rootSpan Tag.E7 GGL {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ} := by rw [himg]
      _ = adjointGroup Tag.E7 GGL := by rw [adjointGroup_eq_rootSpan]
  have hstepmem : ∀ g ∈ adjointGroup Tag.E7 GGL, SK.D.step g ∈ adjointGroup Tag.E7 GGL := by
    intro g hg
    rw [← hmapstep]
    exact Subgroup.mem_map_of_mem _ hg
  let stepHom : ↥(adjointGroup Tag.E7 GGL) →* ↥(adjointGroup Tag.E7 GGL) :=
    { toFun := fun y => ⟨SK.D.step (y : ModGL Tag.E7 GGL), hstepmem _ y.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hhom : ((rootSpan τ GGL Ψ).subtype.comp (F.ε.toMonoidHom.comp stepHom)) =
      (S.D.step.comp ((rootSpan τ GGL Ψ).subtype.comp F.ε.toMonoidHom)) := by
    apply CFSG.LieType.Ree.adjointGroup_hom_ext (τ := Tag.E7) (K := GGL)
    · intro i c
      have hxEl : ((xElement (τ := Tag.E7) (K := GGL) i c : ↥(adjointGroup Tag.E7 GGL)) :
          ModGL Tag.E7 GGL) = pinnedX Tag.E7 GGL (Pi.single i 1) c := by
        change xUnit Tag.E7 GGL i c = pinnedX Tag.E7 GGL (Pi.single i 1) c
        exact (pinnedX_single Tag.E7 GGL i c).symm
      have hroot : IsRoot Tag.E7 (Pi.single i 1) := isRoot_single Tag.E7 i
      have hj : F.j (SK.ρ (Pi.single i 1)) = S.ρ (F.j (Pi.single i 1)) := by
        rw [hρmap _ hroot, F.j_ι _ (hρΨ _ (F.bijOn.mapsTo hroot))]
      have hL : ((rootSpan τ GGL Ψ).subtype.comp (F.ε.toMonoidHom.comp stepHom))
          (xElement i c) = pinnedX τ GGL (S.ρ (F.j (Pi.single i 1))) (c ^ SK.D.q) := by
        show (F.ε (stepHom (xElement i c)) : ModGL τ GGL) = _
        have hstepx : (stepHom (xElement i c) : ↥(adjointGroup Tag.E7 GGL)) =
            ⟨pinnedX Tag.E7 GGL (SK.ρ (Pi.single i 1)) (c ^ SK.D.q),
              pinnedX_mem_adjointGroup _ _⟩ := by
          refine Subtype.ext ?_
          show SK.D.step ((xElement (τ := Tag.E7) (K := GGL) i c : ↥(adjointGroup Tag.E7 GGL)) :
            ModGL Tag.E7 GGL) = _
          rw [hxEl]
          exact CFSG.StandardType.LangRat.step_pinnedX_of_charTwo SK hroot c
        rw [hstepx, F.pinned _ (SK.frob.isRoot_iff _ |>.2 hroot), hj]
      have hR : (S.D.step.comp ((rootSpan τ GGL Ψ).subtype.comp F.ε.toMonoidHom))
          (xElement i c) = pinnedX τ GGL (S.ρ (F.j (Pi.single i 1))) (c ^ SK.D.q) := by
        show S.D.step (F.ε (xElement i c)) = _
        have hx : ((F.ε (xElement i c) : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) =
            pinnedX τ GGL (F.j (Pi.single i 1)) c := by
          have hpin := F.pinned (Pi.single i 1) hroot c
          rw [← hpin,
            show xElement (τ := Tag.E7) (K := GGL) i c =
              ⟨pinnedX Tag.E7 GGL (Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ from
              Subtype.ext hxEl]
        rw [hx, CFSG.StandardType.LangRat.step_pinnedX_of_charTwo S
            (F.isRoot _ (F.bijOn.mapsTo hroot)) c, hqq]
      exact hL.trans hR.symm
    · intro i c
      have hyEl : ((yElement (τ := Tag.E7) (K := GGL) i c : ↥(adjointGroup Tag.E7 GGL)) :
          ModGL Tag.E7 GGL) = pinnedX Tag.E7 GGL (-Pi.single i 1) c := by
        change yUnit Tag.E7 GGL i c = pinnedX Tag.E7 GGL (-Pi.single i 1) c
        exact (pinnedX_neg_single Tag.E7 GGL i c).symm
      have hroot' : IsRoot Tag.E7 (-Pi.single i 1) := isRoot_neg_single Tag.E7 i
      have hj' : F.j (SK.ρ (-Pi.single i 1)) = S.ρ (F.j (-Pi.single i 1)) := by
        rw [hρmap _ hroot', F.j_ι _ (hρΨ _ (F.bijOn.mapsTo hroot'))]
      have hL : ((rootSpan τ GGL Ψ).subtype.comp (F.ε.toMonoidHom.comp stepHom))
          (yElement i c) = pinnedX τ GGL (S.ρ (F.j (-Pi.single i 1))) (c ^ SK.D.q) := by
        show (F.ε (stepHom (yElement i c)) : ModGL τ GGL) = _
        have hstepy : (stepHom (yElement i c) : ↥(adjointGroup Tag.E7 GGL)) =
            ⟨pinnedX Tag.E7 GGL (SK.ρ (-Pi.single i 1)) (c ^ SK.D.q),
              pinnedX_mem_adjointGroup _ _⟩ := by
          refine Subtype.ext ?_
          show SK.D.step ((yElement (τ := Tag.E7) (K := GGL) i c : ↥(adjointGroup Tag.E7 GGL)) :
            ModGL Tag.E7 GGL) = _
          rw [hyEl]
          exact CFSG.StandardType.LangRat.step_pinnedX_of_charTwo SK hroot' c
        rw [hstepy, F.pinned _ (SK.frob.isRoot_iff _ |>.2 hroot'), hj']
      have hR : (S.D.step.comp ((rootSpan τ GGL Ψ).subtype.comp F.ε.toMonoidHom))
          (yElement i c) = pinnedX τ GGL (S.ρ (F.j (-Pi.single i 1))) (c ^ SK.D.q) := by
        show S.D.step (F.ε (yElement i c)) = _
        have hy : ((F.ε (yElement i c) : ↥(rootSpan τ GGL Ψ)) : ModGL τ GGL) =
            pinnedX τ GGL (F.j (-Pi.single i 1)) c := by
          have hpin := F.pinned (-Pi.single i 1) hroot' c
          rw [← hpin,
            show yElement (τ := Tag.E7) (K := GGL) i c =
              ⟨pinnedX Tag.E7 GGL (-Pi.single i 1) c, pinnedX_mem_adjointGroup _ _⟩ from
              Subtype.ext hyEl]
        rw [hy, CFSG.StandardType.LangRat.step_pinnedX_of_charTwo S
            (F.isRoot _ (F.bijOn.mapsTo hroot')) c, hqq]
      exact hL.trans hR.symm
  haveI hfixfin : Finite ↥SK.D.fix := hd.finite_fix
  have hrelidx := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect
    (τ := Tag.E7) (K := K) (L := GGL) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr hFr SK.D.fix
    (fun x hx => ((LangDatum.mem_fix SK.D).1 hx).1)
    (fun x hx => by
      have h2 := ((LangDatum.mem_fix SK.D).1 hx).2
      rwa [hSKD] at h2)).1
  have hIrange : ι.range = (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K GGL)) := by
    rw [hιdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hrel : (ι.range).relIndex SK.D.fix ∣ 2 := hIrange ▸ hrelidx
  have hidx : ((ι.range).subgroupOf SK.D.fix).index ∣ 2 := by
    have h := hrel
    rw [← inf_eq_left.mpr hd.range_le] at h
    rw [show (ι.range).subgroupOf SK.D.fix =
      (ι.range ⊓ SK.D.fix).subgroupOf SK.D.fix from by rw [inf_eq_left.mpr hd.range_le]]
    exact h
  refine ⟨SK, hqq.symm, hρmap, hmapstep, ?_, ?_, ?_, ?_⟩
  ·
    intro y
    refine ⟨hstepmem _ y.2, ?_⟩
    have h := congrArg (fun f => f y) hhom
    simpa [stepHom, MonoidHom.comp_apply] using h
  ·
    haveI : Group.IsPerfect ↥(adjointGroup Tag.E7 K) := hperfK
    have e : ↥(adjointGroup Tag.E7 K) ≃* ↥SK.Γ := hd.mulEquiv hι_inj
    let f : ↥(adjointGroup Tag.E7 K) →* ↥SK.Γ :=
      { toFun := fun x => e x, map_one' := map_one e, map_mul' := map_mul e }
    exact Group.IsPerfect.ofSurjective (f := f) (fun y => ⟨e.symm y, by simp [f]⟩)
  ·
    have e : ↥(adjointGroup Tag.E7 K) ≃* ↥SK.Γ := hd.mulEquiv hι_inj
    refine eq_bot_iff.2 fun z hz => ?_
    have hze : e.symm z ∈ Subgroup.center ↥(adjointGroup Tag.E7 K) := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      obtain ⟨c, rfl⟩ := e.symm.surjective g
      calc e.symm c * e.symm z = e.symm (c * z) := (map_mul e.symm c z).symm
        _ = e.symm (z * c) := by rw [Subgroup.mem_center_iff.1 hz c]
        _ = e.symm z * e.symm c := map_mul e.symm z c
    rw [center_adjointGroup_eq_bot (τ := Tag.E7) (K := K), Subgroup.mem_bot] at hze
    exact Subgroup.mem_bot.2 (e.symm.injective (by rw [hze, map_one]))
  ·
    intro x hxM hodd
    obtain ⟨N, hNodd, hxN⟩ := hodd
    rw [LangDescent.model_eq] at hxM
    obtain ⟨y, hyfix, hyx⟩ := Subgroup.mem_map.1 hxM
    rw [← hyx] at hxN ⊢
    have hyN : y ^ N = 1 := by
      have h1 : (SK.D.g0⁻¹ * y * SK.D.g0) ^ N = 1 := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hxN
      have h2 : (SK.D.g0 * (SK.D.g0⁻¹ * y * SK.D.g0) * SK.D.g0⁻¹) ^ N = 1 := by
        rw [conj_pow, h1, mul_one, mul_inv_cancel]
      rwa [show SK.D.g0 * (SK.D.g0⁻¹ * y * SK.D.g0) * SK.D.g0⁻¹ = y by group] at h2
    have hyI : y ∈ ι.range := by
      have hmem : (⟨y, hyfix⟩ : ↥SK.D.fix) ∈ (ι.range).subgroupOf SK.D.fix := by
        refine CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hidx ?_
        have h1 : (⟨y, hyfix⟩ : ↥SK.D.fix) ^ N = 1 := by
          refine Subtype.ext ?_
          change ((⟨y, hyfix⟩ : ↥SK.D.fix) : ModGL Tag.E7 GGL) ^ N = 1
          simpa using hyN
        exact Odd.of_dvd_nat hNodd (orderOf_dvd_iff_pow_eq_one.2 h1)
      exact Subgroup.mem_subgroupOf.1 hmem
    change (MulAut.conj SK.D.g0⁻¹) y ∈ SK.D.Γ
    rw [LangDescent.Γ_eq hd]
    exact Subgroup.mem_map_of_mem _ hyI

end CFSG.StandardType.RCKRP

end
