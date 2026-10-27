module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem ggLieY5_isComponentOf_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') {L K : Subgroup G} (h : IsComponentOf L K) :
    IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1,
   CFSG.Assembly.IsSubnormal.map e.toMonoidHom h.2.1,
   CFSG.Assembly.IsQuasisimple.of_mulEquiv
     (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm h.2.2⟩

private theorem ggLieY5_map_centralizer {G : Type*} [Group G] (e : G ≃* G) (A : Subgroup G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hy' : b * y = y * b := hy b hb
    rw [← map_mul, ← map_mul, hy']
  · intro hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
    intro a ha
    have h := hx (e a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    have h2 := congrArg (⇑e.symm) h
    simpa using h2

private theorem ggLieY5_a3Case_map {G : Type} [Group G] (e : G ≃* G) {K : Subgroup G}
    (h : GGSixLSevenA3Case K) : GGSixLSevenA3Case (K.map e.toMonoidHom) := by
  let eK : ↥K ≃* ↥(K.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
  have e' : (↥K ⧸ Subgroup.center ↥K) ≃*
      (↥(K.map e.toMonoidHom) ⧸ Subgroup.center ↥(K.map e.toMonoidHom)) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(K.map e.toMonoidHom)) eK
      (Subgroup.map_center_eq eK)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e' h

private theorem ggLieY5_conj_comp {G : Type*} [Group G] (g h : G) :
    (MulAut.conj g).toMonoidHom.comp
        ((MulAut.conj h).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
      (MulAut.conj (g * h * g⁻¹)).toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem ggLieY5_conj_inv_comp {G : Type*} [Group G] (g : G) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

theorem ggLieA3AlgToral_of_datum
    (hC6 : GGLieCentIIPlane3 .E6) (hCF : GGLieCentIIPlane3 .F4)
    (hA6 : GGLieSmallFormA8Plane3 .E6) (hAF : GGLieSmallFormA8Plane3 .F4)
    (hNo : GGLieA3DatumNo) (hE6 : GGLieA3DatumE6) : GGLieA3AlgToral := by
  intro t ht f hf A K hA_le hel hcard hT hKcomp hKA3
  have hfive : GGExcFive t := by
    rcases ht with h | h | h
    · rw [h]; unfold GGExcFive; exact Or.inr (Or.inl rfl)
    · rw [h]; unfold GGExcFive; exact Or.inl rfl
    · rw [h]; unfold GGExcFive; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hΦ : IsSteinbergEnd (langTag t) GGL (2 ^ f) (ggPhi t f) :=
    isSteinbergEnd_ggPhi hfive f
  have hCt : GGLieCentIIPlane3 (langTag t) := by
    rcases ht with rfl | rfl | rfl
    · exact hC6
    · exact hCF
    · exact hC6
  have hAt : GGLieSmallFormA8Plane3 (langTag t) := by
    rcases ht with rfl | rfl | rfl
    · exact hA6
    · exact hAF
    · exact hA6
  obtain ⟨w, g, hg, hlang, a₁, a₂, hmodelRaw, htorus1, htorus2, hp1, hp2, hmapRaw⟩ :=
    ggLiePlaneFrame (τ := langTag t) hf hΦ Nat.prime_three (by norm_num) hA_le hel hcard hT
  let c : ModGL (langTag t) GGL →* ModGL (langTag t) GGL := (MulAut.conj g⁻¹).toMonoidHom
  let D : LangDatum (langTag t) GGL := langDatumOfPosition hΦ w g hg hlang
  have hmodel : (ratPoints (ggPhi t f)).map c = D.model := hmodelRaw
  have hmap : A.map c = Subgroup.closure
      {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} := hmapRaw
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved (langTag t) GGL D
  have hfinΦ : Finite ↥(ratPoints (ggPhi t f)) :=
    finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
  have hfinD : Finite ↥D.model := by
    haveI : Finite ↥(ratPoints (ggPhi t f)) := hfinΦ
    have hsurj : Function.Surjective (fun x : ↥(ratPoints (ggPhi t f)) =>
        (⟨c x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((ratPoints (ggPhi t f)).map c))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfinMap : Finite ↥((ratPoints (ggPhi t f)).map c) := Finite.of_surjective _ hsurj
    rwa [hmodel] at hfinMap
  have hDq : D.q = 2 ^ f := rfl
  have hcard_cl : Nat.card (Subgroup.closure
      {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂}) = 3 ^ 2 := by
    rw [← hmap, Subgroup.card_map_of_injective (f := c) (MulAut.conj g⁻¹).injective, hcard]
  have hΓmap : (⁅ggFixGp t f, ggFixGp t f⁆ : Subgroup (ModGL (langTag t) GGL)).map c = D.Γ := by
    rw [Subgroup.map_commutator]
    have h1 : Subgroup.map c (ggFixGp t f) = D.model := by
      change Subgroup.map c (ratPoints (ggPhi t f)) = D.model
      exact hmodel
    rw [h1]
    rfl
  have hXmap : (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
        Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))).map c =
      D.Γ ⊓ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} :
          Set (ModGL (langTag t) GGL)) := by
    rw [Subgroup.map_inf (⁅ggFixGp t f, ggFixGp t f⁆)
      (Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))) c (MulAut.conj g⁻¹).injective]
    rw [hΓmap, ggLieY5_map_centralizer (MulAut.conj g⁻¹) A, hmap]
  have hK' : IsComponentOf (K.map c)
      (D.Γ ⊓ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit (langTag t) a₁, rootDiagUnit (langTag t) a₂} :
          Set (ModGL (langTag t) GGL))) := by
    have h := ggLieY5_isComponentOf_map_mulEquiv (MulAut.conj g⁻¹) hKcomp
    rwa [hXmap] at h
  obtain ⟨i, hi⟩ := hCt GGL D ρ hρ hfinD ⟨f, hf, hDq⟩ a₁ a₂ htorus1 htorus2 hp1 hp2 hcard_cl
    (K.map c) hK'
  have hquasi : CFSG.IsQuasisimple
      ↥(ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr (hi ▸ hK'.2.2)
  have hA3comp : GGSixLSevenA3Case (ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)) :=
    hi ▸ ggLieY5_a3Case_map (MulAut.conj g⁻¹) hKA3
  have hA8 := hAt GGL D ρ hρ hfinD ⟨f, hf, hDq⟩
      a₁ a₂ htorus1 htorus2 hp1 hp2 hcard_cl i hquasi hA3comp
  have hf1 : f = 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by
      change 2 ^ f = 2 ^ 1
      rw [← hDq, hA8.2.2.2.2, pow_one])
  subst f
  have hyp : GGLieA3DatumHyp t hΦ w g hg hlang a₁ a₂ ρ i :=
    ⟨hρ, htorus1, htorus2, hp1, hp2, hcard_cl, hA8.1, hA8.2.1, hA8.2.2.1, hA8.2.2.2.1⟩
  rcases ht with rfl | rfl | rfl
  · obtain ⟨h, hhΓ, hhle⟩ := hE6 hΦ w g hg hlang a₁ a₂ ρ i hyp
    have hhD : h ∈ D.Γ := hhΓ
    have hhmap : h ∈ (⁅ggFixGp .E6 1, ggFixGp .E6 1⁆ :
        Subgroup (ModGL (langTag .E6) GGL)).map c := by
      rw [hΓmap]
      exact hhD
    obtain ⟨y, hyX0, hyh⟩ := Subgroup.mem_map.mp hhmap
    have h'y : g * h * g⁻¹ = y := by
      rw [← hyh]
      change g * ((MulAut.conj g⁻¹) y) * g⁻¹ = y
      rw [MulAut.conj_apply]
      group
    have hle1 : (Subgroup.closure
        {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂}).map
        (MulAut.conj h).toMonoidHom ≤ K.map c := hi.symm ▸ hhle
    have hle2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle1
    have hLHS : ((Subgroup.closure {rootDiagUnit (langTag .E6) a₁,
          rootDiagUnit (langTag .E6) a₂}).map (MulAut.conj h).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = A.map (MulAut.conj (g * h * g⁻¹)).toMonoidHom := by
      rw [← hmap, Subgroup.map_map (K := A) (g := (MulAut.conj h).toMonoidHom) (f := c),
        Subgroup.map_map (K := A) (g := (MulAut.conj g).toMonoidHom)
          (f := (MulAut.conj h).toMonoidHom.comp c),
        ggLieY5_conj_comp]
    have hRHS : (K.map c).map (MulAut.conj g).toMonoidHom = K := by
      rw [Subgroup.map_map (K := K) (g := (MulAut.conj g).toMonoidHom) (f := c),
        ggLieY5_conj_inv_comp, Subgroup.map_id]
    refine ⟨fun _ => ⟨rfl, ⟨g * h * g⁻¹, ?_, ?_⟩⟩,
      fun hh => absurd hh (by decide)⟩
    · rw [h'y]
      exact hyX0
    · rw [hLHS, hRHS] at hle2
      exact hle2
  · exact ⟨fun hh => absurd hh (by decide),
      fun _ => hNo .F4 (Or.inl rfl) hΦ w g hg hlang a₁ a₂ ρ i hyp⟩
  · exact ⟨fun hh => absurd hh (by decide),
      fun _ => hNo .twistedE6 (Or.inr rfl) hΦ w g hg hlang a₁ a₂ ρ i hyp⟩

end CFSG.StandardType.LieCore
