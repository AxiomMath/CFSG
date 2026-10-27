module

public import CFSG.LocalAnalysis.StandardType.GGTwKGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGKGLayerTransport
public import CFSG.LocalAnalysis.StandardType.GGKGLayersTheta
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeCoroot

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance 100] commutatorElement

private theorem commutator_mul_commute {G : Type*} [Group G] {a a' c c' : G}
    (hca : Commute c a) (hca' : Commute c a') (hcc' : Commute c c') (hc'a : Commute c' a) :
    ⁅a * c, a' * c'⁆ = ⁅a, a'⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul a c (a' * c')]
  rw [commutatorElement_mul_right_eq_mul_conj c a' c']
  rw [commutatorElement_mul_right_eq_mul_conj a a' c']
  rw [hca'.commutator_eq, hcc'.commutator_eq, hc'a.symm.commutator_eq]
  group

theorem ggLayerOf_sup_of_cyclic {G : Type} [Group G] {X D : Subgroup G} (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) (hD : IsQuasisimple D) :
    GGLayerOf (X ⊔ D) D := by
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    letI : CommGroup ↥X := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have hcentral : ∀ x ∈ X, ∀ d ∈ D, d * x = x * d := by
    intro x hx d hd
    exact (Subgroup.mem_centralizer_iff.mp (hXD hx)) d hd
  refine ⟨le_sup_right, ?_, hD, ?_⟩
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 ?_
    exact sup_le (le_trans hXD (Subgroup.centralizer_le_normalizer (D : Set G)))
      Subgroup.le_normalizer
  · intro P hPX hPperf
    have hfac : ∀ g ∈ X ⊔ D, ∃ x ∈ X, ∃ d ∈ D, g = x * d := by
      intro g hg
      rw [Subgroup.sup_eq_closure] at hg
      refine Subgroup.closure_induction (p := fun g _ => ∃ x ∈ X, ∃ d ∈ D, g = x * d)
        ?_ ?_ ?_ ?_ hg
      · intro y hy
        rcases hy with hyX | hyD
        · exact ⟨y, hyX, 1, D.one_mem, by rw [mul_one]⟩
        · exact ⟨1, X.one_mem, y, hyD, by rw [one_mul]⟩
      · exact ⟨1, X.one_mem, 1, D.one_mem, by rw [mul_one]⟩
      · intro a b _ _ iha ihb
        obtain ⟨xa, hxa, da, hda, rfl⟩ := iha
        obtain ⟨xb, hxb, db, hdb, rfl⟩ := ihb
        refine ⟨xa * xb, X.mul_mem hxa hxb, da * db, D.mul_mem hda hdb, ?_⟩
        calc xa * da * (xb * db)
            = xa * (da * (xb * db)) := by group
          _ = xa * ((da * xb) * db) := by group
          _ = xa * ((xb * da) * db) := by rw [hcentral xb hxb da hda]
          _ = xa * (xb * (da * db)) := by group
          _ = xa * xb * (da * db) := by group
      · intro a _ iha
        obtain ⟨xa, hxa, da, hda, rfl⟩ := iha
        refine ⟨xa⁻¹, X.inv_mem hxa, da⁻¹, D.inv_mem hda, ?_⟩
        simpa [mul_inv_rev] using (congrArg Inv.inv (hcentral xa hxa da hda)).symm
    have hcomm_le : ⁅X ⊔ D, X ⊔ D⁆ ≤ D := by
      rw [Subgroup.commutator_le]
      intro g1 hg1 g2 hg2
      obtain ⟨x1, hx1, d1, hd1, rfl⟩ := hfac g1 hg1
      obtain ⟨x2, hx2, d2, hd2, rfl⟩ := hfac g2 hg2
      rw [← hcentral x1 hx1 d1 hd1, ← hcentral x2 hx2 d2 hd2]
      rw [commutator_mul_commute (hca := (hcentral x1 hx1 d1 hd1).symm)
        (hca' := (hcentral x1 hx1 d2 hd2).symm)
        (hcc' := hXcomm x1 hx1 x2 hx2)
        (hc'a := (hcentral x2 hx2 d1 hd1).symm)]
      rw [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem hd1 hd2) (D.inv_mem hd1)) (D.inv_mem hd2)
    calc P = ⁅P, P⁆ := hPperf.symm
      _ ≤ ⁅X ⊔ D, X ⊔ D⁆ := Subgroup.commutator_mono hPX hPX
      _ ≤ D := hcomm_le

theorem layer_of_centralizer_tw {S R L' : Type} [Group S] [Group R] [Group L'] {C : Subgroup S}
    (Θ : R ≃* ↥C) (ψ : L' →* R) (hψ : Function.Surjective ψ) (F : Set (MulAut L'))
    (D : Set S)
    (hFD : ∀ f ∈ F, ∃ d ∈ D, ∀ l : L',
      ((Θ (ψ (f l)) : ↥C) : S) = d * ((Θ (ψ l) : ↥C) : S) * d⁻¹)
    (hDF : ∀ d ∈ D, ∃ f ∈ F, ∀ l : L',
      ((Θ (ψ (f l)) : ↥C) : S) = d * ((Θ (ψ l) : ↥C) : S) * d⁻¹)
    {E : Subgroup ↥C} (h : GGLayerOf ((Subgroup.centralizer D).subgroupOf C) E) :
    GGLayerOf (ggRFix ψ F) (E.comap Θ.toMonoidHom) := by
  have hmap : (ggRFix ψ F).map Θ.toMonoidHom =
      (Subgroup.centralizer D).subgroupOf C := by
    ext c
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨r, hr, rfl⟩ d hd
      obtain ⟨l, hl, hfix⟩ := hr
      rw [← hl]
      obtain ⟨f, hf, hfl⟩ := hDF d hd
      have hc_eq : ((Θ (ψ l) : ↥C) : S) = d * ((Θ (ψ l) : ↥C) : S) * d⁻¹ := by
        have hfl' := hfl l
        rwa [hfix f hf] at hfl'
      have hcd : ((Θ (ψ l) : ↥C) : S) * d = d * ((Θ (ψ l) : ↥C) : S) := by
        conv_lhs => rw [hc_eq]
        group
      exact hcd.symm
    · rintro hcen
      refine ⟨Θ.symm c, ?_, ?_⟩
      · obtain ⟨l, hl⟩ := hψ (Θ.symm c)
        refine ⟨l, hl, ?_⟩
        intro f hf
        obtain ⟨d, hd, hdl⟩ := hFD f hf
        have hΘl : Θ (ψ l) = c := by
          rw [hl]
          exact Θ.apply_symm_apply c
        have hleft : ((Θ (ψ (f l)) : ↥C) : S) = d * (c : S) * d⁻¹ := by
          rw [hdl l, hΘl]
        have hfixd : d * (c : S) * d⁻¹ = (c : S) := by
          rw [hcen d hd]
          group
        have hval : ((Θ (ψ (f l)) : ↥C) : S) = ((Θ (ψ l) : ↥C) : S) := by
          rw [hleft, hfixd, hΘl]
        exact Θ.injective (Subtype.ext hval)
      · exact Θ.apply_symm_apply c
  rw [← hmap] at h
  exact ggLayerOf_comap Θ.toMonoidHom Θ.injective h


theorem corootTuple_eq_zetaVec_kg {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1)
    (β : Fin Tag.E6.rank → ℤ) :
    TwE6RootAs.corootTuple β ζ = zetaVec (τ := Tag.E6) ζ hζ (kgExpVec β) := by
  rw [TwE6EndNode3.corootTuple_eq_zetaVec ζ hζ β]
  rfl

namespace KGTwFrame

variable {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {R : Type} [Group R]
  {Θ : R ≃* ↥(twistedE6RootGroup K σ)} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1} {L' : Type} [Group L'] {ψ : L' →* R}
  {A : Subgroup (MulAut L')} {v : WeylGroup TwistTag.E6.tag}
  {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
  {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}

theorem t_coroot (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) (x : Fin 6 → ZMod 3) :
    g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) * g =
      rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) := by
  rw [(hF.ht x).2]
  group

theorem t_zero (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) : t 0 = 1 := by
  have hz : zetaVec (τ := Tag.E6) ζ hζ (0 : Fin 6 → ZMod 3) = 1 := kgZetaE6_zero ζ hζ
  have hdone : rootDiagUnit TwistTag.E6.tag (1 : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) = 1 :=
    rootDiagUnit_one (τ := TwistTag.E6.tag)
  apply baseChangeGL_injective (τ := TwistTag.E6.tag)
    (f := algebraMap K (AlgebraicClosure K))
  rw [(hF.ht 0).2, map_one, hz, hdone]
  group

theorem t_add (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) (x y : Fin 6 → ZMod 3) :
    t (x + y) = t x * t y := by
  have hzadd : zetaVec (τ := Tag.E6) ζ hζ (x + y) =
      zetaVec (τ := Tag.E6) ζ hζ x * zetaVec (τ := Tag.E6) ζ hζ y :=
    kgZetaE6_add ζ hζ x y
  have hd : rootDiagUnit TwistTag.E6.tag
        (zetaVec (τ := Tag.E6) ζ hζ x * zetaVec (τ := Tag.E6) ζ hζ y) =
      rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) *
        rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ y) :=
    (rootDiagUnit_mul (τ := TwistTag.E6.tag) (zetaVec (τ := Tag.E6) ζ hζ x)
      (zetaVec (τ := Tag.E6) ζ hζ y))
  apply baseChangeGL_injective (τ := TwistTag.E6.tag)
    (f := algebraMap K (AlgebraicClosure K))
  rw [(hF.ht (x + y)).2, map_mul, (hF.ht x).2, (hF.ht y).2, hzadd, hd]
  group

theorem t_neg (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) (x : Fin 6 → ZMod 3) :
    t (-x) = (t x)⁻¹ := by
  have h : t (-x) * t x = 1 := by
    rw [← t_add hF (-x) x, neg_add_cancel, t_zero hF]
  exact eq_inv_of_mul_eq_one_left h

theorem t_mem_of_closure (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t)
    (E : Subgroup (ModGL TwistTag.E6.tag K)) {S : Set (Fin 6 → ZMod 3)}
    (hS : ∀ x ∈ S, t x ∈ E) {x : Fin 6 → ZMod 3} (hx : x ∈ AddSubgroup.closure S) :
    t x ∈ E := by
  refine AddSubgroup.closure_induction (p := fun x _ => t x ∈ E) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact hS y hy
  · rw [t_zero hF]
    exact E.one_mem
  · intro a b _ _ iha ihb
    rw [t_add hF a b]
    exact E.mul_mem iha ihb
  · intro a _ iha
    rw [t_neg hF a]
    exact E.inv_mem iha

end KGTwFrame

end CFSG.StandardType.KGL

end
