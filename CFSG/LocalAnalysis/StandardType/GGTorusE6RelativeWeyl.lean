module

public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6SplitNormalizer
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.LieType.Chevalley.GraphFixedRankOneScalar
public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4CoreAux

public noncomputable section

namespace CFSG.StandardType.E6RelativeWeyl

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K] (σ : K →+* K)
variable {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n)
variable (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
variable {ζ : Kˣ} (hζo : orderOf ζ = p) (hζσ : σ (ζ : K) = ζ)

@[expose] def stdFrame (hp : p.Prime) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin Tag.F4.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ

@[expose] def nNative (a : Fin TwistTag.E6.foldedTag.rank) :
    ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  ⟨orbitN TwistTag.E6 K σ a 1, orbitN_mem_graphFixedRootGroup TwistTag.E6 σ a 1⟩

def f4RevTag : Fin Tag.F4.rank ≃ Fin Tag.F4.rank := Fin.revPerm

theorem f4RevTag_eq_f4FoldedIndex (i : Fin Tag.F4.rank) :
    f4RevTag i = f4FoldedIndex i := by
  fin_cases i <;> rfl

theorem coxeterF4_rev (i j : Fin Tag.F4.rank) :
    CoxeterMatrix.F₄.M (f4RevTag i) (f4RevTag j) = CoxeterMatrix.F₄.M i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem coxeter_rev (i j : Fin Tag.F4.rank) :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan Tag.F4))
        (f4RevTag i) (f4RevTag j) =
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan Tag.F4)) i j := by
  rw [← CFSG.StandardType.FrameRoute.coxeterF4_eq]
  exact coxeterF4_rev i j

def revHom : WeylGroup Tag.F4 →* WeylGroup Tag.F4 :=
  (coxeterSystem Tag.F4).lift ⟨fun i => simple Tag.F4 (f4RevTag i), by
    intro i j
    rw [← coxeter_rev i j]
    exact (coxeterSystem Tag.F4).simple_mul_simple_pow (f4RevTag i) (f4RevTag j)⟩

theorem revHom_simple (i : Fin Tag.F4.rank) :
    revHom (simple Tag.F4 i) = simple Tag.F4 (f4RevTag i) :=
  CoxeterSystem.lift_apply_simple (coxeterSystem Tag.F4) _ i

def revHomInv : WeylGroup Tag.F4 →* WeylGroup Tag.F4 :=
  (coxeterSystem Tag.F4).lift ⟨fun i => simple Tag.F4 (f4RevTag.symm i), by
    intro i j
    have h := coxeter_rev (f4RevTag.symm i) (f4RevTag.symm j)
    simp only [Equiv.apply_symm_apply] at h
    rw [h]
    exact (coxeterSystem Tag.F4).simple_mul_simple_pow _ _⟩

theorem revHomInv_simple (i : Fin Tag.F4.rank) :
    revHomInv (simple Tag.F4 i) = simple Tag.F4 (f4RevTag.symm i) :=
  CoxeterSystem.lift_apply_simple (coxeterSystem Tag.F4) _ i

theorem revHom_comp_inv : revHomInv.comp revHom = MonoidHom.id _ := by
  apply (coxeterSystem Tag.F4).ext_simple
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, revHom_simple, revHomInv_simple]
  rw [Equiv.symm_apply_apply]

theorem revHom_inv_comp : revHom.comp revHomInv = MonoidHom.id _ := by
  apply (coxeterSystem Tag.F4).ext_simple
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, revHomInv_simple, revHom_simple]
  rw [Equiv.apply_symm_apply]

def revWeyl : WeylGroup Tag.F4 ≃* WeylGroup Tag.F4 :=
  MulEquiv.ofBijective revHom
    ⟨fun a b hab => by
      have ha := DFunLike.congr_fun revHom_comp_inv a
      have hb := DFunLike.congr_fun revHom_comp_inv b
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at ha hb
      rw [← ha, hab, hb],
     fun y => by
      have hh := DFunLike.congr_fun revHom_inv_comp y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hh
      exact ⟨revHomInv y, hh⟩⟩

theorem revWeyl_simple (i : Fin Tag.F4.rank) :
    revWeyl (simple Tag.F4 i) = simple Tag.F4 (f4RevTag i) :=
  revHom_simple i

theorem nNative_mem_graphFixedRootMonomial (a : Fin TwistTag.E6.foldedTag.rank) :
    ((nNative (K := K) (σ := σ) a : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootMonomial TwistTag.E6 K σ := by
  have hmono : (orbitN TwistTag.E6 K σ a 1 : ModGL TwistTag.E6.tag K) ∈
      monomialSubgroup TwistTag.E6.tag K := by
    rw [coe_orbitN_one]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_monomialSubgroup j
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hmono,
    graphFixedRootGroup_le TwistTag.E6 K σ (nNative (K := K) (σ := σ) a).2⟩,
    (nNative (K := K) (σ := σ) a).2⟩

theorem nNative_conj (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (a : Fin TwistTag.E6.foldedTag.rank)
    (s : Fin Tag.F4.rank → ZMod p) :
    nNative (K := K) (σ := σ) a * stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)
        (Multiplicative.ofAdd s) * (nNative (K := K) (σ := σ) a)⁻¹ =
      stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)
        (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p (simple Tag.F4 a) s)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hM := nNative_mem_graphFixedRootMonomial (K := K) (σ := σ) a
  have h2 := ExcFrames.twE6SplitFrameHom_conj σ hζ hζσ hM s
  have hGF : (nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K) ∈
      graphFixedMonomial TwistTag.E6 K σ := (Subgroup.mem_inf.mp hM).1
  have hmono : (nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K) ∈
      monomialSubgroup TwistTag.E6.tag K := (Subgroup.mem_inf.mp hGF).1
  have hweyl : graphFixedRootWeylHom TwistTag.E6 K σ
      ⟨(nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K), hM⟩ =
      TwistTag.E6.orbitReflection a := by
    change weylQuotientHom TwistTag.E6.tag K
      ⟨(nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K), hmono⟩ =
      TwistTag.E6.orbitReflection a
    apply weylQuotientHom_eq
    have hmap : MapsRootLines (orbitN TwistTag.E6 K σ a 1 : ModGL TwistTag.E6.tag K)
        (TwistTag.E6.orbitReflection a) := by
      rw [coe_orbitN_one]
      exact mapsRootLines_list_prod (τ := TwistTag.E6.tag) (R := K)
        (TwistTag.E6.orbitWord a)
    simpa only [nNative, Subgroup.coe_mk] using hmap
  have hfold : foldedWeylEquiv TwistTag.E6
      ⟨graphFixedRootWeylHom TwistTag.E6 K σ
          ⟨(nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K), hM⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 K σ).le
          ⟨⟨(nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K), hM⟩, rfl⟩⟩ =
      simple Tag.F4 a := by
    rw [show (⟨graphFixedRootWeylHom TwistTag.E6 K σ
          ⟨(nNative (K := K) (σ := σ) a : ModGL TwistTag.E6.tag K), hM⟩, _⟩ :
        relWeylTwist TwistTag.E6) =
        ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩ from Subtype.ext hweyl]
    exact foldedWeylEquiv_orbitReflection TwistTag.E6 a
  rw [hfold] at h2
  simpa only [stdFrame] using h2

theorem normalizer_action (hp5 : 5 ≤ p) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (g : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hg : g ∈ Subgroup.normalizer
      ((stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)).range : Set _)) :
    ∃ u : WeylGroup Tag.F4, ∀ s : Fin Tag.F4.rank → ZMod p,
      g * stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s) * g⁻¹ =
        stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p u s)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let ι := stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)
  have hxs : ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ ∈ ι.range := fun s =>
    (Subgroup.mem_normalizer_iff.mp hg _).mp (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hxC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left g.2
  have hxMono : (g : ModGL TwistTag.E6.tag K) ∈ monomialSubgroup Tag.E6 K := by
    refine ExcFrames.mem_monomialSubgroup_of_conj_e6SplitTorsion hp5 hζo hxC fun v hv => ?_
    obtain ⟨c, hc, h05, h24, rfl⟩ := hv
    obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_twE6SplitTheta_eq hp5 hζo hζ hc h05 h24
    obtain ⟨t, ht⟩ := hxs s
    obtain ⟨c', hc', h05', h24', hc'eq⟩ :=
      ExcFrames.frameDiag_twE6SplitTheta_eq_rootDiagUnit hζ (Multiplicative.toAdd t)
    refine ⟨c', hc', h05', h24', ?_⟩
    have h1 := congrArg (fun y : ↥(graphFixedRootGroup TwistTag.E6 K σ) =>
      (y : ModGL TwistTag.E6.tag K)) ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [← hc'eq, ← hs]
    exact h1.symm
  have hxM : (g : ModGL TwistTag.E6.tag K) ∈ graphFixedRootMonomial TwistTag.E6 K σ :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxMono,
      graphFixedRootGroup_le TwistTag.E6 K σ g.2⟩, g.2⟩
  refine ⟨foldedWeylEquiv TwistTag.E6
    ⟨graphFixedRootWeylHom TwistTag.E6 K σ ⟨(g : ModGL TwistTag.E6.tag K), hxM⟩,
      (graphFixedRootWeylHom_range TwistTag.E6 K σ).le
        ⟨⟨(g : ModGL TwistTag.E6.tag K), hxM⟩, rfl⟩⟩, fun s => ?_⟩
  have h2 := ExcFrames.twE6SplitFrameHom_conj σ hζ hζσ hxM s
  simpa only [stdFrame, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2

theorem exists_markedWeyl_standard (hp5 : 5 ≤ p) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    ∃ hnN : ∀ a : Fin TwistTag.E6.foldedTag.rank,
        nNative (K := K) (σ := σ) a ∈ Subgroup.normalizer
          ((stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)).range : Set _),
      ggAutomizer (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)).range =
        Subgroup.closure (Set.range fun a => ggConjAut _ (hnN a)) ∧
      ∃ e : WeylGroup Tag.F4 ≃* ↥(ggAutomizer
          (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)).range),
        ∀ a, (e (simple Tag.F4 a) : MulAut _) =
          ggConjAut _ (hnN a) := by
  letI : Fact p.Prime := ⟨hp⟩
  let ι := stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  exact exists_markedWeyl_ggAutomizer hodd (E := ι.range) (ι := ι)
    (ExcFrames.twE6SplitFrameHom_injective σ hp5 hζo hζ hζσ) rfl
    (fun a => nNative (K := K) (σ := σ) a)
    (fun a s => nNative_conj (K := K) (σ := σ) (p := p) (hp := hp)
      (hζo := hζo) (hζ := hζ) (hζσ := hζσ) (a := a) (s := s))
    (fun g hg => normalizer_action (K := K) (σ := σ) (p := p) (hp := hp)
      (hp5 := hp5) (hζo := hζo) (hζ := hζ) (hζσ := hζσ) (g := g) (hg := hg))

theorem exists_markedWeyl_standard_conventional (hp5 : 5 ≤ p) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    ∃ hnN : ∀ j : Fin Tag.F4.rank, nNative (K := K) (σ := σ) (f4FoldedIndex j) ∈
        Subgroup.normalizer
          ((stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)).range : Set _),
      ∃ eW : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer
          (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (stdFrame (K := K) (σ := σ) (p := p) (hp := hp) (hζ := hζ) (hζσ := hζσ)).range),
        ∀ j : Fin Tag.F4.rank, (eW (CoxeterMatrix.F₄.simple j) : MulAut _) =
          ggConjAut _ (hnN j) := by
  obtain ⟨hnN, -, e, he⟩ := exists_markedWeyl_standard (K := K) (σ := σ)
    (hp := hp) (hp5 := hp5) (hζo := hζo) (hζ := hζ) (hζσ := hζσ)
  refine ⟨fun j => hnN (f4FoldedIndex j), ?_⟩
  refine ⟨ggF4Row_coxeterGroupEquiv.trans (revWeyl.trans e), ?_⟩
  intro j
  change (e (revWeyl (ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple j))) : MulAut _) =
    ggConjAut _ (hnN (f4FoldedIndex j))
  rw [ggF4Row_coxeterGroupEquiv_simple]
  rw [revWeyl_simple]
  rw [show f4RevTag j = f4FoldedIndex j from f4RevTag_eq_f4FoldedIndex j]
  exact he (f4FoldedIndex j)

end CFSG.StandardType.E6RelativeWeyl
