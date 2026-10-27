module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB3Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart29
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.GGRankOneTorus
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.StandardType.F4ExplicitPos.Sp3Selected

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.LieEmbed CFSG.SeitzReduction.F4Pilot CFSG.StandardType.SelectedRoot
  CFSG.StandardType.RankOneXfer CFSG.StandardType.PsiDiag CFSG.StandardType.PsiDiagChar
  CFSG.StandardType.F4ExplicitPos.RationalC3 CFSG.StandardType.F4ExplicitPos.RationalB3

theorem exists_sp_model {F : Type} [Field F] {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    ∃ model : SelectedSL2Model (Symplectic.rootDatum m F) F (Pi.single i 1),
      (∀ c, model.phi (sl2Upper c) = Sp.x m F (Pi.single i 1) c) ∧
        (∀ c, model.phi (sl2Lower c) = Sp.x m F (-Pi.single i 1) c) ∧
        model.phi.range = (Symplectic.rootDatum m F).rootGroup (Pi.single i 1 : Fin m → ℤ) ⊔
          (Symplectic.rootDatum m F).rootGroup (-Pi.single i 1 : Fin m → ℤ) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Symplectic.rootDatum m F).isFiniteType
    (Dv := (Symplectic.rootDatum m F).divisible) rfl
  have hE := Sp.chevalleyExtras hm O _ (Sp.commutatorFormula O)
  obtain ⟨phi, hinj, hU, hL⟩ := Sp.rankOne (n := m) (F := F) i
  have hroot : (Pi.single i 1 : Fin m → ℤ) ∈ (Symplectic.rootDatum m F).roots :=
    single_mem_roots (D := Symplectic.rootDatum m F) i
  have hroot' : (-Pi.single i 1 : Fin m → ℤ) ∈ (Symplectic.rootDatum m F).roots :=
    neg_single_mem_roots (D := Symplectic.rootDatum m F) i
  have hp := Sp.isParametrization (n := m) (F := F) (Pi.single i 1) hroot
  have hp' := Sp.isParametrization (n := m) (F := F) (-Pi.single i 1) hroot'
  have hup : (sl2UpperUniSub F).map phi = (Symplectic.rootDatum m F).rootGroup (Pi.single i 1) := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨c, rfl⟩ := mem_sl2UpperUniSub_iff.mp hA
      rw [hU c]
      exact (hp.1 _).2 ⟨c, rfl⟩
    · intro hg
      obtain ⟨c, rfl⟩ := (hp.1 g).1 hg
      exact ⟨sl2Upper c, mem_sl2UpperUniSub_iff.mpr ⟨c, rfl⟩, hU c⟩
  have hlow : Set.range (fun t : F => phi (sl2Lower t)) =
      ((Symplectic.rootDatum m F).rootGroup (-Pi.single i 1) : Set (StatedSp m F)) := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact (hp'.1 _).2 ⟨c, (hL c).symm⟩
    · intro hg
      obtain ⟨c, rfl⟩ := (hp'.1 g).1 hg
      exact ⟨c, hL c⟩
  have hscalar : ∀ h ∈ ggTorus (Symplectic.rootDatum m F), ∃ c : F, ∀ t : F,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t)) := by
    intro h hh
    obtain ⟨χ, hχ⟩ := PsiDiag.Symp.ggTorus_conj_x _ hroot h hh
    exact ⟨χ, fun t => by rw [hU, hU, hχ]⟩
  have hdiag : ∀ a : Fˣ, phi (sl2Diag a) ∈ ggTorus (Symplectic.rootDatum m F) :=
    fun a => map_sl2Diag_mem_ggTorus hE i phi hU hL a
  exact ⟨SelectedSL2Model.ofRootMap _ _ hroot phi hinj hup hdiag hscalar, hU, hL,
    SelectedSL2Model.ofRootMap_range _ _ hroot phi hinj hup hdiag hscalar hlow⟩

theorem exponent_c3ToF4_single (i : Fin 3) :
    F4.exponent (pinnedData .F4 (c3ToF4 (Pi.single i 1))).1 = if i = 2 then 1 else 2 := by
  rw [c3ToF4_single, pinnedData_single]
  fin_cases i <;> decide

theorem exponent_c3ToF4_neg_single (i : Fin 3) :
    F4.exponent (pinnedData .F4 (c3ToF4 (-Pi.single i 1))).1 = if i = 2 then 1 else 2 := by
  rw [map_neg, c3ToF4_single, pinnedData_neg_single]
  fin_cases i <;> decide

theorem dualRoot_c3ToF4_single (i : Fin 3) :
    F4.dualRoot (c3ToF4 (Pi.single i 1)) = (Pi.single (Fin.castSucc i) 1 : Fin (Tag.rank .F4) → ℤ) := by
  funext j
  fin_cases i <;> fin_cases j <;> decide

theorem dualRoot_c3ToF4_neg_single (i : Fin 3) :
    F4.dualRoot (c3ToF4 (-Pi.single i 1)) =
      (-Pi.single (Fin.castSucc i) 1 : Fin (Tag.rank .F4) → ℤ) := by
  funext j
  fin_cases i <;> fin_cases j <;> decide

variable {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem finitePinnedRoot_eq_F4 {K : Type} [Field K] [Algebra K Ω] (γ : Fin 3 → ℤ) :
    finitePinnedRoot (K := K) Ω γ = finitePinnedRootF4 (K := K) Ω (c3ToF4 γ) := by
  simp only [finitePinnedRoot, finitePinnedRootF4]
  rw [B3Algebraic.pinnedFamilySign_eq_one_charTwo Ω (c3ToF4 γ)]
  simp only [one_mul]

section CanonicalF4

variable {K : Type} [Field K] [Algebra K Ω]

theorem map_rootGroup_jF4 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((f4Datum K).rootGroup γ).map
        ((adjointGroup .F4 Ω).subtype.comp (AmbientAction.jF4 (K := K) (L := Ω))) =
      finitePinnedRootF4 (K := K) Ω γ := by
  have hx (c : K) : ((adjointGroup .F4 Ω).subtype.comp (AmbientAction.jF4 (K := K) (L := Ω)))
      ((rootOperatorFamily .F4).eltElement ⟨γ, hγ⟩ c) = pinnedX .F4 Ω γ (algebraMap K Ω c) := by
    change ((BaseChange.j (τ := .F4) (algebraMap K Ω)
      ((rootOperatorFamily .F4).eltElement ⟨γ, hγ⟩ c) : adjointGroup .F4 Ω) : ModGL .F4 Ω) = _
    rw [RootBaseChange.j_eltElement, RootOperatorFamily.coe_eltElement,
      (rootOperatorFamily .F4).pinnedX_eq_eltUnit Ω hγ,
      B3Algebraic.pinnedFamilySign_eq_one_charTwo Ω γ, one_mul]
  have hset : ((adjointGroup .F4 Ω).subtype.comp (AmbientAction.jF4 (K := K) (L := Ω))) ''
      ((f4Datum K).rootGroup γ : Set (adjointGroup .F4 K)) =
      Set.range (fun c : K => pinnedX .F4 Ω γ (algebraMap K Ω c)) := by
    rw [RootBaseChange.f4Datum_rootGroup_eq K γ, RootBaseChange.rootGroup_of_isRoot_no117 hγ]
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨c, rfl⟩ := (rootOperatorFamily .F4).mem_rootSubgroup.1 hu
      exact ⟨c, (hx c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, (rootOperatorFamily .F4).eltElement_mem_rootSubgroup _ c, hx c⟩
  rw [finitePinnedRootF4, ← hset, ← Subgroup.coe_map, Subgroup.closure_eq]

theorem map_rankOne_jF4 (k : Fin (Tag.rank .F4)) :
    (CFSG.LieType.CurtisTits.rankOne (f4Datum K).rootGroup k).map
        ((adjointGroup .F4 Ω).subtype.comp (AmbientAction.jF4 (K := K) (L := Ω))) =
      finitePinnedRootF4 (K := K) Ω (Pi.single k 1) ⊔
        finitePinnedRootF4 (K := K) Ω (-Pi.single k 1) := by
  change (((f4Datum K).rootGroup (Pi.single k 1 : Fin (Tag.rank .F4) → ℤ) ⊔
    (f4Datum K).rootGroup (-Pi.single k 1 : Fin (Tag.rank .F4) → ℤ)).map _) = _
  rw [Subgroup.map_sup, map_rootGroup_jF4 (isRoot_single .F4 k),
    map_rootGroup_jF4 (isRoot_neg_single .F4 k)]

theorem map_rankOne_jF4_le_range_conjIM (i : Fin 3) :
    (CFSG.LieType.CurtisTits.rankOne (f4Datum K).rootGroup (c3Node i)).map
        ((adjointGroup .F4 Ω).subtype.comp (AmbientAction.jF4 (K := K) (L := Ω))) ≤
      (conjIM Ω 1).range := by
  have hgen : ∀ γ : Fin 3 → ℤ, γ ∈ roots (isFiniteType_cartanC 3) ∅ →
      finitePinnedRootF4 (K := K) Ω (c3ToF4 γ) ≤ (conjIM Ω 1).range := by
    intro γ hγ
    rw [finitePinnedRootF4, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    refine ⟨Sp.x 3 Ω γ (algebraMap K Ω c), ?_⟩
    rw [conjIM_x_pinned (Ω := Ω) (n := 1) (hγ := hγ),
      B3Algebraic.pinnedFamilySign_eq_one_charTwo Ω (c3ToF4 γ), one_mul, one_mul, inv_one,
      mul_one]
  have hδ : (Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    single_mem_roots (D := Symplectic.rootDatum 3 K) i
  have hδ' : (-Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    neg_single_mem_roots (D := Symplectic.rootDatum 3 K) i
  have h1 := hgen _ hδ
  have h2 := hgen _ hδ'
  rw [c3ToF4_single] at h1
  rw [map_neg, c3ToF4_single] at h2
  rw [map_rankOne_jF4]
  exact sup_le h1 h2

theorem map_rankOne_jF4_le_range_conjBM (i : Fin 3) :
    (CFSG.LieType.CurtisTits.rankOne (f4Datum K).rootGroup (Fin.castSucc i)).map
        ((adjointGroup .F4 Ω).subtype.comp (AmbientAction.jF4 (K := K) (L := Ω))) ≤
      (conjBM Ω 1).range := by
  have hgen : ∀ γ : Fin 3 → ℤ, γ ∈ roots (isFiniteType_cartanC 3) ∅ →
      finitePinnedRootF4 (K := K) Ω (F4.dualRoot (c3ToF4 γ)) ≤ (conjBM Ω 1).range := by
    intro γ hγ
    unfold finitePinnedRootF4
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rcases B3Exact.Narrow.exponent_F4_eq_one_or_two (pinnedData .F4 (c3ToF4 γ)).1 with he | he
    · refine ⟨Sp.x 3 Ω γ (algebraMap K Ω c), ?_⟩
      rw [conjBM_x_pinned (Ω := Ω) (n := 1) (hγ := hγ), he, pow_one, one_mul, inv_one, mul_one]
    · obtain ⟨d, hd⟩ := B3Algebraic.exists_sq_eq_charTwo_algebraic Ω (algebraMap K Ω c)
      refine ⟨Sp.x 3 Ω γ d, ?_⟩
      rw [conjBM_x_pinned (Ω := Ω) (n := 1) (hγ := hγ), he, hd, one_mul, inv_one, mul_one]
  have hδ : (Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    single_mem_roots (D := Symplectic.rootDatum 3 K) i
  have hδ' : (-Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    neg_single_mem_roots (D := Symplectic.rootDatum 3 K) i
  have h1 := hgen _ hδ
  have h2 := hgen _ hδ'
  rw [dualRoot_c3ToF4_single] at h1
  rw [dualRoot_c3ToF4_neg_single] at h2
  exact (map_rankOne_jF4 (Fin.castSucc i)).trans_le (sup_le h1 h2)

end CanonicalF4

variable {f : ℕ} [Algebra (GaloisField 2 f) Ω] {G : Type} [Group G] (η : G →* ModGL .F4 Ω)
  (lam : ↥(StatedSp 3 (GaloisField 2 f)) →* G) (n z : ModGL .F4 Ω)

theorem exists_sp3Model_image_c3
    (hcomp : η.comp lam = ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
      (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3)) (i : Fin 3) :
    ∃ model' : SelectedSL2Model (ggU .PSp 3 f).D (GaloisField 2 f) (Pi.single i 1),
      (∀ t, η (lam (model'.phi (sl2Upper t))) = z * n *
        pinnedX .F4 Ω (c3ToF4 (Pi.single i 1)) (algebraMap (GaloisField 2 f) Ω t) * n⁻¹ * z⁻¹) ∧
      (∀ t, η (lam (model'.phi (sl2Lower t))) = z * n *
        pinnedX .F4 Ω (c3ToF4 (-Pi.single i 1)) (algebraMap (GaloisField 2 f) Ω t) * n⁻¹ * z⁻¹) ∧
      (lam.comp model'.phi).range.map η =
        (finitePinnedRootF4 (K := GaloisField 2 f) Ω (c3ToF4 (Pi.single i 1)) ⊔
          finitePinnedRootF4 (K := GaloisField 2 f) Ω (c3ToF4 (-Pi.single i 1))).map
            (MulAut.conj (z * n)).toMonoidHom := by
  obtain ⟨model', hU, hL, hR⟩ := exists_sp_model (F := GaloisField 2 f) (m := 3) (by norm_num) i
  have hδ : (Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    single_mem_roots (D := Symplectic.rootDatum 3 (GaloisField 2 f)) i
  have hδ' : (-Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    neg_single_mem_roots (D := Symplectic.rootDatum 3 (GaloisField 2 f)) i
  have hup : ∀ t, η (lam (model'.phi (sl2Upper t))) = z * n *
      pinnedX .F4 Ω (c3ToF4 (Pi.single i 1)) (algebraMap (GaloisField 2 f) Ω t) * n⁻¹ * z⁻¹ := by
    intro t
    change (η.comp lam) (model'.phi (sl2Upper t)) = _
    rw [hcomp, hU, Phi_x_pinned (Ω := Ω) (n := n) (z := z) (hγ := hδ),
      B3Algebraic.pinnedFamilySign_eq_one_charTwo Ω (c3ToF4 _), one_mul]
  have hlow : ∀ t, η (lam (model'.phi (sl2Lower t))) = z * n *
      pinnedX .F4 Ω (c3ToF4 (-Pi.single i 1)) (algebraMap (GaloisField 2 f) Ω t) * n⁻¹ * z⁻¹ := by
    intro t
    change (η.comp lam) (model'.phi (sl2Lower t)) = _
    rw [hcomp, hL, Phi_x_pinned (Ω := Ω) (n := n) (z := z) (hγ := hδ'),
      B3Algebraic.pinnedFamilySign_eq_one_charTwo Ω (c3ToF4 _), one_mul]
  have hrange : (lam.comp model'.phi).range.map η =
      (finitePinnedRootF4 (K := GaloisField 2 f) Ω (c3ToF4 (Pi.single i 1)) ⊔
        finitePinnedRootF4 (K := GaloisField 2 f) Ω (c3ToF4 (-Pi.single i 1))).map
          (MulAut.conj (z * n)).toMonoidHom := by
    rw [MonoidHom.range_comp, Subgroup.map_map, hcomp, hR, Subgroup.map_sup,
      ← C3Range.c3RootSubgroup_eq_rootGroup (K := GaloisField 2 f) hδ,
      ← C3Range.c3RootSubgroup_eq_rootGroup (K := GaloisField 2 f) hδ',
      map_Phi_c3RootSubgroup (Ω := Ω) n z hδ, map_Phi_c3RootSubgroup (Ω := Ω) n z hδ',
      finitePinnedRoot_eq_F4, finitePinnedRoot_eq_F4, Subgroup.map_sup]
  exact ⟨model', hup, hlow, hrange⟩

theorem exists_sp3Model_image_b3 (hcomp : η.comp lam = PhiB (K := GaloisField 2 f) Ω n z)
    (i : Fin 3) :
    ∃ model' : SelectedSL2Model (ggU .PSp 3 f).D (GaloisField 2 f) (Pi.single i 1),
      (∀ t, η (lam (model'.phi (sl2Upper t))) = z * n *
        pinnedX .F4 Ω (F4.dualRoot (c3ToF4 (Pi.single i 1)))
          (algebraMap (GaloisField 2 f) Ω t ^ (if i = 2 then 1 else 2)) * n⁻¹ * z⁻¹) ∧
      (∀ t, η (lam (model'.phi (sl2Lower t))) = z * n *
        pinnedX .F4 Ω (F4.dualRoot (c3ToF4 (-Pi.single i 1)))
          (algebraMap (GaloisField 2 f) Ω t ^ (if i = 2 then 1 else 2)) * n⁻¹ * z⁻¹) ∧
      (lam.comp model'.phi).range.map η =
        (finitePinnedRootF4 (K := GaloisField 2 f) Ω (F4.dualRoot (c3ToF4 (Pi.single i 1))) ⊔
          finitePinnedRootF4 (K := GaloisField 2 f) Ω (F4.dualRoot (c3ToF4 (-Pi.single i 1)))).map
            (MulAut.conj (z * n)).toMonoidHom := by
  obtain ⟨model', hU, hL, hR⟩ := exists_sp_model (F := GaloisField 2 f) (m := 3) (by norm_num) i
  have hδ : (Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    single_mem_roots (D := Symplectic.rootDatum 3 (GaloisField 2 f)) i
  have hδ' : (-Pi.single i 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    neg_single_mem_roots (D := Symplectic.rootDatum 3 (GaloisField 2 f)) i
  have hup : ∀ t, η (lam (model'.phi (sl2Upper t))) = z * n *
      pinnedX .F4 Ω (F4.dualRoot (c3ToF4 (Pi.single i 1)))
        (algebraMap (GaloisField 2 f) Ω t ^ (if i = 2 then 1 else 2)) * n⁻¹ * z⁻¹ := by
    intro t
    change (η.comp lam) (model'.phi (sl2Upper t)) = _
    rw [hcomp, hU, PhiB_x_pinned (Ω := Ω) (n := n) (z := z) (hγ := hδ), exponent_c3ToF4_single]
  have hlow : ∀ t, η (lam (model'.phi (sl2Lower t))) = z * n *
      pinnedX .F4 Ω (F4.dualRoot (c3ToF4 (-Pi.single i 1)))
        (algebraMap (GaloisField 2 f) Ω t ^ (if i = 2 then 1 else 2)) * n⁻¹ * z⁻¹ := by
    intro t
    change (η.comp lam) (model'.phi (sl2Lower t)) = _
    rw [hcomp, hL, PhiB_x_pinned (Ω := Ω) (n := n) (z := z) (hγ := hδ'),
      exponent_c3ToF4_neg_single]
  have hrange : (lam.comp model'.phi).range.map η =
      (finitePinnedRootF4 (K := GaloisField 2 f) Ω (F4.dualRoot (c3ToF4 (Pi.single i 1))) ⊔
        finitePinnedRootF4 (K := GaloisField 2 f) Ω (F4.dualRoot (c3ToF4 (-Pi.single i 1)))).map
          (MulAut.conj (z * n)).toMonoidHom := by
    rw [MonoidHom.range_comp, Subgroup.map_map, hcomp, hR, Subgroup.map_sup,
      ← C3Range.c3RootSubgroup_eq_rootGroup (K := GaloisField 2 f) hδ,
      ← C3Range.c3RootSubgroup_eq_rootGroup (K := GaloisField 2 f) hδ',
      map_PhiB_c3RootSubgroup Ω n z hδ, map_PhiB_c3RootSubgroup Ω n z hδ', Subgroup.map_sup]
  exact ⟨model', hup, hlow, hrange⟩

theorem exists_sp3Model_rankOne_c3
    (hcomp : η.comp lam = ((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
      (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3)) (i : Fin 3) :
    ∃ model' : SelectedSL2Model (ggU .PSp 3 f).D (GaloisField 2 f) (Pi.single i 1),
      (lam.comp model'.phi).range.map η =
        ((CFSG.LieType.CurtisTits.rankOne (f4Datum (GaloisField 2 f)).rootGroup (c3Node i)).map
          ((adjointGroup .F4 Ω).subtype.comp
            (AmbientAction.jF4 (K := GaloisField 2 f) (L := Ω)))).map
          (MulAut.conj (z * n)).toMonoidHom := by
  obtain ⟨model', -, -, hrange⟩ := exists_sp3Model_image_c3 η lam n z hcomp i
  refine ⟨model', hrange.trans ?_⟩
  rw [c3ToF4_single, map_neg, c3ToF4_single]
  exact congrArg (fun H => H.map (MulAut.conj (z * n)).toMonoidHom)
    (map_rankOne_jF4 (K := GaloisField 2 f) (c3Node i)).symm

theorem exists_sp3Model_rankOne_b3 (hcomp : η.comp lam = PhiB (K := GaloisField 2 f) Ω n z)
    (i : Fin 3) :
    ∃ model' : SelectedSL2Model (ggU .PSp 3 f).D (GaloisField 2 f) (Pi.single i 1),
      (lam.comp model'.phi).range.map η =
        ((CFSG.LieType.CurtisTits.rankOne (f4Datum (GaloisField 2 f)).rootGroup
            (Fin.castSucc i)).map
          ((adjointGroup .F4 Ω).subtype.comp
            (AmbientAction.jF4 (K := GaloisField 2 f) (L := Ω)))).map
          (MulAut.conj (z * n)).toMonoidHom := by
  obtain ⟨model', -, -, hrange⟩ := exists_sp3Model_image_b3 η lam n z hcomp i
  refine ⟨model', hrange.trans ?_⟩
  rw [dualRoot_c3ToF4_single, dualRoot_c3ToF4_neg_single]
  exact congrArg (fun H => H.map (MulAut.conj (z * n)).toMonoidHom)
    (map_rankOne_jF4 (K := GaloisField 2 f) (Fin.castSucc i)).symm

end CFSG.StandardType.F4ExplicitPos.Sp3Selected

end
