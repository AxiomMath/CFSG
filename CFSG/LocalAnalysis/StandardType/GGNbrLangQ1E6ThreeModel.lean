module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagE6
public import CFSG.LocalAnalysis.StandardType.GGStdPosE6ThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UStd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldFixed
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.StandardType.Q1E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem rootDiagAutHom_apply_coe
    {K : Type} [Field K]
    (a : Fin Tag.E6.rank → Kˣ) (x : adjointGroup .E6 K) :
    ((rootDiagAutHom .E6 K a x : adjointGroup .E6 K) : ModGL .E6 K) =
      rootDiagUnit Tag.E6 a * (x : ModGL .E6 K) * (rootDiagUnit Tag.E6 a)⁻¹ :=
  rfl

theorem componentMarking_congr_equiv {X Y : Type} [Group X] [Group Y] (γ : X ≃* Y)
    {A : Subgroup (MulAut X)} {J : Subgroup X}
    (h : (∀ b ∈ A.map (MulAut.congr γ).toMonoidHom,
          ∀ j ∈ J.map γ.toMonoidHom, b j ∈ J.map γ.toMonoidHom) ∧
      LargeEvenMarking (J.map γ.toMonoidHom)
        (fun _ _ _ I _ θ => GGAutsInduceOn (A.map (MulAut.congr γ).toMonoidHom)
          (J.map γ.toMonoidHom) θ I)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ I _ θ => GGAutsInduceOn A J θ I) := by
  classical
  let eJ : ↥J ≃* ↥(J.map γ.toMonoidHom) := J.equivMapOfInjective γ.toMonoidHom γ.injective
  have hcoe : ∀ j : ↥J, ((eJ j : ↥(J.map γ.toMonoidHom)) : Y) = γ.toMonoidHom (j : X) :=
    fun _ => rfl
  have hcongr : ∀ (a : MulAut X) (x : X),
      (MulAut.congr γ a) (γ.toMonoidHom x) = γ.toMonoidHom (a x) := by
    intro a x
    simp [MulAut.congr_apply]
  have hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := by
    intro a ha j hj
    have hb : MulAut.congr γ a ∈ A.map (MulAut.congr γ).toMonoidHom := ⟨a, ha, rfl⟩
    have hj' : ((eJ ⟨j, hj⟩ : ↥(J.map γ.toMonoidHom)) : Y) ∈ J.map γ.toMonoidHom :=
      (eJ ⟨j, hj⟩).2
    have hmem := h.1 (MulAut.congr γ a) hb
      ((eJ ⟨j, hj⟩ : ↥(J.map γ.toMonoidHom)) : Y) hj'
    have heq : ((MulAut.congr γ a) ((eJ ⟨j, hj⟩ : ↥(J.map γ.toMonoidHom)) : Y)) =
        γ.toMonoidHom (a j) := by
      rw [hcoe ⟨j, hj⟩]
      exact hcongr a j
    obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp hmem
    have hxa : x = a j := by
      apply γ.injective
      change γ.toMonoidHom x = γ.toMonoidHom (a j)
      rw [hxeq, heq]
    exact hxa ▸ hxJ
  have hmark : LargeEvenMarking J (fun _ _ _ I _ θ => GGAutsInduceOn A J θ I) := by
    refine largeEvenMarking_congr eJ ?_ h.2
    intro lab R instR I F θ' hθ' a ha
    obtain ⟨φ, hφ, hind⟩ := hθ' (MulAut.congr γ a) ⟨a, ha, rfl⟩
    refine ⟨φ, hφ, ?_⟩
    have hrel : ∀ j j' : ↥J,
        (a (j : X) = (j' : X)) ↔
          (MulAut.congr γ a) ((eJ j : ↥(J.map γ.toMonoidHom)) : Y) =
            ((eJ j' : ↥(J.map γ.toMonoidHom)) : Y) := by
      intro j j'
      constructor
      · intro hjj
        rw [hcoe j, hcoe j', hcongr a (j : X), hjj]
      · intro hjj
        have h' : γ.toMonoidHom (a (j : X)) = γ.toMonoidHom (j' : X) := by
          rw [← hcongr a (j : X), ← hcoe j, ← hcoe j']
          exact hjj
        exact γ.injective h'
    exact (largeEvenInduces_congr_equiv eJ θ'
      (fun j j' : ↥J => a (j : X) = (j' : X))
      (fun j' j'' : ↥(J.map γ.toMonoidHom) =>
        (MulAut.congr γ a) (j' : Y) = (j'' : Y))
      hrel φ).2 hind
  exact ⟨hnorm, hmark⟩

section Certificates


private theorem q1E6ThreeModel_diag
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {A : Subgroup (MulAut (adjointGroup .E6 K))}
    (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAD : A ≤ (rootDiagAutHom .E6 K).range)
    {u : MulAut (adjointGroup .E6 K)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
  classical
  obtain ⟨a_u, hua⟩ := MonoidHom.mem_range.mp (hAD hu)
  subst u
  have ha_u3 : a_u ^ 3 = 1 := by
    apply rootDiagAutHom_injective
    rw [map_pow, hA.2 _ hu, map_one]
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  let : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  let n : ℕ := f
  have hK : Nat.card K = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, hKf]
  have hperf : commutator ↥(adjointGroup .E6 K) = ⊤ :=
    CFSG.LieType.Chevalley.single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨S, -, hSΓ, hSmodel⟩ := TableCRes.exists_stdSetup_E6 hK hperf
  let umap : (Fin Tag.E6.rank → Kˣ) →* (Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) :=
    MonoidHom.pi fun i =>
      (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom).comp
        (Pi.evalMonoidHom (fun _ : Fin Tag.E6.rank => Kˣ) i)
  have hT : ∀ a : Fin Tag.E6.rank → Kˣ, rootDiagUnit Tag.E6 (umap a) ∈ S.D.torus := by
    intro a
    have hdiagT : rootDiagUnit Tag.E6 (umap a) ∈ torusGroup Tag.E6 L :=
      rootDiagUnit_mem_torusGroup _
    have hdiagM : rootDiagUnit Tag.E6 (umap a) ∈ S.D.model := by
      change rootDiagUnit Tag.E6 (fun i =>
        Units.map (algebraMap K L).toMonoidHom (a i)) ∈ S.D.model
      rw [← baseChangeGL_rootDiagUnit (τ := Tag.E6) ι a]
      exact hSmodel _ (by
        rw [baseChangeGL_rootDiagUnit]
        exact (exceptional_Lang_adjoint_diagonal_lift Tag.E6 L _).1)
    exact CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mpr
      ⟨hdiagT, (LangDatum.mem_model S.D).mp hdiagM |>.2⟩
  let aL : Fin Tag.E6.rank → Lˣ := umap a_u
  have hbc_d : baseChangeGL (τ := Tag.E6) ι (rootDiagUnit Tag.E6 a_u) =
      rootDiagUnit Tag.E6 aL := baseChangeGL_rootDiagUnit (τ := Tag.E6) ι a_u
  have hd : rootDiagUnit Tag.E6 aL ∈ S.D.torus := hT a_u
  have hd3 : ∀ j, aL j ^ 3 = 1 := by
    have h : aL ^ 3 = 1 := by rw [← map_pow, ha_u3, map_one]
    intro j
    simpa using congrFun h j
  have hd1 : rootDiagUnit Tag.E6 aL ≠ 1 := by
    intro h
    have h1 : baseChangeGL (τ := Tag.E6) ι (rootDiagUnit Tag.E6 a_u) = 1 := by
      rw [hbc_d, h]
    have h2 : rootDiagUnit Tag.E6 a_u = 1 := by
      apply baseChangeGL_injective (τ := Tag.E6) (f := ι)
      simpa using h1
    have h3 : a_u = 1 := by
      apply rootDiagUnit_injective (τ := Tag.E6)
      rw [rootDiagUnit_one]
      exact h2
    apply hu1
    rw [h3, map_one]
  let E : Subgroup (Fin Tag.E6.rank → Kˣ) := A.comap (rootDiagAutHom .E6 K)
  have hE_map : E.map (rootDiagAutHom .E6 K) = A :=
    Subgroup.map_comap_eq_self hAD
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    apply rootDiagAutHom_injective
    rw [map_pow, hA.2 _ (Subgroup.mem_comap.mp he), map_one]
  let E_L : Subgroup (ModGL .E6 L) := E.map ((rootDiagUnitHom .E6 L).comp umap)
  have hEL : E_L ≤ S.D.torus := by
    intro e he
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp he
    exact hT a
  have hEL3 : ∀ e ∈ E_L, e ^ 3 = 1 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp he
    change (rootDiagUnit Tag.E6 (umap a)) ^ 3 = 1
    have ha3 : (umap a) ^ 3 = 1 := by
      rw [← map_pow, hE3 a ha, map_one]
    rw [rootDiagUnit_pow, ha3, rootDiagUnit_one]
  let ιR : adjointGroup .E6 K →* ModGL .E6 L :=
    (baseChangeGL (τ := Tag.E6) ι).comp (adjointGroup .E6 K).subtype
  have hιRinj : Function.Injective ιR :=
    (baseChangeGL_injective (τ := Tag.E6) (f := ι)).comp Subtype.val_injective
  let K_L : Subgroup (ModGL .E6 L) := J.map ιR
  have hfixmap : (ggAutFixedSubgroup (rootDiagAutHom .E6 K a_u)).map ιR =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 aL} := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hSΓ]
        exact Subgroup.mem_map_of_mem _ u.2
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have hm : rootDiagUnit Tag.E6 a_u * (u : ModGL .E6 K) *
            (rootDiagUnit Tag.E6 a_u)⁻¹ = (u : ModGL .E6 K) := by
          simpa only [rootDiagAutHom_apply_coe] using congrArg Subtype.val hu
        have h2 : rootDiagUnit Tag.E6 a_u * (u : ModGL .E6 K) =
            (u : ModGL .E6 K) * rootDiagUnit Tag.E6 a_u := by
          have h3 := congrArg (fun z : ModGL .E6 K => z * rootDiagUnit Tag.E6 a_u) hm
          simpa [mul_assoc] using h3
        rw [← hbc_d]
        change baseChangeGL (τ := Tag.E6) ι ((u : adjointGroup .E6 K) : ModGL .E6 K) *
            baseChangeGL (τ := Tag.E6) ι (rootDiagUnit Tag.E6 a_u) =
          baseChangeGL (τ := Tag.E6) ι (rootDiagUnit Tag.E6 a_u) *
            baseChangeGL (τ := Tag.E6) ι ((u : adjointGroup .E6 K) : ModGL .E6 K)
        simpa only [map_mul] using congrArg (baseChangeGL (τ := Tag.E6) ι) h2.symm
    · rintro ⟨hyΓ, hyC⟩
      rw [hSΓ] at hyΓ
      obtain ⟨u, huR, rfl⟩ := Subgroup.mem_map.mp hyΓ
      refine ⟨⟨u, huR⟩, ?_, rfl⟩
      have hcomm : (u : ModGL .E6 K) * rootDiagUnit Tag.E6 a_u =
          rootDiagUnit Tag.E6 a_u * (u : ModGL .E6 K) := by
        have hc := Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [← hbc_d] at hc
        apply baseChangeGL_injective (τ := Tag.E6) (f := ι)
        rw [map_mul, map_mul]
        exact hc
      apply Subtype.ext
      rw [rootDiagAutHom_apply_coe]
      rw [← hcomm]
      group
  have hKopen : CFSG.Open.IsComponentOf K_L
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 aL}) := by
    have hJopen : CFSG.Open.IsComponentOf J
        (ggAutFixedSubgroup (rootDiagAutHom .E6 K a_u)) :=
      CFSG.Assembly.isComponentOf_iff_open.mp hJ
    have hmap := CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_map_of_injective
      ιR hιRinj hJopen
    rwa [hfixmap] at hmap
  have hGE : GGInnerDiagOn E_L K_L :=
    langTorus_innerDiagOn_subgroup_E6_three S hd hd3 hd1 hEL hEL3 hKopen
  have hGE' : LargeEvenMarking K_L (fun lab R _ I F θK =>
      E_L ≤ Subgroup.normalizer (K_L : Set (ModGL .E6 L)) ∧
      ∀ b ∈ E_L, ∃ φ ∈ I, LargeEvenInduces θK (fun l l' : ↥K_L =>
        (l' : ModGL .E6 L) = b⁻¹ * (l : ModGL .E6 L) * b) φ) := hGE
  have preimage : ∀ a ∈ A, ∃ a' : Fin Tag.E6.rank → Kˣ, a' ∈ E ∧
      rootDiagAutHom .E6 K a' = a := by
    intro a ha
    have ha_map : a ∈ E.map (rootDiagAutHom .E6 K) := by rwa [hE_map]
    obtain ⟨a', ha'E, ha'e⟩ := Subgroup.mem_map.mp ha_map
    exact ⟨a', ha'E, ha'e⟩
  have hinter : ∀ (a' : Fin Tag.E6.rank → Kˣ) (x : adjointGroup .E6 K),
      ιR (rootDiagAutHom .E6 K a' x) =
        rootDiagUnit Tag.E6 (umap a') * ιR x * (rootDiagUnit Tag.E6 (umap a'))⁻¹ := by
    intro a' x
    change baseChangeGL (τ := Tag.E6) ι
        (((rootDiagAutHom .E6 K a' x : adjointGroup .E6 K) : ModGL .E6 K)) =
      rootDiagUnit Tag.E6 (umap a') * baseChangeGL (τ := Tag.E6) ι (x : ModGL .E6 K) *
        (rootDiagUnit Tag.E6 (umap a'))⁻¹
    rw [rootDiagAutHom_apply_coe]
    change baseChangeGL (τ := Tag.E6) ι
        (rootDiagUnit Tag.E6 a' * (x : ModGL .E6 K) * (rootDiagUnit Tag.E6 a')⁻¹) =
      rootDiagUnit Tag.E6 (fun i => Units.map (algebraMap K L).toMonoidHom (a' i)) *
        baseChangeGL (τ := Tag.E6) ι (x : ModGL .E6 K) *
        (rootDiagUnit Tag.E6 (fun i =>
          Units.map (algebraMap K L).toMonoidHom (a' i)))⁻¹
    rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit]
  let eJK : ↥J ≃* ↥K_L := J.equivMapOfInjective ιR hιRinj
  have hcoeJK : ∀ j : ↥J, ((eJK j : ↥K_L) : ModGL .E6 L) =
      ιR (j : adjointGroup .E6 K) := fun _ => rfl
  have hmarkJ : LargeEvenMarking J (fun lab R _ I F θ =>
      GGAutsInduceOn A J θ I) := by
    refine largeEvenMarking_congr eJK ?_ hGE'
    intro lab R instR I F θK hP a ha
    obtain ⟨a', ha'E, ha'e⟩ := preimage a ha
    let aL' : Fin Tag.E6.rank → Lˣ := umap a'
    have hmemL : (rootDiagUnit Tag.E6 aL')⁻¹ ∈ E_L := by
      refine Subgroup.inv_mem _ ?_
      exact Subgroup.mem_map.mpr ⟨a', ha'E, rfl⟩
    obtain ⟨φ, hφ, hind⟩ := hP.2 _ hmemL
    refine ⟨φ, hφ, ?_⟩
    have hrel : ∀ j j' : ↥J,
        (a (j : adjointGroup .E6 K) = (j' : adjointGroup .E6 K)) ↔
          (((eJK j' : ↥K_L) : ModGL .E6 L) =
            rootDiagUnit Tag.E6 aL' * ((eJK j : ↥K_L) : ModGL .E6 L) *
              (rootDiagUnit Tag.E6 aL')⁻¹) := by
      intro j j'
      rw [hcoeJK j', hcoeJK j]
      change a (j : adjointGroup .E6 K) = (j' : adjointGroup .E6 K) ↔
        ιR (j' : adjointGroup .E6 K) =
          rootDiagUnit Tag.E6 (umap a') * ιR (j : adjointGroup .E6 K) *
            (rootDiagUnit Tag.E6 (umap a'))⁻¹
      rw [← hinter a' (j : adjointGroup .E6 K), ha'e]
      exact ⟨fun h => congrArg ιR h.symm, fun h => hιRinj h.symm⟩
    have hind' : LargeEvenInduces θK
        (fun l l' : ↥K_L => (l' : ModGL .E6 L) =
          rootDiagUnit Tag.E6 aL' * (l : ModGL .E6 L) *
            (rootDiagUnit Tag.E6 aL')⁻¹) φ := by
      simpa only [inv_inv] using hind
    exact (largeEvenInduces_congr_equiv eJK θK
      (fun j j' : ↥J => a (j : adjointGroup .E6 K) = (j' : adjointGroup .E6 K))
      (fun l l' : ↥K_L => (l' : ModGL .E6 L) =
        rootDiagUnit Tag.E6 aL' * (l : ModGL .E6 L) * (rootDiagUnit Tag.E6 aL')⁻¹)
      hrel φ).2 hind'
  have hnormJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := by
    intro a ha j hj
    obtain ⟨a', ha'E, ha'e⟩ := preimage a ha
    let aL' : Fin Tag.E6.rank → Lˣ := umap a'
    have hmemL : rootDiagUnit Tag.E6 aL' ∈ E_L :=
      Subgroup.mem_map.mpr ⟨a', ha'E, rfl⟩
    have hnormK : E_L ≤ Subgroup.normalizer (K_L : Set (ModGL .E6 L)) :=
      CFSG.StandardType.GGDichotomy.le_normalizer_of_innerDiagOn hGE
    have hjK : ιR (j : adjointGroup .E6 K) ∈ K_L :=
      Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
    have hmemK : ιR (a (j : adjointGroup .E6 K)) ∈ K_L := by
      rw [← ha'e, hinter a' (j : adjointGroup .E6 K)]
      exact (Subgroup.mem_normalizer_iff.mp (hnormK hmemL)
        (ιR (j : adjointGroup .E6 K))).mp hjK
    change ιR (a (j : adjointGroup .E6 K)) ∈ J.map ιR at hmemK
    obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp hmemK
    exact (hιRinj hxeq) ▸ hxJ
  exact ⟨hnormJ, hmarkJ⟩

theorem q1E6ThreeModel_holds
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1)
    {A : Subgroup (MulAut (adjointGroup .E6 K))}
    (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : A ≤ (hatAut .E6 K).range)
    (h5 : 3 ^ 5 ≤ Nat.card A)
    {u : MulAut (adjointGroup .E6 K)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
  classical
  have hAI' : A ≤ LayerSixE.inndiagAut .E6 K := by
    change A ≤ (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)).range ⊔ (rootDiagAutHom .E6 K).range
    rw [← NoOffE6Three.hatAut_range_eq_sup]
    exact hAI
  obtain ⟨g, hg⟩ := exists_inner_conj_mem_diag_e6 h3 hAI' hA h5
  let γ : MulAut (adjointGroup .E6 K) := MulAut.conj g
  let B : Subgroup (MulAut (adjointGroup .E6 K)) :=
    A.map (MulAut.congr γ).toMonoidHom
  let v : MulAut (adjointGroup .E6 K) := MulAut.congr γ u
  let J' : Subgroup (adjointGroup .E6 K) := J.map γ.toMonoidHom
  have hBD : B ≤ (rootDiagAutHom .E6 K).range := by
    rintro _ ⟨a, ha, rfl⟩
    change MulAut.congr γ a ∈ (rootDiagAutHom .E6 K).range
    have hcongr : MulAut.congr γ a = γ * a * γ⁻¹ := by
      ext x
      simp [MulAut.congr_apply]
    rw [hcongr]
    exact hg a ha
  have hBel : CFSG.Open.IsElemAbelian 3 B := by
    exact CFSG.SectionRank.isElemAbelian_map hA (MulAut.congr γ).toMonoidHom
  have hv : v ∈ B := ⟨u, hu, rfl⟩
  have hv1 : v ≠ 1 := by
    intro h
    have hv1' : (MulAut.congr γ) u = 1 := by simpa [v] using h
    exact hu1 ((MulAut.congr γ).injective (by rw [hv1', map_one]))
  have hJ' : CFSG.Assembly.IsComponentOf J' (ggAutFixedSubgroup v) := by
    have hJopen : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) :=
      CFSG.Assembly.isComponentOf_iff_open.mp hJ
    have hmap := CFSG.isComponentOf_map_mulEquiv γ hJopen
    rw [show (ggAutFixedSubgroup u).map γ.toMonoidHom = ggAutFixedSubgroup v from
      (gdf_fixed_congr γ u).symm] at hmap
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hmap
  have hdiag := q1E6ThreeModel_diag hBel hBD hv hv1 hJ'
  exact componentMarking_congr_equiv γ hdiag

end Certificates

end CFSG.StandardType.Q1E6ThreeModel

end
