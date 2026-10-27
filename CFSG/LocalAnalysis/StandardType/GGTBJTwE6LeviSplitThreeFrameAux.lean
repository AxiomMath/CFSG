module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusE6Relative
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeNormalizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.TwistedE6Cover

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def tw3f_orbitIdx (i : Fin TwistTag.E6.tag.rank) : Fin Tag.F4.rank :=
  ⟨(TwistTag.E6.orbitIndex i).val, (TwistTag.E6.orbitIndex i).isLt⟩

private def tw3f_orbitRep (a : Fin Tag.F4.rank) : Fin TwistTag.E6.tag.rank :=
  if a.val = 0 then ⟨0, by decide⟩ else if a.val = 1 then ⟨2, by decide⟩
    else if a.val = 2 then ⟨3, by decide⟩ else ⟨1, by decide⟩

private theorem tw3f_foldMap_apply_E6 (u : Fin Tag.F4.rank → ℤ)
    (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.foldMap TwistTag.E6 u i = u (tw3f_orbitIdx i) := by
  have h := TwistTag.foldMap_apply_apply TwistTag.E6 u i
  rw [h]
  exact congrArg u (Fin.ext rfl)

private theorem tw3f_twE6SplitTheta_apply {p : ℕ} [NeZero p]
    (s : Fin Tag.F4.rank → ZMod p) (i : Fin TwistTag.E6.tag.rank) :
    ExcFrames.twE6SplitTheta p s i = s (tw3f_orbitIdx i) := by
  show ((TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s) i : ℤ) : ZMod p) =
    s (tw3f_orbitIdx i)
  rw [tw3f_foldMap_apply_E6]
  show (((s (tw3f_orbitIdx i)).val : ℤ) : ZMod p) = s (tw3f_orbitIdx i)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem tw3f_exists_twE6SplitTheta_eq {p : ℕ} [NeZero p]
    {y : Fin TwistTag.E6.tag.rank → ZMod p} (hy : ∀ i, y (TwistTag.E6.perm i) = y i) :
    ∃ s, ExcFrames.twE6SplitTheta p s = y := by
  have key : ∀ i : Fin TwistTag.E6.tag.rank,
      tw3f_orbitRep (tw3f_orbitIdx i) = i ∨
        tw3f_orbitRep (tw3f_orbitIdx i) = TwistTag.E6.perm i := by
    decide
  refine ⟨fun a => y (tw3f_orbitRep a), funext fun i => ?_⟩
  rw [tw3f_twE6SplitTheta_apply]
  rcases key i with h | h
  · exact congrArg y h
  · exact (congrArg y h).trans (hy i)

private def tw3f_f4CartanMul {p : ℕ} (s : Fin Tag.F4.rank → ZMod p) :
    Fin Tag.F4.rank → ZMod p :=
  fun a => ∑ b, ((Tag.F4.cartan a b : ℤ) : ZMod p) * s b

private theorem tw3f_f4CartanMul_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (tw3f_f4CartanMul (p := p)) := by
  have e : tw3f_f4CartanMul (p := p) =
      (Tag.F4.cartan.map (Int.castRingHom (ZMod p))).mulVec := by
    funext s a
    simp [tw3f_f4CartanMul, Matrix.mulVec, dotProduct]
  have hd : (Tag.F4.cartan.map (Int.castRingHom (ZMod p))).det =
      ((Tag.F4.cartan.det : ℤ) : ZMod p) := (RingHom.map_det _ _).symm
  rw [e, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hd,
    CFSG.LieType.Chevalley.det_cartan_F4]
  simpa using (isUnit_one : IsUnit (1 : ZMod p))

private theorem tw3f_f4CartanMul_surjective {p : ℕ} [Fact p.Prime] :
    Function.Surjective (tw3f_f4CartanMul (p := p)) :=
  Finite.injective_iff_surjective.mp (tw3f_f4CartanMul_injective (p := p))

theorem tw3f_exists_frameDiag {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {c : Fin Tag.E6.rank → Kˣ} (hc : ∀ i, c i ^ p = 1)
    (h05 : c ⟨0, by decide⟩ = c ⟨5, by decide⟩)
    (h24 : c ⟨2, by decide⟩ = c ⟨4, by decide⟩) :
    ∃ s : Fin Tag.F4.rank → ZMod p,
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ (ExcFrames.twE6SplitTheta p s) =
        rootDiagUnit Tag.E6 c := by
  have hcp : c ^ p = 1 := funext fun i => hc i
  obtain ⟨x, hx⟩ :=
    TableBExc.E6Three.exists_zetaVec_eq (τ := TwistTag.E6.tag) (p := p) hζo hζ hcp
  have hcsym : ∀ i, c (TwistTag.E6.perm i) = c i := by
    intro i
    fin_cases i
    · exact h05.symm
    · rfl
    · exact h24.symm
    · rfl
    · exact h24
    · exact h05
  have hxsym_fun : (fun i => x (TwistTag.E6.perm i)) = x := by
    apply TableBExc.E6Three.zetaVec_injective (τ := TwistTag.E6.tag) (p := p) hζo hζ
    funext i
    change TableBExc.E6Three.zetaVec ζ hζ x (TwistTag.E6.perm i) =
      TableBExc.E6Three.zetaVec ζ hζ x i
    rw [congrFun hx (TwistTag.E6.perm i), hcsym i, ← congrFun hx i]
  have hxsym : ∀ i, x (TwistTag.E6.perm i) = x i := fun i => congrFun hxsym_fun i
  obtain ⟨x'', hx''⟩ := tw3f_exists_twE6SplitTheta_eq (p := p) hxsym
  obtain ⟨s, hs⟩ := tw3f_f4CartanMul_surjective (p := p) x''
  refine ⟨s, ?_⟩
  rw [ExcFrames.frameDiag, TwE6SplitRootGen.frameCoord_twE6SplitTheta]
  change rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ
    (ExcFrames.twE6SplitTheta p (tw3f_f4CartanMul s))) = rootDiagUnit Tag.E6 c
  rw [hs, hx'']
  exact congrArg (rootDiagUnit Tag.E6) hx

theorem tw3f_frame_eq
    {K : Type} [Field K] (σ : K →+* K) {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hζσ : σ (ζ : K) = ζ) (s : Multiplicative (Fin Tag.F4.rank → ZMod 3)) :
    (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ s : ModGL TwistTag.E6.tag K) =
      ExcFrames.E6QPlusThree.e6ThreeDiag ζ hζ s := by
  rw [show s = Multiplicative.ofAdd (Multiplicative.toAdd s) from rfl]
  rw [ExcFrames.twE6SplitFrameHom_apply, ExcFrames.E6QPlusThree.e6ThreeDiag_apply]
  rfl

theorem tw3f_range_eq
    {K : Type} [Field K] (σ : K →+* K) {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hζσ : σ (ζ : K) = ζ) :
    (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range.map
        (Subgroup.subtype (graphFixedRootGroup TwistTag.E6 K σ)) =
      (ExcFrames.E6QPlusThree.e6ThreeDiag ζ hζ).range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := hy
    exact ⟨Multiplicative.toAdd s,
      (tw3f_frame_eq σ hζ hζσ (Multiplicative.toAdd s)).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s),
      ⟨Multiplicative.ofAdd s, rfl⟩, tw3f_frame_eq σ hζ hζσ s⟩

theorem tw3f_normalizer_action_three
    {K : Type} [Field K] [Finite K] (σ : K →+* K)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (hζσ : σ (ζ : K) = ζ)
    (g : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hg : g ∈ Subgroup.normalizer
      ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range : Set _)) :
    ∃ u : WeylGroup Tag.F4, ∀ s : Fin Tag.F4.rank → ZMod 3,
      g * ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * g⁻¹ =
        ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
          (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 u s)) := by
  classical
  let ι := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
  have hxs : ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ ∈ ι.range := fun s =>
    (Subgroup.mem_normalizer_iff.mp hg _).mp (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hxC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left g.2
  have hxMono : (g : ModGL TwistTag.E6.tag K) ∈ monomialSubgroup Tag.E6 K := by
    refine ExcFrames.E6QPlusThree.mem_monomialSubgroup_of_conj_e6ThreeDiag hζo hζ hxC
      fun s => ?_
    rw [← tw3f_range_eq σ hζ hζσ]
    obtain ⟨t, ht⟩ := hxs s
    refine ⟨ι t, ⟨t, rfl⟩, ?_⟩
    have h1 := congrArg (fun y : ↥(graphFixedRootGroup TwistTag.E6 K σ) =>
      (y : ModGL TwistTag.E6.tag K)) ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ι] at h1
    rw [tw3f_frame_eq σ hζ hζσ (Multiplicative.ofAdd s)] at h1
    exact h1
  have hxM : (g : ModGL TwistTag.E6.tag K) ∈ graphFixedRootMonomial TwistTag.E6 K σ :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxMono,
      graphFixedRootGroup_le TwistTag.E6 K σ g.2⟩, g.2⟩
  refine ⟨foldedWeylEquiv TwistTag.E6
    ⟨graphFixedRootWeylHom TwistTag.E6 K σ ⟨(g : ModGL TwistTag.E6.tag K), hxM⟩,
      (graphFixedRootWeylHom_range TwistTag.E6 K σ).le
        ⟨⟨(g : ModGL TwistTag.E6.tag K), hxM⟩, rfl⟩⟩, fun s => ?_⟩
  have h2 := ExcFrames.twE6SplitFrameHom_conj σ hζ hζσ hxM s
  simpa only [ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2

theorem tw3f_markedWeyl_three
    {K : Type} [Field K] [Finite K] (σ : K →+* K)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (hζσ : σ (ζ : K) = ζ) :
    ∃ hnN : ∀ a : Fin TwistTag.E6.foldedTag.rank,
        E6RelativeWeyl.nNative (K := K) (σ := σ) a ∈ Subgroup.normalizer
          ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range : Set _),
      ggAutomizer (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range =
        Subgroup.closure (Set.range fun a => ggConjAut _ (hnN a)) ∧
      ∃ e : WeylGroup Tag.F4 ≃* ↥(ggAutomizer
          (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range),
        ∀ a, (e (simple Tag.F4 a) : MulAut _) = ggConjAut _ (hnN a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ι := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
  have hodd : Odd 3 := by decide
  exact exists_markedWeyl_ggAutomizer hodd (E := ι.range) (ι := ι)
    (TwE6SplitRootGen.twE6SplitFrameHom_injective_of_orderOf σ hζo hζ hζσ) rfl
    (fun a => E6RelativeWeyl.nNative (K := K) (σ := σ) a)
    (fun a s => by
      simpa only [ι, E6RelativeWeyl.stdFrame] using
        E6RelativeWeyl.nNative_conj (K := K) (σ := σ) (p := 3) (hp := Nat.prime_three)
          (hζo := hζo) (hζ := hζ) (hζσ := hζσ) (a := a) (s := s))
    (fun g hg => tw3f_normalizer_action_three σ hζo hζ hζσ g hg)

theorem tw3f_centralizer_three
    {K : Type} [Field K] (σ : K →+* K)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (hζσ : σ (ζ : K) = ζ) :
    Subgroup.centralizer
        ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range :
          Set ↥(graphFixedRootGroup TwistTag.E6 K σ)) ≤ E6RelativeTorus.fullTorus σ := by
  intro t ht
  rw [E6RelativeTorus.mem_fullTorus_iff]
  apply ExcFrames.E6QPlusThree.mem_torusGroup_of_commute_e6ThreeDiag hζo hζ
    (twistedFixedGroup_le_adjointGroup _ _ _ (graphFixedRootGroup_le _ _ _ t.2))
  intro s
  have h := Subgroup.mem_centralizer_iff.mp ht
    (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ s) ⟨_, rfl⟩
  have h' := congrArg (fun y : ↥(graphFixedRootGroup TwistTag.E6 K σ) =>
    (y : ModGL TwistTag.E6.tag K)) h
  simp only [Subgroup.coe_mul] at h'
  rw [tw3f_frame_eq σ hζ hζσ s] at h'
  exact h'.symm

private theorem tw3f_prime_three_or_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ 5 ≤ p := by
  have hp3 : 3 ≤ p := by
    have h := hp.two_le
    omega
  rcases lt_or_eq_of_le hp3 with h | h
  · refine Or.inr ?_
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  · exact Or.inl h.symm

theorem tw3f_markedWeyl
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    ∃ hnN : ∀ a : Fin TwistTag.E6.foldedTag.rank,
        E6RelativeWeyl.nNative (K := K) (σ := σ) a ∈ Subgroup.normalizer
          ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range : Set _),
      ggAutomizer (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range =
        Subgroup.closure (Set.range fun a => ggConjAut _ (hnN a)) ∧
      ∃ e : WeylGroup Tag.F4 ≃* ↥(ggAutomizer
          (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ))
          (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range),
        ∀ a, (e (simple Tag.F4 a) : MulAut _) = ggConjAut _ (hnN a) := by
  rcases tw3f_prime_three_or_five_le Fact.out hp2 with rfl | hp5
  · exact tw3f_markedWeyl_three σ hζo hζ hζσ
  · obtain ⟨hnN, hcl, e, he⟩ := E6RelativeWeyl.exists_markedWeyl_standard
      (K := K) (σ := σ) (p := p) (hp := Fact.out) (hp5 := hp5)
      (hζo := hζo) (hζ := hζ) (hζσ := hζσ)
    refine ⟨hnN, ?_, e, ?_⟩
    · exact hcl
    · intro a
      exact he a

theorem tw3f_coordHom_mem_standardFrame_iff
    {K : Type} [Field K] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hζσ : σ (ζ : K) = ζ) (a : Fin Tag.F4.rank → (fixField σ)ˣ) :
    E6RelativeTorus.coordHom σ hσσ a ∈
        (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range ↔
      ∀ j, a j ^ p = 1 := by
  have _hp2 := hp2
  rw [← E6RelativeTorus.coe_coordHom_mem_splitTorsion_iff σ hσσ a p]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨c, hc, h05, h24, he⟩ :=
      ExcFrames.frameDiag_twE6SplitTheta_eq_rootDiagUnit hζ (Multiplicative.toAdd s)
    exact ⟨c, hc, h05, h24, (congrArg Subtype.val hs).symm.trans he⟩
  · rintro ⟨c, hc, h05, h24, he⟩
    obtain ⟨s, hs⟩ := tw3f_exists_frameDiag hζo hζ hc h05 h24
    exact ⟨Multiplicative.ofAdd s, Subtype.ext (hs.trans he.symm)⟩

theorem tw3f_mem_standardFrame_iff
    {K : Type} [Field K] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) {q p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hpm : p ∣ q - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ)
    (t : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    t ∈ (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range ↔
      t ^ p = 1 ∧ t ∈ (E6RelativeTorus.coordHom σ hσσ).range := by
  constructor
  · intro ht
    have htp : t ^ p = 1 := by
      obtain ⟨s, hs⟩ := ht
      rw [← hs, ← map_pow]
      have hsp : s ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        funext i
        simp
      rw [hsp, map_one]
    have htT : t ∈ E6RelativeTorus.fullTorus σ := by
      obtain ⟨s, hs⟩ := ht
      obtain ⟨c, -, -, -, hc⟩ :=
        ExcFrames.frameDiag_twE6SplitTheta_eq_rootDiagUnit hζ (Multiplicative.toAdd s)
      have he : (t : ModGL TwistTag.E6.tag K) = rootDiagUnit Tag.E6 c :=
        (congrArg Subtype.val hs).symm.trans hc
      have htc : rootDiagUnit Tag.E6 c ∈ adjointGroup TwistTag.E6.tag K := by
        rw [← he]
        exact twistedFixedGroup_le_adjointGroup _ _ _ (graphFixedRootGroup_le _ _ _ t.2)
      rw [E6RelativeTorus.mem_fullTorus_iff, he]
      exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup c htc
    have htm : t ^ (q - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpm
      rw [hk, pow_mul, htp, one_pow]
    exact ⟨htp, E6RelativeTorus.mem_range_coordHom_of_mem_fullTorus σ hσσ hq hσ htT htm⟩
  · rintro ⟨htp, a, rfl⟩
    exact (tw3f_coordHom_mem_standardFrame_iff σ hσσ hp2 hζo hζ hζσ a).mpr
      ((E6RelativeTorus.coordHom_pow_eq_one_iff σ hσσ a p).mp htp)

theorem tw3f_centralizer_le_fullTorus
    {K : Type} [Field K] (σ : K →+* K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    Subgroup.centralizer
        ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range :
          Set ↥(graphFixedRootGroup TwistTag.E6 K σ)) ≤ E6RelativeTorus.fullTorus σ := by
  rcases tw3f_prime_three_or_five_le Fact.out hp2 with rfl | hp5
  · exact tw3f_centralizer_three σ hζo hζ hζσ
  · exact E6RelativeTorus.centralizer_standardFrame_le_fullTorus (K := K) (σ := σ)
      (p := p) (hp5 := hp5) (hζo := hζo) (hζ := hζ) (hζσ := hζσ)

end CFSG.StandardType

end
