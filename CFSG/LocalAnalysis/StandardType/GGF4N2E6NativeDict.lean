module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.Assembly.E6FourDiagonal
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitFrobenius
public import CFSG.Assembly.E6FourCentSpec

public section

namespace CFSG.StandardType.N2E6Native

section Lift

variable {U C G : Type} [Group U] [Group C] [Group G]

theorem conj_eq_of_eq_central_mul (hZ : ∀ w ∈ Subgroup.center U, w ^ 3 = 1) {u g z : U}
    (hu : u ^ 5 ∈ Subgroup.center U) (hz : z ∈ Subgroup.center U) (h : g * u * g⁻¹ = z * u) :
    g * u * g⁻¹ = u := by
  have hcomm : Commute z u := (Subgroup.mem_center_iff.mp hz u).symm
  have hu5 : g * u ^ 5 * g⁻¹ = u ^ 5 := by
    rw [Subgroup.mem_center_iff.mp hu g, mul_inv_cancel_right]
  have h5 : z ^ 5 = 1 := by
    have h' : z ^ 5 * u ^ 5 = u ^ 5 := by
      rw [← hcomm.mul_pow, ← h, conj_pow, hu5]
    exact mul_eq_right.mp h'
  have h1 : orderOf z ∣ Nat.gcd 5 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one (hZ z hz))
  rw [show Nat.gcd 5 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
  rw [h, h1, one_mul]

theorem map_centralizer_of_central (θ : U →* C) (hθk : θ.ker ≤ Subgroup.center U)
    (hZ : ∀ w ∈ Subgroup.center U, w ^ 3 = 1) {u : U} (hu : u ^ 5 ∈ Subgroup.center U) :
    (Subgroup.centralizer {u}).map θ = θ.range ⊓ Subgroup.centralizer {θ u} := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff.mp hh, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_iff.mp hg) u (Set.mem_singleton u)]
  · rintro _ ⟨⟨g, rfl⟩, hc⟩
    have hc' : θ u * θ g = θ g * θ u :=
      (Subgroup.mem_centralizer_iff.mp hc) (θ u) (Set.mem_singleton _)
    have hw : g * u * g⁻¹ * u⁻¹ ∈ Subgroup.center U := hθk (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc',
        mul_inv_cancel_right, mul_inv_cancel])
    have heq := conj_eq_of_eq_central_mul (g := g) hZ hu hw (by group)
    refine ⟨g, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, rfl⟩
    rw [Set.mem_singleton_iff.mp hh]
    calc u * g = g * u * g⁻¹ * g := by rw [heq]
      _ = g * u := by group

theorem unique_component_central_lift (θ : U →* C) (hθ : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center U) (ψ : U →* G) (hψk : ψ.ker ≤ Subgroup.center U)
    (hZ : ∀ w ∈ Subgroup.center U, w ^ 3 = 1) {u : U} (hu : θ u ^ 5 = 1)
    {I₀ : Subgroup C} (hI₀ : CFSG.Open.IsComponentOf I₀ (Subgroup.centralizer {θ u}))
    (huniq : ∀ J, CFSG.Open.IsComponentOf J (Subgroup.centralizer {θ u}) → J = I₀) :
    ∃ K : Subgroup U, CFSG.Open.IsComponentOf K (Subgroup.centralizer {u}) ∧ K.map θ = I₀ ∧
      CFSG.Open.IsComponentOf (K.map ψ) (ψ.range ⊓ Subgroup.centralizer {ψ u}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer {ψ u}) → J = K.map ψ) ∧
      Nonempty (↥(K.map ψ) ⧸ Subgroup.center ↥(K.map ψ) ≃* ↥I₀ ⧸ Subgroup.center ↥I₀) := by
  classical
  have hu5 : u ^ 5 ∈ Subgroup.center U := hθk (by rw [MonoidHom.mem_ker, map_pow, hu])
  have hkθ : ∀ g, θ g = 1 → g ∈ Subgroup.center U := fun g hg => hθk hg
  have hkψ : ∀ g, ψ g = 1 → g ∈ Subgroup.center U := fun g hg => hψk hg
  have hmθ : (Subgroup.centralizer {u}).map θ = Subgroup.centralizer {θ u} := by
    rw [map_centralizer_of_central θ hθk hZ hu5, MonoidHom.range_eq_top.mpr hθ, top_inf_eq]
  have hmψ := map_centralizer_of_central ψ hψk hZ hu5
  obtain ⟨K, hK, hKθ⟩ := CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift θ hkθ
    (X := Subgroup.centralizer {u}) (by rw [hmθ]; exact hI₀)
  have hKψ : CFSG.Open.IsComponentOf (K.map ψ) (ψ.range ⊓ Subgroup.centralizer {ψ u}) := by
    rw [← hmψ]
    exact CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map ψ hkψ hK
  have hkerK : ∀ {H : Type} [Group H] (f : U →* H), f.ker ≤ Subgroup.center U →
      (f.subgroupMap K).ker ≤ Subgroup.center ↥K := by
    intro H _ f hf k hk
    have hk' : (k : U) ∈ Subgroup.center U := hf (by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      simpa using this)
    exact Subgroup.mem_center_iff.mpr fun k' => Subtype.ext (Subgroup.mem_center_iff.mp hk' k')
  refine ⟨K, hK, hKθ, hKψ, fun J hJ => ?_, ?_⟩
  · rw [← hmψ] at hJ
    obtain ⟨K', hK', hK'ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift ψ hkψ hJ
    have h1 : K'.map θ = I₀ := huniq _ (by
      rw [← hmθ]
      exact CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map θ hkθ hK')
    have h2 : K' = K :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfect_lifts_with_same_image_eq θ hθk K' K
        ⟨hK'.2.2.1⟩ ⟨hK.2.2.1⟩ (h1.trans hKθ.symm)
    rw [← hK'ψ, h2]
  · obtain ⟨e1⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hK.2.2.1 (ψ.subgroupMap K) (ψ.subgroupMap_surjective K) (hkerK ψ hψk)
    have hs : Function.Surjective
        ((MulEquiv.subgroupCongr hKθ).toMonoidHom.comp (θ.subgroupMap K)) :=
      (MulEquiv.subgroupCongr hKθ).surjective.comp (θ.subgroupMap_surjective K)
    have hk2 : ((MulEquiv.subgroupCongr hKθ).toMonoidHom.comp (θ.subgroupMap K)).ker ≤
        Subgroup.center ↥K := by
      intro k hk
      refine hkerK θ hθk ?_
      rw [MonoidHom.mem_ker] at hk ⊢
      exact (MulEquiv.subgroupCongr hKθ).injective (by simpa using hk)
    obtain ⟨e2⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hK.2.2.1 _ hs hk2
    exact ⟨e1.symm.trans e2⟩

end Lift

section Injective

variable {C M : Type} [Group C] [Group M]

theorem map_centralizer_of_injective (f : C →* M) (hf : Function.Injective f) (y : C) :
    (Subgroup.centralizer {y}).map f = f.range ⊓ Subgroup.centralizer {f y} := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff.mp hh, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_iff.mp hg) y (Set.mem_singleton y)]
  · rintro _ ⟨⟨g, rfl⟩, hc⟩
    refine ⟨g, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, rfl⟩
    rw [Set.mem_singleton_iff.mp hh]
    apply hf
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hc) (f y) (Set.mem_singleton _)

end Injective

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny

section Native


theorem e6NativeW_involutive_check : ∀ l ∈ Tag.E6.artifactRoots,
    e6NativeW (e6NativeW (toVec Tag.E6.rank l)) = toVec Tag.E6.rank l := by
  decide +kernel

theorem e6NativeW_e6NativeW {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    e6NativeW (e6NativeW γ) = γ := by
  have h := e6NativeW_involutive_check (List.ofFn γ) (isRoot_iff_mem_artifactRoots.mp hγ)
  rwa [toVec_ofFn] at h

@[expose] noncomputable def nativeY (t : SL2 (GaloisField 2 2)) (a : Fin 4 → ℤ) :
    ↥(adjointGroup Tag.E6 (GaloisField 2 2)) :=
  ⟨nativePi fun i => t ^ a i, nativePi_mem_adjointGroup _⟩

theorem coe_nativeY (t : SL2 (GaloisField 2 2)) (a : Fin 4 → ℤ) :
    (nativeY t a : ModGL Tag.E6 (GaloisField 2 2)) = nativePi fun i => t ^ a i := rfl

theorem nativeY_pow_five {t : SL2 (GaloisField 2 2)} (ht : t ^ 5 = 1) (a : Fin 4 → ℤ) :
    nativeY t a ^ 5 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_nativeY, Subgroup.coe_one, ← nativePiHom_apply, ← map_pow]
  convert map_one (nativePiHom (Ω := GaloisField 2 2)) using 2
  funext i
  rw [Pi.pow_apply, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rfl

end Native

section Adjoint


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (GaloisField 2 2) L]
  [IsAlgClosure (GaloisField 2 2) L]

theorem adjoint_pullback (S : LangSetup Tag.E6 L 5) {A : SL2 L}
    (hΓ : S.Γ = (nativeIota L).range.map (MulAut.conj (nativeCas A)⁻¹).toMonoidHom)
    (y : ↥(adjointGroup Tag.E6 (GaloisField 2 2))) {d : ModGL Tag.E6 L}
    (hy : (nativeCas A)⁻¹ * nativeIota L y * nativeCas A = d) {R : Subgroup (ModGL Tag.E6 L)}
    (hR : CFSG.Open.IsComponentOf R (S.Γ ⊓ Subgroup.centralizer {d}))
    (hRu : ∀ J, CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {d}) → J = R) :
    ∃ I₀ : Subgroup ↥(adjointGroup Tag.E6 (GaloisField 2 2)),
      CFSG.Open.IsComponentOf I₀ (Subgroup.centralizer {y}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (Subgroup.centralizer {y}) → J = I₀) ∧
      I₀.map ((MulAut.conj (nativeCas A)⁻¹).toMonoidHom.comp (nativeIota L)) = R ∧
      Nonempty (↥I₀ ⧸ Subgroup.center ↥I₀ ≃* ↥R ⧸ Subgroup.center ↥R) := by
  classical
  set ι' : ↥(adjointGroup Tag.E6 (GaloisField 2 2)) →* ModGL Tag.E6 L :=
    (MulAut.conj (nativeCas A)⁻¹).toMonoidHom.comp (nativeIota L) with hι'
  have hinj : Function.Injective ι' :=
    (MulAut.conj (nativeCas A)⁻¹).injective.comp
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))
  have hιy : ι' y = d := by
    rw [← hy, hι', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hrange : ι'.range = S.Γ := by rw [hΓ, hι', MonoidHom.range_comp]
  have hC : (Subgroup.centralizer {y}).map ι' = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [map_centralizer_of_injective ι' hinj, hrange, hιy]
  have hRle : R ≤ ι'.range := hrange ▸ (hR.1.trans inf_le_left)
  have hRmap : (R.comap ι').map ι' = R := Subgroup.map_comap_eq_self hRle
  have hI₀ : CFSG.Open.IsComponentOf (R.comap ι') (Subgroup.centralizer {y}) := by
    rw [← CFSG.Assembly.isComponentOf_iff_open, ← isComponentOf_map_iff hinj, hRmap, hC,
      CFSG.Assembly.isComponentOf_iff_open]
    exact hR
  refine ⟨R.comap ι', hI₀, fun J hJ => ?_, hRmap, ?_⟩
  · have hJ' : CFSG.Open.IsComponentOf (J.map ι') (S.Γ ⊓ Subgroup.centralizer {d}) := by
      rw [← hC, ← CFSG.Assembly.isComponentOf_iff_open, isComponentOf_map_iff hinj,
        CFSG.Assembly.isComponentOf_iff_open]
      exact hJ
    rw [← hRu _ hJ', Subgroup.comap_map_eq_self_of_injective hinj]
  · let e : ↥(R.comap ι') ≃* ↥R :=
      ((R.comap ι').equivMapOfInjective ι' hinj).trans (MulEquiv.subgroupCongr hRmap)
    obtain ⟨e2⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hI₀.2.2.1 e.toMonoidHom e.surjective (fun k hk => by
        have hk' : e.toMonoidHom k = 1 := MonoidHom.mem_ker.mp hk
        rw [MulEquiv.coe_toMonoidHom] at hk'
        rw [e.injective (hk'.trans (map_one e).symm)]
        exact Subgroup.one_mem _)
    exact ⟨e2⟩

end Adjoint

section Rows


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (GaloisField 2 2) L]
  [IsAlgClosure (GaloisField 2 2) L]

theorem adjoint_pair_component (t : SL2 (GaloisField 2 2)) {A : SL2 L} {ζ : Lˣ}
    (hA : A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 2) A = eqpW)
    (htA : A⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap (GaloisField 2 2) L) t * A = HSL ζ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) {i j : Fin 4} (hij : i ≠ j) {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∃ I₀ : Subgroup ↥(adjointGroup Tag.E6 (GaloisField 2 2)),
      CFSG.Open.IsComponentOf I₀
        (Subgroup.centralizer {nativeY t (Pi.single i 1 + e • Pi.single j 1)}) ∧
      (∀ J, CFSG.Open.IsComponentOf J
        (Subgroup.centralizer {nativeY t (Pi.single i 1 + e • Pi.single j 1)}) → J = I₀) ∧
      LieModel (↥I₀ ⧸ Subgroup.center ↥I₀) .POmegaMinus 4 2 2 := by
  classical
  obtain ⟨S, -, hq, hΦ, -, hρ, hΓ⟩ := exists_nativeSetup hA
  have hy : (nativeCas A)⁻¹ * nativeIota L (nativeY t (Pi.single i 1 + e • Pi.single j 1)) *
      nativeCas A = rootDiagUnit Tag.E6
        (fun k => ζ ^ e6NativeChar (Pi.single i 1 + e • Pi.single j 1) k) :=
    nativeTorus_eq (algebraMap (GaloisField 2 2) L) t htA _
  have hT := (nativeTorus_mem S hΓ _ hy).1
  have hζ5 : ζ ^ 5 = 1 := Units.ext (by simpa using hζ.pow_eq_one)
  have hb : ∀ k, (ζ ^ e6NativeChar (Pi.single i 1 + e • Pi.single j 1) k) ^ 5 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ5, one_zpow]
  have hρ2 : ∀ γ, IsRoot Tag.E6 γ → S.ρ (S.ρ γ) = γ := fun γ hγ => by
    rw [hρ _ ((S.frob.isRoot_iff γ).2 hγ), hρ γ hγ, e6NativeW_e6NativeW hγ]
  have hd1 : rootDiagUnit Tag.E6
      (fun k => ζ ^ e6NativeChar (Pi.single i 1 + e • Pi.single j 1) k) ≠ 1 := fun h => by
    have h5 := (rootDiagUnit_nativeChar_eq_one_iff ζ hζ _).1 h i
    simp [Pi.single_apply, hij] at h5
  obtain ⟨c, hc, -, hr, hn, hs, hout⟩ :=
    CFSG.Assembly.E6FourDiagonal.exists_native_pair_component S.ρ hρ ζ hζ i j hij e he
  obtain ⟨hR, hRu, hL⟩ := lang_D4_component S hq hρ2
    ⟨iterateFrobenius L 2 2, fun x => by rw [hq, iterateFrobenius_def] <;> norm_num, hΦ⟩
    hT hb hd1 c hc hr hn hs hout
  obtain ⟨I₀, hI₀, hI₀u, -, ⟨e2⟩⟩ := adjoint_pullback S hΓ _ hy hR hRu
  exact ⟨I₀, hI₀, hI₀u, LieModel.of_mulEquiv e2.symm hL⟩

theorem adjoint_axis_component (t : SL2 (GaloisField 2 2)) {A : SL2 L} {ζ : Lˣ}
    (hA : A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 2) A = eqpW)
    (htA : A⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap (GaloisField 2 2) L) t * A = HSL ζ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (i : Fin 4) :
    ∃ I₀ : Subgroup ↥(adjointGroup Tag.E6 (GaloisField 2 2)),
      CFSG.Open.IsComponentOf I₀ (Subgroup.centralizer {nativeY t (Pi.single i 1)}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (Subgroup.centralizer {nativeY t (Pi.single i 1)}) →
        J = I₀) ∧
      LieModel (↥I₀ ⧸ Subgroup.center ↥I₀) .PSL 6 2 2 := by
  classical
  obtain ⟨S, -, hq, -, -, hρ, hΓ⟩ := exists_nativeSetup hA
  have hy : (nativeCas A)⁻¹ * nativeIota L (nativeY t (Pi.single i 1)) * nativeCas A =
      rootDiagUnit Tag.E6 (fun k => ζ ^ e6NativeChar (Pi.single i 1) k) :=
    nativeTorus_eq (algebraMap (GaloisField 2 2) L) t htA _
  have hT := (nativeTorus_mem S hΓ _ hy).1
  have hζ5 : ζ ^ 5 = 1 := Units.ext (by simpa using hζ.pow_eq_one)
  have hb : ∀ k, (ζ ^ e6NativeChar (Pi.single i 1) k) ^ 5 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ5, one_zpow]
  have hd1 : rootDiagUnit Tag.E6 (fun k => ζ ^ e6NativeChar (Pi.single i 1) k) ≠ 1 := fun h => by
    have h5 := (rootDiagUnit_nativeChar_eq_one_iff ζ hζ _).1 h i
    simp at h5
  obtain ⟨c, hc, -, hr, hn, hs, hin⟩ :=
    CFSG.Assembly.E6FourDiagonal.exists_native_axis_component S.ρ hρ ζ hζ i
  obtain ⟨hR, hRu, hL⟩ := lang_A5_component S hq hT hb hd1 c hc hr hn hs hin
  obtain ⟨I₀, hI₀, hI₀u, -, ⟨e2⟩⟩ := adjoint_pullback S hΓ _ hy hR hRu
  exact ⟨I₀, hI₀, hI₀u, LieModel.of_mulEquiv e2.symm hL⟩

theorem native_pair_component {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    {t : SL2 (GaloisField 2 2)} (ht : t ^ 5 = 1) {A : SL2 L} {ζ : Lˣ}
    (hA : A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 2) A = eqpW)
    (htA : A⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap (GaloisField 2 2) L) t * A = HSL ζ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) {i j : Fin 4} (hij : i ≠ j) {e : ℤ} (he : e = 1 ∨ e = -1)
    (u : ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hu : e6Isogeny (GaloisField 2 2) u = nativeY t (Pi.single i 1 + e • Pi.single j 1)) :
    ∃ K : Subgroup ↥(e6Data_valid.minGroup (GaloisField 2 2)),
      CFSG.Open.IsComponentOf K (Subgroup.centralizer {u}) ∧
      CFSG.Open.IsComponentOf (K.map ψ) (ψ.range ⊓ Subgroup.centralizer {ψ u}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer {ψ u}) → J = K.map ψ) ∧
      LieModel (↥(K.map ψ) ⧸ Subgroup.center ↥(K.map ψ)) .POmegaMinus 4 2 2 ∧
      CFSG.Open.IsComponentOf (K.map (e6Isogeny (GaloisField 2 2)))
        (Subgroup.centralizer {nativeY t (Pi.single i 1 + e • Pi.single j 1)}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I₀, hI₀, hI₀u, hL⟩ := adjoint_pair_component t hA htA hζ hij he
  obtain ⟨K, hK, hKθ, hKψ, hKu, ⟨e2⟩⟩ := unique_component_central_lift
    (e6Isogeny (GaloisField 2 2)) (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective _)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center _) ψ hψ
    (fun w hw => CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 _ hw)
    (u := u) (I₀ := I₀) (by rw [hu]; exact nativeY_pow_five ht _) (by rw [hu]; exact hI₀)
    (by rw [hu]; exact hI₀u)
  exact ⟨K, hK, hKψ, hKu, LieModel.of_mulEquiv e2.symm hL, hKθ ▸ hI₀⟩

theorem native_axis_component {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    {t : SL2 (GaloisField 2 2)} (ht : t ^ 5 = 1) {A : SL2 L} {ζ : Lˣ}
    (hA : A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 2) A = eqpW)
    (htA : A⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap (GaloisField 2 2) L) t * A = HSL ζ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (i : Fin 4)
    (u : ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hu : e6Isogeny (GaloisField 2 2) u = nativeY t (Pi.single i 1)) :
    ∃ K : Subgroup ↥(e6Data_valid.minGroup (GaloisField 2 2)),
      CFSG.Open.IsComponentOf K (Subgroup.centralizer {u}) ∧
      CFSG.Open.IsComponentOf (K.map ψ) (ψ.range ⊓ Subgroup.centralizer {ψ u}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer {ψ u}) → J = K.map ψ) ∧
      LieModel (↥(K.map ψ) ⧸ Subgroup.center ↥(K.map ψ)) .PSL 6 2 2 ∧
      CFSG.Open.IsComponentOf (K.map (e6Isogeny (GaloisField 2 2)))
        (Subgroup.centralizer {nativeY t (Pi.single i 1)}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I₀, hI₀, hI₀u, hL⟩ := adjoint_axis_component t hA htA hζ i
  obtain ⟨K, hK, hKθ, hKψ, hKu, ⟨e2⟩⟩ := unique_component_central_lift
    (e6Isogeny (GaloisField 2 2)) (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective _)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center _) ψ hψ
    (fun w hw => CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 _ hw)
    (u := u) (I₀ := I₀) (by rw [hu]; exact nativeY_pow_five ht _) (by rw [hu]; exact hI₀)
    (by rw [hu]; exact hI₀u)
  exact ⟨K, hK, hKψ, hKu, LieModel.of_mulEquiv e2.symm hL, hKθ ▸ hI₀⟩

end Rows

section RankOne


theorem e6Isogeny_prod_rankOne
    (φ : Fin 4 → (SL2 (GaloisField 2 2) →* ↥(e6Data_valid.minGroup (GaloisField 2 2))))
    (hφ : ∀ k s, ((e6Isogeny (GaloisField 2 2) (φ k s) : ↥(adjointGroup Tag.E6 (GaloisField 2 2))) :
      ModGL Tag.E6 (GaloisField 2 2)) = rootSL2 Tag.E6 (GaloisField 2 2) (e6NativeGamma k) s)
    (t : SL2 (GaloisField 2 2)) (a : Fin 4 → ℤ) :
    e6Isogeny (GaloisField 2 2) ((List.finRange 4).map fun k => φ k (t ^ a k)).prod =
      nativeY t a := by
  apply Subtype.ext
  rw [map_list_prod, Subgroup.val_list_prod, List.map_map, List.map_map, coe_nativeY]
  unfold nativePi
  congr 1
  exact List.map_congr_left fun k _ => hφ k (t ^ a k)

end RankOne

section Final


theorem native_pair_component_of_order_five {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    {t : SL2 (GaloisField 2 2)} (ht : orderOf t = 5) {i j : Fin 4} (hij : i ≠ j) {e : ℤ}
    (he : e = 1 ∨ e = -1)
    (u : ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hu : e6Isogeny (GaloisField 2 2) u = nativeY t (Pi.single i 1 + e • Pi.single j 1)) :
    ∃ K : Subgroup ↥(e6Data_valid.minGroup (GaloisField 2 2)),
      CFSG.Open.IsComponentOf K (Subgroup.centralizer {u}) ∧
      CFSG.Open.IsComponentOf (K.map ψ) (ψ.range ⊓ Subgroup.centralizer {ψ u}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer {ψ u}) → J = K.map ψ) ∧
      LieModel (↥(K.map ψ) ⧸ Subgroup.center ↥(K.map ψ)) .POmegaMinus 4 2 2 ∧
      CFSG.Open.IsComponentOf (K.map (e6Isogeny (GaloisField 2 2)))
        (Subgroup.centralizer {nativeY t (Pi.single i 1 + e • Pi.single j 1)}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure (GaloisField 2 2)) 2 :=
    charP_of_injective_algebraMap (algebraMap (GaloisField 2 2) _).injective 2
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)] <;> norm_num
  obtain ⟨ζ, hζ, A, hA, htA⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_simultaneous_diagonalizer_order_five
      (Ω := AlgebraicClosure (GaloisField 2 2)) hK4 t ht
  exact native_pair_component ψ hψ (by rw [← ht]; exact pow_orderOf_eq_one t) hA htA hζ hij he
    u hu

theorem native_axis_component_of_order_five {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    {t : SL2 (GaloisField 2 2)} (ht : orderOf t = 5) (i : Fin 4)
    (u : ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hu : e6Isogeny (GaloisField 2 2) u = nativeY t (Pi.single i 1)) :
    ∃ K : Subgroup ↥(e6Data_valid.minGroup (GaloisField 2 2)),
      CFSG.Open.IsComponentOf K (Subgroup.centralizer {u}) ∧
      CFSG.Open.IsComponentOf (K.map ψ) (ψ.range ⊓ Subgroup.centralizer {ψ u}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer {ψ u}) → J = K.map ψ) ∧
      LieModel (↥(K.map ψ) ⧸ Subgroup.center ↥(K.map ψ)) .PSL 6 2 2 ∧
      CFSG.Open.IsComponentOf (K.map (e6Isogeny (GaloisField 2 2)))
        (Subgroup.centralizer {nativeY t (Pi.single i 1)}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure (GaloisField 2 2)) 2 :=
    charP_of_injective_algebraMap (algebraMap (GaloisField 2 2) _).injective 2
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)] <;> norm_num
  obtain ⟨ζ, hζ, A, hA, htA⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_simultaneous_diagonalizer_order_five
      (Ω := AlgebraicClosure (GaloisField 2 2)) hK4 t ht
  exact native_axis_component ψ hψ (by rw [← ht]; exact pow_orderOf_eq_one t) hA htA hζ i u hu

end Final

end CFSG.StandardType.N2E6Native

end
