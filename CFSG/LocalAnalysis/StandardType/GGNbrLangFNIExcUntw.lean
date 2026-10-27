module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacChev
public import CFSG.LocalAnalysis.StandardType.GGCanonicalToLegacy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcInnHolds
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.PerfectAutomorphisms


@[expose] def kgfniExcUntwTag : Tag → LargeEvenLieTag
  | .G2 => .G2
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | _ => .G2

@[expose] def kgfni_hOneProp (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ f ∈ F, orderOf f = p →
    ∀ h ∈ I, h ^ p = 1 → h * f = f * h → h = 1 →
      ∀ J₀ : Subgroup R,
        IsComponentOf J₀ (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)) →
        ∀ f' : MulAut J₀, (∀ j : J₀, (f' j : R) = f j) →
          GGMarkingAll (K := J₀) fun _ _ _ I' _ θ' => kgInducedAut θ' f' ∉ I'

theorem largeEvenRawDatum_repack {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F ∧
      ∀ Q' : LargeEvenRawCont, Q' R I F → LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨_, _, _, _, hq, fun Q' hQ' => ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨_, _, _, _, hq, fun Q' hQ' => ⟨K, i1, i2, hK, hQ'⟩⟩)

private theorem fniEU_hOne_chev {τ : Tag} {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) :
    kgfni_hOneProp p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have hlab : LargeEvenInLambda2 ⟨kgfniExcUntwTag τ, 0, n⟩ := by
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [kgfniExcUntwTag, LargeEvenInLambda2]
      constructor
      · omega
      · simp [hn]
  have htag : KGFNIChevalleyLabel ⟨kgfniExcUntwTag τ, 0, n⟩ := by
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;>
      simp [kgfniExcUntwTag, KGFNIChevalleyLabel]
  have hcongr_refl : ∀ {X : Type} [Group X],
      MulAut.congr (MulEquiv.refl X) = MulEquiv.refl (MulAut X) := by
    intro X _
    ext f x
    simp [MulAut.congr, MulEquiv.trans_apply]
  have hself : LargeEvenRawDatum ⟨kgfniExcUntwTag τ, 0, n⟩
      (fun R' _ _ F' => ∃ e : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) ≃* R',
        F' = MulAut.congr e ''
          LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    all_goals
      refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
      dsimp only [kgfniExcUntwTag, LargeEvenRawDatum, LargeEvenRecipeChevalley]
      refine ⟨MulEquiv.refl _, ?_⟩
      ext φ
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨φ, h, rfl⟩
      · rintro ⟨x, hx, hφx⟩
        rw [← hφx]
        exact hx
  exact fun f hf hord h hh hhp hcomm hh1 J hJ f' hf' =>
    kgFieldRestriction_hOne_of_rawImage hp hp2 hlab (kgfni_rawSimple_chev _ hlab htag) hself
      f hf hord J (by simpa [hh1] using hJ) f' hf'

theorem largeEvenMarkingLegacy_to_canonical {L : Type*} [Group L]
    {P : LargeEvenMarkProp L}
    (hmono : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I I' F : Set (MulAut R))
      (θ : L ⧸ Subgroup.center L ≃* R), I ⊆ I' → P lab R I F θ → P lab R I' F θ)
    (h : CFSG.Assembly.LargeEvenMarkingLegacy L P) :
    CFSG.Assembly.LargeEvenMarking L P := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  refine ⟨hL, lab, hlab, ?_⟩
  refine largeEvenRawDatum_canonical_of_legacy_mono
    (Q := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ, P lab R I F θ) ?_ hraw
  rintro R _ I I' F hsub ⟨hs, hna, θ, hP⟩
  exact ⟨hs, hna, θ, hmono lab R I I' F θ hsub hP⟩

theorem kgfni_false_of_component_marking
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L p) (Rt : FrobRoot SL.D p)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {e : ℕ} (he1 : 1 ≤ e) (hq0 : Rt.q0 = 2 ^ e)
    (hTa : rootDiagUnit τ a ∈ SL.D.torus) (hap : ∀ m, a m ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (hfa : Rt.step0 (rootDiagUnit τ a) = rootDiagUnit τ a)
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hstab : ∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
      Rt.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i)
    {J₀ : Type} [Group J₀] (f' : MulAut J₀) (k : ℕ)
    {C : Type} [Group C] {JP : Subgroup C}
    (E₁ : J₀ ⧸ Subgroup.center J₀ ≃* JP ⧸ Subgroup.center JP)
    (eJ : JP ≃* ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (ψJ : MulAut JP)
    (hA : ∀ s : J₀ ⧸ Subgroup.center J₀,
      E₁ (centerQuotAut J₀ (f' ^ k) s) = onCenterQuotient ψJ (E₁ s))
    (hσ : ∀ j : JP,
      ((eJ (ψJ j) : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) : ModGL τ L) =
        Rt.step0 ((eJ j : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) : ModGL τ L))
    {P : LargeEvenMarkProp J₀}
    (hmark : CFSG.Assembly.LargeEvenMarking J₀ P)
    (hinner : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ≃* R),
      P lab R I F ((E₁.trans (centerQuotCongr eJ)).trans θ) →
        ∃ φ ∈ I, φ = kgInducedAut ((E₁.trans (centerQuotCongr eJ)).trans θ) (f' ^ k) ∧
        LargeEvenInduces ((E₁.trans (centerQuotCongr eJ)).trans θ)
          (fun j k' : J₀ => k' = (f' ^ k) j) φ) :
    False := by
  let E₂ : JP ⧸ Subgroup.center JP ≃*
      ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) :=
    centerQuotCongr eJ
  let E : J₀ ⧸ Subgroup.center J₀ ≃*
      ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) :=
    E₁.trans E₂
  have hM : CFSG.Assembly.LargeEvenMarking
      ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) (fun _ _ _ I _ θ =>
        ∃ φ ∈ I, LargeEvenInduces θ
          (fun x x' : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) =>
            Rt.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ) := by
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
      (CFSG.LocalAnalysis.GLTheoremA.K155X.l154_marking_transport
        hqi.1.commutator_eq_top E hmark)
    rintro lab' R'' _ I'' F'' θ hP
    obtain ⟨φ, hφI, hφeq, -⟩ := hinner lab' R'' I'' F'' θ hP
    refine ⟨φ, hφI, ?_⟩
    rw [hφeq]
    exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_induces_transfer eJ E₁
      (centerQuotAut J₀ (f' ^ k)) ψJ hA
      (fun x : ModGL τ L => Rt.step0 x) hσ θ
  exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_lang_noInnDiag
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154LangInnRes_holds hp hp2 SL Rt he1 hq0
    hTa hap ha1 hfa hqi hstab hM

theorem kgFieldRestriction_of_langSetup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R C : Type} [Group R] [Group C] [Finite C] (eC : R ≃* C) {h f : MulAut R} (k : ℕ)
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L p) (Rt : FrobRoot SL.D p) {e : ℕ} {a : Fin τ.rank → Lˣ}
    (he1 : 1 ≤ e) (hq0 : Rt.q0 = 2 ^ e) (hTa : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ i, a i ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (hfa : Rt.step0 (rootDiagUnit τ a) = rootDiagUnit τ a)
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = SL.Γ)
    (hβ : ∀ c, ι (MulAut.congr eC h c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hφ : ∀ c, ι (MulAut.congr eC (f ^ k) c) = Rt.step0 (ι c))
    (J₀ : Subgroup R) (hJ₀ : IsComponentOf J₀ (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)))
    (f' : MulAut J₀) (hf' : ∀ j : J₀, (f' j : R) = f j) :
    GGMarkingAll (K := J₀) fun _ _ _ I' _ θ' => kgInducedAut θ' f' ∉ I' := by
  let JP : Subgroup C := J₀.map eC.toMonoidHom
  have hJ₀' : CFSG.Open.IsComponentOf J₀ (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)) :=
    isComponentOf_iff_open.mp hJ₀
  have hJPcomp : CFSG.Open.IsComponentOf JP (fixSubgroup (MulAut.congr eC h)) := by
    have h1 : CFSG.Open.IsComponentOf (J₀.map eC.toMonoidHom)
        ((fixSubgroup h).map eC.toMonoidHom) :=
      CFSG.isComponentOf_map_mulEquiv eC hJ₀'
    have hfixc : (fixSubgroup h).map eC.toMonoidHom = fixSubgroup (MulAut.congr eC h) :=
      (fixSubgroup_congr eC h).symm
    rw [hfixc] at h1
    exact h1
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame
    SL hTa hap ha1
  obtain ⟨i, hqi, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup SL hp ι hι
      hrange (MulAut.congr eC h) hβ hTa hap ha1 hTame hJPcomp
  let Ri : Subgroup (ModGL τ L) := rationalComponent SL.ρ SL.Γ (rootCharHom a) i
  have hpow : ∀ (m : ℕ), ∀ j : J₀, ((f' ^ m) j : R) = (f ^ m) j := by
    intro m
    induction m with
    | zero => intro j; rfl
    | succ m ih =>
      intro j
      rw [pow_succ, pow_succ, MulAut.mul_apply, ih (f' j), hf' j]
      rfl
  have hcongr : ∀ x : R, MulAut.congr eC (f ^ k) (eC x) = eC ((f ^ k) x) := by
    intro x
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hstab : ∀ z ∈ Ri, Rt.step0 z ∈ Ri := by
    intro z hz
    have hz' : z ∈ JP.map ι := by rw [hmap]; exact hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz'
    obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hx
    rw [← hxz, ← hje]
    change Rt.step0 (ι (eC j)) ∈ Ri
    rw [← hφ (eC j), hcongr j]
    change ι (eC ((f ^ k) j)) ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i
    rw [show rationalComponent SL.ρ SL.Γ (rootCharHom a) i = JP.map ι from hmap.symm]
    refine Subgroup.mem_map_of_mem ι (Subgroup.mem_map_of_mem eC.toMonoidHom ?_)
    rw [← hpow k ⟨j, hj⟩]
    exact ((f' ^ k) ⟨j, hj⟩).2
  let eJ₀ : J₀ ≃* JP := Subgroup.equivMapOfInjective J₀ eC.toMonoidHom eC.injective
  let E₁ : J₀ ⧸ Subgroup.center J₀ ≃* JP ⧸ Subgroup.center JP := centerQuotCongr eJ₀
  let eJ : JP ≃* Ri :=
    (Subgroup.equivMapOfInjective JP ι hι).trans (MulEquiv.subgroupCongr hmap)
  have hsurjJ : J₀.map (f ^ k).toMonoidHom = J₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
      change (f ^ k) j ∈ J₀
      rw [← hpow k ⟨j, hj⟩]
      exact ((f' ^ k) ⟨j, hj⟩).2
    · intro x hx
      obtain ⟨j, hj⟩ := (f' ^ k).surjective ⟨x, hx⟩
      have hxeq : x = (f ^ k) (j : R) := by
        calc x = ((f' ^ k) j : R) := (congrArg Subtype.val hj).symm
          _ = (f ^ k) (j : R) := hpow k j
      rw [hxeq]
      exact Subgroup.mem_map_of_mem (f ^ k).toMonoidHom (j : J₀).2
  have hstabJP : JP.map (MulAut.congr eC (f ^ k) : C →* C) = JP := by
    change (J₀.map eC.toMonoidHom).map (MulAut.congr eC (f ^ k) : C →* C) = JP
    rw [Subgroup.map_map]
    have hcomm : ((MulAut.congr eC (f ^ k) : C →* C).comp eC.toMonoidHom) =
        (eC.toMonoidHom.comp (f ^ k).toMonoidHom) := by
      ext x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomm, ← Subgroup.map_map, hsurjJ]
  let ψJ : MulAut JP :=
    ((MulAut.congr eC (f ^ k)).subgroupMap JP).trans (MulEquiv.subgroupCongr hstabJP)
  have hψJ_coe : ∀ x : JP, ((ψJ x : JP) : C) = MulAut.congr eC (f ^ k) (x : C) := by
    intro x
    rfl
  have hψ_apply : ∀ j : J₀, eJ₀ ((f' ^ k) j) = ψJ (eJ₀ j) := by
    intro j
    apply Subtype.ext
    rw [hψJ_coe]
    change eC ((f' ^ k) j : R) = MulAut.congr eC (f ^ k) (eC (j : R))
    rw [hpow k j, hcongr]
  have hA : ∀ s : J₀ ⧸ Subgroup.center J₀,
      E₁ (centerQuotAut J₀ (f' ^ k) s) = onCenterQuotient ψJ (E₁ s) := by
    intro s
    induction s using QuotientGroup.induction_on with
    | H j =>
      change centerQuotCongr eJ₀ (centerQuotAut J₀ (f' ^ k) (QuotientGroup.mk j)) =
        onCenterQuotient ψJ (centerQuotCongr eJ₀ (QuotientGroup.mk j))
      rw [centerQuotAut_mk]
      have hmk1 : centerQuotCongr eJ₀ (QuotientGroup.mk ((f' ^ k) j)) =
          QuotientGroup.mk (eJ₀ ((f' ^ k) j)) :=
        QuotientGroup.congr_mk _ _ _ _ _
      have hmk2 : centerQuotCongr eJ₀ (QuotientGroup.mk j) =
          QuotientGroup.mk (eJ₀ j) :=
        QuotientGroup.congr_mk _ _ _ _ _
      rw [hmk1, hmk2]
      change QuotientGroup.mk (eJ₀ ((f' ^ k) j)) = QuotientGroup.mk (ψJ (eJ₀ j))
      exact congrArg QuotientGroup.mk (hψ_apply j)
  have hstep : ∀ j : JP,
      ((eJ (ψJ j) : Ri) : ModGL τ L) = Rt.step0 ((eJ j : Ri) : ModGL τ L) := by
    intro j
    have hcoe : ∀ x : JP, ((eJ x : Ri) : ModGL τ L) = ι (x : C) := fun x => rfl
    rw [hcoe, hcoe, hψJ_coe, hφ]
  intro P hmark
  have hmarkInn : LargeEvenMarking J₀ (fun lab R _ I F θ =>
      P lab R I F θ ∧ GGRawInnField p R I F) :=
    largeEvenMarking_and_labelAll
      (fun lab hlab _ => ggRawInnFieldInput_holds p hp hp2 lab hlab)
      (fun _ _ _ _ _ _ _ => trivial) hmark
  obtain ⟨hcommJ, lab, hlab, hrawInn⟩ := hmarkInn
  obtain ⟨R', _, I', F', hQR, hrepack⟩ := largeEvenRawDatum_repack hrawInn
  obtain ⟨hs, hna, θ_t, hPθt, hinn⟩ := hQR
  let Pinner : LargeEvenMarkProp J₀ := fun _ R _ I F θ =>
    ∃ φ ∈ I, φ = kgInducedAut θ (f' ^ k) ∧
      LargeEvenInduces θ (fun j k' : J₀ => k' = (f' ^ k) j) φ
  refine ⟨hcommJ, lab, hlab, hrepack _ ?_⟩
  refine ⟨hs, hna, θ_t, hPθt, ?_⟩
  intro hmem
  obtain ⟨hmul, hinv, hconj, -⟩ := hinn hs hna
  have hone : (1 : MulAut R') ∈ I' := by simpa using hconj 1
  let H' : Subgroup (MulAut R') :=
    { carrier := I', one_mem' := hone
      mul_mem' := fun ha hb => hmul _ ha _ hb
      inv_mem' := fun ha => hinv _ ha }
  have hmemk : kgInducedAut θ_t (f' ^ k) ∈ I' := by
    have h1 : (kgInducedAut θ_t f') ^ k ∈ H' := H'.pow_mem hmem k
    rw [map_pow]
    exact h1
  have hmono : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I I' F : Set (MulAut R))
      (θ : J₀ ⧸ Subgroup.center J₀ ≃* R),
      I ⊆ I' → Pinner lab R I F θ → Pinner lab R I' F θ := by
    rintro lab R _ I I' F θ hsub ⟨φ, hφI, hφeq, hind⟩
    exact ⟨φ, hsub hφI, hφeq, hind⟩
  have hmarkInner : CFSG.Assembly.LargeEvenMarkingLegacy J₀ Pinner :=
    ⟨hcommJ, lab, hlab, hrepack _ ⟨hs, hna, θ_t,
      ⟨kgInducedAut θ_t (f' ^ k), hmemk, rfl,
        kgInducedAut_induces θ_t (f' ^ k)⟩⟩⟩
  exact kgfni_false_of_component_marking hp hp2 SL Rt i he1 hq0 hTa hap ha1 hfa hqi hstab
    f' k E₁ eJ ψJ hA hstep (largeEvenMarkingLegacy_to_canonical hmono hmarkInner)
    (fun _ _ _ _ _ _ h => h)

theorem kgFieldRestrictionCont_excUntw {τ : Tag} {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) :
    KGFieldRestrictionCont p (LargeEvenCenterQuot (adjointGroup τ K))
      (RecipeExcLang.markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hOneChev := fniEU_hOne_chev hτ hn hK hp hp2
  have hOneModel : kgfni_hOneProp p (LargeEvenCenterQuot (adjointGroup τ K))
      (RecipeExcLang.markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport hOneChev
  intro f hf hord h hh hhp hcomm J₀ hJ₀ f' hf'
  by_cases hh1 : h = 1
  · exact hOneModel f hf hord h hh hhp hcomm hh1 J₀ hJ₀ f' hf'
  ·
    have hr : 0 < τ.rank := by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨w, hw⟩ := RecipeExcLang.exists_inndiagConj_of_mem_markID hh
    obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
    have hcomm' : RecipeExcLang.inndiagConj τ K w * entrywiseAdjointAut τ σ =
        entrywiseAdjointAut τ σ * RecipeExcLang.inndiagConj τ K w := by
      have h1 := congrArg (RecipeExcLang.autEquiv τ K) hcomm
      rw [map_mul, map_mul, hw, hσ] at h1
      exact h1
    have hσp : orderOf σ = p := by
      have h1 : orderOf (RecipeExcLang.autEquiv τ K f) = p := by
        rw [MulEquiv.orderOf_eq, hord]
      rw [hσ] at h1
      rwa [CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ] at h1
    obtain ⟨e, k, T, hep, he1, hT, hk, hcop⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_exists_frob_pow Nat.prime_two
        (by omega) hK hp σ hσp
    have hKe : Nat.card K = 2 ^ (e * p) := by rw [hK, hep]
    have hn2 : 2 ≤ n := by
      have h2 : 2 ≤ e * p := by nlinarith [he1, hp.two_le]
      omega
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hcommT : RecipeExcLang.inndiagConj τ K w * entrywiseAdjointAut τ T =
        entrywiseAdjointAut τ T * RecipeExcLang.inndiagConj τ K w := by
      have hc : Commute (RecipeExcLang.inndiagConj τ K w) (entrywiseAdjointAut τ σ) := hcomm'
      rw [← hk, entrywiseAdjointAut_pow]
      exact hc.pow_right k
    have hfix' := CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_fix_of_commute hK4 T w hcommT
    have hfix : Units.map (entrywiseHom T) (w : ModGL τ K) = (w : ModGL τ K) := by
      have h1 := congrArg Subtype.val hfix'
      rwa [RecipeExcLang.coe_inndiagFieldAut] at h1
    have hwpow : w ^ p = 1 := by
      have h1 : (RecipeExcLang.inndiagConj τ K w) ^ p = 1 := by
        rw [← hw, ← map_pow, hhp, map_one]
      rw [← map_pow] at h1
      exact CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_eq_one_of_inndiagConj hK4 h1
    have hw1 : w ≠ 1 := by
      rintro rfl
      apply hh1
      apply (RecipeExcLang.autEquiv τ K).injective
      rw [hw]
      simp
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
      rcases hτ with rfl | rfl | rfl | rfl | rfl
      · exact (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card
          (K := K) h3).1.commutator_eq_top
      · exact (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (K := K)).1.commutator_eq_top
      · exact (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K).1.commutator_eq_top
      · exact (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1.commutator_eq_top
      · exact (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 (K := K)).1.commutator_eq_top
    obtain ⟨SL, Rt, a, ι, hSLq, hq0, hFrob, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_frobRoot_untw
        hτ hp hp2 he1 hKe hperf T hT (RecipeExcLang.inndiagConj τ K w)
        (entrywiseAdjointAut τ T) w
        (RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag _ w.2)
        (fun c => RecipeExcLang.coe_inndiagConj w c)
        (fun c => coe_entrywiseAdjointAut τ T c)
        (by rw [← Subgroup.coe_pow, hwpow]; rfl) (fun h1 => hw1 (Subtype.ext h1)) hfix
    let eC : LargeEvenCenterQuot (adjointGroup τ K) ≃* ↥(adjointGroup τ K) :=
      centerQuotEquivOfBot center_adjointGroup_eq_bot
    haveI : Finite ↥(adjointGroup τ K) :=
      Finite.of_injective (Subtype.val : ↥(adjointGroup τ K) → ModGL τ K) Subtype.val_injective
    have hEh : MulAut.congr eC h = RecipeExcLang.inndiagConj τ K w := by
      change RecipeExcLang.autEquiv τ K h = RecipeExcLang.inndiagConj τ K w
      exact hw
    have hφeq : entrywiseAdjointAut τ T = MulAut.congr eC (f ^ k) := by
      change entrywiseAdjointAut τ T = RecipeExcLang.autEquiv τ K (f ^ k)
      rw [← hk, entrywiseAdjointAut_pow, ← hσ, ← map_pow]
    exact kgFieldRestriction_of_langSetup hp hp2 eC k SL Rt he1 hq0 hTa hap ha1 hfa ι hι hrange
      (fun c => by rw [hEh]; exact hβ c) (fun c => by rw [← hφeq]; exact hφ c) J₀ hJ₀ f' hf'


theorem kgFieldRestrictionOn_of_excUntw_model {τ : Tag} {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hn : 2 ≤ n) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = kgfniExcUntwTag τ) (hnlab : lab.n = n) :
    LargeEvenLabelAll lab (KGFieldRestrictionCont p) := by
  obtain ⟨t, r, m⟩ := lab
  have hnm : 2 ≤ m := by
    have hmn : m = n := hnlab
    omega
  rcases hτ with hG2 | hF4 | hE6 | hE7 | hE8
  · subst hG2
    subst htag
    intro Q hraw
    dsimp only [kgfniExcUntwTag, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
    letI := hF
    haveI := hfin
    have hCore : KGFieldRestrictionCont p (LargeEvenCenterQuot (adjointGroup .G2 K))
        (RecipeExcLang.markIDImage (IsRoot .G2) K (adjointGroup .G2 K))
        (RecipeFieldExcInn.markFieldImage (IsRoot .G2) K (adjointGroup .G2 K)) :=
      kgFieldRestrictionCont_excUntw (τ := .G2) (K := K) (n := m) (Or.inl rfl) hnm hK hp hp2
    have hChev : KGFieldRestrictionCont p
        (LargeEvenCenterQuot (LargeEvenChevH (Tag.G2).cartan K false))
        (LargeEvenChevIDImage (Tag.G2).cartan K (LargeEvenChevH (Tag.G2).cartan K false))
        (LargeEvenChevFieldImage (Tag.G2).cartan K (LargeEvenChevH (Tag.G2).cartan K false)) := by
      by_contra hnc
      exact (CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport (τ := .G2) (K := K)
        (Q := fun R _ I F => ¬ KGFieldRestrictionCont p R I F) hnc) hCore
    exact ⟨K, hF, hfin, hK, hQ, hChev⟩
  · subst hF4
    subst htag
    intro Q hraw
    dsimp only [kgfniExcUntwTag, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
    letI := hF
    haveI := hfin
    have hCore : KGFieldRestrictionCont p (LargeEvenCenterQuot (adjointGroup .F4 K))
        (RecipeExcLang.markIDImage (IsRoot .F4) K (adjointGroup .F4 K))
        (RecipeFieldExcInn.markFieldImage (IsRoot .F4) K (adjointGroup .F4 K)) :=
      kgFieldRestrictionCont_excUntw (τ := .F4) (K := K) (n := m)
        (Or.inr (Or.inl rfl)) hnm hK hp hp2
    have hChev : KGFieldRestrictionCont p
        (LargeEvenCenterQuot (LargeEvenChevH (Tag.F4).cartan K false))
        (LargeEvenChevIDImage (Tag.F4).cartan K (LargeEvenChevH (Tag.F4).cartan K false))
        (LargeEvenChevFieldImage (Tag.F4).cartan K (LargeEvenChevH (Tag.F4).cartan K false)) := by
      by_contra hnc
      exact (CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport (τ := .F4) (K := K)
        (Q := fun R _ I F => ¬ KGFieldRestrictionCont p R I F) hnc) hCore
    exact ⟨K, hF, hfin, hK, hQ, hChev⟩
  · subst hE6
    subst htag
    intro Q hraw
    dsimp only [kgfniExcUntwTag, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
    letI := hF
    haveI := hfin
    have hCore : KGFieldRestrictionCont p (LargeEvenCenterQuot (adjointGroup .E6 K))
        (RecipeExcLang.markIDImage (IsRoot .E6) K (adjointGroup .E6 K))
        (RecipeFieldExcInn.markFieldImage (IsRoot .E6) K (adjointGroup .E6 K)) :=
      kgFieldRestrictionCont_excUntw (τ := .E6) (K := K) (n := m)
        (Or.inr (Or.inr (Or.inl rfl))) hnm hK hp hp2
    have hChev : KGFieldRestrictionCont p
        (LargeEvenCenterQuot (LargeEvenChevH (Tag.E6).cartan K false))
        (LargeEvenChevIDImage (Tag.E6).cartan K (LargeEvenChevH (Tag.E6).cartan K false))
        (LargeEvenChevFieldImage (Tag.E6).cartan K (LargeEvenChevH (Tag.E6).cartan K false)) := by
      by_contra hnc
      exact (CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport (τ := .E6) (K := K)
        (Q := fun R _ I F => ¬ KGFieldRestrictionCont p R I F) hnc) hCore
    exact ⟨K, hF, hfin, hK, hQ, hChev⟩
  · subst hE7
    subst htag
    intro Q hraw
    dsimp only [kgfniExcUntwTag, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
    letI := hF
    haveI := hfin
    have hCore : KGFieldRestrictionCont p (LargeEvenCenterQuot (adjointGroup .E7 K))
        (RecipeExcLang.markIDImage (IsRoot .E7) K (adjointGroup .E7 K))
        (RecipeFieldExcInn.markFieldImage (IsRoot .E7) K (adjointGroup .E7 K)) :=
      kgFieldRestrictionCont_excUntw (τ := .E7) (K := K) (n := m)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hnm hK hp hp2
    have hChev : KGFieldRestrictionCont p
        (LargeEvenCenterQuot (LargeEvenChevH (Tag.E7).cartan K false))
        (LargeEvenChevIDImage (Tag.E7).cartan K (LargeEvenChevH (Tag.E7).cartan K false))
        (LargeEvenChevFieldImage (Tag.E7).cartan K (LargeEvenChevH (Tag.E7).cartan K false)) := by
      by_contra hnc
      exact (CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport (τ := .E7) (K := K)
        (Q := fun R _ I F => ¬ KGFieldRestrictionCont p R I F) hnc) hCore
    exact ⟨K, hF, hfin, hK, hQ, hChev⟩
  · subst hE8
    subst htag
    intro Q hraw
    dsimp only [kgfniExcUntwTag, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
    letI := hF
    haveI := hfin
    have hCore : KGFieldRestrictionCont p (LargeEvenCenterQuot (adjointGroup .E8 K))
        (RecipeExcLang.markIDImage (IsRoot .E8) K (adjointGroup .E8 K))
        (RecipeFieldExcInn.markFieldImage (IsRoot .E8) K (adjointGroup .E8 K)) :=
      kgFieldRestrictionCont_excUntw (τ := .E8) (K := K) (n := m)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hnm hK hp hp2
    have hChev : KGFieldRestrictionCont p
        (LargeEvenCenterQuot (LargeEvenChevH (Tag.E8).cartan K false))
        (LargeEvenChevIDImage (Tag.E8).cartan K (LargeEvenChevH (Tag.E8).cartan K false))
        (LargeEvenChevFieldImage (Tag.E8).cartan K (LargeEvenChevH (Tag.E8).cartan K false)) := by
      by_contra hnc
      exact (CFSG.LocalAnalysis.GLTheoremA.K155X.excUntw_chev_transport (τ := .E8) (K := K)
        (Q := fun R _ I F => ¬ KGFieldRestrictionCont p R I F) hnc) hCore
    exact ⟨K, hF, hfin, hK, hQ, hChev⟩

end CFSG.StandardType

end
