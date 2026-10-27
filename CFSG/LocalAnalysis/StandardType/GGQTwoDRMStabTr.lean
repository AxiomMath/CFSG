module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFormA

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

private def p9uRMT_SignedPerm (g : DVec m → DVec m) : Prop :=
  ∃ (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3), (∀ i, c i = 1 ∨ c i = -1) ∧
    ∀ i, g (dBasis m i) = c i • dBasis m (σ i)

private lemma p9uRMT_signedPerm_of_dEven {g : DVec m ≃ₗ[ZMod 3] DVec m} (hg : g ∈ dEven m) :
    p9uRMT_SignedPerm g := by
  obtain ⟨σ, c, hc, -, hact⟩ := hg
  exact ⟨σ, c, hc, hact⟩

private lemma p9uRMT_signedPerm_congr {f g : DVec m → DVec m} (h : ∀ v, f v = g v)
    (hg : p9uRMT_SignedPerm g) : p9uRMT_SignedPerm f := by
  obtain ⟨σ, c, hc, hact⟩ := hg
  exact ⟨σ, c, hc, fun i => by rw [h, hact i]⟩

private lemma p9uRMT_signedPerm_neg {g : DVec m → DVec m} (hg : p9uRMT_SignedPerm g) :
    p9uRMT_SignedPerm (fun v => -(g v)) := by
  obtain ⟨σ, c, hc, hact⟩ := hg
  refine ⟨σ, fun i => -c i, ?_, ?_⟩
  · intro i
    rcases hc i with h | h <;> simp [h]
  · intro i
    change -(g (dBasis m i)) = (-c i) • dBasis m (σ i)
    rw [hact i, neg_smul]

private lemma p9uRMT_signedPerm_comp_dNeg {g : DVec m → DVec m} (hg : p9uRMT_SignedPerm g)
    (a : Fin m) : p9uRMT_SignedPerm (fun v => dNeg m a (g v)) := by
  obtain ⟨σ, c, hc, hact⟩ := hg
  refine ⟨σ, fun i => c i * (if σ i = a then (-1 : ZMod 3) else 1), ?_, ?_⟩
  · intro i
    rcases hc i with h | h <;> by_cases h' : σ i = a <;> simp [h, h']
  · intro i
    change dNeg m a (g (dBasis m i)) =
      (c i * (if σ i = a then (-1 : ZMod 3) else 1)) • dBasis m (σ i)
    rw [hact i, map_smul, dNeg_basis, smul_smul]

private lemma p9uRMT_span_ggDSimple (hm : 4 ≤ m) :
    Submodule.span (ZMod 3) (Set.range (ggDSimple 3 m)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (ggDSimple_linearIndependent hm),
    Module.finrank_fintype_fun_eq_card]

private lemma p9uRMT_ext_ggDSimple (hm : 4 ≤ m) {f g : DVec m ≃ₗ[ZMod 3] DVec m}
    (h : ∀ j, f (ggDSimple 3 m j) = g (ggDSimple 3 m j)) : f = g := by
  refine LinearEquiv.ext fun v => ?_
  have hlin : (f : DVec m →ₗ[ZMod 3] DVec m) = (g : DVec m →ₗ[ZMod 3] DVec m) :=
    LinearMap.ext_on (p9uRMT_span_ggDSimple hm) (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact h j)
  exact congrFun (congrArg (fun L : DVec m →ₗ[ZMod 3] DVec m => (L : DVec m → DVec m)) hlin) v

private lemma p9uRMT_dNeg_last_ggDSimple (hm : 2 ≤ m) (j : Fin m) :
    dNeg m ⟨m - 1, by omega⟩ (ggDSimple 3 m j) =
      ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ j) := by
  funext k
  rw [dNeg_apply_coord]
  have hj := j.isLt
  by_cases h2 : (j : ℕ) = m - 2
  · have hjeq : j = ⟨m - 2, by omega⟩ := Fin.ext h2
    rw [hjeq, Equiv.swap_apply_left]
    simp only [ggDSimple, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega
  · by_cases h1 : (j : ℕ) = m - 1
    · have hjeq : j = ⟨m - 1, by omega⟩ := Fin.ext h1
      rw [hjeq, Equiv.swap_apply_right]
      simp only [ggDSimple, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne (fun hh => h2 (by simpa using congrArg Fin.val hh))
        (fun hh => h1 (by simpa using congrArg Fin.val hh))]
      simp only [ggDSimple, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega

private lemma p9uRMT_simpleRefl_eq_dTau (hm : 4 ≤ m) (k : Fin m) :
    (dRMLin m hm).simpleRefl k =
      dTau m (decide (k.val + 1 = m)) (OrthTorus.simpleLo k) (OrthTorus.simpleHi k) := by
  have hrefl : ∀ v : DVec m, (dRMLin m hm).simpleRefl k v =
      v - dDot m (ggDSimple 3 m k) v • ggDSimple 3 m k := fun v =>
    Module.reflection_apply v ((dRMLin m hm).root_coroot_self k)
  by_cases hk : k.val + 1 < m
  · have hne : k ≠ ⟨k.val + 1, hk⟩ := by simp [Fin.ext_iff]
    have hdec : decide (k.val + 1 = m) = false := by
      rw [decide_eq_false_iff_not]; omega
    have hlo : OrthTorus.simpleLo k = k := Fin.ext (OrthTorus.simpleLo_of_lt hk)
    have hhi : OrthTorus.simpleHi k = ⟨k.val + 1, hk⟩ :=
      Fin.ext (OrthTorus.simpleHi_of_lt hk)
    rw [hdec, hlo, hhi]
    exact eq_dTau_of_dDot_reflection false hne (by simpa using ggDSimple_chain hk) hrefl
  · have hlast : k.val + 1 = m := by have := k.isLt; omega
    have hne : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
      simp [Fin.ext_iff]; omega
    have hdec : decide (k.val + 1 = m) = true := by
      rw [decide_eq_true_eq]; omega
    have hlo : OrthTorus.simpleLo k = ⟨m - 2, by omega⟩ :=
      Fin.ext (OrthTorus.simpleLo_of_last hlast)
    have hhi : OrthTorus.simpleHi k = ⟨m - 1, by omega⟩ :=
      Fin.ext (OrthTorus.simpleHi_of_last hlast)
    rw [hdec, hlo, hhi]
    exact eq_dTau_of_dDot_reflection true hne (by simp [ggDSimple_fork hk (by omega)]) hrefl

private lemma p9uRMT_φ_simple (hm : 4 ≤ m) {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    (he : IsDEquiv m e) (i : Fin m) :
    ((e ((ggCoxeterMatrixD m).simple i) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      (dRMLin m hm).simpleRefl i := by
  rw [he i]
  exact (p9uRMT_simpleRefl_eq_dTau hm i).symm

private lemma p9uRMT_weylOf_eq (hm : 4 ≤ m) :
    ggQ2WeylOf (ggDSimple 3 m) (fun k => dDot m (ggDSimple 3 m k)) = (dRMLin m hm).weyl := by
  rw [show (dRMLin m hm).weyl =
      Subgroup.closure (Set.range (dRMLin m hm).simpleRefl) from by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]]
  unfold ggQ2WeylOf
  congr 1
  ext t
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    rw [hj v]
    exact Module.reflection_apply v ((dRMLin m hm).root_coroot_self j)
  · rintro ⟨j, rfl⟩
    refine ⟨j, fun v => ?_⟩
    exact Module.reflection_apply v ((dRMLin m hm).root_coroot_self j)

private lemma p9uRMT_dEven_eq_weyl (hm : 4 ≤ m) : dEven m = (dRMLin m hm).weyl := by
  obtain ⟨e, he⟩ := dEven_equiv hm
  let φ : (ggCoxeterMatrixD m).Group →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (dEven m).subtype.comp e.toMonoidHom
  have hφrange : φ.range = dEven m := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hg
      exact ⟨e.symm ⟨g, hg⟩, by simp [φ]⟩
  have htop : Subgroup.closure (Set.range (ggCoxeterMatrixD m).simple) =
      (⊤ : Subgroup (ggCoxeterMatrixD m).Group) :=
    PresentedGroup.closure_range_of (ggCoxeterMatrixD m).relationsSet
  have hclosure : φ.range = Subgroup.closure
      (Set.range fun i => (dRMLin m hm).simpleRefl i) := by
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (p9uRMT_φ_simple hm he i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(ggCoxeterMatrixD m).simple i, ⟨i, rfl⟩, p9uRMT_φ_simple hm he i⟩
  rw [← hφrange, hclosure]
  rw [show (dRMLin m hm).weyl =
      Subgroup.closure (Set.range (dRMLin m hm).simpleRefl) from by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]]

private lemma p9uRMT_dEven_eq_wq (hm : 4 ≤ m) :
    ggQ2WeylOf (ggDSimple 3 m) (fun k => dDot m (ggDSimple 3 m k)) = dEven m := by
  rw [p9uRMT_weylOf_eq hm, p9uRMT_dEven_eq_weyl hm]

theorem qtwoDRMStab_transfer {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ} (hm : 5 ≤ m)
    {β₀ β : Additive ↥Bs ≃+ DVec m} {J : Subgroup (MulAut ↥Bs)}
    (hJ₀ : qtwoDActsAs β₀ J (dEven m)) (hJ : qtwoDActsAs β J (dEven m))
    {A : Subgroup (MulAut ↥Bs)} {v : DVec m} (hA : qtwoDActsAs β₀ A (dEvenStab m v)) :
    ∃ T : DVec m ≃ₗ[ZMod 3] DVec m,
      (∃ (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3), (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, T (Pi.single i 1) = c i • Pi.single (σ i) 1) ∧
      (∀ b : Additive ↥Bs, β b = T (β₀ b)) ∧ qtwoDActsAs β A (dEvenStab m (T v)) := by
  classical
  have hm4 : 4 ≤ m := by omega
  let T : DVec m ≃ₗ[ZMod 3] DVec m :=
    { (β₀.symm.trans β).toAddMonoidHom.toZModLinearMap 3, β₀.symm.trans β with }
  have hTβ : ∀ b : Additive ↥Bs, T (β₀ b) = β b := by
    intro b
    change (β₀.symm.trans β) (β₀ b) = β b
    simp
  have hconj : ∀ w ∈ dEven m, T * w * T⁻¹ ∈ dEven m := by
    intro w hw
    obtain ⟨a, haJ, ha⟩ := hJ₀.2 w hw
    obtain ⟨w', hw', hw'eq⟩ := hJ.1 a haJ
    have heq : T * w * T⁻¹ = w' := by
      refine LinearEquiv.ext fun x => ?_
      obtain ⟨b, rfl⟩ := β.surjective x
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have hTinv : T⁻¹ (β b) = β₀ b := by
        rw [← hTβ b]
        exact LinearEquiv.symm_apply_apply T (β₀ b)
      have ha' : β₀ (Additive.ofMul (a (Additive.toMul b))) = w (β₀ b) := by
        simpa using ha (Additive.toMul b)
      have hw'eq' : β (Additive.ofMul (a (Additive.toMul b))) = w' (β b) := by
        simpa using hw'eq (Additive.toMul b)
      rw [hTinv, ← ha', hTβ (Additive.ofMul (a (Additive.toMul b))), hw'eq']
    rwa [heq]
  have hconj_inv : ∀ w ∈ dEven m, T⁻¹ * w * T ∈ dEven m := by
    intro w hw
    obtain ⟨a, haJ, ha⟩ := hJ.2 w hw
    obtain ⟨w', hw', hw'eq⟩ := hJ₀.1 a haJ
    have heq : T⁻¹ * w * T = w' := by
      refine LinearEquiv.ext fun x => ?_
      obtain ⟨b, rfl⟩ := β₀.surjective x
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTβ b]
      have ha' : β (Additive.ofMul (a (Additive.toMul b))) = w (β b) := by
        simpa using ha (Additive.toMul b)
      have hw'eq' : β₀ (Additive.ofMul (a (Additive.toMul b))) = w' (β₀ b) := by
        simpa using hw'eq (Additive.toMul b)
      rw [← ha']
      have hTinv : T⁻¹ (β (Additive.ofMul (a (Additive.toMul b)))) =
          β₀ (Additive.ofMul (a (Additive.toMul b))) := by
        rw [← hTβ (Additive.ofMul (a (Additive.toMul b)))]
        exact LinearEquiv.symm_apply_apply T (β₀ (Additive.ofMul (a (Additive.toMul b))))
      rw [hTinv, hw'eq']
    rwa [heq]
  have hTnormal : T ∈ Subgroup.normalizer (dEven m : Set (DVec m ≃ₗ[ZMod 3] DVec m)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact hconj w hw
    · intro hw
      have h2 : T⁻¹ * (T * w * T⁻¹) * T ∈ dEven m := hconj_inv (T * w * T⁻¹) hw
      have h3 : T⁻¹ * (T * w * T⁻¹) * T = w := by group
      rwa [h3] at h2
  have hTnorm : T ∈ Subgroup.normalizer
      (ggQ2WeylOf (ggDSimple 3 m) (fun k => dDot m (ggDSimple 3 m k)) :
        Set (DVec m ≃ₗ[ZMod 3] DVec m)) := by
    rw [p9uRMT_dEven_eq_wq hm4]
    exact hTnormal
  obtain ⟨s, -, -, hsfork, hcases⟩ :=
    ggQ2WeylNormD_fork hm (ggDSimple 3 m) (ggDSimple_linearIndependent hm4)
      (p9uRMT_span_ggDSimple hm4) (fun k => dDot m (ggDSimple 3 m k))
      (fun i j => dDot_ggDSimple hm4 i j) T hTnorm
  have hs_eq : s = dNeg m ⟨m - 1, by omega⟩ := by
    refine p9uRMT_ext_ggDSimple hm4 fun j => ?_
    rw [hsfork j]
    exact (p9uRMT_dNeg_last_ggDSimple (by omega) j).symm
  have hW := p9uRMT_dEven_eq_wq hm4
  have hTsign : p9uRMT_SignedPerm T := by
    rcases hcases with ⟨w, hw, hwT | hwT⟩ | ⟨w, hw, hwT | hwT⟩
    · have hwd : w ∈ dEven m := by rwa [hW] at hw
      exact p9uRMT_signedPerm_congr hwT (p9uRMT_signedPerm_of_dEven hwd)
    · have hwd : w ∈ dEven m := by rwa [hW] at hw
      exact p9uRMT_signedPerm_congr hwT
        (p9uRMT_signedPerm_neg (p9uRMT_signedPerm_of_dEven hwd))
    · have hwd : w ∈ dEven m := by rwa [hW] at hw
      refine p9uRMT_signedPerm_congr (fun x => ?_)
        (p9uRMT_signedPerm_comp_dNeg (g := w) (p9uRMT_signedPerm_of_dEven hwd)
          ⟨m - 1, by omega⟩)
      rw [hwT x, hs_eq]
    · have hwd : w ∈ dEven m := by rwa [hW] at hw
      refine p9uRMT_signedPerm_congr (fun x => ?_)
        (p9uRMT_signedPerm_neg (p9uRMT_signedPerm_comp_dNeg (g := w)
          (p9uRMT_signedPerm_of_dEven hwd) ⟨m - 1, by omega⟩))
      rw [hwT x, hs_eq]
  refine ⟨T, ?_, fun b => (hTβ b).symm, ?_⟩
  · simpa [p9uRMT_SignedPerm] using hTsign
  · refine ⟨?_, ?_⟩
    · intro a haA
      obtain ⟨w, hw, hwact⟩ := hA.1 a haA
      refine ⟨T * w * T⁻¹, ⟨hconj w hw.1, ?_⟩, ?_⟩
      · change (T * w * T⁻¹) (T v) = T v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        rw [show T⁻¹ (T v) = v from LinearEquiv.symm_apply_apply T v, hw.2]
      · intro b
        rw [← hTβ (Additive.ofMul (a b)), hwact b, LinearEquiv.mul_apply,
          LinearEquiv.mul_apply]
        congr 1
        rw [← hTβ (Additive.ofMul b)]
        exact congrArg w (LinearEquiv.symm_apply_apply T (β₀ (Additive.ofMul b))).symm
    · intro w hw
      have hw₀ : T⁻¹ * w * T ∈ dEvenStab m v := by
        refine ⟨hconj_inv w hw.1, ?_⟩
        change (T⁻¹ * w * T) v = v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hw.2]
        exact LinearEquiv.symm_apply_apply T v
      obtain ⟨a, haA, hact⟩ := hA.2 (T⁻¹ * w * T) hw₀
      refine ⟨a, haA, fun b => ?_⟩
      rw [← hTβ (Additive.ofMul (a b)), hact b, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, hTβ (Additive.ofMul b)]
      rw [show T (T⁻¹ (w (β (Additive.ofMul b)))) = w (β (Additive.ofMul b)) from
        LinearEquiv.apply_symm_apply T (w (β (Additive.ofMul b)))]

end CFSG.StandardType.QTwo

end
