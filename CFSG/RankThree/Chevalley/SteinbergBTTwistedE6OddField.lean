module

public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBT
open CFSG.LieType.Chevalley.FieldGraphFieldPointwise

section Data

variable (t : TwistTag) {K : Type} [Field K]

@[expose] def subfieldRootGroupImage (k : Subfield K) (σ₀ : k ≃+* k) :
    Subgroup (ModGL t.tag K) :=
  (graphFixedRootGroup t k σ₀.toRingHom).map (baseChangeGL k.subtype)

@[expose] def subfieldRootGroupInner (σ : K ≃+* K) (k : Subfield K) (σ₀ : k ≃+* k) :
    Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)) :=
  ((subfieldRootGroupImage t k σ₀).subgroupOf (graphFixedRootGroup t K σ.toRingHom)).map
    MulAut.conj

end Data

theorem exists_fieldActor_eq_of_fix_regular_E6 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {w₀ : WeylGroup TwistTag.E6.tag}
    (hw₀ : ∀ w, (coxeterSystem TwistTag.E6.tag).length w ≤
      (coxeterSystem TwistTag.E6.tag).length w₀)
    {n₀ u₀ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hn₀ : (n₀ : ModGL TwistTag.E6.tag K) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀)
    (hu₀ : (u₀ : ModGL TwistTag.E6.tag K) = regularElt K)
    {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hβu : β u₀ = u₀)
    (hβv : β (n₀ * u₀ * n₀⁻¹) = n₀ * u₀ * n₀⁻¹) :
    ∃ η : K ≃+* K, β = fieldActor σ η := by
  obtain ⟨-, -, -, -, -, hΔ, -, hex, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  obtain ⟨g, u, η, rfl⟩ := hex β
  have hCadj : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    fun x => twistedFixedGroup_le_adjointGroup _ _ _ (graphFixedRootGroup_le _ _ _ x.2)
  let ι : graphFixedRootGroup TwistTag.E6 K σ.toRingHom → adjointGroup TwistTag.E6.tag K :=
    fun x => ⟨x, hCadj x⟩
  set β' : MulAut (adjointGroup TwistTag.E6.tag K) := MulAut.conj (ι g) *
    exactNormalAut TwistTag.E6.tag K (compatDiag TwistTag.E6 σ.toRingHom u) η 0 with hβ'
  have hext : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ η :
        MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) x :
          graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
        β' (ι x) := by
    intro x
    simp only [hβ', MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hΔ, coe_fieldActor, coe_exactNormalAut_zero]
  have hβu' : β' (ι u₀) = ι u₀ := Subtype.ext ((hext u₀).symm.trans (congrArg Subtype.val hβu))
  have hβv' : β' (ι n₀ * ι u₀ * (ι n₀)⁻¹) = ι n₀ * ι u₀ * (ι n₀)⁻¹ := Subtype.ext
    ((hext (n₀ * u₀ * n₀⁻¹)).symm.trans (congrArg Subtype.val hβv))
  obtain ⟨a, φ, e, hβ'eq⟩ := exists_exactNormalAut_eq_of_fix_regular (τ := TwistTag.E6.tag)
    (Or.inl rfl) hw₀ (n₀ := ι n₀) (u := ι u₀) (β := β') hn₀
    (show (u₀ : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K by
      rw [hu₀]
      exact regularElt_mem_posUnipotent)
    (fun j => show rootCoord (single_pos j) (u₀ : ModGL TwistTag.E6.tag K) ≠ 0 by
      rw [hu₀, rootCoord_regularElt]
      exact one_ne_zero) hβu' hβv'
  have hreg : ι u₀ = regularElt K := Subtype.ext hu₀
  have he : (e : ℕ) = 0 ∨ (e : ℕ) = 1 := by
    have h := e.isLt
    change (e : ℕ) < 2 at h
    omega
  obtain ⟨φ', hφ'⟩ : ∃ φ' : K ≃+* K, ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      β' (ι x) = exactNormalAut TwistTag.E6.tag K a φ' 0 (ι x) := by
    rcases he with he | he
    · exact ⟨φ, fun x => by rw [hβ'eq, he]⟩
    · refine ⟨φ * σ, fun x => ?_⟩
      have h := DFunLike.congr_fun (exactNormalAut_one_mul_graphField a φ σ) (ι x)
      rw [MulAut.mul_apply, graphField_apply σ (j := ι x) x.2] at h
      rw [hβ'eq, he]
      exact h
  have ha : a = 1 := eq_one_of_exactNormalAut_zero_fix (by rw [← hreg, ← hφ', hβu'])
  subst ha
  refine ⟨φ', MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [hext, hφ', exactNormalAut_one_zero_eq, coe_entrywiseAdjointAut, coe_fieldActor]

theorem twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer {ℓ d m : ℕ}
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hm : 3 ≤ m) (hmodd : Odd m) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * d * m)) (κ : K ≃+* K) (hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (d * m)) (σ₀ : fixSubfield κ ≃+* fixSubfield κ)
    (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ d) (ε : K ≃+* K)
    (hε : ∀ c, ε c = c ^ ℓ ^ (d * (m + 1))) :
    (∀ c : K, c ∈ fixSubfield κ ↔ c ^ ℓ ^ (2 * d) = c) ∧
      Nat.card (fixSubfield κ) = ℓ ^ (2 * d) ∧
      subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ ≤
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
      orderOf (fieldActor (t := TwistTag.E6) σ ε) = m ∧
      ⁅MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom
          (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
        MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom
          (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))⁆ =
        (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
      IsSimpleGroup (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) ∧
      (¬∀ a b : subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀, a * b = b * a) ∧
      (∃ ι : ↥((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ≃*
          ↥(subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀),
        ∀ j, (ι j : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) =
          MulAut.conj (j : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ∧
      subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀ ≤
        Subgroup.centralizer {fieldActor σ ε} ∧
      ((subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀).subgroupOf
        (Subgroup.centralizer {fieldActor σ ε})).Normal ∧
      Subgroup.centralizer {fieldActor σ ε} ⊓
          Subgroup.centralizer (subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀ :
            Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) =
        Subgroup.zpowers (fieldActor σ ε) ∧
      Nat.card (Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε)) = m := by
  classical
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set ι : fixSubfield κ →+* K := (fixSubfield κ).subtype with hιdef
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  have : Finite (fixSubfield κ) := Subtype.finite
  have hdm : 1 ≤ d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2dm : 1 ≤ 2 * d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨j, hj⟩ := hmodd
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ h2dm
      hK
  have hfr1 : fr ^ (2 * d * m) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one fr
  have hσfr : σ = fr ^ (d * m) := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr]
  have hκfr : κ = fr ^ (2 * d) := RingEquiv.ext fun c => by
    rw [hκ, ringAut_pow_apply_of_frobenius hfr]
  have hεfr : ε = fr ^ (d * (m + 1)) := RingEquiv.ext fun c => by
    rw [hε, ringAut_pow_apply_of_frobenius hfr]
  have hκε : κ = ε ^ 2 := by
    rw [hκfr, hεfr, ← pow_mul, show d * (m + 1) * 2 = 2 * d * m + 2 * d by ring, pow_add, hfr1,
      one_mul]
  have hεκ : ε = κ ^ (j + 1) := by
    rw [hεfr, hκfr, ← pow_mul, hj, show d * (2 * j + 1 + 1) = 2 * d * (j + 1) by ring]
  have hσκ : σ = fr ^ d * κ ^ j := by
    rw [hσfr, hκfr, ← pow_mul, ← pow_add, hj, show d * (2 * j + 1) = d + 2 * d * j by ring]
  have hψ : σ * ε = fr ^ d := by
    rw [hσfr, hεfr, ← pow_add, show d * m + d * (m + 1) = 2 * d * m + d by ring, pow_add, hfr1,
      one_mul]
  have hfrd : ∀ c, (fr ^ d) c = c ^ ℓ ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hstab : ∀ (φ : K ≃+* K) (c : K), φ c = c → ∀ n : ℕ, (φ ^ n) c = c := by
    intro φ c h n
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, h]
  have hεK₀ : ∀ c, κ c = c → ε c = c := fun c hc => by
    rw [hεκ]
    exact hstab κ c hc _
  have hκK₀ : ∀ c, ε c = c → κ c = c := fun c hc => by
    rw [hκε]
    exact hstab ε c hc 2
  have hσK₀ : ∀ c, κ c = c → σ c = c ^ ℓ ^ d := fun c hc => by
    rw [hσκ, RingAut.mul_apply, hstab κ c hc j, hfrd]
  have hψc : ∀ c, (σ * ε) c = c ^ ℓ ^ d := fun c => by rw [hψ, hfrd]
  have hκord : orderOf κ = m := by
    rw [hκfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro m rfl), hord,
      Nat.mul_div_cancel_left m (by omega)]
  have hεord : orderOf ε = m := by
    rw [← hκord]
    refine Nat.dvd_antisymm (orderOf_dvd_of_mem_zpowers ?_) (orderOf_dvd_of_mem_zpowers ?_)
    · rw [hεκ]
      exact Subgroup.npow_mem_zpowers κ (j + 1)
    · rw [hκε]
      exact Subgroup.npow_mem_zpowers ε 2
  obtain ⟨-, hk⟩ := card_fixSubfield hℓ h2dm hK κ
  rw [hκord, Nat.mul_div_cancel _ (by omega)] at hk
  have hσ₀' : ∀ c : fixSubfield κ, σ₀.toRingHom c = c ^ ℓ ^ d := fun c => Subtype.ext (by
    change (σ₀ c : K) = _
    rw [hσ₀, SubmonoidClass.coe_pow])
  have hσ₀σ₀ : ∀ c : fixSubfield κ, σ₀ (σ₀ c) = c := fun c => Subtype.ext (by
    rw [hσ₀, hσ₀, ← pow_mul, ← pow_add, show d + d = 2 * d by ring, ← hκ]
    exact c.2)
  have hσι : ∀ c : fixSubfield κ, σ.toRingHom (ι c) = ι (σ₀.toRingHom c) := fun c => by
    change σ c = (σ₀ c : K)
    rw [hσ₀, hσK₀ c c.2]
  have hψι : ∀ c : fixSubfield κ, (σ * ε).toRingHom (ι c) = ι (σ₀.toRingHom c) := fun c => by
    change (σ * ε) c = (σ₀ c : K)
    rw [hσ₀, hψc]
  have hJC : J ≤ C := map_baseChangeGL_graphFixedRootGroup_le (σ := σ₀.toRingHom)
    (Fr := σ.toRingHom) (ι := ι) σ₀.surjective hσι
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.E6 K (σ * ε).toRingHom a,
      ∃ c₀ ∈ orbitField TwistTag.E6 (fixSubfield κ) σ₀.toRingHom a, ι c₀ = c := by
    intro a c hc
    have h2 : (σ * ε) ((σ * ε) c) = c := by
      rw [mem_orbitField] at hc
      obtain ⟨n, hn⟩ := a
      have hn' : n < 4 := hn
      interval_cases n
      · rw [show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two] at hc
        exact hc
      · rw [show (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 by decide, pow_two] at hc
        exact hc
      · rw [show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide, pow_one] at hc
        change (σ * ε) c = c at hc
        rw [hc, hc]
      · rw [show (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 by decide, pow_one] at hc
        change (σ * ε) c = c at hc
        rw [hc, hc]
    have hck : κ c = c := by
      rw [hψc, hψc, ← pow_mul, ← pow_add, show d + d = 2 * d by ring] at h2
      rw [hκ]
      exact h2
    obtain ⟨c₀, rfl⟩ : ∃ c₀ : fixSubfield κ, ι c₀ = c := ⟨⟨c, hck⟩, rfl⟩
    refine ⟨c₀, ?_, rfl⟩
    rw [mem_orbitField] at hc ⊢
    apply ι.injective
    rw [← ringHom_pow_apply_comm hψι, hc]
  have hC0J : graphFixedRootGroup TwistTag.E6 K (σ * ε).toRingHom = J :=
    le_antisymm (graphFixedRootGroup_le_map_baseChangeGL (σ := σ₀.toRingHom)
        (Fr := (σ * ε).toRingHom) (ι := ι) (σ * ε).surjective hψι hpar)
      (map_baseChangeGL_graphFixedRootGroup_le (σ := σ₀.toRingHom) (Fr := (σ * ε).toRingHom)
        (ι := ι) σ₀.surjective hψι)
  have hK₀' : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ TwistTag.E6.order := by
    rw [hk, show TwistTag.E6.order = 2 from rfl, ← pow_mul, mul_comm]
  obtain ⟨hperf₀, -⟩ := finite_fixed_root_group_perfect TwistTag.E6 hℓ hd (fixSubfield κ) hK₀'
    σ₀.toRingHom hσ₀'
  have hJperf : ⁅J, J⁆ = J := by
    rw [hJdef, subfieldRootGroupImage, ← Subgroup.map_commutator, hperf₀]
  have hsimple₀ :=
    isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.E6 (fixSubfield κ) σ₀ hperf₀
  have hιinj : Function.Injective (baseChangeGL (τ := TwistTag.E6.tag) ι) :=
    baseChangeGL_injective _
  set e := Subgroup.equivMapOfInjective
    (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom) _ hιinj with he
  have hsimpleJ : IsSimpleGroup J := by
    have := hsimple₀.1
    exact e.symm.isSimpleGroup
  have hncJ : ¬∀ a b : J, a * b = b * a := by
    intro h
    obtain ⟨x, y, hxy⟩ := hsimple₀.2
    apply hxy
    apply e.injective
    rw [map_mul, map_mul]
    exact h _ _
  have hZ : Subgroup.center C = ⊥ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hK' : Nat.card K = (ℓ ^ (d * m)) ^ 2 := by
    rw [hK, ← pow_mul, show d * m * 2 = 2 * d * m by ring]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hdm K hK' σ hσ
  have hactinj : Function.Injective (fieldActorHom (t := TwistTag.E6) σ) := by
    rw [injective_iff_map_eq_one]
    intro φ h
    have h1 := hΘ (fieldActor σ φ) 1 1 φ (by rw [map_one, map_one, one_mul, one_mul])
    rw [← fieldActorHom_apply, h, map_one] at h1
    exact h1.symm
  have hδord : orderOf δ = m := by
    rw [hδdef, ← fieldActorHom_apply, orderOf_injective _ hactinj ε, hεord]
  set Γ := MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C) with hΓdef
  have hJΓ : J.subgroupOf C ≤ Γ := by
    intro x hx
    obtain ⟨y, -, hy⟩ := Subgroup.mem_subgroupOf.1 hx
    refine Subtype.ext ?_
    change Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x
    rw [← hy]
    have hcomp : ε.toRingHom.comp ι = ι := RingHom.ext fun c => hεK₀ c c.2
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]
  have hΓψ : Γ.map C.subtype ≤ twistedFixedGroup TwistTag.E6 K (σ * ε).toRingHom := by
    rintro _ ⟨g, hg, rfl⟩
    have hδg : Units.map (entrywiseHom ε.toRingHom) (g : ModGL TwistTag.E6.tag K) = g :=
      congrArg Subtype.val hg
    have hgσ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le _ _ _ g.2)
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (σ * ε).toRingHom).2 ⟨hgσ.1, ?_⟩
    rw [twistHom_apply] at hgσ ⊢
    rw [show (σ * ε).toRingHom = σ.toRingHom.comp ε.toRingHom from RingHom.ext fun _ => rfl,
      ← units_map_entrywiseHom_comp, Subgroup.coe_subtype, hδg]
    exact hgσ.2
  have hJsub : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
    rw [commutator_subgroupOf_eq hJC, hJperf]
  have hder : ⁅Γ, Γ⁆ = J.subgroupOf C := by
    refine le_antisymm (fun x hx => ?_) ((le_of_eq hJsub.symm).trans
      (Subgroup.commutator_mono hJΓ hJΓ))
    have h1 : (x : ModGL TwistTag.E6.tag K) ∈ (⁅Γ, Γ⁆).map C.subtype := ⟨x, hx, rfl⟩
    rw [Subgroup.map_commutator] at h1
    have h2 := commutator_twistedFixedGroup_le (t := TwistTag.E6) (σ := (σ * ε).toRingHom)
      (σ * ε).surjective (Subgroup.commutator_mono hΓψ hΓψ h1)
    rw [hC0J] at h2
    exact Subgroup.mem_subgroupOf.2 h2
  obtain ⟨-, hle, hnormal⟩ := derivedFixed_inner_normal hZ hder
  have hregι : (regularElt K : ModGL TwistTag.E6.tag K) =
      baseChangeGL ι (regularElt (fixSubfield κ) : ModGL TwistTag.E6.tag (fixSubfield κ)) := by
    rw [coe_regularElt (K := K), coe_regularElt (K := fixSubfield κ), map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    rw [Function.comp_apply, baseChangeGL_xUnit, map_one]
  have hfixpow : ∀ β : MulAut C, (∀ x : C, (x : ModGL TwistTag.E6.tag K) ∈ J → β x = x) →
      β ∈ Subgroup.zpowers δ := by
    intro β hβ
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
    obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.E6
    rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
    have hn₀J : canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ ∈ J :=
      ⟨_, canonicalRep_mem_graphFixedRootGroup (K := fixSubfield κ) (σ := σ₀.toRingHom) hw₁,
        baseChangeGL_canonicalRep ι w₀⟩
    have hu₀J : (regularElt K : ModGL TwistTag.E6.tag K) ∈ J :=
      ⟨_, regularElt_mem_graphFixedRootGroup (K := fixSubfield κ) σ₀.toRingHom, hregι.symm⟩
    obtain ⟨η, rfl⟩ := exists_fieldActor_eq_of_fix_regular_E6 hℓ hdm hK' σ hσ hw₀
      (n₀ := ⟨_, hJC hn₀J⟩) (u₀ := ⟨_, hJC hu₀J⟩) rfl rfl (hβ _ hu₀J)
      (hβ _ (mul_mem (mul_mem hn₀J hu₀J) (inv_mem hn₀J)))
    have hηK₀ : ∀ c, ε c = c → η c = c := by
      intro c hc
      have hck : κ c = c := hκK₀ c hc
      have hc₀ : (⟨c, hck⟩ : fixSubfield κ) ∈
          orbitField TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ := by
        rw [mem_orbitField, show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two]
        exact hσ₀σ₀ _
      have hy := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩)
      have hyJ : baseChangeGL ι
          (orbitX TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩ :
            ModGL TwistTag.E6.tag (fixSubfield κ)) ∈ J := ⟨_, hy, rfl⟩
      have h1 : Units.map (entrywiseHom η.toRingHom) (baseChangeGL ι
          (orbitX TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩ :
            ModGL TwistTag.E6.tag (fixSubfield κ))) = baseChangeGL ι
          (orbitX TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ⟨0, by decide⟩ ⟨_, hc₀⟩ :
            ModGL TwistTag.E6.tag (fixSubfield κ)) :=
        congrArg Subtype.val (hβ ⟨_, hJC hyJ⟩ hyJ)
      simp only [coe_orbitX_zero, map_mul, baseChangeGL_xUnit, units_map_entrywiseHom_xUnit] at h1
      have h2 := congrArg (rootCoord (single_pos (τ := TwistTag.E6.tag) ⟨0, by decide⟩)) h1
      simp only [rootCoord_single_xUnit_mul_xUnit] at h2
      simpa [hιdef] using h2
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1
      (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hηK₀)
    exact Subgroup.mem_zpowers_iff.2
      ⟨n, (map_zpow (fieldActorHom (t := TwistTag.E6) σ) ε n).symm⟩
  have hcent := centralizer_inf_eq_zpowers_of_fix hZ hle hfixpow
  refine ⟨fun c => by rw [mem_fixSubfield, hκ], hk, hJC, hδord, hder, hsimpleJ, hncJ,
    ⟨(J.subgroupOf C).equivMapOfInjective _ hinj, fun j => rfl⟩, hle, hnormal, hcent,
    by rw [Nat.card_zpowers, hδord]⟩

end CFSG.RankThree.Chevalley
