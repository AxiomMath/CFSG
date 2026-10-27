module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsModule
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeRee
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public noncomputable section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped IsMulCommutative commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

section BaseChange

variable {k K : Type} [Field k] [Field K]

theorem baseChangeGL_letter
    (f : k →+* K) (l : Letter) :
    baseChangeGL f ((l.elt k : adjointGroup ReeTag.F4.tag k) : ModGL ReeTag.F4.tag k) =
      ((l.elt K : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
  cases l with
  | x i =>
    change baseChangeGL f (xUnit ReeTag.F4.tag k (idx i) 1) = xUnit ReeTag.F4.tag K (idx i) 1
    rw [baseChangeGL_xUnit, map_one]
  | n i =>
    change baseChangeGL f (weylElt ReeTag.F4.tag k (idx i) 1) = weylElt ReeTag.F4.tag K (idx i) 1
    exact baseChangeGL_weylElt_one f (idx i)

theorem baseChangeGL_evalG
    (f : k →+* K) : ∀ w : List Letter,
    baseChangeGL f ((evalG k w : adjointGroup ReeTag.F4.tag k) : ModGL ReeTag.F4.tag k) =
      ((evalG K w : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K)
  | [] => by simp [map_one]
  | l :: w => by
    rw [evalG_cons, evalG_cons, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, baseChangeGL_letter,
      baseChangeGL_evalG f w]


variable [Finite k] [Finite K] [CharP k ReeTag.F4.prime] [CharP K ReeTag.F4.prime]

theorem baseChangeGL_genG
    (f : k →+* K) (s : ℕ) :
    baseChangeGL f ((genG k s : adjointGroup ReeTag.F4.tag k) : ModGL ReeTag.F4.tag k) =
      ((genG K s : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
  rw [genG_eq_evalG, genG_eq_evalG]
  exact baseChangeGL_evalG f _

theorem baseChangeGL_gEltG
    (f : k →+* K) (l : ℤ) :
    baseChangeGL f (((gEltG k l : reeFixed ReeTag.F4 k 0) : adjointGroup ReeTag.F4.tag k) :
      ModGL ReeTag.F4.tag k) =
      (((gEltG K l : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) := by
  unfold gEltG
  split_ifs
  · exact baseChangeGL_genG f _
  · simp only [Subgroup.coe_inv, map_inv]
    rw [baseChangeGL_genG f _]

theorem baseChangeGL_gWordG
    (f : k →+* K) : ∀ w : List ℤ,
    baseChangeGL f (((gWordG k w : reeFixed ReeTag.F4 k 0) : adjointGroup ReeTag.F4.tag k) :
      ModGL ReeTag.F4.tag k) =
      (((gWordG K w : reeFixed ReeTag.F4 K 0) : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K)
  | [] => by simp [gWordG_nil, map_one]
  | l :: w => by
    rw [gWordG_cons, gWordG_cons, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, map_mul, baseChangeGL_gEltG, baseChangeGL_gWordG f w]

theorem baseChangeGL_cElt
    (f : k →+* K) (pr : List ℤ × List ℤ) :
    baseChangeGL f (((⁅gWordG k pr.1, gWordG k pr.2⁆ : reeFixed ReeTag.F4 k 0) :
      adjointGroup ReeTag.F4.tag k) : ModGL ReeTag.F4.tag k) =
      ((cElt K pr : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
  rw [cElt, commutatorElement_def, commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, baseChangeGL_gWordG]

end BaseChange


section TwoGroup

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem largeRee_twoGroup_eq_bot
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K) :
    ∀ E : Subgroup ↥(ReeTag.F4.reeGamma K a), IsPGroup ReeTag.F4.prime E →
      (∀ j ∈ signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ), ∀ e ∈ E,
        j * e * j⁻¹ ∈ E) → E = ⊥ := by
  classical
  have hp2 : Nat.Prime ReeTag.F4.prime := Nat.prime_two
  have : Fact ReeTag.F4.prime.Prime := ⟨hp2⟩
  set Γ := ReeTag.F4.reeGamma K a with hΓ
  set J₀ := signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) with hJ₀
  set Jamb : Subgroup (ModGL ReeTag.F4.tag K) := J₀.map Γ.subtype with hJamb
  have hXC : Γ ≤ adjointGroup ReeTag.F4.tag K := fun g hg => (ReeTag.mem_reeGamma.1 hg).1
  have hJX : Jamb ≤ Γ := Subgroup.map_subtype_le _
  have hsub : Jamb.subgroupOf Γ = J₀ :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective J₀
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.F4.tag
  have hJmem : ∀ g : ModGL ReeTag.F4.tag K, g ∈ Γ → g ∈ fixedFieldImage ReeTag.F4.tag σ →
      g ∈ Jamb := fun g hg hgf =>
    ⟨⟨g, hg⟩, Subtype.ext (by
      rw [ReeTag.coe_reeGammaFieldAut]
      exact (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hgf)).2), rfl⟩
  have hu₁Γ : xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1 ∈
      Γ := (Subgroup.mem_inf.1 (ReeTag.f4_fixedBlock_one K a).1).2
  have hu₁F : xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1 ∈
      fixedFieldImage ReeTag.F4.tag σ :=
    mul_mem (xUnit_mem_fixedFieldImage _ (map_one σ)) (xUnit_mem_fixedFieldImage _ (map_one σ))
  have hu₁U : xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1 ∈
      posUnipotent ReeTag.F4.tag K :=
    mul_mem (LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
      (LieType.Chevalley.xUnit_mem_posUnipotent _ 1)
  have hyBΓ : (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K) ∈ Γ :=
    (Subgroup.mem_inf.1 ((ReeTag.bijOn_largeReeCoord hK).1 (Set.mem_univ ((1 : K), (0 : K))))).2
  have hyBU : (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K) ∈
      posUnipotent ReeTag.F4.tag K := by
    unfold ReeTag.largeReeCoord largeReeP largeReeX
    refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;>
      exact pinnedX_mem_rootSpan (S := {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α})
        (largeReeRoot_pos _) _
  have hnΓ : canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ ∈ Γ :=
    (Subgroup.mem_inf.1 (ReeTag.canonicalRep_longest_mem_reeFixedMonomial (t := ReeTag.F4)
      (K := K) (a := a) hw₀)).2
  have hn : canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀ ∈ Jamb :=
    ⟨⟨_, hnΓ⟩, Subtype.ext (by
      rw [ReeTag.coe_reeGammaFieldAut]
      exact entrywise_canonicalRep σ w₀), rfl⟩
  let y : Fin ReeTag.F4.tag.rank → ModGL ReeTag.F4.tag K := fun i =>
    if i.val = 0 ∨ i.val = 3 then
      xUnit ReeTag.F4.tag K ⟨0, by decide⟩ 1 * xUnit ReeTag.F4.tag K ⟨3, by decide⟩ 1
    else (ReeTag.largeReeCoord a K 1 0 : ModGL ReeTag.F4.tag K)
  have hyJ : ∀ i, y i ∈ Jamb := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [y, hi, ↓reduceIte]
      exact hJmem _ hu₁Γ hu₁F
    · simp only [y, hi, ↓reduceIte]
      exact hJmem _ hyBΓ (largeReeCoord_one_mem_fixedFieldImage σ)
  have hyU : ∀ i, y i ∈ posUnipotent ReeTag.F4.tag K := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [y, hi, ↓reduceIte]
      exact hu₁U
    · simp only [y, hi, ↓reduceIte]
      exact hyBU
  have hco : ∀ i, HasCoord i (y i) 1 := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = 3
    · simp only [y, hi, ↓reduceIte]
      exact hasCoord_xUnit_xUnit_one i hi
    · simp only [y, hi, ↓reduceIte]
      refine hasCoord_largeReeCoord_one a i ?_
      have := i.2
      change i.val < 4 at this
      omega
  intro E hE hnorm
  have hWr : IsPGroup ReeTag.F4.prime (E.map Γ.subtype) := hE.map _
  have hWC : E.map Γ.subtype ≤ adjointGroup ReeTag.F4.tag K := by
    rintro _ ⟨e, -, rfl⟩
    exact hXC e.2
  have hbot := eq_bot_of_isPGroup_of_normalized_regular (τ := ReeTag.F4.tag) ReeTag.F4.prime
    (hJX.trans hXC) hWC hWr hyJ hyU (c := fun _ => 1) (fun _ => one_ne_zero) hco hw₀ hn
    (fun j hj w hw => by
      obtain ⟨e, he, rfl⟩ := hw
      have hj' : (⟨j, hJX hj⟩ : ↥Γ) ∈ J₀ := by
        rw [← hsub]
        exact Subgroup.mem_subgroupOf.2 hj
      exact ⟨_, hnorm _ hj' e he, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).1 hbot

end TwoGroup


section Iso

variable {G : Type*} [Group G] {G₁ : Type*} [Group G₁]

@[expose] def isoOfMapEq (Γ : Subgroup G) (J : Subgroup Γ) (M : Subgroup G₁) (f : G₁ →* G)
    (hf : Function.Injective f) (h : J.map Γ.subtype = M.map f) : J ≃* M :=
  ((J.equivMapOfInjective Γ.subtype Γ.subtype_injective).trans (MulEquiv.subgroupCongr h)).trans
    (M.equivMapOfInjective f hf).symm

theorem isoOfMapEq_val (Γ : Subgroup G) (J : Subgroup Γ) (M : Subgroup G₁) (f : G₁ →* G)
    (hf : Function.Injective f) (h : J.map Γ.subtype = M.map f) (x : J) :
    f ((isoOfMapEq Γ J M f hf h x : M) : G₁) = ((x : Γ) : G) := by
  set z : M.map f := MulEquiv.subgroupCongr h
    (J.equivMapOfInjective Γ.subtype Γ.subtype_injective x) with hz
  have h2 : f (((M.equivMapOfInjective f hf).symm z : M) : G₁) = ((z : M.map f) : G) := by
    have := congrArg Subtype.val ((M.equivMapOfInjective f hf).apply_symm_apply z)
    rwa [Subgroup.coe_equivMapOfInjective_apply] at this
  change f (((M.equivMapOfInjective f hf).symm z : M) : G₁) = _
  rw [h2]
  rfl

end Iso

section OddGroup

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem largeRee_oddGroup_eq_bot
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpa : p = 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) :
    ∀ E : Subgroup ↥(ReeTag.F4.reeGamma K a), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ s = 1) →
      (∀ j ∈ signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ), ∀ e ∈ E,
        j * e * j⁻¹ ∈ E) → E = ⊥ := by
  classical
  intro E hEcomm hEexp hnorm
  obtain ⟨hpf, hcard⟩ := card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσ] at hpf hcard
  have hk2 : Nat.card (fixSubfield σ) = 2 := by
    rw [hcard, hpa, Nat.div_self (by omega), pow_one]
  obtain ⟨b, hkcard, hfixed⟩ := largeRee_fixed_data ha hK hp hp3 σ hσ
  have hb : b = 0 := by
    have h1 : 2 ^ (2 * b + 1) = 2 ^ 1 := by rw [← hkcard, hk2, pow_one]
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hb
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * 0 + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinj : Function.Injective (baseChangeGL (τ := ReeTag.F4.tag) (fixSubfield σ).subtype) :=
    baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype
  have hFix : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃*
      ReeTag.F4.reeGamma (fixSubfield σ) 0 :=
    isoOfMapEq (ReeTag.F4.reeGamma K a) _ (ReeTag.F4.reeGamma (fixSubfield σ) 0)
      (baseChangeGL (fixSubfield σ).subtype) hinj (by rw [hFix]; exact hfixed)
  have heC : ∀ x : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ),
      baseChangeGL (fixSubfield σ).subtype
        ((eC x : ReeTag.F4.reeGamma (fixSubfield σ) 0) : ModGL ReeTag.F4.tag (fixSubfield σ)) =
        (((x : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K)) := fun x =>
    isoOfMapEq_val _ _ _ _ hinj _ x
  have hXC : ReeTag.F4.reeGamma K a ≤ adjointGroup ReeTag.F4.tag K := fun g hg =>
    (ReeTag.mem_reeGamma.1 hg).1
  let Φ : reeFixed ReeTag.F4 (fixSubfield σ) 0 ≃*
      signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) :=
    (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).trans eC.symm
  let ι : reeFixed ReeTag.F4 (fixSubfield σ) 0 →* ↥(ReeTag.F4.reeGamma K a) :=
    (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).subtype.comp Φ.toMonoidHom
  have hιval : ∀ t : reeFixed ReeTag.F4 (fixSubfield σ) 0,
      ((ι t : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        baseChangeGL (fixSubfield σ).subtype
          ((t : adjointGroup ReeTag.F4.tag (fixSubfield σ)) :
            ModGL ReeTag.F4.tag (fixSubfield σ)) := by
    intro t
    have h := heC (eC.symm (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0 t))
    rw [MulEquiv.apply_symm_apply, ReeTag.coe_reeFixedEquivReeGamma] at h
    exact h.symm
  let F := AlgebraicClosure K
  have hFr : CharP F ReeTag.F4.prime :=
    charP_of_injective_algebraMap (algebraMap K F).injective _
  have : Fintype ↥(ReeTag.F4.shortLabels) := Fintype.ofFinite _
  have hp0 : ((ReeTag.F4.prime : ℕ) : K) = 0 := CharP.cast_eq_zero K ReeTag.F4.prime
  let ρ₀ : ↥(ReeTag.F4.reeGamma K a) →* Module.End K (ReeTag.F4.shortModule K) :=
    (ReeTag.shortRestrictHom ReeTag.F4 K hp0).comp (Subgroup.inclusion hXC)
  have hρ₀ : Function.Injective ρ₀ :=
    (shortRestrictHom_injective ReeTag.F4).comp (Subgroup.inclusion_injective hXC)
  let ρ : ↥(ReeTag.F4.reeGamma K a) →* Module.End F (↥ReeTag.F4.shortLabels → F) :=
    matrixRep F (ReeTag.F4.shortBasis K) ρ₀
  have hρ : Function.Injective ρ := matrixRep_injective F _ hρ₀
  have hdim : Module.finrank F (↥ReeTag.F4.shortLabels → F) = 26 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card, ReeTag.card_shortLabels]
    rfl
  have hEc : IsMulCommutative E := ⟨⟨fun x y => Subtype.ext (hEcomm _ x.2 _ y.2)⟩⟩
  have : Finite E := Subtype.finite
  have hinv : (Nat.card E : F) ≠ 0 :=
    cast_card_ne_zero_of_exponent (r := ReeTag.F4.prime) Nat.prime_two hs hs2 hEexp
  obtain ⟨hfinE, hcardE⟩ := finite_card_weights ρ E hEc
  have := hfinE
  have hnormι : ∀ g, ∀ v ∈ E, ι g * v * (ι g)⁻¹ ∈ E := fun g v hv => hnorm _ (Φ g).2 v hv
  have hπcard : Nat.card (Wt ρ E) < 32 := by
    have h26 : Nat.card (Wt ρ E) ≤ 26 := by
      rw [hdim] at hcardE
      exact hcardE
    omega
  have hker := titsGamma_commutator_le_ker hk2 hπcard (weightAction ρ E ι hnormι)
  have hcommElt : ∀ pr ∈ modStab ++ modSpan, ∀ v : ↥(ReeTag.F4.reeGamma K a), v ∈ E →
      cElt K pr * (⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ : adjointGroup ReeTag.F4.tag K) =
        (⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ : adjointGroup ReeTag.F4.tag K) * cElt K pr := by
    intro pr hpr v hv
    have htc : (⁅gWordG (fixSubfield σ) pr.1, gWordG (fixSubfield σ) pr.2⁆ :
        reeFixed ReeTag.F4 (fixSubfield σ) 0) ∈
        commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hπt := hker htc
    have hc := centralizes_of_weightAction_eq_one ρ hρ E hEc hinv ι hnormι _ hπt v hv
    have h1 : ((ι ⁅gWordG (fixSubfield σ) pr.1, gWordG (fixSubfield σ) pr.2⁆ :
        ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        ((cElt K pr : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
      rw [hιval, baseChangeGL_cElt]
    have h2 := congrArg (fun z : ↥(ReeTag.F4.reeGamma K a) => (z : ModGL ReeTag.F4.tag K)) hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h1] at h2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hscal : ∀ v : ↥(ReeTag.F4.reeGamma K a), v ∈ E →
      ∃ c : K, ∀ u ∈ ReeTag.F4.shortModule K,
        ((v : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) u = c • u :=
    fun v hv => scalar_of_commutes (⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ :
      adjointGroup ReeTag.F4.tag K) (fun pr hpr => hcommElt pr hpr v hv)
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  obtain ⟨c, hc⟩ := hscal v hv
  have hvZ : v ∈ Subgroup.center ↥(ReeTag.F4.reeGamma K a) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have key : (⟨(y : ModGL ReeTag.F4.tag K), hXC y.2⟩ : adjointGroup ReeTag.F4.tag K) *
        ⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ =
        ⟨(v : ModGL ReeTag.F4.tag K), hXC v.2⟩ *
          ⟨(y : ModGL ReeTag.F4.tag K), hXC y.2⟩ := by
      apply shortRestrictHom_injective ReeTag.F4 (K := K)
      refine LinearMap.ext fun u => Subtype.ext ?_
      simp only [map_mul, Module.End.mul_apply, ReeTag.coe_shortRestrictHom_apply]
      have hyu : ((y : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K))
          (u : RootModule ReeTag.F4.tag K) ∈ ReeTag.F4.shortModule K :=
        ReeTag.mem_shortModule_of_mem hp0 (hXC y.2) u.2
      rw [hc _ hyu, hc _ u.2, map_smul]
    have h3 := congrArg Subtype.val key
    simp only [Subgroup.coe_mul] at h3 ⊢
    exact h3
  rw [hZ] at hvZ
  exact hvZ

end OddGroup


theorem subfieldNonLocalizedLargeReeBZero
    : SubfieldNonLocalizedLargeReeBZero := by
  intro a ha K _ _ _ hK p hp hp3 hpa σ hσ
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  refine nonLocalized_of_elemAbelian (fun s E hs hE0 hEcomm hEexp hle => hE0 ?_)
  have hnorm : ∀ j ∈ signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ), ∀ e ∈ E,
      j * e * j⁻¹ ∈ E := fun j hj e he => (Subgroup.mem_normalizer_iff.1 (hle hj) e).1 he
  by_cases hs2 : s = 2
  · subst hs2
    have : Fact (Nat.Prime 2) := ⟨hs⟩
    have hEp : IsPGroup 2 E := by
      refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
      have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
      rcases (Nat.dvd_prime hs).mp h1 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    exact largeRee_twoGroup_eq_bot hK σ E hEp hnorm
  · exact largeRee_oddGroup_eq_bot ha hK hp hp3 hpa σ hσ hs hs2 E hEcomm hEexp hnorm

end CFSG.SignalizerFunctorTheorem.CatalogBridge
