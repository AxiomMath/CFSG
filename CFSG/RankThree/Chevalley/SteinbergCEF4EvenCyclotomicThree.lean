module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2CubicDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourNonregular
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeTorus
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusDoubleEdge

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl RootSpace
  CFSG.LieType.AlgebraicGroups EvenF4QPlus NativeLevi CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise commutatorElement

namespace EvenF4CyclotomicThree

section Twist

variable {M : Type} [Field M] [CharP M 2]

theorem weylElt_pair_zpow_eq_canonicalRep (κ : F4A2Kind) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (weylElt Tag.F4 M κ.i 1 * weylElt Tag.F4 M κ.j 1) ^ ε =
      canonicalRep (coxeterSystem .F4) M
        (((coxeterSystem .F4).simple κ.i * (coxeterSystem .F4).simple κ.j) ^ ε) := by
  rw [← canonicalRep_simple (coxeterSystem .F4) (R := M) κ.i,
    ← canonicalRep_simple (coxeterSystem .F4) (R := M) κ.j, ← canonicalRep_mul_of_charTwo]
  rcases hε with rfl | rfl
  · rw [zpow_one, zpow_one]
  · rw [zpow_neg_one, zpow_neg_one, canonicalRep_inv_of_charTwo]

theorem canonicalRep_conj_eq_on_subsystemGroup {τ : Tag} {J : Set (Fin τ.rank)}
    {v w : WeylGroup τ} (hvw : ∀ α ∈ parabolicRoots τ J, v • α = w • α) {g : ModGL τ M}
    (hg : g ∈ subsystemGroup τ M J) :
    canonicalRep (coxeterSystem τ) M v * g * (canonicalRep (coxeterSystem τ) M v)⁻¹ =
      canonicalRep (coxeterSystem τ) M w * g * (canonicalRep (coxeterSystem τ) M w)⁻¹ := by
  have h2 : (2 : M) = 0 := CharTwo.two_eq_zero
  have hgen : ∀ α ∈ parabolicRoots τ J, ∀ c : M,
      canonicalRep (coxeterSystem τ) M v * pinnedX τ M α c *
          (canonicalRep (coxeterSystem τ) M v)⁻¹ =
        canonicalRep (coxeterSystem τ) M w * pinnedX τ M α c *
          (canonicalRep (coxeterSystem τ) M w)⁻¹ := fun α hα c => by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 v hα.1 c,
      canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα.1 c, hvw α hα]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, c, rfl | rfl⟩ := hx
    · rw [← pinnedX_single]
      exact hgen _ ⟨isRoot_single τ k,
        fun i hi => Pi.single_eq_of_ne (fun e => hi (by rw [e]; exact hk)) _⟩ c
    · rw [← pinnedX_neg_single]
      refine hgen _ ⟨isRoot_neg_single τ k, fun i hi => ?_⟩ c
      rw [Pi.neg_apply, Pi.single_eq_of_ne (fun e => hi (by rw [e]; exact hk)), neg_zero]
  | one => rw [mul_one, mul_inv_cancel, mul_one, mul_inv_cancel]
  | mul x y _ _ hx hy =>
    calc canonicalRep (coxeterSystem τ) M v * (x * y) * (canonicalRep (coxeterSystem τ) M v)⁻¹ =
          (canonicalRep (coxeterSystem τ) M v * x * (canonicalRep (coxeterSystem τ) M v)⁻¹) *
            (canonicalRep (coxeterSystem τ) M v * y * (canonicalRep (coxeterSystem τ) M v)⁻¹) := by
          group
      _ = (canonicalRep (coxeterSystem τ) M w * x * (canonicalRep (coxeterSystem τ) M w)⁻¹) *
            (canonicalRep (coxeterSystem τ) M w * y * (canonicalRep (coxeterSystem τ) M w)⁻¹) := by
          rw [hx, hy]
      _ = _ := by group
  | inv x _ hx =>
    calc canonicalRep (coxeterSystem τ) M v * x⁻¹ * (canonicalRep (coxeterSystem τ) M v)⁻¹ =
          (canonicalRep (coxeterSystem τ) M v * x * (canonicalRep (coxeterSystem τ) M v)⁻¹)⁻¹ := by
          group
      _ = (canonicalRep (coxeterSystem τ) M w * x * (canonicalRep (coxeterSystem τ) M w)⁻¹)⁻¹ := by
          rw [hx]
      _ = _ := by group

end Twist

section Core

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {K₃ : Type} [Field K₃] [Algebra K K₃]
  [FiniteDimensional K K₃]

theorem cyclotomic_three_core (h3 : Module.finrank K K₃ = 3) (σ : K₃ ≃+* K₃)
    (hσ : ∀ c, σ c = c ^ Fintype.card K) (κ : F4A2Kind) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {v : WeylGroup .F4}
    (hv : ∀ α ∈ parabolicRoots .F4 {κ.i, κ.j},
      v • α = (((coxeterSystem .F4).simple κ.i * (coxeterSystem .F4).simple κ.j) ^ ε) • α)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {b : Fin Tag.F4.rank → K₃ˣ} (hbp : b ^ p = 1)
    (hb1 : b ≠ 1) (hker : rootCharKernel b = parabolicRoots .F4 {κ.i, κ.j})
    (Γ₁ D R : Subgroup (ModGL .F4 K₃))
    (hΓ₁ : Γ₁ = adjointGroup .F4 K₃ ⊓
      (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₃ v) (σ : K₃ →+* K₃)).eqLocus
        (MonoidHom.id _))
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {rootDiagUnit .F4 b}) (hR : R = ⁅D, D⁆) :
    adjointGroup .F4 K₃ ⊓ Subgroup.centralizer {rootDiagUnit .F4 b} =
      torusGroup .F4 K₃ ⊔ subsystemGroup .F4 K₃ {κ.i, κ.j} ∧
    ∃ a ∈ subsystemGroup .F4 K₃ {κ.i, κ.j},
      R = subsystemGroup .F4 K₃ {κ.i, κ.j} ⊓ Γ₁ ∧
      subsystemGroup .F4 K₃ {κ.i, κ.j} ⊓ Γ₁ =
        ((subsystemGroup .F4 K {κ.i, κ.j}).map (baseChangeGL (algebraMap K K₃))).map
          (MulAut.conj a).toMonoidHom ∧
      CFSG.IsQuasisimple R ∧ Group.IsPerfect R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
      D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 K₃)) = (Subgroup.center D).map D.subtype ∧
      (Subgroup.center D).map D.subtype ≤ torusGroup .F4 K₃ ∧
      Odd (Nat.card (Subgroup.center D)) ∧
      ∀ A : SL2 K, a * rootSL2 .F4 K₃ (Pi.single κ.i 1)
        (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A) * a⁻¹ ∈ R := by
  classical
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have hX := toralCentralizer_eq_toralRootGroup_of_le (K := K₃)
    (F4_rootCharStabilizer_le_kernelReflectionGroup hp hp3 hbp hb1)
  have hCx : adjointGroup .F4 K₃ ⊓ Subgroup.centralizer {rootDiagUnit .F4 b} =
      torusGroup .F4 K₃ ⊔ subsystemGroup .F4 K₃ {κ.i, κ.j} := by
    have h1 : toralCentralizer .F4 K₃ b = standardLevi .F4 K₃ {κ.i, κ.j} := by
      rw [hX, toralRootGroup, hker, ← subsystemGroup_eq_rootSpan]
      rfl
    exact h1
  set m := (weylElt Tag.F4 K₃ κ.i 1 * weylElt Tag.F4 K₃ κ.j 1) ^ ε with hm
  set θ : ModGL Tag.F4 K₃ →* ModGL Tag.F4 K₃ :=
    (MulAut.conj m).toMonoidHom.comp (Units.map (entrywiseHom σ.toRingHom)) with hθ
  have hZ : ∀ h, h ∈ simpleCharKernel .F4 K₃ {κ.i, κ.j} ↔ h ∈ torusGroup Tag.F4 K₃ ∧
      torusRootChar h (Pi.single κ.i 1) = 1 ∧ torusRootChar h (Pi.single κ.j 1) = 1 := by
    intro h
    rw [mem_simpleCharKernel]
    constructor
    · rintro ⟨hh, hc⟩
      exact ⟨hh, hc _ (Set.mem_insert _ _), hc _ (Set.mem_insert_of_mem _ rfl)⟩
    · rintro ⟨hh, hi, hj⟩
      refine ⟨hh, fun k hk => ?_⟩
      rcases hk with rfl | hk
      · exact hi
      · rw [Set.mem_singleton_iff.1 hk]
        exact hj
  obtain ⟨-, -, -, hquasiK, -, -, a, ha, -, QK, hQK, hfix, hcentL, hcenterL, hoddZ, hSL2⟩ :=
    even_F4_native_A2_cubic_permutation_descent_including_field_two K K₃ h3 σ hσ κ ε hε θ
      (fun g => rfl) _ (standardLevi .F4 K₃ {κ.i, κ.j}) hZ rfl
  have hagree : ∀ g ∈ subsystemGroup .F4 K₃ {κ.i, κ.j},
      twistedEntrywise (canonicalRep (coxeterSystem .F4) K₃ v) (σ : K₃ →+* K₃) g = θ g := by
    intro g hg
    have hσg := units_map_entrywiseHom_mem_subsystemGroup (σ : K₃ →+* K₃) hg
    rw [twistedEntrywise_apply, canonicalRep_conj_eq_on_subsystemGroup hv hσg,
      ← weylElt_pair_zpow_eq_canonicalRep κ hε]
    rfl
  have hR₀ : subsystemGroup .F4 K₃ {κ.i, κ.j} ⊓ Γ₁ = QK := by
    rw [← hfix]
    ext g
    constructor
    · intro hg
      obtain ⟨hgQ, hgΓ⟩ := Subgroup.mem_inf.1 hg
      rw [hΓ₁] at hgΓ
      exact Subgroup.mem_inf.2 ⟨hgQ, (hagree g hgQ).symm.trans hgΓ.2⟩
    · intro hg
      obtain ⟨hgQ, hgθ⟩ := Subgroup.mem_inf.1 hg
      rw [hΓ₁]
      exact Subgroup.mem_inf.2 ⟨hgQ, subsystemGroup_le_adjointGroup' _ hgQ,
        (hagree g hgQ).trans hgθ⟩
  have hQKmap : QK = ((subsystemGroup .F4 K {κ.i, κ.j}).map
      (baseChangeGL (algebraMap K K₃))).map (MulAut.conj (a : ModGL .F4 K₃)).toMonoidHom := by
    ext g
    rw [hQK, Subgroup.map_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  set R₀ := subsystemGroup .F4 K₃ {κ.i, κ.j} ⊓ Γ₁ with hR₀def
  have hR₀map : R₀ = (subsystemGroup .F4 K {κ.i, κ.j}).map
      ((MulAut.conj (a : ModGL .F4 K₃)).toMonoidHom.comp (baseChangeGL (algebraMap K K₃))) := by
    rw [hR₀, hQKmap, Subgroup.map_map]
  have hinj : Function.Injective
      ((MulAut.conj (a : ModGL .F4 K₃)).toMonoidHom.comp (baseChangeGL (algebraMap K K₃))) :=
    (MulAut.conj _).injective.comp (baseChangeGL_injective (τ := .F4) (algebraMap K K₃))
  have e : subsystemGroup .F4 K {κ.i, κ.j} ≃* R₀ :=
    (Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hR₀map.symm)
  have hquasi : CFSG.IsQuasisimple R₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hquasiK
  have hperf : Group.IsPerfect R₀ := hquasi.1
  have hDL : D ≤ standardLevi .F4 K₃ {κ.i, κ.j} := by
    rw [hD, standardLevi, ← hCx]
    exact inf_le_inf_right _ (by rw [hΓ₁]; exact inf_le_left)
  have hDΓ : D ≤ Γ₁ := by
    rw [hD]
    exact inf_le_left
  have hR₀D : R₀ ≤ D := by
    rw [hD]
    refine le_inf inf_le_right ?_
    intro r hr
    have h1 : r ∈ adjointGroup .F4 K₃ ⊓ Subgroup.centralizer {rootDiagUnit .F4 b} := by
      rw [hCx]
      exact Subgroup.mem_sup_right hr.1
    exact h1.2
  have hRR₀ : R = R₀ := by
    rw [hR]
    apply le_antisymm
    · exact le_inf ((Subgroup.commutator_mono hDL hDL).trans (commutator_standardLevi_le _))
        ((commutator_self_le D).trans hDΓ)
    · rw [← Subgroup.isPerfect_iff.1 hperf]
      exact Subgroup.commutator_mono hR₀D hR₀D
  rw [← hRR₀] at hquasi hperf hR₀D
  have hlayer : CFSG.layer R = ⊤ := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hquasi
  have hRne : R ≠ ⊥ := by
    intro hbot
    obtain ⟨-, hsimpQ, -⟩ := hquasi
    have h0 := (Subgroup.eq_bot_iff_forall R).1 hbot
    have hsub : Subsingleton (R ⧸ Subgroup.center R) := ⟨fun x z => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
      rw [show x = 1 from Subtype.ext (h0 _ x.2), show z = 1 from Subtype.ext (h0 _ z.2)]⟩
    exact not_nontrivial_iff_subsingleton.2 hsub hsimpQ.toNontrivial
  rw [← hR₀, ← hRR₀] at hcentL
  have hZL : ∀ z ∈ simpleCharKernel .F4 K₃ {κ.i, κ.j}, ∀ d ∈ standardLevi .F4 K₃ {κ.i, κ.j},
      d * z = z * d := fun z hz d hd =>
    Subgroup.mem_centralizer_singleton_iff.1 (standardLevi_le_centralizer_of_mem hz hd)
  have hcentD : D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 K₃)) =
      (Subgroup.center D).map D.subtype := by
    refine le_antisymm (fun z hz => ?_) ?_
    · obtain ⟨hzD, hzC⟩ := Subgroup.mem_inf.1 hz
      have hzZ : z ∈ simpleCharKernel .F4 K₃ {κ.i, κ.j} := by
        rw [← hcentL]
        exact Subgroup.mem_inf.2 ⟨hDL hzD, hzC⟩
      refine ⟨⟨z, hzD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
      exact hZL z hzZ d (hDL d.2)
    · rintro _ ⟨d, hd, rfl⟩
      refine Subgroup.mem_inf.2 ⟨d.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hd ⟨r, hR₀D hr⟩)
      exact h1
  have hZD : (Subgroup.center D).map D.subtype ≤ simpleCharKernel .F4 K₃ {κ.i, κ.j} := by
    rw [← hcentD, ← hcentL]
    exact inf_le_inf_right _ hDL
  have hdvd : Nat.card (Subgroup.center D) ∣ Nat.card (simpleCharKernel .F4 K₃ {κ.i, κ.j}) := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    exact Subgroup.card_dvd_of_le hZD
  refine ⟨hCx, a, ha, hRR₀, hR₀.trans hQKmap, hquasi, hperf, hlayer, hRne, hcentD,
    fun z hz => (hZD hz).1, hoddZ.of_dvd_nat hdvd, fun A => ?_⟩
  rw [hRR₀, hR₀, ← hfix]
  exact hSL2 A

end Core

section Setup

variable {L Ω : Type} [Field L] [Field Ω] (ι : L →+* Ω)

theorem exists_rootDiagUnit_of_conj_parabolic {p : ℕ} (hp : p.Prime) {x₀ : ModGL Tag.F4 L}
    (hx₀ : x₀ ∈ torusGroup Tag.F4 L) (hxp : orderOf (baseChangeGL ι x₀) = p)
    (u : WeylGroup Tag.F4) {J : Set (Fin Tag.F4.rank)}
    (hu : (fun α => u • α) '' {α | IsRoot Tag.F4 α ∧ torusRootChar (baseChangeGL ι x₀) α = 1} =
      parabolicRoots Tag.F4 J) :
    ∃ c : Fin Tag.F4.rank → Lˣ,
      canonicalRep (coxeterSystem Tag.F4) L u * x₀ * (canonicalRep (coxeterSystem Tag.F4) L u)⁻¹ =
        rootDiagUnit Tag.F4 c ∧ c ^ p = 1 ∧ c ≠ 1 ∧ rootCharKernel c = parabolicRoots Tag.F4 J := by
  set y₀ := canonicalRep (coxeterSystem Tag.F4) L u * x₀ *
    (canonicalRep (coxeterSystem Tag.F4) L u)⁻¹ with hy₀
  have hy₀H : y₀ ∈ torusGroup Tag.F4 L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer u) x₀).1 hx₀
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  have hord : orderOf y₀ = p := by
    rw [hy₀, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj _).injective x₀, ← orderOf_injective _ hinj x₀, hxp]
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy₀H
  have hcp : c ^ p = 1 := rootDiagUnit_injective (by
    rw [← rootDiagUnit_pow, ← hc, ← hord, pow_orderOf_eq_one, rootDiagUnit_one])
  have hc1 : c ≠ 1 := fun h1 => by
    rw [h1, rootDiagUnit_one] at hc
    rw [hc, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hker₀ : {β | IsRoot Tag.F4 β ∧ torusRootChar y₀ β = 1} = parabolicRoots Tag.F4 J := by
    rw [← hu]
    have e := survivingRoots_canonicalRep_conj (L := L) hx₀ u
    rw [← hy₀] at e
    rw [e]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq, torusRootChar_baseChangeGL, map_eq_one_iff _ ι.injective]
  refine ⟨c, hc, hcp, hc1, ?_⟩
  rw [← hker₀]
  ext β
  constructor
  · rintro ⟨hβ, h1⟩
    refine ⟨hβ, ?_⟩
    rw [hc, torusRootChar_rootDiagUnit c hβ, h1, Units.val_one]
  · rintro ⟨hβ, h1⟩
    refine ⟨hβ, ?_⟩
    rw [hc, torusRootChar_rootDiagUnit c hβ] at h1
    exact Units.val_eq_one.1 h1

end Setup

theorem smul_eq_of_weylAct_eq_on_parabolicRoots {τ : Tag} {v w' : WeylGroup τ}
    {J : Set (Fin τ.rank)}
    (h : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots τ J),
      weylAct τ v z = weylAct τ w' z)
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ J) : v • α = w' • α := by
  apply ofLattice_injective
  rw [← weylAct_ofLattice, ← weylAct_ofLattice]
  exact h _ (Submodule.subset_span ⟨α, hα, rfl⟩)

theorem cyclotomic_three_transport (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]
    (K₃ : IntermediateField K Ω) (g : ModGL .F4 Ω)
    (hgK₃ : g ∈ (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)))
    (Γ : Subgroup (ModGL .F4 Ω)) (hΓ : Γ = conjEntrywiseImage K g⁻¹) (x : ModGL .F4 Ω)
    (hxΓ : x ∈ Γ) (h y : ModGL .F4 Ω)
    (hhK₃ : h ∈ (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)))
    (hy : y = h * x * h⁻¹) (Γ₁ D R : Subgroup (ModGL .F4 Ω))
    (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom) (hD : D = Γ₁ ⊓ Subgroup.centralizer {y})
    (hR : R = ⁅D, D⁆) (hquasi : CFSG.IsQuasisimple R)
    (hcent : D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = (Subgroup.center D).map D.subtype)
    (hodd : Odd (Nat.card (Subgroup.center D))) (κ : F4A2Kind) (a : ModGL .F4 K₃)
    (ha : a ∈ adjointGroup .F4 K₃)
    (hρR : ∀ A : SL2 K, baseChangeGL (algebraMap K₃ Ω) (a * rootSL2 .F4 K₃ (Pi.single κ.i 1)
      (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A) * a⁻¹) ∈ R) :
    ∃ x₀ : adjointGroup .F4 K,
      baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
      (Subgroup.centralizer {x₀}).map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
        D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
      ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆.map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
        R.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
      CFSG.IsQuasisimple (⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
        Subgroup (adjointGroup .F4 K)) ∧
      CFSG.layer (⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
        Subgroup (adjointGroup .F4 K)) = ⊤ ∧
      Subgroup.centralizer {x₀} ⊓ Subgroup.centralizer
          ((⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
            Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
        (Subgroup.center (Subgroup.centralizer {x₀})).map
          (Subgroup.centralizer ({x₀} : Set (adjointGroup .F4 K))).subtype ∧
      Odd (Nat.card (Subgroup.center (Subgroup.centralizer ({x₀} : Set (adjointGroup .F4 K))))) ∧
      ∃ R₀ : Subgroup (adjointGroup .F4 K),
        R₀ ≤ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ ∧
        ∃ k ∈ adjointGroup .F4 K₃,
          (R₀.map ((baseChangeGL (algebraMap K K₃)).comp (adjointGroup .F4 K).subtype)).map
              (MulAut.conj k).toMonoidHom =
            ((rootSL2 .F4 K₃ (Pi.single κ.i 1)).comp
              (Matrix.SpecialLinearGroup.map (algebraMap K K₃))).range := by
  classical
  set ιK : K →+* Ω := algebraMap K Ω with hιK
  set ι : K₃ →+* Ω := algebraMap K₃ Ω with hι
  have hinjK := baseChangeGL_injective (τ := Tag.F4) ιK
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  have hcomp : ∀ r : ModGL .F4 K, baseChangeGL ι (baseChangeGL (algebraMap K K₃) r) =
      baseChangeGL ιK r := fun r => by
    rw [baseChangeGL_baseChangeGL, hι, hιK, ← IsScalarTower.algebraMap_eq]
  rw [hΓ] at hxΓ
  obtain ⟨x₁, hx₁, hx₁x⟩ := hxΓ
  set x₀ : adjointGroup .F4 K := ⟨x₁, hx₁⟩ with hx₀
  have hx₀x : baseChangeGL ιK (x₀ : ModGL .F4 K) = g * x * g⁻¹ := by
    change baseChangeGL ιK x₁ = g * x * g⁻¹
    rw [← hx₁x]
    change baseChangeGL ιK x₁ = g * (g⁻¹ * baseChangeGL ιK x₁ * g⁻¹⁻¹) * g⁻¹
    group
  have hCx := map_centralizer_eq_map_conj K Ω g Γ hΓ x h y hy Γ₁ D hΓ₁ hD x₀ hx₀x
  set ψ := (MulAut.conj (g * h⁻¹)).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj (g * h⁻¹)).injective
  set ι' := (baseChangeGL ιK).comp (adjointGroup .F4 K).subtype with hι'
  have hι'inj : Function.Injective ι' := hinjK.comp Subtype.val_injective
  set C₀ := Subgroup.centralizer ({x₀} : Set (adjointGroup .F4 K)) with hC₀
  have hRmap : ⁅C₀, C₀⁆.map ι' = R.map ψ := by
    rw [Subgroup.map_commutator, hCx, ← Subgroup.map_commutator, hR]
  have e : (⁅C₀, C₀⁆ : Subgroup (adjointGroup .F4 K)) ≃* R :=
    ((Subgroup.equivMapOfInjective _ ι' hι'inj).trans (MulEquiv.subgroupCongr hRmap)).trans
      (Subgroup.equivMapOfInjective R ψ hψinj).symm
  have hquasi₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hquasi
  have hcentmap : (C₀ ⊓ Subgroup.centralizer
      ((⁅C₀, C₀⁆ : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K))).map ι' =
      (D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω))).map ψ := by
    rw [map_inf_centralizer_of_injective hι'inj, map_inf_centralizer_of_injective hψinj, hCx,
      ← Subgroup.coe_map, ← Subgroup.coe_map, hRmap]
  have hZmap : ((Subgroup.center C₀).map C₀.subtype).map ι' =
      ((Subgroup.center D).map D.subtype).map ψ := by
    rw [map_map_center_subtype_of_injective hι'inj, map_map_center_subtype_of_injective hψinj,
      hCx]
  have hcent₀ : C₀ ⊓ Subgroup.centralizer
      ((⁅C₀, C₀⁆ : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
      (Subgroup.center C₀).map C₀.subtype := by
    apply Subgroup.map_injective hι'inj
    rw [hcentmap, hZmap, hcent]
  have eC : C₀ ≃* D :=
    ((Subgroup.equivMapOfInjective _ ι' hι'inj).trans (MulEquiv.subgroupCongr hCx)).trans
      (Subgroup.equivMapOfInjective D ψ hψinj).symm
  have hodd₀ : Odd (Nat.card (Subgroup.center C₀)) := by
    rw [Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
    exact hodd
  refine ⟨x₀, hx₀x, hCx, hRmap, hquasi₀,
    CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hquasi₀, hcent₀, hodd₀, ?_⟩
  obtain ⟨g₀, hg₀, rfl⟩ := hgK₃
  obtain ⟨h₀, hh₀, rfl⟩ := hhK₃
  set b₀ := g₀ * h₀⁻¹ * a with hb₀
  have hb₀C : b₀ ∈ adjointGroup .F4 K₃ := mul_mem (mul_mem hg₀ (inv_mem hh₀)) ha
  set ρK := ((rootSL2 .F4 K₃ (Pi.single κ.i 1)).comp
    (Matrix.SpecialLinearGroup.map (algebraMap K K₃))).range with hρK
  have hclaim : ∀ s ∈ ρK, ∃ r ∈ (⁅C₀, C₀⁆ : Subgroup (adjointGroup .F4 K)),
      baseChangeGL ιK (r : ModGL .F4 K) = baseChangeGL ι (b₀ * s * b₀⁻¹) := by
    rintro _ ⟨A, rfl⟩
    have hmem : baseChangeGL ι (b₀ * (rootSL2 .F4 K₃ (Pi.single κ.i 1)
        (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A)) * b₀⁻¹) ∈ R.map ψ := by
      refine ⟨_, hρR A, ?_⟩
      change baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹ * baseChangeGL ι (a *
          rootSL2 .F4 K₃ (Pi.single κ.i 1) (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A) *
            a⁻¹) * (baseChangeGL ι g₀ * (baseChangeGL ι h₀)⁻¹)⁻¹ = _
      rw [hb₀]
      simp only [map_mul, map_inv]
      group
    rw [← hRmap] at hmem
    obtain ⟨r, hr, hre⟩ := hmem
    exact ⟨r, hr, hre⟩
  refine ⟨(ρK.comap ((MulAut.conj b₀⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K K₃)).comp
    (adjointGroup .F4 K).subtype))) ⊓ ⁅C₀, C₀⁆, inf_le_right, b₀⁻¹, inv_mem hb₀C, ?_⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact (Subgroup.mem_inf.1 hr).1
  · intro s hs
    obtain ⟨r, hr, hre⟩ := hclaim s hs
    have hr' : baseChangeGL (algebraMap K K₃) (r : ModGL .F4 K) = b₀ * s * b₀⁻¹ :=
      hinj (by rw [hcomp, hre])
    have hks : b₀⁻¹ * baseChangeGL (algebraMap K K₃) (r : ModGL .F4 K) * b₀⁻¹⁻¹ = s := by
      rw [hr']
      group
    refine ⟨_, ⟨r, Subgroup.mem_inf.2 ⟨?_, hr⟩, rfl⟩, ?_⟩
    · change b₀⁻¹ * baseChangeGL (algebraMap K K₃) (r : ModGL .F4 K) * b₀⁻¹⁻¹ ∈ ρK
      rw [hks]
      exact hs
    · exact hks

end EvenF4CyclotomicThree

open EvenF4CyclotomicThree

theorem even_F4_cyclotomic_three_nonregular_derived_centralizer {f : ℕ} (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (K₃ : IntermediateField K Ω) (hK₃ : Module.finrank K K₃ = 3)
    (n g : ModGL .F4 Ω) (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 4))
    (hg : g ∈ adjointGroup .F4 Ω) (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n)
    (Γ T₀ : Subgroup (ModGL .F4 Ω)) (hΓ : Γ = conjEntrywiseImage K g⁻¹)
    (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω) (hx : x ∈ T₀) (hxp : orderOf x = p)
    (κ : F4A2Kind) (u : WeylGroup .F4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 {κ.i, κ.j})
    (huw : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {κ.i, κ.j}),
      weylAct .F4 (u * f4Coxeter ^ 4 * u⁻¹) z =
        weylAct .F4 ((simple .F4 κ.i * simple .F4 κ.j) ^ ε) z)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D R : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) (hR : R = ⁅D, D⁆) :
    (adjointGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ⊓ Subgroup.centralizer {y} =
      (torusGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ⊔
        (subsystemGroup .F4 K₃ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₃ Ω)) ∧
    ∃ a ∈ subsystemGroup .F4 K₃ {κ.i, κ.j},
      R = (subsystemGroup .F4 K₃ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₃ Ω)) ⊓ Γ₁ ∧
      (subsystemGroup .F4 K₃ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₃ Ω)) ⊓ Γ₁ =
        ((subsystemGroup .F4 K {κ.i, κ.j}).map (baseChangeGL (algebraMap K Ω))).map
          (MulAut.conj (baseChangeGL (algebraMap K₃ Ω) a)).toMonoidHom ∧
      CFSG.IsQuasisimple R ∧ Group.IsPerfect R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
      D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = (Subgroup.center D).map D.subtype ∧
      (Subgroup.center D).map D.subtype ≤
        (torusGroup .F4 K₃).map (baseChangeGL (algebraMap K₃ Ω)) ∧
      Odd (Nat.card (Subgroup.center D)) ∧
      (∀ A : SL2 K, baseChangeGL (algebraMap K₃ Ω) (a * rootSL2 .F4 K₃ (Pi.single κ.i 1)
        (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A) * a⁻¹) ∈ R) ∧
      ∃ x₀ : adjointGroup .F4 K,
        baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
        (Subgroup.centralizer {x₀}).map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
          D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
        ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆.map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
          R.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
        CFSG.IsQuasisimple (⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
          Subgroup (adjointGroup .F4 K)) ∧
        CFSG.layer (⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
          Subgroup (adjointGroup .F4 K)) = ⊤ ∧
        Subgroup.centralizer {x₀} ⊓ Subgroup.centralizer
            ((⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ :
              Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
          (Subgroup.center (Subgroup.centralizer {x₀})).map
            (Subgroup.centralizer ({x₀} : Set (adjointGroup .F4 K))).subtype ∧
        Odd (Nat.card (Subgroup.center (Subgroup.centralizer
          ({x₀} : Set (adjointGroup .F4 K))))) ∧
        ∃ R₀ : Subgroup (adjointGroup .F4 K),
          R₀ ≤ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ ∧
          ∃ k ∈ adjointGroup .F4 K₃,
            (R₀.map ((baseChangeGL (algebraMap K K₃)).comp (adjointGroup .F4 K).subtype)).map
                (MulAut.conj k).toMonoidHom =
              ((rootSL2 .F4 K₃ (Pi.single κ.i 1)).comp
                (Matrix.SpecialLinearGroup.map (algebraMap K K₃))).range := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : FiniteDimensional K K₃ := Module.finite_of_finrank_eq_succ hK₃
  have : Finite K₃ := Module.finite_of_finite K
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  set ι : K₃ →+* Ω := algebraMap K₃ Ω with hι
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  obtain ⟨-, hCA⟩ := F4_cyclotomic_three_torus_and_regular_prime_centralizers K Ω F hF n hn
  obtain ⟨-, -, -, -, -, h2⟩ := hCA g hg hgn Γ T₀ (T₀.map (MulAut.conj g).toMonoidHom) hΓ hT₀ rfl
  obtain ⟨hgK₃, hT₀K₃, hΓK₃⟩ := h2 ‹_› K₃ hK₃
  obtain ⟨x₀, hx₀H, hx₀⟩ := hT₀K₃ hx
  have hhι : baseChangeGL ι (canonicalRep (coxeterSystem .F4) K₃ u) = h := by
    rw [hh]
    exact baseChangeGL_canonicalRep ι u
  have hu' : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar (baseChangeGL ι x₀) α = 1} =
      parabolicRoots .F4 {κ.i, κ.j} := by
    rw [hx₀]
    exact hu
  obtain ⟨b, hb, hbp, hb1, hker⟩ :=
    exists_rootDiagUnit_of_conj_parabolic ι hp hx₀H (by rw [hx₀]; exact hxp) u hu'
  have hyι : baseChangeGL ι (rootDiagUnit .F4 b) = y := by
    rw [← hb, map_mul, map_mul, map_inv, hhι, hx₀, hy]
  obtain ⟨σ, hσ, hFσ⟩ := exists_frob_restrict F (fun c => by rw [hF, Nat.card_eq_fintype_card])
    K₃
  set v := u * f4Coxeter ^ 4 * u⁻¹ with hv
  have hvJ : ∀ α ∈ parabolicRoots .F4 {κ.i, κ.j},
      v • α = (((coxeterSystem .F4).simple κ.i * (coxeterSystem .F4).simple κ.j) ^ ε) • α :=
    fun α hα => smul_eq_of_weylAct_eq_on_parabolicRoots huw hα
  have hm : baseChangeGL ι (canonicalRep (coxeterSystem .F4) K₃ v) = h * n * h⁻¹ := by
    rw [baseChangeGL_canonicalRep, hh, hn, canonicalRep_conj_eq_of_charTwo]
  have hhC : h ∈ (adjointGroup .F4 K₃).map (baseChangeGL ι) :=
    ⟨_, canonicalRep_mem_adjointGroup _ K₃ u, hhι⟩
  have hFh : Units.map (entrywiseHom F) h = h := by
    rw [hh]
    exact entrywise_canonicalRep (RingEquiv.ofBijective F (frobenius_bijective (k := K) F hF)) u
  have hΓ₁ch : ∀ z, z ∈ Γ₁ ↔ z ∈ (adjointGroup .F4 K₃).map (baseChangeGL ι) ∧
      h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹ = z := by
    intro z
    rw [hΓ₁, Subgroup.mem_map_equiv, hΓK₃, Subgroup.mem_inf]
    change (MulAut.conj h).symm z ∈ _ ∧ twistedEntrywise n F ((MulAut.conj h).symm z) =
      (MulAut.conj h).symm z ↔ _
    rw [MulAut.conj_symm_apply, twistedEntrywise_apply, map_mul, map_mul, map_inv, hFh]
    constructor
    · rintro ⟨hz, hfix⟩
      refine ⟨?_, ?_⟩
      · have e : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem hhC hz) (inv_mem hhC)
      · calc h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹ =
            h * (n * (h⁻¹ * Units.map (entrywiseHom F) z * h) * n⁻¹) * h⁻¹ := by group
          _ = h * (h⁻¹ * z * h) * h⁻¹ := by rw [hfix]
          _ = z := by group
    · rintro ⟨hz, hfix⟩
      refine ⟨mul_mem (mul_mem (inv_mem hhC) hz) hhC, ?_⟩
      calc n * (h⁻¹ * Units.map (entrywiseHom F) z * h) * n⁻¹ =
          h⁻¹ * (h * n * h⁻¹ * Units.map (entrywiseHom F) z * (h * n * h⁻¹)⁻¹) * h := by group
        _ = h⁻¹ * z * h := by rw [hfix]
  set Γ₃ : Subgroup (ModGL .F4 K₃) := adjointGroup .F4 K₃ ⊓
    (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₃ v) (σ : K₃ →+* K₃)).eqLocus
      (MonoidHom.id _) with hΓ₃
  have hΓ₁eq : Γ₁ = Γ₃.map (baseChangeGL ι) := by
    ext z
    rw [hΓ₁ch]
    constructor
    · rintro ⟨⟨z₀, hz₀, rfl⟩, hfix⟩
      refine ⟨z₀, Subgroup.mem_inf.2 ⟨hz₀, ?_⟩, rfl⟩
      change twistedEntrywise (canonicalRep (coxeterSystem .F4) K₃ v) (σ : K₃ →+* K₃) z₀ = z₀
      apply hinj
      rw [twistedEntrywise_apply, map_mul, map_mul, map_inv, hm,
        ← entrywise_baseChangeGL_eq ι F (σ : K₃ →+* K₃) hFσ]
      exact hfix
    · rintro ⟨z₀, hz₀, rfl⟩
      obtain ⟨hz₀C, hfix⟩ := Subgroup.mem_inf.1 hz₀
      change twistedEntrywise (canonicalRep (coxeterSystem .F4) K₃ v) (σ : K₃ →+* K₃) z₀ =
        z₀ at hfix
      refine ⟨⟨z₀, hz₀C, rfl⟩, ?_⟩
      rw [entrywise_baseChangeGL_eq ι F (σ : K₃ →+* K₃) hFσ, ← hm, ← map_mul, ← map_inv,
        ← map_mul, ← twistedEntrywise_apply, hfix]
  set D₃ := Γ₃ ⊓ Subgroup.centralizer {rootDiagUnit .F4 b} with hD₃
  set R₃ := ⁅D₃, D₃⁆ with hR₃
  have hDeq : D = D₃.map (baseChangeGL ι) := by
    rw [hD, hΓ₁eq, hD₃, map_inf_centralizer_of_injective hinj, Set.image_singleton, hyι]
  have hReq : R = R₃.map (baseChangeGL ι) := by
    rw [hR, hDeq, Subgroup.map_commutator]
  obtain ⟨hL₀, a, ha, hRR₀, hR₀a, hquasi₃, hperf₃, -, -, hcent₃, hZH₃, hodd₃, hSL2₃⟩ :=
    cyclotomic_three_core (K := K) (K₃ := K₃) hK₃ σ (fun c => hσ c) κ hε hvJ hp hp3 hbp hb1 hker
      Γ₃ D₃ R₃ rfl rfl rfl
  have e₃ : R₃ ≃* R :=
    (Subgroup.equivMapOfInjective R₃ _ hinj).trans (MulEquiv.subgroupCongr hReq.symm)
  have hquasi : CFSG.IsQuasisimple R := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₃ hquasi₃
  have hRne : R ≠ ⊥ := by
    intro hbot
    obtain ⟨-, hsimpQ, -⟩ := hquasi
    have h0 := (Subgroup.eq_bot_iff_forall R).1 hbot
    have hsub : Subsingleton (R ⧸ Subgroup.center R) := ⟨fun x z => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
      rw [show x = 1 from Subtype.ext (h0 _ x.2), show z = 1 from Subtype.ext (h0 _ z.2)]⟩
    exact not_nontrivial_iff_subsingleton.2 hsub hsimpQ.toNontrivial
  have hC : (adjointGroup .F4 K₃).map (baseChangeGL ι) ⊓ Subgroup.centralizer {y} =
      (torusGroup .F4 K₃).map (baseChangeGL ι) ⊔
        (subsystemGroup .F4 K₃ {κ.i, κ.j}).map (baseChangeGL ι) := by
    rw [← Subgroup.map_sup, ← hL₀, map_inf_centralizer_of_injective hinj, Set.image_singleton,
      hyι]
  have hRQ : R = (subsystemGroup .F4 K₃ {κ.i, κ.j}).map (baseChangeGL ι) ⊓ Γ₁ := by
    rw [hReq, hRR₀, hΓ₁eq, Subgroup.map_inf_eq _ _ _ hinj]
  have hQa : (subsystemGroup .F4 K₃ {κ.i, κ.j}).map (baseChangeGL ι) ⊓ Γ₁ =
      ((subsystemGroup .F4 K {κ.i, κ.j}).map (baseChangeGL (algebraMap K Ω))).map
        (MulAut.conj (baseChangeGL ι a)).toMonoidHom := by
    rw [← hRQ, hReq, hRR₀, hR₀a, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun r => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    rw [baseChangeGL_baseChangeGL, hι, ← IsScalarTower.algebraMap_eq]
  have hcent : D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) =
      (Subgroup.center D).map D.subtype := by
    rw [hDeq, hReq, Subgroup.coe_map, ← map_inf_centralizer_of_injective hinj, hcent₃,
      map_map_center_subtype_of_injective hinj]
  have hZD : (Subgroup.center D).map D.subtype ≤
      (torusGroup .F4 K₃).map (baseChangeGL ι) := by
    rw [hDeq, ← map_map_center_subtype_of_injective hinj]
    exact Subgroup.map_mono hZH₃
  have eD : D₃ ≃* D :=
    (Subgroup.equivMapOfInjective D₃ _ hinj).trans (MulEquiv.subgroupCongr hDeq.symm)
  have hodd : Odd (Nat.card (Subgroup.center D)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eD).toEquiv]
    exact hodd₃
  have hρR : ∀ A : SL2 K, baseChangeGL ι (a * rootSL2 .F4 K₃ (Pi.single κ.i 1)
      (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A) * a⁻¹) ∈ R := fun A => by
    rw [hReq]
    exact ⟨_, hSL2₃ A, rfl⟩
  refine ⟨hC, a, ha, hRQ, hQa, hquasi, hquasi.1,
    CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hquasi, hRne, hcent, hZD, hodd, hρR, ?_⟩
  exact cyclotomic_three_transport K Ω K₃ g hgK₃ Γ hΓ x (hT₀ ▸ hx).2 h y hhC hy Γ₁ D R hΓ₁ hD hR
    hquasi hcent hodd κ a (subsystemGroup_le_adjointGroup_of_any _ ha) hρR

end CFSG.RankThree.Chevalley
