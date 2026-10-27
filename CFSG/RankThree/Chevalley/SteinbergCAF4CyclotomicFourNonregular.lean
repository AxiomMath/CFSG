module

public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularFixed
public import CFSG.RankThree.Chevalley.SteinbergCAF4EvenQPlusTwoPairs
public import CFSG.RankThree.Chevalley.SteinbergBNF4A2RootTraces
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.Chevalley.SteinbergCAF4PairTorus
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusRootPair
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups SteinbergBN EvenF4QPlus RootSpace
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

theorem commutator_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutator_eq_self_of_isPerfect {G : Type*} [Group G] {S : Subgroup G}
    (hS : Group.IsPerfect S) : ⁅S, S⁆ = S := by
  have h := congrArg (Subgroup.map S.subtype) (Group.isPerfect_def.1 hS)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem rootChar_eq_one_of_mem_parabolicRoots {L : Type} [Field L] {b : Fin Tag.F4.rank → Lˣ}
    (h1 : b 1 = 1) (h2 : b 2 = 1) {β : Fin Tag.F4.rank → ℤ}
    (hβ : β ∈ parabolicRoots .F4 ({1, 2} : Set (Fin Tag.F4.rank))) : rootChar b β = 1 := by
  rw [rootChar]
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases hj : j ∈ ({1, 2} : Set (Fin Tag.F4.rank))
  · rcases hj with rfl | rfl
    · rw [h1, one_zpow]
    · rw [h2, one_zpow]
  · rw [hβ.2 j hj, zpow_zero]

theorem map_conj_conjEntrywiseImage {τ : Tag} {L : Type} [Field L] (k : Type) [Field k]
    [Algebra k L] (x y : ModGL τ L) :
    (conjEntrywiseImage k x).map (MulAut.conj y).toMonoidHom = conjEntrywiseImage k (y * x) := by
  rw [conjEntrywiseImage, conjEntrywiseImage, Subgroup.map_map]
  congr 1

theorem odd_F4_cyclotomic_four_nonregular_derived_centralizers {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω (f4Coxeter ^ 3)) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω)
    (hx : x ∈ T₀) (hxp : orderOf x = p) (u : WeylGroup .F4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 {f4Index 1, f4Index 2})
    (huw : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {f4Index 1, f4Index 2}),
      weylAct .F4 (u * f4Coxeter ^ 3 * u⁻¹) z =
        weylAct .F4 ((simple .F4 (f4Index 1) * simple .F4 (f4Index 2)) ^ ε) z)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D R : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) (hR : R = ⁅D, D⁆) :
    ((adjointGroup .F4 Ω ⊓ Subgroup.centralizer {y} : Subgroup (ModGL .F4 Ω)) :
        Set (ModGL .F4 Ω)) =
      (torusGroup .F4 Ω : Set (ModGL .F4 Ω)) * (subsystemGroup .F4 Ω {1, 2} : Set (ModGL .F4 Ω)) ∧
    (∃ a ∈ subsystemGroup .F4 Ω {1, 2},
      R = subsystemGroup .F4 Ω {1, 2} ⊓ Γ₁ ∧
      subsystemGroup .F4 Ω {1, 2} ⊓ Γ₁ =
        ((subsystemGroup .F4 K {1, 2}).map (baseChangeGL (algebraMap K Ω))).map
          (MulAut.conj a).toMonoidHom ∧
      ∃ e : R ≃* matrixIsometryGroup (f4J0 K),
        (∀ z : R, ∃ g' : subsystemGroup .F4 K {1, 2},
          (z : ModGL .F4 Ω) = a * baseChangeGL (algebraMap K Ω) (g' : ModGL .F4 K) * a⁻¹ ∧
            e z = f4B2Rep K g') ∧
        ∀ z : R, z ∈ Subgroup.center R ↔
          (((e z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
              Matrix (Fin 4) (Fin 4) K) = 1 ∨
            (((e z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) :
              Matrix (Fin 4) (Fin 4) K) = -1) ∧
    CFSG.IsQuasisimple R ∧ Group.IsPerfect R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
      Nat.card (Subgroup.center R) = 2 ∧
    (D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = (Subgroup.center D).map D.subtype ∧
      (∀ z, z ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ↔
        z ∈ T₀.map (MulAut.conj h).toMonoidHom ∧ torusRootChar z (Pi.single 1 1) = 1 ∧
          torusRootChar z (Pi.single 2 1) = 1) ∧
      D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ≤ T₀.map (MulAut.conj h).toMonoidHom ∧
      ∀ z₁ ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)),
        ∀ z₂ ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)), z₁ * z₂ = z₂ * z₁) ∧
    (∃ x₀ : adjointGroup .F4 K,
      baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
      (Subgroup.centralizer {x₀}).map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
        D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
      ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆.map
          ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
        R.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
      ∃ R₀ : Subgroup (adjointGroup .F4 K),
        R₀ ≤ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ ∧
        ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧ ∃ k ∈ adjointGroup .F4 M,
          (R₀.map ((baseChangeGL (algebraMap K M)).comp (adjointGroup .F4 K).subtype)).map
              (MulAut.conj k).toMonoidHom =
            (Matrix.SpecialLinearGroup.map (algebraMap K M)).range.map
              ((subsystemGroup .F4 M {F4A2Kind.short.i, F4A2Kind.short.j}).subtype.comp
                (f4A2Iota M .short))) ∧
    ∀ α ∈ {α | IsRoot .F4 α ∧ torusRootChar x α = 1},
      ∀ z ∈ (D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω))).map
          (MulAut.conj h⁻¹).toMonoidHom, torusRootChar z α = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hKchar : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK]
    have h3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    exact h3.trans (Nat.le_self_pow (by omega) ℓ)
  set H := torusGroup .F4 Ω with hHdef
  set Q := subsystemGroup .F4 Ω {1, 2} with hQdef
  have hJ : ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)) = {1, 2} := rfl
  have hQG : Q ≤ adjointGroup .F4 Ω := subsystemGroup_le_adjointGroup_F4 _
  have hHG : H ≤ adjointGroup .F4 Ω := torusGroup_le_adjointGroup_F4
  have hNQ : H ≤ Subgroup.normalizer (Q : Set (ModGL .F4 Ω)) :=
    torusGroup_le_normalizer_subsystemGroup_F4
  have hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha) (torusGroup_le_diagonalGroup hb)
  have hΓfix := conjEntrywiseImage_inv_eq_fixed (Or.inr rfl) F hF hbij hg hgn
  have hxH : x ∈ H := by
    rw [hT₀] at hx
    exact hx.1
  have hxΓ : x ∈ Γ := by
    rw [hT₀] at hx
    exact hx.2
  have hhG : h ∈ adjointGroup .F4 Ω := hh ▸ canonicalRep_mem_adjointGroup _ Ω u
  have hhN : h ∈ Subgroup.normalizer (H : Set (ModGL .F4 Ω)) := hh ▸ canonicalRep_mem_normalizer u
  have hyH : y ∈ H := by
    rw [hy]
    exact (Subgroup.mem_normalizer_iff.1 hhN x).1 hxH
  have hyp : orderOf y = p := by
    rw [hy, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj h).injective x, hxp]
  have hSy : {β | IsRoot .F4 β ∧ torusRootChar y β = 1} = parabolicRoots .F4 {1, 2} := by
    rw [hy, hh, survivingRoots_canonicalRep_conj hxH u, hu, hJ]
  have hχy : ∀ β ∈ parabolicRoots .F4 ({1, 2} : Set (Fin Tag.F4.rank)),
      torusRootChar y β = 1 := fun β hβ => by
    rw [← hSy] at hβ
    exact hβ.2
  have hsingle : ∀ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)),
      (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ parabolicRoots .F4 ({1, 2} : Set (Fin Tag.F4.rank)) :=
    fun i hi => ⟨isRoot_single .F4 i, fun k hk => Pi.single_eq_of_ne (fun e => hk (by
      rw [e]
      exact hi)) 1⟩
  obtain ⟨c', hc'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hc'p : c' ^ p = 1 := rootDiagUnit_injective (by
    rw [← rootDiagUnit_pow, ← hc', ← hyp, pow_orderOf_eq_one, rootDiagUnit_one])
  have hc'1 : c' ≠ 1 := fun h1 => by
    rw [h1, rootDiagUnit_one] at hc'
    rw [hc', orderOf_one] at hyp
    exact hp.one_lt.ne hyp
  have hker : rootCharKernel c' = parabolicRoots .F4 {1, 2} := by
    rw [← hSy]
    ext β
    constructor
    · rintro ⟨hβ, h1⟩
      refine ⟨hβ, ?_⟩
      rw [hc', torusRootChar_rootDiagUnit c' hβ, h1, Units.val_one]
    · rintro ⟨hβ, h1⟩
      refine ⟨hβ, ?_⟩
      rw [hc', torusRootChar_rootDiagUnit c' hβ] at h1
      exact Units.val_eq_one.1 h1
  have hCy : adjointGroup .F4 Ω ⊓ Subgroup.centralizer {y} = H ⊔ Q := by
    have h1 := toralCentralizer_eq_toralRootGroup_of_le
      (F4_rootCharStabilizer_le_kernelReflectionGroup hp hp3 hc'p hc'1)
    rw [toralCentralizer, toralRootGroup, ← hc', hker, ← subsystemGroup_eq_rootSpan] at h1
    exact h1
  have hHQset : ((H ⊔ Q : Subgroup (ModGL .F4 Ω)) : Set (ModGL .F4 Ω)) =
      (H : Set (ModGL .F4 Ω)) * (Q : Set (ModGL .F4 Ω)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNQ
  have hFh : Units.map (entrywiseHom F) h = h := by
    rw [hh]
    exact entrywise_canonicalRep (RingEquiv.ofBijective F hbij) u
  set m := h * n * h⁻¹ with hm
  have hg1G : g * h⁻¹ ∈ adjointGroup .F4 Ω := mul_mem hg (inv_mem hhG)
  have hg1n : (g * h⁻¹)⁻¹ * Units.map (entrywiseHom F) (g * h⁻¹) = m := by
    rw [map_mul, map_inv, hFh, hm, ← hgn]
    group
  have hΓ₁eq : Γ₁ = conjEntrywiseImage K (g * h⁻¹)⁻¹ := by
    rw [hΓ₁, hΓ, map_conj_conjEntrywiseImage, mul_inv_rev, inv_inv]
  have hΓ₁fix : Γ₁ = adjointGroup .F4 Ω ⊓ (twistedEntrywise m F).eqLocus (MonoidHom.id _) := by
    rw [hΓ₁eq]
    exact conjEntrywiseImage_inv_eq_fixed (Or.inr rfl) F hF hbij hg1G hg1n
  have hΓ₁G : Γ₁ ≤ adjointGroup .F4 Ω := by
    rw [hΓ₁fix]
    exact inf_le_left
  have hmN : m ∈ monomialSubgroup .F4 Ω := by
    rw [hm, hh, hn]
    exact mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup Ω u)
      (canonicalRep_mem_monomialSubgroup Ω _)) (inv_mem (canonicalRep_mem_monomialSubgroup Ω u))
  have hmw : MapsRootLines m (u * f4Coxeter ^ 3 * u⁻¹) := by
    rw [hm, hh, hn]
    exact ((mapsRootLines_canonicalRep u).mul (mapsRootLines_canonicalRep _)).mul
      (mapsRootLines_canonicalRep u).inv
  have hwe : ∀ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)),
      (u * f4Coxeter ^ 3 * u⁻¹) • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) =
        ((simple .F4 1 * simple .F4 2) ^ ε) • Pi.single i 1 := fun i hi => by
    have hmem : ofLattice (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
        Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {f4Index 1, f4Index 2}) :=
      Submodule.subset_span ⟨_, hJ ▸ hsingle i hi, rfl⟩
    have h1 := huw _ hmem
    rw [weylAct_ofLattice, weylAct_ofLattice] at h1
    exact ofLattice_injective h1
  obtain ⟨a, haQ, hfixQ⟩ := exists_subsystemGroup_inf_fixed_eq K Ω F hF hmN hmw hε
    (hwe 1 (Or.inl rfl)) (hwe 2 (Or.inr rfl))
  have hQΓ₁ : Q ⊓ Γ₁ = ((subsystemGroup .F4 K {1, 2}).map (baseChangeGL (algebraMap K Ω))).map
      (MulAut.conj a).toMonoidHom := by
    rw [← hfixQ, hΓ₁fix, ← inf_assoc, inf_of_le_left hQG]
  have hDHQ : D ≤ H ⊔ Q := by
    rw [hD, ← hCy]
    exact inf_le_inf_right _ hΓ₁G
  have hQy : Q ≤ Subgroup.centralizer {y} :=
    subsystemGroup_le_centralizer_of_torusRootChar hyH (hχy _ (hsingle 1 (Or.inl rfl)))
      (hχy _ (hsingle 2 (Or.inr rfl)))
  have hRD : Q ⊓ Γ₁ ≤ D := by
    rw [hD]
    exact le_inf inf_le_right (inf_le_left.trans hQy)
  obtain ⟨-, -, hrbijK, -, -, -, -, -, -, -, -⟩ := F4_native_B2_faithful_Sp4_all_characteristics K
  set ιa : ModGL .F4 K →* ModGL .F4 Ω :=
    (MulAut.conj a).toMonoidHom.comp (baseChangeGL (algebraMap K Ω)) with hιa
  have hιa_inj : Function.Injective ιa :=
    (MulAut.conj a).injective.comp (baseChangeGL_injective (τ := .F4) (algebraMap K Ω))
  have hQΓmap : Q ⊓ Γ₁ = (subsystemGroup .F4 K {1, 2}).map ιa := by
    rw [hQΓ₁, Subgroup.map_map]
  set e₁ : subsystemGroup .F4 K {1, 2} ≃* (Q ⊓ Γ₁ : Subgroup (ModGL .F4 Ω)) :=
    (Subgroup.equivMapOfInjective _ ιa hιa_inj).trans (MulEquiv.subgroupCongr hQΓmap.symm)
    with he₁
  set e₂ : subsystemGroup .F4 K {1, 2} ≃* matrixIsometryGroup (f4J0 K) :=
    MulEquiv.ofBijective (f4B2Rep K) hrbijK with he₂
  set eS : (Q ⊓ Γ₁ : Subgroup (ModGL .F4 Ω)) ≃* matrixIsometryGroup (f4J0 K) := e₁.symm.trans e₂
    with heS
  have hSq : CFSG.IsQuasisimple (Q ⊓ Γ₁ : Subgroup (ModGL .F4 Ω)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eS.symm (isQuasisimple_f4Sp K hq3)
  have hSperf : ⁅Q ⊓ Γ₁, Q ⊓ Γ₁⁆ = Q ⊓ Γ₁ := commutator_eq_self_of_isPerfect hSq.1
  have hRS : R = Q ⊓ Γ₁ := by
    rw [hR]
    refine le_antisymm (le_inf ?_ ?_) ?_
    · exact (Subgroup.commutator_mono hDHQ hDHQ).trans
        (commutator_sup_le_of_le_normalizer hHcomm hNQ)
    · exact (commutator_le_self D).trans (hD ▸ inf_le_left)
    · calc Q ⊓ Γ₁ = ⁅Q ⊓ Γ₁, Q ⊓ Γ₁⁆ := hSperf.symm
        _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hRD hRD
  set e : R ≃* matrixIsometryGroup (f4J0 K) := (MulEquiv.subgroupCongr hRS).trans eS with he
  have he_spec : ∀ z : R, ∃ g' : subsystemGroup .F4 K {1, 2},
      (z : ModGL .F4 Ω) = a * baseChangeGL (algebraMap K Ω) (g' : ModGL .F4 K) * a⁻¹ ∧
        e z = f4B2Rep K g' := fun z => by
    refine ⟨e₁.symm (MulEquiv.subgroupCongr hRS z), ?_, rfl⟩
    have h1 := congrArg Subtype.val (e₁.apply_symm_apply (MulEquiv.subgroupCongr hRS z))
    exact h1.symm
  have hRq : CFSG.IsQuasisimple R := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (isQuasisimple_f4Sp K hq3)
  have hcenter : ∀ z : R, z ∈ Subgroup.center R ↔
      (((e z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 ∨
        (((e z : matrixIsometryGroup (f4J0 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          -1 := fun z => by
    rw [← mem_center_f4Sp_iff K (e z)]
    constructor
    · intro hz
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g'
      obtain ⟨w', rfl⟩ := e.surjective g'
      rw [← map_mul, ← map_mul, hz w']
    · intro hz
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w'
      apply e.injective
      rw [map_mul, map_mul, hz (e w')]
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hne : (⟨-1, neg_one_mem_f4Sp K⟩ : matrixIsometryGroup (f4J0 K)) ≠ 1 := by
      intro h1
      have h2 := congrArg (fun A : matrixIsometryGroup (f4J0 K) =>
        ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h1
      simp at h2
      exact hKchar (neg_one_eq_one_iff.1 h2)
    apply hne
    have h3 : e.symm ⟨-1, neg_one_mem_f4Sp K⟩ = 1 :=
      Subtype.ext ((Subgroup.eq_bot_iff_forall R).1 hbot _ (e.symm ⟨-1, neg_one_mem_f4Sp K⟩).2)
    rw [← e.apply_symm_apply ⟨-1, neg_one_mem_f4Sp K⟩, h3, map_one]
  have hcard2 : Nat.card (Subgroup.center R) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact natCard_center_f4Sp K hKchar
  have hRD' : R ≤ D := hRS ▸ hRD
  have hcentR : ∀ z ∈ H ⊔ Q, z ∈ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ↔
      z ∈ H ∧ torusRootChar z (Pi.single 1 1) = 1 ∧ torusRootChar z (Pi.single 2 1) = 1 :=
    fun z hz => by
      rw [hRS, hQΓ₁]
      exact mem_centralizer_conj_subsystemGroup_iff (algebraMap K Ω) haQ hz
  have hHmap : H.map (MulAut.conj h).toMonoidHom = H := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hhN z').1 hz'
    · intro hz
      refine ⟨h⁻¹ * z * h, ?_, by simp [mul_assoc]⟩
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hhN) z).1 hz
      simpa only [inv_inv, SetLike.mem_coe] using h1
  have hHΓ₁ : H ⊓ Γ₁ = T₀.map (MulAut.conj h).toMonoidHom := by
    rw [hT₀, Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective, hHmap, hΓ₁]
  have hCDR : ∀ z, z ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ↔
      z ∈ T₀.map (MulAut.conj h).toMonoidHom ∧ torusRootChar z (Pi.single 1 1) = 1 ∧
        torusRootChar z (Pi.single 2 1) = 1 := fun z => by
    rw [← hHΓ₁]
    constructor
    · rintro ⟨hzD, hzC⟩
      obtain ⟨hzH, h1, h2⟩ := (hcentR z (hDHQ hzD)).1 hzC
      have hzΓ₁ : z ∈ Γ₁ := by
        rw [hD] at hzD
        exact hzD.1
      exact ⟨⟨hzH, hzΓ₁⟩, h1, h2⟩
    · rintro ⟨⟨hzH, hzΓ₁⟩, h1, h2⟩
      have hzD : z ∈ D := by
        rw [hD]
        exact ⟨hzΓ₁, Subgroup.mem_centralizer_singleton_iff.2 (hHcomm z hzH y hyH)⟩
      exact ⟨hzD, (hcentR z (Subgroup.mem_sup_left hzH)).2 ⟨hzH, h1, h2⟩⟩
  have hZD : D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) =
      (Subgroup.center D).map D.subtype := by
    ext z
    constructor
    · intro hz
      have hz' := hz
      obtain ⟨hzD, -⟩ := hz'
      obtain ⟨hzT, h1, h2⟩ := (hCDR z).1 hz
      rw [← hHΓ₁] at hzT
      refine ⟨⟨z, hzD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
      have hle : H ⊔ Q ≤ Subgroup.centralizer {z} :=
        sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.2 (hHcomm t ht z hzT.1))
          (subsystemGroup_le_centralizer_of_torusRootChar hzT.1 h1 h2)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hDHQ d.2))
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨r, hRD' hr⟩)
  have hCDRle : D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ≤
      T₀.map (MulAut.conj h).toMonoidHom := fun z hz => ((hCDR z).1 hz).1
  have hCDRcomm : ∀ z₁ ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)),
      ∀ z₂ ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)), z₁ * z₂ = z₂ * z₁ :=
    fun z₁ hz₁ z₂ hz₂ => by
      have h1 := hCDRle hz₁
      have h2 := hCDRle hz₂
      rw [← hHΓ₁] at h1 h2
      exact hHcomm z₁ h1.1 z₂ h2.1
  have hroot : ∀ α ∈ {α | IsRoot .F4 α ∧ torusRootChar x α = 1},
      ∀ z ∈ (D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω))).map
        (MulAut.conj h⁻¹).toMonoidHom, torusRootChar z α = 1 := by
    rintro α hα _ ⟨z', hz', rfl⟩
    obtain ⟨hz'T, h1, h2⟩ := (hCDR z').1 hz'
    rw [← hHΓ₁] at hz'T
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hz'T.1
    have hb1 : b 1 = 1 := by
      rw [hb, torusRootChar_rootDiagUnit b (isRoot_single .F4 1), rootChar_pi_single] at h1
      exact Units.val_eq_one.1 h1
    have hb2 : b 2 = 1 := by
      rw [hb, torusRootChar_rootDiagUnit b (isRoot_single .F4 2), rootChar_pi_single] at h2
      exact Units.val_eq_one.1 h2
    have hzH : h⁻¹ * z' * h⁻¹⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hhN) z').1 hz'T.1
    obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzH
    have hconj : rootDiagUnit .F4 b = canonicalRep (coxeterSystem .F4) Ω u * rootDiagUnit .F4 a' *
        (canonicalRep (coxeterSystem .F4) Ω u)⁻¹ := by
      rw [← hb, ← ha', ← hh]
      group
    have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff b a' u).1 hconj
    have huα : u • α ∈ parabolicRoots .F4 ({1, 2} : Set (Fin Tag.F4.rank)) := by
      rw [← hJ, ← hu]
      exact ⟨α, hα, rfl⟩
    change torusRootChar (h⁻¹ * z' * h⁻¹⁻¹) α = 1
    rw [ha', torusRootChar_rootDiagUnit a' hα.1, ← hchar,
      rootChar_eq_one_of_mem_parabolicRoots hb1 hb2 huα, Units.val_one]
  have hxΓ' : x ∈ conjEntrywiseImage K g⁻¹ := hΓ ▸ hxΓ
  obtain ⟨c, hcC, hcx⟩ := hxΓ'
  set x₀ : adjointGroup .F4 K := ⟨c, hcC⟩ with hx₀def
  have hx₀ : baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ := by
    rw [← hcx]
    simp only [hx₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set ι' : adjointGroup .F4 K →* ModGL .F4 Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype with hι'
  have hι'inj : Function.Injective ι' :=
    (baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective
  have hyx₀ : g * h⁻¹ * y * (g * h⁻¹)⁻¹ = ι' x₀ := by
    rw [hy]
    change _ = baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K)
    rw [hx₀]
    group
  have hΓ₁' : ∀ d, d ∈ Γ₁ ↔ ∃ w : adjointGroup .F4 K, g * h⁻¹ * d * (g * h⁻¹)⁻¹ = ι' w := by
    intro d
    rw [hΓ₁eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, hw⟩, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      change _ = baseChangeGL (algebraMap K Ω) w
      group
    · rintro ⟨w, hw⟩
      refine ⟨w, w.2, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      change (g * h⁻¹)⁻¹ * baseChangeGL (algebraMap K Ω) (w : ModGL .F4 K) * (g * h⁻¹)⁻¹⁻¹ = d
      rw [show baseChangeGL (algebraMap K Ω) (w : ModGL .F4 K) = ι' w from rfl, ← hw]
      group
  have hD₀ : (Subgroup.centralizer {x₀}).map ι' = D.map (MulAut.conj (g * h⁻¹)).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwx : w * x₀ = x₀ * w := Subgroup.mem_centralizer_singleton_iff.1 hw
      refine ⟨(g * h⁻¹)⁻¹ * ι' w * (g * h⁻¹), ?_, ?_⟩
      · rw [hD]
        refine ⟨(hΓ₁' _).2 ⟨w, by group⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have e1 : ι' w * ι' x₀ = ι' x₀ * ι' w := by rw [← map_mul, hwx, map_mul]
        rw [← hyx₀] at e1
        calc (g * h⁻¹)⁻¹ * ι' w * (g * h⁻¹) * y =
              (g * h⁻¹)⁻¹ * (ι' w * (g * h⁻¹ * y * (g * h⁻¹)⁻¹)) * (g * h⁻¹) := by group
          _ = (g * h⁻¹)⁻¹ * ((g * h⁻¹ * y * (g * h⁻¹)⁻¹) * ι' w) * (g * h⁻¹) := by rw [e1]
          _ = y * ((g * h⁻¹)⁻¹ * ι' w * (g * h⁻¹)) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · rintro ⟨d, hdD, rfl⟩
      rw [hD] at hdD
      obtain ⟨hdΓ, hdy⟩ := hdD
      obtain ⟨w, hw⟩ := (hΓ₁' d).1 hdΓ
      refine ⟨w, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · apply hι'inj
        have hdy' := Subgroup.mem_centralizer_singleton_iff.1 hdy
        rw [map_mul, map_mul, ← hw, ← hyx₀]
        calc g * h⁻¹ * d * (g * h⁻¹)⁻¹ * (g * h⁻¹ * y * (g * h⁻¹)⁻¹) =
              g * h⁻¹ * (d * y) * (g * h⁻¹)⁻¹ := by group
          _ = g * h⁻¹ * (y * d) * (g * h⁻¹)⁻¹ := by rw [hdy']
          _ = g * h⁻¹ * y * (g * h⁻¹)⁻¹ * (g * h⁻¹ * d * (g * h⁻¹)⁻¹) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hw.symm
  have hR₀' : ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆.map ι' =
      R.map (MulAut.conj (g * h⁻¹)).toMonoidHom := by
    rw [Subgroup.map_commutator, hD₀, ← Subgroup.map_commutator, hR]
  set SK : Subgroup (ModGL .F4 K) := (simpleRootSL2 .F4 K 2).range with hSK
  have hSKQ : SK ≤ subsystemGroup .F4 K {1, 2} := by
    rw [hSK, range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c', rfl⟩ | ⟨c', rfl⟩)
    exacts [xUnit_mem_subsystemGroup (Or.inr rfl) c', yUnit_mem_subsystemGroup (Or.inr rfl) c']
  set TΩ : Subgroup (ModGL .F4 Ω) :=
    (SK.map (baseChangeGL (algebraMap K Ω))).map (MulAut.conj (g * h⁻¹ * a)).toMonoidHom with hTΩ
  have hTR : TΩ ≤ R.map (MulAut.conj (g * h⁻¹)).toMonoidHom := by
    rintro _ ⟨_, ⟨s', hs', rfl⟩, rfl⟩
    refine ⟨a * baseChangeGL (algebraMap K Ω) s' * a⁻¹, ?_, ?_⟩
    · rw [hRS, hQΓ₁]
      exact ⟨_, ⟨s', hSKQ hs', rfl⟩, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hTrange : TΩ ≤ ι'.range := by
    rw [← hR₀'] at hTR
    exact hTR.trans (Subgroup.map_le_range _ _)
  set R₀ : Subgroup (adjointGroup .F4 K) := TΩ.comap ι' with hR₀
  have hR₀le : R₀ ≤ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ := by
    intro w hw
    have h1 : ι' w ∈ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆.map ι' := by
      rw [hR₀']
      exact hTR hw
    obtain ⟨w', hw', hww'⟩ := h1
    rw [← hι'inj hww']
    exact hw'
  have hR₀map : R₀.map ι' = TΩ := Subgroup.map_comap_eq_self hTrange
  have haG : a ∈ adjointGroup .F4 Ω := hQG haQ
  set k := (g * h⁻¹ * a)⁻¹ with hk
  have hkG : k ∈ adjointGroup .F4 Ω := inv_mem (mul_mem hg1G haG)
  obtain ⟨M, hMfin, kM, hkMG, hkMk⟩ := exists_finite_mem_map_adjointGroup (Or.inr rfl) K hkG
  have hbc : ∀ z : ModGL .F4 K, baseChangeGL (algebraMap M Ω) (baseChangeGL (algebraMap K M) z) =
      baseChangeGL (algebraMap K Ω) z := fun z => by
    rw [baseChangeGL_baseChangeGL, ← IsScalarTower.algebraMap_eq]
  have hSL : ∀ A : SL2 K, Matrix.SpecialLinearGroup.map (algebraMap M Ω)
      (Matrix.SpecialLinearGroup.map (algebraMap K M) A) =
        Matrix.SpecialLinearGroup.map (algebraMap K Ω) A := fun A => by
    have hcomp : (algebraMap M Ω).comp (algebraMap K M) = algebraMap K Ω :=
      (IsScalarTower.algebraMap_eq K M Ω).symm
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_map]
    rw [← RingHom.coe_comp, hcomp]
  have hbcinj : Function.Injective (baseChangeGL (τ := .F4) (algebraMap M Ω)) :=
    baseChangeGL_injective _
  have hkeq : ((R₀.map ((baseChangeGL (algebraMap K M)).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj kM).toMonoidHom) =
      (Matrix.SpecialLinearGroup.map (algebraMap K M)).range.map
        ((subsystemGroup .F4 M {F4A2Kind.short.i, F4A2Kind.short.j}).subtype.comp
          (f4A2Iota M .short)) := by
    apply Subgroup.map_injective hbcinj
    have hL : ((R₀.map ((baseChangeGL (algebraMap K M)).comp (adjointGroup .F4 K).subtype)).map
        (MulAut.conj kM).toMonoidHom).map (baseChangeGL (algebraMap M Ω)) =
        SK.map (baseChangeGL (algebraMap K Ω)) := by
      ext z
      constructor
      · rintro ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
        obtain ⟨_, ⟨s', hs', rfl⟩, hws⟩ := hw
        refine ⟨s', hs', ?_⟩
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          Subgroup.coe_subtype, map_mul, map_inv, hkMk, hbc]
        change _ = k * ι' w * k⁻¹
        rw [← hws, hk]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨s', hs', rfl⟩
        have hmem : (g * h⁻¹ * a) * baseChangeGL (algebraMap K Ω) s' * (g * h⁻¹ * a)⁻¹ ∈ TΩ :=
          ⟨_, ⟨s', hs', rfl⟩, rfl⟩
        rw [← hR₀map] at hmem
        obtain ⟨w, hw, hws⟩ := hmem
        refine ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, ?_⟩
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          Subgroup.coe_subtype, map_mul, map_inv, hkMk, hbc]
        change k * ι' w * k⁻¹ = _
        rw [hws, hk]
        group
    rw [hL]
    ext z
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      refine ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [coe_f4A2Iota, baseChangeGL_simpleRootSL2_of_field, hSL,
        baseChangeGL_simpleRootSL2_of_field]
      rfl
    · rintro ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
      refine ⟨_, ⟨A, rfl⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [coe_f4A2Iota, baseChangeGL_simpleRootSL2_of_field, baseChangeGL_simpleRootSL2_of_field,
        hSL]
      rfl
  refine ⟨by rw [hCy]; exact hHQset, ⟨a, haQ, hRS, hQΓ₁, e, he_spec, hcenter⟩, hRq, hRq.1,
    CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hRq, hRne, hcard2,
    ⟨hZD, hCDR, hCDRle, hCDRcomm⟩,
    ⟨x₀, hx₀, hD₀, hR₀', R₀, hR₀le, M, hMfin, kM, hkMG, hkeq⟩, hroot⟩

end CFSG.RankThree.Chevalley
