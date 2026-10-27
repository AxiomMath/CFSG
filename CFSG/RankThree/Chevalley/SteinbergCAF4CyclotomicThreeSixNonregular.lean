module

public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularA2Centralizer
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeTorus
public import CFSG.RankThree.Chevalley.SteinbergCFF4CyclotomicSix
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourNonregular
public import CFSG.RankThree.Chevalley.SteinbergCAF4NonregularA2Fixed

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups SteinbergBN EvenF4QPlus RootSpace
  CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise MatrixGroups

theorem odd_F4_cyclotomic_three_six_nonregular_derived_centralizers {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K)
    (ε : ℤ) (w : WeylGroup .F4) (hεw : (ε = 1 ∧ w = f4Coxeter ^ 4) ∨ (ε = -1 ∧ w = f4PhiSix))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω w) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω)
    (hx : x ∈ T₀) (hxp : orderOf x = p) (u : WeylGroup .F4) (κ : F4A2Kind) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1)
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 {κ.i, κ.j})
    (huw : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {κ.i, κ.j}),
      weylAct .F4 (u * w * u⁻¹) z = ε • weylAct .F4 ((simple .F4 κ.i * simple .F4 κ.j) ^ δ) z)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D R : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) (hR : R = ⁅D, D⁆) :
    ((adjointGroup .F4 Ω ⊓ Subgroup.centralizer {y} : Subgroup (ModGL .F4 Ω)) :
        Set (ModGL .F4 Ω)) =
      (torusGroup .F4 Ω : Set (ModGL .F4 Ω)) *
        (subsystemGroup .F4 Ω {κ.i, κ.j} : Set (ModGL .F4 Ω)) ∧
    (∃ a ∈ subsystemGroup .F4 Ω {κ.i, κ.j},
      R = subsystemGroup .F4 Ω {κ.i, κ.j} ⊓ Γ₁ ∧
      (ε = 1 → ∀ z, z ∈ R ↔ ∃ Y : SL(3, K), z = a *
        ((f4A2Equiv Ω κ).symm (Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y) :
          ModGL .F4 Ω) * a⁻¹) ∧
      (ε = -1 → ∀ z, z ∈ R ↔ ∃ X : SL(3, Ω),
        Matrix.SpecialLinearGroup.toGL X ∈ CFSG.RankThree.Classical2.unitarySet (Nat.card K) 3 ∧
          z = a * ((f4A2Equiv Ω κ).symm X : ModGL .F4 Ω) * a⁻¹)) ∧
    CFSG.IsQuasisimple R ∧ Group.IsPerfect R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
      (∀ (g' : subsystemGroup .F4 Ω {κ.i, κ.j}) (hg' : (g' : ModGL .F4 Ω) ∈ R),
        (⟨g', hg'⟩ : R) ∈ Subgroup.center R ↔ ∃ c : Ω,
          ((f4A2Equiv Ω κ g' : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) c) ∧
      Nat.card (Subgroup.center R) = Int.gcd 3 ((Nat.card K : ℤ) - ε) ∧
    (D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = (Subgroup.center D).map D.subtype ∧
      Odd (Nat.card (Subgroup.center D)) ∧
      ∀ z, z ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ↔
        z ∈ T₀.map (MulAut.conj h).toMonoidHom ∧ torusRootChar z (Pi.single κ.i 1) = 1 ∧
          torusRootChar z (Pi.single κ.j 1) = 1) ∧
    ∃ x₀ : adjointGroup .F4 K,
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
              ((subsystemGroup .F4 M {κ.i, κ.j}).subtype.comp (f4A2Iota M κ)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK]
    have h3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    exact h3.trans (Nat.le_self_pow (by omega) ℓ)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hεw with ⟨h1, -⟩ | ⟨h1, -⟩
    exacts [Or.inl h1, Or.inr h1]
  set H := torusGroup .F4 Ω with hHdef
  set Q := subsystemGroup .F4 Ω {κ.i, κ.j} with hQdef
  have hQG : Q ≤ adjointGroup .F4 Ω := subsystemGroup_le_adjointGroup_F4 _
  have hNQ : H ≤ Subgroup.normalizer (Q : Set (ModGL .F4 Ω)) := by
    rw [hHdef, hQdef, subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha) (torusGroup_le_diagonalGroup hb)
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
  have hSy : {β | IsRoot .F4 β ∧ torusRootChar y β = 1} = parabolicRoots .F4 {κ.i, κ.j} := by
    rw [hy, hh, survivingRoots_canonicalRep_conj hxH u, hu]
  have hχy : ∀ β ∈ parabolicRoots .F4 ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      torusRootChar y β = 1 := fun β hβ => by
    rw [← hSy] at hβ
    exact hβ.2
  have hsingle : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈
        parabolicRoots .F4 ({κ.i, κ.j} : Set (Fin Tag.F4.rank)) :=
    fun k hk => ⟨isRoot_single .F4 k, fun l hl => Pi.single_eq_of_ne (fun e => hl (by
      rw [e]
      exact hk)) 1⟩
  obtain ⟨c', hc'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hc'p : c' ^ p = 1 := rootDiagUnit_injective (by
    rw [← rootDiagUnit_pow, ← hc', ← hyp, pow_orderOf_eq_one, rootDiagUnit_one])
  have hc'1 : c' ≠ 1 := fun h1 => by
    rw [h1, rootDiagUnit_one] at hc'
    rw [hc', orderOf_one] at hyp
    exact hp.one_lt.ne hyp
  have hker : rootCharKernel c' = parabolicRoots .F4 {κ.i, κ.j} := by
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
  have hmw : MapsRootLines m (u * w * u⁻¹) := by
    rw [hm, hh, hn]
    exact ((mapsRootLines_canonicalRep u).mul (mapsRootLines_canonicalRep _)).mul
      (mapsRootLines_canonicalRep u).inv
  have hwe : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      (u * w * u⁻¹) • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
        ε • ((simple .F4 κ.i * simple .F4 κ.j) ^ δ • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) :=
    fun k hk => by
      have hmem : ofLattice (Pi.single k 1 : Fin Tag.F4.rank → ℤ) ∈
          Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {κ.i, κ.j}) :=
        Submodule.subset_span ⟨_, hsingle k hk, rfl⟩
      have h1 := huw _ hmem
      rw [weylAct_ofLattice, weylAct_ofLattice] at h1
      apply ofLattice_injective
      rcases hε with rfl | rfl
      · rw [h1, one_smul, one_smul]
      · rw [h1, neg_smul, one_smul, neg_smul, one_smul, ofLattice_neg]
  obtain ⟨a, haQ, hsplitR, hunitR, hRq', hcenR, hcardR, b₀, hb₀Q, hb₀⟩ :=
    exists_A2_inf_fixed_eq hℓ hf K hK Ω F hF (by omega) κ hmN hmw hε hδ hwe (Q ⊓ Γ₁)
      (by rw [hΓ₁fix, ← inf_assoc, inf_of_le_left hQG])
  have hDHQ : D ≤ H ⊔ Q := by
    rw [hD, ← hCy]
    exact inf_le_inf_right _ hΓ₁G
  have hQy : Q ≤ Subgroup.centralizer {y} :=
    subsystemGroup_le_centralizer_of_forall_torusRootChar hyH fun k hk => hχy _ (hsingle k hk)
  have hRD : Q ⊓ Γ₁ ≤ D := by
    rw [hD]
    exact le_inf inf_le_right (inf_le_left.trans hQy)
  have hSperf : ⁅Q ⊓ Γ₁, Q ⊓ Γ₁⁆ = Q ⊓ Γ₁ := commutator_eq_self_of_isPerfect hRq'.1
  have hRS : R = Q ⊓ Γ₁ := by
    rw [hR]
    refine le_antisymm (le_inf ?_ ?_) ?_
    · exact (Subgroup.commutator_mono hDHQ hDHQ).trans
        (commutator_sup_le_of_le_normalizer hHcomm hNQ)
    · exact (commutator_le_self D).trans (hD ▸ inf_le_left)
    · calc Q ⊓ Γ₁ = ⁅Q ⊓ Γ₁, Q ⊓ Γ₁⁆ := hSperf.symm
        _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hRD hRD
  have hRD' : R ≤ D := hRS ▸ hRD
  obtain ⟨U, hU, hRU⟩ : ∃ U : Set (SL(3, Ω)), (∀ C : GL (Fin 3) Ω,
      (∀ X ∈ U, (C : Matrix (Fin 3) (Fin 3) Ω) * (X : Matrix (Fin 3) (Fin 3) Ω) =
        (X : Matrix (Fin 3) (Fin 3) Ω) * C) →
          ∃ c : Ω, (C : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) c) ∧
      ∀ z, z ∈ Q ⊓ Γ₁ ↔ ∃ X ∈ U, z = a * ((f4A2Equiv Ω κ).symm X : ModGL .F4 Ω) * a⁻¹ := by
    rcases hε with rfl | rfl
    · refine ⟨{X | ∃ Y : SL(3, K), X = Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y},
        exists_scalar_of_commute_map_SL3 (algebraMap K Ω), fun z => ?_⟩
      rw [hsplitR rfl z]
      constructor
      · rintro ⟨Y, rfl⟩
        exact ⟨_, ⟨Y, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
        exact ⟨Y, rfl⟩
    · refine ⟨{X | Matrix.SpecialLinearGroup.toGL X ∈
          CFSG.RankThree.Classical2.unitarySet (Nat.card K) 3},
        exists_scalar_of_commute_unitary (K := K), fun z => ?_⟩
      rw [hunitR rfl z]
      constructor
      · rintro ⟨X, hX, rfl⟩
        exact ⟨X, hX, rfl⟩
      · rintro ⟨X, hX, rfl⟩
        exact ⟨X, hX, rfl⟩
  have hcentR : ∀ z ∈ H ⊔ Q, z ∈ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) ↔
      z ∈ H ∧ torusRootChar z (Pi.single κ.i 1) = 1 ∧ torusRootChar z (Pi.single κ.j 1) = 1 :=
    fun z hz => by
      rw [← mem_centralizer_conj_A2_iff κ hU haQ hz, Subgroup.mem_centralizer_iff, hRS]
      constructor
      · intro h1 X hX
        exact (h1 _ ((hRU _).2 ⟨X, hX, rfl⟩)).symm
      · intro h1 r' hr'
        obtain ⟨X, hX, rfl⟩ := (hRU r').1 hr'
        exact (h1 X hX).symm
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
      z ∈ T₀.map (MulAut.conj h).toMonoidHom ∧ torusRootChar z (Pi.single κ.i 1) = 1 ∧
        torusRootChar z (Pi.single κ.j 1) = 1 := fun z => by
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
          (subsystemGroup_le_centralizer_of_forall_torusRootChar hzT.1 (by
            rintro k (rfl | hk)
            · exact h1
            · rw [Set.mem_singleton_iff] at hk
              rw [hk]
              exact h2))
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hDHQ d.2))
    · rintro ⟨w', hw', rfl⟩
      refine ⟨w'.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hw' ⟨r, hRD' hr⟩)
  have hoddT₀ : Odd (Nat.card T₀) := by
    have hcardT : Nat.card (T₀.map (MulAut.conj g).toMonoidHom) = Nat.card T₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [← hcardT]
    rcases hεw with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ((F4_cyclotomic_three_torus_and_regular_prime_centralizers K Ω F hF n hn).2 g hg hgn
        Γ T₀ _ hΓ hT₀ rfl).2.2.2.1
    · exact ((F4_cyclotomic_six_torus_and_surviving_A2_kernels K Ω F hF n hn).2.2.2.2 g hg hgn
        Γ T₀ _ hΓ hT₀ rfl).2.2.2.1
  have hoddZ : Odd (Nat.card (Subgroup.center D)) := by
    have h1 : Nat.card ((Subgroup.center D).map D.subtype) = Nat.card (Subgroup.center D) :=
      Subgroup.card_map_of_injective D.subtype_injective
    have h2 : Nat.card (T₀.map (MulAut.conj h).toMonoidHom) = Nat.card T₀ :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    have hle : (Subgroup.center D).map D.subtype ≤ T₀.map (MulAut.conj h).toMonoidHom := by
      rw [← hZD]
      exact fun z hz => ((hCDR z).1 hz).1
    rw [← h1]
    exact Odd.of_dvd_nat (h2 ▸ hoddT₀) (Subgroup.card_dvd_of_le hle)
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
  set SK : Subgroup (ModGL .F4 K) := (simpleRootSL2 .F4 K κ.i).range with hSK
  set TΩ : Subgroup (ModGL .F4 Ω) :=
    (SK.map (baseChangeGL (algebraMap K Ω))).map (MulAut.conj (g * h⁻¹ * b₀)).toMonoidHom
    with hTΩ
  have hTR : TΩ ≤ R.map (MulAut.conj (g * h⁻¹)).toMonoidHom := by
    rintro _ ⟨_, ⟨_, ⟨Y, rfl⟩, rfl⟩, rfl⟩
    refine ⟨b₀ * baseChangeGL (algebraMap K Ω) (simpleRootSL2 .F4 K κ.i Y) * b₀⁻¹, ?_, ?_⟩
    · rw [hRS, baseChangeGL_simpleRootSL2_of_field]
      exact hb₀ Y
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
  have hb₀G : b₀ ∈ adjointGroup .F4 Ω := hQG hb₀Q
  set k := (g * h⁻¹ * b₀)⁻¹ with hk
  have hkG : k ∈ adjointGroup .F4 Ω := inv_mem (mul_mem hg1G hb₀G)
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
        ((subsystemGroup .F4 M {κ.i, κ.j}).subtype.comp (f4A2Iota M κ)) := by
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
        have hmem : (g * h⁻¹ * b₀) * baseChangeGL (algebraMap K Ω) s' * (g * h⁻¹ * b₀)⁻¹ ∈ TΩ :=
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
    · rintro ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
      refine ⟨_, ⟨A, rfl⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [coe_f4A2Iota, baseChangeGL_simpleRootSL2_of_field, baseChangeGL_simpleRootSL2_of_field,
        hSL]
  subst hRS
  have hRne : subsystemGroup .F4 Ω {κ.i, κ.j} ⊓ Γ₁ ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hRq')
  refine ⟨by rw [hCy]; exact hHQset, ⟨a, haQ, rfl, hsplitR, hunitR⟩, hRq', hRq'.1,
    CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hRq', hRne, hcenR, hcardR,
    ⟨hZD, hoddZ, hCDR⟩, x₀, hx₀, hD₀, hR₀', R₀, hR₀le, M, hMfin, kM, hkMG, hkeq⟩

end CFSG.RankThree.Chevalley
