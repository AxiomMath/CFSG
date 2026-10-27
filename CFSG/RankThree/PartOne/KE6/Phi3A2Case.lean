module

public import CFSG.RankThree.PartOne.KE6.Phi3A2
public import CFSG.RankThree.PartOne.KE6.Phi3Kernel
public import CFSG.RankThree.Chevalley.SteinbergBIE6FiniteLayers
public import CFSG.RankThree.PartOne.KE6.Phi3Orbit
public import CFSG.RankThree.PartOne.KE6.Phi3Std
public import CFSG.RankThree.PartOne.KE6.Phi3Transport
public import CFSG.RankThree.PartOne.KE6.Phi6Shape

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.PartOne.KETw3 (chainRoot13_add)
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_split)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω]

theorem chainRoot13_20 :
    chainRoot chain13 2 0 = -(Pi.single (e6Index 0) 1 + Pi.single (e6Index 2) 1 :
      Fin Tag.E6.rank → ℤ) := by
  rw [chainRoot_swap, ← chainRoot13_add 0 1 2, chainRoot13_simple.1, chainRoot13_simple.2.1]

theorem exists_positive_of_conj {T : WeylGroup Tag.E6} {L : List (List ℤ)}
    (hL : L ∈ e6T3Orbit) (hLT : weylMatrix T = toMat Tag.E6.rank L)
    (hT : ∀ β ∈ parabolicRoots Tag.E6 support13, T • β ∈ parabolicRoots Tag.E6 support13) :
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      T • chainRoot chain13 i j = chainRoot chain13 (π i) (π j) := by
  have hcol : ∀ j : Fin Tag.E6.rank, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
      parabolicRoots Tag.E6 support13 → ∀ i : Fin Tag.E6.rank, i ≠ e6Index 0 → i ≠ e6Index 2 →
        lget L i j = 0 := by
    intro j hj i hi0 hi2
    have h := (hT _ hj).2 i (by
      rintro (h | h)
      · exact hi0 h
      · exact hi2 h)
    rw [← smul_single_apply_eq_lget hLT]
    exact h
  obtain ⟨he0, he2, -⟩ := single13_mem
  have hsh := e6T3Orbit_A2_shape L hL (fun i hi0 hi2 => ⟨hcol _ he0 i hi0 hi2,
    hcol _ he2 i hi0 hi2⟩)
  have hadd : ∀ x y : Fin Tag.E6.rank → ℤ, T • (x + y) = T • x + T • y := fun x y =>
    CFSG.RankThree.Lattice.weyl_smul_add T x y
  have hsup : ∀ (j : Fin Tag.E6.rank) (a b : ℤ),
      (j = e6Index 0 ∨ j = e6Index 2) → (∀ i : Fin Tag.E6.rank, i ≠ e6Index 0 → i ≠ e6Index 2 →
        lget L i j = 0) → lget L (e6Index 0) j = a → lget L (e6Index 2) j = b →
      T • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        a • (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) +
          b • (Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) := by
    intro j a b _ hz ha hb
    funext i
    rw [smul_single_apply_eq_lget hLT, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases hi0 : i = e6Index 0
    · subst hi0
      have h02' : (e6Index 0 : Fin Tag.E6.rank) ≠ e6Index 2 := by decide
      rw [ha, Pi.single_eq_same, Pi.single_eq_of_ne h02', mul_one, mul_zero, add_zero]
    · by_cases hi2 : i = e6Index 2
      · subst hi2
        rw [hb, Pi.single_eq_same, Pi.single_eq_of_ne hi0, mul_one, mul_zero, zero_add]
      · rw [hz i hi0 hi2, Pi.single_eq_of_ne hi0, Pi.single_eq_of_ne hi2]
        simp
  have hc1 : (e6Index 0 : Fin Tag.E6.rank) = 0 := rfl
  have e0 := chainRoot13_simple.1
  have e2 := chainRoot13_simple.2.1
  rcases hsh with ⟨h00, h20, h02, h22⟩ | ⟨h00, h20, h02, h22⟩
  ·
    have hT0 := hsup (e6Index 0) 0 1 (Or.inl rfl) (hcol _ he0) h00 h20
    have hT2 := hsup (e6Index 2) (-1) (-1) (Or.inr rfl) (hcol _ he2) h02 h22
    refine ⟨finRotate 3, ?_⟩
    refine transition_pos_gen (T := fun x => T • x) (ι := chain13) chainRoot13_add hadd
      (finRotate 3) ?_ ?_
    · show T • chainRoot chain13 0 1 = chainRoot chain13 (finRotate 3 0) (finRotate 3 1)
      rw [e0, hT0]
      have : (finRotate 3 0 : Fin 3) = 1 := by decide
      have h2 : (finRotate 3 1 : Fin 3) = 2 := by decide
      rw [this, h2, e2]
      module
    · show T • chainRoot chain13 1 2 = chainRoot chain13 (finRotate 3 1) (finRotate 3 2)
      rw [e2, hT2]
      have h1 : (finRotate 3 1 : Fin 3) = 2 := by decide
      have h2 : (finRotate 3 2 : Fin 3) = 0 := by decide
      rw [h1, h2, chainRoot13_20]
      module
  ·
    have hT0 := hsup (e6Index 0) (-1) (-1) (Or.inl rfl) (hcol _ he0) h00 h20
    have hT2 := hsup (e6Index 2) 1 0 (Or.inr rfl) (hcol _ he2) h02 h22
    refine ⟨(finRotate 3).symm, ?_⟩
    refine transition_pos_gen (T := fun x => T • x) (ι := chain13) chainRoot13_add hadd
      (finRotate 3).symm ?_ ?_
    · show T • chainRoot chain13 0 1 =
        chainRoot chain13 ((finRotate 3).symm 0) ((finRotate 3).symm 1)
      rw [e0, hT0]
      have h1 : ((finRotate 3).symm 0 : Fin 3) = 2 := by decide
      have h2 : ((finRotate 3).symm 1 : Fin 3) = 0 := by decide
      rw [h1, h2, chainRoot13_20]
      module
    · show T • chainRoot chain13 1 2 =
        chainRoot chain13 ((finRotate 3).symm 1) ((finRotate 3).symm 2)
      rw [e2, hT2]
      have h1 : ((finRotate 3).symm 1 : Fin 3) = 0 := by decide
      have h2 : ((finRotate 3).symm 2 : Fin 3) = 1 := by decide
      rw [h1, h2, e0]
      module

section Case

variable {Fr : Ω →+* Ω}

theorem phi3_A2_layer_gen {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support13) :
    (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 ∧
    Finite ↥(rootSpan Tag.E6 Ω S ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S ⊓
      (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    e6Commutant (((rootSpan Tag.E6 Ω S ⊓
        (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) ∧
    ∃ h₀ : ModGL Tag.E6 Ω, ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω (e6Index 0) (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) *
        h₀⁻¹ ∈ rootSpan Tag.E6 Ω S ⊓
          (phi3Theta Ω Fr).eqLocus (MonoidHom.id _) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨π, hπ⟩ := exists_positive_of_conj hL hLT hT
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π i) (π j)) (e * Fr c) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w
      (chainRoot13_mem_parabolicRoots hij).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_permuting_of_theta hFrs
    (phi3ThetaConj Ω Fr w) (phi3ThetaConj_injective w) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, hfin, hqs, -, -, -⟩ := sl3_root_permuting_frobenius_fixed_split hℓ hf hK
    π Φ b (fun i j hij t => by rw [hΦt, hFr])
  set P := rootSpan Tag.E6 Ω S ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _) with hPdef
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup_gen (phi3Theta Ω Fr) (phi3ThetaConj Ω Fr w)
    (phi3ThetaConj_conj w) hQ hmaps Φ hΦ₀
  have hmemQ₁ : ∀ y ∈ rootSpan Tag.E6 Ω S, n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun y hy => by
      rw [← hQ]
      exact ⟨y, hy, rfl⟩
  have hfinP : Finite ↥P := Finite.of_equiv _ e.symm.toEquiv
  have hqsP : CFSG.IsQuasisimple ↥P :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hqs
  set m : ModGL Tag.E6 Ω := a2Inv₁ Ω H' with hmdef
  have hmQ : m ∈ subsystemGroup Tag.E6 Ω support13 := (isA2Layer_a2Inv₁ (Ω := Ω)).mem H'
  have hconj : P.map (MulAut.conj n).toMonoidHom =
      (splitLayer (a2Inv₁ Ω) (algebraMap K Ω)).map (MulAut.conj m).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz := hmemQ₁ y hy.1
      obtain ⟨Y, hY⟩ := (hH' (e ⟨y, hy⟩ : SL(3, Ω))).1 (e ⟨y, hy⟩).2
      have h1 : a2Inv₁ Ω (e ⟨y, hy⟩ : SL(3, Ω)) = n * y * n⁻¹ :=
        (a2Inv₁_eq_iff hz).2 (he ⟨y, hy⟩)
      refine ⟨a2Inv₁ Ω (Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y), ⟨Y, rfl⟩, ?_⟩
      change m * a2Inv₁ Ω (Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y) * m⁻¹ = n * y * n⁻¹
      rw [← h1, hY, map_mul, map_mul, map_inv]
    · rintro ⟨s, ⟨Y, rfl⟩, rfl⟩
      have hX : H' * Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y * H'⁻¹ ∈ fixSubgroup Φ :=
        (hH' _).2 ⟨Y, rfl⟩
      obtain ⟨y, hy⟩ := e.surjective ⟨_, hX⟩
      have hz := hmemQ₁ y y.2.1
      have h1 := he y
      rw [hy] at h1
      have h2 : a2Inv₁ Ω (H' * Matrix.SpecialLinearGroup.map (algebraMap K Ω) Y * H'⁻¹) =
          n * y * n⁻¹ := (a2Inv₁_eq_iff hz).2 h1
      refine ⟨y, y.2, ?_⟩
      change n * (y : ModGL Tag.E6 Ω) * n⁻¹ = m * _ * m⁻¹
      rw [← h2, map_mul, map_mul, map_inv]
      rfl
  obtain ⟨-, -, -, -, -, -, htr, -, -, -, -, hsl, -⟩ :=
    E6_finite_A2_D4_layers_detect_full_module_commutants ℓ f hℓ hf K hK Ω Fr hFr
  have hset : ∀ A : Subgroup (ModGL Tag.E6 Ω),
      ((A.map (MulAut.conj m).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
        (fun g => m * g * m⁻¹) '' (A : Set (ModGL Tag.E6 Ω)) := fun A => by
    rw [Subgroup.coe_map]
    rfl
  have hQset : (fun g => m * g * m⁻¹) '' (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) =
      (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mul_mem (mul_mem hmQ hu) (inv_mem hmQ)
    · intro hg
      exact ⟨m⁻¹ * g * m, mul_mem (mul_mem (inv_mem hmQ) hg) hmQ, by group⟩
  have hcommP : e6Commutant (((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) := by
    rw [hconj, hset, (htr m).1, hQset]
  refine ⟨hQ, hfinP, hqsP, hcommP, n⁻¹ * m, fun B => ?_⟩
  have hB := hsl B
  have hmem : m * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * m⁻¹ ∈
        P.map (MulAut.conj n).toMonoidHom := by
    rw [hconj]
    exact ⟨_, hB, rfl⟩
  obtain ⟨y, hy, hyeq⟩ := hmem
  have hyeq' : n * y * n⁻¹ = m * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * m⁻¹ := hyeq
  have this : n⁻¹ * m * simpleRootSL2 Tag.E6 Ω (e6Index 0)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * (n⁻¹ * m)⁻¹ = y := by
    have h3 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [h3, hyeq']
    group
  rw [this]
  exact hy


theorem phi3_A2_layer_data {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    (rootSpan Tag.E6 Ω (torusRootKernel x)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 ∧
    Finite ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
      (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)) ∧
    e6Commutant (((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
        (phi3Theta Ω Fr).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) ∧
    ∃ h₀ : ModGL Tag.E6 Ω, ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω (e6Index 0) (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) *
        h₀⁻¹ ∈ rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
          (phi3Theta Ω Fr).eqLocus (MonoidHom.id _) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  exact phi3_A2_layer_gen hf hK hFr (fun α hα => hα.1) (torusRootKernel_smul_stable hFr hx) hw

theorem phi3_A2_kernelLayer {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    Nonempty (KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K Unit) := by
  obtain ⟨w, hw⟩ := hA2
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := phi3_A2_layer_data hf hK hFr hx hw
  exact ⟨KernelLayer.single (fun α hα => hα.1) hQ hfin hq hcomm ⟨e6Index 0, h₀, hsl⟩⟩

end Case

end CFSG.RankThree.PartOne.KE6
