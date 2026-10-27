module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.kerRepresentation

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4, item (4.4)

This file proves PF `(4.4)`: in the notation of Theorem `(4.3)`, the base
column `Πᵢ₀` consists exactly of the irreducible characters of `L` whose
kernels contain `K`, and the normalization consequences
`δ₀ = 1`, `Π₀₀ = 1_L`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4

universe v
universe u

/-! ## (4.4) -/

/--
Peterfalvi (4.4): in the notation of Theorem `(4.3)`, the characters `Πᵢ₀`
are exactly the irreducible characters of `L` whose kernels contain `K`.
Furthermore, the base sign is `1` and the base character is `1_L`.
-/
@[expose] public def proposition_4_4_statement
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (_h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (_hB : theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (_hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω) : Prop :=
  (∀ χ : Section1.ClassFunction L,
      Section1.IsIrreducibleCharacterOnGroup χ →
        (Section1.subgroupInKernel' χ K ↔ ∃ i, χ = piChar i j0)) ∧
    deltaSign j0 = 1 ∧
      piChar i0 j0 = Section1.principalCharacter L

end CFSG.Section4

namespace CFSG.Section4Scratch

universe u v

open Section1 Section2 Section3 Section4

/-- Peterfalvi's column sum `μⱼ = ∑ᵢ Πᵢⱼ` from `(4.5)`. -/
@[expose] public def piColumn
    {L : Type u} [Group L]
    {I J : Type*} [Fintype I]
    (piChar : I → J → ClassFunction L) (j : J) : ClassFunction L :=
  ∑ i : I, piChar i j

/-- The larger Section 4 carrier `A ∪ (W \ W₂)ᴸ`. -/
@[expose] public def a0Set
    {L : Type u} [Group L]
    (W2 W : Subgroup L) (A : Set L) : Set L :=
  A ∪ Section2.conjugateSet ((W : Set L) \ (W2 : Set L))

/-- The prime-Dade carrier `A₀ = A ∪ Vᴸ` from Hypothesis `(4.6)`, where
`V = W \ (W₁ ∪ W₂)` is the cyclic-TI set from Section 3. -/
@[expose] public def primeDadeA0Set
    {L : Type u} [Group L]
    (W1 W2 W : Subgroup L) (A : Set L) : Set L :=
  A ∪ Section2.conjugateSet (Section3.cyclicTISet W1 W2 W)

/-- Pull back a subset of the ambient group to a subgroup carrier. -/
@[expose] public def subgroupPullbackSet
    {L : Type u} [Group L]
    (K : Subgroup L) (A : Set L) : Set K :=
  {x : K | (x : L) ∈ A}

/-- The image in an ambient group of a subgroup of a subgroup carrier. -/
@[expose] public def subgroupImage
    {G : Type v} [Group G]
    (L : Subgroup G) (S : Subgroup L) : Subgroup G :=
  S.map L.subtype

/-- The image in an ambient group of a subset of a subgroup carrier. -/
@[expose] public def subgroupImageSet
    {G : Type v} [Group G]
    (L : Subgroup G) (A : Set L) : Set G :=
  {g | ∃ l : L, l ∈ A ∧ (l : G) = g}

/-- Adjoin the identity to a support set. -/
@[expose] public def withOne
    {X : Type*} [One X] (A : Set X) : Set X :=
  A ∪ ({1} : Set X)

/-- The punctured ambient set `L#`, represented on the ambient type itself. -/
@[expose] public def puncturedSet
    {L : Type u} [One L] : Set L :=
  {x : L | x ≠ 1}

/-- The index set used in `(4.9)`: non-base columns of the same degree as `k`. -/
@[expose] public def equalDegreeColumnSet
    {L : Type u} [Group L]
    {I J : Type*} [Fintype I]
    (piChar : I → J → ClassFunction L) (j0 k : J) : Set J :=
  {j : J | j ≠ j0 ∧ Section1.degree (piColumn piChar j) = Section1.degree (piColumn piChar k)}

/-- The corresponding finite subtype of equal-degree, non-base columns. -/
@[expose] public def equalDegreeColumnIndex
    {L : Type u} [Group L]
    {I J : Type*} [Fintype I]
    (piChar : I → J → ClassFunction L) [Fintype J]
    (j0 k : J) : Type _ :=
  {j : J // j ∈ equalDegreeColumnSet piChar j0 k}

public instance equalDegreeColumnIndexFintype
    {L : Type u} [Group L]
    {I J : Type*} [Fintype I]
    (piChar : I → J → ClassFunction L) [Fintype J]
    (j0 k : J) :
    Fintype (equalDegreeColumnIndex piChar j0 k) := by
  dsimp [equalDegreeColumnIndex]
  infer_instance

/-- The column sum of the `σ`-images of the `ωᵢⱼ`, used in `(4.9)(b)`. -/
@[expose] public def omegaColumnSigma
    {W : Type u} [Group W] {G : Type v} [Group G]
    {I J : Type*} [Fintype I]
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (ω : I → J → ClassFunction W) (j : J) : ClassFunction G :=
  ∑ i : I, σ (ω i j)

end CFSG.Section4Scratch

namespace CFSG.Section4

universe u v

open Section1 Section2 Section3

private theorem signed_irreducible_of_irreducible_pf44
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section3.IsSignedIrreducibleCharacter χ := by
  exact ⟨1, Or.inl rfl, χ, hχ, by simp⟩

private theorem sign_mul_self_eq_one_pf44
    {ε : ℂ} (hε : Section1.IsSign ε) :
    ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

private theorem subgroupInKernel'_of_eq_pf44
    {G : Type*} [Group G]
    {phi psi : Section1.ClassFunction G} {A : Subgroup G}
    (hEq : phi = psi) (hA : Section1.subgroupInKernel' phi A) :
    Section1.subgroupInKernel' psi A := by
  intro a
  rw [← hEq]
  exact hA a

private theorem subgroupInKernel'_subgroupRestriction_iff_pf44
    {G : Type*} [Group G]
    (H A : Subgroup G) (hAH : A ≤ H) (phi : Section1.ClassFunction G) :
    Section1.subgroupInKernel' (Section1.subgroupRestriction H phi) (A.subgroupOf H) ↔
      Section1.subgroupInKernel' phi A := by
  have hdegree :
      Section1.degree (Section1.subgroupRestriction H phi) = Section1.degree phi := by
    simp [Section1.degree, Section1.subgroupRestriction]
  constructor
  · intro h a
    simpa [Section1.subgroupRestriction, hdegree] using
      h ⟨⟨(a : G), hAH a.2⟩, a.2⟩
  · intro h a
    simpa [Section1.subgroupRestriction, hdegree] using
      h ⟨((a : A.subgroupOf H) : H), a.2⟩

private theorem subgroupInKernel'_characterInflationByHom_mk'_pf44
    {L : Type*} [Group L] {K : Subgroup L} [K.Normal]
    (chi : (L ⧸ K) →* ℂˣ) :
    Section1.subgroupInKernel'
      (Section1.characterInflationByHom (QuotientGroup.mk' K) chi) K := by
  intro k
  have hkq : QuotientGroup.mk' K (k : L) = 1 :=
    (QuotientGroup.eq_one_iff (N := K) (x := (k : L))).2 k.2
  have hdeg :
      Section1.degree (Section1.characterInflationByHom (QuotientGroup.mk' K) chi) = 1 := by
    simp [Section1.degree, Section1.characterInflationByHom]
  simp [Section1.characterInflationByHom, hkq, hdeg]

private theorem characterInflationByHom_mk'_injective_pf44
    {L : Type*} [Group L] {K : Subgroup L} [K.Normal] :
    Function.Injective
      (fun chi : (L ⧸ K) →* ℂˣ =>
        Section1.characterInflationByHom (QuotientGroup.mk' K) chi) := by
  intro chi eta hEq
  ext q
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K q
  have hval := congrFun hEq g
  simpa [Section1.characterInflationByHom, hg]
    using hval

set_option backward.isDefEq.respectTransparency false in
private theorem characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf44
    {L : Type u} [Group L] [Finite L] {K : Subgroup L} [K.Normal]
    (chi : (L ⧸ K) →* ℂˣ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.characterInflationByHom (QuotientGroup.mk' K) chi) := by
  let lambda : L →* ℂˣ := chi.comp (QuotientGroup.mk' K)
  let rho0 : Representation ℂ L (Fin 1 → ℂ) := Representation.trivial ℂ L (Fin 1 → ℂ)
  have hρ0irr : Representation.IsIrreducible rho0 := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ L) (V := rho0.asModule) (by
        change Module.finrank ℂ (Fin 1 → ℂ) = 1
        simp)
  let rho : Representation ℂ L (Fin 1 → ℂ) :=
    Section1.representationTwistByCharacter lambda rho0
  have hρirr : Representation.IsIrreducible rho :=
    Section1.irreducible_twistByCharacter lambda rho0 hρ0irr
  have hρ0char : rho0.character = Section1.principalCharacter L := by
    ext g
    simp [rho0, Section1.principalCharacter, Representation.character, Representation.trivial]
  have hchar :
      Section1.characterInflationByHom (QuotientGroup.mk' K) chi = rho.character := by
    calc
      Section1.characterInflationByHom (QuotientGroup.mk' K) chi =
          (fun g : L => (lambda g : ℂ)) * Section1.principalCharacter L := by
            ext g
            simp [lambda, Section1.characterInflationByHom, Section1.principalCharacter]
      _ = (fun g : L => (lambda g : ℂ)) * rho0.character := by rw [hρ0char]
      _ = rho.character := by
            simpa [rho] using
              (Section1.representationTwistByCharacter_character lambda rho0).symm
  exact ⟨1, rho, hρirr, hchar⟩

private theorem complex_norm_eq_one_of_pow_eq_one_pf44
    {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    ‖z‖ = 1 := by
  have hpow : ‖z‖ ^ n = (1 : ℝ) := by
    simpa [hz] using (norm_pow z n).symm
  have habs_pow : |(‖z‖ : ℝ) ^ n| = 1 := by
    rw [hpow, abs_one]
  have habs : |(‖z‖ : ℝ)| = 1 :=
    (abs_pow_eq_one (‖z‖ : ℝ) hn).mp habs_pow
  simpa [abs_of_nonneg (norm_nonneg z)] using habs

private theorem complex_eq_one_of_pow_eq_one_of_one_le_re_pf44
    {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) (hre : 1 ≤ z.re) :
    z = 1 := by
  have hnorm : ‖z‖ = 1 := complex_norm_eq_one_of_pow_eq_one_pf44 hn hz
  have hre_le : z.re ≤ 1 := by
    simpa [hnorm] using Complex.re_le_norm z
  have hre_eq : z.re = 1 := le_antisymm hre_le hre
  have hnormSq : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hnorm] at h
    norm_num at h
    exact h
  have him_sq : z.im * z.im = 0 := by
    nlinarith
  have him : z.im = 0 := mul_self_eq_zero.mp him_sq
  exact Complex.ext (by simp [hre_eq]) (by simp [him])

private theorem eigenspace_finrank_pos_pf44
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (μ : f.Eigenvalues) :
    0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
  have hμ : f.HasEigenvalue (μ : ℂ) :=
    Module.End.hasEigenvalue_of_hasGenEigenvalue μ.property
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨v, ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    exact hv.apply_eq_smul
  · intro hzero
    have hvzero : v = 0 := by
      simpa using congrArg Subtype.val hzero
    exact hv.2 hvzero

private theorem finite_order_eq_one_of_trace_eq_finrank_pf44
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (htrace : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) :
    f = 1 := by
  classical
  let m : f.Eigenvalues → ℝ :=
    fun μ => (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℝ)
  have htrace_one :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) := by
    simpa [m] using
      (Section1.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
    have h0 :=
      Section1.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 0) hn hpow
    simpa [m, LinearMap.trace_id] using h0
  have hsum_complex :
      ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) =
        ∑ μ : f.Eigenvalues, (1 : ℂ) * (m μ : ℂ) := by
    rw [← htrace_one, htrace, htrace_zero]
    simp
  have hsum_real :
      ∑ μ : f.Eigenvalues, (μ : ℂ).re * m μ =
        ∑ μ : f.Eigenvalues, (1 : ℝ) * m μ := by
    have h := congrArg Complex.re hsum_complex
    simpa [Complex.re_sum, Complex.re_mul_ofReal] using h
  have hle :
      ∀ μ ∈ (Finset.univ : Finset f.Eigenvalues),
        (μ : ℂ).re * m μ ≤ (1 : ℝ) * m μ := by
    intro μ hμ
    have hμpow : (μ : ℂ) ^ n = 1 :=
      Section1.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 :=
      complex_norm_eq_one_of_pow_eq_one_pf44 hn hμpow
    have hre_le : (μ : ℂ).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (μ : ℂ)
    exact mul_le_mul_of_nonneg_right hre_le (by positivity : 0 ≤ m μ)
  have heq_each :
      ∀ μ : f.Eigenvalues, (μ : ℂ).re * m μ = (1 : ℝ) * m μ := by
    intro μ
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by simpa using hsum_real) μ
      (Finset.mem_univ μ)
  have heigen_eq_one : ∀ μ : f.Eigenvalues, (μ : ℂ) = 1 := by
    intro μ
    have hpos_nat : 0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) :=
      eigenspace_finrank_pos_pf44 μ
    have hpos : 0 < m μ := by
      dsimp [m]
      exact_mod_cast hpos_nat
    have hre_eq : (μ : ℂ).re = 1 := by
      have h := heq_each μ
      nlinarith
    have hμpow : (μ : ℂ) ^ n = 1 :=
      Section1.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    exact complex_eq_one_of_pow_eq_one_of_one_le_re_pf44 hn hμpow (by linarith)
  have htop :
      f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple := Section1.end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup := Section1.eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro μ
    simp [heigen_eq_one μ]
  ext v
  have hv : v ∈ f.eigenspace (1 : ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa using hv

private theorem subgroupInRepresentationKernel_of_subgroupInKernel'_character_pf44
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G)
    (hV : Section1.subgroupInKernel' ρ.character A) :
    Section1.subgroupInRepresentationKernel ρ A := by
  intro a
  have hn : orderOf (a : G) ≠ 0 := Nat.ne_of_gt (orderOf_pos (a : G))
  have hpow : (ρ (a : G)) ^ orderOf (a : G) = 1 := by
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have htrace : LinearMap.trace ℂ V (ρ (a : G)) = (Module.finrank ℂ V : ℂ) := by
    have hchar := hV a
    rw [Section1.degree] at hchar
    change ρ.character (a : G) = ρ.character (1 : G) at hchar
    simpa [Representation.character] using hchar
  exact finite_order_eq_one_of_trace_eq_finrank_pf44 (ρ (a : G)) hn hpow htrace

private theorem exists_ne_one_mem_of_natCard_ne_one_pf44
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : Nat.card H ≠ 1) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 := by
  have hH_ne_bot : H ≠ ⊥ := by
    intro hbot
    apply hH
    simp [hbot]
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hH_ne_bot with ⟨x, hx1⟩
  exact ⟨x, x.2, by simpa using hx1⟩

private theorem w2_le_K_of_hypothesis_4_2_pf44
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    W2 ≤ K := by
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hcard1, _hcyc2, _hcard2,
      hcent, _hW1, _hW2, _hW, _hodd⟩
  rcases exists_ne_one_mem_of_natCard_ne_one_pf44 W1 hcard1 with ⟨x, hxW1, hx1⟩
  have hcentx : Section2.centralizerIn K x = W2 := by
    exact hcent ⟨x, hxW1⟩ (by
      intro hxsub
      exact hx1 (Subtype.ext_iff.mp hxsub))
  intro z hz
  have hz' : z ∈ Section2.centralizerIn K x := by
    simpa [hcentx] using hz
  exact (Subgroup.mem_inf.mp hz').1

private theorem normal_K_of_hypothesis_4_2_pf44
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    K.Normal := by
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  refine ⟨?_⟩
  intro k hk x
  rcases hsemi.mul_surjective x (by trivial) with ⟨h, hh, w, hw, rfl⟩
  have hwk : Section2.conjBy w k ∈ K :=
    hsemi.right_normalizes_left w hw k hk
  show Section2.conjBy (h * w) k ∈ K
  simpa [Section2.conjBy, mul_assoc] using
    K.mul_mem (K.mul_mem hh hwk) (K.inv_mem hh)

private theorem natCard_quotient_K_eq_natCard_W1_pf44
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (hKnorm : K.Normal)
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    Nat.card (L ⧸ K) = Nat.card W1 := by
  letI : K.Normal := hKnorm
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  let q : W1 →* (L ⧸ K) := (QuotientGroup.mk' K).comp W1.subtype
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hk, w, hw, hkw⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    change QuotientGroup.mk' K w = QuotientGroup.mk' K g
    rw [hkw]
    have hk_one : QuotientGroup.mk' K k = 1 :=
      (QuotientGroup.eq_one_iff (N := K) (x := k)).2 hk
    calc
      QuotientGroup.mk' K w = 1 * QuotientGroup.mk' K w := by simp
      _ = QuotientGroup.mk' K k * QuotientGroup.mk' K w := by rw [hk_one]
      _ = QuotientGroup.mk' K (k * w) := by simp
  have hq_inj : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    have hxy_one : q (x * y⁻¹) = 1 := by
      calc
        q (x * y⁻¹) = q x * (q y)⁻¹ := by simp [q]
        _ = 1 := by simp [hxy]
    have hmemK : ((x : L) * (y : L)⁻¹) ∈ K := by
      exact (QuotientGroup.eq_one_iff (N := K) (x := ((x : L) * (y : L)⁻¹))).1
        (by simpa [q] using hxy_one)
    have hmemW1 : ((x : L) * (y : L)⁻¹) ∈ W1 :=
      W1.mul_mem x.2 (W1.inv_mem y.2)
    have hbot : ((x : L) * (y : L)⁻¹) ∈ (⊥ : Subgroup L) := by
      have hinf : ((x : L) * (y : L)⁻¹) ∈ K ⊓ W1 :=
        Subgroup.mem_inf.mpr ⟨hmemK, hmemW1⟩
      simpa [hsemi.inf_eq_bot] using hinf
    have hxy_inv : (x : L) * (y : L)⁻¹ = 1 := by
      simpa using hbot
    calc
      (x : L) = ((x : L) * (y : L)⁻¹) * y := by simp [mul_assoc]
      _ = y := by simp [hxy_inv]
  exact (Nat.card_congr (Equiv.ofBijective q ⟨hq_inj, hq_surj⟩)).symm

private theorem isCyclic_quotient_K_of_hypothesis_4_2_pf44
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (hKnorm : K.Normal)
    (h42 : hypothesis_4_2_statement K W1 W2 W) :
    IsCyclic (L ⧸ K) := by
  letI : K.Normal := hKnorm
  rcases h42 with ⟨hsemi, _hHall, hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  let q : W1 →* (L ⧸ K) := (QuotientGroup.mk' K).comp W1.subtype
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hk, w, hw, hkw⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    change QuotientGroup.mk' K w = QuotientGroup.mk' K g
    rw [hkw]
    have hk_one : QuotientGroup.mk' K k = 1 :=
      (QuotientGroup.eq_one_iff (N := K) k).2 hk
    calc
      QuotientGroup.mk' K w = 1 * QuotientGroup.mk' K w := by simp
      _ = QuotientGroup.mk' K k * QuotientGroup.mk' K w := by rw [hk_one]
      _ = QuotientGroup.mk' K (k * w) := by simp
  letI : IsCyclic W1 := hcyc1
  exact isCyclic_of_surjective q hq_surj

private theorem isCyclic_quotient_ker_of_hypothesis_4_2_pf44
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ L V)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hKleKer : K ≤ ρ.ker) :
    IsCyclic (L ⧸ ρ.ker) := by
  letI : K.Normal := normal_K_of_hypothesis_4_2_pf44 h42
  let q : (L ⧸ K) →* (L ⧸ ρ.ker) :=
    QuotientGroup.lift K (QuotientGroup.mk' ρ.ker) (by
      intro k hk
      exact (QuotientGroup.eq_one_iff (N := ρ.ker) k).2 (hKleKer hk))
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker x
    exact ⟨QuotientGroup.mk' K g, rfl⟩
  letI : IsCyclic (L ⧸ K) :=
    isCyclic_quotient_K_of_hypothesis_4_2_pf44
      (normal_K_of_hypothesis_4_2_pf44 h42) h42
  exact isCyclic_of_surjective q hq_surj

private theorem irreducible_eq_principal_of_both_kernels_pf44
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    {ψ : Section1.ClassFunction W}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hker1 : Section1.subgroupInKernel' ψ (W1.subgroupOf W))
    (hker2 : Section1.subgroupInKernel' ψ (W2.subgroupOf W))
    (hdeg : Section1.degree ψ = 1) :
    ψ = Section1.principalCharacter W := by
  rcases h31 with ⟨_hW1, _hW2, hDirect, _hcycW, _hodd, _hcard1, _hcard2, _hTI⟩
  rcases hψ with ⟨n, ρ, hρirr, hchar⟩
  have hkerRep1 :
      Section1.subgroupInRepresentationKernel ρ (W1.subgroupOf W) :=
    subgroupInRepresentationKernel_of_subgroupInKernel'_character_pf44
      ρ (W1.subgroupOf W) (subgroupInKernel'_of_eq_pf44 hchar hker1)
  have hkerRep2 :
      Section1.subgroupInRepresentationKernel ρ (W2.subgroupOf W) :=
    subgroupInRepresentationKernel_of_subgroupInKernel'_character_pf44
      ρ (W2.subgroupOf W) (subgroupInKernel'_of_eq_pf44 hchar hker2)
  ext x
  rcases hDirect.mul_surjective (x : L) x.2 with ⟨a, ha, b, hb, hmul⟩
  let aW : W := ⟨a, hDirect.left_le ha⟩
  let bW : W := ⟨b, hDirect.right_le hb⟩
  have hxmul : x = aW * bW := by
    apply Subtype.ext
    simpa [aW, bW] using hmul
  have hρa : ρ aW = 1 := hkerRep1 ⟨aW, ha⟩
  have hρb : ρ bW = 1 := hkerRep2 ⟨bW, hb⟩
  have hρx : ρ x = 1 := by
    rw [hxmul, map_mul, hρa, hρb]
    simp
  have hpsi_one : ψ 1 = 1 := by
    simpa [Section1.degree] using hdeg
  have hpsi_x : ψ x = 1 := by
    calc
      ψ x = ρ.character x := by rw [hchar]
      _ = ρ.character 1 := by simp [Representation.character, hρx]
      _ = ψ 1 := by rw [hchar]
      _ = 1 := hpsi_one
  simpa [Section1.principalCharacter] using hpsi_x

private theorem omega_column_eq_base_of_right_kernel_pf44
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J}
    (hker : Section1.subgroupInKernel' (ω i j) (W2.subgroupOf W)) :
    j = j0 := by
  have hkerBase : Section1.subgroupInKernel' (ω i0 j) (W2.subgroupOf W) := by
    intro x
    have hij : ω i j x = 1 := by
      simpa [hω.degree_one i j] using hker x
    have hij0 : ω i j0 x = 1 := by
      simpa [hω.degree_one i j0] using hω.left_kernel i x
    have hprod := hω.product i j x
    rw [hij, hij0] at hprod
    have hbase : ω i0 j x = 1 := by
      simpa using hprod.symm
    simpa [hω.degree_one i0 j] using hbase
  have hprincipal : ω i0 j = Section1.principalCharacter W :=
    irreducible_eq_principal_of_both_kernels_pf44
      (W1 := W1) (W2 := W2) (W := W) h31
      (hω.irreducible i0 j) (hω.right_kernel j) hkerBase (hω.degree_one i0 j)
  have heq : ω i0 j = ω i0 j0 := by
    rw [hprincipal, hω.principal]
  exact (hω.pairwise_eq (i := i0) (i' := i0) (j := j) (j' := j0) heq).2

set_option backward.isDefEq.respectTransparency false in
private theorem subgroupRestriction_isIrreducibleCharacterOnGroup_of_kernel_containing_K_pf44
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hkerK : Section1.subgroupInKernel' χ K) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.subgroupRestriction W χ) := by
  rcases hχ with ⟨n, ρ, hρirr, rfl⟩
  have hkerRep : Section1.subgroupInRepresentationKernel ρ K :=
    subgroupInRepresentationKernel_of_subgroupInKernel'_character_pf44 ρ K hkerK
  have hKleKer : K ≤ ρ.ker := by
    intro k hk
    exact hkerRep ⟨k, hk⟩
  have hcycKer : IsCyclic (L ⧸ ρ.ker) :=
    isCyclic_quotient_ker_of_hypothesis_4_2_pf44
      (K := K) (W1 := W1) (W2 := W2) (W := W) ρ h42 hKleKer
  letI : CommGroup (L ⧸ MonoidHom.ker ρ) := by
    simpa using hcycKer.commGroup
  letI : Std.Commutative (α := L ⧸ MonoidHom.ker ρ) (· * ·) := ⟨mul_comm⟩
  letI : IsMulCommutative (L ⧸ MonoidHom.ker ρ) := ⟨inferInstance⟩
  letI : Representation.IsIrreducible (Theory.Representation.kerRepresentation ρ) :=
    (Theory.Representation.kerRepresentation_irreducible_iff (ρ := ρ)).2 hρirr
  have hdim1 : n = 1 := by
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (ρ := Theory.Representation.kerRepresentation ρ))
  subst hdim1
  let ρW : Representation ℂ W (Fin 1 → ℂ) := ρ.comp W.subtype
  have hρWirr : Representation.IsIrreducible ρW := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ W) (V := ρW.asModule) (by
        change Module.finrank ℂ (Fin 1 → ℂ) = 1
        simp)
  refine ⟨1, ρW, hρWirr, ?_⟩
  ext x
  rfl

private theorem subgroupRestriction_kernel_W2_of_kernel_containing_K_pf44
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    {χ : Section1.ClassFunction L}
    (hkerK : Section1.subgroupInKernel' χ K) :
    Section1.subgroupInKernel' (Section1.subgroupRestriction W χ) (W2.subgroupOf W) := by
  have hW2leK : W2 ≤ K := w2_le_K_of_hypothesis_4_2_pf44 h42
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, hW2, _hW, _hodd⟩
  have hW2ker : Section1.subgroupInKernel' χ W2 := by
    intro x
    exact hkerK ⟨x, hW2leK x.2⟩
  exact (subgroupInKernel'_subgroupRestriction_iff_pf44 W W2 hW2 χ).mpr hW2ker

private theorem proposition_4_4_forward_restriction_to_W
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hkerK : Section1.subgroupInKernel' χ K) :
    ∃ i, Section1.subgroupRestriction W χ = ω i j0 := by
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (theorem_4_3_a K W1 W2 W h42).2
  have hresIrr :
      Section1.IsIrreducibleCharacterOnGroup (Section1.subgroupRestriction W χ) :=
    subgroupRestriction_isIrreducibleCharacterOnGroup_of_kernel_containing_K_pf44
      K W1 W2 W h42 hχ hkerK
  have hresKer :
      Section1.subgroupInKernel' (Section1.subgroupRestriction W χ) (W2.subgroupOf W) :=
    subgroupRestriction_kernel_W2_of_kernel_containing_K_pf44
      K W1 W2 W h42 hkerK
  rcases hω.all_irreducibles (Section1.subgroupRestriction W χ) hresIrr with
    ⟨i, j, hres⟩
  have hj : j = j0 :=
    omega_column_eq_base_of_right_kernel_pf44
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      h31 hω (subgroupInKernel'_of_eq_pf44 hres hresKer)
  refine ⟨i, ?_⟩
  simpa [hj] using hres

private theorem proposition_4_4_forward_uniqueness
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hkerK : Section1.subgroupInKernel' χ K) :
    ∃ i, χ = piChar i j0 := by
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    (theorem_4_3_a K W1 W2 W h42).2
  rcases hB with ⟨hσmap, hsign, hirr, _hdistinct, _hind, hSigma⟩
  rcases proposition_4_4_forward_restriction_to_W
      K W1 W2 W I J i0 j0 ω h42 hω hχ hkerK with ⟨i, hres⟩
  rcases Section3.proposition_3_9_a_uniqueness
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h31 hω with
    ⟨χpf, horth, _hvirt, hsigned, h00, hInd, huniq⟩
  have hchiV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        χ x = ω i j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hresx := congrFun hres ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    simpa [Section1.subgroupRestriction] using hresx
  have hchiEq :
      χ = Section3.sigmaOfPF35 ω χpf (ω i j0) := by
    exact huniq (hω.irreducible i j0)
      (signed_irreducible_of_irreducible_pf44 hχ) hchiV
  have hpiV :
      ∀ x : L, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        (deltaSign j0 • piChar i j0) x =
          ω i j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    have hxWm : x ∈ ((W : Set L) \ (W2 : Set L)) := by
      exact ⟨Section3.cyclicTISet_subset W1 W2 W hx,
        Section3.cyclicTISet_not_mem_right W1 W2 W hx⟩
    have hval := hC.1 i j0 x hxWm
    change deltaSign j0 * piChar i j0 x =
      ω i j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
    calc
      deltaSign j0 * piChar i j0 x =
          deltaSign j0 *
            (deltaSign j0 * ω i j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
              rw [hval]
      _ =
          (deltaSign j0 * deltaSign j0) *
            ω i j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by ring
      _ = ω i j0 ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
        rw [sign_mul_self_eq_one_pf44 (hsign j0)]
        simp
  have hpiEq :
      deltaSign j0 • piChar i j0 = Section3.sigmaOfPF35 ω χpf (ω i j0) := by
    exact huniq (hω.irreducible i j0)
      ⟨deltaSign j0, hsign j0, piChar i j0, hirr i j0, rfl⟩ hpiV
  have hdelta : deltaSign j0 = 1 := by
    rcases hσmap with ⟨_hIso, _hMaps, _hCFOn, _hClass, hσprincipal, _hAgree, _hDetect⟩
    have hbase :
        Section1.principalCharacter L = deltaSign j0 • piChar i0 j0 := by
      calc
        Section1.principalCharacter L = σ (Section1.principalCharacter W) := by
          symm
          exact hσprincipal
        _ = σ (ω i0 j0) := by rw [hω.principal]
        _ = deltaSign j0 • piChar i0 j0 := hSigma i0 j0
    rcases hirr i0 j0 with ⟨n, ρ, _hρ, hchar⟩
    have hdeg :
        Section1.degree (piChar i0 j0) = (n : ℂ) := by
      rw [hchar]
      simpa using Section1.degree_representation_character ρ
    have hbaseDeg : (1 : ℂ) = deltaSign j0 * (n : ℂ) := by
      have hdegEq := congrArg Section1.degree hbase
      simpa [Section1.degree, hdeg, hchar] using hdegEq
    rcases hsign j0 with hδ | hδ
    · exact hδ
    · have hreal := congrArg Complex.re hbaseDeg
      simp [hδ] at hreal
      have hnonneg : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      exfalso
      nlinarith
  refine ⟨i, ?_⟩
  calc
    χ = Section3.sigmaOfPF35 ω χpf (ω i j0) := hchiEq
    _ = deltaSign j0 • piChar i j0 := hpiEq.symm
    _ = piChar i j0 := by simp [hdelta]

private theorem proposition_4_4_reverse_exhaustion
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    ∀ i, Section1.subgroupInKernel' (piChar i j0) K := by
  classical
  letI : K.Normal := normal_K_of_hypothesis_4_2_pf44 h42
  let Q := L ⧸ K
  have hQcyc : IsCyclic Q := by
    simpa [Q] using
      isCyclic_quotient_K_of_hypothesis_4_2_pf44
        (K := K) (W1 := W1) (W2 := W2) (W := W) inferInstance h42
  letI : CommGroup Q := by
    simpa [Q] using hQcyc.commGroup
  have hExpNeZero : NeZero (Monoid.exponent (L ⧸ K)) :=
    Monoid.neZero_exponent_of_finite (G := L ⧸ K)
  have hRoots : HasEnoughRootsOfUnity ℂ (Monoid.exponent (L ⧸ K)) := by
    letI : NeZero (Monoid.exponent (L ⧸ K)) := hExpNeZero
    exact Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent (L ⧸ K))
  have hcard_quot : Nat.card ((L ⧸ K) →* ℂˣ) = Nat.card (L ⧸ K) := by
    letI : CommGroup (L ⧸ K) := by
      simpa using hQcyc.commGroup
    letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (L ⧸ K)) := hRoots
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (L ⧸ K) ℂ
  let inflated : (Q →* ℂˣ) → Section1.ClassFunction L :=
    fun chi => Section1.characterInflationByHom (QuotientGroup.mk' K) chi
  let f : (Q →* ℂˣ) → I := fun chi =>
    Classical.choose <|
      proposition_4_4_forward_uniqueness
        K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC
        (χ := inflated chi)
        (characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf44
          (K := K) chi)
        (subgroupInKernel'_characterInflationByHom_mk'_pf44 (K := K) chi)
  have hf_spec :
      ∀ chi : Q →* ℂˣ, inflated chi = piChar (f chi) j0 := by
    intro chi
    exact Classical.choose_spec <|
      proposition_4_4_forward_uniqueness
        K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC
        (χ := inflated chi)
        (characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf44
          (K := K) chi)
        (subgroupInKernel'_characterInflationByHom_mk'_pf44 (K := K) chi)
  have hf_inj : Function.Injective f := by
    intro chi eta hfeq
    apply characterInflationByHom_mk'_injective_pf44 (K := K)
    calc
      inflated chi = piChar (f chi) j0 := hf_spec chi
      _ = piChar (f eta) j0 := by rw [hfeq]
      _ = inflated eta := (hf_spec eta).symm
  letI : Finite (Q →* ℂˣ) := Finite.of_injective f hf_inj
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
  have hcard_chars_nat : Nat.card (Q →* ℂˣ) = Nat.card I := by
    calc
      Nat.card (Q →* ℂˣ) = Nat.card Q := by
        simpa [Q] using hcard_quot
      _ = Nat.card W1 := by
        simpa [Q] using
          natCard_quotient_K_eq_natCard_W1_pf44
            (K := K) (W1 := W1) (W2 := W2) (W := W) inferInstance h42
      _ = Fintype.card I := hω.card_left.symm
      _ = Nat.card I := by
        simp
  have hcard_chars : Fintype.card (Q →* ℂˣ) = Fintype.card I := by
    rw [← Nat.card_eq_fintype_card (α := Q →* ℂˣ),
      ← Nat.card_eq_fintype_card (α := I)]
    exact hcard_chars_nat
  have hbij : Function.Bijective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard_chars⟩
  intro i
  obtain ⟨chi, hchi⟩ := hbij.surjective i
  have hEq : inflated chi = piChar i j0 := by
    simpa [f, hchi] using hf_spec chi
  exact subgroupInKernel'_of_eq_pf44 hEq
    (subgroupInKernel'_characterInflationByHom_mk'_pf44 (K := K) chi)

/-- PF `(4.4)`: every base-column character has degree one. -/
public theorem proposition_4_4_baseColumn_degree_one
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    ∀ i, Section1.degree (piChar i j0) = 1 := by
  classical
  letI : K.Normal := normal_K_of_hypothesis_4_2_pf44 h42
  let Q := L ⧸ K
  have hQcyc : IsCyclic Q := by
    simpa [Q] using
      isCyclic_quotient_K_of_hypothesis_4_2_pf44
        (K := K) (W1 := W1) (W2 := W2) (W := W) inferInstance h42
  letI : CommGroup Q := by
    simpa [Q] using hQcyc.commGroup
  have hExpNeZero : NeZero (Monoid.exponent (L ⧸ K)) :=
    Monoid.neZero_exponent_of_finite (G := L ⧸ K)
  have hRoots : HasEnoughRootsOfUnity ℂ (Monoid.exponent (L ⧸ K)) := by
    letI : NeZero (Monoid.exponent (L ⧸ K)) := hExpNeZero
    exact Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent (L ⧸ K))
  have hcard_quot : Nat.card ((L ⧸ K) →* ℂˣ) = Nat.card (L ⧸ K) := by
    letI : CommGroup (L ⧸ K) := by
      simpa using hQcyc.commGroup
    letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (L ⧸ K)) := hRoots
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (L ⧸ K) ℂ
  let inflated : (Q →* ℂˣ) → Section1.ClassFunction L :=
    fun chi => Section1.characterInflationByHom (QuotientGroup.mk' K) chi
  let f : (Q →* ℂˣ) → I := fun chi =>
    Classical.choose <|
      proposition_4_4_forward_uniqueness
        K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC
        (χ := inflated chi)
        (characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf44
          (K := K) chi)
        (subgroupInKernel'_characterInflationByHom_mk'_pf44 (K := K) chi)
  have hf_spec :
      ∀ chi : Q →* ℂˣ, inflated chi = piChar (f chi) j0 := by
    intro chi
    exact Classical.choose_spec <|
      proposition_4_4_forward_uniqueness
        K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC
        (χ := inflated chi)
        (characterInflationByHom_mk'_isIrreducibleCharacterOnGroup_pf44
          (K := K) chi)
        (subgroupInKernel'_characterInflationByHom_mk'_pf44 (K := K) chi)
  have hf_inj : Function.Injective f := by
    intro chi eta hfeq
    apply characterInflationByHom_mk'_injective_pf44 (K := K)
    calc
      inflated chi = piChar (f chi) j0 := hf_spec chi
      _ = piChar (f eta) j0 := by rw [hfeq]
      _ = inflated eta := (hf_spec eta).symm
  letI : Finite (Q →* ℂˣ) := Finite.of_injective f hf_inj
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
  have hcard_chars_nat : Nat.card (Q →* ℂˣ) = Nat.card I := by
    calc
      Nat.card (Q →* ℂˣ) = Nat.card Q := by
        simpa [Q] using hcard_quot
      _ = Nat.card W1 := by
        simpa [Q] using
          natCard_quotient_K_eq_natCard_W1_pf44
            (K := K) (W1 := W1) (W2 := W2) (W := W) inferInstance h42
      _ = Fintype.card I := hω.card_left.symm
      _ = Nat.card I := by
        simp
  have hcard_chars : Fintype.card (Q →* ℂˣ) = Fintype.card I := by
    rw [← Nat.card_eq_fintype_card (α := Q →* ℂˣ),
      ← Nat.card_eq_fintype_card (α := I)]
    exact hcard_chars_nat
  have hbij : Function.Bijective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard_chars⟩
  intro i
  obtain ⟨chi, hchi⟩ := hbij.surjective i
  have hEq : inflated chi = piChar i j0 := by
    simpa [f, hchi] using hf_spec chi
  rw [← hEq]
  simp [inflated, Section1.degree, Section1.characterInflationByHom]

/--
PF `(4.4)`, final sentence: in the notation of Theorem `(4.3)`, the base sign
is `1` and the base character is the principal character of `L`.
-/
public theorem proposition_4_4_base
    {L : Type u} [Group L] [Finite L]
    (W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω) :
    deltaSign j0 = 1 ∧
      piChar i0 j0 = Section1.principalCharacter L := by
  rcases hB with ⟨hσmap, hsign, hirr, _hdistinct, _hind, hSigma⟩
  rcases hσmap with ⟨_hIso, _hMaps, _hCFOn, _hClass, hσprincipal, _hAgree, _hDetect⟩
  have hbase :
      Section1.principalCharacter L = deltaSign j0 • piChar i0 j0 := by
    calc
      Section1.principalCharacter L = σ (Section1.principalCharacter W) := by
        symm
        exact hσprincipal
      _ = σ (ω i0 j0) := by rw [hω.principal]
      _ = deltaSign j0 • piChar i0 j0 := hSigma i0 j0
  rcases hirr i0 j0 with ⟨n, ρ, _hρ, hchar⟩
  have hdeg :
      Section1.degree (piChar i0 j0) = (n : ℂ) := by
    rw [hchar]
    simpa using Section1.degree_representation_character ρ
  have hbaseDeg : (1 : ℂ) = deltaSign j0 * (n : ℂ) := by
    have hdegEq := congrArg Section1.degree hbase
    simpa [Section1.degree, hdeg, hchar] using hdegEq
  rcases hsign j0 with hδ | hδ
  · refine ⟨hδ, ?_⟩
    simpa [hδ] using hbase.symm
  · have hreal := congrArg Complex.re hbaseDeg
    simp [hδ] at hreal
    exfalso
    have hnonneg : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    nlinarith

/--
PF `(4.4)`: in the notation of Theorem `(4.3)`, the base-column characters
`Πᵢ₀` are exactly the irreducible characters of `L` whose kernels contain `K`.
Moreover, `δ₀ = 1` and `Π₀₀ = 1_L`.
-/
public theorem proposition_4_4
    {L : Type u} [Group L] [Finite L]
    (K W1 W2 W : Subgroup L)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (piChar : I → J → Section1.ClassFunction L)
    (deltaSign : J → ℂ)
    (h42 : hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hB : theorem_4_3_b_statement W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (hC : theorem_4_3_c_statement W2 W I J piChar deltaSign ω) :
    proposition_4_4_statement
      K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC := by
  refine ⟨?_, proposition_4_4_base W1 W2 W I J i0 j0 ω σ piChar deltaSign hω hB⟩
  intro χ hχ
  constructor
  · intro hkerK
    rcases proposition_4_4_forward_uniqueness
        K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC hχ hkerK with
      ⟨i, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact proposition_4_4_reverse_exhaustion
      K W1 W2 W I J i0 j0 ω σ piChar deltaSign h42 hω hB hC i

end CFSG.Section4
