module

public import CFSG.Quasithin.Vol2.E2SevenKG2L2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineOrbit
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

section Subline

variable {E : Type} [Field E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] noncomputable def sublinePSU :
    SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) →*
      ProjectiveSpecialUnitaryMatrixGroup J :=
  ((ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).comp (sublineHom J hJ)).codRestrict _
    fun m => Subgroup.mem_map_of_mem _ (sublineHom J hJ m).2

theorem coe_sublinePSU (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) :
    ((sublinePSU J hJ m : ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) E) =
      ProjGenLinGroup.mk ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) E) :=
  rfl

theorem sublinePSU_injective : Function.Injective (sublinePSU J hJ) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have h1 : ProjGenLinGroup.mk ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) E) = 1 :=
    congrArg Subtype.val hm
  obtain ⟨c, hc, -, -⟩ := (special_mk_eq_one_iff J hJ (sublineHom J hJ m).2).mp h1
  rw [coe_sublineHom] at hc
  have e11 := congrFun (congrFun hc 1) 1
  simp [scalar_apply] at e11
  have hone : sublineHom J hJ m = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_sublineHom, hc, ← e11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact sublineHom_injective hJ (hone.trans (map_one _).symm)

theorem mem_range_sublinePSU_of_upper {g : ProjectiveSpecialUnitaryMatrixGroup J} {b : E}
    (hb : b + J.conj b = 0) {M : GL (Fin 3) E}
    (hM : (M : Matrix (Fin 3) (Fin 3) E) = !![1, 0, b; 0, 1, 0; 0, 0, 1])
    (hg : (g : ProjGenLinGroup (Fin 3) E) = ProjGenLinGroup.mk M) :
    g ∈ (sublinePSU J hJ).range := by
  have hbk : J.conj b = b := by
    rw [eq_neg_of_add_eq_zero_right hb, CharTwo.neg_eq]
  refine ⟨upperSL _ (Multiplicative.ofAdd ⟨b, hbk⟩), Subtype.ext ?_⟩
  rw [coe_sublinePSU, hg]
  congr 1
  apply Units.ext
  rw [coe_sublineHom_upperSL, hM]
  rfl

theorem hermitianWeylPSU_mem_range_sublinePSU :
    hermitianWeylPSU J hJ ∈ (sublinePSU J hJ).range := by
  have h2 : (2 : unitaryCoverFixedField J) = 0 := Subtype.ext (by
    change (2 : E) = 0
    exact CharTwo.two_eq_zero)
  have hneg : (-1 : unitaryCoverFixedField J) = 1 := by
    have h11 : (1 : unitaryCoverFixedField J) + 1 = 0 := by rw [one_add_one_eq_two, h2]
    exact (eq_neg_of_add_eq_zero_left h11).symm
  have hdet : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (unitaryCoverFixedField J)).det = 1 := by
    rw [det_fin_two_of]
    simpa using hneg
  let m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) := ⟨!![0, 1; 1, 0], hdet⟩
  refine ⟨m, Subtype.ext ?_⟩
  rw [coe_sublinePSU, hermitianWeylPSU_val]
  congr 1
  apply Units.ext
  rw [coe_sublineHom]
  have hE : (-1 : E) = 1 := CharTwo.neg_eq 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m, hermitianWeylGL, hermitianWeylMatrix, hE]

variable [Finite E]

theorem exists_conj_le_range_sublinePSU {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    {A B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hA : ∀ a ∈ A, a ^ 2 = 1) (hB : ∀ b ∈ B, b ^ 2 = 1) (hAB : ¬ IsPGroup 2 ↥(A ⊔ B)) :
    ∃ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (A ⊔ B).map (MulAut.conj x).toMonoidHom ≤ (sublinePSU J hJ).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨-, -, -, -, -, rho, -, hnative, -, h2tr, hstabα, -, -, -, hUTB, -, -, -, ⟨S₀, hS₀⟩, -,
    -, -, -, hinvB, hinvU, -, -⟩ := unitary_three_point_structure J f hf hcard hfixed hJ
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide) with hαdef
  set β := unitaryOuterIsotropicPoint J hJ 2 (by decide) with hβdef
  set U := (hermitianUnipotentPSU J hJ).range with hUdef
  set Bα := unitaryCoordinateStabilizer J 0 with hBα
  set σ := sublinePSU J hJ with hσ
  have hUB : U ≤ Bα := hUTB ▸ le_sup_left
  have hinv : ∀ (f : Equiv.Perm (unitaryIsotropicPoints J)) (p : unitaryIsotropicPoints J),
      f⁻¹ (f p) = p := fun f p => by rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hmemB : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, g ∈ Bα ↔ rho g α = α := fun g => by
    rw [← hstabα, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  have hupper : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, rho g α = α → g ^ 2 = 1 →
      g ∈ σ.range := by
    intro g hgα hg2
    by_cases hg1 : g = 1
    · rw [hg1]
      exact Subgroup.one_mem _
    obtain ⟨b, M, hb, -, hM, hgM⟩ := (hinvB g).mp ⟨(hmemB g).mpr hgα, orderOf_eq_prime hg2 hg1⟩
    exact mem_range_sublinePSU_of_upper J hJ hb hM hgM
  set w := hermitianWeylPSU J hJ with hwdef
  have hwα : rho w α = β := Subtype.ext ((hnative _ _).trans (hermitianWeylPSU_smul_zero J hJ))
  have hwβ : rho w β = α := Subtype.ext ((hnative _ _).trans (hermitianWeylPSU_smul_two J hJ))
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hermitianWeylPSU_mul_self J hJ)
  have hwσ : w ∈ σ.range := hermitianWeylPSU_mem_range_sublinePSU J hJ
  have hlower : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, rho g β = β → g ^ 2 = 1 →
      g ∈ σ.range := by
    intro g hgβ hg2
    have h1 : w * g * w⁻¹ ∈ σ.range := by
      apply hupper
      · rw [hwinv, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hwα, hgβ, hwβ]
      · rw [conj_pow, hg2, mul_one, mul_inv_cancel]
    have h2 : g = w⁻¹ * (w * g * w⁻¹) * w := by simp [mul_assoc]
    rw [h2]
    exact σ.range.mul_mem (σ.range.mul_mem (σ.range.inv_mem hwσ) h1) hwσ
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA x x.2)⟩
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hB x x.2)⟩
  obtain ⟨PA, hPA⟩ := hA2.exists_le_sylow
  obtain ⟨PB, hPB⟩ := hB2.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S₀ PA
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S₀ PB
  have hconjU : ∀ (c : ProjectiveSpecialUnitaryMatrixGroup J)
      (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)), c • S₀ = Q →
      ∀ a ∈ (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      ∃ u ∈ U, a = c * u * c⁻¹ := by
    intro c Q hc a ha
    rw [← hc, Sylow.coe_subgroup_smul, hS₀] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
  have hfix : ∀ (c : ProjectiveSpecialUnitaryMatrixGroup J), ∀ u ∈ U,
      rho (c * u * c⁻¹) (rho c α) = rho c α := by
    intro c u hu
    have huα : rho u α = α := (hmemB u).mp (hUB hu)
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply, hinv, huα]
  have hfixA : ∀ a ∈ A, rho a (rho y α) = rho y α := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := hconjU y PA hy a (hPA ha)
    exact hfix y u hu
  have hfixB : ∀ b ∈ B, rho b (rho z α) = rho z α := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := hconjU z PB hz b (hPB hb)
    exact hfix z u hu
  have hU2 : IsPGroup 2 U := hS₀ ▸ S₀.isPGroup'
  by_cases hpp : rho y α = rho z α
  · exfalso
    apply hAB
    have hle : (A ⊔ B).map (MulAut.conj y⁻¹).toMonoidHom ≤ U := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        obtain ⟨u, hu, rfl⟩ := hconjU y PA hy a (hPA ha)
        simpa [MulAut.conj_apply, mul_assoc] using hu
      · rintro _ ⟨b, hb, rfl⟩
        have hfixb : rho (y⁻¹ * b * y) α = α := by
          simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
          rw [hpp, hfixB b hb, ← hpp, hinv]
        have hsq : (y⁻¹ * b * y) ^ 2 = 1 := by
          have h := conj_pow (a := y⁻¹) (b := b) (i := 2)
          rw [inv_inv] at h
          rw [h, hB b hb, mul_one, inv_mul_cancel]
        change y⁻¹ * b * y⁻¹⁻¹ ∈ U
        rw [inv_inv]
        by_cases h1 : y⁻¹ * b * y = 1
        · rw [h1]
          exact U.one_mem
        · exact (hinvU _ ((hmemB _).mpr hfixb) (orderOf_eq_prime hsq h1)).1
    exact (hU2.to_le hle).of_equiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj y⁻¹).injective).symm
  have hαβ : α ≠ β := fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h).symm
  obtain ⟨x, hxα, hxβ⟩ := h2tr _ _ α β hpp hαβ
  refine ⟨x, ?_⟩
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    change x * a * x⁻¹ ∈ σ.range
    apply hupper
    · have hx' : rho x⁻¹ α = rho y α :=
        calc rho x⁻¹ α = rho x⁻¹ (rho x (rho y α)) := by rw [hxα]
          _ = rho y α := by rw [map_inv, hinv]
      simp only [map_mul, Equiv.Perm.mul_apply]
      rw [hx', hfixA a ha, hxα]
    · rw [conj_pow, hA a ha, mul_one, mul_inv_cancel]
  · rintro _ ⟨b, hb, rfl⟩
    change x * b * x⁻¹ ∈ σ.range
    apply hlower
    · have hx' : rho x⁻¹ β = rho z α :=
        calc rho x⁻¹ β = rho x⁻¹ (rho x (rho z α)) := by rw [hxβ]
          _ = rho z α := by rw [map_inv, hinv]
      simp only [map_mul, Equiv.Perm.mul_apply]
      rw [hx', hfixB b hb, hxβ]
    · rw [conj_pow, hB b hb, mul_one, mul_inv_cancel]

end Subline

variable {G : Type} [Group G] [Finite G]

theorem not_isPGroup_sup_conjSub {K S V : Subgroup G} {q k : ℕ} (hB : fusionBenderBorel ↥K q k)
    (hS : IsSylowTwoOf S K) (hVS : V ≤ S) (hV1 : V ≠ ⊥) {g : G} (hgK : g ∈ K)
    (hgN : g ∉ Subgroup.normalizer (S : Set G)) : ¬ IsPGroup 2 ↥(V ⊔ conjSub g V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK : V ≤ K := hVS.trans hS.1
  have hWK : conjSub g V ≤ K := by
    intro x hx
    rw [mem_conjSub] at hx
    have := K.mul_mem (K.mul_mem hgK (hVK hx)) (K.inv_mem hgK)
    simpa [mul_assoc] using this
  intro hI2
  obtain ⟨S', hS', hIS'⟩ := exists_isSylowTwoOf_ge hI2 (sup_le hVK hWK)
  have h1 : S = S' := eq_of_isSylowTwoOf_of_inf_ne_bot hB hS hS'
    fun h0 => hV1 (le_bot_iff.mp (h0 ▸ le_inf hVS (le_sup_left.trans hIS')))
  have hSg : IsSylowTwoOf (conjSub g S) K := by
    have := isSylowTwoOf_conjSub hS g
    rwa [conjSub_eq_self (Subgroup.le_normalizer hgK)] at this
  have hVg1 : conjSub g V ≠ ⊥ := fun h0 => hV1 (by
    rw [eq_bot_iff] at h0 ⊢
    intro x hx
    have := h0 (show g * x * g⁻¹ ∈ conjSub g V by rw [mem_conjSub]; simpa [mul_assoc] using hx)
    rw [Subgroup.mem_bot] at this ⊢
    have := congrArg (fun w => g⁻¹ * w * g) this
    simpa [mul_assoc] using this)
  have hSS : S = conjSub g S := eq_of_isSylowTwoOf_of_inf_ne_bot hB hS hSg fun h0 => hVg1
    (le_bot_iff.mp (h0 ▸ le_inf (le_sup_right.trans (hIS'.trans h1.symm.le))
      ((conjSub g).monotone hVS)))
  apply hgN
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have : g * z * g⁻¹ ∈ conjSub g S := by rw [mem_conjSub]; simpa [mul_assoc] using hz
    rwa [← hSS] at this
  · intro hz
    rw [hSS, mem_conjSub] at hz
    simpa [mul_assoc] using hz

theorem nonempty_mulEquiv_psu_binary {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSU 3 2 n X) :
    Nonempty (X ≃*
      ProjectiveSpecialUnitaryMatrixGroup (binaryQuadraticHermitian n (by omega))) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hX
  have hcard : Nat.card F = 2 ^ (2 * n) := by rw [hF, ← pow_mul, mul_comm]
  let e₁ : X ≃* GLAProj (GLASUGroup (Fin 3) F (2 ^ n)) := e
  let e₂ : X ≃* PSU3 2 n := e₁.trans (glaSU3EquivNative n hn hcard)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 //
      (binaryQuadraticHermitian n (by omega)).conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  let e₃ := (projectiveSpecialUnitary_equiv_PSU3Model (binaryQuadraticHermitian n (by omega)) n hn
    rfl hEcard hfixed).some
  have hmodel : PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  exact ⟨e₂.trans (e₃.trans (MulEquiv.subgroupCongr hmodel)).symm⟩

theorem kgBenderSubU3_holds : KGBenderSubU3 := by
  intro G _ _ K S V n g hn hK hS hVS hVC hV hV4 hgK hgN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₀, hB⟩ :=
    exists_fusionBenderBorel_of_isBenderOf (⟨hn, Or.inr (Or.inr hK)⟩ : IsBenderOf n ↥K)
  obtain ⟨e⟩ := nonempty_mulEquiv_psu_binary hn hK
  set E := FiniteField.Extension (GaloisField 2 n) 2 2 with hEdef
  have : CharP E 2 := CharP.of_ringHom_of_ne_zero (algebraMap (GaloisField 2 n) E) 2
    (by norm_num)
  set J := binaryQuadraticHermitian n (by omega) with hJdef
  have hEcard : Nat.card E = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hVK : V ≤ K := hVS.trans hS.1
  have hWK : conjSub g V ≤ K := by
    intro x hx
    rw [mem_conjSub] at hx
    have := K.mul_mem (K.mul_mem hgK (hVK hx)) (K.inv_mem hgK)
    simpa [mul_assoc] using this
  set I := V ⊔ conjSub g V with hIdef
  have hIK : I ≤ K := sup_le hVK hWK
  have hW : ∀ w ∈ conjSub g V, w ^ 2 = 1 := by
    intro w hw
    rw [mem_conjSub] at hw
    have h1 := hV.2 _ hw
    have h2 : (g⁻¹ * w * g) ^ 2 = g⁻¹ * w ^ 2 * g := by
      simp only [pow_two, mul_assoc, mul_inv_cancel_left]
    rw [h2] at h1
    have h3 := congrArg (fun x => g * x * g⁻¹) h1
    simpa [mul_assoc] using h3
  obtain ⟨a, ha⟩ := (isPGroup_of_isElemAbelian hV).exists_card_eq
  have ha2 : 2 ≤ a := by
    by_contra h
    rw [ha] at hV4
    interval_cases a <;> norm_num at hV4
  have h4 : 4 ∣ Nat.card I := by
    have := Subgroup.card_dvd_of_le (le_sup_left : V ≤ I)
    rw [ha] at this
    exact (show 4 = 2 ^ 2 by norm_num) ▸ (Nat.pow_dvd_pow 2 ha2).trans this
  have hV1 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV4
    omega
  have hI2 : ¬ IsPGroup 2 I := not_isPGroup_sup_conjSub hB hS hVS hV1 hgK hgN
  set A := (V.subgroupOf K).map e.toMonoidHom with hAdef
  set B' := ((conjSub g V).subgroupOf K).map e.toMonoidHom with hB'def
  have hmap : A ⊔ B' = (I.subgroupOf K).map e.toMonoidHom := by
    rw [hAdef, hB'def, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hVK hWK]
  have hA : ∀ x ∈ A, x ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, show v ^ 2 = 1 from Subtype.ext (by
      simpa using hV.2 _ (Subgroup.mem_subgroupOf.mp hv)), map_one]
  have hB'2 : ∀ x ∈ B', x ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, show v ^ 2 = 1 from Subtype.ext (by
      simpa using hW _ (Subgroup.mem_subgroupOf.mp hv)), map_one]
  have hAB : ¬ IsPGroup 2 ↥(A ⊔ B') := by
    intro h
    rw [hmap] at h
    exact hI2 ((h.of_equiv (Subgroup.equivMapOfInjective _ _ e.injective).symm).of_equiv
      (Subgroup.subgroupOfEquivOfLe hIK))
  obtain ⟨x, hx⟩ := exists_conj_le_range_sublinePSU J hJ hn hEcard hfixed hA hB'2 hAB
  let φ₀ : ↥I →* ProjectiveSpecialUnitaryMatrixGroup J :=
    ((MulAut.conj x).toMonoidHom.comp e.toMonoidHom).comp (Subgroup.inclusion hIK)
  have hφ₀ : Function.Injective φ₀ :=
    (MulAut.conj x).injective.comp (e.injective.comp (Subgroup.inclusion_injective hIK))
  have hφ₀r : ∀ i, φ₀ i ∈ (sublinePSU J hJ).range := by
    intro i
    apply hx
    refine ⟨e (Subgroup.inclusion hIK i), ?_, rfl⟩
    rw [hmap]
    exact ⟨Subgroup.inclusion hIK i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  let σ' := MonoidHom.ofInjective (sublinePSU_injective J hJ)
  let φ₁ : ↥I →* SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) :=
    σ'.symm.toMonoidHom.comp (φ₀.codRestrict _ hφ₀r)
  have hφ₁ : Function.Injective φ₁ :=
    σ'.symm.injective.comp fun a b h => hφ₀ (congrArg Subtype.val h)
  have hk : Nat.card (unitaryCoverFixedField J) = 2 ^ n := card_unitaryCoverFixedField hfixed
  let : Fintype (unitaryCoverFixedField J) := Fintype.ofFinite _
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let τ : unitaryCoverFixedField J ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk,
      GaloisField.card 2 n (by omega)])
  let φ₂ : ↥I →* SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (SpecialLinearGroup.map τ.toRingHom).comp φ₁
  have hφ₂ : Function.Injective φ₂ := (specialLinearGroup_map_injective τ.injective).comp hφ₁
  let π : SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* PSL2MatrixGroup (GaloisField 2 n) :=
    QuotientGroup.mk' _
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact Subgroup.card_eq_one.mp
      (huppert614_card_center_of_neg_one_eq_one (K := GaloisField 2 n) (CharTwo.neg_eq 1))
  obtain ⟨k, hk2, hkn, hk'⟩ := exists_isPSL_of_sup_of_injective (by omega) (π.comp φ₂)
    (hπ.comp hφ₂) rfl hV.2 hW h4 hI2
  exact ⟨k, hk2, hkn, Or.inl hk'⟩

end E2

end CFSG.Quasithin
