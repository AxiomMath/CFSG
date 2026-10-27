module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisPerfect
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.Quasithin.SimsG4

open Matrix CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

theorem two_dvd_natCard (F : Type) [Field F] [Finite F] [CharP F 2] : 2 ∣ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.pos.ne'

theorem pCore_sl2_charTwo (F : Type) [Field F] [Finite F] [CharP F 2] :
    CFSG.pCore 2 (SL₂ F) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 (SL₂ F) with hNdef
  have hN : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hNn : N.Normal := CFSG.pCore_normal
  have hcard : 2 ∣ Nat.card F := two_dvd_natCard F
  have hdvd : 2 ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun]
    exact hcard.trans (dvd_pow_self _ (by simp))
  have h0 : (0 : Fin 2 → F) ∈ MulAction.fixedPoints N (Fin 2 → F) := fun n => smul_zero _
  obtain ⟨w, hw, hw0⟩ :=
    hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hdvd h0
  have hfix : ∀ n ∈ N, ∀ v : Fin 2 → F, (n : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
    intro n hn v
    by_cases hv : v = 0
    · rw [hv, Matrix.mulVec_zero]
    · obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq (Ne.symm hw0) hv
      have hconj : M⁻¹ * n * M ∈ N := by
        have := hNn.conj_mem n hn M⁻¹
        rwa [inv_inv] at this
      have h1 : ((M⁻¹ * n * M : SL₂ F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w :=
        (MulAction.mem_fixedPoints.mp hw) ⟨_, hconj⟩
      have h2 : (n : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) =
          (M : Matrix (Fin 2) (Fin 2) F) * ((M⁻¹ * n * M : SL₂ F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
        congr 1
        rw [mul_assoc, mul_inv_cancel_left]
      rw [← hM, Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h1]
  refine eq_bot_iff.mpr fun n hn => ?_
  rw [Subgroup.mem_bot]
  have hmat : (n : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Matrix.ext_of_mulVec_single fun i => by rw [hfix n hn, Matrix.one_mulVec]
  exact Subtype.ext hmat

variable {F : Type} [Field F] [CharP F 2]

variable (F) in
@[expose] noncomputable def c2LeviProj : ↥(rootC₂ F) →* SL₂ F :=
  (quotS₂Equiv F).symm.toMonoidHom.comp (QuotientGroup.mk' ((radA2 F).subgroupOf (rootC₂ F)))

theorem c2LeviProj_surjective : Function.Surjective (c2LeviProj F) :=
  (quotS₂Equiv F).symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem c2LeviProj_eq_one_iff (g : ↥(rootC₂ F)) :
    c2LeviProj F g = 1 ↔ (g : antiSp F) ∈ radA2 F := by
  rw [c2LeviProj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (quotS₂Equiv F).symm.injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem c2LeviProj_apply (v : Fin 2 → F) (c : F) (M : SL₂ F) (h : aElt v c * sElt M ∈ rootC₂ F) :
    c2LeviProj F ⟨aElt v c * sElt M, h⟩ = M := by
  rw [c2LeviProj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  change _ = quotS₂ F M
  rw [quotS₂_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((⟨aElt v c * sElt M, h⟩ : ↥(rootC₂ F))⁻¹ * ⟨sElt M, sElt_mem_rootC₂ M⟩ :
      ↥(rootC₂ F)) : antiSp F) = (sElt M)⁻¹ * aElt v c * (sElt M)⁻¹⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, aElt_inv, inv_inv]
  rw [e]
  exact conj_mem_radA2 (firstCol_sElt M).inv (aElt_mem_radA2 v c)

@[expose] def aCoordVC (v : Fin 2 → F) (c : F) : Fin 3 → F :=
  ![v 0 ^ 2, c + v 0 * v 1, v 1 ^ 2]

@[expose] def c2Coord (z : antiSp F) : Fin 3 → F :=
  aCoordVC (vecOf₂ z) (mat z 0 3)

theorem c2Coord_aElt (v : Fin 2 → F) (c : F) : c2Coord (aElt v c) = aCoordVC v c := by
  rw [c2Coord, vecOf₂_aElt]
  rfl

omit [CharP F 2] in
theorem aCoordVC_zero : aCoordVC (0 : Fin 2 → F) 0 = 0 := by
  funext i
  fin_cases i <;> simp [aCoordVC]

theorem aCoordVC_add (v w : Fin 2 → F) (c e : F) :
    aCoordVC (v + w) (c + e + (v 0 * w 1 + v 1 * w 0)) = aCoordVC v c + aCoordVC w e := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  funext i
  fin_cases i <;> simp [aCoordVC]
  · linear_combination (v 0 * w 0) * h2
  · linear_combination (v 0 * w 1 + v 1 * w 0) * h2
  · linear_combination (v 1 * w 1) * h2

omit [CharP F 2] in
theorem aCoordVC_eq_zero {v : Fin 2 → F} {c : F} (h : aCoordVC v c = 0) : v = 0 ∧ c = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [aCoordVC] at h0 h1 h2
  have hv : v = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h2
  refine ⟨hv, ?_⟩
  rw [h0, zero_mul, add_zero] at h1
  exact h1

theorem orthAct_aCoordVC (M : SL₂ F) (v : Fin 2 → F) (c : F) :
    orthAct M (aCoordVC v c) = aCoordVC ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ v) c := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet := M.det_coe
  rw [Matrix.det_fin_two] at hdet
  funext i
  fin_cases i <;>
    simp [orthAct, aCoordVC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  · linear_combination (M 0 0 * M 0 1 * (c + v 0 * v 1) - M 0 0 * M 0 1 * v 0 * v 1) * h2
  · linear_combination c * hdet + (M 0 1 * M 1 0 * c) * h2
  · linear_combination (M 1 0 * M 1 1 * (c + v 0 * v 1) - M 1 0 * M 1 1 * v 0 * v 1) * h2

theorem c2_levi_structure [Finite F] {X : Type*} [Group X] (Θ : X ≃* ↥(rootC₂ F)) :
    ∃ φ : X →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 X ∧
      ∃ ψ : ↥(CFSG.pCore 2 X) ≃* Multiplicative (Fin 3 → F),
        ∀ (g : X) (x y : ↥(CFSG.pCore 2 X)), g * (x : X) * g⁻¹ = (y : X) →
          Multiplicative.toAdd (ψ y) = orthAct (φ g) (Multiplicative.toAdd (ψ x)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : X →* SL₂ F := (c2LeviProj F).comp Θ.toMonoidHom with hφ
  have hφs : Function.Surjective φ := c2LeviProj_surjective.comp Θ.surjective
  have hker : ∀ g : X, g ∈ φ.ker ↔ ((Θ g : ↥(rootC₂ F)) : antiSp F) ∈ radA2 F := fun g => by
    rw [MonoidHom.mem_ker]
    exact c2LeviProj_eq_one_iff (Θ g)
  have hkerP : IsPGroup 2 φ.ker := by
    intro g
    refine ⟨1, ?_⟩
    have hsq := mul_self_of_mem_radA2 ((hker g).mp g.2)
    apply Subtype.ext
    apply Θ.injective
    apply Subtype.ext
    simp [pow_two, hsq]
  have hP : φ.ker = CFSG.pCore 2 X := by
    apply le_antisymm
    · exact le_sSup ⟨φ.normal_ker, hkerP⟩
    · intro x hx
      have hmap : (CFSG.pCore 2 X).map φ ≤ CFSG.pCore 2 (SL₂ F) :=
        le_sSup ⟨CFSG.pCore_normal.map φ hφs, CFSG.pCore_isPGroup.map φ⟩
      rw [pCore_sl2_charTwo] at hmap
      exact Subgroup.mem_bot.mp (hmap (Subgroup.mem_map_of_mem φ hx))
  have hmemA : ∀ x : ↥(CFSG.pCore 2 X), ((Θ x : ↥(rootC₂ F)) : antiSp F) ∈ radA2 F := fun x =>
    (hker x).mp (by rw [hP]; exact x.2)
  let ψ₀ : ↥(CFSG.pCore 2 X) →* Multiplicative (Fin 3 → F) :=
    { toFun := fun x => Multiplicative.ofAdd (c2Coord ((Θ x : ↥(rootC₂ F)) : antiSp F))
      map_one' := by
        simp only [OneMemClass.coe_one, map_one]
        rw [← aElt_zero_zero, c2Coord_aElt, aCoordVC_zero]
        rfl
      map_mul' := fun x y => by
        obtain ⟨v, c, hv⟩ := mem_radA2_iff.mp (hmemA x)
        obtain ⟨w, e, hw⟩ := mem_radA2_iff.mp (hmemA y)
        simp only [Subgroup.coe_mul, map_mul, hv, hw, aElt_mul, c2Coord_aElt]
        rw [aCoordVC_add, ofAdd_add] }
  have hψ₀ : ∀ x, ψ₀ x = Multiplicative.ofAdd (c2Coord ((Θ x : ↥(rootC₂ F)) : antiSp F)) :=
    fun _ => rfl
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hψ₀] at hx
    obtain ⟨v, c, hv⟩ := mem_radA2_iff.mp (hmemA x)
    rw [hv, c2Coord_aElt] at hx
    obtain ⟨rfl, rfl⟩ := aCoordVC_eq_zero (Multiplicative.ofAdd.injective hx)
    rw [aElt_zero_zero] at hv
    apply Subtype.ext
    apply Θ.injective
    apply Subtype.ext
    simpa using hv
  have hsurj : Function.Surjective ψ₀ := by
    intro t
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (Multiplicative.toAdd t 0)
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Multiplicative.toAdd t 2)
    set z := aElt ![r, s] (Multiplicative.toAdd t 1 + r * s) with hz
    have hzC : z ∈ rootC₂ F := radA2_le_centralizer_rootU₂ (aElt_mem_radA2 _ _)
    have hxP : Θ.symm ⟨z, hzC⟩ ∈ CFSG.pCore 2 X := by
      rw [← hP, hker, MulEquiv.apply_symm_apply]
      exact aElt_mem_radA2 _ _
    refine ⟨⟨_, hxP⟩, ?_⟩
    rw [hψ₀]
    simp only [MulEquiv.apply_symm_apply]
    rw [hz, c2Coord_aElt]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    funext i
    fin_cases i <;> simp [aCoordVC]
    · rw [hr, pow_two]
    · linear_combination (r * s) * h2
    · rw [hs, pow_two]
  refine ⟨φ, hφs, hP, MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩, ?_⟩
  intro g x y hxy
  obtain ⟨w, e, M, hg⟩ := exists_aElt_mul_sElt (Θ g).2
  obtain ⟨v, c, hx⟩ := mem_radA2_iff.mp (hmemA x)
  have hy : ((Θ y : ↥(rootC₂ F)) : antiSp F) = aElt ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ v) c := by
    have h1 := congrArg (fun t => ((Θ t : ↥(rootC₂ F)) : antiSp F)) hxy
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [← h1, hg, hx]
    have := conj_aElt_normalForm w e 1 M v c
    rw [dElt_one, one_mul] at this
    simpa using this
  have hφg : φ g = M := by
    change c2LeviProj F (Θ g) = M
    have : Θ g = ⟨aElt w e * sElt M, hg ▸ (Θ g).2⟩ := Subtype.ext hg
    rw [this, c2LeviProj_apply]
  change Multiplicative.toAdd (ψ₀ y) = orthAct (φ g) (Multiplicative.toAdd (ψ₀ x))
  rw [hψ₀, hψ₀, toAdd_ofAdd, toAdd_ofAdd, hy, hx, c2Coord_aElt, c2Coord_aElt, hφg,
    orthAct_aCoordVC]

theorem center_rootC₂ : Subgroup.center ↥(rootC₂ F) = (rootU₂ F).subgroupOf (rootC₂ F) := by
  ext z
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hz
    obtain ⟨v, c, M, hzv⟩ := exists_aElt_mul_sElt z.2
    have hM : M = 1 := by
      have hc : c2LeviProj F z ∈ Subgroup.center (SL₂ F) := by
        rw [Subgroup.mem_center_iff]
        intro N
        obtain ⟨g, rfl⟩ := c2LeviProj_surjective N
        rw [← map_mul, ← map_mul, hz g]
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hc
      have hz' : z = ⟨aElt v c * sElt M, hzv ▸ z.2⟩ := Subtype.ext hzv
      rw [hz', c2LeviProj_apply] at hc
      exact hc
    subst hM
    rw [sElt_one, mul_one] at hzv
    have hfix : ∀ N : SL₂ F, (N : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
      intro N
      have h1 := congrArg Subtype.val (hz ⟨sElt N, sElt_mem_rootC₂ N⟩)
      simp only [Subgroup.coe_mul, hzv] at h1
      rw [sElt_mul_aElt] at h1
      have h3 := congrArg vecOf₂ (mul_right_cancel h1)
      rwa [vecOf₂_aElt, vecOf₂_aElt] at h3
    have hv : v = 0 := by
      have e1 := congrFun (hfix ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩) 0
      have e2 := congrFun (hfix ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2
      funext i
      fin_cases i
      · exact e2
      · exact e1
    rw [hzv, hv]
    exact aElt_zero_mem_rootU₂ c
  · intro hz g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.mp g.2 _ hz).symm

@[expose] def slUpper (μ : F) : SL₂ F := ⟨!![1, μ; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slLower (μ : F) : SL₂ F := ⟨!![1, 0; μ, 1], by simp [Matrix.det_fin_two]⟩

theorem rootC₂_le_of_mem {H : Subgroup (antiSp F)} (h0 : ∀ μ : F, aElt 0 μ ∈ H)
    (h1 : ∀ μ : F, sElt (slUpper μ) ∈ H) (h2 : ∀ μ : F, sElt (slLower μ) ∈ H)
    (h3 : ∀ s : F, aElt ![s, 0] 1 * sElt (slUpper (s ^ 2)) ∈ H)
    (h4 : ∀ s : F, aElt ![0, s] 1 * sElt (slLower (s ^ 2)) ∈ H) :
    rootC₂ F ≤ H := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hS : ∀ M : SL₂ F, sElt M ∈ H := by
    intro M
    refine Matrix.SL2.transvection_induction (fun M => sElt M ∈ H) ?_ ?_ M
    · intro i j hij μ
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · convert h1 μ using 2
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [slUpper, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
      · convert h2 μ using 2
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [slLower, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
      · exact absurd rfl hij
    · intro A B hA hB
      rw [← sHom₂_apply, map_mul]
      exact H.mul_mem hA hB
  have hA1 : ∀ s : F, aElt ![s, 0] 0 ∈ H := by
    intro s
    have e : aElt ![s, 0] 0 =
        (aElt ![s, 0] 1 * sElt (slUpper (s ^ 2))) * (sElt (slUpper (s ^ 2)))⁻¹ * aElt 0 1 := by
      rw [mul_inv_cancel_right, aElt_mul]
      congr 1
      · simp
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, mul_zero, add_zero]
        linear_combination (-1 : F) * h2F
    rw [e]
    exact H.mul_mem (H.mul_mem (h3 s) (H.inv_mem (hS _))) (h0 1)
  have hA2 : ∀ s : F, aElt ![0, s] 0 ∈ H := by
    intro s
    have e : aElt ![0, s] 0 =
        (aElt ![0, s] 1 * sElt (slLower (s ^ 2))) * (sElt (slLower (s ^ 2)))⁻¹ * aElt 0 1 := by
      rw [mul_inv_cancel_right, aElt_mul]
      congr 1
      · simp
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, mul_zero, add_zero]
        linear_combination (-1 : F) * h2F
    rw [e]
    exact H.mul_mem (H.mul_mem (h4 s) (H.inv_mem (hS _))) (h0 1)
  intro g hg
  obtain ⟨v, c, M, rfl⟩ := exists_aElt_mul_sElt hg
  refine H.mul_mem ?_ (hS M)
  have e : aElt v c = aElt ![v 0, 0] 0 * aElt ![0, v 1] 0 * aElt 0 (c + v 0 * v 1) := by
    rw [aElt_mul, aElt_mul]
    congr 1
    · funext i
      fin_cases i <;> simp
    · simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
      linear_combination (-(v 0 * v 1)) * h2F
  rw [e]
  exact H.mul_mem (H.mul_mem (hA1 _) (hA2 _)) (h0 _)

end CFSG.Quasithin.SimsG4
