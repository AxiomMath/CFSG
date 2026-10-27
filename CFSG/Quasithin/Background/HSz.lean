module

public import CFSG.Quasithin.Background.HConj
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut

public section

namespace CFSG.Quasithin

namespace H

namespace Sz

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut
  map_mem_suzukiGroup)
open scoped Matrix

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiS_mulVec (u v : K) (x : Fin 4 → K) :
    suzukiS a u v *ᵥ x = ![x 0, u * x 0 + x 1, v * x 0 + u ^ 2 ^ (a + 1) * x 1 + x 2,
      suzukiN a u v * x 0 + (u ^ (2 ^ (a + 1) + 1) + v) * x 1 + u * x 2 + x 3] := by
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiN_one_zero : suzukiN a (1 : K) 0 = 1 := by
  simp [suzukiN]

theorem hasScalarCommutant
    : HasScalarCommutant (suzukiGroup a K) := by
  intro f hf
  have hS : ∀ u v : K, ∀ x, f (suzukiS a u v *ᵥ x) = suzukiS a u v *ᵥ f x := fun u v x =>
    hf _ (suzukiSElt a K u v).2 x
  have hW : ∀ x, f (suzukiW K *ᵥ x) = suzukiW K *ᵥ f x := fun x =>
    hf _ (suzukiWElt a K).2 x
  have hline : ∀ c : K, ∃ d : K, f (Pi.single 3 c) = Pi.single 3 d := by
    intro c
    have h := hS 1 0 (Pi.single 3 c)
    have hfix : suzukiS a (1 : K) 0 *ᵥ Pi.single 3 c = Pi.single 3 c := by
      rw [suzukiS_mulVec]
      ext i
      fin_cases i <;> simp
    rw [hfix, suzukiS_mulVec, suzukiN_one_zero] at h
    set w := f (Pi.single 3 c) with hw
    have e0 : w 0 = 0 := by simpa using congrFun h 1
    have e1 : w 1 = 0 := by simpa using congrFun h 2
    have e2 : w 2 = 0 := by simpa [e0, e1] using congrFun h 3
    refine ⟨w 3, ?_⟩
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  choose φ hφ using hline
  have h0 : ∀ c : K, f (Pi.single 0 c) = Pi.single 0 (φ c) := by
    intro c
    have hW3 : ∀ d : K, suzukiW K *ᵥ (Pi.single 3 d : Fin 4 → K) = Pi.single 0 d := by
      intro d
      rw [suzukiW_mulVec]
      ext i
      fin_cases i <;> simp
    rw [← hW3, hW, hφ, hW3]
  have hS0 : ∀ u c : K, f (Pi.single 1 (u * c)) =
      Pi.single 1 (u * φ c) + Pi.single 3 (suzukiN a u 0 * φ c - φ (suzukiN a u 0 * c)) := by
    intro u c
    have e : suzukiS a u 0 *ᵥ (Pi.single 0 c : Fin 4 → K) =
        Pi.single 0 c + Pi.single 1 (u * c) + Pi.single 3 (suzukiN a u 0 * c) := by
      rw [suzukiS_mulVec]
      ext i
      fin_cases i <;> simp
    have e' : suzukiS a u 0 *ᵥ (Pi.single 0 (φ c) : Fin 4 → K) =
        Pi.single 0 (φ c) + Pi.single 1 (u * φ c) + Pi.single 3 (suzukiN a u 0 * φ c) := by
      rw [suzukiS_mulVec]
      ext i
      fin_cases i <;> simp
    have h := hS u 0 (Pi.single 0 c)
    rw [h0, e, e', map_add, map_add, h0, hφ] at h
    have : f (Pi.single 1 (u * c)) = Pi.single 1 (u * φ c) + Pi.single 3 (suzukiN a u 0 * φ c) -
        Pi.single 3 (φ (suzukiN a u 0 * c)) := by
      rw [← sub_eq_zero]
      rw [← sub_eq_zero] at h
      rw [← h]
      abel
    rw [this, add_sub_assoc, ← Pi.single_sub]
  have hφmul : ∀ u c : K, φ (u * c) = u * φ c := by
    intro u c
    have h1 := hS0 u c
    have h2 := hS0 1 (u * c)
    rw [one_mul, one_mul, suzukiN_one_zero, one_mul, one_mul, sub_self, Pi.single_zero,
      add_zero] at h2
    have := congrFun (h2.symm.trans h1) 1
    simpa using this
  set d := φ 1 with hd
  have hφd : ∀ c : K, φ c = c * d := fun c => by rw [hd, ← hφmul, mul_one]
  have h1 : ∀ c : K, f (Pi.single 1 c) = Pi.single 1 (d * c) := by
    intro c
    have := hS0 c 1
    simp only [mul_one, hφd, one_mul, sub_self, Pi.single_zero, add_zero] at this
    rw [this, mul_comm]
  have h2 : ∀ v : K, f (Pi.single 2 v) = Pi.single 2 (d * v) := by
    intro v
    have e : suzukiS a 0 v *ᵥ (Pi.single 0 1 : Fin 4 → K) =
        Pi.single 0 1 + Pi.single 2 v + Pi.single 3 (suzukiN a 0 v) := by
      rw [suzukiS_mulVec]
      ext i
      fin_cases i <;> simp
    have e' : suzukiS a 0 v *ᵥ (Pi.single 0 d : Fin 4 → K) =
        Pi.single 0 d + Pi.single 2 (v * d) + Pi.single 3 (suzukiN a 0 v * d) := by
      rw [suzukiS_mulVec]
      ext i
      fin_cases i <;> simp
    have h := hS 0 v (Pi.single 0 1)
    rw [h0, e, map_add, map_add, h0, hφ, hφd, hφd, one_mul, e'] at h
    rw [add_left_cancel (add_right_cancel h), mul_comm]
  refine ⟨d, fun x => ?_⟩
  have hx : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) + Pi.single 2 (x 2) +
      Pi.single 3 (x 3) := by
    ext i
    fin_cases i <;> simp
  rw [hx, map_add, map_add, map_add, h0, h1, h2, hφ, hφd, hφd]
  ext i
  fin_cases i <;> simp [mul_comm]

theorem fieldMap_mul_natAut (σ : K ≃+* K) (γ : suzukiGroup a K) :
    fieldMap σ * natAut (suzukiGroup a K) γ * (fieldMap σ)⁻¹ =
      natAut (suzukiGroup a K) (szFieldAut a K σ γ) :=
  toAddMap_injective fun v => by
    rw [toAddMap_natAut, coe_szFieldAut]
    exact toAddMap_fieldMap_conj σ (γ : GL (Fin 4) K) v

theorem fieldMap_mem_natNorm (σ : K ≃+* K) : fieldMap σ ∈ natNorm (suzukiGroup a K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨szFieldAut a K σ γ, (fieldMap_mul_natAut σ γ).symm⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨szFieldAut a K σ.symm γ, ?_⟩
    have h := fieldMap_mul_natAut σ.symm γ
    rw [fieldMap_symm, inv_inv] at h
    rw [← h, hγ]
    group

theorem conjHom_fieldMap (σ : K ≃+* K) :
    conjHom (suzukiGroup a K) ⟨fieldMap σ, fieldMap_mem_natNorm σ⟩ = szFieldAut a K σ := by
  refine MulEquiv.ext fun γ => ?_
  apply natAut_injective
  rw [natAut_conjHom]
  exact fieldMap_mul_natAut σ γ

theorem isSemilinear_of_smul {g : MulAut (StdMod (Fin 4) K)} {c : K}
    {A : Matrix (Fin 4) (Fin 4) K} (h : ∀ v, toAddMap g v = c • (A *ᵥ v)) :
    IsSemilinear g (RingEquiv.refl K) := by
  intro l v
  rw [h, h, Matrix.mulVec_smul, smul_comm]
  rfl

theorem eq_refl_of_szFieldAut_mem_inner {σ : K ≃+* K}
    (h : szFieldAut a K σ ∈ inner (suzukiGroup a K)) : σ = RingEquiv.refl K := by
  obtain ⟨s, hs⟩ := h
  have h1 : conjHom (suzukiGroup a K) ⟨fieldMap σ, fieldMap_mem_natNorm σ⟩ =
      MulAut.conj s := by
    rw [conjHom_fieldMap]
    exact hs.symm
  obtain ⟨c, hc⟩ := exists_smul_of_conjHom_eq hasScalarCommutant _ s h1
  exact (isSemilinear_fieldMap σ).unique (isSemilinear_of_smul hc)

variable [Finite K]

theorem exists_szFieldAut_eq
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x : Outer (suzukiGroup a K)) :
    ∃ σ : K ≃+* K, (QuotientGroup.mk' (inner (suzukiGroup a K))) (szFieldAut a K σ) = x := by
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have : Finite (MulAut (suzukiGroup a K)) := MulEquiv.finite_left
  let f : RingAut K →* Outer (suzukiGroup a K) :=
    (QuotientGroup.mk' (inner (suzukiGroup a K))).comp (szFieldAut a K)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have h1 : szFieldAut a K σ ∈ inner (suzukiGroup a K) := (QuotientGroup.eq_one_iff _).mp hσ
    exact eq_refl_of_szFieldAut_mem_inner h1
  have hcard : Nat.card (Outer (suzukiGroup a K)) ≤ Nat.card (RingAut K) := by
    obtain ⟨-, hdvd⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega : 1 ≤ 2 * a + 1) hK
    have hc' : Nat.card (RingAut K) = 2 * a + 1 := hc
    rw [hc']
    exact Nat.le_of_dvd (by omega) hdvd
  obtain ⟨σ, hσ⟩ := (hf.bijective_of_nat_card_le hcard).2 x
  exact ⟨σ, hσ⟩

theorem exists_smul_of_linear
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : MulAut (StdMod (Fin 4) K)} (hg : g ∈ natNorm (suzukiGroup a K))
    (hlin : IsSemilinear g (RingEquiv.refl K)) :
    ∃ s : suzukiGroup a K, ∃ c : K, ∀ v, toAddMap g v =
      c • ((((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) := by
  obtain ⟨σ, hσ⟩ := exists_szFieldAut_eq ha hK
    ((QuotientGroup.mk' (inner (suzukiGroup a K))) (conjHom (suzukiGroup a K) ⟨g, hg⟩))
  have h1 : (szFieldAut a K σ)⁻¹ * conjHom (suzukiGroup a K) ⟨g, hg⟩ ∈
      inner (suzukiGroup a K) := QuotientGroup.eq.mp hσ
  obtain ⟨s, hs⟩ := h1
  let g' : ↥(natNorm (suzukiGroup a K)) := ⟨fieldMap σ, fieldMap_mem_natNorm σ⟩⁻¹ * ⟨g, hg⟩
  have h2 : conjHom (suzukiGroup a K) g' = MulAut.conj s := by
    rw [map_mul, map_inv, conjHom_fieldMap, hs]
  obtain ⟨c, hc⟩ := exists_smul_of_conjHom_eq hasScalarCommutant g' s h2
  have hgg : g = fieldMap σ * (g' : MulAut (StdMod (Fin 4) K)) := by
    change g = fieldMap σ * ((fieldMap σ)⁻¹ * g)
    group
  have hσsl : IsSemilinear g ((RingEquiv.refl K).trans σ) := by
    rw [hgg]
    exact (isSemilinear_fieldMap σ).mul (isSemilinear_of_smul hc)
  have hσ1 : (RingEquiv.refl K).trans σ = RingEquiv.refl K := hσsl.unique hlin
  have hσ2 : σ = 1 := by
    ext x
    exact congrArg (fun τ : K ≃+* K => τ x) hσ1
  refine ⟨s, c, fun v => ?_⟩
  have hg' : (g' : MulAut (StdMod (Fin 4) K)) = g := by
    have h1 : fieldMap (ι := Fin 4) (1 : RingAut K) = 1 := toAddMap_injective fun _ => rfl
    rw [hgg, hσ2, h1, one_mul]
  rw [← hg']
  exact hc v

theorem eq_one_of_pow_eight_eq_one (hK : Nat.card K = 2 ^ (2 * a + 1)) {c : K}
    (h : c ^ 8 = 1) : c = 1 := by
  obtain ⟨hchar, -⟩ := suzuki_frobenius_exponents a K hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c - 1) ^ 2 ^ 3 = c ^ 2 ^ 3 - 1 ^ 2 ^ 3 := sub_pow_char_pow c 1 3
  have h2 : (c - 1) ^ 2 ^ 3 = 0 := by
    rw [h1, one_pow]
    norm_num [h]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)

theorem mem_natImage_of_sq_eq_one
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : MulAut (StdMod (Fin 4) K)} (hg : g ∈ natNorm (suzukiGroup a K)) (hg2 : g ^ 2 = 1) :
    g ∈ natImage (suzukiGroup a K) := by
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hcop : Nat.Coprime 2 (Nat.card (Outer (suzukiGroup a K))) := by
    obtain ⟨-, hdvd⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
    have h2 : Nat.Coprime 2 (2 * a + 1) := by
      rw [Nat.coprime_two_left]
      exact odd_two_mul_add_one a
    exact h2.coprime_dvd_right hdvd
  have hin : conjHom (suzukiGroup a K) ⟨g, hg⟩ ∈ inner (suzukiGroup a K) := by
    refine mem_inner_of_pow_eq_one (k := 2) ?_ hcop
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(natNorm (suzukiGroup a K))) ^ 2 = 1 := Subtype.ext hg2
    rw [this, map_one]
  obtain ⟨s, hs⟩ := hin
  obtain ⟨c, hc⟩ := exists_smul_of_conjHom_eq hasScalarCommutant _ s hs.symm
  set S : Matrix (Fin 4) (Fin 4) K :=
    (((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hS
  have hM : (c ^ 2) • (S * S) = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    have h1 := congrArg (fun y => toAddMap y v) hg2
    simp only [pow_two, toAddMap_mul] at h1
    rw [hc, hc, Matrix.mulVec_smul, smul_smul] at h1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.one_mulVec, pow_two]
    exact h1
  have hdet : (c ^ 2) ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, Matrix.det_one, hS,
      det_suzukiGroup, mul_one, mul_one] at h1
    exact h1
  have hc1 : c = 1 := eq_one_of_pow_eight_eq_one hK (by rw [← hdet]; ring)
  refine ⟨s, toAddMap_injective fun v => ?_⟩
  rw [hc, hc1, one_smul, toAddMap_natAut]

theorem pRank_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hXN : X ≤ natNorm (suzukiGroup a K)) :
    CFSG.Open.pRank 2 X ≤ 2 * a + 1 := by
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank X
  have hEI : E ≤ natImage (suzukiGroup a K) := fun x hx =>
    mem_natImage_of_sq_eq_one ha hK (hXN (hEX hx)) (hE.2 x hx)
  have h1 : CFSG.Open.pRank 2 X ≤ CFSG.Open.pRank 2 (natImage (suzukiGroup a K)) :=
    le_pRank Nat.prime_two hEI hE hEc
  have h2 : CFSG.Open.pRank 2 (natImage (suzukiGroup a K)) =
      CFSG.Open.twoRank (suzukiGroup a K) := by
    rw [natImage, MonoidHom.range_eq_map, pRank_two_map_of_injective _ (natAut_injective _)]
    rfl
  rw [h2, CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_suzukiGroup hK] at h1
  exact h1

theorem rkIdx_fixV_conj {V : Type*} [CommGroup V] [Finite V] (g x : MulAut V) :
    rkIdx (fixV (Subgroup.zpowers (g * x * g⁻¹))) = rkIdx (fixV (Subgroup.zpowers x)) := by
  have h : (Subgroup.zpowers x).map (congrHom g) = Subgroup.zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    congr 1
  rw [← h, rkIdx_fixV_map_congrHom]

theorem orderOf_suzukiSElt_zero_one
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    orderOf (suzukiSElt a K 0 1) = 2 := by
  obtain ⟨hchar, -⟩ := suzuki_frobenius_exponents a K hK
  apply orderOf_eq_prime
  · rw [sq, suzukiSElt_mul hK, add_zero, zero_pow (by positivity), zero_mul, add_zero,
      CharTwo.add_self_eq_zero, suzukiSElt_zero_zero hK]
  · intro h
    have := congrArg (fun g : suzukiGroup a K =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 0) h
    simp [coe_suzukiSElt, suzukiS] at this

theorem rkIdx_fixV_suzukiSElt (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rkIdx (fixV (Subgroup.zpowers (natAut (suzukiGroup a K) (suzukiSElt a K 0 1)))) =
      2 * (2 * a + 1) := by
  have hfix : ∀ v : Fin 4 → K,
      toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 1)) v = v ↔ v 0 = 0 ∧ v 1 = 0 := by
    intro v
    rw [toAddMap_natAut, coe_suzukiSElt, suzukiS_mulVec]
    constructor
    · intro h
      have h2 := congrFun h 2
      have h3 := congrFun h 3
      simp [suzukiN] at h2 h3
      refine ⟨h2, ?_⟩
      simpa [h2] using h3
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> simp [h0, h1]
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers (natAut (suzukiGroup a K)
      (suzukiSElt a K 0 1)))) = 2 ^ (2 * (2 * a + 1)) := by
    rw [card_fixV_zpowers]
    have : Nat.card {v : Fin 4 → K //
        toAddMap (natAut (suzukiGroup a K) (suzukiSElt a K 0 1)) v = v} = Nat.card (K × K) := by
      refine Nat.card_congr
        { toFun := fun v => (v.1 2, v.1 3)
          invFun := fun p => ⟨![0, 0, p.1, p.2], (hfix _).mpr ⟨rfl, rfl⟩⟩
          left_inv := fun v => by
            apply Subtype.ext
            obtain ⟨h0, h1⟩ := (hfix v.1).mp v.2
            ext i
            fin_cases i
            · exact h0.symm
            · exact h1.symm
            · rfl
            · rfl
          right_inv := fun p => rfl }
    rw [this, Nat.card_prod, hK, ← pow_add]
    ring_nf
  rw [rkIdx_fixV_of_card hK _ (by simp; omega) hcard]
  simp
  omega

theorem rkIdx_fixV_of_involution
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {t : MulAut (StdMod (Fin 4) K)} (htN : t ∈ natNorm (suzukiGroup a K)) (ht : orderOf t = 2) :
    rkIdx (fixV (Subgroup.zpowers t)) = 2 * (2 * a + 1) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  obtain ⟨x, rfl⟩ := mem_natImage_of_sq_eq_one ha hK htN ht2
  have hx : orderOf x = 2 := by
    rw [← orderOf_injective _ (natAut_injective _) x]
    exact ht
  obtain ⟨u, hu⟩ := isConj_iff.mp ((CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate
    hK) (suzukiSElt a K 0 1) x (orderOf_suzukiSElt_zero_one hK) hx)
  have hconj : natAut (suzukiGroup a K) x = natAut (suzukiGroup a K) u *
      natAut (suzukiGroup a K) (suzukiSElt a K 0 1) * (natAut (suzukiGroup a K) u)⁻¹ := by
    rw [← hu, map_mul, map_mul, map_inv]
  rw [hconj, rkIdx_fixV_conj, rkIdx_fixV_suzukiSElt hK]

theorem not_isFOneModule
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hXN : X ≤ natNorm (suzukiGroup a K)) :
    ¬ IsFOneModule X := by
  rintro ⟨A, ⟨hAX, hA1, hAel⟩, hoff⟩
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have hrk : rk ↥A ≤ 2 * a + 1 := (rk_le_pRank hAX hAel).trans (pRank_le ha hK hXN)
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have hbo : orderOf (b : MulAut (StdMod (Fin 4) K)) = 2 :=
    orderOf_eq_prime (hAel.2 b b.2) (fun h => hb1 (Subtype.ext h))
  have h2 := rkIdx_fixV_of_involution ha hK (hXN (hAX b.2)) hbo
  have h3 : rkIdx (fixV (Subgroup.zpowers (b : MulAut (StdMod (Fin 4) K)))) ≤
      rkIdx (fixV A) :=
    rkIdx_anti (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr b.2 hy))
  omega

theorem alphaH_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hXN : X ≤ natNorm (suzukiGroup a K)) :
    alphaH X = 1 :=
  alphaH_eq_one_of_not_isFOneModule (not_isFOneModule ha hK hXN)

theorem eq_one_of_pow_two_pow_eq_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : ℕ) {c : K}
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  obtain ⟨hchar, -⟩ := suzuki_frobenius_exponents a K hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c - 1) ^ 2 ^ k = c ^ 2 ^ k - 1 ^ 2 ^ k := sub_pow_char_pow c 1 k
  rw [h, one_pow, sub_self] at h1
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)

abbrev dEnt (a : ℕ) (l : Kˣ) : Fin 4 → K :=
  ![((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K), ((l ^ (2 ^ a : ℤ) : Kˣ) : K),
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K), ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)]

omit [Finite K] in
theorem suzukiD_eq_diagonal (l : Kˣ) : suzukiD a l = Matrix.diagonal (dEnt a l) := rfl

theorem zpow_sub_eq_one {G : Type*} [Group G] {l : G} {m n : ℤ} (h : l ^ m = l ^ n) :
    l ^ (m - n) = 1 := by
  rw [_root_.zpow_sub, h, mul_inv_cancel]

theorem dEnt_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ} (hl : l ≠ 1) :
    ∀ i j, dEnt a l i = dEnt a l j → i = j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hb1, -, hb3⟩ := suzuki_frobenius_exponents a K hK
  have hodd := odd_card_units hK
  have hA : ∀ {m n : ℤ}, ((l ^ m : Kˣ) : K) = ((l ^ n : Kˣ) : K) → l ^ (m - n) = 1 :=
    fun h => zpow_sub_eq_one (Units.ext h)
  have e1 : l ^ (1 : ℤ) ≠ 1 := by rwa [zpow_one]
  have e2 : l ^ ((2 : ℤ) ^ (a + 1) + 1) ≠ 1 := by
    intro h
    apply hl
    apply hb1.1
    change l ^ ((2 : ℤ) ^ (a + 1) + 1) = (1 : Kˣ) ^ ((2 : ℤ) ^ (a + 1) + 1)
    rw [h, _root_.one_zpow]
  have e3 : l ^ ((2 : ℤ) ^ (a + 1) + 2) ≠ 1 := by
    intro h
    have h1 : (l ^ (1 + (2 : ℤ) ^ a)) ^ 2 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, ← h]
      congr 1
      push_cast
      ring
    have h2 := eq_one_of_sq_eq_one hK h1
    apply hl
    apply hb3.1
    change l ^ (1 + (2 : ℤ) ^ a) = (1 : Kˣ) ^ (1 + (2 : ℤ) ^ a)
    rw [h2, _root_.one_zpow]
  have e4 : l ^ ((2 : ℤ) ^ (a + 1)) ≠ 1 := by
    intro h
    apply hl
    have h1 : l ^ (2 ^ (a + 1)) = 1 := by
      rw [← zpow_natCast]
      push_cast
      exact h
    have h2 : orderOf l ∣ 2 ^ (a + 1) := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf l ∣ Nat.card Kˣ := orderOf_dvd_natCard l
    have hcop : Nat.Coprime (2 ^ (a + 1)) (Nat.card Kˣ) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3)
  have hneg : ∀ {e : ℤ}, l ^ (-e) = 1 → l ^ e = 1 := fun h => by
    rwa [_root_.zpow_neg, inv_eq_one] at h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [dEnt] at hij ⊢ <;> first
    | rfl
    | (exfalso; have h := hA hij; first
        | (apply e1; convert h using 2; ring1)
        | (apply e2; convert h using 2; ring1)
        | (apply e3; convert h using 2; ring1)
        | (apply e4; convert h using 2; ring1)
        | (apply e1; apply hneg; convert h using 2; ring1)
        | (apply e2; apply hneg; convert h using 2; ring1)
        | (apply e3; apply hneg; convert h using 2; ring1)
        | (apply e4; apply hneg; convert h using 2; ring1))

theorem card_fix_smul_suzukiD_le (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ} (hl : l ≠ 1)
    (c : K) : Nat.card {w : Fin 4 → K // c • (suzukiD a l *ᵥ w) = w} ≤ Nat.card K := by
  have h1 : Nat.card {w : Fin 4 → K // c • (suzukiD a l *ᵥ w) = w} =
      Nat.card {w : Fin 4 → K // ∀ i, c * (dEnt a l i * w i) = w i} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rw [suzukiD_eq_diagonal, funext_iff]
    simp [Matrix.mulVec_diagonal]
  rw [h1]
  exact card_fix_diag_le _ (dEnt_injective hK hl) c

theorem le_rkIdx_fixV_of_odd
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hXN : X ≤ natNorm (suzukiGroup a K)) {p : ℕ}
    [hpf : Fact p.Prime] (hp2 : p ≠ 2) {y : MulAut (StdMod (Fin 4) K)} (hyX : y ∈ X)
    (hyo : orderOf y = p) : 8 * (2 * a + 1) ≤ 3 * rkIdx (fixV (Subgroup.zpowers y)) := by
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have hp : p.Prime := hpf.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  have hV : Nat.card (StdMod (Fin 4) K) = 2 ^ ((2 * a + 1) * 4) := by
    rw [card_stdMod, hK, Fintype.card_fin, ← pow_mul]
  obtain ⟨σ, hsl⟩ := exists_semilinear hasScalarCommutant (hXN hyX)
  by_cases hσ : σ = RingEquiv.refl K
  swap
  ·
    have hσp : σ ^ p = 1 := by
      have h1 := hsl.pow p
      rw [hyp] at h1
      exact h1.unique isSemilinear_one
    have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ
    obtain ⟨⟨k, hk⟩, hcard⟩ := card_fixV_of_semilinear (by omega) hK hsl hσo hyp
    simp only [Fintype.card_fin] at hcard
    have hj : (2 * a + 1) * 4 / p = 4 * k := by
      rw [hk, show p * k * 4 = p * (4 * k) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [hj] at hcard
    have hkp : 3 * k ≤ p * k := Nat.mul_le_mul_right k hp3
    have hle : 4 * k ≤ (2 * a + 1) * Fintype.card (Fin 4) := by
      rw [Fintype.card_fin, hk]
      generalize p * k = P at hkp ⊢
      omega
    rw [rkIdx_fixV_of_card hK y hle hcard, Fintype.card_fin, hk]
    generalize p * k = P at hkp ⊢
    omega
  rw [hσ] at hsl
  obtain ⟨s, c, hc⟩ := exists_smul_of_linear ha hK (hXN hyX) hsl
  set S : Matrix (Fin 4) (Fin 4) K :=
    (((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hS
  have hpow : ∀ k : ℕ, ∀ v, toAddMap (y ^ k) v = c ^ k • ((S ^ k) *ᵥ v) := by
    intro k
    induction k with
    | zero =>
      intro v
      rw [pow_zero, pow_zero, pow_zero, one_smul, Matrix.one_mulVec]
      rfl
    | succ k ih =>
      intro v
      rw [pow_succ', toAddMap_mul, ih, hc, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec,
        ← pow_succ', ← pow_succ']
  have hM : c ^ p • S ^ p = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    have h1 := hpow p v
    rw [hyp, toAddMap_one] at h1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact h1.symm
  have hcp : c ^ p = 1 := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_pow, Fintype.card_fin, Matrix.det_one, hS, det_suzukiGroup,
      one_pow, mul_one] at h1
    exact eq_one_of_pow_two_pow_eq_one hK 2 (by rw [← h1]; ring)
  have hSp : S ^ p = 1 := by rw [hcp, one_smul] at hM; exact hM
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  by_cases hs1 : s = 1
  ·
    have hS1 : S = 1 := by simp only [hS, hs1, OneMemClass.coe_one, Units.val_one]
    have hc1 : c ≠ 1 := by
      intro h
      apply hy1
      refine toAddMap_injective fun v => ?_
      rw [hc, h, hS1, one_smul, Matrix.one_mulVec, toAddMap_one]
    have hcard : Nat.card ↥(fixV (Subgroup.zpowers y)) = 2 ^ 0 := by
      rw [card_fixV_zpowers, pow_zero, Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun v w => Subtype.ext ?_⟩, ⟨⟨0, toAddMap_zero y⟩⟩⟩
      have hz : ∀ u : {v : Fin 4 → K // toAddMap y v = v}, u.1 = 0 := by
        intro u
        have h1 := u.2
        rw [hc, hS1, Matrix.one_mulVec] at h1
        have h2 : (c - 1) • u.1 = 0 := by rw [sub_smul, one_smul, h1, sub_self]
        exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc1)
      rw [hz v, hz w]
    rw [rkIdx_fixV_of_card hK y (by simp) hcard]
    simp
    omega
  have hsp : s ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hS, hSp]
    rfl
  have hso : orderOf s = p := orderOf_eq_prime hsp hs1
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hpdvd : p ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [← suzuki_order hK, ← hso]
    exact orderOf_dvd_natCard s
  by_cases hpq : p ∣ 2 ^ (2 * a + 1) - 1
  ·
    obtain ⟨h, hh⟩ := exists_conj_mem_suzukiT hK hp hp2 hpq hso
    obtain ⟨l, hl⟩ := mem_suzukiT_iff.mp hh
    have hl1 : l ≠ 1 := by
      rintro rfl
      apply hs1
      have h1 : suzukiDElt a K 1 = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [coe_suzukiDElt, suzukiD_eq_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [h1] at hl
      have := congrArg (fun z => h * z * h⁻¹) hl
      simpa [mul_assoc] using this.symm
    set H : Matrix (Fin 4) (Fin 4) K :=
      (((h : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hH
    set Hi : Matrix (Fin 4) (Fin 4) K :=
      (((h⁻¹ : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hHi
    have hHHi : H * Hi = 1 := by
      rw [hH, hHi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
      rfl
    have hHiH : Hi * H = 1 := by
      rw [hH, hHi, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    have hD : suzukiD a l = Hi * S * H := by
      have := congrArg (fun z : suzukiGroup a K => ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
        hl
      simp only [coe_suzukiDElt, Subgroup.coe_mul, Units.val_mul] at this
      rw [this]
    have hcard : Nat.card ↥(fixV (Subgroup.zpowers y)) ≤ 2 ^ (2 * a + 1) := by
      rw [card_fixV_zpowers, ← hK]
      refine le_trans (Nat.card_le_card_of_injective
        (fun v : {v : Fin 4 → K // toAddMap y v = v} =>
          (⟨Hi *ᵥ v.1, ?_⟩ : {w : Fin 4 → K // c • (suzukiD a l *ᵥ w) = w}))
        fun v w hvw => Subtype.ext ?_) (card_fix_smul_suzukiD_le hK hl1 c)
      · have h1 := v.2
        rw [hc] at h1
        rw [hD, Matrix.mulVec_mulVec, Matrix.mul_assoc, hHHi, Matrix.mul_one,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, h1]
      · have := congrArg (fun z => H *ᵥ z) (congrArg Subtype.val hvw)
        simpa [Matrix.mulVec_mulVec, hHHi] using this
    have h1 := le_rkIdx_of_card_le hV hcard
    omega
  ·
    have hc1 : c = 1 := by
      have : Fintype K := Fintype.ofFinite K
      have h1 : c ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one c hc0
      rw [Fintype.card_eq_nat_card, hK] at h1
      have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
      have h3 : orderOf c ∣ 2 ^ (2 * a + 1) - 1 := orderOf_dvd_of_pow_eq_one h1
      rcases (Nat.dvd_prime hp).mp h2 with h4 | h4
      · exact orderOf_eq_one_iff.mp h4
      · exact absurd (h4 ▸ h3) hpq
    have hpq2 : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
      rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h1 | h1
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · exfalso
          have h3 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h2)
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
        · exact absurd h2 hpq
      · exact h1
    let W : Submodule K (Fin 4 → K) :=
      { carrier := {v | toAddMap y v = v}
        add_mem' := fun {v w} hv hw => by
          change toAddMap y (v + w) = v + w
          rw [toAddMap_add, hv, hw]
        zero_mem' := toAddMap_zero y
        smul_mem' := fun c' v hv => by
          change toAddMap y (c' • v) = c' • v
          rw [hsl c' v, hv]
          rfl }
    have hWcard : Nat.card ↥(fixV (Subgroup.zpowers y)) =
        (2 ^ (2 * a + 1)) ^ Module.finrank K W := by
      rw [card_fixV_zpowers, ← hK]
      exact Module.natCard_eq_pow_finrank (K := K) (V := W)
    have hW4 : Module.finrank K W < 4 := by
      have hWtop : W ≠ ⊤ := by
        intro h
        apply hy1
        refine toAddMap_injective fun v => ?_
        have : v ∈ W := by rw [h]; trivial
        exact this
      have := Submodule.finrank_lt hWtop
      rwa [Module.finrank_fin_fun] at this
    have hmod := card_modEq_fix (V := StdMod (Fin 4) K) hyo
    have hfixeq : Nat.card {v : StdMod (Fin 4) K // y v = v} =
        Nat.card ↥(fixV (Subgroup.zpowers y)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_fixV_zpowers_iff.symm)
    rw [hfixeq, hWcard, card_stdMod, hK, Fintype.card_fin] at hmod
    have hw0 := eq_zero_of_modEq_of_dvd_sq_add_one hp hp2 hpq2 hW4 hmod
    rw [hw0, pow_zero] at hWcard
    rw [rkIdx_fixV_of_card hK y (by simp) (hWcard.trans (pow_zero 2).symm)]
    simp
    omega

theorem le_betaH (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hXN : X ≤ natNorm (suzukiGroup a K)) :
    ((8 * (2 * a + 1) : ℕ) : ℕ∞) ≤ 3 * betaH X := by
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have hb : (((8 * (2 * a + 1) + 2) / 3 : ℕ) : ℕ∞) ≤ betaH X := by
    rw [le_betaH_iff_isPGroup]
    intro U _ hnp
    obtain ⟨p, hp, hp2, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(X ⊓ centSub U) := by
      by_contra h
      push Not at h
      apply hnp
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro d hd hdd
      by_contra hd2
      exact h d hd hd2 hdd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ centSub U)) p hpdvd
    have hxo : orderOf (y : MulAut (StdMod (Fin 4) K)) = p := by
      rw [Subgroup.orderOf_coe, hy]
    have hUx : U ≤ fixV (Subgroup.zpowers (y : MulAut (StdMod (Fin 4) K))) := fun u hu =>
      mem_fixV_zpowers_iff.mpr (y.2.2 u hu)
    have h1 := le_rkIdx_fixV_of_odd ha hK hXN hp2 y.2.1 hxo
    have h2 := rkIdx_anti hUx
    have h3 : (8 * (2 * a + 1) + 2) / 3 ≤ rkIdx U := by omega
    exact_mod_cast h3
  calc ((8 * (2 * a + 1) : ℕ) : ℕ∞) ≤ ((3 * ((8 * (2 * a + 1) + 2) / 3) : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega)
    _ = 3 * (((8 * (2 * a + 1) + 2) / 3 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ 3 * betaH X := mul_le_mul_right hb 3

end Sz

open Sz in
theorem H3_Sz
    {V : Type*} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)} {n : ℕ}
    (hL : BinaryNaturalSz L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    CFSG.Open.pRank 2 M ≤ n ∧ ¬ IsFOneModule M ∧ alphaH M = 1 ∧
      ((8 * n : ℕ) : ℕ∞) ≤ 3 * betaH M := by
  obtain ⟨a, ha, rfl, K, _, _, hK, hreal⟩ := hL
  obtain ⟨e, -, h2⟩ := exists_transport_natural hreal hLM hMN
  have : Finite (StdMod (Fin 4) K) := Finite.of_equiv V e.toEquiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pRank_two_map_congrHom e]
    exact pRank_le ha hK h2
  · rw [← isFOneModule_map_congrHom e]
    exact not_isFOneModule ha hK h2
  · rw [← alphaH_map_congrHom e]
    exact Sz.alphaH_eq_one ha hK h2
  · rw [← betaH_map_congrHom e]
    exact le_betaH ha hK h2

end H

end CFSG.Quasithin
