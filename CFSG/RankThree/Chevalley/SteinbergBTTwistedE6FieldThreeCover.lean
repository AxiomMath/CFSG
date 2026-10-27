module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6FieldThree
public import CFSG.RankThree.CentralCover.SteinbergBNFourDimensionalNormalizer
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)

section Plane

variable {r : ℕ} {K : Type} [Field K] [Algebra (ZMod r) K]

abbrev fieldThreePlane (r : ℕ) (K : Type) [Field K] [Algebra (ZMod r) K] :
    K →ₗ[ZMod r] ZMod r × ZMod r × K :=
  (LinearMap.inr (ZMod r) (ZMod r) (ZMod r × K)).comp (LinearMap.inr (ZMod r) (ZMod r) K)

theorem fieldThreePlane_injective : Function.Injective (fieldThreePlane r K) := fun x y h => by
  simpa using congrArg (fun v : ZMod r × ZMod r × K => v.2.2) h

abbrev fieldThreePlaneEquiv (r : ℕ) (K : Type) [Field K] [Algebra (ZMod r) K] :
    K ≃ₗ[ZMod r] LinearMap.range (fieldThreePlane r K) :=
  LinearEquiv.ofInjective _ fieldThreePlane_injective

@[expose] def fieldThreeSigma (r : ℕ) {K : Type} [Field K] [Algebra (ZMod r) K] (c : K) :
    (ZMod r × ZMod r × K) →ₗ[ZMod r] ZMod r × ZMod r × K where
  toFun v := (-v.1, v.2.1, c * v.2.2)
  map_add' v w := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' a v := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, mul_neg,
        Algebra.mul_smul_comm]

theorem fieldThreeSigma_apply (c : K) (a b : ZMod r) (v : K) :
    fieldThreeSigma r c (a, b, v) = (-a, b, c * v) :=
  rfl

theorem fieldThreeSigma_mem (c : K) :
    ∀ v ∈ LinearMap.range (fieldThreePlane r K), fieldThreeSigma r c v ∈
      LinearMap.range (fieldThreePlane r K) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨c * x, by simp [fieldThreeSigma_apply]⟩

theorem fieldThreeSigma_restrict_add (c : K) (d₀ : ZMod r) :
    ((fieldThreeSigma r c).restrict (fieldThreeSigma_mem c) + d₀ • 1 :
      Module.End (ZMod r) (LinearMap.range (fieldThreePlane r K))) =
      ((fieldThreePlaneEquiv r K : K ≃ₗ[ZMod r] _) : K →ₗ[ZMod r] _) ∘ₗ
        Algebra.lmul (ZMod r) K (c + algebraMap (ZMod r) K d₀) ∘ₗ
          ((fieldThreePlaneEquiv r K).symm :
            LinearMap.range (fieldThreePlane r K) →ₗ[ZMod r] K) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  obtain ⟨x, hx⟩ := w.2
  have hw : w = fieldThreePlaneEquiv r K x := Subtype.ext hx.symm
  rw [hw]
  simp [LinearEquiv.ofInjective_apply, fieldThreeSigma_apply, Algebra.smul_def]

theorem fieldThreeSigma_restrict_sub_one (c : K) :
    ((fieldThreeSigma r c).restrict (fieldThreeSigma_mem c) - 1 :
      Module.End (ZMod r) (LinearMap.range (fieldThreePlane r K))) =
      ((fieldThreePlaneEquiv r K : K ≃ₗ[ZMod r] _) : K →ₗ[ZMod r] _) ∘ₗ
        Algebra.lmul (ZMod r) K (c - 1) ∘ₗ
          ((fieldThreePlaneEquiv r K).symm :
            LinearMap.range (fieldThreePlane r K) →ₗ[ZMod r] K) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  obtain ⟨x, hx⟩ := w.2
  have hw : w = fieldThreePlaneEquiv r K x := Subtype.ext hx.symm
  rw [hw]
  simp [LinearEquiv.ofInjective_apply, fieldThreeSigma_apply]

theorem fieldThreeSigma_restrict_add_one (c : K) :
    ((fieldThreeSigma r c).restrict (fieldThreeSigma_mem c) + 1 :
      Module.End (ZMod r) (LinearMap.range (fieldThreePlane r K))) =
      ((fieldThreePlaneEquiv r K : K ≃ₗ[ZMod r] _) : K →ₗ[ZMod r] _) ∘ₗ
        Algebra.lmul (ZMod r) K (c + 1) ∘ₗ
          ((fieldThreePlaneEquiv r K).symm :
            LinearMap.range (fieldThreePlane r K) →ₗ[ZMod r] K) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  obtain ⟨x, hx⟩ := w.2
  have hw : w = fieldThreePlaneEquiv r K x := Subtype.ext hx.symm
  rw [hw]
  simp [LinearEquiv.ofInjective_apply, fieldThreeSigma_apply]

end Plane

section Prime

variable {r : ℕ} {K : Type} [Field K] [Finite K] [Algebra (ZMod r) K]

abbrev fieldThreePrimeField {r : ℕ} (hrp : r.Prime) : Field (ZMod r) :=
  @ZMod.instField r ⟨hrp⟩

theorem fieldThree_finrank (hrp : r.Prime) (hK : Nat.card K = r ^ 2) :
    Module.finrank (ZMod r) K = 2 := by
  let _ := fieldThreePrimeField hrp
  have h := Module.natCard_eq_pow_finrank (K := ZMod r) (V := K)
  rw [hK, Nat.card_zmod] at h
  exact Nat.pow_right_injective hrp.two_le h.symm

theorem fieldThree_det (hrp : r.Prime) (hr3 : r = 3) (hK : Nat.card K = 9) {c : K}
    (hc4 : c ^ 4 = -1) : LinearMap.det (Algebra.lmul (ZMod r) K c) = -1 := by
  let _ := fieldThreePrimeField hrp
  rw [← Algebra.norm_apply]
  apply (algebraMap (ZMod r) K).injective
  rw [FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod, map_neg, map_one, hr3,
    show (9 - 1) / (3 - 1) = 4 by norm_num]
  exact hc4

end Prime

theorem twisted_E6_field_three_actual_central_cover_local_three_rank_four {G : Type} [Group G]
    [Finite G] (Y : Subgroup G)
    (hY : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 3 1) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      CFSG.Assembly.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
      CFSG.IsPLocal 2 (Subgroup.normalizer (Subgroup.zpowers u : Set G)) ∧
      4 ≤ localRank 3 G ∧ 4 ≤ CFSG.twoLocalOddRank G ∧ ¬CFSG.twoLocalOddRank G ≤ 3 := by
  classical
  obtain ⟨-, hmod⟩ := hY
  obtain ⟨K, _, _, hK, σ, hσ, φ, hφ, hker⟩ :=
    exists_surj_graphFixedRootGroup_of_model Nat.prime_three le_rfl hmod
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have hσ3 : ∀ c, σ c = c ^ 3 := fun c => by rw [hσ, pow_one]
  obtain ⟨⟨c, hc⟩, hrest⟩ := twisted_E6_field_three_native_four_dimensional_root_action K hK9 σ hσ3
  obtain ⟨hnC, hzC, hz2, ι, hιinj, hιn, hιz, -⟩ := hrest c hc
  obtain ⟨r, hr3⟩ : ∃ r : ℕ, r = 3 := ⟨3, rfl⟩
  have hrp : r.Prime := hr3 ▸ Nat.prime_three
  have : CharP K r :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hrp
      (by norm_num : 1 ≤ 2) (by rw [hK9, hr3]; norm_num)
  let _ : Algebra (ZMod r) K := ZMod.algebra K r
  have hc4 : (c : K) ^ 4 = -1 := by
    have h8 : (c : K) ^ 4 * (c : K) ^ 4 = 1 := by
      rw [← pow_add, show 4 + 4 = orderOf c by rw [hc], ← Units.val_pow_eq_pow_val,
        pow_orderOf_eq_one, Units.val_one]
    rcases mul_self_eq_one_iff.1 h8 with h | h
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one]))
        (pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hc]; norm_num) : c ^ 4 ≠ 1)
    · exact h
  have hne : (1 : K) ≠ -1 := fun h => by
    have h2 := (neg_one_eq_one_iff (R := K)).1 h.symm
    rw [ringChar.eq K r, hr3] at h2
    norm_num at h2
  have hinj : Function.Injective (algebraMap (ZMod r) K) := ZMod.castHom_injective K
  let ψ₀ : ZMod r →+* (⊥ : Subfield K) :=
    (algebraMap (ZMod r) K).codRestrict ⊥ fun a => by
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
      rw [map_intCast]
      exact intCast_mem _ n
  have hψ₀ : Function.Injective ψ₀ := fun a b h => hinj (congrArg Subtype.val h)
  let E : Multiplicative (ZMod r × ZMod r × K) →*
      Multiplicative ((⊥ : Subfield K) × (⊥ : Subfield K) × K) :=
    AddMonoidHom.toMultiplicative
      ((ψ₀.toAddMonoidHom).prodMap ((ψ₀.toAddMonoidHom).prodMap (AddMonoidHom.id K)))
  have hE : ∀ (a b : ZMod r) (v : K),
      E (Multiplicative.ofAdd (a, b, v)) = Multiplicative.ofAdd (ψ₀ a, ψ₀ b, v) :=
    fun a b v => rfl
  have hEinj : Function.Injective E := by
    intro x y h
    have h' := congrArg Multiplicative.toAdd h
    simp only [E, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd] at h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    exact Multiplicative.toAdd.injective
      (Prod.ext (hψ₀ h1) (Prod.ext (hψ₀ h3) (by simpa using h4)))
  set e := ι.comp E
  have he : Function.Injective e := hιinj.comp hEinj
  set jm := LinearMap.inl (ZMod r) (ZMod r) (ZMod r × K)
  set jp := (LinearMap.inr (ZMod r) (ZMod r) (ZMod r × K)).comp
    (LinearMap.inl (ZMod r) (ZMod r) K)
  have hjm : Function.Injective jm := LinearMap.inl_injective
  have hjp : Function.Injective jp := LinearMap.inr_injective.comp LinearMap.inl_injective
  set n : graphFixedRootGroup TwistTag.E6 K σ := ⟨fieldThreeN c, hnC⟩
  set z : graphFixedRootGroup TwistTag.E6 K σ := ⟨fieldThreeZ, hzC⟩
  have hn : ∀ v, n * e (Multiplicative.ofAdd v) * n⁻¹ =
      e (Multiplicative.ofAdd (fieldThreeSigma r (c : K) v)) := by
    rintro ⟨a, b, v⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, fieldThreeSigma_apply]
    change fieldThreeN c * (ι (E (Multiplicative.ofAdd (a, b, v))) : ModGL TwistTag.E6.tag K) *
        (fieldThreeN c)⁻¹ = (ι (E (Multiplicative.ofAdd (-a, b, (c : K) * v))) : _)
    rw [hE, hE, hιn, show ψ₀ (-a) = -ψ₀ a from map_neg ψ₀ a]
  have hzo : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hzD : ∀ v, Commute z (e (Multiplicative.ofAdd v)) := fun v => Subtype.ext (hιz _)
  set P := fieldThreePlaneEquiv r K
  have hres := fieldThreeSigma_restrict_add (r := r) (c : K) 0
  rw [zero_smul, add_zero, map_zero, add_zero] at hres
  have hdet : LinearMap.det ((fieldThreeSigma r (c : K)).restrict (fieldThreeSigma_mem _)) =
      -1 := by
    rw [hres, LinearMap.det_conj]
    exact fieldThree_det hrp hr3 hK9 hc4
  have hunit : ∀ t : K, t ≠ 0 → IsUnit
      ((P : K →ₗ[ZMod r] LinearMap.range (fieldThreePlane r K)) ∘ₗ Algebra.lmul (ZMod r) K t ∘ₗ
        (P.symm : LinearMap.range (fieldThreePlane r K) →ₗ[ZMod r] K)) := fun t ht => by
    have h1 : Function.Bijective (Algebra.lmul (ZMod r) K t) :=
      (Module.End.isUnit_iff _).1 (Algebra.lmul_isUnit_iff.2 (IsUnit.mk0 t ht))
    refine (Module.End.isUnit_iff _).2 ?_
    exact P.bijective.comp (h1.comp P.symm.bijective)
  have hTm : IsUnit ((fieldThreeSigma r (c : K)).restrict (fieldThreeSigma_mem _) - 1) := by
    rw [fieldThreeSigma_restrict_sub_one]
    exact hunit ((c : K) - 1) (sub_ne_zero.2 fun h => hne (by rw [← hc4, h, one_pow]))
  have hTp : IsUnit ((fieldThreeSigma r (c : K)).restrict (fieldThreeSigma_mem _) + 1) := by
    rw [fieldThreeSigma_restrict_add_one]
    exact hunit ((c : K) + 1) (fun h => hne (by
      rw [← hc4, eq_neg_of_add_eq_zero_left h]
      norm_num))
  obtain ⟨-, u, huY, hu2, A, hAle, hAel, hAcard, hloc, hrank⟩ :=
    CFSG.RankThree.CentralCover.four_dimensional_normalizer_actual_central_cover_local_rank Y φ
      hφ hker.le (hr := ⟨hrp⟩) (by rw [hr3]; norm_num) e he
      (by rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod, hK9, hr3]; norm_num)
      (LinearMap.range jm) (LinearMap.range jp) (LinearMap.range (fieldThreePlane r K))
      (by
        refine eq_top_iff.2 fun x _ => ?_
        obtain ⟨a, b, v⟩ := x
        have hx : ((a, b, v) : ZMod r × ZMod r × K) = jm a + jp b + fieldThreePlane r K v := by
          simp [jm, jp]
        rw [hx]
        exact Submodule.add_mem_sup (Submodule.add_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩) ⟨v, rfl⟩)
      (by
        refine ⟨Submodule.disjoint_def.2 fun x hx1 hx2 => ?_,
          Submodule.disjoint_def.2 fun x hx1 hx2 => ?_⟩
        · obtain ⟨a, rfl⟩ := hx1
          obtain ⟨y, ⟨b, rfl⟩, w, ⟨v, rfl⟩, hyw⟩ := Submodule.mem_sup.1 hx2
          have h1 : (0 : ZMod r) = a := by simpa [jm, jp] using congrArg Prod.fst hyw
          simp [jm, ← h1]
        · obtain ⟨b, rfl⟩ := hx1
          obtain ⟨v, hv⟩ := hx2
          have h1 : (0 : ZMod r) = b := by
            simpa [jp] using congrArg (fun x : ZMod r × ZMod r × K => x.2.1) hv
          simp [jp, ← h1])
      (by rw [LinearMap.finrank_range_of_inj hjm, CommSemiring.finrank_self])
      (by rw [LinearMap.finrank_range_of_inj hjp, CommSemiring.finrank_self])
      (by
        rw [LinearMap.finrank_range_of_inj fieldThreePlane_injective]
        exact fieldThree_finrank hrp (by rw [hK9, hr3]; norm_num))
      (fieldThreeSigma r (c : K))
      (by
        rintro _ ⟨a, rfl⟩
        simp [jm, fieldThreeSigma])
      (by
        rintro _ ⟨b, rfl⟩
        simp [jp, fieldThreeSigma])
      (fieldThreeSigma_mem _) hdet hTm hTp hn hzo hzD
  subst hr3
  have h3G : 3 ∣ Nat.card G :=
    (Dvd.intro_left _ (hAcard.symm.trans (by norm_num))).trans (Subgroup.card_subgroup_dvd_card A)
  have he4 : 4 ≤ CFSG.twoLocalOddRank G :=
    hrank.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num)
      h3G)
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := hloc
  exact ⟨u, huY, hu2, A, hAle, hAel, hAcard, ⟨Q, hQ1, hQ2, hQ3⟩, hrank, he4, by omega⟩

end CFSG.RankThree.Chevalley
