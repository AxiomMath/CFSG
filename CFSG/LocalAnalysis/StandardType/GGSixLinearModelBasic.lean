module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelOmega
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinModel

section Bstar

variable {G : Type} [Group G]

theorem card_le_of_bstarUniqueIn [Finite G] {p : ℕ} (hp : p.Prime) {M Bs E : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsM : Bs ≤ M) (hU : GGBstarUniqueIn p M Bs)
    (hE : IsElemAbelian p E) (hEM : E ≤ M) : Nat.card E ≤ Nat.card Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : ∀ {X : Subgroup G}, IsElemAbelian p X → IsPGroup p X := fun hX b =>
    ⟨1, Subtype.ext (by simpa using hX.2 b b.2)⟩
  obtain ⟨Q, hQ⟩ := ((hpg hBs).comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  obtain ⟨R, hR⟩ := ((hpg hE).comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M R Q
  have hPM : (Q : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hPp : IsPGroup p ((Q : Subgroup ↥M).map M.subtype) := Q.isPGroup'.map M.subtype
  have hBsP : Bs ≤ (Q : Subgroup ↥M).map M.subtype := fun b hb => ⟨⟨b, hBsM hb⟩, hQ hb, rfl⟩
  have hmaxM : ∀ S : Subgroup G, S ≤ M → IsPGroup p S →
      (Q : Subgroup ↥M).map M.subtype ≤ S → S = (Q : Subgroup ↥M).map M.subtype := by
    intro S hSM hSp hPS
    have hSp' : IsPGroup p (S.subgroupOf M) :=
      hSp.comap_of_injective M.subtype M.subtype_injective
    have hQS : (Q : Subgroup ↥M) ≤ S.subgroupOf M := fun q hq => hPS ⟨q, hq, rfl⟩
    have hSQ := Q.is_maximal' hSp' hQS
    rw [← Subgroup.map_subgroupOf_eq_of_le hSM, hSQ]
  have hEP : E.map (MulAut.conj (g : G)).toMonoidHom ≤ (Q : Subgroup ↥M).map M.subtype := by
    rintro _ ⟨e, he, rfl⟩
    have hmem : MulAut.conj g (⟨e, hEM he⟩ : M) ∈ ((g • R : Sylow p M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR (show (⟨e, hEM he⟩ : M) ∈
        E.comap M.subtype from he))
    rw [hg] at hmem
    exact ⟨_, hmem, rfl⟩
  have h := (hU _ hPM hPp hBsP hmaxM _ hEP (isElemAbelian_map_hom hE _)).1
  rwa [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective] at h

end Bstar

theorem sq_dvd_two_pow_sub_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ f) (hf : 1 ≤ f)
    (hdvd : p ∣ 2 ^ f - 1) : p ^ 2 ∣ 2 ^ f - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, rfl⟩ := hpf
  have hg : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · rw [h, mul_zero] at hf
      omega
    · exact h
  set r := 2 ^ g with hrdef
  have hr1 : 1 < r := Nat.one_lt_two_pow (by omega)
  have hrp : 2 ^ (p * g) = r ^ p := by rw [hrdef, ← pow_mul, mul_comm]
  rw [hrp] at hdvd ⊢
  have hrp1 : 1 ≤ r ^ p := Nat.one_le_pow _ _ (by omega)
  have hr : p ∣ r - 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
    rw [Nat.cast_sub hrp1, Nat.cast_pow, Nat.cast_one, ZMod.pow_card, sub_eq_zero] at hdvd
    rw [Nat.cast_sub hr1.le, Nat.cast_one, hdvd, sub_self]
  have hnr : ¬ p ∣ r := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hv := padicValNat.pow_sub_pow (x := r) (y := 1) (hp.odd_of_ne_two hp2) hr1 hr hnr
    hp.ne_zero
  rw [one_pow] at hv
  have hne : r ^ p - 1 ≠ 0 := by
    have : 1 < r ^ p := Nat.one_lt_pow hp.ne_zero hr1
    omega
  rw [padicValNat_dvd_iff_le hne, hv, padicValNat_self]
  have : 1 ≤ padicValNat p (r - 1) := one_le_padicValNat_of_dvd (by omega) hr
  omega

variable {F : Type} [Field F]

theorem exists_pow_eq_of_sq_dvd [Finite F] {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ Nat.card Fˣ)
    {ω : Fˣ} (hω : ω ^ p = 1) : ∃ ζ : Fˣ, ζ ^ p = ω := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  obtain ⟨k, hk⟩ := h
  have hN : 0 < Nat.card Fˣ := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hζ₀ : orderOf (γ ^ k) = p ^ 2 := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hγ, hk]; exact dvd_mul_left _ _), hγ, hk,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have hζ₁ : orderOf ((γ ^ k) ^ p) = p := by
    rw [orderOf_pow_of_dvd hp.ne_zero (by rw [hζ₀]; exact dvd_pow_self p two_ne_zero), hζ₀,
      pow_two, Nat.mul_div_cancel _ hp.pos]
  have hprim : IsPrimitiveRoot (((γ ^ k) ^ p : Fˣ) : F) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζ₁)
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (ω : F))
    (by rw [← Units.val_pow_eq_pow_val, hω, Units.val_one])
  refine ⟨(γ ^ k) ^ i, Units.ext ?_⟩
  rw [← hi, ← Units.val_pow_eq_pow_val]
  congr 1
  exact pow_right_comm _ _ _

theorem det_eq_of_pow_eq_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = p) {M : Matrix ι ι F} {c : F}
    (hM : M ^ p = Matrix.scalar ι c) (hc : ∀ b : F, b ^ p ≠ c) : M.det = c := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hι ▸ hp.pos)
  have hirr : Irreducible (X ^ p - C c) := X_pow_sub_C_irreducible_of_prime hp hc
  have hmon : (X ^ p - C c : F[X]).Monic := monic_X_pow_sub_C c hp.ne_zero
  have hann : aeval M (X ^ p - C c) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hM, Matrix.algebraMap_eq_diagonal,
      Matrix.scalar_apply, sub_eq_zero]
    rfl
  have hmin : minpoly F M = X ^ p - C c := by
    have hdvd := minpoly.dvd F M hann
    rcases hirr.dvd_iff.mp hdvd with hu | ha
    · exact absurd hu (minpoly.not_isUnit F M)
    · exact Polynomial.eq_of_monic_of_associated (minpoly.monic (Matrix.isIntegral M)) hmon ha.symm
  have hchar : M.charpoly = X ^ p - C c := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic M)
      (hmin ▸ Matrix.minpoly_dvd_charpoly M) ?_
    rw [Matrix.charpoly_natDegree_eq_dim, hι, natDegree_X_pow_sub_C]
  rw [Matrix.det_eq_sign_charpoly_coeff, hchar, hι]
  simp [coeff_X_pow, hp.ne_zero.symm, (hp.odd_of_ne_two hp2).neg_one_pow]


theorem eq_one_of_pow_eq_one_of_not_dvd {f p : ℕ} (hf : f ≠ 0) (hp : p.Prime) (hpf : ¬ p ∣ f)
    {σ : GaloisField 2 f ≃+* GaloisField 2 f} (hσ : σ ^ p = 1) : σ = 1 := by
  have hcomm : ∀ (τ : GaloisField 2 f ≃+* GaloisField 2 f) (x : ZMod 2),
      τ (algebraMap (ZMod 2) (GaloisField 2 f) x) = algebraMap (ZMod 2) (GaloisField 2 f) x :=
    fun τ x => congrArg (fun φ : ZMod 2 →+* GaloisField 2 f => φ x)
      (RingHom.ext_zmod (τ.toRingHom.comp (algebraMap (ZMod 2) (GaloisField 2 f)))
        (algebraMap (ZMod 2) (GaloisField 2 f)))
  let ι : (GaloisField 2 f ≃+* GaloisField 2 f) →*
      (GaloisField 2 f ≃ₐ[ZMod 2] GaloisField 2 f) :=
    { toFun := fun τ => AlgEquiv.ofRingEquiv (hcomm τ)
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  have hι : Function.Injective ι := fun a b h =>
    RingEquiv.ext fun x => congrArg (fun φ : GaloisField 2 f ≃ₐ[ZMod 2] GaloisField 2 f => φ x) h
  have hcard : Nat.card (GaloisField 2 f ≃ₐ[ZMod 2] GaloisField 2 f) = f := by
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank 2 hf]
  have hdvd1 : orderOf σ ∣ f := by
    have h := orderOf_dvd_natCard (ι σ)
    rwa [hcard, orderOf_injective ι hι σ] at h
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hσ) with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h1 ▸ hdvd1) hpf

variable {G : Type*} [Group G]

theorem exists_mem_ggInducedPairs_of_pow_eq_one [Finite F] [CharP F 2] {m : ℕ} (hm : 2 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : ∀ σ : F ≃+* F, σ ^ p = 1 → σ = 1)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {y : G}
    (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyp : y ^ p = 1) :
    ∃ A : GL (Fin (m + 1)) F, (y, A) ∈ LinFusion.ggInducedPairs ψ := by
  set N := Subgroup.normalizer (ψ.range : Set G)
  set φN := ψ.range.normalizerMonoidHom
  set Θ := AutPSL.projEquiv (m := m) (K := F) hker hC
  set χ : N →* MulAut (projectiveSL (m + 1) F) := (MulAut.congr Θ).symm.toMonoidHom.comp φN
  set α := χ ⟨y, hy⟩ with hαdef
  have hαp : α ^ p = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨y, hy⟩ : N) ^ p = 1 := Subtype.ext (by simpa using hyp)
    rw [this, map_one]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := m + 1) (by omega)).2 α
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero (n := m + 1) (by omega)
    (hp.odd_of_ne_two hp2) hε
    (by rw [← hαeq]; exact hαp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hI := AutPSL.inndiag_normal (n := m + 1) (K := F) (by omega)
  have hσp : σ ^ p = 1 := by
    have h1 : (QuotientGroup.mk α : MulAut (projectiveSL (m + 1) F) ⧸ AutPSL.inndiag) =
        QuotientGroup.mk (fieldAut (m + 1) F σ) := by
      rw [hαeq, QuotientGroup.eq]
      have := hI.conj_mem _ (inv_mem (⟨A, rfl⟩ : conjAut (m + 1) F A ∈ AutPSL.inndiag))
        (fieldAut (m + 1) F σ)⁻¹
      convert this using 1
      group
    have h2 : (QuotientGroup.mk (fieldAut (m + 1) F (σ ^ p)) :
        MulAut (projectiveSL (m + 1) F) ⧸ AutPSL.inndiag) = 1 := by
      rw [map_pow, QuotientGroup.mk_pow, ← h1, ← QuotientGroup.mk_pow, hαp, QuotientGroup.mk_one]
    exact AutPSL.eq_one_of_fieldAut_mem (by omega) ((QuotientGroup.eq_one_iff _).mp h2)
  rw [hσ σ hσp, map_one, mul_one] at hαeq
  refine ⟨A, fun u => ?_⟩
  have h2 : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F A u =
      InnerDiagA.conjSL A u := Subtype.ext (by rw [coe_slConjugation, InnerDiagA.coe_conjSL])
  have key : Θ.symm (φN ⟨y, hy⟩ (Θ (proj (m + 1) F u))) =
      proj (m + 1) F (InnerDiagA.conjSL A u) := by
    rw [← h2, ← conjAut_proj, ← hαeq]
    rfl
  rw [MulEquiv.symm_apply_eq] at key
  exact congrArg Subtype.val key

end LinModel

end CFSG.StandardType
