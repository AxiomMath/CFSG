module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem twConj_of_mem_C0 (σ : K ≃+* K) (c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    twConj K σ ⟨c, graphFixedRootGroup_le_twInndiag σ c.2⟩ = MulAut.conj c :=
  MulEquiv.ext fun h => Subtype.ext (by rw [coe_twConj]; rfl)

theorem twConj_mem_markID {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (w : twInndiagGroup K σ) :
    (MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))).symm
      (twConj K σ w) ∈ markIDImage (IsRoot TwistTag.E6.tag) K
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  set L := AlgebraicClosure K
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK2
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨b, hb, c, hc, hwbc⟩ := exists_decomp_of_mem_twInndiag hn hK hσ (L := L)
    (Fr := iterateFrobenius L 2 n) (fun c => by rw [iterateFrobenius_def]) w.2
  have hsplit : w = ⟨rootDiagUnit TwistTag.E6.tag b, rootDiagUnit_mem_twInndiag hb⟩ *
      ⟨c, graphFixedRootGroup_le_twInndiag σ hc⟩ := Subtype.ext hwbc
  have hN := rootDiagUnit_mem_normalizer_graphFixedRootGroup hb
  rw [hsplit, map_mul, map_mul, twConj_of_mem_C0 σ ⟨c, hc⟩]
  have hconj : (MulAut.congr (centerQuotEquivOfBot hZ)).symm (MulAut.conj ⟨c, hc⟩) =
      MulAut.conj ((centerQuotEquivOfBot hZ).symm ⟨c, hc⟩) := by
    rw [MulEquiv.symm_apply_eq, mulAut_congr_conj, MulEquiv.apply_symm_apply]
  rw [hconj]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨b, ?_, ?_, ?_⟩))
    (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
  · intro h
    have hm := (Subgroup.mem_normalizer_iff.1 hN (h : ModGL TwistTag.E6.tag K)).1 h.2
    exact ⟨⟨_, hm⟩, (markDiag_rel_iff b _ _).2 rfl⟩
  · intro h'
    have hm := (Subgroup.mem_normalizer_iff.1 (inv_mem hN) (h' : ModGL TwistTag.E6.tag K)).1
      h'.2
    rw [inv_inv] at hm
    refine ⟨⟨_, hm⟩, (markDiag_rel_iff b _ _).2 ?_⟩
    change (h' : ModGL TwistTag.E6.tag K) = rootDiagUnit TwistTag.E6.tag b *
      ((rootDiagUnit TwistTag.E6.tag b)⁻¹ * h' * rootDiagUnit TwistTag.E6.tag b) *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹
    group
  · intro h h' hrel
    rw [congr_symm_apply_mk hZ]
    congr 1
    apply Subtype.ext
    rw [coe_twConj]
    exact ((markDiag_rel_iff b _ _).1 hrel).symm

theorem ggRawFieldConj_C0_E6 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp2 : p ≠ 2) :
    GGRawFieldConj p (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      (markIDImage (IsRoot TwistTag.E6.tag) K (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  intro _ _ u _ f _ huf hpow
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  set e := centerQuotEquivOfBot hZ with he
  set Ψ := MulAut.congr e with hΨ
  have hmemI := twConj_mem_markID hn hK σ hσ
  set x := Ψ (u * f) with hx
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hpow, map_one]
  obtain ⟨-, -, -, -, -, hΔ, hfield, hNF, ⟨Θ, hΘ, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  obtain ⟨g, a, δ, hga⟩ := hNF x
  have hb : IsCompatE6 σ.toRingHom (compatDiag TwistTag.E6 σ.toRingHom a) := fun i =>
    compatDiag_perm a i
  set w : twInndiagGroup K σ := ⟨(g : ModGL TwistTag.E6.tag K) *
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom a),
    mul_mem (graphFixedRootGroup_le_twInndiag σ g.2) (rootDiagUnit_mem_twInndiag hb)⟩ with hw
  have hwx : twConj K σ w = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom a := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_twConj, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hΔ a h]
    simp only [hw]
    group
  have hxw : x = twConj K σ w * fieldActor σ δ := by rw [hga, hwx]
  have hΘx : Θ x = δ := hΘ x g a δ hga
  have hδp : δ ^ p = 1 := by rw [← hΘx, ← map_pow, hxp, map_one]
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    apply huf
    have h1 : u * f = Ψ.symm (twConj K σ w) := by
      rw [MulEquiv.eq_symm_apply, ← hx, hxw, fieldActor_one, mul_one]
    rw [h1]
    exact hmemI w
  have : Fact p.Prime := ⟨hp⟩
  have hδord : orderOf δ = p := orderOf_eq_prime hδp hδ1
  have hq3 : 3 ≤ 2 ^ n := by
    have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
    obtain ⟨-, -, -, -, hcardAut, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega) hK2
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
    have hp2n : p ∣ 2 * n := by
      rw [← hδord, ← hcardAut]
      exact orderOf_dvd_natCard δ
    have hpn : p ∣ n := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left hp2n
    have hn3 : 3 ≤ n := le_trans (by have := hp.two_le; omega) (Nat.le_of_dvd (by omega) hpn)
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
  set X := MulAut.conj w * twInndiagFieldAut K σ δ with hXdef
  have hX1 : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (X ⟨h, graphFixedRootGroup_le_twInndiag σ h.2⟩ : ModGL TwistTag.E6.tag K) =
        (x h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hxw]
    rfl
  have hXk : ∀ (k : ℕ) (h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ((X ^ k) ⟨h, graphFixedRootGroup_le_twInndiag σ h.2⟩ : ModGL TwistTag.E6.tag K) =
        ((x ^ k) h : ModGL TwistTag.E6.tag K) := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply]
      have e1 : (X ^ k) ⟨h, graphFixedRootGroup_le_twInndiag σ h.2⟩ =
          ⟨((x ^ k) h : ModGL TwistTag.E6.tag K),
            graphFixedRootGroup_le_twInndiag σ ((x ^ k) h).2⟩ := Subtype.ext (ih h)
      rw [e1]
      exact hX1 _
  set N := ((List.range p).map fun i => (twInndiagFieldAut K σ δ ^ i) w).prod with hN
  have hpow' : X ^ p = MulAut.conj N * twInndiagFieldAut K σ (δ ^ p) := by
    rw [CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, map_pow]
  have hN1 : N = 1 := by
    refine Subtype.ext (eq_one_of_commute_C0 hn hK hσ hq3 N.2 fun c hc => ?_)
    have e1 := hXk p ⟨c, hc⟩
    rw [hxp, MulAut.one_apply, hpow', hδp, map_one, mul_one, MulAut.conj_apply] at e1
    change (N : ModGL TwistTag.E6.tag K) * c * (N : ModGL TwistTag.E6.tag K)⁻¹ = c at e1
    calc (N : ModGL TwistTag.E6.tag K) * c = ((N : ModGL TwistTag.E6.tag K) * c *
          (N : ModGL TwistTag.E6.tag K)⁻¹) * (N : ModGL TwistTag.E6.tag K) := by group
      _ = c * N := by rw [e1]
  have hXp : X ^ p = 1 := by rw [hpow', hδp, hN1, map_one, map_one, mul_one]
  obtain ⟨v, hv⟩ := exists_conj_eq_twInndiagFieldAut hn hK σ hσ hp hp2 δ hδord w hXp
  refine ⟨Ψ.symm (fieldActor σ δ), ⟨δ, fun h h' hrel => ?_⟩, Ψ.symm (twConj K σ v⁻¹),
    hmemI v⁻¹, ?_, ?_⟩
  ·
    rw [hΨ, congr_symm_apply_mk hZ]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    rw [hfield δ h]
    exact hrel.symm
  ·
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ fun h1 => hδ1 ?_
    · rw [← fieldActorHom_apply (t := TwistTag.E6), ← map_pow, hδp, map_one]
    · have h2 := hΘ (fieldActor σ δ) 1 1 δ (by rw [map_one, map_one, one_mul, one_mul])
      rw [h1, map_one] at h2
      exact h2.symm
  ·
    have hX' : X = MulAut.conj v⁻¹ * twInndiagFieldAut K σ δ * MulAut.conj v := by
      rw [map_inv]
      have e0 : X = (MulAut.conj v)⁻¹ * (MulAut.conj v * X * (MulAut.conj v)⁻¹) *
          MulAut.conj v := by group
      rw [e0, hv]
    have key : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (x h : ModGL TwistTag.E6.tag K) = (v : ModGL TwistTag.E6.tag K)⁻¹ *
          Units.map (entrywiseHom δ.toRingHom) ((v : ModGL TwistTag.E6.tag K) *
            (h : ModGL TwistTag.E6.tag K) * (v : ModGL TwistTag.E6.tag K)⁻¹) *
              (v : ModGL TwistTag.E6.tag K) := by
      intro h
      rw [← hX1 h, hX']
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_twInndiagFieldAut, inv_inv]
    apply Ψ.injective
    have hR : Ψ (Ψ.symm (twConj K σ v⁻¹) * Ψ.symm (fieldActor σ δ) *
        (Ψ.symm (twConj K σ v⁻¹))⁻¹) = (twConj K σ v)⁻¹ * fieldActor σ δ * twConj K σ v := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
    rw [hR, ← hx, ← map_inv]
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [key h]
    simp only [MulAut.mul_apply, coe_twConj, coe_fieldActor, Subgroup.coe_inv, inv_inv]

end RecipeExcLang

end CFSG.StandardType
