module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4ShortFix
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofOut
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.CGT.Timmesfeld75 Matrix
open scoped MatrixGroups

namespace Res148BD4

section Certs


theorem nonempty_sl2_equiv_short {K : Type} [Field K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    Nonempty (SL(2, K) ≃* Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) := by
  have hinj := orbitRankOneHom_injective_D4 hσ Sec11.KS11Lie4Proof.d4Outer
  have hle := range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    Sec11.KS11Lie4Proof.d4Outer
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.D4 K σ.toRingHom Sec11.KS11Lie4Proof.d4Outer := by
    have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
      rw [← ringEquiv_pow_three_apply, hσ]
      rfl
    intro c
    rw [show Sec11.KS11Lie4Proof.d4Outer = ⟨0, by decide⟩ from rfl, orbitField_D4_zero_eq_top σ h3]
    exact Subfield.mem_top c
  let r : K ≃+* orbitField TwistTag.D4 K σ.toRingHom Sec11.KS11Lie4Proof.d4Outer :=
    { toFun := fun c => ⟨c, hmem c⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let sr : SL(2, K) ≃* SL2 (orbitField TwistTag.D4 K σ.toRingHom Sec11.KS11Lie4Proof.d4Outer) :=
    { toFun := SpecialLinearGroup.map (r : K →+* _)
      invFun := SpecialLinearGroup.map (r.symm : _ →+* K)
      left_inv := fun g => by
        ext i j
        rfl
      right_inv := fun g => by
        ext i j
        rfl
      map_mul' := map_mul _ }
  exact ⟨sr.trans ((MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hle).symm)⟩

theorem eq_bot_of_le_short_fixed {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ3 : β ^ 3 = 1)
    (hβin : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hβS : ∀ x ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom,
      β x ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    {N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hN : N ≤ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hNβ : ∀ x ∈ N, β x = x)
    (hNn : ∀ y ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, β y = y → ∀ x ∈ N,
      y * x * y⁻¹ ∈ N)
    (hN3 : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [ringEquiv_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have h3q : ¬ 3 ∣ 2 ^ n := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨eK⟩ := nonempty_sl2_equiv_short hσ3
  set S := Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom with hS
  have hmapS : S.map β.toMonoidHom = S := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hβS x hx
    · rw [Subgroup.card_map_of_injective β.injective]
  let βS : S ≃* S := (β.subgroupMap S).trans (MulEquiv.subgroupCongr hmapS)
  have hβSapp : ∀ x : S, ((βS x : S) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = β x :=
    fun x => rfl
  let φ : SL(2, K) ≃* SL(2, K) := eK.trans (βS.trans eK.symm)
  have hφ : ∀ x, ((eK (φ x) : S) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      β (eK x) := by
    intro x
    change ((eK (eK.symm (βS (eK x))) : S) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = _
    rw [MulEquiv.apply_symm_apply, hβSapp]
  obtain ⟨g, τ, hgτ⟩ := exists_eq_conj_sl2FieldAut φ
  have hφ3 : ∀ x, φ (φ (φ x)) = x := by
    intro x
    apply eK.injective
    apply Subtype.ext
    rw [hφ, hφ, hφ, ← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hβ3, MulAut.one_apply]
  set M := g * sl2FieldAut τ g * sl2FieldAut τ (sl2FieldAut τ g) with hM
  have hφ3' : ∀ x, M * sl2FieldAut ((τ.trans τ).trans τ) x * M⁻¹ = x := by
    intro x
    calc M * sl2FieldAut ((τ.trans τ).trans τ) x * M⁻¹ =
        g * sl2FieldAut τ (g * sl2FieldAut τ (g * sl2FieldAut τ x * g⁻¹) * g⁻¹) * g⁻¹ := by
          rw [sl2FieldAut_trans, sl2FieldAut_trans]
          simp only [hM, MulEquiv.trans_apply, map_mul, map_inv]
          group
      _ = φ (φ (φ x)) := by rw [hgτ, hgτ, hgτ]
      _ = x := hφ3 x
  have hτ3 : (τ.trans τ).trans τ = RingEquiv.refl K := eq_refl_of_conj_sl2FieldAut hφ3'
  have hM1 : M = 1 := by
    refine sl2_eq_one_of_commute fun x => ?_
    have h := hφ3' x
    rw [hτ3, sl2FieldAut_refl, MulEquiv.refl_apply] at h
    calc M * x = M * x * M⁻¹ * M := by group
      _ = x * M := by rw [h]
  by_cases hτ1 : τ = RingEquiv.refl K
  ·
    exfalso
    have hφg : ∀ x, φ x = g * x * g⁻¹ := by
      intro x
      rw [hgτ, hτ1, sl2FieldAut_refl, MulEquiv.refl_apply]
    have hg3 : g ^ 3 = 1 := by
      have h := hM1
      rw [hM, hτ1, sl2FieldAut_refl, MulEquiv.refl_apply, MulEquiv.refl_apply] at h
      rw [pow_three, ← mul_assoc]
      exact h
    set s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ((eK g : S) :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) with hsdef
    have hβs : β s = s := by
      rw [hsdef, ← hφ, hφg]
      congr 2
      group
    have hβy : ∀ y ∈ S, β y = s * y * s⁻¹ := by
      intro y hy
      have hy' : y = ((eK (eK.symm ⟨y, hy⟩) : S) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
        by rw [MulEquiv.apply_symm_apply]
      rw [hy', ← hφ, hφg, map_mul, map_mul, map_inv]
      rfl
    have hs3 : s ^ 3 = 1 := by
      rw [hsdef, ← Subgroup.coe_pow, ← map_pow, hg3, map_one, Subgroup.coe_one]
    set β' := β * (MulAut.conj s)⁻¹ with hβ'
    have hβ'fix : ∀ y ∈ S, β' y = y := by
      intro y hy
      rw [hβ', MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply, map_mul, map_mul,
        map_inv, hβs, hβy y hy]
      group
    have hcomm : Commute β (MulAut.conj s) := by
      have h : β * MulAut.conj s * β⁻¹ = MulAut.conj s := by
        ext m
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
          MulEquiv.apply_symm_apply, hβs]
      calc β * MulAut.conj s = β * MulAut.conj s * β⁻¹ * β := by group
        _ = MulAut.conj s * β := by rw [h]
    have hβ'3 : β' ^ 3 = 1 := by
      rw [hβ', (hcomm.inv_right).mul_pow, hβ3, one_mul, inv_pow, ← map_pow, hs3, map_one, inv_one]
    have hin := Sec11.KS11Lie5Proof.d4ShortOut_holds K (2 ^ n) σ hK hσ h3q β' ⟨1, by
      rw [pow_one]; exact hβ'3⟩ hβ'fix
    apply hβin
    obtain ⟨t, ht⟩ := hin
    refine ⟨t * s, ?_⟩
    rw [map_mul, ht, hβ']
    group
  ·
    have hτ3' : τ ^ 3 = 1 := by
      ext c
      rw [ringEquiv_pow_three_apply]
      have := congrArg (fun ρ : K ≃+* K => ρ c) hτ3
      exact this
    have hτne : τ ≠ 1 := hτ1
    have hτord : orderOf τ = 3 := orderOf_eq_prime hτ3' hτne
    obtain ⟨-, -, -, hcyc, -⟩ := even_triality_exact_automorphism_normal_form hn1 K hK σ hσ
    haveI : IsCyclic (K ≃+* K) := hcyc
    have hσord := Sec8.Item8ModelProof.orderOf_sigma hn1 hK hσ
    have hcardσ : Nat.card (autFixedSubfield σ) = 2 ^ n := KFacts.card_fixSubfield_of_cube hn1 hK hσ
    have hfix : Nat.card (autFixedSubfield τ) = 2 ^ n := by
      rcases Sec8.Item8ModelProof.eq_or_eq_inv_of_pow_three hσord hτ3' hτne with rfl | rfl
      · exact hcardσ
      · rw [← hcardσ]
        refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
        rw [mem_autFixedSubfield, mem_autFixedSubfield]
        change σ.symm c = c ↔ σ c = c
        rw [RingEquiv.symm_apply_eq]
        exact eq_comm
    have h4 : 4 ≤ Nat.card (autFixedSubfield τ) := by
      rw [hfix]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    set f : SL(2, K) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      S.subtype.comp eK.toMonoidHom with hf
    have hfinj : Function.Injective f := fun x y h => eK.injective (Subtype.ext h)
    have hfr : f.range = S := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (eK x).2
      · intro hy
        refine ⟨eK.symm ⟨y, hy⟩, ?_⟩
        change ((eK (eK.symm ⟨y, hy⟩) : S) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = y
        rw [MulEquiv.apply_symm_apply]
    set MK := N.comap f with hMK
    have hmapMK : MK.map f = N := by
      rw [hMK, Subgroup.map_comap_eq, hfr, inf_eq_right.2 hN]
    have hfapp : ∀ x, f x = ((eK x : S) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      fun x => rfl
    have hφfix : ∀ x, φ x = x ↔ β (f x) = f x := by
      intro x
      rw [hfapp, ← hφ]
      constructor
      · intro h
        rw [h]
      · intro h
        exact eK.injective (Subtype.ext h)
    have hgM : g * sl2FieldAut τ g * sl2FieldAut τ (sl2FieldAut τ g) = 1 := hM1
    have hMKbot := eq_bot_of_le_fixed hτord h4 hgM MK
      (fun x hx => by
        rw [← hgτ]
        exact (hφfix x).2 (hNβ _ hx))
      (fun y hy x hx => by
        have hy' : φ y = y := by rw [hgτ]; exact hy
        change f (y * x * y⁻¹) ∈ N
        rw [map_mul, map_mul, map_inv]
        exact hNn (f y) (by rw [hfapp]; exact (eK y).2) ((hφfix y).1 hy') (f x) hx)
      (by
        rw [← Subgroup.card_map_of_injective hfinj, hmapMK]
        exact hN3)
    rw [← hmapMK, hMKbot, Subgroup.map_bot]

end Certs

end Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
