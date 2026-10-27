module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSubspaceCount
import CFSG.Timmesfeld.Transvection.AssembleModelSU
import CFSG.Timmesfeld.Transvection.ModelSUGeometry
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOrthogonality

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace SUTrans

section Bridge

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {K : Type*} [Group K]
  {m : ℕ} {Φ : SU σ m →* K}
include hσ

theorem commutator_map_eq_bot_iff [CharP F 2] (hker : Φ.ker ≤ Subgroup.center (SU σ m))
    {v w : Fin m → F} {T T' : Subgroup (SU σ m)} (hT : IsUTransGroup σ v T)
    (hT' : IsUTransGroup σ w T') (hv : v ≠ 0) (hvv : uForm σ v v = 0)
    (hww : uForm σ w w = 0) :
    ⁅T.map Φ, T'.map Φ⁆ = ⊥ ↔ uForm σ v w = 0 := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  rw [← commuting_iff_commutator_eq_bot]
  refine ⟨fun hc => ?_, fun h => ModelRank.commuting_map Φ (hT.commuting hσ hT' h)⟩
  rcases hT.uForm_eq_zero_of_center hσ one_ne_zero h1 hT' hv hvv hww
    (ModelRank.commutator_mem_center hker hc) with h | ⟨l, rfl⟩
  · exact h
  · rw [uForm_smul_right, hvv, mul_zero]

theorem map_eq_map_iff [CharP F 2] (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
    (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {v w : Fin m → F} {T T' : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ v T) (hT' : IsUTransGroup σ w T') (hv : v ≠ 0) (hw : w ≠ 0)
    (hvv : uForm σ v v = 0) (hww : uForm σ w w = 0) :
    T.map Φ = T'.map Φ ↔ ∃ l : F, w = l • v := by
  refine ⟨fun he => ?_, ?_⟩
  · by_contra hprop
    push Not at hprop
    have hvw : uForm σ v w = 0 := (commutator_map_eq_bot_iff hσ hker hT hT' hv hvv hww).1 (by
      rw [← he, ← commuting_iff_commutator_eq_bot]
      exact ModelRank.commuting_map Φ (hT.commuting hσ hT hvv))
    obtain ⟨z, hzz, hvz, hwz⟩ :=
      ModelRank.exists_isotropic_perp_not_perp hσ htr hv hvv hww hvw hprop
    have hz : z ≠ 0 := by
      rintro rfl
      exact hvz (uForm_zero_right v)
    obtain ⟨Tz, hTz⟩ := ModelRank.exists_isUTransGroup hσ hzz
    have hzv := (commutator_map_eq_bot_iff hσ hker hTz hT hz hzz hvv).1 (by
      rw [he]
      exact (commutator_map_eq_bot_iff hσ hker hTz hT' hz hzz hww).2 (uForm_eq_zero_comm hσ hwz))
    exact hvz (uForm_eq_zero_comm hσ hzv)
  · rintro ⟨l, rfl⟩
    have hl : l ≠ 0 := by
      rintro rfl
      exact hw (zero_smul F v)
    rw [(IsUTransGroup.of_smul hσ hl hT').eq hT]

theorem exists_eq_map_of_mem (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    {U : Subgroup K} (hU : U ∈ Δ) :
    ∃ (v : Fin m → F) (T : Subgroup (SU σ m)), v ≠ 0 ∧ uForm σ v v = 0 ∧
      IsUTransGroup σ v T ∧ U = T.map Φ := by
  obtain ⟨x, rfl⟩ := (hΔ U).1 hU
  set e : Fin m → F := Pi.single (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) 1
  exact ⟨suMat σ m x *ᵥ e, _, suMat_mulVec_ne_zero σ x (single_one_ne_zero _),
    (uForm_mulVec σ x e e).trans (uForm_single_self (lowIdx_ne_rev _ _)),
    (ModelRank.isUTransGroup_rootGroup_unitaryLongRoot hσ hm).conjSub x, rfl⟩

theorem map_mem [CharP F 2] (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (hm : 2 ≤ m)
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    {v : Fin m → F} {T : Subgroup (SU σ m)} (hv : v ≠ 0) (hvv : uForm σ v v = 0)
    (hT : IsUTransGroup σ v T) : T.map Φ ∈ Δ := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  set e : Fin m → F := Pi.single (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) 1
  have hR : IsUTransGroup σ e (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) :=
    ModelRank.isUTransGroup_rootGroup_unitaryLongRoot hσ hm
  obtain ⟨g, l, hl, hg, -⟩ := ModelRank.exists_suMat_mulVec_eq_smul_of_perp hσ htr one_ne_zero h1
    (j := 0) (w := e) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (single_one_ne_zero _) hv
    (uForm_single_self (lowIdx_ne_rev _ _)) hvv
  have hTg : IsUTransGroup σ v (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) g) :=
    IsUTransGroup.of_smul hσ hl (by rw [← hg]; exact hR.conjSub g)
  exact (hΔ _).2 ⟨g, by rw [hTg.eq hT]⟩

theorem exists_isoLinesEquiv [CharP F 2] (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
    (hker : Φ.ker ≤ Subgroup.center (SU σ m)) (hm : 2 ≤ m) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map Φ)
    {τ : F →+* F} {B : (Fin m → F) →ₛₗ[τ] (Fin m → F) →ₗ[F] F}
    (hB : ∀ x y, B x y = uForm σ x y) :
    ∃ e : TotIsoSubspaces B 1 ≃ Δ, ∀ L, ∃ (v : Fin m → F) (T : Subgroup (SU σ m)), v ≠ 0 ∧
      uForm σ v v = 0 ∧ L.1 = F ∙ v ∧ IsUTransGroup σ v T ∧ (e L : Subgroup K) = T.map Φ := by
  have hvec : ∀ L : TotIsoSubspaces B 1,
      ∃ v : Fin m → F, v ≠ 0 ∧ uForm σ v v = 0 ∧ L.1 = F ∙ v := by
    intro L
    obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L.1) fun h0 => by
      have h := L.2.1
      rw [h0, finrank_bot] at h
      exact zero_ne_one h
    exact ⟨v, hv0, (hB v v).symm.trans (L.2.2 v hvL v hvL),
      eq_span_singleton_of_mem_of_finrank_eq_one L.2.1 hvL hv0⟩
  choose vec hvec0 hvecI hvecL using hvec
  choose grp hgrp using fun L => ModelRank.exists_isUTransGroup hσ (hvecI L)
  let ψ : TotIsoSubspaces B 1 → Δ := fun L =>
    ⟨(grp L).map Φ, map_mem hσ htr hm hΔ (hvec0 L) (hvecI L) (hgrp L)⟩
  have hinj : Function.Injective ψ := by
    intro L L' hLL'
    obtain ⟨l, hl⟩ := (map_eq_map_iff hσ htr hker (hgrp L) (hgrp L') (hvec0 L) (hvec0 L')
      (hvecI L) (hvecI L')).1 (congrArg Subtype.val hLL')
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hvec0 L' (by rw [hl, zero_smul])
    refine Subtype.ext ?_
    rw [hvecL L, hvecL L', hl, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hl0)]
  have hsurj : Function.Surjective ψ := by
    rintro ⟨U, hU⟩
    obtain ⟨v, T, hv, hvv, hT, rfl⟩ := exists_eq_map_of_mem hσ hm hΔ hU
    let L : TotIsoSubspaces B 1 := ⟨F ∙ v, finrank_span_singleton hv, fun x hx y hy => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [hB, uForm_smul_left, uForm_smul_right, hvv, mul_zero, mul_zero]⟩
    have hmem : vec L ∈ F ∙ v := by
      have h := Submodule.mem_span_singleton_self (R := F) (vec L)
      rw [← hvecL L] at h
      exact h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    exact ⟨L, Subtype.ext ((map_eq_map_iff hσ htr hker hT (hgrp L) hv (hvec0 L) hvv
      (hvecI L)).2 ⟨c, hc.symm⟩).symm⟩
  exact ⟨Equiv.ofBijective ψ ⟨hinj, hsurj⟩,
    fun L => ⟨vec L, grp L, hvec0 L, hvecI L, hvecL L, hgrp L, rfl⟩⟩

end Bridge

section Form

variable {f : ℕ}

private theorem fieldData (hf : 1 ≤ f) : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
  ⟨Nat.prime_two, hf, GaloisField.card 2 (2 * f) (by omega)⟩

private theorem gramForm_antidiag_apply (hf : 1 ≤ f) {m : ℕ}
    (x y : Fin m → GaloisField 2 (2 * f)) :
    gramForm (fieldData hf) (antidiag m) x y =
      uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) x y := by
  rw [gramForm_apply, uForm]
  congr 1

private theorem antidiag_mul_antidiag {F : Type*} [Field F] (m : ℕ) :
    (antidiag m : Matrix (Fin m) (Fin m) F) * antidiag m = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · by_cases h : i = j
    · subst h
      simp [antidiag]
    · have h' : j ≠ Fin.rev (Fin.rev i) := by
        rw [Fin.rev_rev]
        exact Ne.symm h
      simp [antidiag, h', Matrix.one_apply_ne h, Ne.symm h]
  · intro b _ hb
    simp [antidiag, hb]
  · simp

private theorem gramForm_antidiag_isSymm (hf : 1 ≤ f) (m : ℕ) :
    (gramForm (fieldData hf)
      (antidiag m : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * f)))).IsSymm := by
  refine gramForm_isSymm _ ?_
  ext i j
  have hiff : i = Fin.rev j ↔ j = Fin.rev i :=
    ⟨fun e => by rw [e, Fin.rev_rev], fun e => by rw [e, Fin.rev_rev]⟩
  simp only [antidiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, hiff]
  split_ifs <;> simp

private theorem gramForm_antidiag_separatingLeft (hf : 1 ≤ f) (m : ℕ) :
    (gramForm (fieldData hf)
      (antidiag m : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * f)))).SeparatingLeft :=
  gramForm_separatingLeft _ fun h0 => by
    have h := congrArg det (antidiag_mul_antidiag (F := GaloisField 2 (2 * f)) m)
    rw [det_mul, h0, zero_mul, det_one] at h
    exact zero_ne_one h

end Form

theorem strictMono_isoPointCount {q : ℤ} (hq : 2 ≤ q) :
    StrictMono fun k : ℕ => (q ^ (k + 1) - (-1) ^ (k + 1)) * (q ^ k - (-1) ^ k) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hpow : (-1 : ℤ) ^ (k + 1) ≤ 1 := by
    rcases neg_one_pow_eq_or ℤ (k + 1) with h | h <;> rw [h] <;> norm_num
  have hqk : q ≤ q ^ (k + 1) := le_self_pow₀ (by linarith) (by omega)
  have h1 : 0 < q ^ (k + 1) - (-1) ^ (k + 1) := by linarith
  have h2 : 0 < q ^ k * (q ^ 2 - 1) := by
    have : 0 < q ^ k := pow_pos (by linarith) k
    have : 0 < q ^ 2 - 1 := by nlinarith
    positivity
  have e : (q ^ (k + 1 + 1) - (-1) ^ (k + 1 + 1)) * (q ^ (k + 1) - (-1) ^ (k + 1)) -
      (q ^ (k + 1) - (-1) ^ (k + 1)) * (q ^ k - (-1) ^ k) =
        (q ^ (k + 1) - (-1) ^ (k + 1)) * (q ^ k * (q ^ 2 - 1)) := by ring
  show (q ^ (k + 1) - (-1) ^ (k + 1)) * (q ^ k - (-1) ^ k) <
    (q ^ (k + 1 + 1) - (-1) ^ (k + 1 + 1)) * (q ^ (k + 1) - (-1) ^ (k + 1))
  nlinarith [mul_pos h1 h2]

end SUTrans

open SUTrans

theorem IsSUImage.natCard_mul_eq {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)}
    {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm) :
    (Nat.card Δ : ℤ) * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) =
      (((2 ^ f : ℕ) : ℤ) ^ m - (-1) ^ m) * (((2 ^ f : ℕ) : ℤ) ^ (m - 1) - (-1) ^ (m - 1)) := by
  obtain ⟨Φ, hker, -, hΔ⟩ := hX
  have hF := card_galoisField_two_mul hf
  obtain ⟨e, -⟩ := exists_isoLinesEquiv (unitaryInvolution_involutive hF)
    (fun a ha => exists_add_unitaryInvolution_eq hF ha) hker hm hΔ
    (gramForm_antidiag_apply hf (m := m))
  rw [← Nat.card_congr e]
  exact card_isoLines_mul (fieldData hf) (gramForm_antidiag_isSymm hf m)
    (gramForm_antidiag_separatingLeft hf m) (Module.finrank_fin_fun _) hm

theorem IsSUImage.natCard_perp_mul_eq {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)}
    {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm) (hm4 : 4 ≤ m)
    {T : Subgroup K} (hT : T ∈ Δ) :
    (Nat.card {B // B ∈ Δ ∧ B ≠ T ∧ ⁅T, B⁆ = ⊥} : ℤ) * (((2 ^ f : ℕ) : ℤ) ^ 2 - 1) =
      ((2 ^ f : ℕ) : ℤ) ^ 2 * ((((2 ^ f : ℕ) : ℤ) ^ (m - 2) - (-1) ^ (m - 2)) *
        (((2 ^ f : ℕ) : ℤ) ^ (m - 2 - 1) - (-1) ^ (m - 2 - 1))) := by
  obtain ⟨Φ, hker, -, hΔ⟩ := hX
  have hF := card_galoisField_two_mul hf
  have hσ := unitaryInvolution_involutive hF
  set h := fieldData hf
  set B := gramForm h (antidiag m : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * f)))
  have hBu : ∀ x y, B x y = uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) x y :=
    gramForm_antidiag_apply hf
  have hB : B.IsSymm := gramForm_antidiag_isSymm hf m
  have hBl : B.SeparatingLeft := gramForm_antidiag_separatingLeft hf m
  obtain ⟨e, he⟩ := exists_isoLinesEquiv hσ (fun a ha => exists_add_unitaryInvolution_eq hF ha)
    hker hm hΔ hBu
  set L₀ := e.symm ⟨T, hT⟩
  obtain ⟨a, Ta, ha0, haa, hL₀, hTa, heL₀⟩ := he L₀
  have hTeq : T = Ta.map Φ := by
    rw [← heL₀, Equiv.apply_symm_apply]
  have hQP : ∀ M : TotIsoSubspaces B 1,
      (M.1 ≠ GaloisField 2 (2 * f) ∙ a ∧ ∀ y ∈ M.1, B a y = 0) ↔
        ((e M : Subgroup K) ≠ T ∧ ⁅T, (e M : Subgroup K)⁆ = ⊥) := by
    intro M
    obtain ⟨v, TM, hv0, hvv, hM, hTM, heM⟩ := he M
    refine and_congr (not_congr ⟨fun h => ?_, fun h => ?_⟩) ?_
    · rw [show M = L₀ from Subtype.ext (h.trans hL₀.symm), Equiv.apply_symm_apply]
    · have hML : M = L₀ := by
        rw [← e.symm_apply_apply M, show e M = ⟨T, hT⟩ from Subtype.ext h]
      rw [hML, hL₀]
    · rw [hTeq, heM, commutator_map_eq_bot_iff hσ hker hTa hTM ha0 haa hvv, hM]
      refine ⟨fun h => (hBu a v).symm.trans (h v (Submodule.mem_span_singleton_self v)),
        fun h y hy => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, smul_eq_mul, hBu, h, mul_zero]
  have e1 : {B' // B' ∈ Δ ∧ B' ≠ T ∧ ⁅T, B'⁆ = ⊥} ≃
      {M : TotIsoSubspaces B 1 // M.1 ≠ GaloisField 2 (2 * f) ∙ a ∧ ∀ y ∈ M.1, B a y = 0} :=
    ({ toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
       invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      {B' // B' ∈ Δ ∧ B' ≠ T ∧ ⁅T, B'⁆ = ⊥} ≃
        {U : Δ // (U : Subgroup K) ≠ T ∧ ⁅T, (U : Subgroup K)⁆ = ⊥}).trans
      (e.subtypeEquiv hQP).symm
  have haa' : B a a = 0 := (hBu a a).trans haa
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ :=
    CFSG.LinearGroups.hermitian_hyperbolic_splitting h hB hBl ha0 haa'
  obtain ⟨-, -, -, hUsep, hUdim⟩ := hsplit b hab hbb
  have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
  have hUa : ∀ x ∈ pairOrth B a b, B x a = 0 := fun x hx => by
    rw [← hB.eq a x,
      (Submodule.mem_orthogonalBilin.mp hx) a (Submodule.subset_span (by simp)), map_zero]
  rw [Nat.card_congr e1, card_orth_lines h hB ha0 haa',
    Nat.card_congr (isoFiberEquiv ha0 haa' hba hUa 1 : {W : TotIsoSubspaces B 2 // a ∈ W.1} ≃ _),
    Nat.cast_mul, Nat.cast_pow (2 ^ f) 2, mul_assoc,
    card_isoLines_mul h (hB.domRestrict _) hUsep (m := m - 2)
      (by rw [hUdim, Module.finrank_fin_fun]) (by omega)]

theorem unitaryPerpCount : UnitaryPerpCount := by
  intro K K' _ _ _ _ X X' Δ Δ' f m m' hf hm hm' hX hX' T hT hc
  have h1 := hX.natCard_perp_mul_eq hm hT
  have h2 := hX'.natCard_mul_eq
  have hq : (2 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_self_pow (by omega) 2
  have hc' := congrArg (Nat.cast : ℕ → ℤ) hc
  rw [Nat.cast_mul, Nat.cast_pow (2 ^ f) 2] at hc'
  have key : (((2 ^ f : ℕ) : ℤ) ^ (m - 2) - (-1) ^ (m - 2)) *
      (((2 ^ f : ℕ) : ℤ) ^ (m - 2 - 1) - (-1) ^ (m - 2 - 1)) =
      (((2 ^ f : ℕ) : ℤ) ^ m' - (-1) ^ m') * (((2 ^ f : ℕ) : ℤ) ^ (m' - 1) - (-1) ^ (m' - 1)) := by
    have hq0 : ((2 ^ f : ℕ) : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
    apply mul_left_cancel₀ hq0
    rw [← h1, hc', mul_assoc, h2]
  obtain ⟨a, ha⟩ : ∃ a, m - 2 = a + 1 := ⟨m - 3, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, m' = b + 1 := ⟨m' - 1, by omega⟩
  rw [ha, hb, Nat.add_sub_cancel, Nat.add_sub_cancel] at key
  have hab := (strictMono_isoPointCount hq).injective key
  omega

end CFSG.RankThree.GF2n.Tim81
