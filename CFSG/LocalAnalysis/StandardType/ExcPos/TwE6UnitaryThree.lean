module

public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.Open.LocalVocabulary
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Torus
import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.Open.StatedCenterThree
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.SemisimpleCentralizers.HeldLangSU
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Open CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

theorem exists_diag_torus3 {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ T : Subgroup (GL (Fin 6) K), IsElemAbelian 3 T ∧ Nat.card T = 3 ^ 5 ∧
      (∀ t : Fin 6 → Kˣ, (∀ i, t i ^ 3 = 1) → ∏ i, t i = 1 → diagGL t ∈ T) ∧
      (∀ A ∈ T, ∃ t : Fin 6 → Kˣ, (∀ i, t i ^ 3 = 1) ∧ ∏ i, t i = 1 ∧ A = diagGL t) := by
  classical
  let μ : Subgroup Kˣ := rootsOfUnity 3 K
  have hμcard : Nat.card μ = 3 := CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3
  have hμ3 : ∀ z : μ, z ^ 3 = 1 := fun z => Subtype.ext ((mem_rootsOfUnity 3 _).1 z.2)
  let prod : (Fin 6 → μ) →* μ :=
    { toFun := fun t => ∏ i, t i
      map_one' := by simp
      map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
  let T : Subgroup (Fin 6 → μ) := prod.ker
  let ψ : (Fin 6 → μ) →* GL (Fin 6) K :=
    { toFun := fun t => diagGL fun i => (t i : Kˣ)
      map_one' := by
        rw [← diagGL_one]
        rfl
      map_mul' := fun a b => by
        rw [← diagGL_mul]
        rfl }
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h2 := diagGL_injective hab
    exact funext fun i => Subtype.ext (congrFun h2 i)
  let ψ' : T →* GL (Fin 6) K := ψ.comp T.subtype
  have hψ'inj : Function.Injective ψ' := hψinj.comp Subtype.val_injective
  have hTcard : Nat.card T = 3 ^ 5 := by
    have h1 := Subgroup.card_ker_mul_card_range prod
    have hrange : prod.range = ⊤ := by
      rw [eq_top_iff]
      intro z _
      refine ⟨Pi.mulSingle (0 : Fin 6) z, ?_⟩
      show ∏ i, (Pi.mulSingle (0 : Fin 6) z : Fin 6 → μ) i = z
      rw [Finset.prod_pi_mulSingle']
      simp
    have h2 : Nat.card (Fin 6 → μ) = 3 ^ 6 := by
      rw [Nat.card_fun, hμcard, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hrange, Subgroup.card_top, hμcard, h2] at h1
    have h3' : 3 ^ 6 = 3 ^ 5 * 3 := by norm_num
    rw [h3'] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hcoe : ∀ s : Fin 6 → μ, ((∏ i, s i : μ) : Kˣ) = ∏ i, (s i : Kˣ) := fun s =>
    map_prod μ.subtype s Finset.univ
  refine ⟨ψ'.range, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show ψ' a * ψ' b = ψ' b * ψ' a
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    funext i
    exact mul_comm _ _
  · rintro x ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (funext fun i => by simpa using hμ3 ((a : Fin 6 → μ) i))
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hψ'inj).toEquiv.symm, hTcard]
  · intro t ht hprod
    let s : Fin 6 → μ := fun i => ⟨t i, (mem_rootsOfUnity 3 _).2 (ht i)⟩
    have hs : s ∈ T := by
      show prod s = 1
      refine Subtype.ext ?_
      show ((∏ i, s i : μ) : Kˣ) = 1
      rw [hcoe s]
      exact hprod
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    refine ⟨fun i => (s i : Kˣ), fun i => (mem_rootsOfUnity 3 _).1 (s i).2, ?_, rfl⟩
    have h1 : prod s = 1 := hs
    have h2 := congrArg Subtype.val h1
    exact (hcoe s).symm.trans h2

theorem exists_elemAbelian_three_pow_five_of_cube_eq_one
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (h3 : 3 ∣ 2 ^ f + 1)
    (B : unitarySL σ) (hB : B ^ 3 = 1) :
    ∃ E : Subgroup (unitarySL σ), IsElemAbelian 3 E ∧ B ∈ E ∧ 3 ^ 5 ≤ Nat.card E := by
  classical
  have hfd : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hbar : hfd.bar = σ := RingHom.ext fun c => by rw [UnitaryFieldData.bar_apply, hσ]
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hq1 : 2 ^ f + 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr h3
    have hq2 : 2 ^ f ≡ 2 [MOD 3] := by
      have h3' : 2 + 1 ≡ 0 [MOD 3] := by norm_num [Nat.ModEq]
      exact Nat.ModEq.add_right_cancel' 1 (hq1.trans h3'.symm)
    have hq2sq : (2 ^ f) ^ 2 ≡ 1 [MOD 3] := by
      have h := Nat.ModEq.pow 2 hq2
      have h4 : (2 ^ 2 : ℕ) ≡ 1 [MOD 3] := by norm_num [Nat.ModEq]
      exact h.trans h4
    exact hq2sq.symm.dvd'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζu, hζu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  have hζ : IsPrimitiveRoot (ζu : K) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hζu)
  let J : Matrix (Fin 6) (Fin 6) K := antiId K
  let Bm : Matrix (Fin 6) (Fin 6) K :=
    ((B : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  have hBunit : (Bm.map σ)ᵀ * J * Bm = J := mem_unitarySL_iff.mp B.2
  have hJherm : (J.map hfd.bar)ᵀ = J := by
    rw [hbar, antiId_map, antiId_transpose]
  have hJdet : J.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (antiId_mul_self (E := K))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  let g : Module.End K (Fin 6 → K) := Matrix.toLin' Bm
  have hBm3 : Bm ^ 3 = 1 := by
    have h1 : (B : Matrix.SpecialLinearGroup (Fin 6) K) ^ 3 = 1 := congrArg Subtype.val hB
    have h2 := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 6) K => (z : Matrix (Fin 6) (Fin 6) K)) h1
    simpa [Bm, Matrix.SpecialLinearGroup.coe_pow] using h2
  have hg3 : g ^ 3 = 1 := by
    refine LinearMap.ext fun v => ?_
    have h1 : (g ^ 3) v = (Bm ^ 3) *ᵥ v := by
      simp [g, pow_succ, Module.End.mul_apply, Matrix.mulVec_mulVec, Matrix.toLin'_apply,
        Matrix.mul_assoc]
    rw [h1, hBm3, Matrix.one_mulVec]
    rfl
  have hiso : ∀ v w, gramForm hfd J (g v) (g w) = gramForm hfd J v w := by
    intro v w
    have := (gramForm_isometry_iff hfd J Bm).mpr (by rw [hbar]; exact hBunit)
    simpa [g, Matrix.toLin'_apply] using this v w
  obtain ⟨b, μ, hbμ, hbo⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis hfd hζ h3
      (gramForm_isSymm hfd hJherm) (gramForm_separatingLeft hfd hJdet) (ι := Unit)
      (fun _ => g) (fun _ _ => Commute.refl _) (fun _ => hg3) (fun _ v w => hiso v w)
  let e : Fin (Module.finrank K (Fin 6 → K)) ≃ Fin 6 := finCongr (Module.finrank_fin_fun K)
  let b' := b.reindex e
  let μ' : Fin 6 → K := fun j => μ () (e.symm j)
  have hb'j : ∀ j, b' j = b (e.symm j) := fun j => by simp [b']
  have heig : ∀ j, Bm *ᵥ b' j = μ' j • b' j := fun j => by
    have := hbμ () (e.symm j)
    simpa [g, Matrix.toLin'_apply, hb'j, μ'] using this
  have hortho : ∀ i j, gramForm hfd J (b' i) (b' j) = if i = j then 1 else 0 := fun i j => by
    have := hbo (e.symm i) (e.symm j)
    simpa [hb'j, e.symm.injective.eq_iff] using this
  let Qm : Matrix (Fin 6) (Fin 6) K := (Pi.basisFun K (Fin 6)).toMatrix b'
  have hQapply : ∀ i j, Qm i j = b' j i := fun i j => by
    simp [Qm, Module.Basis.toMatrix_apply]
  have hQcol : ∀ j, Qm *ᵥ Pi.single j 1 = b' j := fun j => by
    ext i
    simp [Matrix.mulVec_single_one, hQapply]
  have hQ : (Qm.map hfd.bar)ᵀ * J * Qm = 1 := by
    ext i j
    have h1 := gramForm_mulVec hfd J Qm (Pi.single i 1) (Pi.single j 1)
    rw [hQcol i, hQcol j, hortho i j, gramForm_single] at h1
    rw [Matrix.one_apply]
    exact h1.symm
  have hQdet : IsUnit Qm.det := by
    have := (Pi.basisFun K (Fin 6)).isUnit_det b'
    rwa [Module.Basis.det_apply] at this
  have hμ3 : ∀ j, μ' j ^ 3 = 1 := by
    intro j
    have hpow : ∀ n : ℕ, (g ^ n) (b' j) = μ' j ^ n • b' j := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Module.End.mul_apply]
        have hg1 : g (b' j) = μ' j • b' j := by simpa [g, Matrix.toLin'_apply] using heig j
        rw [hg1, map_smul, ih, smul_smul, pow_succ, mul_comm]
    have h1 := hpow 3
    rw [hg3] at h1
    have h2 : b' j = μ' j ^ 3 • b' j := by simpa using h1
    have h3' : (μ' j ^ 3 - 1) • b' j = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3' with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (b'.ne_zero j)
  have hμne : ∀ j, μ' j ≠ 0 := fun j h0 => by
    have := hμ3 j
    rw [h0] at this
    norm_num at this
  let u : Fin 6 → Kˣ := fun j => Units.mk0 (μ' j) (hμne j)
  have hu3 : ∀ j, u j ^ 3 = 1 := fun j => Units.ext (by simpa [u] using hμ3 j)
  have hBQ : Bm * Qm = Qm * Matrix.diagonal μ' := by
    ext i j
    have h1 : (Bm * Qm) i j = (Bm *ᵥ b' j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hQapply]
    rw [h1, heig j, Matrix.mul_diagonal, hQapply]
    simp [mul_comm]
  have hBconj : Bm = Qm * Matrix.diagonal μ' * Qm⁻¹ := by
    calc Bm = Bm * (Qm * Qm⁻¹) := by rw [Matrix.mul_nonsing_inv _ hQdet, Matrix.mul_one]
      _ = (Bm * Qm) * Qm⁻¹ := by rw [Matrix.mul_assoc]
      _ = Qm * Matrix.diagonal μ' * Qm⁻¹ := by rw [hBQ]
  have hdetB : ∏ j, u j = 1 := by
    have h1 : Bm.det = 1 := (B : Matrix.SpecialLinearGroup (Fin 6) K).2
    have h2 : Bm.det = ∏ j, μ' j := by
      rw [hBconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm (Qm.det),
        mul_assoc, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hQdet, Matrix.det_one, mul_one]
    refine Units.ext ?_
    rw [Units.coe_prod]
    simpa [u] using h2.symm.trans h1
  have hQiso : ∀ x y, gramForm hfd J (Qm *ᵥ x) (Qm *ᵥ y) = gramForm hfd 1 x y := by
    intro x y
    rw [gramForm_mulVec, hQ]
  have hconj_unit : ∀ d : Fin 6 → K, (∀ i, hfd.bar (d i) * d i = 1) →
      ((Qm * Matrix.diagonal d * Qm⁻¹).map hfd.bar)ᵀ * J * (Qm * Matrix.diagonal d * Qm⁻¹) = J := by
    intro d hd
    refine (gramForm_isometry_iff hfd J _).mp ?_
    intro x y
    have hDiso : ∀ x y, gramForm hfd 1 (Matrix.diagonal d *ᵥ x) (Matrix.diagonal d *ᵥ y) =
        gramForm hfd 1 x y := by
      intro x y
      refine (gramForm_isometry_iff hfd 1 (Matrix.diagonal d)).mpr ?_ x y
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.mul_apply, Matrix.diagonal_apply, hd]
      · simp [Matrix.mul_apply, Matrix.diagonal_apply, hij]
    have hx : x = Qm *ᵥ (Qm⁻¹ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQdet, Matrix.one_mulVec]
    have hy : y = Qm *ᵥ (Qm⁻¹ *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQdet, Matrix.one_mulVec]
    have hm : ∀ z : Fin 6 → K, (Qm * Matrix.diagonal d * Qm⁻¹) *ᵥ z =
        Qm *ᵥ (Matrix.diagonal d *ᵥ (Qm⁻¹ *ᵥ z)) := by
      intro z
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hm x, hm y, hQiso, hDiso, ← hQiso]
    rw [← hx, ← hy]
  obtain ⟨T, hTel, hTcard, hTmem, hTchar⟩ := exists_diag_torus3 h3K
  let Q : GL (Fin 6) K := Matrix.nonsingInvUnit Qm hQdet
  let Ψ : GL (Fin 6) K →* GL (Fin 6) K := (MulAut.conj Q).toMonoidHom
  let ι : unitarySL σ →* GL (Fin 6) K :=
    Matrix.SpecialLinearGroup.toGL.comp (unitarySL σ).subtype
  have hι : Function.Injective ι :=
    Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective
  have hΨ : Function.Injective Ψ := (MulAut.conj Q).injective
  have hΨval : ∀ A : GL (Fin 6) K, ((Ψ A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Qm * (A : Matrix (Fin 6) (Fin 6) K) * Qm⁻¹ := fun A => rfl
  have hTQ : ∀ A ∈ T, Ψ A ∈ ι.range := by
    intro A hA
    obtain ⟨t, ht3, htp, rfl⟩ := hTchar A hA
    let d : Fin 6 → K := fun i => (t i : K)
    have hd : ∀ i, hfd.bar (d i) * d i = 1 := fun i =>
      CFSG.RankThree.PartOne.KCUnitaryPlane.bar_eq_inv_of_pow_eq_one hfd h3
        (μ := (t i : K)) (by simpa using congrArg Units.val (ht3 i))
    let M : Matrix (Fin 6) (Fin 6) K := Qm * Matrix.diagonal d * Qm⁻¹
    have hdetM : M.det = 1 := by
      have h1 : M.det = ∏ i, d i := by
        show (Qm * Matrix.diagonal d * Qm⁻¹).det = _
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm (Qm.det), mul_assoc,
          ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hQdet, Matrix.det_one, mul_one]
      rw [h1]
      have h2 := congrArg Units.val htp
      simpa [d, Units.coe_prod] using h2
    let Mσ : Matrix.SpecialLinearGroup (Fin 6) K := ⟨M, hdetM⟩
    have hMu : Mσ ∈ unitarySL σ := by
      rw [mem_unitarySL_iff]
      have := hconj_unit d hd
      rw [hbar] at this
      exact this
    refine ⟨⟨Mσ, hMu⟩, ?_⟩
    refine Units.ext ?_
    show (Mσ : Matrix (Fin 6) (Fin 6) K) = _
    rw [hΨval]
    rfl
  let TQ : Subgroup (GL (Fin 6) K) := T.map Ψ
  let E : Subgroup (unitarySL σ) := TQ.comap ι
  have hTQrange : TQ ≤ ι.range := by
    rintro _ ⟨A, hA, rfl⟩
    exact hTQ A hA
  refine ⟨E, (hTel.map Ψ).comap hι, ?_, ?_⟩
  · show ι B ∈ TQ
    refine ⟨diagGL u, hTmem u hu3 hdetB, ?_⟩
    refine Units.ext ?_
    rw [hΨval]
    show Qm * Matrix.diagonal (fun j => (u j : K)) * Qm⁻¹ = Bm
    rw [hBconj]
    rfl
  · have hmap : (TQ.comap ι).map ι = TQ := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hTQrange]
    exact le_of_eq (by
      calc 3 ^ 5 = Nat.card T := hTcard.symm
        _ = Nat.card TQ := (Subgroup.card_map_of_injective hΨ).symm
        _ = Nat.card ((TQ.comap ι).map ι) := by rw [hmap]
        _ = Nat.card E := Subgroup.card_map_of_injective hι)

end CFSG.StandardType.LieKnownR2.ExcPos
