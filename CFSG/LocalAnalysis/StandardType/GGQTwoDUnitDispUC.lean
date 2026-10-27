module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylGen

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]

theorem qtwoDB36_perfect {X N : Subgroup G} (hN : LargeEvenPComponent 3 X N) :
    commutator ↥N = ⊤ := by
  have hL := (largeEvenPComponent_iff_lBalance 3 X N).1 hN
  exact (CFSG.ComponentClassification.LBalance.pComponent_perfect 3 X N hL.2).commutator_eq_top

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

private lemma qtwoDB36_b'_central {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N) :
    (b' : G) ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  exact Subgroup.mem_centralizer_singleton_iff.mp (hN.1 hn)

private lemma qtwoDB36_three_smul (v : DVec m) : 3 • v = 0 := by
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  funext j
  rw [Pi.smul_apply, nsmul_eq_mul, h3, zero_mul, Pi.zero_apply]

private lemma qtwoDB36_eq_b'_pow (s : ↥Bs) (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hoff : ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0) :
    ∃ k : ℕ, s = b' ^ k := by
  refine ⟨(βL (Additive.ofMul s) c).val, ?_⟩
  apply Additive.ofMul.injective
  apply βL.injective
  rw [ofMul_pow, map_nsmul, hb']
  funext j
  by_cases hj : j = c
  · rw [hj, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val (βL (Additive.ofMul s) c)).symm
  · rw [hoff j hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]

private lemma qtwoDB36_b'_pow_three (hb' : βL (Additive.ofMul b') = Pi.single c 1) :
    b' ^ 3 = 1 := by
  apply Additive.ofMul.injective
  apply βL.injective
  rw [ofMul_pow, map_nsmul, hb', ofMul_one, map_zero]
  exact qtwoDB36_three_smul _

private lemma qtwoDB36_b'_ne_one (hb' : βL (Additive.ofMul b') = Pi.single c 1) : b' ≠ 1 := by
  intro h
  have h1 : βL (Additive.ofMul b') = βL (Additive.ofMul (1 : ↥Bs)) := by rw [h]
  rw [hb', ofMul_one, map_zero] at h1
  have := congrFun h1 c
  simp at this

theorem qtwoDB36_gamma_of (hm : 1 ≤ m) (hBsE : IsElemAbelian 3 Bs)
    (hSC : ∀ h ∈ Subgroup.centralizer (Bs : Set G), h ^ 3 = 1 → h ∈ Bs)
    (hcard : Nat.card Bs = 3 ^ m) (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    {N : Subgroup G} (hb'N : (b' : G) ∈ Subgroup.centralizer (N : Set G))
    (hcent : ∀ s : ↥Bs, βL (Additive.ofMul s) c = 0 →
      (s : G) ∈ Subgroup.centralizer (N : Set G) → s = 1)
    (hinner : ∀ s : ↥Bs, ∃ t ∈ N, ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ = t * n * t⁻¹)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) :
    (∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔ ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0) ∧
      Nat.card (ggGamma N hBsN).range = 3 ^ (m - 1) ∧ IsElemAbelian 3 (ggGamma N hBsN).range ∧
        (ggGamma N hBsN).range ≤ (MulAut.conj : ↥N →* MulAut ↥N).range ∧
          GGTorusSelfCent 3 (ggGamma N hBsN).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker_char : ∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔
      ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0 := by
    intro s
    rw [ggGamma_eq_one_iff]
    constructor
    · intro hs k hk
      let kk : ℕ := (βL (Additive.ofMul s) c).val
      let tB : ↥Bs := s * (b' ^ kk)⁻¹
      have hpow : (((b' ^ kk : ↥Bs) : G)) ∈ Subgroup.centralizer (N : Set G) := by
        rw [Subgroup.coe_pow]
        exact Subgroup.pow_mem _ hb'N kk
      have htB_centN : (tB : G) ∈ Subgroup.centralizer (N : Set G) := by
        show ((s * (b' ^ kk)⁻¹ : ↥Bs) : G) ∈ Subgroup.centralizer (N : Set G)
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact Subgroup.mul_mem _ hs (Subgroup.inv_mem _ hpow)
      have hofmul : Additive.ofMul tB = Additive.ofMul s - kk • Additive.ofMul b' := by
        simp only [tB, ofMul_mul, ofMul_inv, ofMul_pow, sub_eq_add_neg]
      have htc : βL (Additive.ofMul tB) c = 0 := by
        rw [hofmul, map_sub, map_nsmul, hb', Pi.sub_apply]
        have hc : (kk • Pi.single c (1 : ZMod 3) : DVec m) c = (kk : ZMod 3) := by simp
        rw [hc, show (kk : ZMod 3) = βL (Additive.ofMul s) c from ZMod.natCast_zmod_val _]
        exact sub_self _
      have htBeq : tB = 1 := hcent tB htc htB_centN
      have hs_eq : s = b' ^ kk := by
        have h1 : (s : ↥Bs) * (b' ^ kk)⁻¹ = 1 := htBeq
        exact mul_inv_eq_one.mp h1
      rw [hs_eq, ofMul_pow, map_nsmul, hb']
      simp only [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero]
    · intro hoff
      obtain ⟨kk, rfl⟩ := qtwoDB36_eq_b'_pow _ hb' hoff
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hpow : (((b' ^ kk : ↥Bs) : G)) ∈ Subgroup.centralizer (N : Set G) := by
        rw [Subgroup.coe_pow]
        exact Subgroup.pow_mem _ hb'N kk
      exact Subgroup.mem_centralizer_iff.mp hpow n hn
  have hb'ker : b' ∈ (ggGamma N hBsN).ker := by
    rw [MonoidHom.mem_ker]
    exact (hker_char b').mpr (by
      intro k hk
      simp [hb', hk])
  have hker_le : (ggGamma N hBsN).ker ≤ Subgroup.zpowers b' := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    obtain ⟨kk, hkk⟩ := qtwoDB36_eq_b'_pow s hb' ((hker_char s).mp hs)
    rw [hkk]
    exact Subgroup.npow_mem_zpowers b' kk
  have hker_eq : (ggGamma N hBsN).ker = Subgroup.zpowers b' :=
    le_antisymm hker_le (Subgroup.zpowers_le.mpr hb'ker)
  have hcard_ker : Nat.card (ggGamma N hBsN).ker = 3 := by
    rw [hker_eq, Nat.card_zpowers,
      orderOf_eq_prime (qtwoDB36_b'_pow_three hb') (qtwoDB36_b'_ne_one hb')]
  have hcard_range : Nat.card (ggGamma N hBsN).range = 3 ^ (m - 1) := by
    have h := Subgroup.card_ker_mul_card_range (ggGamma N hBsN)
    rw [hcard_ker, hcard] at h
    have hm1 : 1 ≤ m := hm
    have hpow : 3 * 3 ^ (m - 1) = 3 ^ m := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hm1]
    rw [← hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hElem : IsElemAbelian 3 (ggGamma N hBsN).range := by
    have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBsE.1.is_comm.comm a b
    have hBp : ∀ a : ↥Bs, a ^ 3 = 1 := fun a =>
      Subtype.ext (by simpa using hBsE.2 a a.2)
    exact isElemAbelian_range hBc hBp _
  have hInner : (ggGamma N hBsN).range ≤ (MulAut.conj : ↥N →* MulAut ↥N).range := by
    rintro φ ⟨s, rfl⟩
    obtain ⟨t, htN, htact⟩ := hinner s
    refine MonoidHom.mem_range.mpr ⟨⟨t, htN⟩, ?_⟩
    ext n
    rw [MulAut.conj_apply, ggGamma_coe]
    simpa using (htact n n.2).symm
  exact ⟨hker_char, hcard_range, hElem, hInner, ggTorusSelfCent_ggGamma hBsN hSC⟩

private noncomputable def qtwoDB36_wBsFun {m : ℕ} (βL : Additive ↥Bs ≃+ DVec m)
    (w : DVec m ≃ₗ[ZMod 3] DVec m) : ↥Bs →* ↥Bs where
  toFun s := Additive.toMul (βL.symm (w (βL (Additive.ofMul s))))
  map_one' := by
    apply Additive.ofMul.injective
    apply βL.injective
    simp only [ofMul_one, map_zero, LinearEquiv.map_zero, ofMul_toMul, AddEquiv.apply_symm_apply,
      toMul_zero]
  map_mul' s t := by
    apply Additive.ofMul.injective
    apply βL.injective
    simp only [ofMul_mul, map_add, ofMul_toMul, AddEquiv.apply_symm_apply]

private lemma qtwoDB36_wBsFun_apply {m : ℕ} (βL : Additive ↥Bs ≃+ DVec m)
    (w : DVec m ≃ₗ[ZMod 3] DVec m) (s : ↥Bs) :
    βL (Additive.ofMul (qtwoDB36_wBsFun βL w s)) = w (βL (Additive.ofMul s)) := by
  change βL (Additive.ofMul (Additive.toMul (βL.symm (w (βL (Additive.ofMul s)))))) =
    w (βL (Additive.ofMul s))
  rw [ofMul_toMul, AddEquiv.apply_symm_apply]

private lemma qtwoDB36_wBsFun_mul_apply {m : ℕ} (βL : Additive ↥Bs ≃+ DVec m)
    (w₁ w₂ : DVec m ≃ₗ[ZMod 3] DVec m) (s : ↥Bs) :
    qtwoDB36_wBsFun βL (w₁ * w₂) s = qtwoDB36_wBsFun βL w₁ (qtwoDB36_wBsFun βL w₂ s) := by
  apply Additive.ofMul.injective
  apply βL.injective
  rw [qtwoDB36_wBsFun_apply, LinearEquiv.mul_apply, qtwoDB36_wBsFun_apply,
    qtwoDB36_wBsFun_apply]

private lemma qtwoDB36_wBsFun_div_apply {m : ℕ} (βL : Additive ↥Bs ≃+ DVec m)
    (w₁ w₂ : DVec m ≃ₗ[ZMod 3] DVec m) (s : ↥Bs) :
    βL (Additive.ofMul (qtwoDB36_wBsFun βL w₁ s * (qtwoDB36_wBsFun βL w₂ s)⁻¹)) =
      w₁ (βL (Additive.ofMul s)) - w₂ (βL (Additive.ofMul s)) := by
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg, qtwoDB36_wBsFun_apply, sub_eq_add_neg]

private lemma qtwoDB36_eval_smul_basis_same (m : ℕ) (a : ZMod 3) (j : Fin m) :
    (a • dBasis m j) j = a := by
  simp [dBasis, Pi.basisFun_apply]

private lemma qtwoDB36_eval_smul_basis_of_ne (m : ℕ) (a : ZMod 3) {i j : Fin m} (h : i ≠ j) :
    (a • dBasis m i) j = 0 := by
  simp only [dBasis, Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_of_ne' h, smul_zero]

private lemma qtwoDB36_dEven_fix_eq_of_sub_supported {m : ℕ} {c : Fin m}
    {w₁ w₂ : DVec m ≃ₗ[ZMod 3] DVec m} (hw₁ : w₁ ∈ dEven m) (hw₂ : w₂ ∈ dEven m)
    (hfix₁ : w₁ (Pi.single c 1) = Pi.single c 1) (hfix₂ : w₂ (Pi.single c 1) = Pi.single c 1)
    (hsub : ∀ v : DVec m, ∀ j : Fin m, j ≠ c → (w₁ v - w₂ v) j = 0) : w₁ = w₂ := by
  obtain ⟨σ₁, T₁, hσ₁c, -, -, hact₁⟩ := ggQTwoDUnit_dEven_fix_decomp hw₁ hfix₁
  obtain ⟨σ₂, T₂, hσ₂c, -, -, hact₂⟩ := ggQTwoDUnit_dEven_fix_decomp hw₂ hfix₂
  refine (dBasis m).ext' fun k => ?_
  by_cases hk : k = c
  · rw [hk]
    have h1 : w₁ (dBasis m c) = dBasis m c := by
      simpa [dBasis, Pi.basisFun_apply] using hfix₁
    have h2 : w₂ (dBasis m c) = dBasis m c := by
      simpa [dBasis, Pi.basisFun_apply] using hfix₂
    rw [h1, h2]
  · have hk₁ : σ₁ k ≠ c := fun h => hk (σ₁.injective (by rw [h, hσ₁c]))
    by_cases hσ : σ₁ k = σ₂ k
    · rw [hact₁ k, hact₂ k, hσ]
      have hval := hsub (dBasis m k) (σ₂ k) (by rwa [hσ] at hk₁)
      rw [hact₁ k, hact₂ k, hσ] at hval
      rw [Pi.sub_apply, qtwoDB36_eval_smul_basis_same, qtwoDB36_eval_smul_basis_same,
        sub_eq_zero] at hval
      rw [hval]
    · have hval := hsub (dBasis m k) (σ₁ k) hk₁
      rw [hact₁ k, hact₂ k] at hval
      rw [Pi.sub_apply, qtwoDB36_eval_smul_basis_same,
        qtwoDB36_eval_smul_basis_of_ne m _ (Ne.symm hσ), sub_zero] at hval
      have hT : σ₁ k ∉ T₁ := by
        intro hmem
        rw [if_pos hmem] at hval
        exact absurd hval (by decide)
      rw [if_neg hT] at hval
      exact absurd hval (by decide)

theorem qtwoDB36_weyl_embed_of {N : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (hker_char : ∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔
      ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ a' ∈ ggAutomizer N Bs,
      ∀ s : ↥Bs, βL (Additive.ofMul (a' s)) = w (βL (Additive.ofMul s))) :
    ∃ Θ : ↥(dEvenStab m (Pi.single c 1)) →*
        ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range),
      Function.Injective Θ ∧ ∀ (w : ↥(dEvenStab m (Pi.single c 1))) (s : ↥Bs),
        (Θ w : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
          (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm
            ((w : DVec m ≃ₗ[ZMod 3] DVec m) (βL (Additive.ofMul s))))) := by
  classical
  let A : Subgroup (MulAut ↥N) := (ggGamma N hBsN).range
  let f : ↥Bs →* ↥A := (ggGamma N hBsN).rangeRestrict
  have hf_surj : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  have hf_one : ∀ s : ↥Bs, f s = 1 ↔ ggGamma N hBsN s = 1 := fun s => Subtype.ext_iff
  have hf_apply : ∀ s : ↥Bs, (f s : MulAut ↥N) = ggGamma N hBsN s :=
    fun s => MonoidHom.coe_rangeRestrict _ s
  have hker_f : ∀ s t : ↥Bs, f s = f t ↔
      ∀ k : Fin m, k ≠ c → βL (Additive.ofMul (s * t⁻¹)) k = 0 := by
    intro s t
    constructor
    · intro h k hk
      have h2 : ggGamma N hBsN s = ggGamma N hBsN t := by
        have h2' : (f s : MulAut ↥N) = (f t : MulAut ↥N) := congrArg Subtype.val h
        rwa [hf_apply s, hf_apply t] at h2'
      have h1 : ggGamma N hBsN (s * t⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      exact (hker_char (s * t⁻¹)).mp h1 k hk
    · intro h
      have h1 : ggGamma N hBsN (s * t⁻¹) = 1 := (hker_char (s * t⁻¹)).mpr h
      have h2 : ggGamma N hBsN s = ggGamma N hBsN t := by
        have h3 := congrArg (fun x => x * ggGamma N hBsN t) h1
        rw [one_mul, ← map_mul] at h3
        have hst : s * t⁻¹ * t = s := by group
        rwa [hst] at h3
      exact Subtype.ext (by rw [hf_apply s, hf_apply t]; exact h2)
  let Φ : (w : DVec m ≃ₗ[ZMod 3] DVec m) → w (Pi.single c 1) = Pi.single c 1 →
      ↥A →* ↥A := fun w hwc =>
    f.liftOfRightInverse (Function.surjInv hf_surj) (Function.rightInverse_surjInv hf_surj)
      ⟨f.comp (qtwoDB36_wBsFun βL w), by
        intro s hs
        rw [MonoidHom.mem_ker] at hs ⊢
        have hs1 : ggGamma N hBsN s = 1 := (hf_one s).mp hs
        have hsupp := (hker_char s).mp hs1
        have hwfix : w (βL (Additive.ofMul s)) = βL (Additive.ofMul s) := by
          have hdecomp : βL (Additive.ofMul s) =
              βL (Additive.ofMul s) c • Pi.single c 1 := by
            funext j
            by_cases hj : j = c
            · subst hj; simp
            · rw [hsupp j hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
          rw [hdecomp, map_smul, hwc]
        have hwBs : qtwoDB36_wBsFun βL w s = s := by
          apply Additive.ofMul.injective
          apply βL.injective
          rw [qtwoDB36_wBsFun_apply]
          exact hwfix
        show f (qtwoDB36_wBsFun βL w s) = 1
        rw [hwBs, hs]⟩
  have hΦ_apply : ∀ (w : DVec m ≃ₗ[ZMod 3] DVec m)
      (hwc : w (Pi.single c 1) = Pi.single c 1) (s : ↥Bs),
      Φ w hwc (f s) = f (qtwoDB36_wBsFun βL w s) := by
    intro w hwc s
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ s
  haveI : Finite ↥A := inferInstance
  have hbij : ∀ w : ↥(dEvenStab m (Pi.single c 1)),
      Function.Bijective (Φ (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2.2) := by
    intro w
    have hwc_symm : (w : DVec m ≃ₗ[ZMod 3] DVec m).symm (Pi.single c 1) =
        Pi.single c 1 := by
      have h := congrArg (fun v => (w : DVec m ≃ₗ[ZMod 3] DVec m).symm v) w.2.2
      simpa using h.symm
    have hleft : Function.LeftInverse
        (Φ ((w : DVec m ≃ₗ[ZMod 3] DVec m).symm) hwc_symm)
        (Φ (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2.2) := by
      intro x
      obtain ⟨s, rfl⟩ := hf_surj x
      rw [hΦ_apply (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2.2,
        hΦ_apply ((w : DVec m ≃ₗ[ZMod 3] DVec m).symm) hwc_symm]
      congr 1
      apply Additive.ofMul.injective
      apply βL.injective
      simp only [qtwoDB36_wBsFun_apply, LinearEquiv.symm_apply_apply]
    exact (Finite.injective_iff_bijective).mp hleft.injective
  let Ψ : ↥(dEvenStab m (Pi.single c 1)) → MulAut ↥A :=
    fun w => MulEquiv.ofBijective (Φ (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2.2) (hbij w)
  have hΨ_apply : ∀ (w : ↥(dEvenStab m (Pi.single c 1))) (s : ↥Bs),
      (Ψ w) (f s) = f (qtwoDB36_wBsFun βL (w : DVec m ≃ₗ[ZMod 3] DVec m) s) := by
    intro w s
    change Φ (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2.2 (f s) = _
    rw [hΦ_apply (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2.2]
  have hΨ_map_mul : ∀ w₁ w₂ : ↥(dEvenStab m (Pi.single c 1)),
      Ψ (w₁ * w₂) = Ψ w₁ * Ψ w₂ := by
    intro w₁ w₂
    refine MulEquiv.ext fun x => ?_
    obtain ⟨s, rfl⟩ := hf_surj x
    rw [MulAut.mul_apply, hΨ_apply (w₁ * w₂) s, hΨ_apply w₂ s,
      hΨ_apply w₁ (qtwoDB36_wBsFun βL (w₂ : DVec m ≃ₗ[ZMod 3] DVec m) s)]
    congr 1
    rw [Subgroup.coe_mul, qtwoDB36_wBsFun_mul_apply]
  let Θ₀ : ↥(dEvenStab m (Pi.single c 1)) →* MulAut ↥A := MonoidHom.mk' Ψ hΨ_map_mul
  have hmem : ∀ w : ↥(dEvenStab m (Pi.single c 1)),
      Ψ w ∈ ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range A := by
    intro w
    obtain ⟨a', hauto, ha'w⟩ := hW (w : DVec m ≃ₗ[ZMod 3] DVec m) w.2
    obtain ⟨n, hnN, hnNorm, hnAct⟩ := mem_ggAutomizer_iff.mp hauto
    have hnorm : MulAut.conj (⟨n, hnN⟩ : ↥N) ∈
        Subgroup.normalizer (A : Set (MulAut ↥N)) :=
      conj_mem_normalizer_range_ggGamma hBsN hnN hnNorm
    have hΨeq : Ψ w = ggConjAut A hnorm := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨s, rfl⟩ := hf_surj x
      apply Subtype.ext
      rw [ggConjAut_apply]
      have hwBs_eq : qtwoDB36_wBsFun βL (w : DVec m ≃ₗ[ZMod 3] DVec m) s = a' s := by
        apply Additive.ofMul.injective
        apply βL.injective
        rw [qtwoDB36_wBsFun_apply, ha'w s]
      have hsub : (⟨n * (s : G) * n⁻¹,
            (Subgroup.mem_normalizer_iff.mp hnNorm s).mp s.2⟩ : ↥Bs) = a' s :=
        Subtype.ext (hnAct s).symm
      have hL : ((Ψ w (f s) : ↥A) : MulAut ↥N) = ggGamma N hBsN (a' s) := by
        rw [hΨ_apply w s, hwBs_eq]
        rfl
      have hR : MulAut.conj (⟨n, hnN⟩ : ↥N) * ((f s : ↥A) : MulAut ↥N) *
            (MulAut.conj (⟨n, hnN⟩ : ↥N))⁻¹ = ggGamma N hBsN (a' s) := by
        rw [← hsub]
        exact (ggGamma_conj N hBsN ⟨n, hnN⟩ s _).symm
      rw [hL, hR]
    rw [hΨeq]
    exact ggConjAut_mem_ggAutomizer (g := MulAut.conj (⟨n, hnN⟩ : ↥N))
      (MonoidHom.mem_range.mpr ⟨⟨n, hnN⟩, rfl⟩) hnorm
  let Θ : ↥(dEvenStab m (Pi.single c 1)) →*
      ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range A) :=
    Θ₀.codRestrict (ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range A) hmem
  have hΘ_inj : Function.Injective Θ := by
    intro w₁ w₂ h
    have hΨ : Ψ w₁ = Ψ w₂ := by
      have h2 : (Θ₀ w₁ : MulAut ↥A) = (Θ₀ w₂ : MulAut ↥A) :=
        congrArg (fun z : ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range A) =>
          (z : MulAut ↥A)) h
      exact h2
    have hact : ∀ s : ↥Bs,
        f (qtwoDB36_wBsFun βL (w₁ : DVec m ≃ₗ[ZMod 3] DVec m) s) =
        f (qtwoDB36_wBsFun βL (w₂ : DVec m ≃ₗ[ZMod 3] DVec m) s) := by
      intro s
      have h := congrFun (congrArg (fun z : MulAut ↥A => (z : ↥A → ↥A)) hΨ) (f s)
      rw [hΨ_apply w₁ s, hΨ_apply w₂ s] at h
      exact h
    have hsub : ∀ v : DVec m, ∀ k : Fin m, k ≠ c →
        ((w₁ : DVec m ≃ₗ[ZMod 3] DVec m) v -
          (w₂ : DVec m ≃ₗ[ZMod 3] DVec m) v) k = 0 := by
      intro v k hk
      obtain ⟨t, rfl⟩ := βL.surjective v
      have h1 := (hker_f
        (qtwoDB36_wBsFun βL (w₁ : DVec m ≃ₗ[ZMod 3] DVec m) (Additive.toMul t))
        (qtwoDB36_wBsFun βL (w₂ : DVec m ≃ₗ[ZMod 3] DVec m) (Additive.toMul t))).mp
        (hact (Additive.toMul t)) k hk
      rw [qtwoDB36_wBsFun_div_apply] at h1
      rwa [ofMul_toMul] at h1
    have heq : (w₁ : DVec m ≃ₗ[ZMod 3] DVec m) = (w₂ : DVec m ≃ₗ[ZMod 3] DVec m) :=
      qtwoDB36_dEven_fix_eq_of_sub_supported w₁.2.1 w₂.2.1 w₁.2.2 w₂.2.2 hsub
    exact Subtype.ext heq
  refine ⟨Θ, hΘ_inj, ?_⟩
  intro w s
  change (Θ₀ w : MulAut ↥A) (f s) =
    f (qtwoDB36_wBsFun βL (w : DVec m ≃ₗ[ZMod 3] DVec m) s)
  exact hΨ_apply w s

theorem qtwoDB36_gamma (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) :
    (∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔ ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0) ∧
      Nat.card (ggGamma N hBsN).range = 3 ^ (m - 1) ∧ IsElemAbelian 3 (ggGamma N hBsN).range ∧
        (ggGamma N hBsN).range ≤ (MulAut.conj : ↥N →* MulAut ↥N).range ∧
          GGTorusSelfCent 3 (ggGamma N hBsN).range := by
  have hBsE : IsElemAbelian 3 Bs := by
    have h := hbase.hyp.bstar.2.1
    rwa [hbase.p_eq] at h
  exact qtwoDB36_gamma_of (by omega) hBsE
    (fun h hh h3 => hbase.hyp.bstar.2.2.2 h hh (by rw [hbase.p_eq]; exact h3)) hbase.card_bs
    hdel.coord (qtwoDB36_b'_central hN)
    (fun s hsc hsC => ggQTwoDUnit_cent_E hm hbase hcoords hdel s hsc
      (Subgroup.centralizer_le hJ₁ hsC) (Subgroup.centralizer_le hJ₂ hsC))
    (fun s => ggQTwoDUnit_inner_N hm hbase hcoords hdel hN hJ₁ hJ₂ s) hBsN

theorem qtwoDB36_weyl_embed (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G} (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) :
    ∃ Θ : ↥(dEvenStab m (Pi.single c 1)) →*
        ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range),
      Function.Injective Θ ∧ ∀ (w : ↥(dEvenStab m (Pi.single c 1))) (s : ↥Bs),
        (Θ w : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
          (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm
            ((w : DVec m ≃ₗ[ZMod 3] DVec m) (βL (Additive.ofMul s))))) :=
  qtwoDB36_weyl_embed_of hBsN (qtwoDB36_gamma hm hbase hcoords hdel hN hJ₁ hJ₂ hBsN).1
    fun w hw => by
      obtain ⟨a', ha'J, ha'w⟩ := hcoords.join_onto w hw.1
      exact ⟨a', ggAutomizer_mono Bs (sup_le hJ₁ hJ₂)
        (ggQTwoDUnit_weyl_X (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign
          hdel.norm hdel.conj ha'J hw.1 hw.2 ha'w), ha'w⟩

end CFSG.StandardType.QTwo

end
