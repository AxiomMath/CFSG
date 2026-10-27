module

public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUAniso
import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private theorem mul_tvMat_comm {σ : K ≃+* K} {A : Matrix (Fin n) (Fin n) K}
    {a : Fin n → K} {lam : K}
    (hA : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y)
    (ha : A *ᵥ a = lam • a) (hlam : σ lam * lam = 1) (t : K) :
    A * tvMat σ a t = tvMat σ a t * A := by
  have hherm : ∀ w, herm σ a (A *ᵥ w) = lam * herm σ a w := by
    intro w
    have h := hA a w
    rw [ha, herm_smul_left] at h
    calc herm σ a (A *ᵥ w) = lam * (σ lam * herm σ a (A *ᵥ w)) := by
          rw [← mul_assoc, mul_comm lam (σ lam), hlam, one_mul]
      _ = lam * herm σ a w := by rw [h]
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tvMat_mulVec, tvMat_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, ha, hherm (Pi.single i 1), smul_smul]
  module

private theorem uCentre_of_eigen {σ : K ≃+* K} {H : Subgroup (SUid σ n)}
    {A : Matrix (Fin n) (Fin n) K} (hA : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y)
    {a : Fin n → K} {lam : K} (ha : A *ᵥ a = lam • a) (hlam : σ lam * lam = 1)
    (hH : ∀ g : SUid σ n, A * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A → g ∈ H) :
    USeitz.UCentre H a := by
  intro g t _ hg
  have hmat : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tvMat σ a t := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [show ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 =
        g • Pi.single i 1 from rfl, hg, tvMat_mulVec]
  exact hH g (by rw [hmat]; exact mul_tvMat_comm hA ha hlam t)

private lemma eq_neg_of_ne_of_sign {a b : K} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : a ≠ b) : a = -b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl h
  · simp
  · simp
  · exact absurd rfl h

theorem eq_top_of_comm_unitary_conj (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c) {H : Subgroup (SUid σ n)}
    {A A' : Matrix (Fin n) (Fin n) K} {l : K} (hl : σ l * l = 1) (hAu : (A.map σ)ᵀ * A = 1)
    (hA'u : (A'.map σ)ᵀ * A' = 1) (hA2 : A * A = (l * l) • 1) (hA'2 : A' * A' = (l * l) • 1)
    (hcomm : A * A' = A' * A) (hne : A' ≠ A) (hne' : A' ≠ -A)
    (hH : ∀ g : SUid σ n,
      (A * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : GL (Fin n) K) * A ∨
        A' * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : GL (Fin n) K) * A') →
      g ∈ H) :
    H = ⊤ := by
  classical
  have hσeq : σ = h.barEquiv := RingEquiv.ext hσ
  have hσ' : IsUnitaryInvolution σ := hσeq.symm ▸ h.isUnitaryInvolution_barEquiv
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff (self := h.charP) K p 2).mp h2))
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  let J : Matrix (Fin n) (Fin n) K := l⁻¹ • A
  let J' : Matrix (Fin n) (Fin n) K := l⁻¹ • A'
  have hJJ : J * J = 1 := by
    change (l⁻¹ • A) * (l⁻¹ • A) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, hA2, smul_smul, smul_smul,
      show l⁻¹ * l⁻¹ * (l * l) = 1 by field_simp, one_smul]
  have hJ'J' : J' * J' = 1 := by
    change (l⁻¹ • A') * (l⁻¹ • A') = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, hA'2, smul_smul, smul_smul,
      show l⁻¹ * l⁻¹ * (l * l) = 1 by field_simp, one_smul]
  have hcommJ : J * J' = J' * J := by
    change (l⁻¹ • A) * (l⁻¹ • A') = (l⁻¹ • A') * (l⁻¹ • A)
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hcomm]
  have hscal : σ l⁻¹ * l⁻¹ = 1 := by
    have := congrArg Inv.inv hl
    simpa [map_inv₀, mul_comm] using this
  have hJiso : ∀ x y, herm σ (J *ᵥ x) (J *ᵥ y) = herm σ x y := by
    intro x y
    change herm σ ((l⁻¹ • A) *ᵥ x) ((l⁻¹ • A) *ᵥ y) = herm σ x y
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      herm_mulVec, show conjTr σ A = (A.map σ)ᵀ from rfl, hAu, Matrix.one_mulVec,
      ← mul_assoc, hscal, one_mul]
  have hJ'iso : ∀ x y, herm σ (J' *ᵥ x) (J' *ᵥ y) = herm σ x y := by
    intro x y
    change herm σ ((l⁻¹ • A') *ᵥ x) ((l⁻¹ • A') *ᵥ y) = herm σ x y
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      herm_mulVec, show conjTr σ A' = (A'.map σ)ᵀ from rfl, hA'u, Matrix.one_mulVec,
      ← mul_assoc, hscal, one_mul]
  let B : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ h.bar (RingHom.id K) (fun x y => herm σ x y)
      (fun x x' y => by simp)
      (fun c x y => by rw [herm_smul_left, hσ c, smul_eq_mul])
      (fun x y y' => by simp)
      (fun c x y => by rw [herm_smul_right, RingHom.id_apply, smul_eq_mul])
  have hBapp : ∀ x y : Fin n → K, B x y = herm σ x y := fun x y => rfl
  have hB : B.IsSymm := by
    refine ⟨fun x y => ?_⟩
    rw [hBapp, hBapp, herm_conj σ hσ'.invol x y, ← hσ]
  have hBl : B.SeparatingLeft := by
    intro x hx
    apply eq_zero_of_herm σ
    intro y
    rw [← hBapp]
    exact hx y
  let g : Bool → Module.End K (Fin n → K) := fun b =>
    if b then J.mulVecLin else J'.mulVecLin
  have hcommg : ∀ i j, Commute (g i) (g j) := by
    intro i j
    cases i <;> cases j
    · exact Commute.refl _
    · change J'.mulVecLin.comp J.mulVecLin = J.mulVecLin.comp J'.mulVecLin
      rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hcommJ.symm]
    · change J.mulVecLin.comp J'.mulVecLin = J'.mulVecLin.comp J.mulVecLin
      rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hcommJ]
    · exact Commute.refl _
  have hpowg : ∀ i, g i ^ 2 = 1 := by
    intro i
    cases i
    · change J'.mulVecLin.comp J'.mulVecLin = 1
      rw [← Matrix.mulVecLin_mul, hJ'J', Matrix.mulVecLin_one]
      rfl
    · change J.mulVecLin.comp J.mulVecLin = 1
      rw [← Matrix.mulVecLin_mul, hJJ, Matrix.mulVecLin_one]
      rfl
  have hiso : ∀ i v w, B (g i v) (g i w) = B v w := by
    intro i v w
    cases i
    · have := hJ'iso v w
      simpa [g, B] using this
    · have := hJiso v w
      simpa [g, B] using this
  have hpq : 2 ∣ p ^ f + 1 := by
    have hodd : Odd p := h.prime.odd_of_ne_two hp
    exact even_iff_two_dvd.mp ((hodd.pow (n := f)).add_one)
  have hζ : IsPrimitiveRoot (-1 : K) 2 := @IsPrimitiveRoot.neg_one K _ p _ h.charP hp
  obtain ⟨b, μ, hbμ, hon⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis
      (h := h) (p := 2) (ζ := -1) hζ hpq hB hBl g hcommg hpowg hiso
  let e₀ : Fin (Module.finrank K (Fin n → K)) ≃ Fin n :=
    finCongr (Module.finrank_fin_fun (n := n) K)
  let b' : Module.Basis (Fin n) K (Fin n → K) := b.reindex e₀
  have hb' : ∀ k, b' k = b (e₀.symm k) := fun k => by
    simp [b', Module.Basis.reindex_apply]
  have he : ∀ i j, herm σ (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    have h := hon (e₀.symm i) (e₀.symm j)
    rw [hBapp] at h
    rw [hb' i, hb' j]
    rwa [show (if e₀.symm i = e₀.symm j then (1 : K) else 0) = (if i = j then 1 else 0)
      from by simp [e₀.symm.injective.eq_iff]] at h
  let s : Fin n → K := fun k => μ true (e₀.symm k)
  let s' : Fin n → K := fun k => μ false (e₀.symm k)
  have hJs : ∀ k, J *ᵥ b' k = s k • b' k := by
    intro k
    have h := hbμ true (e₀.symm k)
    have h2 : g true (b (e₀.symm k)) = J *ᵥ b (e₀.symm k) := by
      simp [g]
    rw [h2] at h
    rw [hb' k]
    exact h
  have hJ's : ∀ k, J' *ᵥ b' k = s' k • b' k := by
    intro k
    have h := hbμ false (e₀.symm k)
    have h2 : g false (b (e₀.symm k)) = J' *ᵥ b (e₀.symm k) := by
      simp [g]
    rw [h2] at h
    rw [hb' k]
    exact h
  have hAeq : A = l • J := by
    change A = l • (l⁻¹ • A)
    rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have hA'eq : A' = l • J' := by
    change A' = l • (l⁻¹ • A')
    rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have hAe : ∀ k, A *ᵥ b' k = (l * s k) • b' k := by
    intro k
    rw [hAeq, Matrix.smul_mulVec, hJs k, smul_smul]
  have hA'e : ∀ k, A' *ᵥ b' k = (l * s' k) • b' k := by
    intro k
    rw [hA'eq, Matrix.smul_mulVec, hJ's k, smul_smul]
  have hs2 : ∀ k, s k * s k = 1 := by
    intro k
    have h1 : (s k * s k) • b' k = b' k := by
      rw [← smul_smul, ← hJs k, ← Matrix.mulVec_smul, ← hJs k, Matrix.mulVec_mulVec,
        hJJ, Matrix.one_mulVec]
    have h2 : (s k * s k - 1) • b' k = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · linear_combination h
    · exact absurd h (b'.ne_zero k)
  have hs2' : ∀ k, s' k * s' k = 1 := by
    intro k
    have h1 : (s' k * s' k) • b' k = b' k := by
      rw [← smul_smul, ← hJ's k, ← Matrix.mulVec_smul, ← hJ's k, Matrix.mulVec_mulVec,
        hJ'J', Matrix.one_mulVec]
    have h2 : (s' k * s' k - 1) • b' k = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · linear_combination h
    · exact absurd h (b'.ne_zero k)
  have hsign : ∀ k, s k = 1 ∨ s k = -1 := fun k => mul_self_eq_one_iff.mp (hs2 k)
  have hsign' : ∀ k, s' k = 1 ∨ s' k = -1 := fun k => mul_self_eq_one_iff.mp (hs2' k)
  have hlnorm : ∀ k, σ (l * s k) * (l * s k) = 1 := by
    intro k
    rcases hsign k with hk | hk
    · simpa [hk] using hl
    · simpa [hk, map_neg, neg_mul_neg] using hl
  have hlnorm' : ∀ k, σ (l * s' k) * (l * s' k) = 1 := by
    intro k
    rcases hsign' k with hk | hk
    · simpa [hk] using hl
    · simpa [hk, map_neg, neg_mul_neg] using hl
  have hAiso : ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y := by
    intro x y
    have hAu' : conjTr σ A * A = 1 := by simpa [conjTr] using hAu
    rw [herm_mulVec, hAu', Matrix.one_mulVec]
  have hA'iso : ∀ x y, herm σ (A' *ᵥ x) (A' *ᵥ y) = herm σ x y := by
    intro x y
    have hA'u' : conjTr σ A' * A' = 1 := by simpa [conjTr] using hA'u
    rw [herm_mulVec, hA'u', Matrix.one_mulVec]
  have hpairA : ∀ i j, i ≠ j → s i = s j → ∀ x y : K,
      σ x * x + σ y * y = 0 → USeitz.UCentre H (x • b' i + y • b' j) := by
    intro i j hij hss x y hxy
    refine uCentre_of_eigen (H := H) hAiso (a := x • b' i + y • b' j) (lam := l * s i)
      ?_ (hlnorm i) ?_
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hAe i, hAe j, ← hss]
      module
    · intro g hg
      exact hH g (Or.inl hg)
  have hpairA' : ∀ i j, i ≠ j → s' i = s' j → ∀ x y : K,
      σ x * x + σ y * y = 0 → USeitz.UCentre H (x • b' i + y • b' j) := by
    intro i j hij hss x y hxy
    refine uCentre_of_eigen (H := H) hA'iso (a := x • b' i + y • b' j) (lam := l * s' i)
      ?_ (hlnorm' i) ?_
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hA'e i, hA'e j, ← hss]
      module
    · intro g hg
      exact hH g (Or.inr hg)
  have hpair : ∀ i j, i ≠ j → ∀ x y : K, σ x * x + σ y * y = 0 →
      USeitz.UCentre H (x • b' i + y • b' j) := by
    intro i j hij x y hxy
    by_cases hss : s i = s j
    · exact hpairA i j hij hss x y hxy
    by_cases hss' : s' i = s' j
    · exact hpairA' i j hij hss' x y hxy
    have hsi : s j = - s i := eq_neg_of_ne_of_sign (hsign j) (hsign i) (Ne.symm hss)
    have hs'i : s' j = - s' i :=
      eq_neg_of_ne_of_sign (hsign' j) (hsign' i) (Ne.symm hss')
    have hc_eq : s' j * s j = s' i * s i := by rw [hsi, hs'i, neg_mul_neg]
    by_cases hcase : ∃ k, (s k = s i ∧ s' k = s' j) ∨ (s k = s j ∧ s' k = s' i)
    · obtain ⟨k, hk | hk⟩ := hcase
      · obtain ⟨hsk, hsk'⟩ := hk
        have hik : i ≠ k := by
          intro h
          exact hss' (by rw [h, hsk'])
        have hkj : k ≠ j := by
          intro h
          exact hss (by rw [← hsk, h])
        have hx : herm σ (b' i) (b' i) = 1 := by rw [he, if_pos rfl]
        have hz : herm σ (b' k) (b' k) = 1 := by rw [he, if_pos rfl]
        have hxz : herm σ (b' i) (b' k) = 0 := by rw [he, if_neg hik]
        obtain ⟨t, ht, htx, hfix⟩ := USeitz.exists_mem_of_orthonormal hσ'
          (H := H) (x := b' i) (z := b' k) hx hz hxz
          (fun α β hαβ => hpairA i k hik hsk.symm α β hαβ) 0 1 (by simp)
        have htx' : t • b' i = b' k := by simpa using htx
        have htj : t • b' j = b' j := by
          refine hfix (b' j) ?_ ?_
          · rw [he, if_neg hij]
          · rw [he, if_neg hkj]
        have hts : t • (x • b' i + y • b' j) = x • b' k + y • b' j := by
          rw [smul_add, smul_comm t x (b' i), smul_comm t y (b' j), htx', htj]
        have hcenter : USeitz.UCentre H (x • b' k + y • b' j) :=
          hpairA' k j hkj hsk' x y hxy
        refine USeitz.uCentre_of_smul ht ?_
        rwa [hts]
      · obtain ⟨hsk, hsk'⟩ := hk
        have hjk : j ≠ k := by
          intro h
          exact hss' (by rw [h, hsk'])
        have hik : i ≠ k := by
          intro h
          exact hss (by rw [h, hsk])
        have hx : herm σ (b' j) (b' j) = 1 := by rw [he, if_pos rfl]
        have hz : herm σ (b' k) (b' k) = 1 := by rw [he, if_pos rfl]
        have hxz : herm σ (b' j) (b' k) = 0 := by rw [he, if_neg hjk]
        obtain ⟨t, ht, htx, hfix⟩ := USeitz.exists_mem_of_orthonormal hσ'
          (H := H) (x := b' j) (z := b' k) hx hz hxz
          (fun α β hαβ => hpairA j k hjk hsk.symm α β hαβ) 0 1 (by simp)
        have htx' : t • b' j = b' k := by simpa using htx
        have hti : t • b' i = b' i := by
          refine hfix (b' i) ?_ ?_
          · rw [he, if_neg hij.symm]
          · rw [he, if_neg (Ne.symm hik)]
        have hts : t • (x • b' i + y • b' j) = x • b' i + y • b' k := by
          rw [smul_add, smul_comm t x (b' i), smul_comm t y (b' j), hti, htx']
        have hcenter : USeitz.UCentre H (x • b' i + y • b' k) :=
          hpairA' i k hik hsk'.symm x y hxy
        refine USeitz.uCentre_of_smul ht ?_
        rwa [hts]
    · exfalso
      have hprod : ∀ k, s' k * s k = s' i * s i := by
        intro k
        by_cases h1 : s k = s i
        · by_cases h2 : s' k = s' i
          · rw [h1, h2]
          · exact absurd ⟨k, Or.inl ⟨h1, by
              rw [eq_neg_of_ne_of_sign (hsign' k) (hsign' i) h2,
                ← eq_neg_of_ne_of_sign (hsign' j) (hsign' i) (Ne.symm hss')]⟩⟩ hcase
        · have hsk : s k = s j := by
            rw [eq_neg_of_ne_of_sign (hsign k) (hsign i) h1,
              ← eq_neg_of_ne_of_sign (hsign j) (hsign i) (Ne.symm hss)]
          by_cases h2 : s' k = s' i
          · exact absurd ⟨k, Or.inr ⟨hsk, h2⟩⟩ hcase
          · have hsk' : s' k = s' j := by
              rw [eq_neg_of_ne_of_sign (hsign' k) (hsign' i) h2,
                ← eq_neg_of_ne_of_sign (hsign' j) (hsign' i) (Ne.symm hss')]
            rw [hsk, hsk', hc_eq]
      have hck : ∀ k, (s' i * s i) * s k = s' k := by
        intro k
        rw [← hprod k, mul_assoc, hs2 k, mul_one]
      have hA'c : A' = (s' i * s i) • A := by
        apply Matrix.toLin'.injective
        refine b'.ext fun k => ?_
        simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply]
        rw [hA'e k, Matrix.smul_mulVec, hAe k, smul_smul, ← hck k]
        congr 1
        ring
      have hc2 : (s' i * s i) * (s' i * s i) = 1 := by
        calc (s' i * s i) * (s' i * s i) = (s' i * s' i) * (s i * s i) := by ring
          _ = 1 := by rw [hs2' i, hs2 i, one_mul]
      rcases mul_self_eq_one_iff.mp hc2 with hc | hc
      · exact hne (by rw [hA'c, hc, one_smul])
      · exact hne' (by rw [hA'c, hc, neg_one_smul])
  have hrepr : ∀ (v : Fin n → K) (i : Fin n), b'.repr v i = herm σ (b' i) v := by
    intro v i
    have h := USeitz.herm_lc_right he i (fun k => b'.repr v k)
    rw [show USeitz.lc b' (fun k => b'.repr v k) = v by
      rw [USeitz.lc, Module.Basis.sum_repr]] at h
    exact h.symm
  have hc' : ∀ c : Fin n → K, c = USeitz.lc b' (fun i => herm σ (b' i) c) := by
    intro c
    conv_lhs => rw [← Module.Basis.sum_repr b' c]
    rw [USeitz.lc]
    exact Finset.sum_congr rfl fun i _ => by rw [hrepr c i]
  have hcentres : ∀ c : Fin n → K, herm σ c c = 0 → USeitz.UCentre H c := by
    intro c hcc
    have hf : ∑ i, σ (herm σ (b' i) c) * herm σ (b' i) c = 0 := by
      rw [← USeitz.herm_lc he (fun i => herm σ (b' i) c) (fun i => herm σ (b' i) c)]
      rw [← hc' c]
      exact hcc
    have h := USeitz.uCentre_lc hσ' h2K he hpair (fun i => herm σ (b' i) c) hf
    rwa [← hc' c] at h
  have hTle : T σ n ≤ H := USeitz.T_le_of_uCentre hcentres
  have h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1 := by
    intro _
    obtain ⟨u, hu⟩ := hσ'.exists_norm_neg_one
    refine ⟨u, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero, zero_mul] at hu
      have h1 : (1 : K) = 0 := by linear_combination hu
      exact one_ne_zero h1
    · rw [hu]
      intro h
      have h2 : (2 : K) = 0 := by linear_combination -h
      exact h2K h2
  have hTtop : T σ n = ⊤ := T_eq_top hσ' (by omega) h3
  rw [eq_top_iff, ← hTtop]
  exact hTle

end CFSG.LocalAnalysis.WeakClosure81.UOuter
