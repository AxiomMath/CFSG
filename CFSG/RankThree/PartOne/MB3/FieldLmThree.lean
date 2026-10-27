module

public import CFSG.RankThree.PartOne.S11c.SuFiveFixed
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Module CFSG.RankThree.PartOne.KFSU5

variable {F : Type} [Field F] [Finite F]

theorem charTwo_of_card (hF : Nat.card F = 2 ^ 7) : CharP F 2 := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (p := 2) (f := 7) (by rw [← Nat.card_eq_fintype_card, hF])

theorem eq_one_of_fixes_e0 (hF : Nat.card F = 2 ^ 7) {M : Matrix (Fin 3) (Fin 3) F}
    (hdet : M.det = 1) (hM7 : M ^ 7 = 1) (he : M *ᵥ (Pi.single 0 1) = Pi.single 0 1) : M = 1 := by
  classical
  have := Fintype.ofFinite F
  have hchar : CharP F 2 := charTwo_of_card hF
  let e : Fin 1 ⊕ Fin 2 ≃ Fin 3 := finSumFinEquiv
  let R : Matrix (Fin 3) (Fin 3) F ≃ₐ[F] Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) F :=
    Matrix.reindexAlgEquiv F F e.symm
  have hN7 : R M ^ 7 = 1 := by rw [← map_pow, hM7, map_one]
  have hNdet : (R M).det = 1 := (Matrix.det_reindexAlgEquiv F F e.symm M).trans hdet
  have hcol : ∀ i : Fin 3, M i 0 = (Pi.single 0 1 : Fin 3 → F) i := by
    intro i
    have := congrFun he i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have he0 : e (Sum.inl 0) = 0 := by decide
  have he1 : e (Sum.inr 0) = 1 := by decide
  have he2 : e (Sum.inr 1) = 2 := by decide
  have hRM : ∀ x y, R M x y = M (e x) (e y) := fun x y => by
    simp [R, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  have hA : (R M).toBlocks₁₁ = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.toBlocks₁₁, hRM, he0, hcol]
  have hC : (R M).toBlocks₂₁ = 0 := by
    ext i j
    fin_cases j
    fin_cases i
    · simp [Matrix.toBlocks₂₁, hRM, he0, he1, hcol]
    · simp [Matrix.toBlocks₂₁, hRM, he0, he2, hcol]
  set N := R M with hNdef
  set D := N.toBlocks₂₂ with hD
  set B := N.toBlocks₁₂ with hB
  have hNblocks : N = fromBlocks 1 B 0 D := by
    have := fromBlocks_toBlocks N
    rw [hA, hC] at this
    exact this.symm
  have hpow : ∀ k : ℕ, ∃ Bk : Matrix (Fin 1) (Fin 2) F, N ^ k = fromBlocks 1 Bk 0 (D ^ k) := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp [fromBlocks_one]⟩
    | succ k ih =>
      obtain ⟨Bk, hBk⟩ := ih
      refine ⟨B + Bk * D, ?_⟩
      rw [pow_succ, hBk, hNblocks]
      simp [fromBlocks_multiply, pow_succ]
  obtain ⟨B7, hB7⟩ := hpow 7
  have hD7 : D ^ 7 = 1 := by
    rw [hN7] at hB7
    have h1 : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0 (1 : Matrix (Fin 2) (Fin 2) F) :
        Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) F) = 1 := fromBlocks_one
    rw [← h1] at hB7
    exact (fromBlocks_inj.mp hB7).2.2.2.symm
  have hDdet : D.det = 1 := by
    rw [hNblocks, det_fromBlocks_zero₂₁] at hNdet
    simpa using hNdet
  let Dsl : SpecialLinearGroup (Fin 2) F := ⟨D, hDdet⟩
  have hDsl7 : Dsl ^ 7 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]; exact hD7)
  have hDsl1 : Dsl = 1 := by
    have h1 : orderOf Dsl ∣ 7 := orderOf_dvd_of_pow_eq_one hDsl7
    have h2 : orderOf Dsl ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := orderOf_dvd_natCard Dsl
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF] at h2
    have h3 : Nat.Coprime 7 (2 ^ 7 * ((2 ^ 7) ^ 2 - 1)) := by decide
    have := Nat.eq_one_of_dvd_coprimes h3 h1 h2
    exact orderOf_eq_one_iff.mp this
  have hD1 : D = 1 := congrArg Subtype.val hDsl1
  have hN2 : N ^ 2 = 1 := by
    have hBB : B + B = 0 := by
      ext i j
      simp [CharTwo.add_self_eq_zero]
    rw [pow_two, hNblocks, hD1, fromBlocks_multiply]
    simp [hBB, fromBlocks_one]
  have hN1 : N = 1 := by
    have : N ^ 7 = N := by
      rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul, hN2, one_pow, one_mul]
    rw [← this, hN7]
  have : R M = R 1 := by rw [map_one]; exact hN1
  exact R.injective this

omit [Finite F] in
theorem exists_unit_mulVec_e0 {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ P : GL (Fin 3) F, ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1) = v := by
  classical
  by_cases h0 : v 0 ≠ 0
  · refine ⟨Matrix.GeneralLinearGroup.mk'' !![v 0, 0, 0; v 1, 1, 0; v 2, 0, 1] ?_, ?_⟩
    · simp [Matrix.det_fin_three, h0]
    · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  by_cases h1 : v 1 ≠ 0
  · refine ⟨Matrix.GeneralLinearGroup.mk'' !![v 0, 1, 0; v 1, 0, 0; v 2, 0, 1] ?_, ?_⟩
    · simp [Matrix.det_fin_three, h1]
    · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : v 2 ≠ 0 := by
    intro h2
    apply hv
    push Not at h0 h1
    ext i; fin_cases i <;> simp [h0, h1, h2]
  refine ⟨Matrix.GeneralLinearGroup.mk'' !![v 0, 1, 0; v 1, 0, 1; v 2, 0, 0] ?_, ?_⟩
  · simp [Matrix.det_fin_three, h2]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem eq_one_of_fixes_vector (hF : Nat.card F = 2 ^ 7) {g : GL (Fin 3) F}
    (hdet : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1) (hg7 : g ^ 7 = 1)
    {v : Fin 3 → F} (hv : v ≠ 0) (hgv : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    g = 1 := by
  obtain ⟨P, hP⟩ := exists_unit_mulVec_e0 hv
  set g' : GL (Fin 3) F := P⁻¹ * g * P with hg'
  have hdet' : ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det g' = Matrix.GeneralLinearGroup.det g := by
      rw [hg', map_mul, map_mul, map_inv]
      simp [mul_comm]
    have h2 := congrArg (fun u : Fˣ => (u : F)) h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply, hdet] using h2
  have hg'7 : g' ^ 7 = 1 := by
    rw [hg', show P⁻¹ * g * P = P⁻¹ * g * P⁻¹⁻¹ by simp, conj_pow, hg7]
    simp
  have hfix : ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 := by
    have hPinv : ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = Pi.single 0 1 := by
      rw [← hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hg', Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hgv,
      hPinv]
  have := eq_one_of_fixes_e0 hF hdet' (by rw [← Units.val_pow_eq_pow_val, hg'7, Units.val_one]) hfix
  have hg'1 : g' = 1 := Units.ext this
  have : g = P * g' * P⁻¹ := by rw [hg']; group
  rw [this, hg'1]; group


omit [Finite F] in
theorem exists_eigenvector_of_invariant {M : Matrix (Fin 3) (Fin 3) F}
    {W : Submodule F (Fin 3 → F)} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hinv : ∀ w ∈ W, M *ᵥ w ∈ W) : ∃ x : Fin 3 → F, x ≠ 0 ∧ ∃ μ : F, M *ᵥ x = μ • x := by
  classical
  have hfin : finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  have hlt : finrank F W < 3 := by
    have := Submodule.finrank_lt hW1
    rwa [hfin] at this
  have hpos : 0 < finrank F W := by
    rcases Nat.eq_zero_or_pos (finrank F W) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hW0
    · exact h
  rcases (by omega : finrank F W = 1 ∨ finrank F W = 2) with h1 | h2
  ·
    obtain ⟨w, hw0, hgen⟩ := finrank_eq_one_iff'.mp h1
    obtain ⟨c, hc⟩ := hgen ⟨M *ᵥ (w : Fin 3 → F), hinv w w.2⟩
    refine ⟨(w : Fin 3 → F), fun h => hw0 (Subtype.ext h), c, ?_⟩
    exact (congrArg Subtype.val hc).symm
  ·
    obtain ⟨u, hu⟩ : ∃ u : Fin 3 → F, u ∉ W := by
      by_contra hcon
      push Not at hcon
      exact hW1 (eq_top_iff.mpr fun x _ => hcon x)
    have hspan : finrank F (Submodule.span F {u}) = 1 :=
      finrank_span_singleton (fun h => hu (h ▸ W.zero_mem))
    have hinf : W ⊓ Submodule.span F {u} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxW, hxu⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxu
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd (by simpa [smul_smul, hc] using W.smul_mem c⁻¹ hxW) hu
    have hsup : W ⊔ Submodule.span F {u} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F {u})
      rw [hinf, finrank_bot, hspan, h2] at this
      rw [hfin]
      omega
    have hMu : M *ᵥ u ∈ W ⊔ Submodule.span F {u} := by rw [hsup]; trivial
    obtain ⟨w₀, hw₀, y, hy, hMuy⟩ := Submodule.mem_sup.mp hMu
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
    let f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.toLin' M - μ • LinearMap.id
    have hrange : ∀ x, f x ∈ W := by
      intro x
      have hx : x ∈ W ⊔ Submodule.span F {u} := by rw [hsup]; trivial
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hfx : f (w + c • u) = (M *ᵥ w - μ • w) + c • w₀ := by
        simp only [f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_smul, ← hMuy]
        module
      rw [hfx]
      exact W.add_mem (W.sub_mem (hinv w hw) (W.smul_mem μ hw)) (W.smul_mem c hw₀)
    have hker : LinearMap.ker f ≠ ⊥ := by
      intro hbot
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
      have hsurj := LinearMap.injective_iff_surjective.mp hinj
      obtain ⟨x, hx⟩ := hsurj u
      exact hu (hx ▸ hrange x)
    obtain ⟨x, hxk, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
    refine ⟨x, hx0, μ, ?_⟩
    have : f x = 0 := hxk
    simpa [f, sub_eq_zero, Matrix.toLin'_apply] using this

theorem eigenvalue_eq_one (hF : Nat.card F = 2 ^ 7) {g : GL (Fin 3) F} (hg7 : g ^ 7 = 1)
    {v : Fin 3 → F} (hv : v ≠ 0) {μ : F}
    (hgv : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = μ • v) : μ = 1 := by
  classical
  have := Fintype.ofFinite F
  have hpow : ∀ k : ℕ, (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]
  have h7 := hpow 7
  have hg7' : (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 7) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg7, Units.val_one]
  rw [hg7', Matrix.one_mulVec] at h7
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hμ7 : μ ^ 7 = 1 := by
    have := congrFun h7 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_left_eq_self₀.mp this.symm).resolve_right hi
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ7
  have h127 : μ ^ 127 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card, hF] at this
  have := pow_gcd_eq_one.mpr ⟨hμ7, h127⟩
  rwa [show Nat.gcd 7 127 = 1 by norm_num, pow_one] at this

theorem no_eigenvector (hF : Nat.card F = 2 ^ 7) {g : GL (Fin 3) F}
    (hdet : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1) (hg7 : g ^ 7 = 1)
    (hg1 : g ≠ 1) {x : Fin 3 → F} (hx : x ≠ 0) {μ : F}
    (hgx : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = μ • x) : False := by
  have hμ := eigenvalue_eq_one hF hg7 hx hgx
  rw [hμ, one_smul] at hgx
  exact hg1 (eq_one_of_fixes_vector hF hdet hg7 hx hgx)

theorem fieldLm_ne_three {G : Type} [Group G] {K S : Subgroup G} {d : G}
    (hF : Nat.card F = 2 ^ 7) (φ : ↥K ≃* SpecialLinearGroup (Fin 3) F) (hSK : S ≤ K)
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hdK : d ∈ K) (hd7 : orderOf d = 7)
    (hdS : d ∈ Subgroup.normalizer (S : Set G)) : False := by
  classical
  have hF2 : 2 ∣ Nat.card F := by rw [hF]; exact dvd_pow_self 2 (by norm_num)
  let ι : ↥K →* GL (Fin 3) F := SpecialLinearGroup.toGL.comp φ.toMonoidHom
  have hι : Function.Injective ι :=
    SpecialLinearGroup.toGL_injective.comp φ.injective
  let S' : Subgroup (GL (Fin 3) F) := (S.subgroupOf K).map ι
  have hS'2 : IsPGroup 2 S' := (hS2.comap_subtype (K := K)).map ι
  have hS'1 : S' ≠ ⊥ := by
    intro hbot
    apply hS1
    rw [eq_bot_iff]
    intro s hs
    have hsK : s ∈ K := hSK hs
    have h1 : ι ⟨s, hsK⟩ ∈ S' := ⟨⟨s, hsK⟩, hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨s, hsK⟩ : K) = 1 := hι (h1.trans ι.map_one.symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  obtain ⟨v, hvfix, hv0⟩ := exists_ne_zero_mem_fixSub (n := 3) (by norm_num) hF2 hS'2
  have hW0 : fixSub S' ≠ ⊥ := fun h => hv0 (by
    have := hvfix
    rw [h] at this
    exact (Submodule.mem_bot F).mp this)
  have hW1 : fixSub S' ≠ ⊤ := fun h => hS'1 (eq_bot_of_fixSub_eq_top h)
  let d₀ : ↥K := ⟨d, hdK⟩
  let d' : GL (Fin 3) F := ι d₀
  have hconj : ∀ s ∈ S', d'⁻¹ * s * d' ∈ S' := by
    rintro _ ⟨s₀, hs₀, rfl⟩
    refine ⟨d₀⁻¹ * s₀ * d₀, ?_, by simp [d', map_mul, map_inv]⟩
    have hs0 : (s₀ : G) ∈ S := hs₀
    have : d⁻¹ * (s₀ : G) * d ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdS) (s₀ : G)).mp hs0
      simpa using this
    exact this
  have hinv : ∀ w ∈ fixSub S', ((d' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ fixSub S' :=
    fun w hw => mulVec_mem_fixSub_of_inv_conj hconj hw
  obtain ⟨x, hx0, μ, hxμ⟩ := exists_eigenvector_of_invariant hW0 hW1 hinv
  have hd7' : d₀ ^ 7 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one d
    rw [hd7] at this
    simpa using this
  have hd'7 : d' ^ 7 = 1 := by rw [← map_pow, hd7', map_one]
  have hd'1 : d' ≠ 1 := by
    intro h
    have : d₀ = 1 := hι (h.trans ι.map_one.symm)
    have hd1 : d = 1 := congrArg Subtype.val this
    rw [hd1, orderOf_one] at hd7
    omega
  have hdet : ((d' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := (φ d₀).2
  exact no_eigenvector hF hdet hd'7 hd'1 hx0 hxμ

end CFSG.RankThree.PartOne.MB3
