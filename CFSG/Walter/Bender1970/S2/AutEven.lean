module

public import CFSG.Walter.Bender1970.S2.Basic
import CFSG.Walter.PSL2Facts.Even
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.Walter

open scoped MatrixGroups Pointwise

section PSL2Even

variable {f : ℕ}

theorem psl2_even_sylow_inf_eq_bot (hf : 2 ≤ f) {P P' : Sylow 2 PSL(2, GaloisField 2 f)}
    (h : P ≠ P') : (P : Subgroup PSL(2, GaloisField 2 f)) ⊓ P' = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxP'⟩
  rw [Subgroup.mem_bot]
  by_contra hx1
  apply h
  have h1 := psl2_even_centralizer_involution hf P hxP hx1
  have h2 := psl2_even_centralizer_involution hf P' hxP' hx1
  exact Sylow.ext (h1.symm.trans h2)

theorem psl2_even_normalizer_inf_eq_bot (hf : 2 ≤ f) {P P' : Sylow 2 PSL(2, GaloisField 2 f)}
    (h : P ≠ P') : Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f)) ⊓ P' = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxP'⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    P'.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxP')
  have hsup := hx2.to_sup_of_normal_right' P.isPGroup' (Subgroup.zpowers_le.mpr hxN)
  have hle := P.is_maximal' hsup le_sup_right
  have hxP : x ∈ (P : Subgroup PSL(2, GaloisField 2 f)) := by
    rw [← hle]
    exact (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
  rw [← psl2_even_sylow_inf_eq_bot hf h]
  exact ⟨hxP, hxP'⟩

theorem psl2_even_mulAut_eq_one (hf : 2 ≤ f) (φ : MulAut PSL(2, GaloisField 2 f))
    (hφ : Odd (orderOf φ)) (S : Sylow 2 PSL(2, GaloisField 2 f))
    (hφS : ∀ x ∈ (S : Subgroup PSL(2, GaloisField 2 f)), φ x = x) : φ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := PSL(2, GaloisField 2 f) with hLdef
  have hf0 : f ≠ 0 := by omega
  have hcomm' : ∀ (g : L) (P : Sylow 2 L), φ • (g • P) = (φ g) • (φ • P) := by
    intro g P
    apply Sylow.ext
    ext x
    rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
      Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have key : (MulAut.conj g)⁻¹ • (φ⁻¹ • x) = φ⁻¹ • ((MulAut.conj (φ g))⁻¹ • x) := by
      simp only [MulAut.smul_def, MulAut.conj_inv_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [key]
  have hcomm : ∀ s ∈ (S : Subgroup L), ∀ P : Sylow 2 L, φ • (s • P) = s • (φ • P) := by
    intro s hs P
    rw [hcomm', hφS s hs]
  have hφS' : φ • S = S := by
    apply Sylow.ext
    ext x
    rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
    constructor
    · intro hx
      have h1 := hφS _ hx
      rw [MulAut.apply_inv_self] at h1
      rw [h1]
      exact hx
    · intro hx
      have h1 := hφS _ hx
      have h2 : φ⁻¹ x = x := by
        conv_lhs => rw [← h1]
        exact MulAut.inv_apply_self _ φ x
      rw [h2]
      exact hx
  have hφS'' : φ⁻¹ • S = S := by
    conv_lhs => rw [← hφS']
    rw [inv_smul_smul]
  have horbit : ∀ P₀ : Sylow 2 L, P₀ ≠ S → ∀ P : Sylow 2 L, P ≠ S →
      ∃ s ∈ (S : Subgroup L), s • P₀ = P := by
    intro P₀ hP₀
    have hne : ∀ s ∈ (S : Subgroup L), s • P₀ ≠ S := by
      intro s hs h
      apply hP₀
      have h1 : s⁻¹ • S = S :=
        Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ((S : Subgroup L).inv_mem hs))
      calc P₀ = s⁻¹ • (s • P₀) := (inv_smul_smul s P₀).symm
        _ = s⁻¹ • S := by rw [h]
        _ = S := h1
    let g : ↥(S : Subgroup L) → {P : Sylow 2 L // P ≠ S} := fun s =>
      ⟨(s : L) • P₀, hne s s.2⟩
    have hg : Function.Injective g := by
      intro s s' hss'
      have h1 : (s : L) • P₀ = (s' : L) • P₀ := congrArg Subtype.val hss'
      have h2 : ((s' : L)⁻¹ * s) • P₀ = P₀ := by rw [mul_smul, h1, inv_smul_smul]
      rw [Sylow.smul_eq_iff_mem_normalizer] at h2
      have h3 : (s' : L)⁻¹ * s ∈ Subgroup.normalizer ((P₀ : Subgroup L) : Set L) ⊓ S :=
        ⟨h2, (S : Subgroup L).mul_mem ((S : Subgroup L).inv_mem s'.2) s.2⟩
      rw [psl2_even_normalizer_inf_eq_bot hf hP₀, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact Subtype.ext h3.symm
    have hcardS : Nat.card (S : Subgroup L) = 2 ^ f := (psl2_even_sylow_two hf S).2
    have hcardP : Nat.card {P : Sylow 2 L // P ≠ S} = 2 ^ f := by
      have h1 := psl2_even_card_sylow hf0
      have : Fintype (Sylow 2 L) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card] at h1 ⊢
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h1]
      omega
    have hbij : Function.Bijective g :=
      hg.bijective_of_nat_card_le (by rw [hcardS, hcardP])
    intro P hP
    obtain ⟨s, hs⟩ := hbij.2 ⟨P, hP⟩
    exact ⟨s, s.2, congrArg Subtype.val hs⟩
  have hφP : ∀ P : Sylow 2 L, φ • P = P := by
    intro P₀
    by_cases hP₀ : P₀ = S
    · rw [hP₀]
      exact hφS'
    have hφP₀ : φ • P₀ ≠ S := by
      intro h
      apply hP₀
      calc P₀ = φ⁻¹ • (φ • P₀) := (inv_smul_smul φ P₀).symm
        _ = φ⁻¹ • S := by rw [h]
        _ = S := hφS''
    obtain ⟨s₀, hs₀, hs₀eq⟩ := horbit P₀ hP₀ (φ • P₀) hφP₀
    have hpow : ∀ k : ℕ, (φ ^ k) • P₀ = (s₀ ^ k) • P₀ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_smul, ih, hcomm _ ((S : Subgroup L).pow_mem hs₀ k), ← hs₀eq,
          ← mul_smul, ← pow_succ]
    have h1 := hpow (orderOf φ)
    rw [pow_orderOf_eq_one, one_smul] at h1
    have h2 : s₀ ^ orderOf φ ∈ Subgroup.normalizer ((P₀ : Subgroup L) : Set L) ⊓ S :=
      ⟨Sylow.smul_eq_iff_mem_normalizer.mp h1.symm, (S : Subgroup L).pow_mem hs₀ _⟩
    rw [psl2_even_normalizer_inf_eq_bot hf hP₀, Subgroup.mem_bot] at h2
    have h3 : s₀ = 1 := by
      have hdvd : orderOf s₀ ∣ orderOf φ := orderOf_dvd_of_pow_eq_one h2
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨s₀, hs₀⟩
      rw [Subgroup.orderOf_mk] at hk
      rw [hk] at hdvd
      have hk0 : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hφ)
          (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    rw [← hs₀eq, h3, one_smul]
  have hfix : ∀ τ : L, orderOf τ = 2 → φ τ = τ := by
    intro τ hτ
    by_cases hτS : τ ∈ (S : Subgroup L)
    · exact hφS τ hτS
    have hτp : IsPGroup 2 (Subgroup.zpowers τ) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ, pow_one])
    obtain ⟨P, hP⟩ := hτp.exists_le_sylow
    have hτP : τ ∈ (P : Subgroup L) := hP (Subgroup.mem_zpowers τ)
    have hSP : S ≠ P := fun h => hτS (h ▸ hτP)
    have h1 : φ τ ∈ (P : Subgroup L) := by
      have : φ τ ∈ ((φ • P : Sylow 2 L) : Subgroup L) := by
        rw [Sylow.pointwise_smul_def]
        exact Subgroup.smul_mem_pointwise_smul τ φ _ hτP
      rwa [hφP P] at this
    have h2 : (τ⁻¹ * φ τ) • S = S := by
      have h3 := hcomm' τ S
      rw [hφP, hφS'] at h3
      rw [mul_smul, ← h3, inv_smul_smul]
    rw [Sylow.smul_eq_iff_mem_normalizer] at h2
    have h4 : τ⁻¹ * φ τ ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) ⊓ P :=
      ⟨h2, (P : Subgroup L).mul_mem ((P : Subgroup L).inv_mem hτP) h1⟩
    rw [psl2_even_normalizer_inf_eq_bot hf hSP, Subgroup.mem_bot, inv_mul_eq_one] at h4
    exact h4.symm
  have : IsSimpleGroup L := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [GaloisField.card 2 f hf0]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
  have hI : Subgroup.normalClosure {x : L | orderOf x = 2} ≤
      φ.toMonoidHom.eqLocus (MonoidHom.id L) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    have hy2 : orderOf y = 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hxy
      have h1 := MulEquiv.orderOf_eq (MulAut.conj c) x
      rw [MulAut.conj_apply, hc] at h1
      rw [h1]
      exact hx
    exact hfix y hy2
  have hne : Subgroup.normalClosure {x : L | orderOf x = 2} ≠ ⊥ := by
    obtain ⟨hSel, hScard⟩ := psl2_even_sylow_two hf S
    have : Nontrivial (S : Subgroup L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hScard]
      exact Nat.one_lt_two_pow hf0
    obtain ⟨⟨s, hs⟩, hs1⟩ := exists_ne (1 : (S : Subgroup L))
    have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hso : orderOf s = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (S : Subgroup L)) s hs) hs1'
    intro h
    apply hs1'
    have : s ∈ Subgroup.normalClosure {x : L | orderOf x = 2} :=
      Subgroup.subset_normalClosure hso
    rwa [h, Subgroup.mem_bot] at this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure {x : L | orderOf x = 2}) with h | h
  · exact absurd h hne
  · apply MulEquiv.ext
    intro x
    have hx : x ∈ φ.toMonoidHom.eqLocus (MonoidHom.id L) := hI (h ▸ Subgroup.mem_top x)
    exact hx

end PSL2Even

theorem IsTypeL2Even.mulAut_eq_one {L : Type*} [Group L] [Finite L] (hL : IsTypeL2Even L)
    (φ : MulAut L) (hφ : Odd (orderOf φ)) (S : Sylow 2 L)
    (hφS : ∀ x ∈ (S : Subgroup L), φ x = x) : φ = 1 := by
  obtain ⟨f, hf, ⟨e⟩⟩ := hL
  set ψ := MulAut.congr e with hψ
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  have h1 : ψ φ = 1 := by
    refine psl2_even_mulAut_eq_one hf (ψ φ) (by rwa [MulEquiv.orderOf_eq])
      (S.mapSurjective hes) ?_
    intro x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hψ, MulAut.congr_apply]
    simp [hφS y hy]
  have h2 := congrArg ψ.symm h1
  rwa [MulEquiv.symm_apply_apply, map_one] at h2

end CFSG.Walter
