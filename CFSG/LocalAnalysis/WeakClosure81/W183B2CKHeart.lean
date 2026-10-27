module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKTensor
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKLine
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKFrob
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct

private lemma w183b2_map_sub_left {k : Type} [CommRing k] {M N : Type} [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] (f f' : Module.End k M) (g : Module.End k N) :
    TensorProduct.map (f - f') g = TensorProduct.map f g - TensorProduct.map f' g := by
  have hneg : -f' = (-1 : k) • f' := by simp
  rw [sub_eq_add_neg, TensorProduct.map_add_left, sub_eq_add_neg, hneg,
    TensorProduct.map_smul_left]
  congr 1
  exact neg_one_smul (R := k) (TensorProduct.map f' g)

private lemma w183b2_map_sub_right {k : Type} [CommRing k] {M N : Type} [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] (f : Module.End k M) (g g' : Module.End k N) :
    TensorProduct.map f (g - g') = TensorProduct.map f g - TensorProduct.map f g' := by
  have hneg : -g' = (-1 : k) • g' := by simp
  rw [sub_eq_add_neg, TensorProduct.map_add_right, sub_eq_add_neg, hneg,
    TensorProduct.map_smul_right]
  congr 1
  exact neg_one_smul (R := k) (TensorProduct.map f g')

private lemma w183b2_smul_one_eq_one {k U : Type} [Field k] [AddCommGroup U] [Module k U]
    [Nontrivial U] {c : k} (h : c • (1 : Module.End k U) = 1) : c = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : U)
  have hcv : c • v = v := by
    simpa using congrArg (fun f : Module.End k U => f v) h
  have hz : (c - 1) • v = 0 := by rw [sub_smul, one_smul, hcv, sub_self]
  rcases (smul_eq_zero.mp hz) with h0 | hv0
  · exact sub_eq_zero.mp h0
  · exact absurd hv0 hv

private lemma w183b2_eq_one_of_mul_self {k : Type} [Field k] [CharP k 2] {c : k}
    (h : c * c = 1) : c = 1 := by
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

private lemma w183b2_tensor_mul_eq_map_left {k U₁ U₂ : Type} [Field k] [AddCommGroup U₁]
    [Module k U₁] [FiniteDimensional k U₁] [AddCommGroup U₂] [Module k U₂]
    [FiniteDimensional k U₂] {b : Module.End k U₂} (hb : b ≠ 0) {X Y : Module.End k U₁}
    (h : TensorProduct.map X b = TensorProduct.map Y b) : X = Y := by
  have hsub : TensorProduct.map (X - Y) b = 0 := by
    rw [w183b2_map_sub_left, h, sub_self]
  by_contra hne
  have hne' : X - Y ≠ 0 := sub_ne_zero.mpr hne
  have h0 : TensorProduct.map (X - Y) b = TensorProduct.map 0 b := by
    rw [hsub, TensorProduct.map_zero_left]
  obtain ⟨c, hc, h1, _⟩ := w183b2_map_eq_map hne' hb h0
  have hXY : X - Y = 0 := by
    rcases (smul_eq_zero.mp h1.symm) with hc0 | hXY
    · exact absurd hc0 hc
    · exact hXY
  exact hne' hXY

theorem w183b2_core_tensor {k : Type} [Field k] [IsAlgClosed k] [CharP k 2] {Δ : Type} [Group Δ]
    [Finite Δ] (hΔ : ∀ d : Δ, d * d = 1) {U₁ U₂ : Type} [AddCommGroup U₁] [Module k U₁]
    [FiniteDimensional k U₁] [Nontrivial U₁] [AddCommGroup U₂] [Module k U₂]
    [FiniteDimensional k U₂] [Nontrivial U₂] (T : Δ →* Module.End k (U₁ ⊗[k] U₂))
    (hinj : ∀ d, T d = 1 → d = 1) (hquad : ∀ d e, (T d - 1) * (T e - 1) = 0)
    (hn₁ : ∀ d (X : Module.End k U₁), ∃ X' : Module.End k U₁,
      T d * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T d)
    (hn₂ : ∀ d (Y : Module.End k U₂), ∃ Y' : Module.End k U₂,
      T d * TensorProduct.map LinearMap.id Y = TensorProduct.map LinearMap.id Y' * T d)
    (hc₁ : ∃ e, ∃ X : Module.End k U₁,
      T e * TensorProduct.map X LinearMap.id ≠ TensorProduct.map X LinearMap.id * T e)
    (hc₂ : ∃ e, ∃ Y : Module.End k U₂,
      T e * TensorProduct.map LinearMap.id Y ≠ TensorProduct.map LinearMap.id Y * T e)
    (hF : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U₁) (F : Subfield k) (S : Set (Module.End k U₁)),
      Finite F ∧ Nat.card F ≤ 4 ∧ Submodule.span k S = ⊤ ∧
      (∀ s ∈ S, ∀ i j, LinearMap.toMatrix b b s i j ∈ F) ∧
      ∀ d, ∀ s ∈ S, ∃ s' ∈ S,
        T d * TensorProduct.map s LinearMap.id = TensorProduct.map s' LinearMap.id * T d) :
    Nat.card Δ ≤ 4 := by
  classical
  haveI hnt1 : Nontrivial (Module.End k U₁) := ⟨0, 1, fun hcon => by
    obtain ⟨v, hv⟩ := exists_ne (0 : U₁)
    have h' : (0 : U₁) = v := by
      simpa using congrArg (fun f : Module.End k U₁ => f v) hcon
    exact hv h'.symm⟩
  haveI hnt2 : Nontrivial (Module.End k U₂) := ⟨0, 1, fun hcon => by
    obtain ⟨v, hv⟩ := exists_ne (0 : U₂)
    have h' : (0 : U₂) = v := by
      simpa using congrArg (fun f : Module.End k U₂ => f v) hcon
    exact hv h'.symm⟩
  have hcomm : ∀ d e : Δ, d * e = e * d := by
    intro d e
    rw [eq_inv_of_mul_eq_one_right (hΔ (d * e)), mul_inv_rev,
      inv_eq_of_mul_eq_one_left (hΔ d), inv_eq_of_mul_eq_one_left (hΔ e)]
  have hTpure : ∀ d : Δ, ∃ (a : Module.End k U₁) (b : Module.End k U₂),
      a * a = 1 ∧ b * b = 1 ∧ T d = TensorProduct.map a b := by
    intro d
    have hTT : T d * T d = 1 := by rw [← map_mul T d d, hΔ d, map_one T]
    obtain ⟨a₀, b₀, hTd⟩ :=
      w183b2_tensor_normalizer (T d) ⟨⟨T d, T d, hTT, hTT⟩, rfl⟩ (hn₁ d) (hn₂ d)
    have hsq : TensorProduct.map (a₀ * a₀) (b₀ * b₀) = 1 := by
      rw [TensorProduct.map_mul, ← hTd, hTT]
    obtain ⟨c, hc, ha₀, hb₀⟩ := w183b2_map_eq_one hsq
    obtain ⟨e, he⟩ := IsAlgClosed.exists_eq_mul_self c
    have he0 : e ≠ 0 := by rintro rfl; exact hc (by simpa using he)
    refine ⟨e⁻¹ • a₀, e • b₀, ?_, ?_, ?_⟩
    · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ha₀, smul_smul,
        show e⁻¹ * e⁻¹ * c = 1 by
          rw [he, ← mul_assoc (e⁻¹ * e⁻¹) e e, mul_assoc e⁻¹ e⁻¹ e,
            inv_mul_cancel₀ he0, mul_one, inv_mul_cancel₀ he0],
        one_smul]
    · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hb₀, smul_smul,
        show e * e * c⁻¹ = 1 by rw [he.symm, mul_inv_cancel₀ hc], one_smul]
    · rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul,
        show e⁻¹ * e = 1 by exact inv_mul_cancel₀ he0, one_smul, ← hTd]
  choose A B hAB using hTpure
  have hA : ∀ d, A d * A d = 1 := fun d => (hAB d).1
  have hB : ∀ d, B d * B d = 1 := fun d => (hAB d).2.1
  have hT : ∀ d, T d = TensorProduct.map (A d) (B d) := fun d => (hAB d).2.2
  have hunitA : ∀ d, IsUnit (A d) := fun d => ⟨⟨A d, A d, hA d, hA d⟩, rfl⟩
  have hunitB : ∀ d, IsUnit (B d) := fun d => ⟨⟨B d, B d, hB d, hB d⟩, rfl⟩
  have hpair : ∀ {a a' : Module.End k U₁} {b b' : Module.End k U₂},
      a * a = 1 → a' * a' = 1 → b * b = 1 → b' * b' = 1 →
      TensorProduct.map a b = TensorProduct.map a' b' → a' = a ∧ b' = b := by
    intro a a' b b' ha1 ha1' hb1 hb1' h
    have ha0 : a ≠ 0 := (show IsUnit a from ⟨⟨a, a, ha1, ha1⟩, rfl⟩).ne_zero
    have hb0 : b ≠ 0 := (show IsUnit b from ⟨⟨b, b, hb1, hb1⟩, rfl⟩).ne_zero
    obtain ⟨c, hc, hca, hcb⟩ := w183b2_map_eq_map ha0 hb0 h
    have hcc : (c * c) • (1 : Module.End k U₁) = 1 := by
      calc (c * c) • (1 : Module.End k U₁)
          = (c * c) • (a * a) := by rw [ha1]
        _ = (c • a) * (c • a) := by
              rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
        _ = a' * a' := by rw [← hca]
        _ = 1 := ha1'
    have hc2 : c * c = 1 := w183b2_smul_one_eq_one hcc
    refine ⟨?_, ?_⟩
    · rw [hca, w183b2_eq_one_of_mul_self hc2, one_smul]
    · rw [hcb, w183b2_eq_one_of_mul_self hc2, one_smul]
  have hA1 : A 1 = 1 := by
    have heq : TensorProduct.map (A 1) (B 1) =
        TensorProduct.map (1 : Module.End k U₁) 1 := by
      rw [← hT 1, map_one T, TensorProduct.map_one]
    exact (hpair (hA 1) (by simp) (hB 1) (by simp) heq).1.symm
  have hB1 : B 1 = 1 := by
    have heq : TensorProduct.map (A 1) (B 1) =
        TensorProduct.map (1 : Module.End k U₁) 1 := by
      rw [← hT 1, map_one T, TensorProduct.map_one]
    exact (hpair (hA 1) (by simp) (hB 1) (by simp) heq).2.symm
  have hA_comm : ∀ d e : Δ, A d * A e = A e * A d := by
    intro d e
    have hde : T d * T e = T e * T d := by rw [← map_mul T d e, ← map_mul T e d, hcomm d e]
    have heq : TensorProduct.map (A d * A e) (B d * B e) =
        TensorProduct.map (A e * A d) (B e * B d) := by
      calc TensorProduct.map (A d * A e) (B d * B e)
          = TensorProduct.map (A d) (B d) * TensorProduct.map (A e) (B e) :=
            TensorProduct.map_mul (A d) (A e) (B d) (B e)
        _ = T d * T e := by rw [← hT d, ← hT e]
        _ = T e * T d := hde
        _ = TensorProduct.map (A e) (B e) * TensorProduct.map (A d) (B d) := by
            rw [hT e, hT d]
        _ = TensorProduct.map (A e * A d) (B e * B d) :=
            (TensorProduct.map_mul (A e) (A d) (B e) (B d)).symm
    obtain ⟨c, hc, h1, _⟩ := w183b2_map_eq_map
      ((hunitA d).mul (hunitA e)).ne_zero ((hunitB d).mul (hunitB e)).ne_zero heq
    have hx2 : (A d * A e) * (A d * A e) = c • (1 : Module.End k U₁) := by
      calc (A d * A e) * (A d * A e)
          = A d * ((A e * A d) * A e) := by rw [mul_assoc, mul_assoc (A e) (A d) (A e)]
        _ = A d * ((c • (A d * A e)) * A e) := by rw [h1]
        _ = A d * (c • ((A d * A e) * A e)) := by rw [Algebra.smul_mul_assoc]
        _ = c • (A d * ((A d * A e) * A e)) := by rw [Algebra.mul_smul_comm]
        _ = c • ((A d * A d) * (A e * A e)) := by
              rw [mul_assoc, ← mul_assoc (A d) (A d) (A e * A e)]
        _ = c • (1 : Module.End k U₁) := by rw [hA d, hA e, one_mul]
    have hxy1 : (A d * A e) * (A e * A d) = 1 := by
      rw [mul_assoc, ← mul_assoc (A e) (A e) (A d), hA e, one_mul, hA d]
    have h1' : (A d * A e) * (A e * A d) = c • ((A d * A e) * (A d * A e)) := by
      rw [h1, Algebra.mul_smul_comm]
    have hcc : (c * c) • (1 : Module.End k U₁) = 1 := by
      calc (c * c) • (1 : Module.End k U₁)
          = c • (c • (1 : Module.End k U₁)) := by rw [smul_smul]
        _ = c • ((A d * A e) * (A d * A e)) := by rw [← hx2]
        _ = (A d * A e) * (A e * A d) := by rw [← h1']
        _ = 1 := hxy1
    rw [h1, w183b2_eq_one_of_mul_self (w183b2_smul_one_eq_one hcc), one_smul]
  have hA_exists : ∃ e : Δ, A e ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    obtain ⟨e, X, hX⟩ := hc₁
    exact hX (by
      have hAe : A e = 1 := by simpa using h e
      rw [hT e, hAe, show (LinearMap.id : Module.End k U₂) = 1 from rfl]
      simp only [← TensorProduct.map_mul, one_mul, mul_one])
  have hB_exists : ∃ e : Δ, B e ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    obtain ⟨e, Y, hY⟩ := hc₂
    exact hY (by
      have hBe : B e = 1 := by simpa using h e
      rw [hT e, hBe, show (LinearMap.id : Module.End k U₁) = 1 from rfl]
      simp only [← TensorProduct.map_mul, one_mul, mul_one])
  have hA_ne_one : ∀ d : Δ, d ≠ 1 → A d ≠ 1 := by
    intro d hd hAd
    have hBd : B d ≠ 1 := by
      intro hBd1
      exact hd (hinj d (by rw [hT d, hAd, hBd1, TensorProduct.map_one]))
    obtain ⟨e, hAe1⟩ := hA_exists
    have hβ : B d - 1 ≠ 0 := sub_ne_zero.mpr hBd
    have hd_eq : T d - 1 = TensorProduct.map 1 (B d - 1) := by
      rw [hT d, hAd, ← TensorProduct.map_one, w183b2_map_sub_right]
    have hq' : TensorProduct.map (A e) ((B d - 1) * B e) =
        TensorProduct.map 1 (B d - 1) := by
      have h := hquad d e
      rw [hd_eq, hT e, mul_sub, ← TensorProduct.map_mul, mul_one] at h
      simpa using sub_eq_zero.mp h
    obtain ⟨c, hc, h1, _⟩ := w183b2_map_eq_map (hunitA e).ne_zero
      (fun hcon => hβ ((hunitB e).mul_left_eq_zero.mp hcon)) hq'
    have hAe_scalar : A e = c⁻¹ • (1 : Module.End k U₁) := by
      conv_rhs => rw [h1]
      rw [inv_smul_smul₀ hc]
    have hcc : (c⁻¹ * c⁻¹) • (1 : Module.End k U₁) = 1 := by
      calc (c⁻¹ * c⁻¹) • (1 : Module.End k U₁)
          = (c⁻¹ • (1 : Module.End k U₁)) * (c⁻¹ • (1 : Module.End k U₁)) := by
            rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one]
        _ = A e * A e := by rw [← hAe_scalar]
        _ = 1 := hA e
    exact hAe1 (by
      rw [hAe_scalar, w183b2_eq_one_of_mul_self (w183b2_smul_one_eq_one hcc), one_smul])
  have hB_ne_one : ∀ d : Δ, d ≠ 1 → B d ≠ 1 := by
    intro d hd hBd
    have hAd : A d ≠ 1 := hA_ne_one d hd
    obtain ⟨e, hBe1⟩ := hB_exists
    have hα : A d - 1 ≠ 0 := sub_ne_zero.mpr hAd
    have hd_eq : T d - 1 = TensorProduct.map (A d - 1) 1 := by
      rw [hT d, hBd, ← TensorProduct.map_one, w183b2_map_sub_left]
    have hq' : TensorProduct.map (A d - 1) 1 =
        TensorProduct.map ((A d - 1) * A e) (B e) := by
      have h := hquad d e
      rw [hd_eq, hT e, mul_sub, ← TensorProduct.map_mul, mul_one] at h
      simpa using (sub_eq_zero.mp h).symm
    obtain ⟨c, hc, _, h2⟩ := w183b2_map_eq_map hα one_ne_zero hq'
    have hBe_scalar : B e = c⁻¹ • (1 : Module.End k U₂) := by
      conv_rhs => rw [h2]
      rw [inv_smul_smul₀ hc]
    have hcc : (c⁻¹ * c⁻¹) • (1 : Module.End k U₂) = 1 := by
      calc (c⁻¹ * c⁻¹) • (1 : Module.End k U₂)
          = (c⁻¹ • (1 : Module.End k U₂)) * (c⁻¹ • (1 : Module.End k U₂)) := by
            rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one]
        _ = B e * B e := by rw [← hBe_scalar]
        _ = 1 := hB e
    exact hBe1 (by
      rw [hBe_scalar, w183b2_eq_one_of_mul_self (w183b2_smul_one_eq_one hcc), one_smul])
  have hA_inj : ∀ g g' : Δ, A g = A g' → g = g' := by
    intro g g' hgg
    have hTgg : T (g * g') = TensorProduct.map 1 (B g * B g') := by
      rw [map_mul T g g', hT g, hT g', ← TensorProduct.map_mul, hgg, hA g']
    have heq : TensorProduct.map (1 : Module.End k U₁) (B g * B g') =
        TensorProduct.map (A (g * g')) (B (g * g')) := by
      rw [← hTgg, hT (g * g')]
    obtain ⟨c, hc, h1, _⟩ := w183b2_map_eq_map one_ne_zero
      ((hunitB g).mul (hunitB g')).ne_zero heq
    have hcc : (c * c) • (1 : Module.End k U₁) = 1 := by
      calc (c * c) • (1 : Module.End k U₁)
          = (c • (1 : Module.End k U₁)) * (c • (1 : Module.End k U₁)) := by
            rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one]
        _ = A (g * g') * A (g * g') := by rw [← h1]
        _ = 1 := hA (g * g')
    have hAgg' : A (g * g') = 1 := by
      rw [h1, w183b2_eq_one_of_mul_self (w183b2_smul_one_eq_one hcc), one_smul]
    have hgg1 : g * g' = 1 := by
      by_contra hne
      exact hA_ne_one (g * g') hne hAgg'
    calc g = g * 1 := (mul_one g).symm
      _ = g * (g' * g') := by rw [hΔ g']
      _ = (g * g') * g' := by rw [mul_assoc]
      _ = 1 * g' := by rw [hgg1]
      _ = g' := one_mul g'
  by_cases hex : ∃ f₀ : Δ, f₀ ≠ 1
  · obtain ⟨f₀, hf₀⟩ := hex
    have hline : ∀ g : Δ, ∃ c : k, A g - 1 = c • (A f₀ - 1) := by
      intro g
      by_cases hg : g = 1
      · exact ⟨0, by rw [hg, hA1]; simp⟩
      · by_cases hgf : g = f₀
        · exact ⟨1, by rw [hgf, one_smul]⟩
        · have hf1 : A f₀ ≠ 1 := hA_ne_one f₀ hf₀
          have hg2 : B g ≠ 1 := hB_ne_one g hg
          have hq : (TensorProduct.map (A f₀) (B f₀) - 1) *
              (TensorProduct.map (A g) (B g) - 1) = 0 := by
            rw [← hT f₀, ← hT g]; exact hquad f₀ g
          exact w183b2_pair_line (hA f₀) (hA g) (hB f₀) (hB g) hf1 hg2
            (hA_comm f₀ g) hq
    choose coef hcoef using hline
    obtain ⟨n, b, F, S, hFfin, hFcard, hspan, hSF, hSinv⟩ := hF
    haveI : Finite F := hFfin
    have hAmat : ∀ d : Δ, ∀ i j, LinearMap.toMatrix b b (A d) i j ∈ F := by
      intro d
      apply w183b2_frob_descent b F S hspan hSF (A d) (hA d)
      intro s hs
      obtain ⟨s', hs', hs'eq⟩ := hSinv d s hs
      refine ⟨s', hs', ?_⟩
      have hmap : TensorProduct.map (A d * s) (B d) =
          TensorProduct.map (s' * A d) (B d) := by
        have h := hs'eq
        rw [hT d] at h
        simp only [← TensorProduct.map_mul, mul_one, one_mul] at h
        exact h
      exact w183b2_tensor_mul_eq_map_left (hunitB d).ne_zero hmap
    have hAmat1 : ∀ g : Δ, ∀ i j, LinearMap.toMatrix b b (A g - 1) i j ∈ F := by
      intro g i j
      have hsub : LinearMap.toMatrix b b (A g - 1) =
          LinearMap.toMatrix b b (A g) - LinearMap.toMatrix b b (1 : Module.End k U₁) :=
        map_sub (LinearMap.toMatrix b b) (A g) 1
      rw [hsub, Matrix.sub_apply]
      exact F.sub_mem (hAmat g i j) (by
        rw [LinearMap.toMatrix_one, Matrix.one_apply]
        split_ifs with h
        · exact F.one_mem
        · exact F.zero_mem)
    have hα0 : A f₀ - 1 ≠ 0 := sub_ne_zero.mpr (hA_ne_one f₀ hf₀)
    have hMne : LinearMap.toMatrix b b (A f₀ - 1) ≠ 0 := by
      intro h0
      exact hα0 (by rw [← Matrix.toLin_toMatrix b b (A f₀ - 1), h0, map_zero])
    have hMne' : ¬ ∀ i j, LinearMap.toMatrix b b (A f₀ - 1) i j = 0 := by
      intro hall
      exact hMne (funext fun i => funext fun j => hall i j)
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hMne'
    obtain ⟨j₀, hj₀⟩ := not_forall.mp hi₀
    have hmij : LinearMap.toMatrix b b (A f₀ - 1) i₀ j₀ ≠ 0 := hj₀
    let lam : Δ → F := fun g =>
      ⟨LinearMap.toMatrix b b (A g - 1) i₀ j₀, hAmat1 g i₀ j₀⟩
    have hcoef_entry : ∀ g : Δ, LinearMap.toMatrix b b (A g - 1) i₀ j₀ =
        coef g * LinearMap.toMatrix b b (A f₀ - 1) i₀ j₀ := by
      intro g
      have hmat : LinearMap.toMatrix b b (A g - 1) =
          coef g • LinearMap.toMatrix b b (A f₀ - 1) := by
        rw [hcoef g, map_smul]
      rw [hmat]
      simp [smul_eq_mul]
    have hinjlam : Function.Injective lam := by
      intro g g' heq
      have h1 : LinearMap.toMatrix b b (A g - 1) i₀ j₀ =
          LinearMap.toMatrix b b (A g' - 1) i₀ j₀ := congrArg Subtype.val heq
      rw [hcoef_entry g, hcoef_entry g'] at h1
      have hcc : coef g = coef g' := mul_right_cancel₀ hmij h1
      have hAg : A g = A g' := by
        have hthis : A g - 1 = A g' - 1 := by rw [hcoef g, hcoef g', hcc]
        have := congrArg (fun x : Module.End k U₁ => x + 1) hthis
        simpa using this
      exact hA_inj g g' hAg
    exact le_trans (Nat.card_le_card_of_injective lam hinjlam) hFcard
  · rw [not_exists] at hex
    haveI : Subsingleton Δ := ⟨fun a b => by
      rw [show a = 1 from by simpa using hex a, show b = 1 from by simpa using hex b]⟩
    have h1 : Nat.card Δ ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr ‹Subsingleton Δ›
    omega

end CFSG.LocalAnalysis.WeakClosure81

end
