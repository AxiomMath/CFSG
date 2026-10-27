module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructAb
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGField1
public import Mathlib

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem p9uCard_three_dvd_card_weight_class [FiniteDimensional K V] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι K V) {T : Type*} [DecidableEq (T → K)]
    (f : T → V →ₗ[K] V) (μ : T → ι → K)
    (hf : ∀ t j, f t (b j) = μ t j • b j) (χ : T → K) {c : V →ₗ[K] V} {l : K}
    (hl : ∀ a : K, a ^ 3 ≠ l) (hc : ∀ t v, f t (c v) = c (f t v))
    (hc3 : c ^ 3 = algebraMap K (Module.End K V) l) :
    3 ∣ (Finset.univ.filter (fun j => (fun t => μ t j) = χ)).card := by
  classical
  set J : Finset ι := Finset.univ.filter (fun j => (fun t => μ t j) = χ) with hJ
  have hlin : LinearIndepOn K id ((J.image b : Finset V) : Set V) := by
    rw [Finset.coe_image]
    exact (linearIndepOn_iff_image (f := b) (s := (J : Set ι))
      (fun _ _ _ _ h => b.injective h)).1 (b.linearIndependent.linearIndepOn (J : Set ι))
  set S : Submodule K V := Submodule.span K (b '' (J : Set ι)) with hS
  have hfin : Module.finrank K S = J.card := by
    rw [hS]
    have hcoe : b '' (J : Set ι) = ((J.image b : Finset V) : Set V) := by
      rw [Finset.coe_image]
    rw [hcoe, finrank_span_finset_eq_card hlin,
      Finset.card_image_of_injective J b.injective]
  have hcmap : Submodule.map c S ≤ S := by
    rw [hS, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hy
    have hχ : ∀ t : T, χ t = μ t j := by
      intro t
      have h : (fun s : T => μ s j) = χ := by
        have := hj
        rw [hJ] at this
        simpa using this
      exact (congrFun h t).symm
    have hw : ∀ t : T, f t (c (b j)) = χ t • c (b j) := by
      intro t
      rw [hc t (b j), hf t j, map_smul, hχ t]
    have hzero : ∀ i, i ∉ J → b.repr (c (b j)) i = 0 := by
      intro i hi
      have hne : (fun t : T => μ t i) ≠ χ := by
        intro h
        apply hi
        rw [hJ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
      have h1 : b.repr (f t (c (b j))) i = μ t i * b.repr (c (b j)) i :=
        repr_apply_of_eigen b (f t) (μ t) (hf t) _ i
      rw [hw t, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
      have h3 : (μ t i - χ t) * b.repr (c (b j)) i = 0 := by rw [sub_mul, ← h1, sub_self]
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) ht
      · exact h
    rw [← b.sum_repr (c (b j))]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ J
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hzero i hi, zero_smul]
      exact Submodule.zero_mem _
  have hdvd : 3 ∣ Module.finrank K S :=
    CFSG.StandardType.UnitSixThreeKG.three_dvd_finrank_of_invariant (M := c) (l := l) hl hc3 S
      (fun w hw => hcmap (Submodule.mem_map_of_mem hw))
  rwa [hfin] at hdvd

theorem card_le_three_pow_finrank_div_three [Finite K] (hK : Nat.card K = 4)
    [FiniteDimensional K V] {T : Subgroup (V ≃ₗ[K] V)}
    (hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT3 : ∀ x ∈ T, x ^ 3 = 1) {c : V ≃ₗ[K] V}
    (hc : ∀ t ∈ T, c * t = t * c) {l : K} (hl : ∀ a : K, a ^ 3 ≠ l)
    (hc3 : ∀ v, (c ^ 3) v = l • v) :
    Nat.card T ≤ 3 ^ (Module.finrank K V / 3) := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hK
  have hcomm : ∀ s t : T, Commute ((s : V ≃ₗ[K] V) : V →ₗ[K] V) ((t : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    intro s t
    have h : ((s : V ≃ₗ[K] V) : V →ₗ[K] V) * ((t : V ≃ₗ[K] V) : V →ₗ[K] V) =
        ((t : V ≃ₗ[K] V) : V →ₗ[K] V) * ((s : V ≃ₗ[K] V) : V →ₗ[K] V) := by
      refine LinearMap.ext fun v => ?_
      have := congrArg (fun e : V ≃ₗ[K] V => e v) (hab s s.2 t t.2)
      simpa using this
    exact h
  have hpow : ∀ t : T, ((t : V ≃ₗ[K] V) : V →ₗ[K] V) ^ 3 = 1 := fun t =>
    toLinearMap_pow_three (hT3 t t.2)
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ
    (fun t : T => ((t : V ≃ₗ[K] V) : V →ₗ[K] V)) hcomm hpow
  have hμ0 : ∀ t j, μ t j ≠ 0 := by
    intro t j h0
    have h1 := hb t j
    rw [h0, zero_smul] at h1
    exact b.ne_zero j ((t : V ≃ₗ[K] V).map_eq_zero_iff.1 h1)
  have hinj : Function.Injective μ := by
    intro t t' h
    apply Subtype.ext
    have h1 : ((t : V ≃ₗ[K] V) : V →ₗ[K] V) = ((t' : V ≃ₗ[K] V) : V →ₗ[K] V) :=
      b.ext fun j => by rw [hb t j, hb t' j, h]
    exact LinearEquiv.ext fun v => LinearMap.congr_fun h1 v
  have h1 := card_le_three_pow_card_image hK μ hμ0 hinj
  set k := (Finset.univ.image (fun j t => μ t j)).card with hk
  have hcommc : ∀ t : T, ∀ v : V,
      ((t : V ≃ₗ[K] V) : V →ₗ[K] V) (((c : V ≃ₗ[K] V) : V →ₗ[K] V) v) =
      ((c : V ≃ₗ[K] V) : V →ₗ[K] V) (((t : V ≃ₗ[K] V) : V →ₗ[K] V) v) := by
    intro t v
    have h := congrArg (fun e : V ≃ₗ[K] V => e v) (hc t t.2)
    simpa using h.symm
  have hc3L : ((c : V ≃ₗ[K] V) : V →ₗ[K] V) ^ 3 = algebraMap K (Module.End K V) l := by
    ext v
    rw [Module.algebraMap_end_apply]
    simpa [Module.End.pow_apply, LinearEquiv.pow_apply] using hc3 v
  have hle : 3 * k ≤ Module.finrank K V := by
    have hmul := Finset.mul_card_image_le_card
      (f := fun (j : Fin (Module.finrank K V)) (t : T) => μ t j) (Finset.univ) 3 ?_
    · simpa using hmul
    · intro χ hχ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hχ
      have hmem : j ∈ Finset.univ.filter (fun a => (fun t => μ t a) = (fun t => μ t j)) := by
        simp
      have hpos : 0 < (Finset.univ.filter (fun a => (fun t => μ t a) = (fun t => μ t j))).card :=
        Finset.card_pos.2 ⟨j, hmem⟩
      exact Nat.le_of_dvd hpos (p9uCard_three_dvd_card_weight_class b
        (fun t : T => ((t : V ≃ₗ[K] V) : V →ₗ[K] V)) μ hb _ hl hcommc hc3L)
  have hkdiv : k ≤ Module.finrank K V / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    simpa [mul_comm] using hle
  calc Nat.card T ≤ 3 ^ k := h1
    _ ≤ 3 ^ (Module.finrank K V / 3) := Nat.pow_le_pow_right (by norm_num) hkdiv

theorem three_dvd_finrank_and_card_le_of_abelian_cube [Finite K] (hK : Nat.card K = 4)
    [FiniteDimensional K V] {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {x : V ≃ₗ[K] V} (hx : x ∈ Q) (hx3 : x ^ 3 ≠ 1) :
    3 ∣ Module.finrank K V ∧ Nat.card Q ≤ 3 ^ (1 + Module.finrank K V / 3) := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hZ := scalarLike_scalars (V := V) hK
  obtain ⟨T, hTQ, hT3, -, hTcard⟩ := exists_cube_kernel_of_good hZ hQ
  obtain ⟨ω, hω⟩ := mem_scalars_iff.1 (hQ.2 x hx)
  have hωne1 : (ω : K) ≠ 1 := by
    intro h
    apply hx3
    refine LinearEquiv.ext fun v => ?_
    rw [hω v, h, one_smul]
    rfl
  have hl : ∀ a : K, a ^ 3 ≠ (ω : K) := by
    intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      rw [zero_pow (by norm_num)] at ha
      exact ω.ne_zero ha.symm
    · rw [pow_three_of_ne_zero hK ha0] at ha
      exact hωne1 ha.symm
  have hx3L : ((x : V ≃ₗ[K] V) : V →ₗ[K] V) ^ 3 =
      algebraMap K (Module.End K V) (ω : K) := by
    ext v
    rw [Module.algebraMap_end_apply]
    simpa [Module.End.pow_apply, LinearEquiv.pow_apply] using hω v
  have h3dvd : 3 ∣ Module.finrank K V := by
    have := CFSG.StandardType.UnitSixThreeKG.three_dvd_finrank_of_invariant
      (M := ((x : V ≃ₗ[K] V) : V →ₗ[K] V)) (l := (ω : K)) hl hx3L ⊤
      (fun w _ => Submodule.mem_top)
    simpa using this
  have hTbound : Nat.card T ≤ 3 ^ (Module.finrank K V / 3) :=
    card_le_three_pow_finrank_div_three hK (T := T)
      (fun y hy z hz => hab y (hTQ hy) z (hTQ hz)) hT3
      (fun t ht => hab x hx t (hTQ ht)) hl hω
  refine ⟨h3dvd, ?_⟩
  calc Nat.card Q ≤ 3 * Nat.card T := hTcard
    _ ≤ 3 * 3 ^ (Module.finrank K V / 3) := Nat.mul_le_mul_left _ hTbound
    _ = 3 ^ (1 + Module.finrank K V / 3) := by rw [pow_add, pow_one]

end CFSG.StandardType.FrameRoute

end
