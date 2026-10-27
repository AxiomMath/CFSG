module

public import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

private lemma plh_exists_notMem_of_natCard_lt {α : Type*} [Finite α] (s : Finset α)
    (h : s.card < Nat.card α) : ∃ a, a ∉ s := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using h)
  exact ⟨a, ha⟩

private lemma plh_exists_notMem_union_image {K ι : Type*} [Field K] [Finite K] [DecidableEq K]
    (B : Finset K) (C : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → K)
    (h : B.card + C.card < Nat.card K) : ∃ a, a ∉ B ∪ (C.filter p).image f := by
  classical
  have hI : ((C.filter p).image f).card ≤ C.card :=
    le_trans Finset.card_image_le (Finset.card_filter_le C p)
  have hle : (B ∪ (C.filter p).image f).card ≤ B.card + C.card :=
    le_trans (Finset.card_union_le B _) (Nat.add_le_add_left hI B.card)
  exact plh_exists_notMem_of_natCard_lt _ (lt_of_le_of_lt hle h)

theorem exists_notMem_of_card_lt {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (S : Finset (Submodule K V)) (hS : ∀ T ∈ S, T ≠ ⊤) (hcard : S.card < Nat.card K) :
    ∃ v : V, ∀ T ∈ S, v ∉ T := by
  classical
  have hcard' : S.card < ENat.card K := by
    rw [ENat.card_eq_coe_natCard]
    exact ENat.natCast_lt_natCast.mpr hcard
  have hsub := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (s := S.attach)
    (p := fun i : {T // T ∈ S} => (i : Submodule K V))
    (fun i => hS i.1 i.2) (by rwa [Finset.card_attach])
  rw [Set.ssubset_univ_iff, Set.ne_univ_iff_exists_notMem] at hsub
  obtain ⟨v, hv⟩ := hsub
  refine ⟨v, fun T hT => ?_⟩
  intro hvT
  exact hv (Set.mem_iUnion.2 ⟨⟨T, hT⟩,
    Set.mem_iUnion.2 ⟨Finset.mem_attach S ⟨T, hT⟩, hvT⟩⟩)

theorem exists_avoiding_three {K : Type*} [Field K] [Finite K] (Bx By Bz : Finset K)
    (C : Finset (K × K × K × K)) (hC : ∀ w ∈ C, w.1 ≠ 0 ∨ w.2.1 ≠ 0 ∨ w.2.2.1 ≠ 0)
    (hx : Bx.card + C.card < Nat.card K) (hy : By.card + C.card < Nat.card K)
    (hz : Bz.card + C.card < Nat.card K) :
    ∃ a b c : K, a ∉ Bx ∧ b ∉ By ∧ c ∉ Bz ∧
      ∀ w ∈ C, w.1 * a + w.2.1 * b + w.2.2.1 * c ≠ w.2.2.2 := by
  classical
  obtain ⟨a, ha⟩ := plh_exists_notMem_union_image (K := K) (ι := K × K × K × K) Bx C
    (fun w => w.2.1 = 0 ∧ w.2.2.1 = 0) (fun w => w.2.2.2 / w.1) hx
  obtain ⟨b, hb⟩ := plh_exists_notMem_union_image (K := K) (ι := K × K × K × K) By C
    (fun w => w.2.2.1 = 0 ∧ w.2.1 ≠ 0) (fun w => (w.2.2.2 - w.1 * a) / w.2.1) hy
  obtain ⟨c, hc⟩ := plh_exists_notMem_union_image (K := K) (ι := K × K × K × K) Bz C
    (fun w => w.2.2.1 ≠ 0) (fun w => (w.2.2.2 - w.1 * a - w.2.1 * b) / w.2.2.1) hz
  refine ⟨a, b, c, (fun h => ha (Finset.mem_union_left _ h)),
    (fun h => hb (Finset.mem_union_left _ h)),
    (fun h => hc (Finset.mem_union_left _ h)), ?_⟩
  intro w hw
  by_cases hγ : w.2.2.1 = 0
  · by_cases hβ : w.2.1 = 0
    · have hα : w.1 ≠ 0 := by
        rcases hC w hw with h | h | h
        · exact h
        · exact absurd hβ h
        · exact absurd hγ h
      have hwmem : w ∈ C.filter (fun w => w.2.1 = 0 ∧ w.2.2.1 = 0) := by
        rw [Finset.mem_filter]; exact ⟨hw, hβ, hγ⟩
      have hane : a ≠ w.2.2.2 / w.1 := by
        intro hae
        exact ha (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hwmem, hae.symm⟩))
      intro hcon
      apply hane
      simp only [hβ, hγ, zero_mul, add_zero] at hcon
      rw [eq_div_iff hα, mul_comm]
      exact hcon
    · have hwmem : w ∈ C.filter (fun w => w.2.2.1 = 0 ∧ w.2.1 ≠ 0) := by
        rw [Finset.mem_filter]; exact ⟨hw, hγ, hβ⟩
      have hbne : b ≠ (w.2.2.2 - w.1 * a) / w.2.1 := by
        intro hbe
        exact hb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hwmem, hbe.symm⟩))
      intro hcon
      apply hbne
      have hβb : w.2.1 * b = w.2.2.2 - w.1 * a := by
        simp only [hγ, zero_mul, add_zero] at hcon
        rw [eq_sub_iff_add_eq, add_comm]
        exact hcon
      rw [eq_div_iff hβ, mul_comm]
      exact hβb
  · have hwmem : w ∈ C.filter (fun w => w.2.2.1 ≠ 0) := by
      rw [Finset.mem_filter]; exact ⟨hw, hγ⟩
    have hcne : c ≠ (w.2.2.2 - w.1 * a - w.2.1 * b) / w.2.2.1 := by
      intro hce
      exact hc (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hwmem, hce.symm⟩))
    intro hcon
    apply hcne
    have hγc : w.2.2.1 * c = w.2.2.2 - w.1 * a - w.2.1 * b := by
      have h1 : w.2.2.1 * c = w.2.2.2 - (w.1 * a + w.2.1 * b) := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hcon
      rw [sub_sub]
      exact h1
    rw [eq_div_iff hγ, mul_comm]
    exact hγc

theorem exists_cone_vector {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (x y z e : V) (Bx By Bz : Finset K) (S : Finset (Submodule K V))
    (hS : ∀ T ∈ S, ¬ (x ∈ T ∧ y ∈ T ∧ z ∈ T ∧ e ∈ T))
    (hx : Bx.card + S.card < Nat.card K) (hy : By.card + S.card < Nat.card K)
    (hz : Bz.card + S.card < Nat.card K) :
    ∃ a b c : K, a ∉ Bx ∧ b ∉ By ∧ c ∉ Bz ∧ ∀ T ∈ S, a • x + b • y + c • z + e ∉ T := by
  classical
  have hw : ∀ T : {T // T ∈ S}, ∃ w : V, (w = x ∨ w = y ∨ w = z ∨ w = e) ∧ w ∉ T.1 := by
    intro T
    by_cases hxT : x ∈ T.1
    · by_cases hyT : y ∈ T.1
      · by_cases hzT : z ∈ T.1
        · exact ⟨e, Or.inr (Or.inr (Or.inr rfl)),
            fun heT => hS T.1 T.2 ⟨hxT, hyT, hzT, heT⟩⟩
        · exact ⟨z, Or.inr (Or.inr (Or.inl rfl)), hzT⟩
      · exact ⟨y, Or.inr (Or.inl rfl), hyT⟩
    · exact ⟨x, Or.inl rfl, hxT⟩
  let w : {T // T ∈ S} → V := fun T => Classical.choose (hw T)
  have hw_spec : ∀ T, (w T = x ∨ w T = y ∨ w T = z ∨ w T = e) ∧ w T ∉ T.1 :=
    fun T => Classical.choose_spec (hw T)
  have hex : ∀ T : {T // T ∈ S}, ∃ φ : V →ₗ[K] K,
      (∀ v ∈ T.1, φ v = 0) ∧ φ (w T) = 1 := by
    intro T
    obtain ⟨f0, hf0ne, hf0ker⟩ :=
      Submodule.exists_le_ker_of_notMem (p := T.1) (v := w T) (hw_spec T).2
    refine ⟨(f0 (w T))⁻¹ • f0, ?_, ?_⟩
    · intro v hv
      rw [LinearMap.smul_apply, smul_eq_mul, (show f0 v = 0 from hf0ker hv), mul_zero]
    · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf0ne]
  let φ : {T // T ∈ S} → (V →ₗ[K] K) := fun T => Classical.choose (hex T)
  have hφ : ∀ T, (∀ v ∈ T.1, φ T v = 0) ∧ φ T (w T) = 1 :=
    fun T => Classical.choose_spec (hex T)
  let cond : {T // T ∈ S} → K × K × K × K := fun T => (φ T x, φ T y, φ T z, - φ T e)
  let C : Finset (K × K × K × K) :=
    (S.attach.filter (fun T => φ T x ≠ 0 ∨ φ T y ≠ 0 ∨ φ T z ≠ 0)).image cond
  have hCcard : C.card ≤ S.card := by
    have h1 : C.card ≤
        (S.attach.filter (fun T => φ T x ≠ 0 ∨ φ T y ≠ 0 ∨ φ T z ≠ 0)).card :=
      Finset.card_image_le
    have h2 : (S.attach.filter (fun T => φ T x ≠ 0 ∨ φ T y ≠ 0 ∨ φ T z ≠ 0)).card ≤
        S.attach.card := Finset.card_filter_le _ _
    rw [Finset.card_attach] at h2
    exact le_trans h1 h2
  have hCpred : ∀ u ∈ C, u.1 ≠ 0 ∨ u.2.1 ≠ 0 ∨ u.2.2.1 ≠ 0 := by
    intro u hu
    dsimp only [C] at hu
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hu
    simpa only [cond] using (Finset.mem_filter.mp hT).2
  obtain ⟨a, b, c, ha, hb, hc, hav⟩ :=
    exists_avoiding_three Bx By Bz C hCpred
      (lt_of_le_of_lt (Nat.add_le_add_left hCcard Bx.card) hx)
      (lt_of_le_of_lt (Nat.add_le_add_left hCcard By.card) hy)
      (lt_of_le_of_lt (Nat.add_le_add_left hCcard Bz.card) hz)
  refine ⟨a, b, c, ha, hb, hc, ?_⟩
  intro T hT
  let T' : {T // T ∈ S} := ⟨T, hT⟩
  have hφT := hφ T'
  by_cases htri : φ T' x ≠ 0 ∨ φ T' y ≠ 0 ∨ φ T' z ≠ 0
  · have hmemC : cond T' ∈ C := by
      dsimp only [C]
      rw [Finset.mem_image]
      exact ⟨T', Finset.mem_filter.mpr ⟨Finset.mem_attach S T', htri⟩, rfl⟩
    have hcond := hav (cond T') hmemC
    dsimp only [cond] at hcond
    intro hvT
    have h0 : φ T' (a • x + b • y + c • z + e) = 0 := hφT.1 _ hvT
    have hval : φ T' (a • x + b • y + c • z + e) =
        a * φ T' x + b * φ T' y + c * φ T' z + φ T' e := by
      simp only [map_add, map_smul, smul_eq_mul]
    have hne : a * φ T' x + b * φ T' y + c * φ T' z + φ T' e ≠ 0 := by
      intro hzero
      apply hcond
      rw [eq_neg_iff_add_eq_zero]
      rw [mul_comm (φ T' x) a, mul_comm (φ T' y) b, mul_comm (φ T' z) c]
      exact hzero
    rw [hval] at h0
    exact hne h0
  · have hx0 : φ T' x = 0 := by by_contra h; exact htri (Or.inl h)
    have hy0 : φ T' y = 0 := by by_contra h; exact htri (Or.inr (Or.inl h))
    have hz0 : φ T' z = 0 := by by_contra h; exact htri (Or.inr (Or.inr h))
    have he0 : φ T' e ≠ 0 := by
      intro he
      have hw0 : φ T' (w T') = 0 := by
        rcases (hw_spec T').1 with h | h | h | h
        · rw [h]; exact hx0
        · rw [h]; exact hy0
        · rw [h]; exact hz0
        · rw [h]; exact he
      rw [hw0] at hφT
      exact zero_ne_one hφT.2
    intro hvT
    have h0 : φ T' (a • x + b • y + c • z + e) = 0 := hφT.1 _ hvT
    have hval : φ T' (a • x + b • y + c • z + e) = φ T' e := by
      simp only [map_add, map_smul, smul_eq_mul, hx0, hy0, hz0, mul_zero, add_zero, zero_add]
    rw [hval] at h0
    exact he0 h0

end CFSG.ClassicalInvolution.Phan.PhanE

end
