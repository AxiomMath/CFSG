module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SpPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpQv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.Open (StatedProj StatedSp)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
  (unipSp spForm spN spT isSp_spN spN_mul_self spT_mul_spT spForm_swap spForm_self)

variable {r : ℕ} {K : Type} [Field K]

private lemma spForm_add_right (y z w : Fin r ⊕ Fin r → K) :
    spForm y (z + w) = spForm y z + spForm y w := by
  simp [spForm, Matrix.mulVec_add, dotProduct_add]

private lemma spForm_smul_right (y z : Fin r ⊕ Fin r → K) (c : K) :
    spForm y (c • z) = c * spForm y z := by
  simp [spForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem spT_smul_left (c : K) (a b : Fin r ⊕ Fin r → K) :
    spT (c • a) b = c • spT a b := by
  simp only [spT, Matrix.mulVec_smul, Matrix.vecMulVec_smul]

private theorem spT_smul_right (c : K) (a b : Fin r ⊕ Fin r → K) :
    spT b (c • a) = c • spT b a := by
  simp only [spT, Matrix.smul_vecMulVec]

private theorem spN_smul_self (κ : K) (v : Fin r ⊕ Fin r → K) :
    spN v (κ • v) = (2 * κ) • spT v v := by
  rw [spN, spT_smul_left, spT_smul_right, ← add_smul, ← two_mul]

private theorem spT_self_mul_spN_of_orth {v c : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0) :
    spT v v * spN v c = 0 := by
  rw [spN, Matrix.mul_add, spT_mul_spT, spT_mul_spT, spForm_self, spForm_swap v c, hvc,
    neg_zero]
  simp

private theorem spN_mul_spN_of_orth {v c c' : Fin r ⊕ Fin r → K} (hvc : spForm v c = 0)
    (hvc' : spForm v c' = 0) : spN v c * spN v c' = spForm c' c • spT v v := by
  rw [spN, spN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [spT_mul_spT, hvc, spForm_self, spForm_swap v c', hvc', neg_zero, zero_smul,
    zero_add, add_zero]

private theorem spT_self_ne_zero {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) : spT v v ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, spForm y v ≠ 0 := by
    obtain ⟨y, -, hy⟩ := exists_spForm_sep (S := (∅ : Set (Fin r ⊕ Fin r → K))) (c := v)
      (by simpa using hv)
    exact ⟨y, by rw [spForm_swap, hy]; norm_num⟩
  intro h
  have h2 : spT v v *ᵥ y = 0 := by rw [h, Matrix.zero_mulVec]
  rw [spT_mulVec] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact hy h3
  · exact hv h3

private theorem exists_orth_notMem_span (hr : 2 ≤ r) {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    ∃ e : Fin r ⊕ Fin r → K, spForm v e = 0 ∧ e ∉ Submodule.span K {v} := by
  classical
  obtain ⟨y, -, hy⟩ := exists_spForm_sep (S := (∅ : Set (Fin r ⊕ Fin r → K))) (c := v)
    (by simpa using hv)
  let φ : (Fin r ⊕ Fin r → K) →ₗ[K] K :=
    { toFun := fun z => spForm v z
      map_add' := by intro a b; simp [spForm, Matrix.mulVec_add, dotProduct_add]
      map_smul' := by
        intro c a
        simp [spForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] }
  have hφ : ∀ z, φ z = spForm v z := fun _ => rfl
  have hφy : φ y = 1 := by rw [hφ]; exact hy
  have hφne : φ ≠ 0 := fun h0 => by rw [h0] at hφy; exact one_ne_zero hφy.symm
  have hfin : Module.finrank K (LinearMap.ker φ) + 1 = Module.finrank K (Fin r ⊕ Fin r → K) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hφne
  have hV : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
    omega
  have hle : Submodule.span K {v} ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha, SetLike.mem_coe, LinearMap.mem_ker, hφ]
    exact spForm_self v
  have hlt : Module.finrank K (Submodule.span K {v}) < Module.finrank K (LinearMap.ker φ) := by
    rw [finrank_span_singleton hv]
    omega
  obtain ⟨-, e, he1, he2⟩ :=
    SetLike.lt_iff_le_and_exists.mp (Submodule.lt_of_le_of_finrank_lt_finrank hle hlt)
  exact ⟨e, by rw [← hφ]; exact LinearMap.mem_ker.mp he1, he2⟩

private lemma mem_span_three {V : Type} [AddCommGroup V] [Module K V] (v e g x : V)
    (h : x ∈ Submodule.span K ({v, e, g} : Set V)) :
    ∃ α β γ : K, x = α • v + β • e + γ • g := by
  rw [show ({v, e, g} : Set V) = insert v (insert e {g}) by simp] at h
  rw [Submodule.mem_span_insert] at h
  obtain ⟨α, z, hz, rfl⟩ := h
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨β, w, hw, rfl⟩ := hz
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨γ, rfl⟩ := hw
  exact ⟨α, β, γ, by rw [add_assoc]⟩

private def tripleForm (v u f : Fin r ⊕ Fin r → K) :
    (Fin r ⊕ Fin r → K) →ₗ[K] K × K × K where
  toFun y := (spForm v y, spForm u y, spForm f y)
  map_add' y z := by
    simp [spForm, Matrix.mulVec_add, dotProduct_add]
  map_smul' c y := by
    simp [spForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem exists_orth_three (hr : 3 ≤ r) {v u f : Fin r ⊕ Fin r → K} (hv : v ≠ 0)
    (hvu : spForm v u = 0) (hvf : spForm v f = 0) (huf : spForm u f = 1) :
    ∃ e : Fin r ⊕ Fin r → K, spForm v e = 0 ∧ spForm u e = 0 ∧ spForm f e = 0 ∧
      e ∉ Submodule.span K ({v, u, f} : Set (Fin r ⊕ Fin r → K)) := by
  classical
  let L := tripleForm v u f
  let S : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K ({v, u, f} : Set _)
  have hL : L = tripleForm v u f := rfl
  have hker : ∀ y, y ∈ LinearMap.ker L ↔
      spForm v y = 0 ∧ spForm u y = 0 ∧ spForm f y = 0 := by
    intro y
    rw [LinearMap.mem_ker, hL]
    change (spForm v y, spForm u y, spForm f y) = 0 ↔ _
    simp
  have hrank : Module.finrank K (LinearMap.range L) + Module.finrank K (LinearMap.ker L) =
      Module.finrank K (Fin r ⊕ Fin r → K) :=
    LinearMap.finrank_range_add_finrank_ker L
  have hV : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
    omega
  have hcod : Module.finrank K (K × K × K) = 3 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  have hrange : Module.finrank K (LinearMap.range L) ≤ 3 := by
    calc Module.finrank K (LinearMap.range L)
        ≤ Module.finrank K (⊤ : Submodule K (K × K × K)) := Submodule.finrank_mono le_top
      _ = 3 := by rw [finrank_top, hcod]
  have hker3 : 3 ≤ Module.finrank K (LinearMap.ker L) := by omega
  have hInf : LinearMap.ker L ⊓ S = Submodule.span K {v} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxL, hxS⟩ := hx
      obtain ⟨α, β, γ, hdec⟩ := mem_span_three v u f x hxS
      obtain ⟨-, hu0, hf0⟩ := (hker x).mp hxL
      have hγ : γ = 0 := by
        have h := hu0
        rw [hdec, spForm_add_right, spForm_add_right, spForm_smul_right, spForm_smul_right,
          spForm_smul_right, spForm_self, spForm_swap v u, hvu, huf] at h
        simpa using h
      have hβ : β = 0 := by
        have h := hf0
        rw [hdec, spForm_add_right, spForm_add_right, spForm_smul_right, spForm_smul_right,
          spForm_smul_right, spForm_self, spForm_swap v f, hvf, spForm_swap u f, huf] at h
        simpa using h
      rw [Submodule.mem_span_singleton]
      exact ⟨α, by rw [hdec, hβ, hγ, zero_smul, zero_smul, add_zero, add_zero]⟩
    · intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨α, rfl⟩ := hx
      refine ⟨(hker _).mpr ⟨?_, ?_, ?_⟩, Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩
      · rw [spForm_smul_right, spForm_self, mul_zero]
      · rw [spForm_smul_right, spForm_swap v u, hvu, neg_zero, mul_zero]
      · rw [spForm_smul_right, spForm_swap v f, hvf, neg_zero, mul_zero]
  have hfinInf : Module.finrank K ↥(LinearMap.ker L ⊓ S) = 1 := by
    rw [hInf, finrank_span_singleton hv]
  have hlt : Module.finrank K ↥(LinearMap.ker L ⊓ S) < Module.finrank K (LinearMap.ker L) := by
    rw [hfinInf]
    omega
  obtain ⟨-, e, he1, he2⟩ :=
    SetLike.lt_iff_le_and_exists.mp (Submodule.lt_of_le_of_finrank_lt_finrank inf_le_left hlt)
  obtain ⟨hv0, hu0, hf0⟩ := (hker e).mp he1
  refine ⟨e, hv0, hu0, hf0, fun heS => he2 ⟨he1, heS⟩⟩

private theorem exists_heis_pair_orth (hr : 3 ≤ r) (h2 : (2 : K) ≠ 0)
    {v u : Fin r ⊕ Fin r → K} (hv : v ≠ 0) (hvu : spForm v u = 0)
    (hin : u ∉ Submodule.span K {v}) :
    ∃ (f : Fin r ⊕ Fin r → K) (ι₁ ι₂ : Heis K →* StatedProj (StatedSp r K)),
      spForm v f = 0 ∧ spForm u f = 1 ∧ Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ x y, Commute (ι₁ x) (ι₂ y)) ∧ (∀ c : K, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) ∧
      ι₁ ⟨1, 0, 0⟩ = proj r K (unipSp (spN v u) (isSp_spN v u) (spN_mul_self hvu)) ∧
      (∀ (c : K) (hs : (c • (spN v u * spN v f - spN v f * spN v u))ᵀ * formJ r K +
          formJ r K * (c • (spN v u * spN v f - spN v f * spN v u)) = 0)
        (hN : c • (spN v u * spN v f - spN v f * spN v u) *
          (c • (spN v u * spN v f - spN v f * spN v u)) = 0),
        ι₁ ⟨0, 0, c⟩ = proj r K
          (unipSp (c • (spN v u * spN v f - spN v f * spN v u)) hs hN)) := by
  classical
  obtain ⟨f, hf, huf⟩ := exists_spForm_sep (S := ({v} : Set (Fin r ⊕ Fin r → K))) (c := u) hin
  have hvf : spForm v f = 0 := hf v (Set.mem_singleton v)
  obtain ⟨e, hve, hue, hfe, hespan⟩ := exists_orth_three hr hv hvu hvf huf
  obtain ⟨f₂, hf₂, hef₂⟩ :=
    exists_spForm_sep (S := ({v, u, f} : Set (Fin r ⊕ Fin r → K))) (c := e) hespan
  have hv₂ : spForm v f₂ = 0 := hf₂ v (by simp)
  have hu₂ : spForm u f₂ = 0 := hf₂ u (by simp)
  have hff₂ : spForm f f₂ = 0 := hf₂ f (by simp)
  have hmul₁ : spN v u * spN v f = -spT v v := by
    rw [spN_mul_spN_of_orth hvu hvf, spForm_swap u f, huf, neg_one_smul]
  have hmul₂ : spN v f * spN v u = spT v v := by
    rw [spN_mul_spN_of_orth hvf hvu, huf, one_smul]
  have hmul₃ : spN v e * spN v f₂ = -spT v v := by
    rw [spN_mul_spN_of_orth hve hv₂, spForm_swap e f₂, hef₂, neg_one_smul]
  have hmul₄ : spN v f₂ * spN v e = spT v v := by
    rw [spN_mul_spN_of_orth hv₂ hve, hef₂, one_smul]
  have h121 : spN v u * spN v f * spN v u = 0 := by
    rw [hmul₁, Matrix.neg_mul, spT_self_mul_spN_of_orth hvu, neg_zero]
  have h212 : spN v f * spN v u * spN v f = 0 := by
    rw [hmul₂, spT_self_mul_spN_of_orth hvf]
  have h343 : spN v e * spN v f₂ * spN v e = 0 := by
    rw [hmul₃, Matrix.neg_mul, spT_self_mul_spN_of_orth hve, neg_zero]
  have h434 : spN v f₂ * spN v e * spN v f₂ = 0 := by
    rw [hmul₄, spT_self_mul_spN_of_orth hv₂]
  have h12 : spN v u * spN v f ≠ 0 := by
    rw [hmul₁]
    exact neg_ne_zero.mpr (spT_self_ne_zero hv)
  have h34 : spN v e * spN v f₂ ≠ 0 := by
    rw [hmul₃]
    exact neg_ne_zero.mpr (spT_self_ne_zero hv)
  have hPQ : spN v u * spN v f ≠ spN v f * spN v u := by
    rw [hmul₁, hmul₂]
    intro h
    have hz : (2 : K) • spT v v = 0 := by
      rw [two_smul]
      exact neg_eq_iff_add_eq_zero.mp h
    rcases smul_eq_zero.mp hz with h0 | h0
    · exact h2 h0
    · exact spT_self_ne_zero hv h0
  have hPQ' : spN v e * spN v f₂ ≠ spN v f₂ * spN v e := by
    rw [hmul₃, hmul₄]
    intro h
    have hz : (2 : K) • spT v v = 0 := by
      rw [two_smul]
      exact neg_eq_iff_add_eq_zero.mp h
    rcases smul_eq_zero.mp hz with h0 | h0
    · exact h2 h0
    · exact spT_self_ne_zero hv h0
  have h13 : spN v u * spN v e = 0 := by
    rw [spN_mul_spN_of_orth hvu hve, spForm_swap u e, hue, neg_zero, zero_smul]
  have h14 : spN v u * spN v f₂ = 0 := by
    rw [spN_mul_spN_of_orth hvu hv₂, spForm_swap u f₂, hu₂, neg_zero, zero_smul]
  have h23 : spN v f * spN v e = 0 := by
    rw [spN_mul_spN_of_orth hvf hve, spForm_swap f e, hfe, neg_zero, zero_smul]
  have h24 : spN v f * spN v f₂ = 0 := by
    rw [spN_mul_spN_of_orth hvf hv₂, spForm_swap f f₂, hff₂, neg_zero, zero_smul]
  have h31 : spN v e * spN v u = 0 := by
    rw [spN_mul_spN_of_orth hve hvu, hue, zero_smul]
  have h32 : spN v e * spN v f = 0 := by
    rw [spN_mul_spN_of_orth hve hvf, hfe, zero_smul]
  have h41 : spN v f₂ * spN v u = 0 := by
    rw [spN_mul_spN_of_orth hv₂ hvu, hu₂, zero_smul]
  have h42 : spN v f₂ * spN v f = 0 := by
    rw [spN_mul_spN_of_orth hv₂ hvf, hff₂, zero_smul]
  have hcen : spN v u * spN v f - spN v f * spN v u =
      spN v e * spN v f₂ - spN v f₂ * spN v e := by
    rw [hmul₁, hmul₂, hmul₃, hmul₄]
  obtain ⟨ι₁, ι₂, hι₁, hι₂, hcomm, hceneq, hι1, -, hlast⟩ :=
    exists_heis_pair_projectiveSp (hr := by omega)
      (N₁ := spN v u) (N₂ := spN v f) (N₃ := spN v e) (N₄ := spN v f₂)
      (hs₁ := isSp_spN v u) (hs₂ := isSp_spN v f) (hs₃ := isSp_spN v e)
      (hs₄ := isSp_spN v f₂)
      (h₁ := spN_mul_self hvu) (h₂ := spN_mul_self hvf) (h₃ := spN_mul_self hve)
      (h₄ := spN_mul_self hv₂)
      (h₁₂₁ := h121) (h₂₁₂ := h212) (h₃₄₃ := h343) (h₄₃₄ := h434)
      (h₁₂ := h12) (hPQ := hPQ) (h₃₄ := h34) (hPQ' := hPQ')
      (h13 := h13) (h14 := h14) (h23 := h23) (h24 := h24)
      (h31 := h31) (h32 := h32) (h41 := h41) (h42 := h42) (hcen := hcen)
  exact ⟨f, ι₁, ι₂, hvf, huf, hι₁, hι₂, hcomm, hceneq, hι1, hlast⟩

theorem good_unipSp_spN_three [Finite K] (hK : Nat.card K = 3) (hr : 3 ≤ r)
    {v u : Fin r ⊕ Fin r → K} (hv : v ≠ 0) (hu : u ≠ 0) (hvu : spForm v u = 0) :
    orderOf (proj r K (unipSp (spN v u) (isSp_spN v u) (spN_mul_self hvu))) = 3 ∧
      IsExtraGood (proj r K (unipSp (spN v u) (isSp_spN v u) (spN_mul_self hvu))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 3 := charP_of_card_eq_prime hK'
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).mp (by exact_mod_cast h)
    omega
  by_cases hin : u ∈ Submodule.span K {v}
  ·
    obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hin
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hκ
      exact hu hκ.symm
    obtain ⟨e, hve, hespan⟩ := exists_orth_notMem_span (by omega) hv
    obtain ⟨f, ι₁, ι₂, hvf, hef, hι₁, hι₂, hcomm, hceneq, hι1, hlast⟩ :=
      exists_heis_pair_orth hr h2 hv hve hespan
    have hEq : (-κ) • (spN v e * spN v f - spN v f * spN v e) = spN v u := by
      rw [spN_mul_spN_of_orth hve hvf, spN_mul_spN_of_orth hvf hve, spForm_swap e f, hef,
        neg_one_smul, one_smul, ← hκ, spN_smul_self]
      module
    have hs : ((-κ) • (spN v e * spN v f - spN v f * spN v e))ᵀ * formJ r K +
        formJ r K * ((-κ) • (spN v e * spN v f - spN v f * spN v e)) = 0 := by
      rw [hEq]
      exact isSp_spN v u
    have hN : ((-κ) • (spN v e * spN v f - spN v f * spN v e)) *
        ((-κ) • (spN v e * spN v f - spN v f * spN v e)) = 0 := by
      rw [hEq]
      exact spN_mul_self hvu
    have hx : proj r K (unipSp (spN v u) (isSp_spN v u) (spN_mul_self hvu)) =
        ι₁ ⟨0, 0, -κ⟩ := by
      rw [hlast (-κ) hs hN, unipSp_congr hEq hs hN (isSp_spN v u) (spN_mul_self hvu)]
    refine ⟨?_, ?_⟩
    · rw [hx, orderOf_injective ι₁ hι₁]
      refine orderOf_eq_prime
        (Heis.pow_prime_eq_one (p := 3) (by norm_num) (by norm_num) ⟨0, 0, -κ⟩) ?_
      intro h
      have hc : (-κ : K) = 0 := by simpa using congrArg Heis.c h
      exact (neg_ne_zero.mpr hκ0) hc
    · rw [hx]
      exact isExtraGood_of_heis_pair hK hι₁ hι₂ hcomm hceneq ⟨0, 0, -κ⟩
  ·
    obtain ⟨f, ι₁, ι₂, hvf, huf, hι₁, hι₂, hcomm, hceneq, hι1, hlast⟩ :=
      exists_heis_pair_orth hr h2 hv hvu hin
    refine ⟨?_, ?_⟩
    · rw [← hι1, orderOf_injective ι₁ hι₁]
      refine orderOf_eq_prime
        (Heis.pow_prime_eq_one (p := 3) (by norm_num) (by norm_num) ⟨1, 0, 0⟩) ?_
      intro h
      have ha : (1 : K) = 0 := by simpa using congrArg Heis.a h
      exact one_ne_zero ha
    · rw [← hι1]
      exact isExtraGood_of_heis_pair hK hι₁ hι₂ hcomm hceneq ⟨1, 0, 0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
