module

public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pzn_card_le_rank_add_one_of_ker {p : ℕ} [Fact p.Prime] {n : ℕ}
    (C0 : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ZMod p)
    (h : ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (C0 j k : ZMod p) * c k = 0) →
      c ∈ Submodule.span (ZMod p) ({v} : Set (Fin n → ZMod p))) :
    n ≤ Matrix.rank (C0.map (Int.castRingHom (ZMod p))) + 1 := by
  set A := C0.map (Int.castRingHom (ZMod p)) with hA
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hker : LinearMap.ker A.mulVecLin ≤ Submodule.span (ZMod p) ({v} : Set (Fin n → ZMod p)) := by
    intro c hc
    refine h c fun j => ?_
    have := congrFun (LinearMap.mem_ker.mp hc) j
    simpa [Matrix.mulVec, dotProduct, hA] using this
  have h2 : Module.finrank (ZMod p) (LinearMap.ker A.mulVecLin) ≤ 1 := by
    refine (Submodule.finrank_mono hker).trans ?_
    simpa using finrank_span_le_card (R := ZMod p) ({v} : Set (Fin n → ZMod p))
  have h3 : Matrix.rank A = Module.finrank (ZMod p) (LinearMap.range A.mulVecLin) := rfl
  have h4 : Module.finrank (ZMod p) (Fin n → ZMod p) = n := by simp
  omega

private theorem pzn_ker_span_of_prop {n : ℕ} {p : ℕ} [Fact p.Prime]
    (P : (Fin n → ZMod p) → Prop)
    (h : ∀ c d, P c → P d → c ≠ 0 → ∃ l : ZMod p, d = l • c) :
    ∃ v : Fin n → ZMod p, ∀ c, P c → c ∈ Submodule.span (ZMod p) ({v} : Set (Fin n → ZMod p)) := by
  by_cases hex : ∃ c, P c ∧ c ≠ 0
  · obtain ⟨c0, hc0, hc0ne⟩ := hex
    refine ⟨c0, fun c hc => ?_⟩
    obtain ⟨l, hl⟩ := h c0 c hc0 hc hc0ne
    rw [hl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · push Not at hex
    exact ⟨0, fun c hc => by rw [hex c hc]; exact Submodule.zero_mem _⟩

private theorem pzn_ker_span_zero {n : ℕ} {p : ℕ} [Fact p.Prime] {C0 : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (C0 j k : ZMod p) * c k = 0) → c = 0) :
    ∃ v : Fin n → ZMod p, ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (C0 j k : ZMod p) * c k = 0) →
      c ∈ Submodule.span (ZMod p) ({v} : Set (Fin n → ZMod p)) :=
  ⟨0, fun c hc => by rw [h c hc]; exact Submodule.zero_mem _⟩

theorem ggIntCartan_card_le_rank_add_one {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) :
    Fintype.card Λ ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 := by
  have key : ∀ {n : ℕ} (e : Fin n ≃ Λ) (C0 : Matrix (Fin n) (Fin n) ℤ),
      (∀ i j, C (e i) (e j) = C0 i j) →
      (∃ v : Fin n → ZMod p, ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (C0 j k : ZMod p) * c k = 0) →
        c ∈ Submodule.span (ZMod p) ({v} : Set (Fin n → ZMod p))) →
      Fintype.card Λ ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 := by
    intro n e C0 hC0 ⟨v, hv⟩
    have hsub : C.submatrix e e = C0 := by
      ext i j
      exact hC0 i j
    have h1 := pzn_card_le_rank_add_one_of_ker C0 v hv
    have hcard : Fintype.card Λ = n := by simpa using (Fintype.card_congr e).symm
    have hr : Matrix.rank (C0.map (Int.castRingHom (ZMod p))) =
        Matrix.rank (C.map (Int.castRingHom (ZMod p))) := by
      rw [← hsub, ← Matrix.submatrix_map]
      exact Matrix.rank_submatrix _ e e
    rw [hcard, ← hr]
    exact h1
  have hp : p.Prime := hpf.out
  rcases ggIntCartan_models hM hC with
    ⟨n, e, hn, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4 | hF4⟩ | ⟨e, hG2 | hG2⟩
  · exact key e _ hA (pzn_ker_span_of_prop _ fun c d hc hd hne =>
      ggCartanA_ker_le_one c d hc hd hne)
  · exact key e _ hB (pzn_ker_span_zero (ggCartanB_ker_zero hp2 (by omega)))
  · exact key e _ hCC (pzn_ker_span_zero (ggCartanC_ker_zero hp2 (by omega)))
  · exact key e _ hD (pzn_ker_span_zero (ggCartanD_ker_zero hp2 (by omega)))
  · by_cases hp3 : p = 3
    · subst hp3
      refine key e _ hE6 ⟨![1, 0, 2, 0, 1, 2], fun c hc => ?_⟩
      have hcE : ∀ j, ∑ k, (CartanMatrix.E₆ j k : ZMod 3) * c k = 0 := by
        intro j
        have := hc j
        simpa [CartanMatrix.E_six_eq] using this
      have hk := ggCartanE₆_ker_coord c hcE
      have : c = c 0 • (![1, 0, 2, 0, 1, 2] : Fin 6 → ZMod 3) := by
        funext k
        simp [hk k, mul_comm]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · exact key e _ hE6 (pzn_ker_span_zero (ggCartanE6Ind_ker_zero hp3))
  · exact key e _ hE7 (pzn_ker_span_zero (ggCartanE7_ker_zero hp2))
  · exact key e _ hE8 (pzn_ker_span_zero (ggCartanE8_ker_zero hp2))
  · exact key e _ hF4 (pzn_ker_span_zero (ggCartanF4_ker_zero hp2))
  · refine key e (Matrix.transpose CartanMatrix.F₄) (fun i j => hF4 i j) ?_
    exact pzn_ker_span_zero (ggCartan_ker_zero_of_not_dvd_det (Matrix.transpose CartanMatrix.F₄)
      (by rw [Matrix.det_transpose, CartanMatrix.F₄_det]
          exact ggTor_not_dvd_small hp hp2 (by norm_num)))
  · exact key e _ hG2 (pzn_ker_span_zero (ggCartanG2_ker_zero hp2))
  · refine key e (Matrix.transpose CartanMatrix.G₂) (fun i j => hG2 i j) ?_
    exact pzn_ker_span_zero (ggCartan_ker_zero_of_not_dvd_det (Matrix.transpose CartanMatrix.G₂)
      (by rw [Matrix.det_transpose, CartanMatrix.G₂_det]
          exact ggTor_not_dvd_small hp hp2 (by norm_num)))

theorem ggIntCartan_A_or_E6_of_nonzero_kernel {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (hker : ∃ κ : Λ → ZMod p, κ ≠ 0 ∧
      ∀ i, ∑ j, (C i j : ZMod p) * κ j = 0) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) := by
  obtain ⟨κ, hκ0, hκ⟩ := hker
  have hdet : ∀ {n : ℕ} {T : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ),
      (∀ i j, C (e i) (e j) = T i j) → (T.det : ZMod p) ≠ 0 → False := by
    intro n T e he hT
    apply hκ0
    have hv : ∀ i, ∑ j, (T i j : ZMod p) * κ (e j) = 0 := fun i => by
      rw [← hκ (e i)]
      exact Fintype.sum_equiv e _ _ fun j => by rw [he]
    have hmap : ((Int.castRingHom (ZMod p)).mapMatrix T).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact hT
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hmap
      (funext fun i => by simpa [Matrix.mulVec, dotProduct] using hv i)
    funext k
    simpa using congrFun h0 (e.symm k)
  have h1 : ((1 : ℤ) : ZMod p) ≠ 0 := by simp
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    simpa using zmod_two_ne_zero hp2
  rcases ggIntCartan_models hM hC with
    ⟨n, e, hn, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF | hF⟩ | ⟨e, hG | hG⟩
  · left
    have hzero : ((n + 1 : ℕ) : ZMod p) = 0 := by
      by_contra h
      apply hdet e hA
      rw [CartanMatrix.A_det]
      push_cast at h ⊢
      exact h
    exact ⟨n, e, hn, (ZMod.natCast_eq_zero_iff (n + 1) p).mp hzero, hA⟩
  · exact (hdet e hB (by rw [CartanMatrix.B_det (by omega)]; exact h2)).elim
  · exact (hdet e hCC (by rw [CartanMatrix.C_det (by omega)]; exact h2)).elim
  · have h4 : ((4 : ℤ) : ZMod p) ≠ 0 := by
      have heq : ((4 : ℤ) : ZMod p) = ((2 : ℤ) : ZMod p) * ((2 : ℤ) : ZMod p) := by
        norm_num
      rw [heq]
      exact mul_ne_zero h2 h2
    exact (hdet e hD (by rw [CartanMatrix.D_det (by omega)]; exact h4)).elim
  · right
    have hp3 : p = 3 := by
      have hzero : (3 : ZMod p) = 0 := by
        by_contra h
        apply hdet e hE6
        rw [CartanMatrix.E_det (by norm_num : 3 ≤ 6)]
        norm_num only
        exact h
      have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
      exact ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left hpf.out.ne_one
    exact ⟨hp3, e, hE6⟩
  · exact (hdet e hE7 (by rw [CartanMatrix.E₇_det]; exact h2)).elim
  · exact (hdet e hE8 (by rw [CartanMatrix.E₈_det]; exact h1)).elim
  · exact (hdet e hF (by rw [CartanMatrix.F₄_det]; exact h1)).elim
  · exact (hdet (T := CartanMatrix.F₄.transpose) e hF
      (by rw [Matrix.det_transpose, CartanMatrix.F₄_det]; exact h1)).elim
  · exact (hdet e hG (by rw [CartanMatrix.G₂_det]; exact h1)).elim
  · exact (hdet (T := CartanMatrix.G₂.transpose) e hG
      (by rw [Matrix.det_transpose, CartanMatrix.G₂_det]; exact h1)).elim

theorem ggIntCartan_A_or_E6_of_rank_lt {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hr : Matrix.rank (C.map (Int.castRingHom (ZMod p))) < Fintype.card Λ) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  let A := C.map (Int.castRingHom (ZMod p))
  have hk : A.mulVecLin.ker ≠ ⊥ := by
    intro hbot
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hbot] at h
    simp only [finrank_bot, add_zero, Module.finrank_pi] at h
    change Matrix.rank A = Fintype.card Λ at h
    exact (Nat.ne_of_lt hr) h
  obtain ⟨κ, hκ, hκ0⟩ := (Submodule.ne_bot_iff _).mp hk
  apply ggIntCartan_A_or_E6_of_nonzero_kernel hM hC hp2
  refine ⟨κ, hκ0, fun i => ?_⟩
  have hz := congrFun (LinearMap.mem_ker.mp hκ) i
  simpa [A, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using hz

theorem ggIntCartan_four_le_rank {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {p : ℕ} [hpf : Fact p.Prime]
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (h4 : 4 ≤ Fintype.card Λ) :
    4 ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p))) := by
  classical
  by_cases h5 : 5 ≤ Fintype.card Λ
  · have hle := ggIntCartan_card_le_rank_add_one hM hC p hp2
    omega
  · have hcard : Fintype.card Λ = 4 := by omega
    by_contra hrank
    have hlt4 : Matrix.rank (C.map (Int.castRingHom (ZMod p))) < 4 :=
      Nat.lt_of_not_ge hrank
    have hr : Matrix.rank (C.map (Int.castRingHom (ZMod p))) < Fintype.card Λ := by
      omega
    rcases ggIntCartan_A_or_E6_of_rank_lt hM hC hp2 hr with
      ⟨n, e, hn, hpdiv, hA⟩ | ⟨hp3, e, hE6⟩
    · have hn4 : n = 4 := by simpa [hcard] using Fintype.card_congr e
      have hpdiv5 : p ∣ 5 := by simpa [hn4] using hpdiv
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_five).mp hpdiv5)
    · have hc : 6 = 4 := by simpa [hcard] using Fintype.card_congr e
      omega


private theorem fixed_axis_comp_rank_lt {k U V W : Type} [Field k]
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module k U] [Module k V]
    [Module k W] [FiniteDimensional k V] (f : U →ₗ[k] V) (a : V →ₗ[k] W)
    {z : V} (hz : z ≠ 0) (hzker : a z = 0) {n : ℕ}
    (hdim : Module.finrank k V ≤ n) : Module.finrank k (a.comp f).range < n := by
  have hk : 1 ≤ Module.finrank k a.ker :=
    Submodule.one_le_finrank_iff.mpr ((Submodule.ne_bot_iff _).mpr
      ⟨z, LinearMap.mem_ker.mpr hzker, hz⟩)
  have hle := Submodule.finrank_mono (LinearMap.range_comp_le_range f a)
  have ha := LinearMap.finrank_range_add_finrank_ker a
  omega

theorem ggIntCartan_A_or_E6_of_finrank_le {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hαh : ∀ i j, α i (h j) = (C i j : ZMod p))
    {z : V} (hz : z ≠ 0) (hzα : ∀ i, α i z = 0)
    (hdim : Module.finrank (ZMod p) V ≤ Fintype.card Λ) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  let f : (Λ → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  let a : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi α
  have hcomp : a.comp f = (C.map (Int.castRingHom (ZMod p))).mulVecLin := by
    refine LinearMap.pi_ext fun j r => ?_
    funext i
    simp [f, a, hαh, Matrix.mulVec_single]
    exact mul_comm _ _
  have hzker : a z = 0 := by
    funext i
    exact hzα i
  have hr := fixed_axis_comp_rank_lt f a hz hzker hdim
  apply ggIntCartan_A_or_E6_of_rank_lt hM hC hp2
  have hrank : Module.finrank (ZMod p) (a.comp f).range =
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) := by
    rw [hcomp]
    rfl
  omega


private theorem pzn_finrank_le {k U V W : Type*} [Field k] [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup W] [Module k U] [Module k V] [Module k W] [FiniteDimensional k U]
    [FiniteDimensional k V] (f : U →ₗ[k] V) (a : V →ₗ[k] W) {z : V} (hz : z ≠ 0)
    (hzker : a z = 0) (h : Module.finrank k (a.comp f).ker ≤ 1) :
    Module.finrank k U ≤ Module.finrank k V := by
  have hker_ne_bot : a.ker ≠ ⊥ :=
    (Submodule.ne_bot_iff a.ker).mpr ⟨z, by rw [LinearMap.mem_ker]; exact hzker, hz⟩
  have hker_ge : 1 ≤ Module.finrank k a.ker := Submodule.one_le_finrank_iff.mpr hker_ne_bot
  have hrange_le : Module.finrank k (a.comp f).range ≤ Module.finrank k a.range :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range f a)
  have ha := LinearMap.finrank_range_add_finrank_ker a
  have hcomp := LinearMap.finrank_range_add_finrank_ker (a.comp f)
  omega

theorem ggPZ_card_le_finrank {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hαh : ∀ i j, α i (h j) = (C i j : ZMod p)) {z : V} (hz : z ≠ 0) (hzα : ∀ i, α i z = 0) :
    Fintype.card Λ ≤ Module.finrank (ZMod p) V := by
  classical
  let f : (Λ → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  let a : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi α
  have hcomp : a.comp f = (C.map (Int.castRingHom (ZMod p))).mulVecLin := by
    refine LinearMap.pi_ext fun j r => ?_
    funext i
    simp [f, a, hαh, Matrix.mulVec_single]
    exact mul_comm _ _
  have hz0 : a z = 0 := by
    funext i
    exact hzα i
  have hker : Module.finrank (ZMod p) (a.comp f).ker ≤ 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (a.comp f)
    have h2 : Module.finrank (ZMod p) (a.comp f).range =
        Matrix.rank (C.map (Int.castRingHom (ZMod p))) := by
      rw [hcomp]
      rfl
    have h3 := ggIntCartan_card_le_rank_add_one hM hC p hp2
    have h4 : Module.finrank (ZMod p) (Λ → ZMod p) = Fintype.card Λ := by simp
    omega
  have := pzn_finrank_le f a hz hz0 hker
  simpa using this

end CFSG.StandardType

end
