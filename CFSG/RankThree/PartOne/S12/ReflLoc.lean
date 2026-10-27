module

public import CFSG.RankThree.PartOne.S12.ReflSet

public section

namespace CFSG.RankThree.PartOne

namespace ReflF

open Module LinearMap

open scoped _root_.Classical

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Dim

theorem ReflData.range_nop (h2 : (2 : K) ≠ 0) {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K}
    (h : ReflData T r φ) : LinearMap.range (Nop T) = K ∙ r := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [h.nop_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨(2 : K)⁻¹ • r, ?_⟩
    rw [h.nop_apply, map_smul, h.pair, smul_eq_mul, inv_mul_cancel₀ h2, one_smul]

theorem ReflData.finrank_range_nop (h2 : (2 : K) ≠ 0) {T : V ≃ₗ[K] V} {r : V}
    {φ : V →ₗ[K] K} (h : ReflData T r φ) : finrank K (LinearMap.range (Nop T)) = 1 := by
  rw [h.range_nop h2]
  exact finrank_span_singleton h.ne

theorem ReflData.finrank_ker_nop [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ) {n : ℕ}
    (hV : finrank K V = n + 1) : finrank K (LinearMap.ker (Nop T)) = n := by
  have := LinearMap.finrank_range_add_finrank_ker (Nop T)
  rw [h.finrank_range_nop h2, hV] at this
  omega

end Dim

section Basic

theorem IsRSet.sub {𝒟 P : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hsub : P ⊆ 𝒟)
    (hcl : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ ∈ P) : IsRSet P where
  refl T hT := h.refl T (hsub hT)
  conj := hcl
  ord T hT S hS := h.ord T (hsub hT) S (hsub hS)

theorem IsRSet.inv_eq {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T : V ≃ₗ[K] V} (hT : T ∈ 𝒟) :
    T⁻¹ = T := by
  obtain ⟨r, φ, hd⟩ := h.refl T hT
  exact inv_eq_of_mul_eq_one_right hd.mul_self

theorem IsRSet.conj_comm_iff {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T : V ≃ₗ[K] V}
    (hT : T ∈ 𝒟) (S : V ≃ₗ[K] V) : T * (T * S * T⁻¹) = (T * S * T⁻¹) * T ↔ T * S = S * T := by
  rw [h.inv_eq hT]
  have hTT : T * T = 1 := by
    obtain ⟨r, φ, hd⟩ := h.refl T hT
    exact hd.mul_self
  have e1 : T * (T * S * T) = S * T := by
    calc T * (T * S * T) = (T * T) * S * T := by group
      _ = S * T := by rw [hTT, one_mul]
  have e2 : (T * S * T) * T = T * S := by
    calc (T * S * T) * T = T * S * (T * T) := by group
      _ = T * S := by rw [hTT, mul_one]
  rw [e1, e2]
  exact eq_comm

theorem IsRSet.roots_indep [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T S : V ≃ₗ[K] V} (hT : T ∈ 𝒟) (hS : S ∈ 𝒟)
    (hne : T ≠ S) {r s : V} {φ ψ : V →ₗ[K] K} (hd : ReflData T r φ) (hd' : ReflData S s ψ)
    (a b : K) (hab : a • r + b • s = 0) : a = 0 ∧ b = 0 := by
  have e1 : 2 * a + b * φ s = 0 := by
    have := congrArg φ hab
    simpa [map_add, map_smul, hd.pair, smul_eq_mul, mul_comm] using this
  have e2 : a * ψ r + 2 * b = 0 := by
    have := congrArg ψ hab
    simpa [map_add, map_smul, hd'.pair, smul_eq_mul, mul_comm] using this
  rcases dichotomy h2 h3 hd hd' hne (h.ord T hT S hS hne) with ⟨h1, h1'⟩ | hb
  · rw [h1] at e1
    rw [h1'] at e2
    refine ⟨?_, ?_⟩
    · have : (2 : K) * a = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left h2
    · have : (2 : K) * b = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_left h2
  · have hx : φ s ≠ 0 := fun e => by rw [e, zero_mul] at hb; exact zero_ne_one hb
    have h3b : (3 : K) * (b * φ s) = 0 := by
      linear_combination 2 * φ s * e2 - e1 - 2 * a * hb
    have hb0 : b = 0 := by
      rcases mul_eq_zero.1 h3b with h' | h'
      · exact absurd h' h3
      · exact (mul_eq_zero.1 h').resolve_right hx
    refine ⟨?_, hb0⟩
    rw [hb0] at e1
    have : (2 : K) * a = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_left h2

theorem IsRSet.two_le_finrank [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 P : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hsub : P ⊆ 𝒟) {T S : V ≃ₗ[K] V} (hT : T ∈ P)
    (hS : S ∈ P) (hne : T ≠ S) : 2 ≤ finrank K (Uspan P) := by
  obtain ⟨r, φ, hd⟩ := h.refl T (hsub hT)
  obtain ⟨s, ψ, hd'⟩ := h.refl S (hsub hS)
  have hli : LinearIndependent K ![r, s] := by
    rw [LinearIndependent.pair_iff]
    exact fun a b hab => h.roots_indep h2 h3 (hsub hT) (hsub hS) hne hd hd' a b hab
  have hrange : ∀ {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K}, T ∈ P → ReflData T r φ →
      r ∈ Uspan P := by
    intro T r φ hT hd
    refine Submodule.subset_span ⟨T, hT, ?_⟩
    rw [hd.range_nop h2]
    exact Submodule.mem_span_singleton_self r
  have hle : Submodule.span K (Set.range ![r, s]) ≤ Uspan P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hrange hT hd
    · exact hrange hS hd'
  have h2' := finrank_span_eq_card hli
  have := Submodule.finrank_mono hle
  rw [h2'] at this
  simpa using this

end Basic

section Planar

theorem IsRSet.eq_of_parallel [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {W Z : V ≃ₗ[K] V} (hW : W ∈ 𝒟) (hZ : Z ∈ 𝒟)
    {w z : V} {χ χ' : V →ₗ[K] K} (hdW : ReflData W w χ) (hdZ : ReflData Z z χ') {c : K}
    (hwz : w = c • z) : W = Z := by
  by_contra hne
  have hc : c ≠ 0 := by
    rintro rfl
    exact hdW.ne (by rw [hwz, zero_smul])
  have e1 : c * χ z = 2 := by
    have := hdW.pair
    rwa [hwz, map_smul, smul_eq_mul] at this
  have e2 : χ' w = c * 2 := by
    rw [hwz, map_smul, smul_eq_mul, hdZ.pair]
  have h4 : χ z * χ' w = 4 := by
    rw [e2]
    linear_combination 2 * e1
  have htr := hdW.trace_nop_comp_nop hdZ
  rw [h4] at htr
  rcases h.dich h2 h3 hW hZ hne with ⟨h0, -, -⟩ | ⟨h1, -, -, -⟩
  · rw [h0, map_zero] at htr
    have : (2 : K) * 2 = 0 := by linear_combination -htr
    exact h2 ((mul_eq_zero.1 this).resolve_left h2)
  · rw [h1] at htr
    have : (3 : K) = 0 := by linear_combination -htr
    exact h3 this

theorem third_point (h3 : (3 : K) ≠ 0) {T S W : V ≃ₗ[K] V} {r s w : V}
    {φ ψ χ : V →ₗ[K] K} (hT : ReflData T r φ) (hS : ReflData S s ψ) (hW : ReflData W w χ)
    (hbr : φ s * ψ r = 1) (hWT : φ w * χ r = 1) (hWS : ψ w * χ s = 1)
    (hw : w ∈ Submodule.span K {r, s}) : ∃ c : K, w = c • T s := by
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hw
  have hφw : φ w = 2 * α + φ s * β := by
    rw [← hαβ, map_add, map_smul, map_smul, hT.pair, smul_eq_mul, smul_eq_mul]
    ring
  have hψw : ψ w = ψ r * α + 2 * β := by
    rw [← hαβ, map_add, map_smul, map_smul, hS.pair, smul_eq_mul, smul_eq_mul]
    ring
  have hχw : α * χ r + β * χ s = 2 := by
    have := hW.pair
    rw [← hαβ, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact this
  rw [hφw] at hWT
  rw [hψw] at hWS
  set a := φ s with ha
  set b := ψ r with hb
  have key : 3 * b * (α + a * β) ^ 2 = 0 := by
    linear_combination (-((2 * α + a * β) * (b * α + 2 * β))) * hχw +
      (α * (b * α + 2 * β)) * hWT + (β * (2 * α + a * β)) * hWS +
      (4 * α * β + 3 * a * β ^ 2) * hbr
  have hb0 : b ≠ 0 := fun e => by rw [e, mul_zero] at hbr; exact zero_ne_one hbr
  have hα : α + a * β = 0 := by
    have : (α + a * β) ^ 2 = 0 := by
      rcases mul_eq_zero.1 key with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact absurd h'' h3
        · exact absurd h'' hb0
      · exact h'
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  refine ⟨β, ?_⟩
  rw [← hαβ, hT.apply s]
  have : α = -(a * β) := by linear_combination hα
  rw [this]
  module

end Planar

section PB

theorem pb_identity [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 P : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hsub : P ⊆ 𝒟)
    (hcl : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ ∈ P)
    (hpb : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → a * b ≠ b * a) (hne : P.Nonempty) :
    ∃ lam : K, (∀ y ∈ Uspan P, Ssum P y = lam • y) ∧
      (finrank K (Uspan P) : K) * lam = 2 * P.card ∧ 2 * lam = 3 + P.card := by
  have hP := h.sub hsub hcl
  have hconn : Conn P := by
    intro Q hQ hQne hQcl
    obtain ⟨x, hx⟩ := hQne
    apply Finset.Subset.antisymm hQ
    intro y hy
    by_cases hxy : x = y
    · rw [← hxy]
      exact hx
    · exact hQcl x hx y hy (hpb x (hQ hx) y hy hxy)
  obtain ⟨lam, -, hb, hm, hs⟩ := trace_identity h2 h3 hP hconn hne
  refine ⟨lam, hs, hm, ?_⟩
  obtain ⟨T, hT⟩ := hne
  have hTb := hb T hT
  have hfil : P.filter (fun S => T * S ≠ S * T) = P.erase T := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hS, hn⟩
      exact ⟨fun e => hn (by rw [e]), hS⟩
    · rintro ⟨hne', hS⟩
      exact ⟨hS, hpb T hT S hS (Ne.symm hne')⟩
  rw [hfil, Finset.card_erase_of_mem hT] at hTb
  have hcard : 1 ≤ P.card := Finset.card_pos.2 ⟨T, hT⟩
  rw [Nat.cast_sub hcard] at hTb
  rw [hTb]
  push_cast
  ring

end PB

section Comm

@[expose] noncomputable def commSet (𝒟 : Finset (V ≃ₗ[K] V)) (t : V ≃ₗ[K] V) : Finset (V ≃ₗ[K] V) :=
  𝒟.filter fun s => s ≠ t ∧ t * s = s * t

theorem mem_commSet {𝒟 : Finset (V ≃ₗ[K] V)} {t s : V ≃ₗ[K] V} :
    s ∈ commSet 𝒟 t ↔ s ∈ 𝒟 ∧ s ≠ t ∧ t * s = s * t := by
  simp [commSet]

theorem IsRSet.commSet_closed {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {t : V ≃ₗ[K] V}
    {a b : V ≃ₗ[K] V} (ha : a ∈ commSet 𝒟 t) (hb : b ∈ commSet 𝒟 t) :
    a * b * a⁻¹ ∈ commSet 𝒟 t := by
  obtain ⟨ha𝒟, hat, hca⟩ := mem_commSet.1 ha
  obtain ⟨hb𝒟, hbt, hcb⟩ := mem_commSet.1 hb
  refine mem_commSet.2 ⟨h.conj a ha𝒟 b hb𝒟, ?_, ?_⟩
  · intro e
    apply hbt
    have haa : a * a = 1 := by
      obtain ⟨r, φ, hd⟩ := h.refl a ha𝒟
      exact hd.mul_self
    rw [h.inv_eq ha𝒟] at e
    have : b = a * t * a := by
      calc b = (a * a) * b * (a * a) := by rw [haa, one_mul, mul_one]
        _ = a * (a * b * a) * a := by group
        _ = a * t * a := by rw [e]
    rw [this]
    have hat' : a * t = t * a := hca.symm
    calc a * t * a = t * a * a := by rw [hat']
      _ = t := by rw [mul_assoc, haa, mul_one]
  · have haa : a * a = 1 := by
      obtain ⟨r, φ, hd⟩ := h.refl a ha𝒟
      exact hd.mul_self
    rw [h.inv_eq ha𝒟]
    have e1 : t * a = a * t := hca
    have e2 : t * b = b * t := hcb
    calc t * (a * b * a) = (t * a) * b * a := by group
      _ = a * (t * b) * a := by rw [e1]; group
      _ = a * (b * t) * a := by rw [e2]
      _ = a * b * (t * a) := by group
      _ = a * b * (a * t) := by rw [e1]
      _ = (a * b * a) * t := by group

end Comm

@[expose] noncomputable def noncommSet (𝒟 : Finset (V ≃ₗ[K] V)) (t : V ≃ₗ[K] V) :
    Finset (V ≃ₗ[K] V) :=
  𝒟.filter fun S => t * S ≠ S * t

theorem card_split {𝒟 : Finset (V ≃ₗ[K] V)} {t : V ≃ₗ[K] V} (ht : t ∈ 𝒟) :
    𝒟.card = (commSet 𝒟 t).card + 1 + (noncommSet 𝒟 t).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := 𝒟) (fun S => t * S = S * t)
  have hcomm : 𝒟.filter (fun S => t * S = S * t) = insert t (commSet 𝒟 t) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, mem_commSet]
    constructor
    · rintro ⟨hS, hc⟩
      by_cases hSt : S = t
      · exact Or.inl hSt
      · exact Or.inr ⟨hS, hSt, hc⟩
    · rintro (rfl | ⟨hS, -, hc⟩)
      · exact ⟨ht, rfl⟩
      · exact ⟨hS, hc⟩
  have htnot : t ∉ commSet 𝒟 t := fun hmem => (mem_commSet.1 hmem).2.1 rfl
  rw [hcomm, Finset.card_insert_of_notMem htnot] at hsplit
  have hnc : 𝒟.filter (fun S => ¬ t * S = S * t) = noncommSet 𝒟 t := by
    ext S
    simp [noncommSet]
  rw [hnc] at hsplit
  omega

section Counting

variable [FiniteDimensional K V]

theorem card_comm_cast (hdim : finrank K V = 4) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hconn : Conn 𝒟) (hU : Uspan 𝒟 = ⊤)
    {t : V ≃ₗ[K] V} (ht : t ∈ 𝒟) : (((commSet 𝒟 t).card : ℕ) : K) = 3 := by
  obtain ⟨lam, -, hb, hm, -⟩ := trace_identity h2 h3 h hconn ⟨t, ht⟩
  have hb' : 2 * lam = 4 + (((noncommSet 𝒟 t).card : ℕ) : K) := hb t ht
  rw [hU, finrank_top, hdim] at hm
  have hsplitK : (((commSet 𝒟 t).card : ℕ) : K) + 1 + (((noncommSet 𝒟 t).card : ℕ) : K) =
      𝒟.card := by
    have := congrArg (Nat.cast (R := K)) (card_split ht)
    push_cast at this
    exact this.symm
  push_cast at hm
  set a : K := (((commSet 𝒟 t).card : ℕ) : K)
  set b : K := (((noncommSet 𝒟 t).card : ℕ) : K)
  have h2a : (2 : K) * (a - 3) = 0 := by
    linear_combination 2 * hb' + 2 * hsplitK - hm
  have := (mul_eq_zero.1 h2a).resolve_left h2
  linear_combination this

end Counting

section Dims

variable [FiniteDimensional K V]

theorem IsRSet.finrank_span_pair (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T S : V ≃ₗ[K] V} (hT : T ∈ 𝒟) (hS : S ∈ 𝒟)
    (hne : T ≠ S) {r s : V} {φ ψ : V →ₗ[K] K} (hd : ReflData T r φ) (hd' : ReflData S s ψ) :
    finrank K (Submodule.span K {r, s}) = 2 := by
  have hli : LinearIndependent K ![r, s] := by
    rw [LinearIndependent.pair_iff]
    exact fun a b hab => h.roots_indep h2 h3 hT hS hne hd hd' a b hab
  have h2' := finrank_span_eq_card hli
  have hr : Set.range ![r, s] = {r, s} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  rw [hr] at h2'
  simpa using h2'

omit [FiniteDimensional K V] in
theorem mem_Uspan_of_root {𝒟 : Finset (V ≃ₗ[K] V)} (h2 : (2 : K) ≠ 0) {T : V ≃ₗ[K] V}
    (hT : T ∈ 𝒟) {r : V} {φ : V →ₗ[K] K} (hd : ReflData T r φ) : r ∈ Uspan 𝒟 := by
  refine Submodule.subset_span ⟨T, hT, ?_⟩
  rw [hd.range_nop h2]
  exact Submodule.mem_span_singleton_self r

omit [FiniteDimensional K V] in
theorem Uspan_mono {P Q : Finset (V ≃ₗ[K] V)} (h : P ⊆ Q) : Uspan P ≤ Uspan Q :=
  Submodule.span_mono fun _ ⟨T, hT, hx⟩ => ⟨T, h hT, hx⟩

omit [FiniteDimensional K V] in
theorem Uspan_le_ker {P : Finset (V ≃ₗ[K] V)} {t : V ≃ₗ[K] V}
    (hP : ∀ s ∈ P, Nop t ∘ₗ Nop s = 0) : Uspan P ≤ LinearMap.ker (Nop t) := by
  rw [Uspan, Submodule.span_le]
  rintro x ⟨s, hs, y, rfl⟩
  have := LinearMap.congr_fun (hP s hs) y
  simpa using this

theorem IsRSet.commSet_finrank_lt (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {Δ : Finset (V ≃ₗ[K] V)} (h : IsRSet Δ) {w : V ≃ₗ[K] V} (hw : w ∈ Δ) :
    finrank K (Uspan (commSet Δ w)) < finrank K (Uspan Δ) := by
  obtain ⟨r, φ, hd⟩ := h.refl w hw
  have hsub : commSet Δ w ⊆ Δ := fun x hx => (mem_commSet.1 hx).1
  have hker : Uspan (commSet Δ w) ≤ LinearMap.ker (Nop w) := by
    refine Uspan_le_ker fun s hs => ?_
    obtain ⟨hsΔ, hsw, hc⟩ := mem_commSet.1 hs
    rcases h.dich h2 h3 hw hsΔ (Ne.symm hsw) with ⟨h0, -, -⟩ | ⟨-, -, -, hnc⟩
    · exact h0
    · exact absurd hc hnc
  have hle : Uspan (commSet Δ w) ≤ LinearMap.ker (Nop w) ⊓ Uspan Δ :=
    le_inf hker (Uspan_mono hsub)
  have hlt : LinearMap.ker (Nop w) ⊓ Uspan Δ < Uspan Δ := by
    refine lt_of_le_of_ne inf_le_right fun e => ?_
    have hr : r ∈ LinearMap.ker (Nop w) := by
      have : r ∈ LinearMap.ker (Nop w) ⊓ Uspan Δ := by
        rw [e]
        exact mem_Uspan_of_root h2 hw hd
      exact this.1
    rw [LinearMap.mem_ker, hd.nop_apply, hd.pair] at hr
    have : (2 : K) • r = 0 := hr
    exact hd.ne ((smul_eq_zero.1 this).resolve_left h2)
  exact lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt)

theorem card_le_one_of_finrank_lt_two (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 P : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hsub : P ⊆ 𝒟)
    (hlt : finrank K (Uspan P) < 2) : P.card ≤ 1 := by
  by_contra hcon
  obtain ⟨T, hT, S, hS, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < P.card)
  have := h.two_le_finrank h2 h3 hsub hT hS hne
  omega

end Dims

section Cases

variable [FiniteDimensional K V]

theorem IsRSet.pair_eq_one (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {𝒟 : Finset (V ≃ₗ[K] V)}
    (h : IsRSet 𝒟) {T S : V ≃ₗ[K] V} (hT : T ∈ 𝒟) (hS : S ∈ 𝒟) {r s : V}
    {φ ψ : V →ₗ[K] K} (hdT : ReflData T r φ) (hdS : ReflData S s ψ) (hne : T * S ≠ S * T) :
    φ s * ψ r = 1 := by
  have hTS : T ≠ S := fun e => hne (by rw [e])
  rcases h.dich h2 h3 hT hS hTS with ⟨-, -, hc⟩ | ⟨ht, -, -, -⟩
  · exact absurd hc hne
  · rw [hdT.trace_nop_comp_nop hdS] at ht
    exact ht

theorem caseConn (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {Δ : Finset (V ≃ₗ[K] V)} (h : IsRSet Δ) (hconn : Conn Δ) (hcard : ((Δ.card : ℕ) : K) = 3)
    (hno3 : ∀ x ∈ Δ, ∀ y ∈ Δ, ∀ z ∈ Δ, x ≠ y → x ≠ z → y ≠ z → x * y = y * x →
      x * z = z * x → y * z = z * y → False)
    (hle3 : finrank K (Uspan Δ) ≤ 3) :
    ∃ u ∈ Δ, ∃ v ∈ Δ, u ≠ v ∧ u * v ≠ v * u ∧ Δ = {u, v, u * v * u⁻¹} := by
  have hge : 3 ≤ Δ.card := by
    by_contra hlt
    have hc : Δ.card = 0 ∨ Δ.card = 1 ∨ Δ.card = 2 := by omega
    rcases hc with hc | hc | hc <;> rw [hc] at hcard <;> push_cast at hcard
    · exact h3 (by linear_combination -hcard)
    · exact h2 (by linear_combination -hcard)
    · exact one_ne_zero (by linear_combination -hcard)
  have hne : Δ.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨lam, -, hb, hm, -⟩ := trace_identity h2 h3 h hconn hne
  obtain ⟨u₀, hu₀, v₀, hv₀, huv₀⟩ := Finset.one_lt_card.1 (by omega : 1 < Δ.card)
  have hm2 : 2 ≤ finrank K (Uspan Δ) :=
    h.two_le_finrank h2 h3 (Finset.Subset.refl Δ) hu₀ hv₀ huv₀
  have hrel : ∀ w ∈ Δ, ((finrank K (Uspan Δ) : ℕ) : K) *
      (4 + (((noncommSet Δ w).card : ℕ) : K)) = 12 := by
    intro w hw
    have hbw : 2 * lam = 4 + (((noncommSet Δ w).card : ℕ) : K) := hb w hw
    calc ((finrank K (Uspan Δ) : ℕ) : K) * (4 + (((noncommSet Δ w).card : ℕ) : K))
        = (finrank K (Uspan Δ) : K) * (2 * lam) := by rw [hbw]
      _ = 2 * ((finrank K (Uspan Δ) : K) * lam) := by ring
      _ = 2 * (2 * (Δ.card : K)) := by rw [hm]
      _ = 12 := by rw [hcard]; norm_num
  have hsplit : ∀ w ∈ Δ, (((commSet Δ w).card : ℕ) : K) + 1 +
      (((noncommSet Δ w).card : ℕ) : K) = 3 := by
    intro w hw
    have := congrArg (Nat.cast (R := K)) (card_split hw)
    push_cast at this
    rw [← hcard]
    exact this.symm
  have hcases : finrank K (Uspan Δ) = 2 ∨ finrank K (Uspan Δ) = 3 := by omega
  rcases hcases with hm2' | hm3'
  ·
    have hpb : ∀ x ∈ Δ, ∀ y ∈ Δ, x ≠ y → x * y ≠ y * x := by
      intro x hx y hy hxy hcomm
      have hrw := hrel x hx
      rw [hm2'] at hrw
      have hsp := hsplit x hx
      push_cast at hrw
      have h2b : (2 : K) * ((((noncommSet Δ x).card : ℕ) : K) - 2) = 0 := by
        linear_combination hrw
      have hb2 : (((noncommSet Δ x).card : ℕ) : K) = 2 := by
        have := (mul_eq_zero.1 h2b).resolve_left h2
        linear_combination this
      have ha0 : (((commSet Δ x).card : ℕ) : K) = 0 := by linear_combination hsp - hb2
      have hlt := h.commSet_finrank_lt h2 h3 hx
      rw [hm2'] at hlt
      have hle1 : (commSet Δ x).card ≤ 1 :=
        card_le_one_of_finrank_lt_two h2 h3 h (fun z hz => (mem_commSet.1 hz).1) hlt
      have hy' : y ∈ commSet Δ x := mem_commSet.2 ⟨hy, Ne.symm hxy, hcomm⟩
      have hcard1 : (commSet Δ x).card = 1 :=
        le_antisymm hle1 (Finset.card_pos.2 ⟨y, hy'⟩)
      rw [hcard1] at ha0
      simp at ha0
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < Δ.card)
    refine ⟨u, hu, v, hv, huv, hpb u hu v hv huv, ?_⟩
    obtain ⟨r, φ, hdu⟩ := h.refl u hu
    obtain ⟨s, ψ, hdv⟩ := h.refl v hv
    have hspan : Submodule.span K {r, s} = Uspan Δ := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact mem_Uspan_of_root h2 hu hdu
        · exact mem_Uspan_of_root h2 hv hdv
      · rw [h.finrank_span_pair h2 h3 hu hv huv hdu hdv, hm2']
    have hz : u * v * u⁻¹ ∈ Δ := h.conj u hu v hv
    have hdz : ReflData (u * v * u⁻¹) (u s) (ψ ∘ₗ ((u.symm : V ≃ₗ[K] V) : V →ₗ[K] V)) :=
      hdv.conj u
    have hbr : φ s * ψ r = 1 := h.pair_eq_one h2 h3 hu hv hdu hdv (hpb u hu v hv huv)
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      by_cases hwu : w = u
      · exact Or.inl hwu
      by_cases hwv : w = v
      · exact Or.inr (Or.inl hwv)
      right
      right
      obtain ⟨w₀, χ, hdw⟩ := h.refl w hw
      have hWT : φ w₀ * χ r = 1 :=
        h.pair_eq_one h2 h3 hu hw hdu hdw (hpb u hu w hw (Ne.symm hwu))
      have hWS : ψ w₀ * χ s = 1 :=
        h.pair_eq_one h2 h3 hv hw hdv hdw (hpb v hv w hw (Ne.symm hwv))
      have hmem : w₀ ∈ Submodule.span K {r, s} := by
        rw [hspan]
        exact mem_Uspan_of_root h2 hw hdw
      obtain ⟨c, hc⟩ := third_point h3 hdu hdv hdw hbr hWT hWS hmem
      exact h.eq_of_parallel h2 h3 hw hz hdw hdz hc
    · rintro (rfl | rfl | rfl)
      · exact hu
      · exact hv
      · exact hz
  ·
    exfalso
    obtain ⟨w, hw⟩ := hne
    have hrw := hrel w hw
    rw [hm3'] at hrw
    have hsp := hsplit w hw
    push_cast at hrw
    have hb0 : (((noncommSet Δ w).card : ℕ) : K) = 0 := by
      have : (3 : K) * (((noncommSet Δ w).card : ℕ) : K) = 0 := by linear_combination hrw
      exact (mul_eq_zero.1 this).resolve_left h3
    have ha2 : (((commSet Δ w).card : ℕ) : K) = 2 := by linear_combination hsp - hb0
    have hCΔ : commSet Δ w ⊆ Δ := fun x hx => (mem_commSet.1 hx).1
    have hCcl : ∀ x ∈ commSet Δ w, ∀ y ∈ commSet Δ w, x * y * x⁻¹ ∈ commSet Δ w :=
      fun x hx y hy => h.commSet_closed hx hy
    have hCpb : ∀ x ∈ commSet Δ w, ∀ y ∈ commSet Δ w, x ≠ y → x * y ≠ y * x := by
      intro x hx y hy hxy hcomm
      obtain ⟨hxΔ, hxw, cx⟩ := mem_commSet.1 hx
      obtain ⟨hyΔ, hyw, cy⟩ := mem_commSet.1 hy
      exact hno3 w hw x hxΔ y hyΔ (Ne.symm hxw) (Ne.symm hyw) hxy cx cy hcomm
    have hCge : 2 ≤ (commSet Δ w).card := by
      by_contra hlt
      have hc : (commSet Δ w).card = 0 ∨ (commSet Δ w).card = 1 := by omega
      rcases hc with hc | hc <;> rw [hc] at ha2 <;> push_cast at ha2
      · exact h2 (by linear_combination -ha2)
      · exact one_ne_zero (by linear_combination -ha2)
    obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Finset.one_lt_card.1 (by omega : 1 < (commSet Δ w).card)
    obtain ⟨lamC, -, hmC, h2C⟩ := pb_identity h2 h3 h hCΔ hCcl hCpb ⟨x₀, hx₀⟩
    have hmC2 : 2 ≤ finrank K (Uspan (commSet Δ w)) :=
      h.two_le_finrank h2 h3 hCΔ hx₀ hy₀ hxy₀
    have hmC3 := h.commSet_finrank_lt h2 h3 hw
    rw [hm3'] at hmC3
    have hmCfin : finrank K (Uspan (commSet Δ w)) = 2 := by omega
    rw [hmCfin] at hmC
    push_cast at hmC
    exact one_ne_zero (by linear_combination ha2 - h2C + hmC)

theorem pb_card_cases (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {Δ P Q : Finset (V ≃ₗ[K] V)} (h : IsRSet Δ) (hP : P ⊆ Δ) (hQ : Q ⊆ Δ)
    (hcl : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ ∈ P)
    (hpb : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → a * b ≠ b * a) (hPne : P.Nonempty) (hQne : Q.Nonempty)
    (hcross : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hdisj : Disjoint P Q)
    {W : Submodule K V} (hW : finrank K W = 3) (hUW : Uspan Δ ≤ W) :
    ((P.card : ℕ) : K) = 1 ∨ ((P.card : ℕ) : K) = 3 := by
  obtain ⟨lam, hs, hm, h2l⟩ := pb_identity h2 h3 h hP hcl hpb hPne
  have hPW : Uspan P ≤ W := (Uspan_mono hP).trans hUW
  have hm3 : finrank K (Uspan P) ≤ 3 := (Submodule.finrank_mono hPW).trans hW.le
  obtain ⟨T, hT⟩ := hPne
  obtain ⟨rT, φT, hdT⟩ := h.refl T (hP hT)
  have hm1 : 1 ≤ finrank K (Uspan P) := by
    have hle : K ∙ rT ≤ Uspan P := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact mem_Uspan_of_root h2 hT hdT
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hdT.ne] at this
    exact this
  have hcases : finrank K (Uspan P) = 1 ∨ finrank K (Uspan P) = 2 ∨ finrank K (Uspan P) = 3 := by
    omega
  rcases hcases with hm' | hm' | hm'
  · left
    rw [hm'] at hm
    push_cast at hm
    have h3n : (3 : K) * (((P.card : ℕ) : K) - 1) = 0 := by linear_combination h2l - 2 * hm
    have := (mul_eq_zero.1 h3n).resolve_left h3
    linear_combination this
  · right
    rw [hm'] at hm
    push_cast at hm
    linear_combination h2l - hm
  · exfalso
    have hUP : Uspan P = W := Submodule.eq_of_le_of_finrank_eq hPW (by rw [hm', hW])
    obtain ⟨y, hy⟩ := hQne
    obtain ⟨ry, φy, hdy⟩ := h.refl y (hQ hy)
    have hry : ry ∈ Uspan P := by
      rw [hUP]
      exact hUW ((Uspan_mono hQ) (mem_Uspan_of_root h2 hy hdy))
    have hS0 : Ssum P ry = 0 := by
      rw [Ssum_apply]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxy : x ≠ y := fun e => Finset.disjoint_left.1 hdisj hx (e ▸ hy)
      rcases h.dich h2 h3 (hP hx) (hQ hy) hxy with ⟨h0, -, -⟩ | ⟨-, -, -, hnc⟩
      · have := LinearMap.congr_fun h0 ((2 : K)⁻¹ • ry)
        have hNy : Nop y ((2 : K)⁻¹ • ry) = ry := by
          rw [hdy.nop_apply, map_smul, hdy.pair, smul_eq_mul, inv_mul_cancel₀ h2, one_smul]
        rw [LinearMap.comp_apply, hNy, LinearMap.zero_apply] at this
        exact this
      · exact absurd (hcross x hx y hy) hnc
    have hlam0 : lam = 0 := by
      have := hs ry hry
      rw [hS0] at this
      have hz : lam • ry = 0 := this.symm
      exact (smul_eq_zero.1 hz).resolve_right hdy.ne
    rw [hm'] at hm
    push_cast at hm
    rw [hlam0] at hm h2l
    have hn0 : ((P.card : ℕ) : K) = 0 := by
      have : (2 : K) * ((P.card : ℕ) : K) = 0 := by linear_combination -hm
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [hn0] at h2l
    exact h3 (by linear_combination -h2l)

theorem caseDisc (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {Δ : Finset (V ≃ₗ[K] V)} (h : IsRSet Δ) (hnc : ¬ Conn Δ) (hcard : ((Δ.card : ℕ) : K) = 3)
    (hno3 : ∀ x ∈ Δ, ∀ y ∈ Δ, ∀ z ∈ Δ, x ≠ y → x ≠ z → y ≠ z → x * y = y * x →
      x * z = z * x → y * z = z * y → False)
    {W : Submodule K V} (hW : finrank K W = 3) (hUW : Uspan Δ ≤ W) : False := by
  unfold Conn at hnc
  push Not at hnc
  obtain ⟨P, hPΔ, hPne, hPcl, hPD⟩ := hnc
  have hQne : (Δ \ P).Nonempty := by
    by_contra hQ
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hQ
    exact hPD (Finset.Subset.antisymm hPΔ hQ)
  have hQΔ : Δ \ P ⊆ Δ := Finset.sdiff_subset
  have hcross : ∀ x ∈ P, ∀ y ∈ Δ \ P, x * y = y * x := by
    intro x hx y hy
    by_contra hne
    exact (Finset.mem_sdiff.1 hy).2 (hPcl x hx y (Finset.mem_sdiff.1 hy).1 hne)
  have hPclosed : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ ∈ P := by
    intro a ha b hb
    have haΔ := hPΔ ha
    have hmem := h.conj a haΔ b (hPΔ hb)
    by_cases hcomm : a * b = b * a
    · have : a * b * a⁻¹ = b := by rw [mul_inv_eq_iff_eq_mul]; exact hcomm
      rw [this]
      exact hb
    · refine hPcl a ha _ hmem ?_
      intro e
      exact hcomm ((h.conj_comm_iff haΔ b).1 e)
  have hQclosed : ∀ a ∈ Δ \ P, ∀ b ∈ Δ \ P, a * b * a⁻¹ ∈ Δ \ P := by
    intro a ha b hb
    have haΔ := (Finset.mem_sdiff.1 ha).1
    have hbΔ := (Finset.mem_sdiff.1 hb).1
    refine Finset.mem_sdiff.2 ⟨h.conj a haΔ b hbΔ, fun hP => ?_⟩
    have hc : a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := (hcross _ hP a ha).symm
    have hab : a * b = b * a := (h.conj_comm_iff haΔ b).1 hc
    have : a * b * a⁻¹ = b := by rw [mul_inv_eq_iff_eq_mul]; exact hab
    rw [this] at hP
    exact (Finset.mem_sdiff.1 hb).2 hP
  have hPpb : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → a * b ≠ b * a := by
    intro x hx y hy hxy hcomm
    obtain ⟨z, hz⟩ := hQne
    have hzP : z ∉ P := (Finset.mem_sdiff.1 hz).2
    exact hno3 x (hPΔ hx) y (hPΔ hy) z (Finset.mem_sdiff.1 hz).1 hxy
      (fun e => hzP (e ▸ hx)) (fun e => hzP (e ▸ hy)) hcomm (hcross x hx z hz) (hcross y hy z hz)
  have hQpb : ∀ a ∈ Δ \ P, ∀ b ∈ Δ \ P, a ≠ b → a * b ≠ b * a := by
    intro x hx y hy hxy hcomm
    obtain ⟨z, hz⟩ := hPne
    have hzP : z ∉ Δ \ P := fun hmem => (Finset.mem_sdiff.1 hmem).2 hz
    exact hno3 x (Finset.mem_sdiff.1 hx).1 y (Finset.mem_sdiff.1 hy).1 z (hPΔ hz) hxy
      (fun e => hzP (e ▸ hx)) (fun e => hzP (e ▸ hy)) hcomm
      (hcross z hz x hx).symm (hcross z hz y hy).symm
  have hdisj : Disjoint P (Δ \ P) := Finset.disjoint_sdiff
  have h1 := pb_card_cases h2 h3 h hPΔ hQΔ hPclosed hPpb hPne hQne hcross hdisj hW hUW
  have h2' := pb_card_cases h2 h3 h hQΔ hPΔ hQclosed hQpb hQne hPne
    (fun x hx y hy => (hcross y hy x hx).symm) hdisj.symm hW hUW
  have hsum : ((P.card : ℕ) : K) + (((Δ \ P).card : ℕ) : K) = 3 := by
    rw [← hcard]
    have := Finset.card_sdiff_add_card_eq_card hPΔ
    have := congrArg (Nat.cast (R := K)) this
    push_cast at this
    linear_combination this
  rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2'
  · exact one_ne_zero (by linear_combination -hsum + h1 + h2')
  · exact one_ne_zero (by linear_combination hsum - h1 - h2')
  · exact one_ne_zero (by linear_combination hsum - h1 - h2')
  · exact h3 (by linear_combination hsum - h1 - h2')

theorem local_structure (hdim : finrank K V = 4) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hconn : Conn 𝒟) (hU : Uspan 𝒟 = ⊤)
    (hno4 : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, ∀ d ∈ 𝒟, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      c ≠ d → a * b = b * a → a * c = c * a → a * d = d * a → b * c = c * b → b * d = d * b →
      c * d = d * c → False)
    {t : V ≃ₗ[K] V} (ht : t ∈ 𝒟) :
    ∃ u ∈ 𝒟, ∃ v ∈ 𝒟, u ≠ v ∧ u * v ≠ v * u ∧ commSet 𝒟 t = {u, v, u * v * u⁻¹} := by
  obtain ⟨rt, φt, hdt⟩ := h.refl t ht
  have hΔ𝒟 : commSet 𝒟 t ⊆ 𝒟 := fun x hx => (mem_commSet.1 hx).1
  have hΔcl : ∀ a ∈ commSet 𝒟 t, ∀ b ∈ commSet 𝒟 t, a * b * a⁻¹ ∈ commSet 𝒟 t :=
    fun a ha b hb => h.commSet_closed ha hb
  have hΔR : IsRSet (commSet 𝒟 t) := h.sub hΔ𝒟 hΔcl
  have hcard := card_comm_cast hdim h2 h3 h hconn hU ht
  have hno3 : ∀ x ∈ commSet 𝒟 t, ∀ y ∈ commSet 𝒟 t, ∀ z ∈ commSet 𝒟 t, x ≠ y → x ≠ z → y ≠ z →
      x * y = y * x → x * z = z * x → y * z = z * y → False := by
    intro x hx y hy z hz hxy hxz hyz cxy cxz cyz
    obtain ⟨hx𝒟, hxt, ctx⟩ := mem_commSet.1 hx
    obtain ⟨hy𝒟, hyt, cty⟩ := mem_commSet.1 hy
    obtain ⟨hz𝒟, hzt, ctz⟩ := mem_commSet.1 hz
    exact hno4 t ht x hx𝒟 y hy𝒟 z hz𝒟 (Ne.symm hxt) (Ne.symm hyt) (Ne.symm hzt) hxy hxz hyz
      ctx cty ctz cxy cxz cyz
  have hker : Uspan (commSet 𝒟 t) ≤ LinearMap.ker (Nop t) := by
    refine Uspan_le_ker fun s hs => ?_
    obtain ⟨hs𝒟, hst, hc⟩ := mem_commSet.1 hs
    rcases h.dich h2 h3 ht hs𝒟 (Ne.symm hst) with ⟨h0, -, -⟩ | ⟨-, -, -, hnc⟩
    · exact h0
    · exact absurd hc hnc
  have hW : finrank K (LinearMap.ker (Nop t)) = 3 :=
    hdt.finrank_ker_nop h2 (by rw [hdim])
  have hle3 : finrank K (Uspan (commSet 𝒟 t)) ≤ 3 :=
    (Submodule.finrank_mono hker).trans hW.le
  by_cases hc : Conn (commSet 𝒟 t)
  · obtain ⟨u, hu, v, hv, huv, hnc, hΔeq⟩ := caseConn h2 h3 hΔR hc hcard hno3 hle3
    exact ⟨u, hΔ𝒟 hu, v, hΔ𝒟 hv, huv, hnc, hΔeq⟩
  · exact (caseDisc h2 h3 hΔR hc hcard hno3 hW hker).elim

end Cases

end ReflF

end CFSG.RankThree.PartOne
