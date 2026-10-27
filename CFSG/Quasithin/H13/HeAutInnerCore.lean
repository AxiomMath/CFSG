module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.LocDbl.AutInner

variable {P : Type} [Group P]

@[expose] def aimg (φ : MulAut P) (S : Subgroup P) : Subgroup P := S.map φ.toMonoidHom

theorem mem_aimg {φ : MulAut P} {S : Subgroup P} {y : P} : y ∈ aimg φ S ↔ ∃ s ∈ S, φ s = y := by
  simp [aimg, Subgroup.mem_map]

theorem mem_aimg_inv {φ : MulAut P} {S : Subgroup P} {y : P} : y ∈ aimg φ S ↔ φ⁻¹ y ∈ S := by
  rw [mem_aimg]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro h
    exact ⟨φ⁻¹ y, h, by simp⟩

theorem aimg_mul (φ ψ : MulAut P) (S : Subgroup P) : aimg (φ * ψ) S = aimg φ (aimg ψ S) := by
  ext y
  rw [mem_aimg, mem_aimg]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨ψ s, (mem_aimg).2 ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, hz, rfl⟩
    obtain ⟨s, hs, rfl⟩ := mem_aimg.1 hz
    exact ⟨s, hs, rfl⟩

theorem card_aimg (φ : MulAut P) (S : Subgroup P) : Nat.card (aimg φ S) = Nat.card S :=
  Subgroup.card_map_of_injective φ.injective

theorem aimg_mono (φ : MulAut P) {S T : Subgroup P} (h : S ≤ T) : aimg φ S ≤ aimg φ T :=
  Subgroup.map_mono h

theorem aimg_injective (φ : MulAut P) {S T : Subgroup P} (h : aimg φ S = aimg φ T) : S = T := by
  ext y
  have h1 : φ y ∈ aimg φ S ↔ φ y ∈ aimg φ T := by rw [h]
  rw [mem_aimg_inv, mem_aimg_inv] at h1
  simpa using h1

theorem mem_aimg_conj {k y : P} {S : Subgroup P} : y ∈ aimg (MulAut.conj k) S ↔ k⁻¹ * y * k ∈ S := by
  rw [mem_aimg_inv]
  simp [MulAut.conj_inv_apply]

theorem mem_normalizer_iff_aimg {V : Subgroup P} {n : P} :
    n ∈ Subgroup.normalizer (V : Set P) ↔ aimg (MulAut.conj n) V = V := by
  constructor
  · intro hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (V : Set P) := Subgroup.inv_mem _ hn
    ext y
    rw [mem_aimg_conj]
    have := Subgroup.mem_normalizer_iff.mp hn' y
    simpa using this.symm
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    constructor
    · intro hy
      have h2 : n * y * n⁻¹ ∈ aimg (MulAut.conj n) V := by
        rw [mem_aimg_conj, e]
        exact hy
      rwa [h] at h2
    · intro hy
      rw [← h, mem_aimg_conj, e] at hy
      exact hy

theorem sylow_of_card_two' [Finite P] {K : Subgroup P} {k : ℕ} (hK : Nat.card K = 2 ^ k)
    (hnd : ¬ 2 ^ (k + 1) ∣ Nat.card P) : ∃ S : Sylow 2 P, S.toSubgroup = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨K, IsPGroup.of_card (n := k) hK, ?_⟩, rfl⟩
  intro R hR hle
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card P := Subgroup.card_subgroup_dvd_card R
  rw [hm] at hdvd
  have hmk : m ≤ k := by
    by_contra hc
    push Not at hc
    exact hnd ((pow_dvd_pow 2 (by omega)).trans hdvd)
  have hRK : Nat.card R ≤ Nat.card K := by
    rw [hm, hK]
    exact Nat.pow_le_pow_right (by norm_num) hmk
  exact (Subgroup.eq_of_le_of_card_ge hle hRK).symm

open Pointwise in
theorem exists_conj_of_card_two' [Finite P] {K K' : Subgroup P} {k : ℕ} (hK : Nat.card K = 2 ^ k)
    (hK' : Nat.card K' = 2 ^ k) (hnd : ¬ 2 ^ (k + 1) ∣ Nat.card P) :
    ∃ g : P, aimg (MulAut.conj g) K = K' := by
  obtain ⟨S, hS⟩ := sylow_of_card_two' hK hnd
  obtain ⟨S', hS'⟩ := sylow_of_card_two' hK' hnd
  haveI : Finite (Sylow 2 P) :=
    Finite.of_injective (fun S : Sylow 2 P => (S : Subgroup P)) (fun S T h => Sylow.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S S'
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • S.toSubgroup = S'.toSubgroup := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [hS, hS'] at h1
  rw [← h1]
  rfl

theorem exists_conj_in_of_card_two [Finite P] {V K K' : Subgroup P} {k : ℕ} (hKV : K ≤ V) (hK'V : K' ≤ V)
    (hK : Nat.card K = 2 ^ k) (hK' : Nat.card K' = 2 ^ k) (hnd : ¬ 2 ^ (k + 1) ∣ Nat.card V) :
    ∃ g ∈ V, aimg (MulAut.conj g) K = K' := by
  have hc1 : Nat.card (K.subgroupOf V) = 2 ^ k := by
    rw [← hK]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKV).toEquiv
  have hc2 : Nat.card (K'.subgroupOf V) = 2 ^ k := by
    rw [← hK']; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'V).toEquiv
  obtain ⟨g, hg⟩ := exists_conj_of_card_two' hc1 hc2 hnd
  refine ⟨g, g.2, ?_⟩
  have hle : aimg (MulAut.conj (g : P)) K ≤ K' := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := mem_aimg.1 hy
    have hsV : (⟨s, hKV hs⟩ : ↥V) ∈ K.subgroupOf V := hs
    have h1 : (MulAut.conj g) ⟨s, hKV hs⟩ ∈ aimg (MulAut.conj g) (K.subgroupOf V) :=
      mem_aimg.2 ⟨_, hsV, rfl⟩
    rw [hg] at h1
    exact h1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_aimg, hK, hK'])

theorem exists_odd_pow_mem [Finite P] {R : Subgroup P} {k : ℕ} (hR : Nat.card R = 2 ^ k)
    (hP : ¬ 2 ^ (k + 1) ∣ Nat.card P) {n : P} (hn : n ∈ Subgroup.normalizer (R : Set P)) :
    ∃ m : ℕ, Odd m ∧ n ^ m ∈ R := by
  set N := Subgroup.normalizer (R : Set P) with hN
  have hRN : R ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := R.subgroupOf N
  haveI : H.Normal := Subgroup.normal_in_normalizer
  have hmem := Subgroup.pow_index_mem H (⟨n, hn⟩ : ↥N)
  refine ⟨H.index, ?_, ?_⟩
  · have h1 := H.card_mul_index
    have h2 : Nat.card H = 2 ^ k := by
      rw [← hR]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
    have h3 : Nat.card N ∣ Nat.card P := Subgroup.card_subgroup_dvd_card N
    rw [h2] at h1
    rw [← h1] at h3
    rw [Nat.odd_iff]
    by_contra hc
    have h2d : 2 ∣ H.index := by omega
    have h4 : 2 ^ (k + 1) ∣ 2 ^ k * H.index := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left (2 ^ k) h2d
    exact hP (h4.trans h3)
  · have := Subgroup.mem_subgroupOf.mp hmem
    simpa using this

theorem normalizer_fix [Finite P] {R : Subgroup P} (hR : Nat.card R = 2 ^ 10)
    (hP : ¬ 2 ^ 11 ∣ Nat.card P) {W₁ W₂ : Subgroup P}
    (hover : ∀ V : Subgroup P, R ≤ V → Nat.card V = 138240 → V = W₁ ∨ V = W₂)
    {n : P} (hn : n ∈ Subgroup.normalizer (R : Set P)) {V : Subgroup P} (hRV : R ≤ V)
    (hV : Nat.card V = 138240) : n ∈ Subgroup.normalizer (V : Set P) := by
  have hnR : aimg (MulAut.conj n) R = R := mem_normalizer_iff_aimg.mp hn
  have key : ∀ V' : Subgroup P, R ≤ V' → Nat.card V' = 138240 →
      R ≤ aimg (MulAut.conj n) V' ∧ Nat.card (aimg (MulAut.conj n) V') = 138240 := by
    intro V' hV' hc
    refine ⟨?_, by rw [card_aimg, hc]⟩
    calc R = aimg (MulAut.conj n) R := hnR.symm
      _ ≤ aimg (MulAut.conj n) V' := aimg_mono _ hV'
  have hsq : n ^ 2 ∈ Subgroup.normalizer (V : Set P) := by
    rw [mem_normalizer_iff_aimg]
    have hpow : MulAut.conj (n ^ 2) = MulAut.conj n * MulAut.conj n := by
      rw [map_pow, pow_two]
    rw [hpow, aimg_mul]
    by_cases h : aimg (MulAut.conj n) V = V
    · rw [h, h]
    · have k1 := key V hRV hV
      have k2 := key _ k1.1 k1.2
      have a1 := hover V hRV hV
      have a2 := hover _ k1.1 k1.2
      have a3 := hover _ k2.1 k2.2
      have hne2 : aimg (MulAut.conj n) (aimg (MulAut.conj n) V) ≠ aimg (MulAut.conj n) V := by
        intro h2
        exact h (aimg_injective _ h2)
      by_contra hcon
      rcases a1 with e1 | e1 <;> rcases a2 with e2 | e2 <;> rcases a3 with e3 | e3 <;>
        first
        | exact h (e2.trans e1.symm)
        | exact hne2 (e3.trans e2.symm)
        | exact hcon (e3.trans e1.symm)
  obtain ⟨m, hm, hnm⟩ := exists_odd_pow_mem hR hP hn
  have hnmV : n ^ m ∈ Subgroup.normalizer (V : Set P) := Subgroup.le_normalizer (hRV hnm)
  obtain ⟨t, rfl⟩ := hm
  have e1 : n ^ (2 * t + 1) = (n ^ 2) ^ t * n := by rw [pow_succ, pow_mul]
  have e2 : n = ((n ^ 2) ^ t)⁻¹ * n ^ (2 * t + 1) := by rw [e1, inv_mul_cancel_left]
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq t)) hnmV

theorem aimg_normalizer (φ : MulAut P) {B : Subgroup P} {s : P}
    (hs : s ∈ Subgroup.normalizer (B : Set P)) :
    φ s ∈ Subgroup.normalizer ((aimg φ B : Subgroup P) : Set P) := by
  rw [mem_normalizer_iff_aimg] at hs ⊢
  have e : MulAut.conj (φ s) * φ = φ * MulAut.conj s := by
    ext x
    simp [MulAut.conj_apply]
  calc aimg (MulAut.conj (φ s)) (aimg φ B) = aimg (MulAut.conj (φ s) * φ) B := (aimg_mul _ _ _).symm
    _ = aimg (φ * MulAut.conj s) B := by rw [e]
    _ = aimg φ (aimg (MulAut.conj s) B) := aimg_mul _ _ _
    _ = aimg φ B := by rw [hs]

theorem normalizer_B [Finite P] {R : Subgroup P}
    (hnn : ∀ N : Subgroup P, N.Normal → Nat.card N ≠ 69120)
    (hR : Nat.card R = 2 ^ 10) {W₁ W₂ W₃ : Subgroup P}
    (h₁ : Nat.card W₁ = 138240) (h₂ : Nat.card W₂ = 138240) (h₃ : Nat.card W₃ = 21504)
    (hcls : ∀ Y : Subgroup P, R ≤ Y → Y ≠ ⊤ → Y ≤ W₁ ∨ Y ≤ W₂ ∨ Y ≤ W₃)
    {B₁ : Subgroup P} (hRB : R ≤ Subgroup.normalizer (B₁ : Set P)) (hB : Nat.card B₁ = 69120) :
    Subgroup.normalizer (B₁ : Set P) = W₁ ∨ Subgroup.normalizer (B₁ : Set P) = W₂ := by
  set N := Subgroup.normalizer (B₁ : Set P) with hN
  have hne : N ≠ ⊤ := by
    intro h
    have : B₁.Normal := Subgroup.normalizer_eq_top_iff.mp h
    exact hnn B₁ this hB
  have hBN : B₁ ≤ N := Subgroup.le_normalizer
  have hd1 : Nat.card R ∣ Nat.card N := Subgroup.card_dvd_of_le hRB
  have hd2 : Nat.card B₁ ∣ Nat.card N := Subgroup.card_dvd_of_le hBN
  have hd : 138240 ∣ Nat.card N := by
    have h := Nat.lcm_dvd hd1 hd2
    rw [hR, hB] at h
    have hl : Nat.lcm (2 ^ 10) 69120 = 138240 := by norm_num
    rwa [hl] at h
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hle : 138240 ≤ Nat.card N := Nat.le_of_dvd hpos hd
  rcases hcls N hRB hne with h | h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [h₁]; exact hle))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [h₂]; exact hle))
  · exfalso
    have := hd.trans (h₃ ▸ Subgroup.card_dvd_of_le h)
    norm_num at this

theorem aut_stab_inner [Finite P] (hPcard : Nat.card P = 4030387200)
    (hnn : ∀ N : Subgroup P, N.Normal → Nat.card N ≠ 69120)
    {R : Subgroup P} (hR : Nat.card R = 2 ^ 10)
    {W₁ W₂ W₃ : Subgroup P} (hRW₁ : R ≤ W₁) (hRW₂ : R ≤ W₂)
    (h₁ : Nat.card W₁ = 138240) (h₂ : Nat.card W₂ = 138240) (h₃ : Nat.card W₃ = 21504)
    (hcls : ∀ Y : Subgroup P, R ≤ Y → Y ≠ ⊤ → Y ≤ W₁ ∨ Y ≤ W₂ ∨ Y ≤ W₃)
    (ξ : MulAut P) (hξR : aimg ξ R = R) (hξ₁ : aimg ξ W₁ ≠ W₁) (hξ₂ : aimg ξ W₂ ≠ W₂)
    (hOut : ∀ f : MulAut P, (∃ k : P, ∀ x, f x = k * x * k⁻¹) ∨ (∃ k : P, ∀ x, f x = k * ξ x * k⁻¹))
    {S B : Subgroup P} (hS : Nat.card S = 2 ^ 10) (hSB : S ≤ Subgroup.normalizer (B : Set P))
    (hB : Nat.card B = 69120) {f : MulAut P} (hfB : aimg f B = B) :
    ∃ k : P, ∀ x, f x = k * x * k⁻¹ := by
  have hnd : ¬ 2 ^ (10 + 1) ∣ Nat.card P := by rw [hPcard]; norm_num
  rcases hOut f with h | ⟨k, hk0⟩
  · exact h
  have hk : f = MulAut.conj k * ξ := MulEquiv.ext fun x => by
    simp [hk0, MulAut.conj_apply, mul_assoc]
  exfalso
  have hover : ∀ V : Subgroup P, R ≤ V → Nat.card V = 138240 → V = W₁ ∨ V = W₂ := by
    intro V hRV hV
    have hVne : V ≠ ⊤ := by
      intro h
      rw [h, Subgroup.card_top, hPcard] at hV
      norm_num at hV
    rcases hcls V hRV hVne with h | h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [h₁, hV]))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [h₂, hV]))
    · exfalso
      have := (h₃ ▸ Subgroup.card_dvd_of_le h : Nat.card V ∣ 21504)
      rw [hV] at this
      norm_num at this
  obtain ⟨c, hc⟩ := exists_conj_of_card_two' (K := S) (K' := R) (k := 10) hS hR hnd
  set B₁ : Subgroup P := aimg (MulAut.conj c) B with hB₁
  have hB₁c : Nat.card B₁ = 69120 := by rw [hB₁, card_aimg, hB]
  have hRB₁ : R ≤ Subgroup.normalizer (B₁ : Set P) := by
    rw [← hc]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := mem_aimg.1 hy
    exact aimg_normalizer (MulAut.conj c) (hSB hs)
  have hV := normalizer_B hnn hR h₁ h₂ h₃ hcls hRB₁ hB₁c
  set V : Subgroup P := Subgroup.normalizer (B₁ : Set P) with hVdef
  have hVcard : Nat.card V = 138240 := by
    rcases hV with h | h
    · rw [h, h₁]
    · rw [h, h₂]
  have hRV : R ≤ V := hRB₁
  set f₁ : MulAut P := MulAut.conj c * f * (MulAut.conj c)⁻¹ with hf₁
  have hf₁B : aimg f₁ B₁ = B₁ := by
    rw [hf₁, hB₁, ← aimg_mul, inv_mul_cancel_right, aimg_mul, hfB]
  have hf₁V : aimg f₁ V ≤ V := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := mem_aimg.1 hy
    have := aimg_normalizer f₁ hn
    rwa [hf₁B] at this
  have hR'V : aimg f₁ R ≤ V := (aimg_mono f₁ hRV).trans hf₁V
  obtain ⟨w, hwV, hw⟩ := exists_conj_in_of_card_two (V := V) (K := aimg f₁ R) (K' := R) (k := 10) hR'V hRV
    (by rw [card_aimg, hR]) hR (by rw [hVcard]; norm_num)
  set f₂ : MulAut P := MulAut.conj w * f₁ with hf₂
  have hf₂R : aimg f₂ R = R := by rw [hf₂, aimg_mul]; exact hw
  have hwN : aimg (MulAut.conj w) V = V := mem_normalizer_iff_aimg.mp (Subgroup.le_normalizer hwV)
  have hf₂V : aimg f₂ V = V := by
    have hle : aimg f₂ V ≤ V := by
      rw [hf₂, aimg_mul]
      calc aimg (MulAut.conj w) (aimg f₁ V) ≤ aimg (MulAut.conj w) V := aimg_mono _ hf₁V
        _ = V := hwN
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_aimg])
  have hξc : ξ * (MulAut.conj c)⁻¹ = MulAut.conj (ξ c⁻¹) * ξ := by
    ext x
    simp [MulAut.conj_apply, MulAut.conj_inv_apply, mul_assoc]
  have hf₂ξ : f₂ = MulAut.conj (w * c * k * ξ c⁻¹) * ξ := by
    rw [hf₂, hf₁, hk]
    calc MulAut.conj w * (MulAut.conj c * (MulAut.conj k * ξ) * (MulAut.conj c)⁻¹)
        = MulAut.conj w * MulAut.conj c * MulAut.conj k * (ξ * (MulAut.conj c)⁻¹) := by
          simp only [mul_assoc]
      _ = MulAut.conj w * MulAut.conj c * MulAut.conj k * (MulAut.conj (ξ c⁻¹) * ξ) := by rw [hξc]
      _ = MulAut.conj (w * c * k * ξ c⁻¹) * ξ := by
          simp only [map_mul, mul_assoc]
  set k₂ : P := w * c * k * ξ c⁻¹ with hk₂
  have hk₂R : aimg (MulAut.conj k₂) R = R := by
    have := hf₂R
    rwa [hf₂ξ, aimg_mul, hξR] at this
  have hk₂N : k₂ ∈ Subgroup.normalizer (R : Set P) := mem_normalizer_iff_aimg.mpr hk₂R
  have hk₂V : k₂ ∈ Subgroup.normalizer (V : Set P) := normalizer_fix hR (by simpa using hnd) hover hk₂N hRV hVcard
  have hk₂V' : aimg (MulAut.conj k₂) V = V := mem_normalizer_iff_aimg.mp hk₂V
  have hξV : aimg ξ V = V := by
    apply aimg_injective (MulAut.conj k₂)
    rw [hk₂V', ← aimg_mul, ← hf₂ξ]
    exact hf₂V
  rcases hV with h | h
  · exact hξ₁ (by rw [← h]; exact hξV)
  · exact hξ₂ (by rw [← h]; exact hξV)

theorem mem_normalizer_map {Q J : Type} [Group Q] [Group J] (e : Q ≃* J) {B : Subgroup Q} {s : Q}
    (hs : s ∈ Subgroup.normalizer (B : Set Q)) :
    e s ∈ Subgroup.normalizer ((B.map e.toMonoidHom : Subgroup J) : Set J) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have := Subgroup.mem_normalizer_iff.mp hs (e.symm z)
  simpa using this

theorem transport {Q J : Type} [Group Q] [Group J] [Finite Q] (e : Q ≃* J)
    (h : ∀ S B : Subgroup J, Nat.card S = 2 ^ 10 → S ≤ Subgroup.normalizer (B : Set J) →
      Nat.card B = 69120 → ∀ f : MulAut J, aimg f B = B → ∃ k : J, ∀ x, f x = k * x * k⁻¹)
    (S B : Subgroup Q) (hS : Nat.card S = 2 ^ 10) (hSB : S ≤ Subgroup.normalizer (B : Set Q))
    (hB : Nat.card B = 69120) (f : Q →* Q) (hf : Function.Bijective f) (hfB : B.map f = B) :
    ∃ k : Q, ∀ x : Q, f x = k * x * k⁻¹ := by
  haveI : Finite J := Finite.of_equiv Q e.toEquiv
  let F : MulAut Q := MulEquiv.ofBijective f hf
  let F' : MulAut J := MulAut.congr e F
  have hF'e : ∀ x : Q, F' (e x) = e (f x) := by
    intro x
    simp [F', F, MulAut.congr_apply]
  have hS' : Nat.card (S.map e.toMonoidHom) = 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hS
  have hB' : Nat.card (B.map e.toMonoidHom) = 69120 := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hB
  have hSB' : S.map e.toMonoidHom ≤ Subgroup.normalizer ((B.map e.toMonoidHom : Subgroup J) : Set J) := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_normalizer_map e (hSB hs)
  have hle : aimg F' (B.map e.toMonoidHom) ≤ B.map e.toMonoidHom := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_aimg.1 hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    have : F' (e.toMonoidHom b) = e (f b) := hF'e b
    rw [this]
    have hfb : f b ∈ B := by rw [← hfB]; exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    exact Subgroup.mem_map.mpr ⟨f b, hfb, rfl⟩
  have hfB' : aimg F' (B.map e.toMonoidHom) = B.map e.toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_aimg])
  obtain ⟨k', hk'⟩ := h _ _ hS' hSB' hB' F' hfB'
  refine ⟨e.symm k', fun x => ?_⟩
  have h1 : F' (e x) = k' * e x * k'⁻¹ := hk' (e x)
  have h2 : e (f x) = e (e.symm k' * x * (e.symm k')⁻¹) := by
    rw [← hF'e x, h1]; simp
  exact e.injective h2

@[expose] def HeAutInnerFor (J : Type) [Group J] : Prop :=
  ∀ S B : Subgroup J, Nat.card S = 2 ^ 10 → S ≤ Subgroup.normalizer (B : Set J) →
    Nat.card B = 69120 → ∀ f : J →* J, Function.Bijective f → B.map f = B →
      ∃ k : J, ∀ x : J, f x = k * x * k⁻¹

theorem transport' {Q J : Type} [Group Q] [Group J] [Finite Q]
    (h : ∀ S B : Subgroup J, Nat.card S = 2 ^ 10 → S ≤ Subgroup.normalizer (B : Set J) →
      Nat.card B = 69120 → ∀ f : MulAut J, aimg f B = B → ∃ k : J, ∀ x, f x = k * x * k⁻¹)
    (e : Q ≃* J) : HeAutInnerFor Q :=
  fun S B hS hSB hB f hf hfB => transport e h S B hS hSB hB f hf hfB

theorem transport_hom {Q J : Type} [Group Q] [Group J] [Finite Q] (h : HeAutInnerFor J) (e : Q ≃* J) :
    HeAutInnerFor Q :=
  transport' (fun S B hS hSB hB f hfB => h S B hS hSB hB f.toMonoidHom f.bijective hfB) e

end CFSG.Quasithin.H13.LocDbl.AutInner
