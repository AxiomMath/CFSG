module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Sylow

variable {G : Type*} [Group G]

theorem relIndex_sup_eq_of_le_normalizer' {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem isSylowTwoOf_inf_of_le_normalizer [Finite G] {T M N : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (T ⊓ N) N := by
  refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, ?_⟩
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hT.1.trans hMN
  have h1 : N.relIndex (T ⊔ N) = N.relIndex T := relIndex_sup_eq_of_le_normalizer' hTN
  have hsup : T ⊔ N ≤ M := sup_le hT.1 hNM
  have e1 := Subgroup.relIndex_mul_relIndex (T ⊓ N) N (T ⊔ N) inf_le_right le_sup_right
  have e2 := Subgroup.relIndex_mul_relIndex (T ⊓ N) T (T ⊔ N) inf_le_left le_sup_left
  have h2 : (T ⊓ N).relIndex T = N.relIndex T := Subgroup.inf_relIndex_left T N
  rw [h1] at e1
  rw [h2] at e2
  have hne : N.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcancel : (T ⊓ N).relIndex N = T.relIndex (T ⊔ N) := by
    have : (T ⊓ N).relIndex N * N.relIndex T = T.relIndex (T ⊔ N) * N.relIndex T := by
      rw [e1, ← e2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  have h3 := Subgroup.relIndex_mul_relIndex T (T ⊔ N) M le_sup_left hsup
  intro h
  have h' : 2 ∣ (T ⊓ N).relIndex N := h
  rw [hcancel] at h'
  apply hT.2.2
  show 2 ∣ T.relIndex M
  rw [← h3]
  exact Dvd.dvd.mul_right h' _

theorem card_sup_eq_mul_of_le_normalizer [Finite G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) (h : A ⊓ B = ⊥) :
    Nat.card ↥(B ⊔ A) = Nat.card B * Nat.card A := by
  have h1 : A.relIndex (B ⊔ A) = A.relIndex B := relIndex_sup_eq_of_le_normalizer' hB
  have h2 := Subgroup.relIndex_mul_card A B
  have h3 := Subgroup.relIndex_mul_card A (B ⊔ A)
  rw [h, Subgroup.card_bot, mul_one] at h2
  rw [inf_of_le_left le_sup_right, h1, h2] at h3
  exact h3.symm

theorem le_normalizer_sup' {T A B : Subgroup G} (hA : T ≤ Subgroup.normalizer (A : Set G))
    (hB : T ≤ Subgroup.normalizer (B : Set G)) :
    T ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ A ⊔ B, t * x * t⁻¹ ∈ A ⊔ B := by
    intro t ht x hx
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj t).toMonoidHom :=
      sup_le (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hA ht) a).mp ha))
        (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hB ht) b).mp hb))
    simpa [MulAut.conj_apply] using hle hx
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key t ht x hx, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem exists_relIndex_oTwoUpper [Finite G] (H : Subgroup G) :
    ∃ j : ℕ, (oTwoUpper H).relIndex H = 2 ^ j := by
  classical
  have hNH : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hnorm : ((oTwoUpper H).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNH
  have hQ : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  refine ⟨n, ?_⟩
  show ((oTwoUpper H).subgroupOf H).index = 2 ^ n
  rw [Subgroup.index_eq_card]
  exact hn

theorem eq_one_of_mem_of_odd_of_isPGroup [Finite G] {E P : Subgroup G} (hE : Odd (Nat.card E))
    (hP : IsPGroup 2 P) {x : G} (hxE : x ∈ E) (hxP : x ∈ P) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf x ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hxE
  have h2 : Odd (orderOf x) := hE.of_dvd_nat h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  have hk' : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  rw [hk'] at h2
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr h2) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem normalizes_of_le_of_card_dvd_prime [Finite G] {Mb E Y : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hE : Nat.card E ∣ p) (hYE : Y ≤ E)
    (hEn : ∀ g ∈ Mb, ∀ e ∈ E, g * e * g⁻¹ ∈ E) : ∀ g ∈ Mb, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
  have hY : Nat.card Y ∣ p := (Subgroup.card_dvd_of_le hYE).trans hE
  rcases (Nat.dvd_prime hp).mp hY with h1 | h1
  · intro g _ y hy
    have hbot : Y = ⊥ := Subgroup.card_eq_one.mp h1
    have : y = 1 := by rw [hbot] at hy; exact Subgroup.mem_bot.mp hy
    rw [this]
    simp
  · have hEp : Nat.card E = p := by
      refine Nat.dvd_antisymm hE ?_
      rw [← h1]
      exact Subgroup.card_dvd_of_le hYE
    have hYE' : Y = E := Subgroup.eq_of_le_of_card_ge hYE (by rw [h1, hEp])
    subst hYE'
    exact hEn

end Sylow

section Twenty

variable {H : Type*} [Group H] [Finite H]

theorem exists_normal_of_card_twenty (hH : Nat.card H = 20) :
    ∃ P : Subgroup H, P.Normal ∧ Nat.card P = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 H) := inferInstance
  have hnd := Sylow.not_dvd_index P
  have hmul := Subgroup.card_mul_index (P : Subgroup H)
  obtain ⟨n, hn⟩ := (P.isPGroup').exists_card_eq
  have hP : Nat.card (P : Subgroup H) = 5 := by
    rw [hn, hH] at hmul
    rcases n with _ | _ | n
    · exfalso; apply hnd; simp at hmul; rw [hmul]; norm_num
    · simpa using hn
    · exfalso
      have h25 : 25 ∣ 20 := by
        rw [← hmul]
        exact Dvd.dvd.mul_right (Dvd.intro_left (5 ^ n) (by ring)) _
      omega
  have hidx : (P : Subgroup H).index = 4 := by
    rw [hP, hH] at hmul
    omega
  have hmod := card_sylow_modEq_one 5 H
  have hdvd : Nat.card (Sylow 5 H) ∣ 4 := by
    have := Sylow.card_dvd_index P
    rwa [hidx] at this
  have hn1 : Nat.card (Sylow 5 H) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 5 H) := Nat.card_pos
    unfold Nat.ModEq at hmod
    generalize Nat.card (Sylow 5 H) = m at *
    interval_cases m <;> omega
  have : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hn1).1
  exact ⟨P, inferInstance, hP⟩

end Twenty

section Twenty'

variable {A : Type*} [Group A] [Finite A]

theorem exists_normal_five_of_card_twenty {X : Subgroup A} (hX : Nat.card X = 20) :
    ∃ P : Subgroup A, P ≤ X ∧ Nat.card P = 5 ∧ (∀ x ∈ X, x ^ 4 ∈ P) ∧
      ∀ g ∈ X, ∀ y ∈ P, g * y * g⁻¹ ∈ P := by
  obtain ⟨P, hPn, hP5⟩ := exists_normal_of_card_twenty hX
  have hidx : P.index = 4 := by
    have := Subgroup.card_mul_index P
    rw [hP5, hX] at this
    omega
  refine ⟨P.map X.subtype, Subgroup.map_subtype_le P, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hP5]
  · intro x hx
    refine ⟨⟨x, hx⟩ ^ 4, ?_, rfl⟩
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ : X) : X ⧸ P) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := X ⧸ P) (x := QuotientGroup.mk (⟨x, hx⟩ : X))
      rwa [← Subgroup.index_eq_card, hidx] at this
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  · intro g hg y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, hPn.conj_mem y' hy' ⟨g, hg⟩, rfl⟩

theorem card_oTwoUpper_dvd_five {X : Subgroup A} (hX : Nat.card X = 20) :
    Nat.card (oTwoUpper X) ∣ 5 := by
  obtain ⟨P, -, hP5, hP4, -⟩ := exists_normal_five_of_card_twenty hX
  have hle : oTwoUpper X ≤ P := oTwoUpper_le_of_pow_mem fun x hx => ⟨2, by simpa using hP4 x hx⟩
  rw [← hP5]
  exact Subgroup.card_dvd_of_le hle

end Twenty'

section Decomp

variable {A : Type*} [Group A] [Finite A]

theorem normalizer_le_of_decomp {Mb Tb Sb E : Subgroup A} {b : A}
    (hdec : ∀ g ∈ Mb, ∃ e ∈ E, ∃ t ∈ Tb, e * t = g) (hTMb : Tb ≤ Mb)
    (hEn : ∀ g ∈ Mb, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hEodd : Odd (Nat.card E))
    (hT2 : IsPGroup 2 Tb) (hSTb : Sb ≤ Tb) (hSn : Tb ≤ Subgroup.normalizer (Sb : Set A))
    (hBS : b ∈ Sb) (hfpf : ∀ e ∈ E, b * e = e * b → e = 1) :
    ∀ g ∈ Mb, g ∈ Subgroup.normalizer (Sb : Set A) → g ∈ Tb := by
  intro g hg hgN
  obtain ⟨e, he, t, ht, rfl⟩ := hdec g hg
  have heN : e ∈ Subgroup.normalizer (Sb : Set A) := by
    have : e = (e * t) * t⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ (hSn ht))
  have hcomm : ∀ s ∈ Sb, e * s = s * e := by
    intro s hs
    have h1 : e * s * e⁻¹ ∈ Sb := (Subgroup.mem_normalizer_iff.mp heN s).mp hs
    have h2 : e * s * e⁻¹ * s⁻¹ ∈ Sb := Sb.mul_mem h1 (Sb.inv_mem hs)
    have h3 : e * s * e⁻¹ * s⁻¹ ∈ E := by
      have : e * s * e⁻¹ * s⁻¹ = e * (s * e⁻¹ * s⁻¹) := by group
      rw [this]
      exact E.mul_mem he (hEn s (hTMb (hSTb hs)) e⁻¹ (E.inv_mem he))
    have h4 : e * s * e⁻¹ * s⁻¹ = 1 :=
      eq_one_of_mem_of_odd_of_isPGroup hEodd (hT2.to_le hSTb) h3 h2
    have h5 : e * s * e⁻¹ = s := mul_inv_eq_one.mp h4
    calc e * s = e * s * e⁻¹ * e := by group
      _ = s * e := by rw [h5]
  have he1 : e = 1 := hfpf e he (hcomm b hBS).symm
  rw [he1, one_mul]
  exact ht

end Decomp

end CFSG.Quasithin
