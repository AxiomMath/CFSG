module

import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u4x_covBy {T X : Subgroup Q} (hlt : T < X) {r : ℕ} (hr : r.Prime)
    (hX : Nat.card X ∣ r * Nat.card T) : T ⋖ X := by
  refine ⟨hlt, fun Y hTY hYX => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hTY.le
  have hT0 : 0 < Nat.card T := Nat.card_pos
  have hk' : k ∣ r := by
    have h := (Subgroup.card_dvd_of_le hYX.le).trans hX
    rw [hk, mul_comm r] at h
    exact Nat.dvd_of_mul_dvd_mul_left hT0 h
  rcases (Nat.dvd_prime hr).1 hk' with rfl | rfl
  · rw [mul_one] at hk
    exact hTY.ne (Subgroup.eq_of_le_of_card_ge hTY.le hk.le)
  · refine hYX.ne (Subgroup.eq_of_le_of_card_ge hYX.le ?_)
    rw [hk, mul_comm]
    exact Nat.le_of_dvd (Nat.mul_pos hr.pos hT0) hX

theorem u4x_eq_one_of_isPGroup {S : Subgroup Q} (hS : IsPGroup 2 S) {y : Q} (hy : y ∈ S)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨y, hy⟩
  have h1 : orderOf y ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have hcop : Nat.Coprime (2 ^ k) r :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop)
    (orderOf_dvd_of_pow_eq_one hyr))

theorem u4x_card_sup_dvd {S T : Subgroup Q} (hST : S ≤ T) {y : Q}
    (hyS : y ∈ normalizer (S : Set Q))
    (hTV : T ≤ normalizer ((zpowers y ⊔ S : Subgroup Q) : Set Q)) {r : ℕ} (hyr : y ^ r = 1) :
    Nat.card ↥(T ⊔ (zpowers y ⊔ S)) ∣ r * Nat.card T := by
  have h1 := PartTwo.card_sup_mul_card_inf_of_le_normalizer (zpowers_le.2 hyS)
  have h2 := PartTwo.card_sup_mul_card_inf_of_le_normalizer hTV
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_inf (le_sup_right : S ≤ zpowers y ⊔ S) hST)
  have hy : Nat.card (zpowers y) ∣ r := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hyr
  refine Dvd.dvd.trans ?_ (Nat.mul_dvd_mul_right hy (Nat.card T))
  refine ⟨k * Nat.card ↥(S ⊓ zpowers y),
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card S) ?_⟩
  calc Nat.card S * (Nat.card (zpowers y) * Nat.card T)
      = Nat.card ↥(zpowers y ⊔ S) * Nat.card ↥(S ⊓ zpowers y) * Nat.card T := by
        rw [h1]; ring
    _ = Nat.card ↥(T ⊔ (zpowers y ⊔ S)) * Nat.card ↥((zpowers y ⊔ S) ⊓ T) *
        Nat.card ↥(S ⊓ zpowers y) := by rw [h2]; ring
    _ = Nat.card S * (Nat.card ↥(T ⊔ (zpowers y ⊔ S)) * (k * Nat.card ↥(S ⊓ zpowers y))) := by
        rw [hk]; ring

theorem u4x_mem_normalizer_sup {A B : Subgroup Q} {g : Q} (hA : g ∈ normalizer (A : Set Q))
    (hB : g ∈ normalizer (B : Set Q)) : g ∈ normalizer ((A ⊔ B : Subgroup Q) : Set Q) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem u4x_mem_normalizer_inf {F₀ F₁ T : Subgroup Q} (hcomm : ∀ x ∈ F₀, ∀ y ∈ F₁, x * y = y * x)
    (hinf : F₀ ⊓ F₁ = ⊥) (hN : (F₀ ⊔ F₁).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    {x₀ x₁ : Q} (hx₀ : x₀ ∈ F₀) (hx₁ : x₁ ∈ F₁) (hβ : x₀ * x₁ ∈ normalizer (T : Set Q)) :
    x₀ ∈ normalizer ((T ⊓ (F₀ ⊔ F₁) : Subgroup Q) : Set Q) ∧
      x₁ ∈ normalizer ((T ⊓ (F₀ ⊔ F₁) : Subgroup Q) : Set Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTβ : ∀ s ∈ T, x₀ * x₁ * s * (x₀ * x₁)⁻¹ ∈ T := fun s hs =>
    (mem_normalizer_iff.1 hβ s).1 hs
  constructor <;> refine Subgroup.mem_normalizer_fintype fun s hs => ?_ <;>
    obtain ⟨s₀, hs₀, s₁, hs₁, rfl⟩ := u4x_mem_sup hcomm hs.2 <;>
    obtain ⟨hs₀T, hs₁T⟩ := u4x_mem_of_mul_mem hcomm hinf hT hN hs₀ hs₁ hs.1
  · have e1 := hcomm x₀ hx₀ s₁ hs₁
    have e2 := hcomm s₀ hs₀ x₁ hx₁
    have e : x₀ * (s₀ * s₁) * x₀⁻¹ = x₀ * x₁ * s₀ * (x₀ * x₁)⁻¹ * s₁ := by
      calc x₀ * (s₀ * s₁) * x₀⁻¹ = x₀ * s₀ * (x₀⁻¹ * (x₀ * s₁)) * x₀⁻¹ := by group
        _ = x₀ * s₀ * (x₀⁻¹ * (s₁ * x₀)) * x₀⁻¹ := by rw [e1]
        _ = x₀ * (s₀ * x₁) * x₁⁻¹ * x₀⁻¹ * s₁ := by group
        _ = x₀ * (x₁ * s₀) * x₁⁻¹ * x₀⁻¹ * s₁ := by rw [e2]
        _ = x₀ * x₁ * s₀ * (x₀ * x₁)⁻¹ * s₁ := by group
    exact ⟨e ▸ mul_mem (hTβ _ hs₀T) hs₁T, hN.conj_mem _ hs.2 x₀⟩
  · have e1 := hcomm s₀ hs₀ x₁ hx₁
    have e2 := hcomm x₀ hx₀ (x₁ * s₁ * x₁⁻¹)
      (mul_mem (mul_mem hx₁ hs₁) (inv_mem hx₁))
    have e : x₁ * (s₀ * s₁) * x₁⁻¹ = s₀ * (x₀ * x₁ * s₁ * (x₀ * x₁)⁻¹) := by
      calc x₁ * (s₀ * s₁) * x₁⁻¹ = x₁ * s₀ * x₁⁻¹ * (x₁ * s₁ * x₁⁻¹) := by group
        _ = s₀ * x₁ * x₁⁻¹ * (x₁ * s₁ * x₁⁻¹) := by rw [← e1]
        _ = s₀ * (x₁ * s₁ * x₁⁻¹ * x₀ * x₀⁻¹) := by group
        _ = s₀ * (x₀ * (x₁ * s₁ * x₁⁻¹) * x₀⁻¹) := by rw [← e2]
        _ = s₀ * (x₀ * x₁ * s₁ * (x₀ * x₁)⁻¹) := by group
    exact ⟨e ▸ mul_mem hs₀T (hTβ _ hs₁T), hN.conj_mem _ hs.2 x₁⟩

end Generic

theorem u4x_conj_mem_barImage {M P P' : Subgroup G} {t : ↥M}
    (h : P.map (MulAut.conj (t : G)).toMonoidHom = P') {x : Bar2 M} (hx : x ∈ barImage M P) :
    uc22p21cPi M t * x * (uc22p21cPi M t)⁻¹ ∈ barImage M P' := by
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hx
  refine uc22p21c_mem_barImage.2 ⟨t * m * t⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [← h, uc22p21c_mem_map_conj]
  show (t : G)⁻¹ * ((t : G) * m * (t : G)⁻¹) * t ∈ P
  rw [show (t : G)⁻¹ * ((t : G) * m * (t : G)⁻¹) * t = m by group]
  exact hm

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem conj_cases (u : U4X D L K n) {t : G} (ht : t ∈ D.M) :
    (t ∈ normalizer (L : Set G) ∧ t ∈ normalizer (K : Set G)) ∨
      (L.map (MulAut.conj t).toMonoidHom = K ∧ K.map (MulAut.conj t).toMonoidHom = L) := by
  have hL' : L.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M L := ⟨t, ht, rfl⟩
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M K := ⟨t, ht, rfl⟩
  rw [u.hset] at hL'
  rw [uc22p2214_conjSetOf_eq u.mem_K, u.hset] at hK'
  have hinj := Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL' hK'
  rcases hL' with hL' | hL' <;> rcases hK' with hK' | hK'
  · exact absurd (hinj (hL'.trans hK'.symm)).symm u.hne
  · exact Or.inl ⟨mem_normalizer_iff_map_conj_eq.2 hL', mem_normalizer_iff_map_conj_eq.2 hK'⟩
  · exact Or.inr ⟨hL', hK'⟩
  · exact absurd (hinj (hL'.trans hK'.symm)).symm u.hne

theorem conj_mem_V (u : U4X D L K n) {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L)
    (hx₁ : x₁ ∈ barImage D.M K)
    (hN : x₀ * x₁ ∈ normalizer (barImage D.M D.T : Set (Bar2 D.M))) {t : ↥D.M}
    (ht : (t : G) ∈ D.T) :
    uc22p21cPi D.M t * (x₀ * x₁⁻¹) * (uc22p21cPi D.M t)⁻¹ ∈
      zpowers (x₀ * x₁⁻¹) ⊔ (barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hinf, -, -, -, hXn, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hT := u4x_isSylowOf_barImage (p := 2) D.sylowM
  have hτ : uc22p21cPi D.M t ∈ barImage D.M D.T := uc22p21c_mem_barImage.2 ⟨t, ht, rfl⟩
  set τ := uc22p21cPi D.M t with hτdef
  have hβ : τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ ∈ barImage D.M D.T := by
    rw [show τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ = τ * (x₀ * x₁ * τ⁻¹ * (x₀ * x₁)⁻¹) by group]
    exact mul_mem hτ ((mem_normalizer_iff.1 hN τ⁻¹).1 (inv_mem hτ))
  have hS : ∀ {s}, s ∈ barImage D.M D.T → s ∈ barImage D.M L ⊔ barImage D.M K →
      s ∈ zpowers (x₀ * x₁⁻¹) ⊔ (barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K)) :=
    fun h₁ h₂ => mem_sup_right ⟨h₁, h₂⟩
  have hy : x₀ * x₁⁻¹ ∈
      zpowers (x₀ * x₁⁻¹) ⊔ (barImage D.M D.T ⊓ (barImage D.M L ⊔ barImage D.M K)) :=
    mem_sup_left (mem_zpowers _)
  rcases u.conj_cases t.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have ha : τ * x₀ * τ⁻¹ * x₀⁻¹ ∈ barImage D.M L :=
      mul_mem ((mem_normalizer_iff.1 (uc22ine229_mk_mem_normalizer h0) x₀).1 hx₀) (inv_mem hx₀)
    have hb : τ * x₁ * τ⁻¹ * x₁⁻¹ ∈ barImage D.M K :=
      mul_mem ((mem_normalizer_iff.1 (uc22ine229_mk_mem_normalizer h1) x₁).1 hx₁) (inv_mem hx₁)
    have e1 := hcomm x₀ hx₀ _ hb
    have e : τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
        τ * x₀ * τ⁻¹ * x₀⁻¹ * (τ * x₁ * τ⁻¹ * x₁⁻¹) := by
      calc τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
          τ * x₀ * τ⁻¹ * x₀⁻¹ * (x₀ * (τ * x₁ * τ⁻¹ * x₁⁻¹)) * x₀⁻¹ := by group
        _ = τ * x₀ * τ⁻¹ * x₀⁻¹ * (τ * x₁ * τ⁻¹ * x₁⁻¹ * x₀) * x₀⁻¹ := by rw [e1]
        _ = τ * x₀ * τ⁻¹ * x₀⁻¹ * (τ * x₁ * τ⁻¹ * x₁⁻¹) := by group
    obtain ⟨haT, hbT⟩ := u4x_mem_of_mul_mem hcomm hinf hT hXn ha hb (by rw [← e]; exact hβ)
    rw [show τ * (x₀ * x₁⁻¹) * τ⁻¹ =
      τ * x₀ * τ⁻¹ * x₀⁻¹ * (x₀ * x₁⁻¹) * (τ * x₁ * τ⁻¹ * x₁⁻¹)⁻¹ by group]
    exact mul_mem (mul_mem (hS haT (mem_sup_left ha)) hy) (inv_mem (hS hbT (mem_sup_right hb)))
  · have h0' : τ * x₀ * τ⁻¹ ∈ barImage D.M K := u4x_conj_mem_barImage h0 hx₀
    have h1' : τ * x₁ * τ⁻¹ ∈ barImage D.M L := u4x_conj_mem_barImage h1 hx₁
    have ha : τ * x₁ * τ⁻¹ * x₀⁻¹ ∈ barImage D.M L := mul_mem h1' (inv_mem hx₀)
    have hb : τ * x₀ * τ⁻¹ * x₁⁻¹ ∈ barImage D.M K := mul_mem h0' (inv_mem hx₁)
    have e1 := hcomm _ h1' _ h0'
    have e2 := hcomm _ (inv_mem hx₀) _ hb
    have e : τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
        τ * x₁ * τ⁻¹ * x₀⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹) := by
      calc τ * (x₀ * x₁) * τ⁻¹ * (x₀ * x₁)⁻¹ =
          τ * x₀ * τ⁻¹ * (τ * x₁ * τ⁻¹) * x₁⁻¹ * x₀⁻¹ := by group
        _ = τ * x₁ * τ⁻¹ * (τ * x₀ * τ⁻¹) * x₁⁻¹ * x₀⁻¹ := by rw [← e1]
        _ = τ * x₁ * τ⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹ * x₀⁻¹) := by group
        _ = τ * x₁ * τ⁻¹ * (x₀⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹)) := by rw [← e2]
        _ = τ * x₁ * τ⁻¹ * x₀⁻¹ * (τ * x₀ * τ⁻¹ * x₁⁻¹) := by group
    obtain ⟨haT, hbT⟩ := u4x_mem_of_mul_mem hcomm hinf hT hXn ha hb (by rw [← e]; exact hβ)
    rw [show τ * (x₀ * x₁⁻¹) * τ⁻¹ =
      τ * x₀ * τ⁻¹ * x₁⁻¹ * (x₀ * x₁⁻¹)⁻¹ * (τ * x₁ * τ⁻¹ * x₀⁻¹)⁻¹ by group]
    exact mul_mem (mul_mem (hS hbT (mem_sup_right hb)) (inv_mem hy))
      (inv_mem (hS haT (mem_sup_left ha)))

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
