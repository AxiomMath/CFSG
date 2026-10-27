module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSectionAbelian
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSectionCount

public section

namespace CFSG.ShultStronglyClosedTI.CentralSection

open Subgroup

theorem card_sq_eq_one {P : Type*} [Group P] [Finite P] :
    Nat.card {g : P // g ^ 2 = 1} = Nat.card {g : P // orderOf g = 2} + 1 := by
  classical
  have := Fintype.ofFinite P
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun g : P => orderOf g = 2)
    (a := 1) (by simp only [Finset.mem_filter, Finset.mem_univ, orderOf_one,
      OfNat.one_ne_ofNat, and_false, not_false_eq_true])]
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, orderOf_eq_prime_iff]
  constructor
  · intro hg
    by_cases h1 : g = 1
    · exact Or.inl h1
    · exact Or.inr ⟨hg, h1⟩
  · rintro (rfl | ⟨hg, -⟩)
    · exact one_pow 2
    · exact hg

theorem singerSection_of {P X : Type*} [Group P] [Group X] [IsCyclic X] {Q : Subgroup P}
    [Q.Normal] (hQZ : Q ≤ center P) (hQel : IsElementaryAbelian 2 Q)
    (hPQ : IsElementaryAbelian 2 (P ⧸ Q)) {φ : X →* MulAut P}
    (hφQ : ∀ x : X, Q.map (φ x).toMonoidHom = Q)
    (hreg : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 → ∃! x : X, φ x a = b) {T : Subgroup P}
    (hT : ∀ t ∈ T, ∀ x : X, φ x t = t) (hTel : IsElementaryAbelian 2 T) (hQT : Q ⊓ T = ⊥)
    (hCT : ∀ t ∈ T, t ≠ 1 → centralizer {t} = Q ⊔ T) : SingerSection Q T φ where
  le_center := hQZ
  sq_eq_one z hz := by
    have := hQel
    exact elemPow_eq_one_of_isElementaryAbelian z hz
  commutator_mem a b := by
    have := hPQ
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      isMulCommutative_iff.mp inferInstance (a : P ⧸ Q) (b : P ⧸ Q)]
    group
  sq_mem a := by
    have := hPQ
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ Q)) _
  comm := isMulCommutative_iff.mp inferInstance
  map_mem x z hz := by
    rw [← hφQ x]
    exact mem_map_of_mem _ hz
  eq_one_of_fixed x z hz hz1 hfix := (hreg z hz hz1 z hz hz1).unique hfix
    (by simp only [map_one, MulAut.one_apply])
  exists_map_eq z hz hz1 z' hz' hz1' := (hreg z hz hz1 z' hz' hz1').exists
  fixed x t ht := hT t ht x
  sq_eq_one_of_mem t ht := by
    have := hTel
    exact elemPow_eq_one_of_isElementaryAbelian t ht
  inf_eq_bot := hQT
  centralizer_eq := hCT

theorem singer_central_section_characteristic_abelian_subgroup {P X : Type*} [Group P] [Finite P]
    [Group X] [IsCyclic X] {q e : ℕ} (hq : q = 2 ^ e) (he : 2 ≤ e) (hP : IsPGroup 2 P)
    {Q : Subgroup P} [Q.Normal] (hQZ : Q ≤ center P) (hQel : IsElementaryAbelian 2 Q)
    (hQcard : Nat.card Q = q) (hPQ : IsElementaryAbelian 2 (P ⧸ Q)) (hX : Nat.card X = q - 1)
    (φ : X →* MulAut P) (hφQ : ∀ x : X, Q.map (φ x).toMonoidHom = Q)
    (hreg : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 → ∃! x : X, φ x a = b) {T : Subgroup P}
    (hT : ∀ p : P, p ∈ T ↔ ∀ x : X, φ x p = p) (hTbot : T ≠ ⊥)
    (hTel : IsElementaryAbelian 2 T) (hQT : Q ⊓ T = ⊥)
    (hCT : ∀ t ∈ T, t ≠ 1 → centralizer {t} = Q ⊔ T)
    (hinv : Nat.card {p : P // orderOf p = 2} = q - 1 + q ^ 2 * (Nat.card T - 1)) :
    Nat.card T = 2 ∧ Nat.card P = 2 * q ^ 2 ∧
      (∃ R : Subgroup P, (IsMulCommutative R ∧ Nat.card R = q ^ 2) ∧
        (∀ S : Subgroup P, IsMulCommutative S → Nat.card S = q ^ 2 → S = R) ∧
        R.Characteristic ∧ Q < R ∧ R < ⊤) ∧
      ∀ A : Subgroup (MulAut P), (∀ σ ∈ A, Q.map σ.toMonoidHom = Q) →
        ¬ ∀ W : Subgroup (P ⧸ Q),
          (∀ σ ∈ A, ∀ p : P, (p : P ⧸ Q) ∈ W → ((σ p : P) : P ⧸ Q) ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have h : SingerSection Q T φ :=
    singerSection_of hQZ hQel hPQ hφQ hreg (fun t ht => (hT t).mp ht) hTel hQT hCT
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := ne_bot_iff_exists_ne_one.mp hTbot
  have ht₀1' : t₀ ≠ 1 := fun h1 => ht₀1 (Subtype.ext h1)
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x₁, hx₁⟩ := exists_ne (1 : X)
  have hcount : Nat.card {g : P // g ^ 2 = 1} =
      Nat.card Q + Nat.card Q ^ 2 * (Nat.card T - 1) := by
    rw [card_sq_eq_one, hinv, hQcard]
    omega
  have hT2 : Nat.card T = 2 :=
    le_antisymm (h.card_le_two ht₀ ht₀1' (by omega) hcount) ((one_lt_card_iff_ne_bot T).mpr hTbot)
  obtain ⟨hPcard, hHcard⟩ := h.card_eq hP (hQcard.trans hq) hT2 ht₀ ht₀1' hcount
  set R := h.twistSubgroup x₁ with hRdef
  have hRcard : Nat.card R = q ^ 2 := by
    rw [← hQcard]
    exact h.card_twistSubgroup ht₀ ht₀1' hx₁ hPcard hHcard
  rw [hQcard] at hPcard
  have hRne : ∃ r ∈ R, r ∉ Q := by
    by_contra hall
    have hle : R ≤ Q := fun r hr => by_contra fun hrQ => hall ⟨r, hr, hrQ⟩
    have := card_le_of_le hle
    rw [hRcard, hQcard] at this
    nlinarith
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    h.mul_comm_of_mem_twistSubgroup ht₀ ht₀1' hx₁ hRne ha hb
  have hRab : IsMulCommutative R :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hRcomm a a.2 b b.2)
  have huniq : ∀ S : Subgroup P, IsMulCommutative S → Nat.card S = q ^ 2 → S = R := by
    intro S hS hScard
    have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (isMulCommutative_iff.mp hS ⟨a, ha⟩ ⟨b, hb⟩)
    have hle := h.le_twistSubgroup ht₀ ht₀1' hx₁ (hQcard ▸ hq4) (hQcard ▸ hPcard)
      (hQcard ▸ hRcard) hRcomm hScomm (hQcard ▸ hScard)
    exact eq_of_le_of_card_ge hle (by rw [hRcard, hScard])
  have hchar : R.Characteristic :=
    characteristic_iff_map_eq.mpr fun ϕ => huniq _ (map_isMulCommutative R ϕ.toMonoidHom)
      (by rw [card_map_of_injective ϕ.injective, hRcard])
  have hσR : ∀ σ : MulAut P, ∀ p ∈ R, σ p ∈ R := fun σ p hp => by
    rw [← characteristic_iff_map_eq.mp hchar σ]
    exact mem_map_of_mem σ.toMonoidHom hp
  have hQR : Q ≤ R := h.le_twistSubgroup_self x₁
  have ht₀R : t₀ ∉ R := h.t₀_notMem_twistSubgroup ht₀ ht₀1' hx₁
  have hmemW : ∀ p : P, (p : P ⧸ Q) ∈ R.map (QuotientGroup.mk' Q) ↔ p ∈ R := by
    intro p
    constructor
    · rintro ⟨r, hr, hrp⟩
      have hp : p = r * (r⁻¹ * p) := by group
      rw [hp]
      exact mul_mem hr (hQR (QuotientGroup.eq.mp hrp))
    · exact fun hp => mem_map_of_mem _ hp
  refine ⟨hT2, hPcard, ⟨R, ⟨hRab, hRcard⟩, huniq, hchar, lt_of_le_of_ne hQR ?_,
    lt_of_le_of_ne le_top ?_⟩, ?_⟩
  · intro hQR'
    have hc := congrArg (fun K : Subgroup P => Nat.card K) hQR'
    simp only [hQcard, hRcard] at hc
    nlinarith
  · intro hR
    exact ht₀R (hR ▸ mem_top t₀)
  · intro A _ hirr
    rcases hirr (R.map (QuotientGroup.mk' Q))
        (fun σ _ p hp => (hmemW _).mpr (hσR σ p ((hmemW p).mp hp))) with hbot | htop
    · obtain ⟨r, hr, hrQ⟩ := hRne
      have hrW := (hmemW r).mpr hr
      rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at hrW
      exact hrQ hrW
    · have ht₀W : (t₀ : P ⧸ Q) ∈ R.map (QuotientGroup.mk' Q) := by
        rw [htop]
        exact mem_top _
      exact ht₀R ((hmemW t₀).mp ht₀W)

end CFSG.ShultStronglyClosedTI.CentralSection
