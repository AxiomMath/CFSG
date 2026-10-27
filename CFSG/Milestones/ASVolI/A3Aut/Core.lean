module

public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.ASVolI

open scoped Pointwise

section Core

variable {A : Type} [Group A]

theorem burnsideAut_map_conj_le_normalizer {X Y : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (Y : Set A)) (h : X ≤ Subgroup.normalizer (Y : Set A)) :
    X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Y : Set A) := by
  rintro _ ⟨x, hx, rfl⟩
  have : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (h hx)) (Subgroup.inv_mem _ hg)

theorem burnsideAut_map_conj_self {Y : Subgroup A} {g : A} (hg : g ∈ Y) :
    Y.map (MulAut.conj g).toMonoidHom = Y :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)

theorem burnsideAut_mem_map_conj {X : Subgroup A} {g x : A} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := rfl
    rw [this]
    simpa [mul_assoc] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem burnsideAut_mem_sup_iff {Y X : Subgroup A} (hXY : X ≤ Subgroup.normalizer (Y : Set A))
    {x : A} : x ∈ Y ⊔ X ↔ ∃ y ∈ Y, ∃ z ∈ X, x = y * z := by
  constructor
  · intro hx
    have : x ∈ ((Y ⊔ X : Subgroup A) : Set A) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y X hXY] at this
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 this
    exact ⟨y, hy, z, hz, rfl⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

variable [Finite A]

theorem burnsideAut_disjoint_of_odd {S H : Subgroup A} (hS : IsPGroup 2 S) (hH : Odd (Nat.card H)) :
    Disjoint S H := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hH)


theorem burnsideAut_conj_of_complements {p : ℕ} [Fact p.Prime] {E Z Y : Subgroup A}
    (hZE : Z ≤ Subgroup.normalizer (E : Set A)) (hYE : Y ≤ Subgroup.normalizer (E : Set A))
    (hE : IsPGroup p E) (hZp : ¬ p ∣ Nat.card Z)
    (hEZ : Disjoint E Z) (hEY : Disjoint E Y) (hYZ : E ⊔ Y = E ⊔ Z) :
    ∃ e ∈ E, Y.map (MulAut.conj e).toMonoidHom = Z := by
  set H₀ : Subgroup A := E ⊔ Z with hH₀
  have hEH : E ≤ H₀ := le_sup_left
  have hZH : Z ≤ H₀ := le_sup_right
  have hYH : Y ≤ H₀ := hYZ ▸ le_sup_right
  have hH₀N : H₀ ≤ Subgroup.normalizer (E : Set A) := sup_le Subgroup.le_normalizer hZE
  haveI : (E.subgroupOf H₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).2 hH₀N
  have hmul : ∀ g ∈ H₀, ∃ e ∈ E, ∃ z ∈ Z, e * z = g := by
    intro g hg
    obtain ⟨e, he, z, hz, rfl⟩ := (burnsideAut_mem_sup_iff hZE).1 hg
    exact ⟨e, he, z, hz, rfl⟩
  have hmulY : ∀ g ∈ H₀, ∃ e ∈ E, ∃ y ∈ Y, e * y = g := by
    intro g hg
    have hg' : g ∈ E ⊔ Y := hYZ ▸ hg
    obtain ⟨e, he, y, hy, rfl⟩ := (burnsideAut_mem_sup_iff hYE).1 hg'
    exact ⟨e, he, y, hy, rfl⟩
  have hN : IsPGroup p (E.subgroupOf H₀) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  have hZg : ¬ p ∣ Nat.card (Z.subgroupOf H₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    exact hZp
  have hdisj : ∀ {W : Subgroup A}, Disjoint E W → Disjoint (E.subgroupOf H₀) (W.subgroupOf H₀) := by
    intro W hW
    rw [Subgroup.disjoint_def] at hW ⊢
    intro x hx1 hx2
    have := hW hx1 hx2
    exact Subtype.ext this
  have htop : ∀ {W : Subgroup A}, W ≤ H₀ → (∀ g ∈ H₀, ∃ e ∈ E, ∃ w ∈ W, e * w = g) →
      E.subgroupOf H₀ ⊔ W.subgroupOf H₀ = ⊤ := by
    intro W hW hmulW
    rw [eq_top_iff]
    intro g _
    obtain ⟨e, he, w, hw, hew⟩ := hmulW g.1 g.2
    have h1 : (⟨e, hEH he⟩ : H₀) ∈ E.subgroupOf H₀ := he
    have h2 : (⟨w, hW hw⟩ : H₀) ∈ W.subgroupOf H₀ := hw
    have : g = ⟨e, hEH he⟩ * ⟨w, hW hw⟩ := Subtype.ext hew.symm
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  obtain ⟨n, hn, hnY⟩ := CFSG.GH74.BNPair.exists_conj_of_complements_top (p := p) hN hZg
    (hdisj hEZ) (hdisj hEY) (htop hZH hmul) (htop hYH hmulY)
  refine ⟨(n : A), hn, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : (⟨y, hYH hy⟩ : H₀) ∈ Y.subgroupOf H₀ := hy
    have h2 : n * ⟨y, hYH hy⟩ * n⁻¹ ∈ Z.subgroupOf H₀ := by
      rw [← hnY]
      exact Subgroup.mem_map.2 ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa [MulAut.conj_apply] using h3
  · intro hx
    have h1 : (⟨x, hZH hx⟩ : H₀) ∈ Z.subgroupOf H₀ := hx
    rw [← hnY] at h1
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
    refine ⟨(y : A), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this

theorem burnsideAut_card_sup_of_le_normalizer {X Y : Subgroup A}
    (hYX : Y ≤ Subgroup.normalizer (X : Set A)) (hXY : X ⊓ Y = ⊥) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y :=
  burnsideA315x_card_sup (Subgroup.set_mul_normalizer_comm (Y : Set A) X fun _ hy => hYX hy).symm
    hXY

theorem burnsideAut_case5_core_aux {Lb I J Φ Sb H₀ Bb : Subgroup A}
    (hSbLb : Sb ≤ Lb) (hLbI : Lb ≤ I) (hIJ : I ≤ J)
    (hΦI : Φ ≤ Subgroup.normalizer (I : Set A)) (hIΦ : I ⊓ Φ = ⊥)
    (hΦJ : Φ ≤ Subgroup.normalizer (J : Set A))
    (hΦS : Φ ≤ Subgroup.normalizer (Sb : Set A))
    (hNS : I ⊓ Subgroup.normalizer (Sb : Set A) = Sb ⊔ H₀)
    (hH₀I : H₀ ≤ I) (hH₀S : H₀ ≤ Subgroup.normalizer (Sb : Set A))
    (hH₀odd : Odd (Nat.card H₀)) (hΦH₀ : Φ ≤ Subgroup.normalizer (H₀ : Set A))
    (hSb2 : IsPGroup 2 Sb) (hB : Bb ≤ H₀ ⊔ Φ) (hBodd : Odd (Nat.card Bb)) :
    ∃ F H : Subgroup A, F ≤ Φ ∧ Nat.card F ∣ Nat.card Bb ∧
      F ≤ Subgroup.normalizer (Sb : Set A) ∧ F ≤ Subgroup.normalizer (H : Set A) ∧
      CFSG.Quasithin.A315.IsCartan 2 Sb ((F ⊔ Bb ⊔ Lb) ⊓ J) H ∧
      F ⊔ Bb ⊔ Lb = H ⊔ Bb ⊔ Lb ∧ Bb ≤ F ⊔ H ∧
      ∀ x ∈ F, ∃ b ∈ Bb, x * b⁻¹ ∈ I := by
  have hH₀Φ : ∀ {x : A}, x ∈ H₀ ⊔ Φ ↔ ∃ h ∈ H₀, ∃ φ ∈ Φ, x = h * φ :=
    burnsideAut_mem_sup_iff hΦH₀
  have hBH₀ : Bb ≤ Subgroup.normalizer (H₀ : Set A) := hB.trans (sup_le Subgroup.le_normalizer hΦH₀)
  have hIΦ' : ∀ {φ : A}, φ ∈ Φ → φ ∈ I → φ = 1 := fun {φ} hφ hφI => by
    have : φ ∈ I ⊓ Φ := ⟨hφI, hφ⟩
    rw [hIΦ] at this
    exact this
  set W : Subgroup A := Φ ⊓ (H₀ ⊔ Bb) ⊔ Bb ⊔ Lb with hW
  set F : Subgroup A := Φ ⊓ (H₀ ⊔ Bb) with hF
  set H₁ : Subgroup A := W ⊓ H₀ with hH₁
  set F₀ : Subgroup A := F ⊓ J with hF₀
  set H : Subgroup A := H₁ ⊔ F₀ with hH
  have hFΦ : F ≤ Φ := inf_le_left
  have hFW : F ≤ W := le_sup_left.trans le_sup_left
  have hBW : Bb ≤ W := le_sup_right.trans le_sup_left
  have hLW : Lb ≤ W := le_sup_right
  have hFH₀ : ∀ {x : A}, x ∈ H₀ ⊔ Bb ↔ ∃ h ∈ H₀, ∃ b ∈ Bb, x = h * b :=
    burnsideAut_mem_sup_iff hBH₀
  have hdec : ∀ b ∈ Bb, ∃ h ∈ H₁, ∃ φ ∈ F, b = h * φ := by
    intro b hb
    obtain ⟨h, hh, φ, hφ, rfl⟩ := hH₀Φ.1 (hB hb)
    have hφF : φ ∈ F := ⟨hφ, hFH₀.2 ⟨h⁻¹, H₀.inv_mem hh, h * φ, hb, by group⟩⟩
    refine ⟨h, ⟨?_, hh⟩, φ, hφF, rfl⟩
    have : h = (h * φ) * φ⁻¹ := by group
    rw [this]
    exact W.mul_mem (hBW hb) (W.inv_mem (hFW hφF))
  have hdecF : ∀ φ ∈ F, ∃ h ∈ H₁, ∃ b ∈ Bb, φ = h * b := by
    intro φ hφ
    obtain ⟨h, hh, b, hb, hφeq⟩ := hFH₀.1 hφ.2
    refine ⟨h, ⟨?_, hh⟩, b, hb, hφeq⟩
    have : h = φ * b⁻¹ := by rw [hφeq]; group
    rw [this]
    exact W.mul_mem (hFW hφ) (W.inv_mem (hBW hb))
  have hH₁H₀ : H₁ ≤ H₀ := inf_le_right
  have hH₁W : H₁ ≤ W := inf_le_left
  have hF₀F : F₀ ≤ F := inf_le_left
  have hF₀J : F₀ ≤ J := inf_le_right
  have hFH₀n : F ≤ Subgroup.normalizer (H₀ : Set A) := hFΦ.trans hΦH₀
  have hFWn : F ≤ Subgroup.normalizer (W : Set A) := hFW.trans Subgroup.le_normalizer
  have hFH₁n : F ≤ Subgroup.normalizer (H₁ : Set A) :=
    (le_inf hFWn hFH₀n).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hFJn : F ≤ Subgroup.normalizer (J : Set A) := hFΦ.trans hΦJ
  have hFF₀n : F ≤ Subgroup.normalizer (F₀ : Set A) :=
    (le_inf Subgroup.le_normalizer hFJn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hFHn : F ≤ Subgroup.normalizer (H : Set A) :=
    (le_inf hFH₁n hFF₀n).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup H₁ F₀)
  have hF₀H₁n : F₀ ≤ Subgroup.normalizer (H₁ : Set A) := hF₀F.trans hFH₁n
  have hH₁F₀ : H₁ ⊓ F₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    exact hIΦ' (hFΦ (hF₀F hx2)) (hH₀I (hH₁H₀ hx1))
  have hH₀F : H₀ ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    exact hIΦ' (hFΦ hx2) (hH₀I hx1)
  have hsupF : H₀ ⊔ F = H₀ ⊔ Bb := by
    refine le_antisymm (sup_le le_sup_left inf_le_right) (sup_le le_sup_left ?_)
    intro b hb
    obtain ⟨h, hh, φ, hφ, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem_sup (hH₁H₀ hh) hφ
  have hcardF : Nat.card ↥(H₀ ⊔ F) = Nat.card H₀ * Nat.card F :=
    burnsideAut_card_sup_of_le_normalizer hFH₀n hH₀F
  have hcardFdvd : Nat.card F ∣ Nat.card Bb := by
    have h1 : Bb.relIndex (H₀ ⊔ Bb) = Bb.relIndex H₀ := burnsideA315x_relIndex_sup hBH₀
    have h2 : Bb.relIndex (H₀ ⊔ Bb) * Nat.card ↥(Bb ⊓ (H₀ ⊔ Bb)) = Nat.card ↥(H₀ ⊔ Bb) :=
      Subgroup.relIndex_mul_card Bb (H₀ ⊔ Bb)
    have h3 : Bb.relIndex H₀ * Nat.card ↥(Bb ⊓ H₀) = Nat.card H₀ := Subgroup.relIndex_mul_card Bb H₀
    have h4 : Bb ⊓ (H₀ ⊔ Bb) = Bb := inf_eq_left.2 le_sup_right
    rw [h4, h1] at h2
    rw [← hsupF, hcardF] at h2
    have hpos : 0 < Nat.card H₀ := Nat.card_pos
    refine ⟨Nat.card ↥(Bb ⊓ H₀), ?_⟩
    have h5 : Nat.card H₀ * (Nat.card F * Nat.card ↥(Bb ⊓ H₀)) =
        Nat.card H₀ * Nat.card Bb := by
      calc Nat.card H₀ * (Nat.card F * Nat.card ↥(Bb ⊓ H₀))
          = Nat.card H₀ * Nat.card F * Nat.card ↥(Bb ⊓ H₀) := by ring
        _ = Bb.relIndex H₀ * Nat.card Bb * Nat.card ↥(Bb ⊓ H₀) := by rw [h2]
        _ = (Bb.relIndex H₀ * Nat.card ↥(Bb ⊓ H₀)) * Nat.card Bb := by ring
        _ = Nat.card H₀ * Nat.card Bb := by rw [h3]
    exact (Nat.eq_of_mul_eq_mul_left hpos h5).symm
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat hBodd hcardFdvd
  have hHcard : Nat.card H = Nat.card H₁ * Nat.card F₀ :=
    burnsideAut_card_sup_of_le_normalizer hF₀H₁n hH₁F₀
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Nat.odd_mul.2 ⟨Odd.of_dvd_nat hH₀odd (Subgroup.card_dvd_of_le hH₁H₀),
      Odd.of_dvd_nat hFodd (Subgroup.card_dvd_of_le hF₀F)⟩
  have hWIF : W ≤ I ⊔ F := by
    refine sup_le (sup_le le_sup_right ?_) (hLbI.trans le_sup_left)
    intro b hb
    obtain ⟨h, hh, φ, hφ, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem_sup (hH₀I (hH₁H₀ hh)) hφ
  have hFI : F ≤ Subgroup.normalizer (I : Set A) := hFΦ.trans hΦI
  have hHle : H ≤ W ⊓ J ⊓ Subgroup.normalizer (Sb : Set A) := by
    refine sup_le (le_inf (le_inf hH₁W (hH₁H₀.trans (hH₀I.trans hIJ))) (hH₁H₀.trans hH₀S)) ?_
    exact le_inf (le_inf (hF₀F.trans hFW) hF₀J) (hF₀F.trans (hFΦ.trans hΦS))
  have hSbW : Sb ≤ W := hSbLb.trans hLW
  have hborel : W ⊓ J ⊓ Subgroup.normalizer (Sb : Set A) = Sb ⊔ H := by
    refine le_antisymm ?_ (sup_le (le_inf (le_inf hSbW (hSbLb.trans (hLbI.trans hIJ)))
      Subgroup.le_normalizer) hHle)
    rintro x ⟨⟨hxW, hxJ⟩, hxN⟩
    obtain ⟨i, hi, f, hf, rfl⟩ := (burnsideAut_mem_sup_iff hFI).1 (hWIF hxW)
    have hfN : f ∈ Subgroup.normalizer (Sb : Set A) := hFΦ.trans hΦS hf
    have hiN : i ∈ Subgroup.normalizer (Sb : Set A) := by
      have : i = (i * f) * f⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hfN)
    have hiSH : i ∈ Sb ⊔ H₀ := by
      rw [← hNS]
      exact ⟨hi, hiN⟩
    obtain ⟨s, hs, h, hh, rfl⟩ := (burnsideAut_mem_sup_iff hH₀S).1 hiSH
    have hhW : h ∈ W := by
      have : h = s⁻¹ * (s * h * f) * f⁻¹ := by group
      rw [this]
      exact W.mul_mem (W.mul_mem (W.inv_mem (hSbW hs)) hxW) (W.inv_mem (hFW hf))
    have hfJ : f ∈ J := by
      have : f = (s * h)⁻¹ * (s * h * f) := by group
      rw [this]
      exact J.mul_mem (J.inv_mem (hIJ hi)) hxJ
    have h1 : h * f ∈ H := Subgroup.mul_mem_sup ⟨hhW, hh⟩ ⟨hf, hfJ⟩
    have : s * h * f = s * (h * f) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hs h1
  have hSbH : Sb ⊓ H = ⊥ := disjoint_iff.1 (burnsideAut_disjoint_of_odd hSb2 hHodd)
  have hindex : H.relIndex (Sb ⊔ H) = Nat.card Sb := by
    have hHn : H ≤ Subgroup.normalizer (Sb : Set A) := hHle.trans inf_le_right
    rw [burnsideA315x_relIndex_sup hHn]
    have h1 := Subgroup.relIndex_mul_card H Sb
    rw [inf_comm, hSbH] at h1
    simpa using h1
  obtain ⟨k, hk⟩ := hSb2.exists_card_eq
  refine ⟨F, H, hFΦ, hcardFdvd, hFΦ.trans hΦS, hFHn, ⟨hHle, ?_, k, ?_⟩, ?_, ?_, ?_⟩
  · rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hHodd
  · change H.relIndex (W ⊓ J ⊓ Subgroup.normalizer (Sb : Set A)) = 2 ^ k
    rw [hborel, hindex, hk]
  · apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro φ hφ
        obtain ⟨h, hh, b, hb, rfl⟩ := hdecF φ hφ
        exact (H ⊔ Bb ⊔ Lb).mul_mem
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hh)))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact hHle.trans (inf_le_left.trans inf_le_left)
      · exact hBW
      · exact hLW
  · intro b hb
    obtain ⟨h, hh, φ, hφ, rfl⟩ := hdec b hb
    exact (F ⊔ H).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hh))
      (Subgroup.mem_sup_left hφ)
  · intro x hx
    obtain ⟨h, hh, b, hb, rfl⟩ := hdecF x hx
    refine ⟨b, hb, ?_⟩
    have : h * b * b⁻¹ = h := by group
    rw [this]
    exact hH₀I (hH₁H₀ hh)

theorem burnsideAut_case5_core {Lb I J Φ Sb H₀ Bb : Subgroup A}
    (hSbLb : Sb ≤ Lb) (hLbI : Lb ≤ I) (hIJ : I ≤ J)
    (hΦI : Φ ≤ Subgroup.normalizer (I : Set A)) (hIΦ : I ⊓ Φ = ⊥)
    (hΦJ : Φ ≤ Subgroup.normalizer (J : Set A))
    (hΦS : Φ ≤ Subgroup.normalizer (Sb : Set A))
    (hNS : I ⊓ Subgroup.normalizer (Sb : Set A) = Sb ⊔ H₀)
    (hH₀I : H₀ ≤ I) (hH₀S : H₀ ≤ Subgroup.normalizer (Sb : Set A))
    (hH₀odd : Odd (Nat.card H₀)) (hΦH₀ : Φ ≤ Subgroup.normalizer (H₀ : Set A))
    (hSb2 : IsPGroup 2 Sb) (hBΦ : Bb ≤ I ⊔ Φ) (hBS : Bb ≤ Subgroup.normalizer (Sb : Set A))
    (hBodd : Odd (Nat.card Bb)) :
    ∃ s ∈ Sb, ∃ F H : Subgroup A, F ≤ Φ.map (MulAut.conj s).toMonoidHom ∧
      Nat.card F ∣ Nat.card Bb ∧
      F ≤ Subgroup.normalizer (Sb : Set A) ∧ F ≤ Subgroup.normalizer (H : Set A) ∧
      CFSG.Quasithin.A315.IsCartan 2 Sb ((F ⊔ Bb ⊔ Lb) ⊓ J) H ∧
      F ⊔ Bb ⊔ Lb = H ⊔ Bb ⊔ Lb ∧ Bb ≤ F ⊔ H ∧
      ∀ x ∈ F, ∃ b ∈ Bb, x * b⁻¹ ∈ I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSbI : Sb ≤ I := hSbLb.trans hLbI
  have hIΦ' : ∀ {φ : A}, φ ∈ Φ → φ ∈ I → φ = 1 := fun {φ} hφ hφI => by
    have : φ ∈ I ⊓ Φ := ⟨hφI, hφ⟩
    rw [hIΦ] at this
    exact this
  have hH₀Φn : H₀ ⊔ Φ ≤ Subgroup.normalizer (Sb : Set A) := sup_le hH₀S hΦS
  have hIΦN : ∀ x ∈ I ⊔ Φ, x ∈ Subgroup.normalizer (Sb : Set A) → x ∈ Sb ⊔ (H₀ ⊔ Φ) := by
    intro x hx hxN
    obtain ⟨i, hi, φ, hφ, rfl⟩ := (burnsideAut_mem_sup_iff hΦI).1 hx
    have hiN : i ∈ Subgroup.normalizer (Sb : Set A) := by
      have : i = (i * φ) * φ⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ (hΦS hφ))
    have hiSH : i ∈ Sb ⊔ H₀ := by rw [← hNS]; exact ⟨hi, hiN⟩
    obtain ⟨s, hs, h, hh, rfl⟩ := (burnsideAut_mem_sup_iff hH₀S).1 hiSH
    have : s * h * φ = s * (h * φ) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hs (Subgroup.mul_mem_sup hh hφ)
  set C : Subgroup A := (Sb ⊔ Bb) ⊓ (H₀ ⊔ Φ) with hC
  have hSbBbN : Sb ⊔ Bb ≤ Subgroup.normalizer (Sb : Set A) := sup_le Subgroup.le_normalizer hBS
  have hCN : C ≤ Subgroup.normalizer (Sb : Set A) := inf_le_left.trans hSbBbN
  have hSbC : Sb ⊔ C = Sb ⊔ Bb := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) (sup_le le_sup_left ?_)
    intro b hb
    have hbIΦ : b ∈ I ⊔ Φ := hBΦ hb
    obtain ⟨s, hs, y, hy, rfl⟩ := (burnsideAut_mem_sup_iff hH₀Φn).1 (hIΦN b hbIΦ (hBS hb))
    have hyC : y ∈ C := by
      refine ⟨?_, hy⟩
      have : y = s⁻¹ * (s * y) := by group
      rw [this]
      exact (Sb ⊔ Bb).mul_mem (Subgroup.mem_sup_left (Sb.inv_mem hs)) (Subgroup.mem_sup_right hb)
    exact Subgroup.mul_mem_sup hs hyC
  have hdisjC : Disjoint Sb C := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxC
    obtain ⟨h, hh, φ, hφ, hxeq⟩ := (burnsideAut_mem_sup_iff hΦH₀).1 hxC.2
    have hφ1 : φ = 1 := by
      refine hIΦ' hφ ?_
      have : φ = h⁻¹ * x := by rw [hxeq]; group
      rw [this]
      exact I.mul_mem (I.inv_mem (hH₀I hh)) (hSbI hxS)
    rw [hφ1, mul_one] at hxeq
    rw [hxeq] at hxS
    have h1 : h ∈ Sb ⊓ H₀ := ⟨hxS, hh⟩
    rw [disjoint_iff.1 (burnsideAut_disjoint_of_odd hSb2 hH₀odd)] at h1
    rw [hxeq]
    exact h1
  have hdisjB : Disjoint Sb Bb := burnsideAut_disjoint_of_odd hSb2 hBodd
  have hBp : ¬ 2 ∣ Nat.card Bb := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hBodd
  obtain ⟨e, he, hCe⟩ := burnsideAut_conj_of_complements (p := 2) hBS hCN hSb2 hBp hdisjB hdisjC
    hSbC
  set ψ : A →* A := (MulAut.conj e).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj e).injective
  have heI : e ∈ I := hSbI he
  have heN : e ∈ Subgroup.normalizer (Sb : Set A) := Subgroup.le_normalizer he
  have hBle : Bb ≤ H₀.map ψ ⊔ Φ.map ψ := by
    rw [← hCe, ← Subgroup.map_sup]
    exact Subgroup.map_mono inf_le_right
  have hIψ : I.map ψ = I := burnsideAut_map_conj_self heI
  have hNψ : (Subgroup.normalizer (Sb : Set A)).map ψ = Subgroup.normalizer (Sb : Set A) :=
    burnsideAut_map_conj_self heN
  have hSbψ : Sb.map ψ = Sb := burnsideAut_map_conj_self he
  have hΦ'I : Φ.map ψ ≤ Subgroup.normalizer (I : Set A) :=
    burnsideAut_map_conj_le_normalizer (Subgroup.le_normalizer heI) hΦI
  have hIΦ'' : I ⊓ Φ.map ψ = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxI, hxΦ⟩
    have h1 : e⁻¹ * x * e ∈ Φ := burnsideAut_mem_map_conj.1 hxΦ
    have h2 : e⁻¹ * x * e ∈ I := I.mul_mem (I.mul_mem (I.inv_mem heI) hxI) heI
    have h3 := hIΦ' h1 h2
    have : x = e * (e⁻¹ * x * e) * e⁻¹ := by group
    rw [Subgroup.mem_bot, this, h3]
    group
  have hΦ'J : Φ.map ψ ≤ Subgroup.normalizer (J : Set A) :=
    burnsideAut_map_conj_le_normalizer (Subgroup.le_normalizer (hIJ heI)) hΦJ
  have hΦ'S : Φ.map ψ ≤ Subgroup.normalizer (Sb : Set A) :=
    burnsideAut_map_conj_le_normalizer heN hΦS
  have hNS' : I ⊓ Subgroup.normalizer (Sb : Set A) = Sb ⊔ H₀.map ψ := by
    have h1 : (I ⊓ Subgroup.normalizer (Sb : Set A)).map ψ = (Sb ⊔ H₀).map ψ := by rw [hNS]
    rw [Subgroup.map_inf _ _ _ hψinj, hIψ, hNψ, Subgroup.map_sup, hSbψ] at h1
    exact h1
  have hH₀'I : H₀.map ψ ≤ I := hIψ ▸ Subgroup.map_mono hH₀I
  have hH₀'S : H₀.map ψ ≤ Subgroup.normalizer (Sb : Set A) :=
    burnsideAut_map_conj_le_normalizer heN hH₀S
  have hH₀'odd : Odd (Nat.card (H₀.map ψ)) := by
    rw [Subgroup.card_map_of_injective hψinj]
    exact hH₀odd
  have hΦ'H₀' : Φ.map ψ ≤ Subgroup.normalizer (H₀.map ψ : Set A) := by
    have h1 := Subgroup.map_equiv_normalizer_eq H₀ (MulAut.conj e)
    rw [← h1]
    exact Subgroup.map_mono hΦH₀
  obtain ⟨F, H, hF, hrest⟩ := burnsideAut_case5_core_aux hSbLb hLbI hIJ hΦ'I hIΦ'' hΦ'J hΦ'S hNS'
    hH₀'I hH₀'S hH₀'odd hΦ'H₀' hSb2 hBle hBodd
  exact ⟨e, he, F, H, hF, hrest⟩

end Core

section Borel

@[expose] def burnsideAut_SolvBorel (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, S ≤ Y → Group.IsSolvable ↥Y → Y ≤ Subgroup.normalizer (S : Set X)

theorem burnsideAut_le_of_sylow {G : Type} [Group G] [Finite G] {S P L : Subgroup G}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S L) (hSP : S ≤ P) (hPL : P ≤ L)
    (hP : IsPGroup 2 P) : P ≤ S := by
  have h1 := Subgroup.relIndex_mul_relIndex S P L hSP hPL
  have h2 : S.relIndex P ∣ Nat.card P := Subgroup.relIndex_dvd_card S P
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  rcases j with _ | j
  · simp only [pow_zero] at hj
    exact Subgroup.relIndex_eq_one.1 hj
  · exfalso
    apply hS.2.2
    change 2 ∣ S.relIndex L
    rw [← h1, hj]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero j)) _

theorem burnsideAut_le_normalizer_of_hyp {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B)
    (hsb : burnsideAut_SolvBorel ↥L ((T ⊓ L).subgroupOf L)) :
    B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  haveI := h.sqtk.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hLn : L.Normal := burnsideA315x_normal h
  have hT2 : IsPGroup 2 T := h.sylow.2.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L := burnsideA315x_sylow_inf h.sylow
  have hBnil : Group.IsNilpotent ↥B := by
    rcases h.cases with hab | ⟨r, hr, hBr, -⟩
    · haveI := hab
      exact CommGroup.isNilpotent
    · haveI : Fact r.Prime := ⟨hr⟩
      exact hBr.isNilpotent
  set X : Subgroup G := B ⊔ T with hX
  have hXsolv : Group.IsSolvable ↥X := by
    have hBle : B ≤ X := le_sup_left
    have hTle : T ≤ X := le_sup_right
    have eA : ↥(B.subgroupOf X) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBle
    have eC : ↥(T.subgroupOf X) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTle
    haveI := hBnil
    refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf X)
      (T.subgroupOf X) (Group.nilpotent_of_mulEquiv eA.symm)
      ((hT2.of_equiv eC.symm).isNilpotent) ?_ ?_
    · rw [Nat.card_congr eA.toEquiv, Nat.card_congr eC.toEquiv]
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk]
      exact (Nat.coprime_two_left.2 h.odd).symm.pow_right k
    · intro g
      have hg : (g : G) ∈ ((B ⊔ T : Subgroup G) : Set G) := g.2
      rw [burnsideA315x_coe_sup h.perm] at hg
      obtain ⟨b, hb, t, ht, hbt⟩ := hg
      exact ⟨⟨b, hBle hb⟩, hb, ⟨t, hTle ht⟩, ht, Subtype.ext hbt.symm⟩
  set Y : Subgroup G := X ⊓ L with hY
  have hYsolv : Group.IsSolvable ↥(Y.subgroupOf L) := by
    have e : ↥(Y.subgroupOf L) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe inf_le_right
    have hinj : Function.Injective ((Subgroup.inclusion (inf_le_left : Y ≤ X)).comp
      e.toMonoidHom) :=
      (Subgroup.inclusion_injective (inf_le_left : Y ≤ X)).comp e.injective
    exact solvable_of_solvable_injective hinj
  have hSY : (T ⊓ L).subgroupOf L ≤ Y.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
  have hYN := hsb _ hSY hYsolv
  have hYNG : Y ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyL : y ∈ L := hy.2
    have hm := Subgroup.mem_normalizer_iff.1 (hYN (Subgroup.mem_subgroupOf.2 hy :
      (⟨y, hyL⟩ : ↥L) ∈ Y.subgroupOf L))
    constructor
    · intro hz
      have hzL : z ∈ L := hz.2
      have h1 := (hm ⟨z, hzL⟩).1 (Subgroup.mem_subgroupOf.2 hz)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · intro hz
      have hzL : y * z * y⁻¹ ∈ L := hz.2
      have hzL' : z ∈ L := by
        have : z = y⁻¹ * (y * z * y⁻¹) * y := by group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem hyL) hzL) hyL
      have h1 := (hm ⟨z, hzL'⟩).2 (by
        rw [Subgroup.mem_subgroupOf]
        simpa using hz)
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1
  intro b hb
  have hbX : b ∈ X := Subgroup.mem_sup_left hb
  set P : Subgroup G := (T ⊓ L).map (MulAut.conj b).toMonoidHom with hP
  have hPY : P ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, hLn.conj_mem x hx.2 b⟩
    exact X.mul_mem (X.mul_mem hbX (Subgroup.mem_sup_right hx.1)) (X.inv_mem hbX)
  have hP2 : IsPGroup 2 P := (hT2.to_le inf_le_left).map _
  have hPS2 : IsPGroup 2 ↥(P ⊔ (T ⊓ L)) :=
    IsPGroup.to_sup_of_normal_right' hP2 (hT2.to_le inf_le_left) (hPY.trans hYNG)
  have hPSL : P ⊔ (T ⊓ L) ≤ L := sup_le (hPY.trans inf_le_right) inf_le_right
  have hle := burnsideAut_le_of_sylow hS le_sup_right hPSL hPS2
  have hPS : P ≤ T ⊓ L := le_sup_left.trans hle
  have hPeq : P = T ⊓ L := by
    refine Subgroup.eq_of_le_of_card_ge hPS ?_
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj b).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hPeq

end Borel

end CFSG.ASVolI
