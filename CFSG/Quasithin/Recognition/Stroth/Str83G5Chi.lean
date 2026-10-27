module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Defs


public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

private theorem map_conj_map_conj_inv (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
  ext y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  simp [mul_assoc]

private theorem normalizer_map_conj (K : Subgroup G) (g : G) :
    normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (normalizer (K : Set G)).map (MulAut.conj g).toMonoidHom :=
  (map_equiv_normalizer_eq K (MulAut.conj g)).symm

private theorem map_conj_eq_of_mem_normalizer {Y : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Y : Set G)) : Y.map (MulAut.conj g).toMonoidHom = Y :=
  mem_normalizer_iff_map_conj_eq.mp hg

theorem isYSimple_map_conj {Y C S : Subgroup G} {g : G} (h : IsYSimple Y C S)
    (hg : g ∈ normalizer (Y : Set G)) :
    IsYSimple Y (C.map (MulAut.conj g).toMonoidHom) (S.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hlt, hSC, hYC, hYS, hmax⟩ := h
  have hinj := (MulAut.conj g).injective
  have hY := map_conj_eq_of_mem_normalizer hg
  have hY' := map_conj_eq_of_mem_normalizer (inv_mem hg)
  refine ⟨(map_lt_map_iff_of_injective hinj).mpr hlt, ?_, ?_, ?_, fun J hCJ hJS hSJ hYJ => ?_⟩
  · rw [normalizer_map_conj]
    exact map_mono hSC
  · rw [normalizer_map_conj, ← hY]
    exact map_mono hYC
  · rw [normalizer_map_conj, ← hY]
    exact map_mono hYS
  · set J' := J.map (MulAut.conj g⁻¹).toMonoidHom
    have hJ : J'.map (MulAut.conj g).toMonoidHom = J := map_conj_map_conj_inv J g
    have hback : ∀ K : Subgroup G,
        (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := fun K => by
      simpa using map_conj_map_conj_inv K g⁻¹
    have h1 : C ≤ J' := by
      rw [← hback C]
      exact map_mono hCJ
    have h2 : J' ≤ S := by
      rw [← hback S]
      exact map_mono hJS
    have h3 : S ≤ normalizer (J' : Set G) := by
      rw [normalizer_map_conj, ← hback S]
      exact map_mono hSJ
    have h4 : Y ≤ normalizer (J' : Set G) := by
      rw [normalizer_map_conj, ← hY']
      exact map_mono hYJ
    rcases hmax J' h1 h2 h3 h4 with h5 | h5
    · left
      rw [← hJ, h5]
    · right
      rw [← hJ, h5]

theorem isYSeries_map_conj {Y C : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) :
    ∀ {l : List (Subgroup G)} {D : Subgroup G}, IsYSeries Y C l D →
      IsYSeries Y (C.map (MulAut.conj g).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
  | [], D, h => by
    have hCD : C = D := h
    subst hCD
    exact rfl
  | S :: l, _, h => ⟨isYSimple_map_conj h.1 hg, isYSeries_map_conj hg h.2⟩

theorem facMultiset_map_conj {β : Type} (f : Subgroup G → Subgroup G → β) (g : G) :
    ∀ (l : List (Subgroup G)) (D : Subgroup G),
      facMultiset f (l.map fun T => T.map (MulAut.conj g).toMonoidHom)
          (D.map (MulAut.conj g).toMonoidHom) =
        facMultiset (fun C S => f (C.map (MulAut.conj g).toMonoidHom)
          (S.map (MulAut.conj g).toMonoidHom)) l D
  | [], _ => rfl
  | S :: l, D => by
    simp only [List.map_cons, facMultiset]
    rw [facMultiset_map_conj f g l S]

theorem chiLab_eq_inf {Y S S' D : Subgroup G} {ζ : GaloisField 2 n} {d₁ d₂ : G}
    (hd₁ : d₁ ∈ Y) (hd₂ : d₂ ∈ Y) (h : IsYSimple Y S D) (h' : IsYSimple Y S' D)
    (hne : S ≠ S') : chiLab ζ d₁ d₂ S D = chiLab ζ d₁ d₂ (S ⊓ S') S' := by
  classical
  have hS'D : S' ≤ D := h'.1.le
  have hDS : D ≤ normalizer (S : Set G) := h.2.1
  have hS'S : S' ≤ normalizer (S : Set G) := hS'D.trans hDS
  have hsup : S' ⊔ S = D := by rw [sup_comm]; exact h.sup_eq h' hne
  have hmul : ∀ x ∈ D, ∃ s' ∈ S', ∃ s ∈ S, x = s' * s := by
    intro x hx
    have hx' : x ∈ ((S' ⊔ S : Subgroup G) : Set G) := by rw [hsup]; exact hx
    rw [coe_mul_of_left_le_normalizer_right S' S hS'S] at hx'
    obtain ⟨s', hs', s, hs, rfl⟩ := hx'
    exact ⟨s', hs', s, hs, rfl⟩
  have hconj : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S := fun y hy s hs =>
    (mem_normalizer_iff.mp (h.2.2.1 hy) s).mp hs
  have hconj' : ∀ y ∈ Y, ∀ s ∈ S', y * s * y⁻¹ ∈ S' := fun y hy s hs =>
    (mem_normalizer_iff.mp (h'.2.2.1 hy) s).mp hs
  ext φ
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨β, fun s hs t ht => hβ.map_mul s (hS'D hs) t (hS'D ht), fun s hs => ?_,
      fun s hs => hβ.conj₁ s (hS'D hs), fun s hs => hβ.conj₂ s (hS'D hs)⟩
    rw [hβ.eq_zero_iff s (hS'D hs), mem_inf]
    exact ⟨fun h1 => ⟨h1, hs⟩, fun h1 => h1.1⟩
  · rintro ⟨β', hβ'⟩
    let β : G → GaloisField 2 n := fun x =>
      if hx : ∃ s' ∈ S', ∃ s ∈ S, x = s' * s then β' hx.choose else 0
    have hwd : ∀ s' ∈ S', ∀ s ∈ S, β (s' * s) = β' s' := by
      intro s' hs' s hs
      have hx : ∃ u ∈ S', ∃ v ∈ S, s' * s = u * v := ⟨s', hs', s, hs, rfl⟩
      simp only [β, dif_pos hx]
      obtain ⟨hc', t, ht, hct⟩ := hx.choose_spec
      have hmem : hx.choose⁻¹ * s' ∈ S ⊓ S' := by
        refine ⟨?_, S'.mul_mem (S'.inv_mem hc') hs'⟩
        have : hx.choose⁻¹ * s' = t * s⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hct, mul_inv_cancel_right]
        rw [this]
        exact S.mul_mem ht (S.inv_mem hs)
      have h0 := (hβ'.eq_zero_iff _ (S'.mul_mem (S'.inv_mem hc') hs')).mpr hmem
      have h1 := hβ'.map_mul hx.choose hc' (hx.choose⁻¹ * s') (S'.mul_mem (S'.inv_mem hc') hs')
      rw [mul_inv_cancel_left, h0, add_zero] at h1
      exact h1.symm
    refine ⟨β, ⟨fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩⟩
    · obtain ⟨s₁', hs₁', s₁, hs₁, rfl⟩ := hmul x hx
      obtain ⟨s₂', hs₂', s₂, hs₂, rfl⟩ := hmul y hy
      have e : s₁' * s₁ * (s₂' * s₂) = s₁' * s₂' * (s₂'⁻¹ * s₁ * s₂' * s₂) := by group
      have hmem : s₂'⁻¹ * s₁ * s₂' * s₂ ∈ S := by
        refine S.mul_mem ?_ hs₂
        have := (mem_normalizer_iff.mp (hS'S (S'.inv_mem hs₂')) s₁).mp hs₁
        simpa using this
      rw [e, hwd _ (S'.mul_mem hs₁' hs₂') _ hmem, hwd _ hs₁' _ hs₁, hwd _ hs₂' _ hs₂,
        hβ'.map_mul _ hs₁' _ hs₂']
    · obtain ⟨s', hs', s, hs, rfl⟩ := hmul x hx
      rw [hwd _ hs' _ hs, hβ'.eq_zero_iff _ hs', mem_inf]
      refine ⟨fun h1 => S.mul_mem h1.1 hs, fun h1 => ⟨?_, hs'⟩⟩
      have := S.mul_mem h1 (S.inv_mem hs)
      rwa [mul_inv_cancel_right] at this
    · obtain ⟨s', hs', s, hs, rfl⟩ := hmul x hx
      have e : d₁ * (s' * s) * d₁⁻¹ = d₁ * s' * d₁⁻¹ * (d₁ * s * d₁⁻¹) := by group
      rw [e, hwd _ (hconj' d₁ hd₁ s' hs') _ (hconj d₁ hd₁ s hs), hwd _ hs' _ hs,
        hβ'.conj₁ _ hs']
    · obtain ⟨s', hs', s, hs, rfl⟩ := hmul x hx
      have e : d₂ * (s' * s) * d₂⁻¹ = d₂ * s' * d₂⁻¹ * (d₂ * s * d₂⁻¹) := by group
      rw [e, hwd _ (hconj' d₂ hd₂ s' hs') _ (hconj d₂ hd₂ s hs), hwd _ hs' _ hs,
        hβ'.conj₂ _ hs']

theorem pow_eq_pow_of_natCast_eq {ζ : GaloisField 2 n} (hζ : orderOf ζ = 2 ^ n - 1) {m₁ m₂ : ℕ}
    (h : (m₁ : ZMod (2 ^ n - 1)) = (m₂ : ZMod (2 ^ n - 1))) : ζ ^ m₁ = ζ ^ m₂ := by
  rw [← pow_mod_orderOf ζ m₁, ← pow_mod_orderOf ζ m₂, hζ]
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [h]

namespace IsChiEmb

variable {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G} {φ : Coord n}
  {β : G → GaloisField 2 n}

theorem map_one (h : IsChiEmb ζ d₁ d₂ C S φ β) : β 1 = 0 := by
  have := h.map_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at this
  exact left_eq_add.mp this

theorem conj₁_pow (h : IsChiEmb ζ d₁ d₂ C S φ β) (hS₁ : d₁ ∈ normalizer (S : Set G)) (k : ℕ) :
    ∀ s ∈ S, d₁ ^ k * s * (d₁ ^ k)⁻¹ ∈ S ∧
      β (d₁ ^ k * s * (d₁ ^ k)⁻¹) = (ζ ^ φ.1.val) ^ k * β s := by
  induction k with
  | zero => intro s hs; simpa using hs
  | succ k ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := ih s hs
    have e : d₁ ^ (k + 1) * s * (d₁ ^ (k + 1))⁻¹ = d₁ * (d₁ ^ k * s * (d₁ ^ k)⁻¹) * d₁⁻¹ := by
      group
    rw [e]
    refine ⟨(mem_normalizer_iff.mp hS₁ _).mp h1, ?_⟩
    rw [h.conj₁ _ h1, h2, pow_succ]
    ring

theorem conj₂_pow (h : IsChiEmb ζ d₁ d₂ C S φ β) (hS₂ : d₂ ∈ normalizer (S : Set G)) (k : ℕ) :
    ∀ s ∈ S, d₂ ^ k * s * (d₂ ^ k)⁻¹ ∈ S ∧
      β (d₂ ^ k * s * (d₂ ^ k)⁻¹) = (ζ ^ φ.2.val) ^ k * β s := by
  induction k with
  | zero => intro s hs; simpa using hs
  | succ k ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := ih s hs
    have e : d₂ ^ (k + 1) * s * (d₂ ^ (k + 1))⁻¹ = d₂ * (d₂ ^ k * s * (d₂ ^ k)⁻¹) * d₂⁻¹ := by
      group
    rw [e]
    refine ⟨(mem_normalizer_iff.mp hS₂ _).mp h1, ?_⟩
    rw [h.conj₂ _ h1, h2, pow_succ]
    ring

theorem conj_mul_pow (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (hS₁ : d₁ ∈ normalizer (S : Set G)) (hS₂ : d₂ ∈ normalizer (S : Set G))
    (a b : ZMod (2 ^ n - 1)) :
    ∀ s ∈ S, (d₁ ^ a.val * d₂ ^ b.val) * s * (d₁ ^ a.val * d₂ ^ b.val)⁻¹ ∈ S ∧
      β ((d₁ ^ a.val * d₂ ^ b.val) * s * (d₁ ^ a.val * d₂ ^ b.val)⁻¹) =
        ζ ^ (a * φ.1 + b * φ.2).val * β s := by
  intro s hs
  have : NeZero (2 ^ n - 1) := ⟨by have := Nat.one_lt_two_pow hn; omega⟩
  obtain ⟨h1, h2⟩ := h.conj₂_pow hS₂ b.val s hs
  obtain ⟨h3, h4⟩ := h.conj₁_pow hS₁ a.val _ h1
  have e : (d₁ ^ a.val * d₂ ^ b.val) * s * (d₁ ^ a.val * d₂ ^ b.val)⁻¹ =
      d₁ ^ a.val * (d₂ ^ b.val * s * (d₂ ^ b.val)⁻¹) * (d₁ ^ a.val)⁻¹ := by group
  rw [e]
  refine ⟨h3, ?_⟩
  rw [h4, h2, ← mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  apply pow_eq_pow_of_natCast_eq hζ
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  ring

theorem conj (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (hS₁ : d₁ ∈ normalizer (S : Set G)) (hS₂ : d₂ ∈ normalizer (S : Set G)) {g : G}
    {a b a' b' : ZMod (2 ^ n - 1)} (h₁ : g⁻¹ * d₁ * g = d₁ ^ a.val * d₂ ^ b.val)
    (h₂ : g⁻¹ * d₂ * g = d₁ ^ a'.val * d₂ ^ b'.val) :
    IsChiEmb ζ d₁ d₂ (C.map (MulAut.conj g).toMonoidHom) (S.map (MulAut.conj g).toMonoidHom)
      (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2) fun s => β (g⁻¹ * s * g) := by
  have key : ∀ (d : G) (e : G), g⁻¹ * d * g = e → ∀ s : G,
      g⁻¹ * (d * s * d⁻¹) * g = e * (g⁻¹ * s * g) * e⁻¹ := by
    rintro d e rfl s
    group
  refine ⟨fun s hs t ht => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · rw [mem_map_conj_iff] at hs ht
    have e : g⁻¹ * (s * t) * g = g⁻¹ * s * g * (g⁻¹ * t * g) := by group
    rw [e, h.map_mul _ hs _ ht]
  · rw [mem_map_conj_iff] at hs
    rw [h.eq_zero_iff _ hs, mem_map_conj_iff]
  · rw [mem_map_conj_iff] at hs
    simp only
    rw [key d₁ _ h₁ s]
    exact (h.conj_mul_pow hn hζ hS₁ hS₂ a b _ hs).2
  · rw [mem_map_conj_iff] at hs
    simp only
    rw [key d₂ _ h₂ s]
    exact (h.conj_mul_pow hn hζ hS₁ hS₂ a' b' _ hs).2

theorem frob (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (s : ℕ) :
    IsChiEmb ζ d₁ d₂ C S (((2 : ZMod (2 ^ n - 1)) ^ s) • φ) fun g => β g ^ 2 ^ s := by
  have : NeZero (2 ^ n - 1) := ⟨by have := Nat.one_lt_two_pow hn; omega⟩
  have hcast : ∀ x : ZMod (2 ^ n - 1),
      (((2 : ZMod (2 ^ n - 1)) ^ s * x).val : ZMod (2 ^ n - 1)) = ((x.val * 2 ^ s : ℕ) :
        ZMod (2 ^ n - 1)) := by
    intro x
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [h.map_mul x hx y hy, add_pow_char_pow]
  · rw [pow_eq_zero_iff (pow_ne_zero _ two_ne_zero), h.eq_zero_iff x hx]
  · simp only [Prod.smul_fst, smul_eq_mul]
    rw [h.conj₁ x hx, mul_pow, ← pow_mul, pow_eq_pow_of_natCast_eq hζ (hcast φ.1)]
  · simp only [Prod.smul_snd, smul_eq_mul]
    rw [h.conj₂ x hx, mul_pow, ← pow_mul, pow_eq_pow_of_natCast_eq hζ (hcast φ.2)]

end IsChiEmb

end CFSG.Quasithin.Stroth.G5

end
