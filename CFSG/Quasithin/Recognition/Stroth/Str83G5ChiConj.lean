module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Chi
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ChiCls

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

namespace IsChiEmb

variable {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G} {φ : Coord n}
  {β : G → GaloisField 2 n}

theorem chiLab_eq_cls (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (hS₁ : d₁ ∈ normalizer (S : Set G)) (hS₂ : d₂ ∈ normalizer (S : Set G)) (hCS : ¬ S ≤ C) :
    chiLab ζ d₁ d₂ C S = (cls φ : Set (Coord n)) := by
  refine (h.chiLab_subset_cls hn hζ hS₁ hS₂ hCS).antisymm ?_
  intro ψ hψ
  simp only [cls, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hψ
  obtain ⟨s, -, rfl⟩ := hψ
  exact ⟨_, h.frob hn hζ s⟩

theorem restrict (h : IsChiEmb ζ d₁ d₂ C S φ β) {X : Subgroup G} (hX : X ≤ S) :
    IsChiEmb ζ d₁ d₂ (X ⊓ C) X φ β := by
  refine ⟨fun s hs t ht => h.map_mul s (hX hs) t (hX ht), fun s hs => ?_,
    fun s hs => h.conj₁ s (hX hs), fun s hs => h.conj₂ s (hX hs)⟩
  rw [h.eq_zero_iff s (hX hs), mem_inf]
  exact ⟨fun hc => ⟨hs, hc⟩, fun hc => hc.2⟩

private theorem map_inv (h : IsChiEmb ζ d₁ d₂ C S φ β) {s : G} (hs : s ∈ S) :
    β s⁻¹ = -β s := by
  have h1 := h.map_mul s hs s⁻¹ (S.inv_mem hs)
  rw [mul_inv_cancel, h.map_one] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

private theorem exists_pow_eq_of_orderOf {ω : GaloisField 2 n} (hn : n ≠ 0)
    (hω : orderOf ω = 2 ^ n - 1) {x : GaloisField 2 n} (hx : x ≠ 0) : ∃ k : ℕ, ω ^ k = x := by
  have hN : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [orderOf_eq_zero_iff'.mpr fun k hk => by simp [zero_pow hk.ne']] at hω
    omega
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  set ω' : (GaloisField 2 n)ˣ := Units.mk0 ω hω0
  have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn]
  have hord : orderOf ω' = 2 ^ n - 1 := by
    rw [← orderOf_units, Units.val_mk0, hω]
  have htop : zpowers ω' = ⊤ :=
    eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  have hmem : Units.mk0 x hx ∈ Submonoid.powers ω' :=
    mem_powers_iff_mem_zpowers.mpr (htop ▸ mem_top _)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
  exact ⟨k, by simpa [ω'] using congrArg Units.val hk⟩

theorem isYSimple (h : IsChiEmb ζ d₁ d₂ C S φ β) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (hφ : IsUnit φ.1) {Y : Subgroup G} (hd₁ : d₁ ∈ Y) (hCS : C < S)
    (hSC : S ≤ normalizer (C : Set G)) (hYC : Y ≤ normalizer (C : Set G))
    (hYS : Y ≤ normalizer (S : Set G)) : IsYSimple Y C S := by
  refine ⟨hCS, hSC, hYC, hYS, fun J hCJ hJS _ hYJ => ?_⟩
  by_cases hJ : ∃ j ∈ J, β j ≠ 0
  · right
    obtain ⟨j₀, hj₀, hβj₀⟩ := hJ
    set ω : GaloisField 2 n := ζ ^ φ.1.val
    have hω : orderOf ω = 2 ^ n - 1 := by
      obtain ⟨u, hu⟩ := hφ
      have hcop : Nat.Coprime φ.1.val (2 ^ n - 1) := by
        rw [← hu]
        exact ZMod.val_coe_unit_coprime u
      rw [Nat.Coprime.orderOf_pow (by rw [hζ]; exact hcop.symm), hζ]
    have hpow : ∀ k : ℕ, ∃ j ∈ J, β j = ω ^ k * β j₀ := by
      intro k
      induction k with
      | zero => exact ⟨j₀, hj₀, by rw [pow_zero, one_mul]⟩
      | succ k ih =>
        obtain ⟨j, hj, hβj⟩ := ih
        refine ⟨d₁ * j * d₁⁻¹, (mem_normalizer_iff.mp (hYJ hd₁) j).mp hj, ?_⟩
        rw [h.conj₁ j (hJS hj), hβj, pow_succ]
        ring
    refine le_antisymm hJS fun s hs => ?_
    by_cases hβs : β s = 0
    · exact hCJ ((h.eq_zero_iff s hs).mp hβs)
    · obtain ⟨k, hk⟩ := exists_pow_eq_of_orderOf hn hω (div_ne_zero hβs hβj₀)
      obtain ⟨j, hj, hβj⟩ := hpow k
      have hβj' : β j = β s := by rw [hβj, hk, div_mul_cancel₀ _ hβj₀]
      have h0 : β (j⁻¹ * s) = 0 := by
        rw [h.map_mul _ (S.inv_mem (hJS hj)) _ hs, h.map_inv (hJS hj), hβj', neg_add_cancel]
      have hc : j⁻¹ * s ∈ J := hCJ ((h.eq_zero_iff _ (S.mul_mem (S.inv_mem (hJS hj)) hs)).mp h0)
      have := J.mul_mem hj hc
      rwa [mul_inv_cancel_left] at this
  · left
    push Not at hJ
    exact le_antisymm (fun j hj => (h.eq_zero_iff j (hJS hj)).mp (hJ j hj)) hCJ

end IsChiEmb

theorem chiLab_map_conj {ζ : GaloisField 2 n} {d₁ d₂ : G} {C S : Subgroup G} {φ : Coord n}
    (hφ : φ ∈ chiLab ζ d₁ d₂ C S) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1)
    (hS₁ : d₁ ∈ normalizer (S : Set G)) (hS₂ : d₂ ∈ normalizer (S : Set G)) (hCS : ¬ S ≤ C)
    {g : G} {a b a' b' : ZMod (2 ^ n - 1)} (h₁ : g⁻¹ * d₁ * g = d₁ ^ a.val * d₂ ^ b.val)
    (h₂ : g⁻¹ * d₂ * g = d₁ ^ a'.val * d₂ ^ b'.val) :
    chiLab ζ d₁ d₂ (C.map (MulAut.conj g).toMonoidHom) (S.map (MulAut.conj g).toMonoidHom) =
      (cls (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2) : Set (Coord n)) := by
  obtain ⟨β, hβ⟩ := hφ
  have hN : ∀ {d : G} {a b : ZMod (2 ^ n - 1)}, g⁻¹ * d * g = d₁ ^ a.val * d₂ ^ b.val →
      d ∈ normalizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro d a b hd
    rw [← map_equiv_normalizer_eq S (MulAut.conj g), mem_map_conj_iff, hd]
    exact mul_mem (pow_mem hS₁ _) (pow_mem hS₂ _)
  refine (hβ.conj hn hζ hS₁ hS₂ h₁ h₂).chiLab_eq_cls hn hζ (hN h₁) (hN h₂) fun hle => hCS ?_
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hle

end CFSG.Quasithin.Stroth.G5

end
