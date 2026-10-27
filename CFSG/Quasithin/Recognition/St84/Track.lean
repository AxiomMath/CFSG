module

public import CFSG.Quasithin.Recognition.St84.Hyp

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def lineShift (ℓ : Line Γ) (a : ℤ) : Line Γ where
  vert i := ℓ.vert (i + a)
  adj i := by
    have h := ℓ.adj (i + a)
    rwa [show i + a + 1 = i + 1 + a by omega] at h
  nb i := by
    have h := ℓ.nb (i + a)
    rwa [show i + a + 2 = i + 2 + a by omega] at h

@[simp] theorem lineShift_vert (ℓ : Line Γ) (a i : ℤ) :
    (lineShift ℓ a).vert i = ℓ.vert (i + a) := rfl

@[expose] def trackShift (T : Track Γ G) (a : ℤ) : Track Γ G where
  line := lineShift T.line a
  τ := T.τ
  trans i := by
    rw [lineShift_vert, lineShift_vert]
    rw [show i + 2 + a = i + a + 2 by omega]
    exact T.trans (i + a)

@[simp] theorem trackShift_vert (T : Track Γ G) (a i : ℤ) :
    (trackShift T a).line.vert i = T.line.vert (i + a) := rfl

@[simp] theorem trackShift_τ (T : Track Γ G) (a : ℤ) : (trackShift T a).τ = T.τ := rfl

@[expose] def kTrackOfPair (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {α β : V} {x y : G} (hαβ : Γ.Adj α β) (h : CrossPair α β x y) (K : Subgroup G)
    (hKα : ∀ k ∈ K, k • α = α) (hKβ : ∀ k ∈ K, k • β = β)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    KTrack Γ G :=
  let T₀ := trackOfPair hadj hαβ h
  { line := lineShift T₀.line 1
    τ := y * x
    trans := by
      intro i
      rw [lineShift_vert, lineShift_vert]
      rw [show i + 2 + 1 = i + 1 + 2 by omega]
      exact T₀.trans (i + 1)
    K := K
    K_fix := by
      have hstep : ∀ {g : G}, g ∈ Subgroup.normalizer (K : Set G) → ∀ {v : V},
          (∀ k ∈ K, k • v = v) → ∀ k ∈ K, k • (g • v) = g • v := by
        intro g hg v hv k hk
        have hk' : g⁻¹ * k * g ∈ K := (Subgroup.mem_normalizer_iff''.1 hg k).1 hk
        calc k • (g • v) = (k * g) • v := (mul_smul k g v).symm
          _ = (g * (g⁻¹ * k * g)) • v := by congr 1; group
          _ = g • ((g⁻¹ * k * g) • v) := mul_smul g (g⁻¹ * k * g) v
          _ = g • v := by rw [hv _ hk']
      have hτN : T₀.τ ∈ Subgroup.normalizer (K : Set G) := mul_mem hyK hxK
      have hpow : ∀ m : ℤ, ∀ {v : V}, (∀ k ∈ K, k • v = v) →
          ∀ k ∈ K, k • (T₀.τ ^ m • v) = T₀.τ ^ m • v := by
        intro m v hv
        refine zpow_induction_left (g := T₀.τ)
          (P := fun a => ∀ k ∈ K, k • (a • v) = a • v) ?_ ?_ ?_ m
        · intro k hk
          simpa using hv k hk
        · intro a ha k hk
          simpa [mul_smul] using hstep hτN ha k hk
        · intro a ha k hk
          simpa [mul_smul] using hstep (inv_mem hτN) ha k hk
      have hfix0 : ∀ k ∈ K, k • T₀.line.vert 0 = T₀.line.vert 0 := by
        intro k hk
        rw [trackOfPair_vert_zero hadj hαβ h]
        exact hstep (inv_mem hxK) hKβ k hk
      have hfix1 : ∀ k ∈ K, k • T₀.line.vert 1 = T₀.line.vert 1 := by
        intro k hk
        rw [trackOfPair_vert_one hadj hαβ h]
        exact hKα k hk
      intro k hk i
      show k • (lineShift T₀.line 1).vert i = (lineShift T₀.line 1).vert i
      rw [lineShift_vert]
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (i + 1)
      · rw [hm, show 2 * m = 0 + 2 * m by omega, ← Track.zpow_smul_vert T₀ m 0]
        exact hpow m hfix0 k hk
      · rw [hm, show 2 * m + 1 = 1 + 2 * m by omega, ← Track.zpow_smul_vert T₀ m 1]
        exact hpow m hfix1 k hk
    τ_norm := mul_mem hyK hxK }

section KPair

variable (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) {α β : V} {x y : G}
  (hαβ : Γ.Adj α β) (h : CrossPair α β x y) (K : Subgroup G)
  (hKα : ∀ k ∈ K, k • α = α) (hKβ : ∀ k ∈ K, k • β = β)
  (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hyK : y ∈ Subgroup.normalizer (K : Set G))

@[simp] theorem kTrackOfPair_K :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).K = K := rfl

@[simp] theorem kTrackOfPair_τ :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).τ = y * x := rfl

@[simp] theorem kTrackOfPair_line :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).line =
      lineShift (trackOfPair hadj hαβ h).line 1 := rfl

@[simp] theorem kTrackOfPair_vert (i : ℤ) :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).line.vert i =
      (trackOfPair hadj hαβ h).line.vert (i + 1) := by
  rw [kTrackOfPair_line, lineShift_vert]

@[simp] theorem kTrackOfPair_vert_zero :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).line.vert 0 = α := by
  have h0 := kTrackOfPair_vert hadj hαβ h K hKα hKβ hxK hyK (0 : ℤ)
  rw [show (0 : ℤ) + 1 = 1 by omega] at h0
  rw [h0, trackOfPair_vert_one hadj hαβ h]

@[simp] theorem kTrackOfPair_vert_one :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).line.vert 1 = β := by
  have h1 := kTrackOfPair_vert hadj hαβ h K hKα hKβ hxK hyK (1 : ℤ)
  rw [show (1 : ℤ) + 1 = 2 by omega] at h1
  rw [h1, trackOfPair_vert_two hadj hαβ h]

@[simp] theorem kTrackOfPair_vert_neg_one :
    (kTrackOfPair hadj hαβ h K hKα hKβ hxK hyK).line.vert (-1) = x⁻¹ • β := by
  have hm := kTrackOfPair_vert hadj hαβ h K hKα hKβ hxK hyK (-1 : ℤ)
  rw [show (-1 : ℤ) + 1 = 0 by omega] at hm
  rw [hm, trackOfPair_vert_zero hadj hαβ h]

end KPair

theorem exists_kTrack (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {α β : V} (hαβ : Γ.Adj α β) {K : Subgroup G} (hKα : ∀ k ∈ K, k • α = α)
    (hKβ : ∀ k ∈ K, k • β = β) {x y : G} (hx : CrossPair α β x y)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ T : KTrack Γ G, T.K = K ∧ T.τ = y * x ∧ T.line.vert 0 = α ∧ T.line.vert 1 = β :=
  ⟨kTrackOfPair hadj hαβ hx K hKα hKβ hxK hyK,
    kTrackOfPair_K hadj hαβ hx K hKα hKβ hxK hyK,
    kTrackOfPair_τ hadj hαβ hx K hKα hKβ hxK hyK,
    kTrackOfPair_vert_zero hadj hαβ hx K hKα hKβ hxK hyK,
    kTrackOfPair_vert_one hadj hαβ hx K hKα hKβ hxK hyK⟩

theorem fixSet_convex (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (T : Track Γ G) (U : Subgroup G) {i j k : ℤ} (hi : i ∈ T.fixSet U)
    (hj : j ∈ T.fixSet U) (hik : i ≤ k) (hkj : k ≤ j) : k ∈ T.fixSet U := by
  intro g hg
  exact Line.fixes_between hT hadj T.line hik hkj (hi g hg) (hj g hg)

theorem fixSet_trichotomy (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) (T : Track Γ G) (U : Subgroup G) :
    T.fixSet U = Set.univ ∨ T.fixSet U = ∅ ∨ ∃ a b : ℤ, a ≤ b ∧ T.fixSet U = Set.Icc a b := by
  rcases T.fixSet_eq_univ_or_bounded hT hadj hfin U with huniv | ⟨a, b, hb⟩
  · exact Or.inl huniv
  · by_cases hempty : T.fixSet U = ∅
    · exact Or.inr (Or.inl hempty)
    · right
      right
      obtain ⟨i₀, hi₀⟩ := Set.nonempty_iff_ne_empty.2 hempty
      obtain ⟨c, hc, hcle⟩ :=
        Int.exists_least_of_bdd (P := fun z => z ∈ T.fixSet U)
          ⟨a, fun z hz => (hb z hz).1⟩ ⟨i₀, hi₀⟩
      obtain ⟨d, hd, hdle⟩ :=
        Int.exists_greatest_of_bdd (P := fun z => z ∈ T.fixSet U)
          ⟨b, fun z hz => (hb z hz).2⟩ ⟨i₀, hi₀⟩
      refine ⟨c, d, hcle d hd, ?_⟩
      ext i
      constructor
      · intro hi
        exact ⟨hcle i hi, hdle i hi⟩
      · rintro ⟨hci, hid⟩
        exact fixSet_convex hT hadj T U hc hd hci hid

end CFSG.Quasithin.St84
