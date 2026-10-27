module

public import CFSG.Quasithin.EmptyFaithful.S146F9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section V4

variable {Γ : Type*} [Group Γ]

theorem v4_conj_cases {W : Subgroup Γ} (hW : Nat.card W = 4) (hexp : ∀ y ∈ W, y * y = 1) {x : Γ}
    (hx : x ∈ Subgroup.normalizer (W : Set Γ)) (h3 : x ^ 3 = 1) (hnc : ∃ y ∈ W, x * y * x⁻¹ ≠ y)
    {a b : Γ} (ha : a ∈ W) (ha1 : a ≠ 1) (hb : b ∈ W) (hb1 : b ≠ 1) :
    b = a ∨ b = x * a * x⁻¹ ∨ b = x⁻¹ * a * x := by
  have hx3 : x * (x * x) = 1 := by
    calc x * (x * x) = x ^ 3 := (pow_three x).symm
      _ = 1 := h3
  have hnfix : ∀ c ∈ W, c ≠ 1 → x * c * x⁻¹ ≠ c := fun c hc hc1 hfix => by
    obtain ⟨y, hyW, hy⟩ := hnc
    exact hy (v4_centralizes hW hexp hx h3 hc hc1 hfix y hyW)
  have hxi : x⁻¹ ∈ Subgroup.normalizer (W : Set Γ) := Subgroup.inv_mem _ hx
  have hy : x * a * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hx a).mp ha
  have hc : x⁻¹ * a * x ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp hxi a).mp ha
    simpa using this
  have hy1 : x * a * x⁻¹ ≠ 1 := fun h => ha1 (by
    have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
    rw [this, h]; group)
  have hya : x * a * x⁻¹ ≠ a := hnfix a ha ha1
  rcases v4_mem_four hW hexp ha hy ha1 hy1 hya b hb with h | h | h | h
  · exact absurd h hb1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right
    right
    rw [h]
    have hc1 : x⁻¹ * a * x ≠ 1 := fun h' => ha1 (by
      have : a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      rw [this, h']; group)
    have hca : x⁻¹ * a * x ≠ a := by
      intro hca
      apply hya
      calc x * a * x⁻¹ = x * (x⁻¹ * a * x) * x⁻¹ := by rw [hca]
        _ = a := by group
    have hcy : x⁻¹ * a * x ≠ x * a * x⁻¹ := by
      intro hcy
      apply hya
      have E1 : a = (x * x) * a * (x * x)⁻¹ := by
        calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
          _ = x * (x * a * x⁻¹) * x⁻¹ := by rw [hcy]
          _ = (x * x) * a * (x * x)⁻¹ := by group
      calc x * a * x⁻¹ = x * ((x * x) * a * (x * x)⁻¹) * x⁻¹ := by rw [← E1]
        _ = (x * (x * x)) * a * (x * (x * x))⁻¹ := by group
        _ = a := by rw [hx3]; group
    rcases v4_mem_four hW hexp ha hy ha1 hy1 hya _ hc with h' | h' | h' | h'
    · exact absurd h' hc1
    · exact absurd h' hca
    · exact absurd h' hcy
    · exact h'.symm

end V4

section Transfer

variable {G : Type} [Group G]

theorem Sec4.conj_cases {Z U₁ : Subgroup G} {x : G} (h : Sec4 Z U₁ x) {a b : G} (ha : a ∈ U₁)
    (haZ : a ∉ Z) (hb : b ∈ U₁) (hbZ : b ∉ Z) :
    a⁻¹ * b ∈ Z ∨ (x * a * x⁻¹)⁻¹ * b ∈ Z ∨ (x⁻¹ * a * x)⁻¹ * b ∈ Z := by
  have hW := h.card_tilde
  have hexp := h.exp_tilde
  have hxW := h.mem_normalizer_tilde
  have h3 := h.pow_three_tilde
  have hnc : ∃ y ∈ tildeOf Z U₁, secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ * y *
      (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩)⁻¹ ≠ y := by
    obtain ⟨y, hy, hyc⟩ := h.nc
    refine ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨y, h.norm hy⟩,
      secMk_mem_secImg (x := ⟨y, h.norm hy⟩) hy, fun heq => hyc ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at heq
    exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (Z : Set G)) (B := Z)
      (x := ⟨x, h.xZ⟩) (y := ⟨y, h.norm hy⟩) heq
  have haW : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ ∈ tildeOf Z U₁ :=
    secMk_mem_secImg (x := ⟨a, h.norm ha⟩) ha
  have hbW : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨b, h.norm hb⟩ ∈ tildeOf Z U₁ :=
    secMk_mem_secImg (x := ⟨b, h.norm hb⟩) hb
  have ha1 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ ≠ 1 := fun h1 =>
    haZ (secMk_eq_one_iff.mp h1)
  have hb1 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨b, h.norm hb⟩ ≠ 1 := fun h1 =>
    hbZ (secMk_eq_one_iff.mp h1)
  have key := v4_conj_cases hW hexp hxW h3 hnc haW ha1 hbW hb1
  have hxN : x ∈ Subgroup.normalizer (Z : Set G) := h.xZ
  have haN : a ∈ Subgroup.normalizer (Z : Set G) := h.norm ha
  rcases key with h1 | h1 | h1
  · left
    exact secMk_eq_secMk_iff.mp h1.symm
  · right
    left
    have e : secMk (Subgroup.normalizer (Z : Set G)) Z
        ((⟨x, hxN⟩ : Subgroup.normalizer (Z : Set G)) * ⟨a, haN⟩ * (⟨x, hxN⟩ :
          Subgroup.normalizer (Z : Set G))⁻¹) =
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ *
          secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ *
            (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩)⁻¹ := by
      simp only [map_mul, map_inv]
    have := secMk_eq_secMk_iff.mp (e.trans h1.symm)
    simpa using this
  · right
    right
    have e : secMk (Subgroup.normalizer (Z : Set G)) Z
        ((⟨x, hxN⟩ : Subgroup.normalizer (Z : Set G))⁻¹ * ⟨a, haN⟩ * ⟨x, hxN⟩) =
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩)⁻¹ *
          secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, h.norm ha⟩ *
            secMk (Subgroup.normalizer (Z : Set G)) Z ⟨x, h.xZ⟩ := by
      simp only [map_mul, map_inv]
    have := secMk_eq_secMk_iff.mp (e.trans h1.symm)
    simpa using this

end Transfer

section Orbit

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem tZero_le_tZero_of_mod {u v : G} (hv : v ∈ mcOf T) (hu : u ∈ mcOf T)
    (h : v⁻¹ * u ∈ quasithinOmegaOneCenter T) : tZero T u ≤ tZero T v := by
  intro x hx
  obtain ⟨hxT, hc⟩ := (S146T.mem_tZero_iff hu).mp hx
  refine (S146T.mem_tZero_iff hv).mpr ⟨hxT, ?_⟩
  have hζ : v⁻¹ * u ∈ quasithinOmegaOneCenter T := h
  have h1 : x * (v⁻¹ * u) = (v⁻¹ * u) * x := S146T.comm_Z_T hxT hζ
  have h2 : x⁻¹ * (v⁻¹ * u) = (v⁻¹ * u) * x⁻¹ := S146T.comm_Z_T (T.inv_mem hxT) hζ
  have e : ⁅x, u⁆ = ⁅x, v⁆ := by
    simp only [commutatorElement_def]
    have hu' : u = v * (v⁻¹ * u) := by group
    set ζ := v⁻¹ * u with hζdef
    rw [hu']
    calc x * (v * ζ) * x⁻¹ * (v * ζ)⁻¹ = x * v * (ζ * x⁻¹) * (ζ⁻¹ * v⁻¹) := by group
      _ = x * v * (x⁻¹ * ζ) * (ζ⁻¹ * v⁻¹) := by rw [h2]
      _ = x * v * x⁻¹ * v⁻¹ := by group
  rw [← e]
  exact hc

theorem IsDec12.exists_fixed_vector (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    ∃ u₁ ∈ uHi T M H H₁, u₁ ∉ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u₁ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := le_normalizer_conjClosure _ _
  have hUQ := S.conjClosure_le_pCoreOf hH
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hH
  have huHi_le : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hUH₁ : conjClosure (VZ T M) H ≤ H₁ := hUQ.trans h.Q₁
  have hT₀2 : IsPGroup 2 (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) :=
    hT2.to_le inf_le_left
  have hT₀N₁ : (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) ≤
      Subgroup.normalizer (H₁ : Set G) := inf_le_right
  have hT₀NU : (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) ≤
      Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := (inf_le_left.trans hTH).trans hHU
  have hT₀NZ : (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hx.1)
  have hT₀Nuhi : (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) ≤
      Subgroup.normalizer (uHi T M H H₁ : Set G) :=
    (le_inf (S145.le_normalizer_commutator hT₀NU hT₀N₁) hT₀NZ).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have huhiT₀ : uHi T M H H₁ ≤ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) :=
    le_inf ((huHi_le.trans hUQ).trans hQT) ((huHi_le.trans hUH₁).trans Subgroup.le_normalizer)
  have hlt : quasithinOmegaOneCenter T < uHi T M H H₁ := by
    refine lt_of_le_of_ne le_sup_right fun heq => ?_
    have hr := h.rank₁.2 hp3
    have h0 : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 0 := by
      rw [← heq]
      simp [mIdx]
    omega
  obtain ⟨u₁, hu₁, hu₁Z, hfix⟩ := exists_fixed_mod hT₀2 huhiT₀ hlt hT₀Nuhi hT₀NZ
  have hu₁G : u₁ ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH (huHi_le hu₁)
  exact ⟨u₁, hu₁, hu₁Z, fun x hx => (S146T.mem_tZero_iff hu₁G).mpr ⟨hx.1, hfix x hx⟩⟩

theorem IsDec12.exists_conj_fixed (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hp3 : p = 3) (hOF : IsOFourPlusOn T M H) (h : IsDec12 T M H p H₀ H₁ H₂ t) {w : G}
    (hw : w ∈ uHi T M H H₁) (hwZ : w ∉ quasithinOmegaOneCenter T) :
    ∃ y ∈ H₁, T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T (y * w * y⁻¹) := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  obtain ⟨u₁, hu₁, hu₁Z, hu₁T⟩ := h.exists_fixed_vector S hred hp3
  have hu₁G : u₁ ∈ mcOf T :=
    S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure hH₁H hu₁)
  have hdec3 : IsDec12 T M H 3 H₀ H₁ H₂ t := hp3 ▸ h
  obtain ⟨x, hxH₁, hxQ, -, hx3⟩ := hdec3.exists_odd_three
  have hSec := h.sec4 S hred hp3 hOF hxH₁ hxQ hx3
  have hN₁ : H₁ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) := h.le_normalizer_uHi S hred
  have key : ∀ y ∈ H₁, (y * w * y⁻¹)⁻¹ * u₁ ∈ quasithinOmegaOneCenter T →
      T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T (y * w * y⁻¹) := fun y hy hmod => by
    have hv : y * w * y⁻¹ ∈ uHi T M H H₁ := (Subgroup.mem_normalizer_iff.mp (hN₁ hy) w).mp hw
    have hvG : y * w * y⁻¹ ∈ mcOf T :=
      S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure hH₁H hv)
    exact hu₁T.trans (tZero_le_tZero_of_mod hvG hu₁G hmod)
  rcases hSec.conj_cases hw hwZ hu₁ hu₁Z with h1 | h1 | h1
  · refine ⟨1, H₁.one_mem, key 1 H₁.one_mem ?_⟩
    simpa using h1
  · exact ⟨x, hxH₁, key x hxH₁ h1⟩
  · refine ⟨x⁻¹, H₁.inv_mem hxH₁, key x⁻¹ (H₁.inv_mem hxH₁) ?_⟩
    simpa using h1

theorem input14617Orbit_proved : Input14617Orbit := by
  intro G _ _ T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec w hw hwZ
  exact hdec.exists_conj_fixed S hred hp3 hOF hw hwZ

end Orbit

section Trans

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem mul_inv_mem_Z_of_inv_mul_mem {a b : G} (ha : a ∈ mcOf T)
    (h : a⁻¹ * b ∈ quasithinOmegaOneCenter T) : a * b⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hc : a * (a⁻¹ * b)⁻¹ = (a⁻¹ * b)⁻¹ * a :=
    S146T.comm_Z ha ((quasithinOmegaOneCenter T).inv_mem h)
  have e : a * b⁻¹ = (a⁻¹ * b)⁻¹ := by
    calc a * b⁻¹ = a * (a⁻¹ * b)⁻¹ * a⁻¹ := by group
      _ = (a⁻¹ * b)⁻¹ * a * a⁻¹ := by rw [hc]
      _ = (a⁻¹ * b)⁻¹ := by group
  rw [e]
  exact (quasithinOmegaOneCenter T).inv_mem h

theorem IsDec12.exists_conj_mod_one (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u u' : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) (hu' : u' ∈ uHi T M H H₁)
    (hu'Z : u' ∉ quasithinOmegaOneCenter T) :
    ∃ c ∈ H₁, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hdec3 : IsDec12 T M H 3 H₀ H₁ H₂ t := hp3 ▸ h
  obtain ⟨x, hxH₁, hxQ, -, hx3⟩ := hdec3.exists_odd_three
  have hSec := h.sec4 S hred hp3 hOF hxH₁ hxQ hx3
  have huG : u ∈ mcOf T :=
    S.mem_mcOf_of_mem_conjClosure hH (uHi_le_conjClosure hH₁H hu)
  have hxG : x ∈ mcOf T := S.le_mcOf hH (hH₁H hxH₁)
  rcases hSec.conj_cases hu huZ hu' hu'Z with h1 | h1 | h1
  · refine ⟨1, H₁.one_mem, ?_⟩
    have := mul_inv_mem_Z_of_inv_mul_mem huG h1
    simpa using this
  · refine ⟨x, hxH₁, ?_⟩
    have hxuG : x * u * x⁻¹ ∈ mcOf T :=
      (mcOf T).mul_mem ((mcOf T).mul_mem hxG huG) ((mcOf T).inv_mem hxG)
    exact mul_inv_mem_Z_of_inv_mul_mem hxuG h1
  · refine ⟨x⁻¹, H₁.inv_mem hxH₁, ?_⟩
    have hxuG : x⁻¹ * u * x ∈ mcOf T :=
      (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem hxG) huG) hxG
    have := mul_inv_mem_Z_of_inv_mul_mem hxuG h1
    simpa using this

theorem IsDec12.exists_conj_mod_mixed (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u u' : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) (hu' : u' ∈ uHi T M H H₂)
    (hu'Z : u' ∉ quasithinOmegaOneCenter T) :
    ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hu'' : t⁻¹ * u' * t ∈ uHi T M H H₁ := by
    have : u' ∈ conjSub t (uHi T M H H₁) := by
      rw [h.conjSub_uHi hred]
      exact hu'
    exact mem_conjSub.mp this
  have hu''Z : t⁻¹ * u' * t ∉ quasithinOmegaOneCenter T := by
    intro hz
    apply hu'Z
    have hcom : t * (t⁻¹ * u' * t) = (t⁻¹ * u' * t) * t := S146T.comm_Z_T h.t_mem hz
    have e : u' = t * (t⁻¹ * u' * t) * t⁻¹ := by group
    rw [e, hcom]
    simpa [mul_assoc] using hz
  obtain ⟨c₁, hc₁H₁, hc₁⟩ := h.exists_conj_mod_one S hred hp3 hOF hu huZ hu'' hu''Z
  refine ⟨t * c₁, H.mul_mem (hTH h.t_mem) (hH₁H hc₁H₁), ?_⟩
  set ζ := c₁ * u * c₁⁻¹ * (t⁻¹ * u' * t)⁻¹ with hζ
  have hcom : t * ζ = ζ * t := S146T.comm_Z_T h.t_mem hc₁
  have e : t * c₁ * u * (t * c₁)⁻¹ * u'⁻¹ = t * ζ * t⁻¹ := by
    rw [hζ]
    group
  rw [e, hcom]
  have : ζ * t * t⁻¹ = ζ := by group
  rw [mul_assoc, mul_inv_cancel, mul_one]
  exact hc₁

theorem IsDec12.exists_conj_mod (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u u' : G}
    (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (hu' : u' ∈ uHi T M H H₁ ∨ u' ∈ uHi T M H H₂) (hu'Z : u' ∉ quasithinOmegaOneCenter T) :
    ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T := by
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  rcases hu with hu | hu <;> rcases hu' with hu' | hu'
  · obtain ⟨c, hc, hc'⟩ := h.exists_conj_mod_one S hred hp3 hOF hu huZ hu' hu'Z
    exact ⟨c, hH₁H hc, hc'⟩
  · exact h.exists_conj_mod_mixed S hred hp3 hOF hu huZ hu' hu'Z
  · exact h.swap.exists_conj_mod_mixed S hred hp3 hOF hu huZ hu' hu'Z
  · obtain ⟨c, hc, hc'⟩ := h.swap.exists_conj_mod_one S hred hp3 hOF hu huZ hu' hu'Z
    exact ⟨c, hH₂H hc, hc'⟩

theorem input14617Trans_proved : Input14617Trans := by
  intro G _ _ T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec u u' hu huZ hu' hu'Z
  exact hdec.exists_conj_mod S hred hp3 hOF hu huZ hu' hu'Z

end Trans

section Singular

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem card_le_two_mul_of_comm_mem_Z (S : Setting146 G T M) {Y : Subgroup G} (hY : Y ≤ mcOf T)
    {w : G} (hc : ∀ y ∈ Y, ⁅y, w⁆ ∈ quasithinOmegaOneCenter T) :
    Nat.card Y ≤ 2 * Nat.card (Y ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
  by_cases hall : Y ≤ Subgroup.centralizer ({w} : Set G)
  · rw [inf_eq_left.mpr hall]
    omega
  · obtain ⟨q₀, hq₀Y, hq₀⟩ : ∃ q₀ ∈ Y, q₀ ∉ Subgroup.centralizer ({w} : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hall fun y hy => hcon y hy
    have hq₀1 : ⁅q₀, w⁆ ≠ 1 := by
      intro h1
      apply hq₀
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact (S146T.comm_eq_one_iff.mp h1)
    have hq₀Z := hc q₀ hq₀Y
    have hXY : (Y ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) ≤ Y := inf_le_left
    have hidx : (Y ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G).relIndex Y = 2 := by
      rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
      refine ⟨⟨q₀, hq₀Y⟩, fun b => ?_⟩
      have hbY : (b : G) ∈ Y := b.2
      have hbZ := hc b hbY
      have hmul : ⁅(b : G) * q₀, w⁆ = ⁅q₀, w⁆ * ⁅(b : G), w⁆ := by
        rw [S146T.comm_mul_left]
        have : (b : G) * ⁅q₀, w⁆ * (b : G)⁻¹ = ⁅q₀, w⁆ := by
          rw [S146T.comm_Z (hY hbY) hq₀Z]; group
        rw [this]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      show Xor ((b : G) * q₀ ∈ (Y ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G))
        ((b : G) ∈ (Y ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G))
      by_cases hβ : ⁅(b : G), w⁆ = 1
      · refine Or.inr ⟨⟨hbY, ?_⟩, fun h' => hq₀1 ?_⟩
        · show (b : G) ∈ Subgroup.centralizer ({w} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          rw [Set.mem_singleton_iff] at hv
          rw [hv]
          exact (S146T.comm_eq_one_iff.mp hβ)
        · have h2 := Subgroup.mem_centralizer_iff.mp h'.2 w rfl
          have := S146T.comm_eq_one_iff.mpr h2
          rwa [hmul, hβ, mul_one] at this
      · have hβγ : ⁅(b : G), w⁆ = ⁅q₀, w⁆ :=
          S.Z_eq_of_iff hbZ hq₀Z ⟨fun h' => absurd h' hβ, fun h' => absurd h' hq₀1⟩
        refine Or.inl ⟨⟨Y.mul_mem hbY hq₀Y, ?_⟩, fun h' => hβ ?_⟩
        · show (b : G) * q₀ ∈ Subgroup.centralizer ({w} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          rw [Set.mem_singleton_iff] at hv
          rw [hv]
          apply S146T.comm_eq_one_iff.mp
          rw [hmul, ← hβγ]
          have := S146T.Z_sq hbZ
          rwa [sq] at this
        · have h2 := Subgroup.mem_centralizer_iff.mp h'.2 w rfl
          exact S146T.comm_eq_one_iff.mpr h2
    have e := Subgroup.relIndex_mul_card (H := Y ⊓ Subgroup.centralizer ({w} : Set G)) (K := Y)
    rw [inf_eq_left.mpr hXY, hidx] at e
    omega

end Singular

section Pair

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.T_le_tZero_pair (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u₁ : G} (hu₁ : u₁ ∈ uHi T M H H₁)
    (hu₁T : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u₁) :
    T ≤ tZero T (u₁ * (t * u₁ * t⁻¹)) := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := le_normalizer_conjClosure _ _
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have htT : t ∈ T := h.t_mem
  have htH : t ∈ H := hTH htT
  have hu₁U : u₁ ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H hu₁
  have hu₂U : t * u₁ * t⁻¹ ∈ conjClosure (VZ T M) H :=
    (Subgroup.mem_normalizer_iff.mp (hHU htH) u₁).mp hu₁U
  have hu₁G : u₁ ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu₁U
  have hu₂G : t * u₁ * t⁻¹ ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hu₂U
  have hw₀G : u₁ * (t * u₁ * t⁻¹) ∈ mcOf T := (mcOf T).mul_mem hu₁G hu₂G
  have hcomm : u₁ * (t * u₁ * t⁻¹) = (t * u₁ * t⁻¹) * u₁ := isElemAbelian_comm hUab hu₁U hu₂U
  have hT₀eq := h.inf_normalizer_eq hTH
  have htH₀ : t ∉ H₀ := fun ht0 => h.t_not (h.H₀_le_normalizer_H₁ ht0)
  have htinvH₀ : t⁻¹ ∉ H₀ := fun ht0 => htH₀ (by simpa using H₀.inv_mem ht0)
  have ht2 : t * t ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) := by
    have h1 : t * t⁻¹⁻¹ ∈ H₀ := mul_inv_mem_of_relIndex_two h.index htH (H.inv_mem htH) htH₀ htinvH₀
    refine ⟨T.mul_mem htT htT, h.H₀_le_normalizer_H₁ ?_⟩
    simpa using h1
  have hT₀C : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T (u₁ * (t * u₁ * t⁻¹)) := by
    intro s hs
    have hsH₀ : s ∈ T ⊓ H₀ := by rw [← hT₀eq]; exact hs
    have hs' : t⁻¹ * s * t ∈ T ⊓ Subgroup.normalizer (H₁ : Set G) := by
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem htT) hs.1) htT, h.H₀_le_normalizer_H₁ ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_H₀ (H.inv_mem htH)) s).mp hsH₀.2
      simpa using this
    have hζ₁ : ⁅s, u₁⁆ ∈ quasithinOmegaOneCenter T := ((S146T.mem_tZero_iff hu₁G).mp (hu₁T hs)).2
    have hζ' : ⁅t⁻¹ * s * t, u₁⁆ ∈ quasithinOmegaOneCenter T :=
      ((S146T.mem_tZero_iff hu₁G).mp (hu₁T hs')).2
    have hζ₂ : ⁅s, t * u₁ * t⁻¹⁆ ∈ quasithinOmegaOneCenter T := by
      have e : ⁅s, t * u₁ * t⁻¹⁆ = t * ⁅t⁻¹ * s * t, u₁⁆ * t⁻¹ := by
        simp only [commutatorElement_def]; group
      have hc : t * ⁅t⁻¹ * s * t, u₁⁆ = ⁅t⁻¹ * s * t, u₁⁆ * t := S146T.comm_Z_T htT hζ'
      rw [e, hc]
      simpa [mul_assoc] using hζ'
    refine (S146T.mem_tZero_iff hw₀G).mpr ⟨hs.1, ?_⟩
    rw [S146T.comm_mul_right]
    have hc2 : u₁ * ⁅s, t * u₁ * t⁻¹⁆ = ⁅s, t * u₁ * t⁻¹⁆ * u₁ := S146T.comm_Z hu₁G hζ₂
    rw [hc2]
    have : ⁅s, t * u₁ * t⁻¹⁆ * u₁ * u₁⁻¹ = ⁅s, t * u₁ * t⁻¹⁆ := by group
    rw [this]
    exact (quasithinOmegaOneCenter T).mul_mem hζ₁ hζ₂
  have htC : t ∈ tZero T (u₁ * (t * u₁ * t⁻¹)) := by
    have hη : ⁅t * t, u₁⁆ ∈ quasithinOmegaOneCenter T := ((S146T.mem_tZero_iff hu₁G).mp (hu₁T ht2)).2
    refine (S146T.mem_tZero_iff hw₀G).mpr ⟨htT, ?_⟩
    have hηc : (t * (t * u₁ * t⁻¹) * t⁻¹) = ⁅t * t, u₁⁆ * u₁ := by
      simp only [commutatorElement_def]; group
    have e : ⁅t, u₁ * (t * u₁ * t⁻¹)⁆ =
        (t * u₁ * t⁻¹) * ⁅t * t, u₁⁆ * u₁ * (t * u₁ * t⁻¹)⁻¹ * u₁⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hcen : (t * u₁ * t⁻¹) * ⁅t * t, u₁⁆ = ⁅t * t, u₁⁆ * (t * u₁ * t⁻¹) := S146T.comm_Z hu₂G hη
    rw [mul_assoc (t * u₁ * t⁻¹), ← mul_assoc (t * u₁ * t⁻¹) ⁅t * t, u₁⁆, hcen]
    have e2 : ⁅t * t, u₁⁆ * (t * u₁ * t⁻¹) * u₁ * (t * u₁ * t⁻¹)⁻¹ * u₁⁻¹ = ⁅t * t, u₁⁆ := by
      have : (t * u₁ * t⁻¹) * u₁ = u₁ * (t * u₁ * t⁻¹) := hcomm.symm
      calc ⁅t * t, u₁⁆ * (t * u₁ * t⁻¹) * u₁ * (t * u₁ * t⁻¹)⁻¹ * u₁⁻¹
          = ⁅t * t, u₁⁆ * ((t * u₁ * t⁻¹) * u₁) * (t * u₁ * t⁻¹)⁻¹ * u₁⁻¹ := by group
        _ = ⁅t * t, u₁⁆ * (u₁ * (t * u₁ * t⁻¹)) * (t * u₁ * t⁻¹)⁻¹ * u₁⁻¹ := by rw [this]
        _ = ⁅t * t, u₁⁆ := by group
    rw [e2]
    exact hη
  intro s hsT
  by_cases hs0 : s ∈ H₀
  · exact hT₀C (by rw [hT₀eq]; exact ⟨hsT, hs0⟩)
  · have hst : s * t⁻¹ ∈ H₀ := mul_inv_mem_of_relIndex_two h.index (hTH hsT) htH hs0 htH₀
    have hmem : s * t⁻¹ ∈ tZero T (u₁ * (t * u₁ * t⁻¹)) :=
      hT₀C (by rw [hT₀eq]; exact ⟨T.mul_mem hsT (T.inv_mem htT), hst⟩)
    have := (tZero T (u₁ * (t * u₁ * t⁻¹))).mul_mem hmem htC
    simpa using this

end Pair

section SingularMain

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.exists_singular_centralizer (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {w : G} (hw : w ∈ uK T M H) (hw1 : w ∉ uHi T M H H₁)
    (hw2 : w ∉ uHi T M H H₂) :
    ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
      Nat.card T ≤ 2 * Nat.card S' := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hU₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hc : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hU₁ hx) (hU₂ hy)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁)
    (uHi T M H H₂) hc
  have hwsup : w ∈ uHi T M H H₁ ⊔ uHi T M H H₂ := by
    rw [h.dir_sup]
    exact Subgroup.mem_sup_left hw
  have hw' : w ∈ (uHi T M H H₁ : Set G) * (uHi T M H H₂ : Set G) := by
    rw [← hset]
    exact hwsup
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hw'
  have hZU₁ := Z_le_uHi T M H H₁
  have hZU₂ := Z_le_uHi T M H H₂
  have haZ : a ∉ quasithinOmegaOneCenter T := fun haZ => hw2 (by
    rw [← hab]
    exact (uHi T M H H₂).mul_mem (hZU₂ haZ) hb)
  have hbZ : b ∉ quasithinOmegaOneCenter T := fun hbZ => hw1 (by
    rw [← hab]
    exact (uHi T M H H₁).mul_mem ha (hZU₁ hbZ))
  obtain ⟨u₁, hu₁, hu₁Z, hu₁T⟩ := h.exists_fixed_vector S hred hp3
  have hu₂ : t * u₁ * t⁻¹ ∈ uHi T M H H₂ := by
    rw [← h.conjSub_uHi hred]
    exact mem_conjSub.mpr (by simpa [mul_assoc] using hu₁)
  have hu₂Z : t * u₁ * t⁻¹ ∉ quasithinOmegaOneCenter T := by
    intro hz
    apply hu₁Z
    have hcom : t⁻¹ * (t * u₁ * t⁻¹) = (t * u₁ * t⁻¹) * t⁻¹ :=
      S146T.comm_Z_T (T.inv_mem h.t_mem) hz
    have e : u₁ = t⁻¹ * (t * u₁ * t⁻¹) * t := by group
    rw [e, hcom]
    simpa [mul_assoc] using hz
  obtain ⟨c₁, hc₁H₁, hc₁⟩ := h.exists_conj_mod_one S hred hp3 hOF hu₁ hu₁Z ha haZ
  obtain ⟨c₂, hc₂H₂, hc₂⟩ := h.swap.exists_conj_mod_one S hred hp3 hOF hu₂ hu₂Z hb hbZ
  have hη₁ : c₂ * u₁ * c₂⁻¹ * u₁⁻¹ ∈ quasithinOmegaOneCenter T := by
    have h1 := (quasithinOmegaOneCenter T).inv_mem
      (h.cent₁ (Subgroup.commutator_mem_commutator hu₁ hc₂H₂))
    rw [commutatorElement_inv] at h1
    simpa [commutatorElement_def] using h1
  have hη₂ : c₁ * b * c₁⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T := by
    have h1 := (quasithinOmegaOneCenter T).inv_mem
      (h.cent₂ (Subgroup.commutator_mem_commutator hb hc₁H₁))
    rw [commutatorElement_inv] at h1
    simpa [commutatorElement_def] using h1
  have hc₁G : c₁ ∈ mcOf T := hHG (hH₁H hc₁H₁)
  have haG : a ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH (hU₁ ha)
  set ζ₁ := c₁ * u₁ * c₁⁻¹ * a⁻¹ with hζ₁def
  set ζ₂ := c₂ * (t * u₁ * t⁻¹) * c₂⁻¹ * b⁻¹ with hζ₂def
  set η₁ := c₂ * u₁ * c₂⁻¹ * u₁⁻¹ with hη₁def
  set η₂ := c₁ * b * c₁⁻¹ * b⁻¹ with hη₂def
  have E1 : c₁ * u₁ * c₁⁻¹ = ζ₁ * a := by rw [hζ₁def]; group
  have E2 : c₂ * (t * u₁ * t⁻¹) * c₂⁻¹ = ζ₂ * b := by rw [hζ₂def]; group
  have E3 : c₂ * u₁ * c₂⁻¹ = η₁ * u₁ := by rw [hη₁def]; group
  have E4 : c₁ * b * c₁⁻¹ = η₂ * b := by rw [hη₂def]; group
  have hcη₁ : c₁ * η₁ * c₁⁻¹ = η₁ := by
    rw [S146T.comm_Z hc₁G hη₁]; group
  have hcζ₂ : c₁ * ζ₂ * c₁⁻¹ = ζ₂ := by
    rw [S146T.comm_Z hc₁G hc₂]; group
  have haζ₂ : a * ζ₂ = ζ₂ * a := S146T.comm_Z haG hc₂
  have haη₂ : a * η₂ = η₂ * a := S146T.comm_Z haG hη₂
  have hmain : c₁ * c₂ * (u₁ * (t * u₁ * t⁻¹)) * (c₁ * c₂)⁻¹ = w * (η₁ * ζ₁ * ζ₂ * η₂) := by
    calc c₁ * c₂ * (u₁ * (t * u₁ * t⁻¹)) * (c₁ * c₂)⁻¹
        = c₁ * ((c₂ * u₁ * c₂⁻¹) * (c₂ * (t * u₁ * t⁻¹) * c₂⁻¹)) * c₁⁻¹ := by group
      _ = c₁ * ((η₁ * u₁) * (ζ₂ * b)) * c₁⁻¹ := by rw [E3, E2]
      _ = (c₁ * η₁ * c₁⁻¹) * (c₁ * u₁ * c₁⁻¹) * (c₁ * ζ₂ * c₁⁻¹) * (c₁ * b * c₁⁻¹) := by group
      _ = η₁ * (ζ₁ * a) * ζ₂ * (η₂ * b) := by rw [hcη₁, E1, hcζ₂, E4]
      _ = η₁ * ζ₁ * (a * ζ₂) * η₂ * b := by group
      _ = η₁ * ζ₁ * (ζ₂ * a) * η₂ * b := by rw [haζ₂]
      _ = η₁ * ζ₁ * ζ₂ * (a * η₂) * b := by group
      _ = η₁ * ζ₁ * ζ₂ * (η₂ * a) * b := by rw [haη₂]
      _ = (η₁ * ζ₁ * ζ₂ * η₂) * (a * b) := by group
      _ = w * (η₁ * ζ₁ * ζ₂ * η₂) := by
        rw [← hab]
        have hζ : η₁ * ζ₁ * ζ₂ * η₂ ∈ quasithinOmegaOneCenter T :=
          (quasithinOmegaOneCenter T).mul_mem
            ((quasithinOmegaOneCenter T).mul_mem
              ((quasithinOmegaOneCenter T).mul_mem hη₁ hc₁) hc₂) hη₂
        have hab' : a * b ∈ mcOf T := (mcOf T).mul_mem haG (S.mem_mcOf_of_mem_conjClosure hH (hU₂ hb))
        exact (S146T.comm_Z hab' hζ).symm
  have hζ : η₁ * ζ₁ * ζ₂ * η₂ ∈ quasithinOmegaOneCenter T :=
    (quasithinOmegaOneCenter T).mul_mem
      ((quasithinOmegaOneCenter T).mul_mem ((quasithinOmegaOneCenter T).mul_mem hη₁ hc₁) hc₂) hη₂
  have hcH : c₁ * c₂ ∈ H := H.mul_mem (hH₁H hc₁H₁) (hH₂H hc₂H₂)
  have hcG : c₁ * c₂ ∈ mcOf T := hHG hcH
  have hwU : w ∈ conjClosure (VZ T M) H := by
    have : w ∈ ((uK T M H : Subgroup G)) := hw
    exact S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _) hw
  have hwG : w ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hwU
  have hvG : (c₁ * c₂)⁻¹ * w * (c₁ * c₂) ∈ mcOf T :=
    (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem hcG) hwG) hcG
  have hw₀G : u₁ * (t * u₁ * t⁻¹) ∈ mcOf T := by
    have hu₁G : u₁ ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH (hU₁ hu₁)
    have hu₂G : t * u₁ * t⁻¹ ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH (hU₂ hu₂)
    exact (mcOf T).mul_mem hu₁G hu₂G
  have hmod : ((c₁ * c₂)⁻¹ * w * (c₁ * c₂))⁻¹ * (u₁ * (t * u₁ * t⁻¹)) ∈
      quasithinOmegaOneCenter T := by
    have hcen : (c₁ * c₂)⁻¹ * (η₁ * ζ₁ * ζ₂ * η₂) * (c₁ * c₂) = η₁ * ζ₁ * ζ₂ * η₂ := by
      have := S146T.comm_Z ((mcOf T).inv_mem hcG) hζ
      rw [this]; group
    have e : u₁ * (t * u₁ * t⁻¹) =
        ((c₁ * c₂)⁻¹ * w * (c₁ * c₂)) * (η₁ * ζ₁ * ζ₂ * η₂) := by
      calc u₁ * (t * u₁ * t⁻¹) = (c₁ * c₂)⁻¹ * (c₁ * c₂ * (u₁ * (t * u₁ * t⁻¹)) * (c₁ * c₂)⁻¹) *
            (c₁ * c₂) := by group
        _ = (c₁ * c₂)⁻¹ * (w * (η₁ * ζ₁ * ζ₂ * η₂)) * (c₁ * c₂) := by rw [hmain]
        _ = ((c₁ * c₂)⁻¹ * w * (c₁ * c₂)) * ((c₁ * c₂)⁻¹ * (η₁ * ζ₁ * ζ₂ * η₂) * (c₁ * c₂)) := by
            group
        _ = ((c₁ * c₂)⁻¹ * w * (c₁ * c₂)) * (η₁ * ζ₁ * ζ₂ * η₂) := by rw [hcen]
    rw [e, inv_mul_cancel_left]
    exact hζ
  have hTpair := h.T_le_tZero_pair S hred hu₁ hu₁T
  have hY : conjSub (c₁ * c₂) T ≤ H := by
    intro y hy
    have hs : (c₁ * c₂)⁻¹ * y * (c₁ * c₂) ∈ T := mem_conjSub.mp hy
    have : (c₁ * c₂) * ((c₁ * c₂)⁻¹ * y * (c₁ * c₂)) * (c₁ * c₂)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hcH (hTH hs)) (H.inv_mem hcH)
    simpa [mul_assoc] using this
  have hcomm : ∀ y ∈ conjSub (c₁ * c₂) T, ⁅y, w⁆ ∈ quasithinOmegaOneCenter T := by
    intro y hy
    have hs : (c₁ * c₂)⁻¹ * y * (c₁ * c₂) ∈ T := mem_conjSub.mp hy
    have h1 : ⁅(c₁ * c₂)⁻¹ * y * (c₁ * c₂), (c₁ * c₂)⁻¹ * w * (c₁ * c₂)⁆ ∈
        quasithinOmegaOneCenter T :=
      ((S146T.mem_tZero_iff hvG).mp
        (tZero_le_tZero_of_mod hvG hw₀G hmod (hTpair hs))).2
    have e : ⁅y, w⁆ = (c₁ * c₂) * ⁅(c₁ * c₂)⁻¹ * y * (c₁ * c₂), (c₁ * c₂)⁻¹ * w * (c₁ * c₂)⁆ *
        (c₁ * c₂)⁻¹ := by
      simp only [commutatorElement_def]; group
    have hcen := S146T.comm_Z hcG h1
    rw [e, hcen]
    simpa [mul_assoc] using h1
  have hYG : conjSub (c₁ * c₂) T ≤ mcOf T := hY.trans hHG
  have hcard := card_le_two_mul_of_comm_mem_Z S hYG hcomm
  refine ⟨conjSub (c₁ * c₂) T ⊓ Subgroup.centralizer ({w} : Set G),
    le_inf (inf_le_left.trans hY) inf_le_right, ?_, ?_⟩
  · exact (isPGroup_conjSub S.hyp.sylow.1).to_le inf_le_left
  · rw [← CosetGeom.card_conjSub (c₁ * c₂) T]
    exact hcard

end SingularMain

theorem input14617Singular_proved : Input14617Singular := by
  intro G _ _ T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec w hw hw1 hw2
  exact hdec.exists_singular_centralizer S hred hp3 hOF hw hw1 hw2

end CFSG.Quasithin
