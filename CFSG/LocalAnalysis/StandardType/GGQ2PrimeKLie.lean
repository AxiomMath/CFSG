module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeBasic

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open

theorem inner_unique {G : Type} [Group G] {X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1) {g k k' : G} (hk : k ∈ X) (hk' : k' ∈ X)
    (h : ∀ y ∈ X, g * y * g⁻¹ = k * y * k⁻¹) (h' : ∀ y ∈ X, g * y * g⁻¹ = k' * y * k'⁻¹) :
    k = k' := by
  have := hZX (k⁻¹ * k') (mul_mem (inv_mem hk) hk') fun y hy => by
    have e := (h y hy).symm.trans (h' y hy)
    calc k⁻¹ * k' * y = k⁻¹ * (k' * y * k'⁻¹) * k' := by group
      _ = k⁻¹ * (k * y * k⁻¹) * k' := by rw [e]
      _ = y * (k⁻¹ * k') := by group
  exact inv_mul_eq_one.1 this

@[expose] noncomputable def innerPart {G : Type} [Group G] {B X : Subgroup G} (b : G) : G :=
  open Classical in
  if hb : b ∈ B ∧ ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹ then hb.2.choose else 1

theorem innerPart_spec {G : Type} [Group G] {B X : Subgroup G}
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) {b : G} (hb : b ∈ B) :
    innerPart (B := B) (X := X) b ∈ X ∧
      ∀ y ∈ X, b * y * b⁻¹ =
        innerPart (B := B) (X := X) b * y * (innerPart (B := B) (X := X) b)⁻¹ := by
  have hb' : b ∈ B ∧ ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹ := ⟨hb, hinn b hb⟩
  unfold innerPart
  rw [dif_pos hb']
  exact hb'.2.choose_spec

theorem innerPart_eq {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹)
    {b k : G} (hb : b ∈ B) (hk : k ∈ X)
    (h : ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) : innerPart (B := B) (X := X) b = k :=
  inner_unique hZX (innerPart_spec hinn hb).1 hk (innerPart_spec hinn hb).2 h

theorem innerPart_mul {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) :
    innerPart (B := B) (X := X) (b * b') =
      innerPart (B := B) (X := X) b * innerPart (B := B) (X := X) b' := by
  obtain ⟨hk, hks⟩ := innerPart_spec hinn hb
  obtain ⟨hk', hks'⟩ := innerPart_spec hinn hb'
  refine innerPart_eq hZX hinn (mul_mem hb hb') (mul_mem hk hk') fun y hy => ?_
  have hy' : innerPart (B := B) (X := X) b' * y * (innerPart (B := B) (X := X) b')⁻¹ ∈ X :=
    mul_mem (mul_mem hk' hy) (inv_mem hk')
  calc b * b' * y * (b * b')⁻¹ = b * (b' * y * b'⁻¹) * b⁻¹ := by group
    _ = _ := by rw [hks' y hy, hks _ hy']; group

theorem innerPart_one {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹)
    : innerPart (B := B) (X := X) (1 : G) = 1 :=
  innerPart_eq hZX hinn (one_mem _) (one_mem _) fun y _ => by group

@[expose] noncomputable def centPart {G : Type} [Group G] {B X : Subgroup G}
    (b : G) : G := (innerPart (B := B) (X := X) b)⁻¹ * b

theorem centPart_cent {G : Type} [Group G] {B X : Subgroup G}
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹)
    {b : G} (hb : b ∈ B) {y : G} (hy : y ∈ X) :
    centPart (B := B) (X := X) b * y = y * centPart (B := B) (X := X) b := by
  obtain ⟨-, hks⟩ := innerPart_spec hinn hb
  have e := hks y hy
  unfold centPart
  set k := innerPart (B := B) (X := X) b
  calc k⁻¹ * b * y = k⁻¹ * (b * y * b⁻¹) * b := by group
    _ = k⁻¹ * (k * y * k⁻¹) * b := by rw [e]
    _ = y * (k⁻¹ * b) := by group

theorem centPart_one {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹)
    : centPart (B := B) (X := X) (1 : G) = 1 := by
  simp [centPart, innerPart_one hZX hinn]

theorem elemAbelian_comm' {G : Type} [Group G] {B : Subgroup G} (hBab : IsElemAbelian 3 B)
    {a b : G} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a :=
  congrArg Subtype.val (hBab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem innerPart_comm {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) (hBab : IsElemAbelian 3 B)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) :
    innerPart (B := B) (X := X) b * innerPart (B := B) (X := X) b' =
      innerPart (B := B) (X := X) b' * innerPart (B := B) (X := X) b := by
  rw [← innerPart_mul hZX hinn hb hb', ← innerPart_mul hZX hinn hb' hb,
    elemAbelian_comm' hBab hb hb']

theorem centPart_mul {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) (hBab : IsElemAbelian 3 B)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) :
    centPart (B := B) (X := X) b * centPart (B := B) (X := X) b' =
      centPart (B := B) (X := X) (b * b') := by
  obtain ⟨hk, hks⟩ := innerPart_spec hinn hb
  obtain ⟨hk', -⟩ := innerPart_spec hinn hb'
  unfold centPart
  rw [innerPart_mul hZX hinn hb hb']
  set k := innerPart (B := B) (X := X) b
  set k' := innerPart (B := B) (X := X) b'
  have hkk : k * k' = k' * k := innerPart_comm hZX hinn hBab hb hb'
  have e : b * k'⁻¹ * b⁻¹ = k * k'⁻¹ * k⁻¹ := hks _ (inv_mem hk')
  have e2 : b * k'⁻¹ = k'⁻¹ * b := by
    have : b * k'⁻¹ = k * k'⁻¹ * k⁻¹ * b := by rw [← e]; group
    rw [this]
    have : k * k'⁻¹ * k⁻¹ = k'⁻¹ := by
      calc k * k'⁻¹ * k⁻¹ = k'⁻¹ * (k' * k) * k'⁻¹ * k⁻¹ := by group
        _ = k'⁻¹ * (k * k') * k'⁻¹ * k⁻¹ := by rw [hkk]
        _ = k'⁻¹ := by group
    rw [this]
  calc k⁻¹ * b * (k'⁻¹ * b') = k⁻¹ * (b * k'⁻¹) * b' := by group
    _ = k⁻¹ * (k'⁻¹ * b) * b' := by rw [e2]
    _ = (k' * k)⁻¹ * (b * b') := by group
    _ = (k * k')⁻¹ * (b * b') := by rw [hkk]

@[expose] noncomputable def decompHom {G : Type} [Group G] {B X : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) (hBab : IsElemAbelian 3 B)
    : (B × B) →* G where
  toFun q := innerPart (B := B) (X := X) q.1.1 * centPart (B := B) (X := X) q.2.1
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one]
    rw [innerPart_one hZX hinn, centPart_one hZX hinn, one_mul]
  map_mul' q r := by
    simp only [Prod.fst_mul, Prod.snd_mul, MulMemClass.coe_mul]
    rw [innerPart_mul hZX hinn q.1.2 r.1.2, ← centPart_mul hZX hinn hBab q.2.2 r.2.2]
    have hc := centPart_cent (B := B) hinn q.2.2 (innerPart_spec hinn r.1.2).1
    calc innerPart (B := B) (X := X) q.1.1 * innerPart (B := B) (X := X) r.1.1 *
          (centPart (B := B) (X := X) q.2.1 * centPart (B := B) (X := X) r.2.1)
        = innerPart (B := B) (X := X) q.1.1 *
          (centPart (B := B) (X := X) q.2.1 * innerPart (B := B) (X := X) r.1.1) *
            centPart (B := B) (X := X) r.2.1 := by rw [hc]; group
      _ = _ := by group

theorem decomp {G : Type} [Group G] {B X T : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) (hBab : IsElemAbelian 3 B)
    [Finite G] (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ normalizer (T : Set G)) (hXT : X ≤ normalizer (T : Set G))
    (hrank : twoLocalPrimeRank 3 G ≤ 6) (hcard : Nat.card B = 3 ^ 6) {b : G} (hb : b ∈ B) :
    innerPart (B := B) (X := X) b ∈ B ⊓ X ∧
      centPart (B := B) (X := X) b ∈ B ⊓ centralizer (X : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ := decompHom hZX hinn hBab with hφ
  have hcomm : ∀ q r : B × B, q * r = r * q := fun q r =>
    Prod.ext (Subtype.ext (elemAbelian_comm' hBab q.1.2 r.1.2))
      (Subtype.ext (elemAbelian_comm' hBab q.2.2 r.2.2))
  have hP : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, q, rfl⟩ := u
      obtain ⟨_, r, rfl⟩ := v
      exact Subtype.ext (show φ q * φ r = φ r * φ q by rw [← map_mul, ← map_mul, hcomm])
    · rintro _ ⟨q, rfl⟩
      rw [← map_pow]
      have : q ^ 3 = 1 := Prod.ext (Subtype.ext (by simpa using hBab.2 _ q.1.2))
        (Subtype.ext (by simpa using hBab.2 _ q.2.2))
      rw [this, map_one]
  have hφb : ∀ c (hc : c ∈ B), φ (⟨c, hc⟩, ⟨c, hc⟩) = c := fun c hc => by
    show innerPart (B := B) (X := X) c * ((innerPart (B := B) (X := X) c)⁻¹ * c) = c
    group
  have hBP : B ≤ φ.range := fun c hc => ⟨_, hφb c hc⟩
  have hPT : φ.range ≤ normalizer (T : Set G) := by
    rintro _ ⟨q, rfl⟩
    show innerPart (B := B) (X := X) q.1.1 * ((innerPart (B := B) (X := X) q.2.1)⁻¹ * q.2.1) ∈ _
    exact mul_mem (hXT (innerPart_spec hinn q.1.2).1)
      (mul_mem (inv_mem (hXT (innerPart_spec hinn q.2.2).1)) (hBT q.2.2))
  have h3 : IsPGroup 3 φ.range := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (by simpa using hP.2 _ g.2)⟩
  obtain ⟨n, hn⟩ := h3.exists_card_eq
  have hn6 : n ≤ 6 := (le_twoLocalPrimeRank (by norm_num) T _ hT hT2 hPT hP hn).trans hrank
  have hPB : φ.range = B := by
    refine (Subgroup.eq_of_le_of_card_ge hBP ?_).symm
    rw [hn, hcard]
    exact Nat.pow_le_pow_right (by norm_num) hn6
  have hk : innerPart (B := B) (X := X) b ∈ B := by
    suffices h : innerPart (B := B) (X := X) b ∈ φ.range by rwa [hPB] at h
    refine ⟨(⟨b, hb⟩, 1), ?_⟩
    show innerPart (B := B) (X := X) b * centPart (B := B) (X := X) ((1 : B) : G) = _
    rw [OneMemClass.coe_one, centPart_one hZX hinn, mul_one]
  have hc : centPart (B := B) (X := X) b ∈ B := by
    suffices h : centPart (B := B) (X := X) b ∈ φ.range by rwa [hPB] at h
    refine ⟨(1, ⟨b, hb⟩), ?_⟩
    show innerPart (B := B) (X := X) ((1 : B) : G) * centPart (B := B) (X := X) b = _
    rw [OneMemClass.coe_one, innerPart_one hZX hinn, one_mul]
  exact ⟨⟨hk, (innerPart_spec hinn hb).1⟩,
    ⟨hc, mem_centralizer_iff.2 fun y hy => (centPart_cent hinn hb hy).symm⟩⟩

theorem decomp_eq {G : Type} [Group G] {B X T : Subgroup G}
    (hZX : ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1)
    (hinn : ∀ b ∈ B, ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹) (hBab : IsElemAbelian 3 B)
    [Finite G] (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ normalizer (T : Set G)) (hXT : X ≤ normalizer (T : Set G))
    (hrank : twoLocalPrimeRank 3 G ≤ 6) (hcard : Nat.card B = 3 ^ 6) :
    B = (B ⊓ X) ⊔ (B ⊓ centralizer (X : Set G)) := by
  refine le_antisymm (fun b hb => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨hk, hc⟩ := decomp hZX hinn hBab hT hT2 hBT hXT hrank hcard hb
  have : b = innerPart (B := B) (X := X) b * centPart (B := B) (X := X) b := by
    unfold centPart; group
  rw [this]
  exact mul_mem (mem_sup_left hk) (mem_sup_right hc)

theorem fpf_of_moves {G : Type} [Group G] [Finite G] {T : Subgroup G} (hT : Nat.card T = 4) {x : G}
    (hxT : x ∈ normalizer (T : Set G)) (hx3 : x ^ 3 = 1) (hmv : ∃ s ∈ T, x * s * x⁻¹ ≠ s) :
    ∀ t ∈ T, x * t * x⁻¹ = t → t = 1 := by
  intro t₀ ht₀ hfix₀
  by_contra hne
  obtain ⟨s, hs, hsx⟩ := hmv
  set F : Subgroup T := (centralizer ({x} : Set G)).subgroupOf T with hF
  have hmemF : ∀ y : T, y ∈ F ↔ x * (y : G) * x⁻¹ = y := by
    intro y
    rw [hF, mem_subgroupOf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hσT : ∀ y ∈ T, x * y * x⁻¹ ∈ T := fun y hy => (mem_normalizer_iff.1 hxT y).1 hy
  have hFdvd : Nat.card F ∣ 4 := hT ▸ Subgroup.card_subgroup_dvd_card F
  have hF1 : Nat.card F ≠ 1 := by
    intro h1
    have := (Subgroup.card_eq_one.1 h1)
    have ht : (⟨t₀, ht₀⟩ : T) ∈ F := (hmemF _).2 hfix₀
    rw [this, mem_bot] at ht
    exact hne (congrArg Subtype.val ht)
  have hF4 : Nat.card F ≠ 4 := by
    intro h4
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h4, hT])
    have : (⟨s, hs⟩ : T) ∈ F := htop ▸ mem_top _
    exact hsx ((hmemF _).1 this)
  have hF2 : Nat.card F = 2 := by
    have : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hFdvd
    interval_cases h : Nat.card F <;> simp_all
  have hidx : F.index = 2 := by
    have := Subgroup.card_mul_index F
    rw [hF2, hT] at this
    omega
  set σs : T := ⟨x * s * x⁻¹, hσT s hs⟩ with hσs
  have hsF : (⟨s, hs⟩ : T) ∉ F := fun h => hsx ((hmemF _).1 h)
  have hσsF : σs ∉ F := by
    intro h
    have h1 := (hmemF _).1 h
    apply hsx
    have : x * (x * s * x⁻¹) * x⁻¹ = x * s * x⁻¹ := h1
    have h2 : x * s * x⁻¹ = s := by
      have := congrArg (fun g => x⁻¹ * g * x) this
      simpa [mul_assoc] using this
    exact h2
  have hf : (⟨s, hs⟩ : T)⁻¹ * σs ∈ F := by
    rw [mul_mem_iff_of_index_two hidx, inv_mem_iff]
    exact ⟨fun h => absurd h hsF, fun h => absurd h hσsF⟩
  set f : G := s⁻¹ * (x * s * x⁻¹) with hfdef
  have hffix : x * f * x⁻¹ = f := (hmemF _).1 hf
  have hf2 : f * f = 1 := by
    have := pow_card_eq_one' (G := F) (x := ⟨_, hf⟩)
    rw [hF2] at this
    have := congrArg (fun y : F => ((y : T) : G)) this
    simpa [pow_two] using this
  have hσ : x * s * x⁻¹ = s * f := by rw [hfdef]; group
  have hσ2 : x * (x * s * x⁻¹) * x⁻¹ = s := by
    rw [hσ]
    calc x * (s * f) * x⁻¹ = (x * s * x⁻¹) * (x * f * x⁻¹) := by group
      _ = s := by rw [hσ, hffix, mul_assoc, hf2, mul_one]
  have hσ3 : x * (x * (x * s * x⁻¹) * x⁻¹) * x⁻¹ = s := by
    have : x * (x * (x * s * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * s * (x ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [this, hx3]; group
  rw [hσ2] at hσ3
  exact hsx hσ3

end CFSG.GGQ2Prime
