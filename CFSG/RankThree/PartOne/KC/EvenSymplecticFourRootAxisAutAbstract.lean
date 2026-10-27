module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open CFSG.ComponentClassification.OuterAutomorphisms

section Stab

variable {G : Type*} [Group G]

@[expose] def autStab (H : Subgroup G) : Subgroup (MulAut G) where
  carrier := {α | ∀ x, α x ∈ H ↔ x ∈ H}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {α β} hα hβ x => by rw [MulAut.mul_apply, hα, hβ]
  inv_mem' := fun {α} hα x => by
    have h := hα (α⁻¹ x)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

theorem mem_autStab {H : Subgroup G} {α : MulAut G} :
    α ∈ autStab H ↔ ∀ x, α x ∈ H ↔ x ∈ H :=
  Iff.rfl

theorem conj_mem_autStab_iff {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (x : G) : MulAut.conj g x ∈ H ↔ x ∈ H := by
  rw [Subgroup.mem_normalizer_iff] at hg
  rw [MulAut.conj_apply]
  exact (hg x).symm

end Stab

section Facts

variable {G : Type*} [Group G] {K : Type} [Field K] [CharP K 2] [Finite K]

structure AutNormalizerFacts (n : ℕ) (U A : Subgroup G) (s : SL₂ K →* G) (d : Kˣ →* G)
    (coord : K → G) (Fr : MulAut G) : Prop where
  stab_eq : autStab U = autStab A
  mem_iff : ∀ α : MulAut G, α ∈ autStab U ↔
    ∃ a ∈ A, ∃ (l : Kˣ) (M : SL₂ K) (k : ℕ), k < n ∧
      α = MulAut.conj (a * (d l * s M)) * Fr ^ k
  unique : ∀ a ∈ A, ∀ a' ∈ A, ∀ (l l' : Kˣ) (M M' : SL₂ K) (k k' : ℕ), k < n → k' < n →
    MulAut.conj (a * (d l * s M)) * Fr ^ k = MulAut.conj (a' * (d l' * s M')) * Fr ^ k' →
      a = a' ∧ l = l' ∧ M = M' ∧ k = k'
  coord_action : ∀ a ∈ A, ∀ (l : Kˣ) (M : SL₂ K) (k : ℕ) (x : K),
    (MulAut.conj (a * (d l * s M)) * Fr ^ k) (coord x) = coord ((l : K) ^ 2 * x ^ 2 ^ k)
  quotient_action : ∀ a ∈ A, ∀ (l : Kˣ) (M : SL₂ K) (k : ℕ) (M₀ : SL₂ K),
    (s (M * (frobSL K ^ k) M₀ * M⁻¹))⁻¹ * (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀) ∈ A
  centralizer : ∀ α : MulAut G, (∀ u ∈ U, α u = u) ↔
    ∃ g ∈ Subgroup.centralizer (U : Set G), α = MulAut.conj g
  inner_action : ∀ α ∈ autStab U,
    ((∃ c ∈ Subgroup.centralizer (U : Set G), ∀ y ∈ Subgroup.centralizer (U : Set G),
        (c * y * c⁻¹)⁻¹ * α y ∈ A) ↔
      ∃ g ∈ Subgroup.normalizer (U : Set G), α = MulAut.conj g)
  kernel_action : ∀ α ∈ autStab U,
    ((∀ y ∈ Subgroup.centralizer (U : Set G), y⁻¹ * α y ∈ A) ↔
      ∃ a ∈ A, ∃ l : Kˣ, α = MulAut.conj (a * d l))

theorem frobRingEquiv_pow_apply (k : ℕ) (x : K) : (frobRingEquiv K ^ k) x = x ^ 2 ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, frobRingEquiv_apply, ih, ← pow_mul, pow_succ, mul_comm]

theorem slFieldAut_frobRingEquiv_pow (k : ℕ) :
    slFieldAut K (frobRingEquiv K ^ k) = frobSL K ^ k :=
  map_pow (slFieldAut K) (frobRingEquiv K) k

theorem eq_zero_of_frobRingEquiv_pow_eq_one {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {k : ℕ} (hk : k < n) (h : frobRingEquiv K ^ k = 1) : k = 0 := by
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [(frobRingEquiv_data hn hK).1] at h1
  exact Nat.eq_zero_of_dvd_of_lt h1 hk

theorem conj_eq_conj_mul_frobSL_pow {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {N M : SL₂ K}
    {k : ℕ} (hk : k < n) (h : ∀ M₀ : SL₂ K, N * M₀ * N⁻¹ = M * (frobSL K ^ k) M₀ * M⁻¹) :
    N = M ∧ k = 0 := by
  have h1 : MulAut.conj N * slFieldAut K 1 =
      MulAut.conj M * slFieldAut K (frobRingEquiv K ^ k) := by
    rw [map_one, mul_one, slFieldAut_frobRingEquiv_pow]
    refine MulEquiv.ext fun M₀ => ?_
    simp only [MulAut.conj_apply, MulAut.mul_apply]
    exact h M₀
  obtain ⟨hNM, hσ⟩ := conj_mul_slFieldAut_inj h1
  exact ⟨hNM, eq_zero_of_frobRingEquiv_pow_eq_one hn hK hk hσ.symm⟩

end Facts

section Main

variable {G : Type*} [Group G] {K : Type} [Field K] [CharP K 2] [Finite K]
  {U A : Subgroup G} {s : SL₂ K →* G} {d : Kˣ →* G} {coord : K → G} {vec : G → Fin 2 → K}

theorem mem_centralizer_iff_of_autStab {β : MulAut G} (hβ : β ∈ autStab U) (g : G) :
    β g ∈ Subgroup.centralizer (U : Set G) ↔ g ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have := h (β u) ((hβ u).mpr hu)
    apply β.injective
    rw [map_mul, map_mul]
    exact this
  · intro h u hu
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, β u₀ = u := ⟨β⁻¹ u, by simp⟩
    have hu₀U : u₀ ∈ U := (hβ u₀).mp (hu₀ ▸ hu)
    have := h u₀ hu₀U
    rw [← hu₀, ← map_mul, ← map_mul, this]

omit [CharP K 2] [Finite K] in
theorem apply_mem_of_autStab (hS : RootAxisStructure U A s d coord vec) {β : MulAut G}
    (hβ : β ∈ autStab U) {x : G} (hx : x ∈ A) : β x ∈ A := by
  have hβC : ∀ g, g ∈ Subgroup.centralizer (U : Set G) ↔
      β g ∈ Subgroup.centralizer (U : Set G) := fun g =>
    (mem_centralizer_iff_of_autStab hβ g).symm
  have hmap := CFSG.pCore_map_iso 2 (subgroupEquiv β hβC)
  have hxC : x ∈ Subgroup.centralizer (U : Set G) := hS.A_le_C hx
  have h1 : (⟨x, hxC⟩ : Subgroup.centralizer (U : Set G)) ∈
      CFSG.pCore 2 (Subgroup.centralizer (U : Set G)) := by
    rw [hS.C_pCore]
    exact hx
  have h2 := Subgroup.mem_map_of_mem (subgroupEquiv β hβC).toMonoidHom h1
  rw [hmap, hS.C_pCore, Subgroup.mem_subgroupOf] at h2
  exact h2

omit [CharP K 2] [Finite K] in
theorem autStab_le_autStab_of_structure (hS : RootAxisStructure U A s d coord vec) :
    autStab U ≤ autStab A := fun β hβ x =>
  ⟨fun h => by
    have := apply_mem_of_autStab hS (inv_mem hβ) h
    rwa [MulAut.inv_apply_self] at this,
   fun h => apply_mem_of_autStab hS hβ h⟩

omit [CharP K 2] [Finite K] in
theorem pow_apply_coord {Fr : MulAut G} (hF : ∀ x, Fr (coord x) = coord (x ^ 2)) (k : ℕ) (x : K) :
    (Fr ^ k) (coord x) = coord (x ^ 2 ^ k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hF, ih, ← pow_mul, pow_succ, mul_comm]

theorem pow_apply_s {Fr : MulAut G} (hF : ∀ M, Fr (s M) = s (frobSL K M)) (k : ℕ) (M : SL₂ K) :
    (Fr ^ k) (s M) = s ((frobSL K ^ k) M) := by
  induction k generalizing M with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hF, ih, pow_succ, MulAut.mul_apply]

theorem frob_mem_U_iff (hS : RootAxisStructure U A s d coord vec) {Fr : MulAut G}
    (hF : ∀ x, Fr (coord x) = coord (x ^ 2)) (x : G) : Fr x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hS.coord_surj (Fr x) hx
    obtain ⟨z, hz⟩ := exists_sq_eq y
    have h1 : Fr x = Fr (coord z) := by rw [hF, hz, hy]
    rw [Fr.injective h1]
    exact hS.coord_mem z
  · intro hx
    obtain ⟨y, rfl⟩ := hS.coord_surj x hx
    rw [hF]
    exact hS.coord_mem _

omit [CharP K 2] [Finite K] in
theorem conj_coord (hS : RootAxisStructure U A s d coord vec) {a : G} (ha : a ∈ A) (l : Kˣ)
    (M : SL₂ K) (y : K) :
    MulAut.conj (a * (d l * s M)) (coord y) = coord ((l : K) ^ 2 * y) := by
  have hcs : s M * coord y * (s M)⁻¹ = coord y := by
    rw [← (Subgroup.mem_centralizer_iff.mp (hS.s_mem_C M)) (coord y) (hS.coord_mem y),
      mul_inv_cancel_right]
  have hca : ∀ z, z ∈ U → a * z * a⁻¹ = z := fun z hz => by
    rw [← (Subgroup.mem_centralizer_iff.mp (hS.A_le_C ha)) z hz, mul_inv_cancel_right]
  calc MulAut.conj (a * (d l * s M)) (coord y)
      = a * (d l * (s M * coord y * (s M)⁻¹) * (d l)⁻¹) * a⁻¹ := by
        rw [MulAut.conj_apply]
        group
    _ = coord ((l : K) ^ 2 * y) := by
        rw [hcs, hS.d_coord, hca _ (hS.coord_mem _)]

omit [CharP K 2] [Finite K] in
theorem conj_s (hS : RootAxisStructure U A s d coord vec) (a : G) (l : Kˣ) (M M₁ : SL₂ K) :
    MulAut.conj (a * (d l * s M)) (s M₁) = a * s (M * M₁ * M⁻¹) * a⁻¹ := by
  have h1 : d l * s (M * M₁ * M⁻¹) * (d l)⁻¹ = s (M * M₁ * M⁻¹) := by
    rw [← hS.s_comm_d, mul_inv_cancel_right]
  calc MulAut.conj (a * (d l * s M)) (s M₁)
      = a * (d l * (s M * s M₁ * (s M)⁻¹) * (d l)⁻¹) * a⁻¹ := by
        rw [MulAut.conj_apply]
        group
    _ = a * s (M * M₁ * M⁻¹) * a⁻¹ := by
        rw [← map_inv s M, ← map_mul s M, ← map_mul s, h1]

omit [CharP K 2] [Finite K] in
theorem inv_s_mul_mem (hS : RootAxisStructure U A s d coord vec) {a : G} (ha : a ∈ A)
    (Y : SL₂ K) : (s Y)⁻¹ * (a * s Y * a⁻¹) ∈ A := by
  have h1 := hS.A_normal_C (s Y)⁻¹ (inv_mem (hS.s_mem_C Y)) a ha
  have h2 : (s Y)⁻¹ * (a * s Y * a⁻¹) = ((s Y)⁻¹ * a * (s Y)⁻¹⁻¹) * a⁻¹ := by group
  rw [h2]
  exact mul_mem h1 (inv_mem ha)

omit [CharP K 2] [Finite K] in
theorem d_mem_N (hS : RootAxisStructure U A s d coord vec) (l : Kˣ) :
    d l ∈ Subgroup.normalizer (U : Set G) := by
  have := hS.ds_mem_N l 1
  rwa [map_one, mul_one] at this

omit [CharP K 2] [Finite K] in
theorem key_mem (hS : RootAxisStructure U A s d coord vec) {a : G} (ha : a ∈ A) (l : Kˣ) {y : G}
    (hy : y ∈ Subgroup.centralizer (U : Set G)) : y⁻¹ * MulAut.conj (a * d l) y ∈ A := by
  obtain ⟨b, hb, M₂, rfl⟩ := hS.C_decomp y hy
  have hb' : d l * b * (d l)⁻¹ ∈ A := hS.A_normal_N (d l) (d_mem_N hS l) b hb
  have h1 : d l * s M₂ * (d l)⁻¹ = s M₂ := by
    rw [← hS.s_comm_d, mul_inv_cancel_right]
  have hz : (b * s M₂)⁻¹ * (d l * (b * s M₂) * (d l)⁻¹) ∈ A := by
    have e : (b * s M₂)⁻¹ * (d l * (b * s M₂) * (d l)⁻¹) =
        (s M₂)⁻¹ * (b⁻¹ * (d l * b * (d l)⁻¹)) * ((s M₂)⁻¹)⁻¹ := by
      calc (b * s M₂)⁻¹ * (d l * (b * s M₂) * (d l)⁻¹)
          = (s M₂)⁻¹ * b⁻¹ * (d l * b * (d l)⁻¹ * (d l * s M₂ * (d l)⁻¹)) := by group
        _ = (s M₂)⁻¹ * b⁻¹ * (d l * b * (d l)⁻¹ * s M₂) := by rw [h1]
        _ = _ := by group
    rw [e]
    exact hS.A_normal_C (s M₂)⁻¹ (inv_mem (hS.s_mem_C M₂)) _ (mul_mem (inv_mem hb) hb')
  have e2 : (b * s M₂)⁻¹ * MulAut.conj (a * d l) (b * s M₂) =
      ((b * s M₂)⁻¹ * a * ((b * s M₂)⁻¹)⁻¹) *
        ((b * s M₂)⁻¹ * (d l * (b * s M₂) * (d l)⁻¹)) * a⁻¹ := by
    rw [MulAut.conj_apply]
    group
  rw [e2]
  exact mul_mem (mul_mem (hS.A_normal_C _ (inv_mem hy) a ha) hz) (inv_mem ha)

omit [CharP K 2] [Finite K] in
theorem eq_of_inv_s_mul_mem (hS : RootAxisStructure U A s d coord vec) {Y Y' : SL₂ K}
    (h : (s Y')⁻¹ * s Y ∈ A) : Y' = Y := by
  have h4 : s (Y'⁻¹ * Y) ∈ A := by
    rw [map_mul, map_inv]
    exact h
  have := hS.C_unique _ h4 1 (one_mem A) 1 (Y'⁻¹ * Y) (by rw [map_one, mul_one, one_mul])
  exact inv_mul_eq_one.mp this.2.symm

omit [CharP K 2] [Finite K] in
theorem eq_of_conj_inv_s_mul_mem (hS : RootAxisStructure U A s d coord vec) {b : G} (hb : b ∈ A)
    {Y Y' : SL₂ K} (h : (b * s Y' * b⁻¹)⁻¹ * s Y ∈ A) : Y' = Y := by
  apply eq_of_inv_s_mul_mem hS
  have h1 : b⁻¹ * ((b * s Y' * b⁻¹)⁻¹ * s Y) * b ∈ A := mul_mem (mul_mem (inv_mem hb) h) hb
  have h2 : (s Y)⁻¹ * b * ((s Y)⁻¹)⁻¹ ∈ A :=
    hS.A_normal_C _ (inv_mem (hS.s_mem_C Y)) b hb
  have h3 : (s Y')⁻¹ * s Y = (b⁻¹ * ((b * s Y' * b⁻¹)⁻¹ * s Y) * b) *
      (b⁻¹ * ((s Y)⁻¹ * b * ((s Y)⁻¹)⁻¹)) := by group
  rw [h3]
  exact mul_mem h1 (mul_mem (inv_mem hb) h2)

theorem AutNormalizerFacts.of_structure {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hS : RootAxisStructure U A s d coord vec) {Fr : MulAut G}
    (hcoord_inj : Function.Injective coord) (hFcoord : ∀ x, Fr (coord x) = coord (x ^ 2))
    (hFs : ∀ M, Fr (s M) = s (frobSL K M))
    (hclass : ∀ α : MulAut G, α ∈ autStab A → ∃ g ∈ Subgroup.normalizer (U : Set G),
      ∃ k : ℕ, k < n ∧ α = MulAut.conj g * Fr ^ k)
    (hunique : ∀ (g g' : G) (k k' : ℕ), k < n → k' < n →
      MulAut.conj g * Fr ^ k = MulAut.conj g' * Fr ^ k' → g = g' ∧ k = k') :
    AutNormalizerFacts n U A s d coord Fr := by
  have hFU := frob_mem_U_iff hS hFcoord
  have hFUk : ∀ (k : ℕ) (x : G), (Fr ^ k) x ∈ U ↔ x ∈ U := by
    intro k
    induction k with
    | zero => exact fun x => Iff.rfl
    | succ k ih => exact fun x => by rw [pow_succ, MulAut.mul_apply, ih, hFU]
  have hmem_of : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ k : ℕ,
      MulAut.conj g * Fr ^ k ∈ autStab U := fun g hg k x => by
    rw [MulAut.mul_apply, conj_mem_autStab_iff hg, hFUk]
  have hmem_iff : ∀ α : MulAut G, α ∈ autStab U ↔
      ∃ a ∈ A, ∃ (l : Kˣ) (M : SL₂ K) (k : ℕ), k < n ∧
        α = MulAut.conj (a * (d l * s M)) * Fr ^ k := by
    intro α
    constructor
    · intro hα
      obtain ⟨g, hg, k, hk, rfl⟩ := hclass α (autStab_le_autStab_of_structure hS hα)
      obtain ⟨a, ha, l, M, rfl⟩ := hS.N_decomp g hg
      exact ⟨a, ha, l, M, k, hk, rfl⟩
    · rintro ⟨a, ha, l, M, k, hk, rfl⟩
      exact hmem_of _ (mul_mem (hS.A_le_N ha) (hS.ds_mem_N l M)) k
  refine
    { stab_eq := ?_
      mem_iff := hmem_iff
      unique := ?_
      coord_action := ?_
      quotient_action := ?_
      centralizer := ?_
      inner_action := ?_
      kernel_action := ?_ }
  · refine le_antisymm (autStab_le_autStab_of_structure hS) fun α hα => ?_
    obtain ⟨g, hg, k, hk, rfl⟩ := hclass α hα
    exact hmem_of g hg k
  · intro a ha a' ha' l l' M M' k k' hk hk' h
    obtain ⟨hg, hkk⟩ := hunique _ _ k k' hk hk' h
    obtain ⟨h1, h2, h3⟩ := hS.N_unique a ha a' ha' l l' M M' hg
    exact ⟨h1, h2, h3, hkk⟩
  · intro a ha l M k x
    rw [MulAut.mul_apply, pow_apply_coord hFcoord k x, conj_coord hS ha l M]
  · intro a ha l M k M₀
    rw [MulAut.mul_apply, pow_apply_s hFs k M₀, conj_s hS a l M]
    exact inv_s_mul_mem hS ha _
  · intro α
    constructor
    · intro hα
      have hαU : α ∈ autStab U := fun x => ⟨fun hx => by
        have h1 := α.injective (hα (α x) hx)
        rw [← h1]
        exact hx, fun hx => by rw [hα x hx]; exact hx⟩
      obtain ⟨a, ha, l, M, k, hk, rfl⟩ := (hmem_iff α).mp hαU
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have h1 := hα (coord 1) (hS.coord_mem 1)
      rw [MulAut.mul_apply, pow_apply_coord hFcoord k 1, conj_coord hS ha l M] at h1
      have hl2 := hcoord_inj h1
      rw [one_pow, mul_one] at hl2
      have hl : (l : K) = 1 := by
        have h5 : ((l : K) - 1) ^ 2 = 0 := by linear_combination hl2 + (1 - (l : K)) * h2
        exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
      have hl' : l = 1 := Units.ext hl
      have hfix : ∀ x : K, x ^ 2 ^ k = x := fun x => by
        have h3 := hα (coord x) (hS.coord_mem x)
        rw [MulAut.mul_apply, pow_apply_coord hFcoord k x, conj_coord hS ha l M] at h3
        have h4 := hcoord_inj h3
        rw [hl, one_pow, one_mul] at h4
        exact h4
      have hk0 : k = 0 := eq_zero_of_frobRingEquiv_pow_eq_one hn hK hk
        (RingEquiv.ext fun x => by rw [frobRingEquiv_pow_apply, hfix x]; rfl)
      refine ⟨a * s M, mul_mem (hS.A_le_C ha) (hS.s_mem_C M), ?_⟩
      rw [hl', hk0, map_one, one_mul, pow_zero, mul_one]
    · rintro ⟨g, hg, rfl⟩ u hu
      rw [MulAut.conj_apply, ← (Subgroup.mem_centralizer_iff.mp hg) u hu, mul_inv_cancel_right]
  · intro α hα
    constructor
    · rintro ⟨c, hc, hcα⟩
      obtain ⟨a, ha, l, M, k, hk, rfl⟩ := (hmem_iff α).mp hα
      obtain ⟨b, hb, N, rfl⟩ := hS.C_decomp c hc
      have hconj : ∀ M₀ : SL₂ K, N * M₀ * N⁻¹ = M * (frobSL K ^ k) M₀ * M⁻¹ := by
        intro M₀
        have h1 := hcα (s M₀) (hS.s_mem_C M₀)
        have h2 : (b * s N) * s M₀ * (b * s N)⁻¹ = b * s (N * M₀ * N⁻¹) * b⁻¹ := by
          rw [map_mul s, map_mul s, map_inv s]
          group
        rw [h2] at h1
        have h3 : (s (M * (frobSL K ^ k) M₀ * M⁻¹))⁻¹ *
            (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀) ∈ A := by
          rw [MulAut.mul_apply, pow_apply_s hFs k M₀, conj_s hS a l M]
          exact inv_s_mul_mem hS ha _
        have h4 : (b * s (N * M₀ * N⁻¹) * b⁻¹)⁻¹ * s (M * (frobSL K ^ k) M₀ * M⁻¹) ∈ A := by
          have h5 := mul_mem h1 (inv_mem h3)
          have e : ((b * s (N * M₀ * N⁻¹) * b⁻¹)⁻¹ *
              (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀)) *
              ((s (M * (frobSL K ^ k) M₀ * M⁻¹))⁻¹ *
                (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀))⁻¹ =
              (b * s (N * M₀ * N⁻¹) * b⁻¹)⁻¹ * s (M * (frobSL K ^ k) M₀ * M⁻¹) := by group
          rw [e] at h5
          exact h5
        exact eq_of_conj_inv_s_mul_mem hS hb h4
      obtain ⟨-, hk0⟩ := conj_eq_conj_mul_frobSL_pow hn hK hk hconj
      refine ⟨a * (d l * s M), mul_mem (hS.A_le_N ha) (hS.ds_mem_N l M), ?_⟩
      rw [hk0, pow_zero, mul_one]
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨a, ha, l, M, rfl⟩ := hS.N_decomp g hg
      refine ⟨s M, hS.s_mem_C M, fun y hy => ?_⟩
      have hy' : s M * y * (s M)⁻¹ ∈ Subgroup.centralizer (U : Set G) :=
        mul_mem (mul_mem (hS.s_mem_C M) hy) (inv_mem (hS.s_mem_C M))
      have e : MulAut.conj (a * (d l * s M)) y =
          MulAut.conj (a * d l) (s M * y * (s M)⁻¹) := by
        simp only [MulAut.conj_apply]
        group
      rw [e]
      exact key_mem hS ha l hy'
  · intro α hα
    constructor
    · intro h
      obtain ⟨a, ha, l, M, k, hk, rfl⟩ := (hmem_iff α).mp hα
      have hconj : ∀ M₀ : SL₂ K, 1 * M₀ * 1⁻¹ = M * (frobSL K ^ k) M₀ * M⁻¹ := by
        intro M₀
        have h1 := h (s M₀) (hS.s_mem_C M₀)
        have h3 : (s (M * (frobSL K ^ k) M₀ * M⁻¹))⁻¹ *
            (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀) ∈ A := by
          rw [MulAut.mul_apply, pow_apply_s hFs k M₀, conj_s hS a l M]
          exact inv_s_mul_mem hS ha _
        have h4 : (s M₀)⁻¹ * s (M * (frobSL K ^ k) M₀ * M⁻¹) ∈ A := by
          have h5 := mul_mem h1 (inv_mem h3)
          have e : ((s M₀)⁻¹ * (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀)) *
              ((s (M * (frobSL K ^ k) M₀ * M⁻¹))⁻¹ *
                (MulAut.conj (a * (d l * s M)) * Fr ^ k) (s M₀))⁻¹ =
              (s M₀)⁻¹ * s (M * (frobSL K ^ k) M₀ * M⁻¹) := by group
          rw [e] at h5
          exact h5
        have h6 := eq_of_inv_s_mul_mem hS h4
        rw [one_mul, inv_one, mul_one]
        exact h6
      obtain ⟨hNM, hk0⟩ := conj_eq_conj_mul_frobSL_pow hn hK hk hconj
      refine ⟨a, ha, l, ?_⟩
      rw [hk0, ← hNM, pow_zero, mul_one, map_one, mul_one]
    · rintro ⟨a, ha, l, rfl⟩ y hy
      exact key_mem hS ha l hy

end Main

end KCRootAxis

end CFSG.RankThree.PartOne
