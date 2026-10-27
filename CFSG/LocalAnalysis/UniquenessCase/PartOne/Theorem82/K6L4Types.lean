module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Compare
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Pts
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open Subgroup

structure ModelFacts {K : Type} [Field K] [Finite K] (H : Subgroup (GL (Fin 4) K))
    (ζ : CubeRoot K) (r : ℕ) {Y : Type} [Group Y] [Finite Y] (π : H →* Y) : Prop where
  quot : TwoQuot π
  ker : π.ker = (StatedScalars (Fin 4) K).subgroupOf H
  prime : r.Prime
  five : 5 ≤ r
  conj : ConjFact H ζ
  cent : CentFact H ζ r
  sub8 : Sub8Fact H ζ r
  sub9 : Sub9Fact H ζ

section Adapted

variable {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 4) K)} {ζ : CubeRoot K}
  {r : ℕ} {Y : Type} [Group Y] [Finite Y] {π : H →* Y}

theorem exists_adapted (hf : ModelFacts H ζ r π) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) :
    ∃ π' : H →* Y, TwoQuot π' ∧ π'.ker = π.ker ∧ ((D₀ ζ).subgroupOf H).map π' = A := by
  obtain ⟨Ã, hÃea, hÃcard, hÃmap⟩ := hf.quot.exists_lift_E27 hA h27
  obtain ⟨g, hg⟩ := hf.conj.2 Ã hÃea hÃcard
  have hq := hf.quot.comp_conj g⁻¹
  refine ⟨π.comp (MulAut.conj g⁻¹).toMonoidHom, hq.1, hq.2, ?_⟩
  have hmap : ((D₀ ζ).subgroupOf H).map (MulAut.conj g⁻¹).toMonoidHom = Ã := by
    rw [← hg, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id H := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hid, Subgroup.map_id]
  rw [← Subgroup.map_map, hmap, hÃmap]

@[expose] def c0 (ζ : CubeRoot K) (hstd : D₀ ζ ≤ H) (π' : H →* Y) :
    Multiplicative (Fin 4 → ZMod 3) →* Y :=
  π'.comp (stdDiagHomH ζ hstd)

private theorem c0_spec_range (hstd : D₀ ζ ≤ H) {π' : H →* Y} {A : Subgroup Y}
    (hA : ((D₀ ζ).subgroupOf H).map π' = A) : (c0 ζ hstd π').range = A := by
  have hrange_std : (stdDiagHomH ζ hstd).range = (D₀ ζ).subgroupOf H :=
    (MonoidHom.subgroupOf_range_eq_of_le (stdDiagHom ζ) hstd).symm
  rw [c0, MonoidHom.range_comp, hrange_std, hA]

private theorem c0_spec_ker (hstd : D₀ ζ ≤ H) {π' : H →* Y} {A : Subgroup Y}
    (hrange : (c0 ζ hstd π').range = A) (h27 : Nat.card A = 27) :
    ∀ v, c0 ζ hstd π' v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t := by
  have hconst : ∀ t : ZMod 3, c0 ζ hstd π' (Multiplicative.ofAdd fun _ => t) = 1 := by
    intro t
    have h1 : stdDiagHomH ζ hstd (Multiplicative.ofAdd fun _ => t) = 1 := by
      apply Subtype.ext
      exact stdDiagHom_const ζ t
    rw [show c0 ζ hstd π' (Multiplicative.ofAdd fun _ => t) =
      π' (stdDiagHomH ζ hstd (Multiplicative.ofAdd fun _ => t)) from rfl, h1, map_one]
  exact ker_of_card (c0 ζ hstd π') (by rw [hrange, h27]) hconst

private theorem c0_spec_normalizer (hstd : D₀ ζ ≤ H) {π' : H →* Y} (hπ' : TwoQuot π')
    {A : Subgroup Y} (hA : ((D₀ ζ).subgroupOf H).map π' = A) :
    ∀ n ∈ Subgroup.normalizer (A : Set Y), ∃ ρ : Equiv.Perm (Fin 4), ∀ v,
      n * c0 ζ hstd π' v * n⁻¹ =
        c0 ζ hstd π' (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i)) := by
  intro n hn
  have hn' : n ∈ Subgroup.normalizer ((((D₀ ζ).subgroupOf H).map π' : Subgroup Y) : Set Y) := by
    rw [hA]; exact hn
  have hS : ∀ s ∈ (D₀ ζ).subgroupOf H, s ^ 3 = 1 := by
    intro s hs
    have hs' : ((s : H) : GL (Fin 4) K) ∈ D₀ ζ := (Subgroup.mem_subgroupOf).mp hs
    apply Subtype.ext
    simpa using D₀_pow_three ζ hs'
  obtain ⟨h, hπh, hnorm⟩ := hπ'.normalizer_lift (S := (D₀ ζ).subgroupOf H) hS hn'
  have hg : ((h : H) : GL (Fin 4) K) ∈
      Subgroup.normalizer ((D₀ ζ : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K)) := by
    have hmem : h ∈ (Subgroup.normalizer
        ((D₀ ζ : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K))).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hstd]
      exact hnorm
    exact (Subgroup.mem_subgroupOf).mp hmem
  obtain ⟨ρ, hρ⟩ := monomial_of_normalizes ζ hg
  refine ⟨ρ, fun v => ?_⟩
  have hH : h * stdDiagHomH ζ hstd v * h⁻¹ =
      stdDiagHomH ζ hstd (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i)) := by
    apply Subtype.ext
    simpa [stdDiagHomH] using hρ v
  calc n * c0 ζ hstd π' v * n⁻¹
      = π' h * π' (stdDiagHomH ζ hstd v) * (π' h)⁻¹ := by
        rw [← hπh]; rfl
    _ = π' (h * stdDiagHomH ζ hstd v * h⁻¹) := by
        simp only [map_mul, map_inv]
    _ = π' (stdDiagHomH ζ hstd
          (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i))) := by
        rw [hH]
    _ = c0 ζ hstd π' (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i)) := rfl

theorem c0_spec (hstd : D₀ ζ ≤ H) {π' : H →* Y} (hπ' : TwoQuot π') {A : Subgroup Y}
    (hA : ((D₀ ζ).subgroupOf H).map π' = A) (h27 : Nat.card A = 27) :
    (c0 ζ hstd π').range = A ∧
      (∀ v, c0 ζ hstd π' v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t) ∧
      (∀ n ∈ Subgroup.normalizer (A : Set Y), ∃ ρ : Equiv.Perm (Fin 4), ∀ v,
        n * c0 ζ hstd π' v * n⁻¹ =
          c0 ζ hstd π' (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i))) := by
  have hrange := c0_spec_range hstd hA
  exact ⟨hrange, c0_spec_ker hstd hrange h27, c0_spec_normalizer hstd hπ' hA⟩

end Adapted

section Points

variable {Y : Type} [Group Y] [Finite Y]

private theorem centralizer_inv_singleton {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

private theorem exists_conj_centralizer {c : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (hc4 : ∀ σ : Equiv.Perm (Fin 4), ∃ n : Y, ∀ v, n * c v * n⁻¹ =
      c (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)))
    (hconst : ∀ t : ZMod 3, c (Multiplicative.ofAdd fun _ => t) = 1)
    {a u : Fin 4 → ZMod 3} {σ : Equiv.Perm (Fin 4)} {ε t : ZMod 3} (hε : ε ≠ 0)
    (hu : ∀ i, u i = ε * a (σ i) + t) :
    ∃ n : Y, Subgroup.centralizer ({c (Multiplicative.ofAdd u)} : Set Y) =
      (Subgroup.centralizer ({c (Multiplicative.ofAdd a)} : Set Y)).map
        (MulAut.conj n).toMonoidHom := by
  obtain ⟨n, hn⟩ := hc4 σ
  have hz : n * c (Multiplicative.ofAdd a) * n⁻¹ =
      c (Multiplicative.ofAdd fun i => a (σ i)) := by
    simpa using hn (Multiplicative.ofAdd a)
  have hu' : c (Multiplicative.ofAdd u) =
      c (Multiplicative.ofAdd fun i => ε * a (σ i)) := by
    conv_lhs => rw [show u = fun i => ε * a (σ i) + t from funext hu]
    rw [show (Multiplicative.ofAdd fun i => ε * a (σ i) + t) =
        (Multiplicative.ofAdd fun i => ε * a (σ i)) *
          (Multiplicative.ofAdd fun _ => t) from by
      rw [← ofAdd_add]; rfl]
    rw [map_mul, hconst t, mul_one]
  have hε12 : ε = 1 ∨ ε = 2 :=
    (show ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = 2 by decide) ε hε
  rcases hε12 with h1 | h2
  · refine ⟨n, ?_⟩
    rw [hu', h1,
      show (fun i => (1 : ZMod 3) * a (σ i)) = fun i => a (σ i) from by funext i; rw [one_mul]]
    rw [← hz]
    exact centralizer_conj n (c (Multiplicative.ofAdd a))
  · refine ⟨n, ?_⟩
    rw [hu', h2,
      show (fun i => (2 : ZMod 3) * a (σ i)) = fun i => -a (σ i) from by
        funext i
        exact (show ∀ e : ZMod 3, (2 : ZMod 3) * e = -e by decide) _]
    rw [show c (Multiplicative.ofAdd fun i => -a (σ i)) =
        (c (Multiplicative.ofAdd fun i => a (σ i)))⁻¹ from by
      rw [show (fun i => -a (σ i)) = -(fun i => a (σ i)) from rfl, ofAdd_neg]
      exact MonoidHom.map_inv c (Multiplicative.ofAdd fun i => a (σ i))]
    rw [← hz, centralizer_inv_singleton]
    exact centralizer_conj n (c (Multiplicative.ofAdd a))

private theorem cmp_centralizer_hc0 {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    {ε : ZMod 3} {τ : Equiv.Perm (Fin 4)} (hε : ε ≠ 0)
    (hcmp : ∀ v, c v = c₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v (τ i)))
    (a : Fin 4 → ZMod 3) :
    c₀ (Multiplicative.ofAdd a) = c (Multiplicative.ofAdd fun i => ε * a (τ⁻¹ i)) := by
  have hε2 : ε * ε = 1 :=
    (show ∀ e : ZMod 3, e ≠ 0 → e * e = 1 by decide) ε hε
  have h := hcmp (Multiplicative.ofAdd fun i => ε * a (τ⁻¹ i))
  simp only [toAdd_ofAdd] at h
  rw [show (fun i => ε * (fun j => ε * a (τ⁻¹ j)) (τ i)) = a from by
    funext i
    change ε * (ε * a (τ⁻¹ (τ i))) = a i
    rw [show τ⁻¹ (τ i) = i from Equiv.symm_apply_apply τ i, ← mul_assoc, hε2, one_mul]] at h
  exact h.symm

private theorem cmp_centralizer_conj {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    {ε : ZMod 3} {τ : Equiv.Perm (Fin 4)} (hε : ε ≠ 0) {a : Fin 4 → ZMod 3} {n : Y}
    (hz : n * c (Multiplicative.ofAdd a) * n⁻¹ =
      c (Multiplicative.ofAdd fun i => a (τ⁻¹ i)))
    (hc0 : c₀ (Multiplicative.ofAdd a) =
      c (Multiplicative.ofAdd fun i => ε * a (τ⁻¹ i))) :
    centralizer ({c₀ (Multiplicative.ofAdd a)} : Set Y) =
      (centralizer ({c (Multiplicative.ofAdd a)} : Set Y)).map (MulAut.conj n).toMonoidHom := by
  rw [hc0]
  have hε12 : ε = 1 ∨ ε = 2 :=
    (show ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = 2 by decide) ε hε
  rcases hε12 with h1 | h2
  · rw [h1,
      show (fun i => (1 : ZMod 3) * a (τ⁻¹ i)) = fun i => a (τ⁻¹ i) from by
        funext i; rw [one_mul]]
    rw [← hz]
    exact centralizer_conj n (c (Multiplicative.ofAdd a))
  · rw [h2,
      show (fun i => (2 : ZMod 3) * a (τ⁻¹ i)) = fun i => -a (τ⁻¹ i) from by
        funext i
        exact (show ∀ e : ZMod 3, (2 : ZMod 3) * e = -e by decide) _]
    rw [show c (Multiplicative.ofAdd fun i => -a (τ⁻¹ i)) =
        (c (Multiplicative.ofAdd fun i => a (τ⁻¹ i)))⁻¹ from by
      rw [show (fun i => -a (τ⁻¹ i)) = -(fun i => a (τ⁻¹ i)) from rfl, ofAdd_neg]
      exact MonoidHom.map_inv c (Multiplicative.ofAdd fun i => a (τ⁻¹ i))]
    rw [← hz, centralizer_inv_singleton]
    exact centralizer_conj n (c (Multiplicative.ofAdd a))

theorem cmp_centralizer {c c₀ : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (hc4 : ∀ σ : Equiv.Perm (Fin 4), ∃ n : Y, ∀ v, n * c v * n⁻¹ =
      c (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)))
    {ε : ZMod 3} {τ : Equiv.Perm (Fin 4)} (hε : ε ≠ 0)
    (hcmp : ∀ v, c v = c₀ (Multiplicative.ofAdd fun i => ε * Multiplicative.toAdd v (τ i)))
    (a : Fin 4 → ZMod 3) :
    ∃ n : Y, centralizer ({c (Multiplicative.ofAdd a)} : Set Y) =
      (centralizer ({c₀ (Multiplicative.ofAdd a)} : Set Y)).map (MulAut.conj n).toMonoidHom := by
  obtain ⟨n, hn⟩ := hc4 τ⁻¹
  have hz : n * c (Multiplicative.ofAdd a) * n⁻¹ =
      c (Multiplicative.ofAdd fun i => a (τ⁻¹ i)) := by
    simpa using hn (Multiplicative.ofAdd a)
  have hC := cmp_centralizer_conj hε hz (cmp_centralizer_hc0 hε hcmp a)
  refine ⟨n⁻¹, ?_⟩
  rw [hC, Subgroup.map_map]
  have hid : (MulAut.conj n⁻¹).toMonoidHom.comp (MulAut.conj n).toMonoidHom = MonoidHom.id Y := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [hid, Subgroup.map_id]

end Points

section Assembly

variable {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 4) K)} {ζ : CubeRoot K}
  {r : ℕ} {Y : Type} [Group Y] [Finite Y] {π : H →* Y}

theorem loc_points (hf : ModelFacts H ζ r π) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (hc : IsSumZeroCoords A c) :
    Loc1 r (centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y)) ∧
    Loc2 r (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y)) ∧
    Loc3 r (centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y)) ∧
    (Nat.card (centralizer (A : Set Y))).factorization 3 =
      (Nat.card (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y))).factorization 3 := by
  obtain ⟨π', hπ', hker', hA'⟩ := exists_adapted hf hA h27
  have hstd : D₀ ζ ≤ H := hf.conj.1
  have hker'' : π'.ker = (StatedScalars (Fin 4) K).subgroupOf H := hker'.trans hf.ker
  have hr2 : r ≠ 2 := by
    intro h
    have h5 := hf.five
    rw [h] at h5
    norm_num at h5
  obtain ⟨h₀r, h₀k, h₀n⟩ := c0_spec hstd hπ' hA' h27
  obtain ⟨ε, τ, hε, hcmp⟩ := compare_coords hc h₀r h₀k h₀n
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := cmp_centralizer hc.2.2.2 hε hcmp ![1, 1, -1, -1]
    rw [hn]
    simpa [c0, stdPt] using
      Loc1.conj r (loc1_standard hπ' hker'' hstd hf.prime hr2 hf.cent hf.sub8) n
  · obtain ⟨n, hn⟩ := cmp_centralizer hc.2.2.2 hε hcmp ![1, -1, 0, 0]
    rw [hn]
    simpa [c0, stdPt] using
      Loc2.conj r (loc2_standard hπ' hstd hf.prime hr2 hf.cent) n
  · obtain ⟨n, hn⟩ := cmp_centralizer hc.2.2.2 hε hcmp ![1, 1, 1, 0]
    rw [hn]
    simpa [c0, stdPt] using
      Loc3.conj r (loc3_standard hπ' hker'' hstd hf.prime hr2 hf.cent hf.sub9) n
  · have hstd3 : (Nat.card (centralizer (A : Set Y))).factorization 3 =
        (Nat.card (centralizer
          ({c0 ζ hstd π' (.ofAdd ![1, -1, 0, 0])} : Set Y))).factorization 3 := by
      simpa [c0, stdPt, hA'] using threePart_standard hπ' hstd r hf.cent
    obtain ⟨n, hn⟩ := cmp_centralizer hc.2.2.2 hε hcmp ![1, -1, 0, 0]
    have hcard : Nat.card (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y)) =
        Nat.card (centralizer ({c0 ζ hstd π' (.ofAdd ![1, -1, 0, 0])} : Set Y)) := by
      rw [hn, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    rw [hstd3, hcard]

private theorem dvd_of_shape {Y : Type} [Group Y] [Finite Y]
    {c : Multiplicative (Fin 4 → ZMod 3) →* Y}
    (hc4 : ∀ σ : Equiv.Perm (Fin 4), ∃ n : Y, ∀ v, n * c v * n⁻¹ =
      c (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)))
    (hconst : ∀ t : ZMod 3, c (Multiplicative.ofAdd fun _ => t) = 1)
    {a u : Fin 4 → ZMod 3} {σ : Equiv.Perm (Fin 4)} {ε t : ZMod 3} (hε : ε ≠ 0)
    (hu : ∀ i, u i = ε * a (σ i) + t) {r k : ℕ} (hr : r.Prime)
    (hka : (Nat.card (Subgroup.centralizer
      ({c (Multiplicative.ofAdd a)} : Set Y))).factorization r = k) (hk : 1 ≤ k) :
    r ∣ Nat.card (Subgroup.centralizer ({c (Multiplicative.ofAdd u)} : Set Y)) := by
  obtain ⟨n, hn⟩ := exists_conj_centralizer (c := c) hc4 hconst hε hu
  rw [hn, Subgroup.card_map_of_injective (MulAut.conj n).injective]
  exact (hr.dvd_iff_one_le_factorization
    (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)).mpr (by rw [hka]; exact hk)

private theorem exists_point_dvd_zpowers {X : Subgroup Y} (hX3 : Nat.card X = 3) :
    ∃ x : Y, x ∈ X ∧ x ≠ 1 ∧
      Subgroup.centralizer (X : Set Y) = Subgroup.centralizer ({x} : Set Y) := by
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hX3
    norm_num at hX3
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hxne' : (x : Y) ≠ 1 := fun h => hxne (Subtype.ext h)
  refine ⟨(x : Y), x.2, hxne', ?_⟩
  have hzp_le : Subgroup.zpowers (x : Y) ≤ X := Subgroup.zpowers_le.mpr x.2
  have hdiv : orderOf (x : Y) ∣ 3 := by
    have hd := Subgroup.card_dvd_of_le hzp_le
    rwa [Nat.card_zpowers, hX3] at hd
  have ho3 : orderOf (x : Y) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact absurd h fun hh => hxne' (orderOf_eq_one_iff.mp hh)
    · exact h
  have hX_eq : X = Subgroup.zpowers (x : Y) := by
    refine (Subgroup.eq_of_le_of_card_ge hzp_le ?_).symm
    rw [Nat.card_zpowers, ho3, hX3]
  conv_lhs => rw [hX_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem exists_point_dvd (r : ℕ) (hr : r.Prime) {A : Subgroup Y}
    {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (hc : IsSumZeroCoords A c)
    (h1 : Loc1 r (centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y)))
    (h2 : Loc2 r (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y)))
    (h3 : Loc3 r (centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y))) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → r ∣ Nat.card (centralizer (X : Set Y)) := by
  intro X hXA hX3
  obtain ⟨x, hxX, hxne', hcX⟩ := exists_point_dvd_zpowers hX3
  have hxmem : x ∈ c.range := by rw [hc.1]; exact hXA hxX
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hxmem
  let u : Fin 4 → ZMod 3 := Multiplicative.toAdd v
  have hv' : c (Multiplicative.ofAdd u) = (x : Y) := hv
  have hu_nc : ¬ ∃ t : ZMod 3, u = fun _ => t := by
    rintro ⟨t, ht⟩
    have h1' : c (Multiplicative.ofAdd u) = 1 := (hc.2.1 (Multiplicative.ofAdd u)).mpr ⟨t, ht⟩
    rw [hv'] at h1'
    exact hxne' h1'
  obtain ⟨ε, σ, t, hε, hshape⟩ := point_classes u hu_nc
  have hconst : ∀ s : ZMod 3, c (Multiplicative.ofAdd fun _ => s) = 1 :=
    fun s => (hc.2.1 (Multiplicative.ofAdd fun _ => s)).mpr ⟨s, rfl⟩
  rw [hcX, hv'.symm]
  rcases hshape with hshape | hshape | hshape
  · exact dvd_of_shape hc.2.2.2 hconst hε hshape hr h1.1 (by norm_num)
  · exact dvd_of_shape hc.2.2.2 hconst hε hshape hr h2 (by norm_num)
  · exact dvd_of_shape hc.2.2.2 hconst hε hshape hr h3.1 (by norm_num)

theorem sylow_vii {A : Subgroup Y} {x : Y} (hx : x ∈ A)
    (h : (Nat.card (centralizer (A : Set Y))).factorization 3 =
      (Nat.card (centralizer ({x} : Set Y))).factorization 3) :
    ∀ Q : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 3 Q (centralizer (A : Set Y)) →
      CFSG.ABGLocalTools.IsSylowOf 3 Q (centralizer ({x} : Set Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro Q hQ
  have hle : Subgroup.centralizer (A : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hx)
  have hQle : Q ≤ Subgroup.centralizer ({x} : Set Y) := hQ.le.trans hle
  have hcard : Nat.card Q =
      3 ^ (Nat.card (Subgroup.centralizer ({x} : Set Y))).factorization 3 := by
    rw [hQ.card_eq, h]
  exact CFSG.ABGLocalTools.isSylowOf_of_card hQle hcard

theorem l4Local_of_facts (hf : ModelFacts H ζ r π) :
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 → ∀ c, IsSumZeroCoords A c →
      (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
        r ∣ Nat.card (centralizer (X : Set Y))) ∧
      (Nat.card (centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y))).factorization r = 2 ∧
      (Nat.card (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y))).factorization r = 1 ∧
      (Nat.card (centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y))).factorization r = 3 ∧
      pRank r (centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y)) = 2 ∧
      pRank r (centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y)) = 2 ∧
      (∀ Q : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 3 Q (centralizer (A : Set Y)) →
        CFSG.ABGLocalTools.IsSylowOf 3 Q
          (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y))) ∧
      (∃ K : Subgroup Y, K ≤ centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y) ∧
        ¬ IsSolvable ↥K ∧ ⁅K, K⁆ = K ∧ Nat.card K = r ^ 2 * (r ^ 2 - 1) ^ 2 / 2 ∧
        ∀ N : Subgroup Y, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) → N = ⊥) ∧
      (∃ K : Subgroup Y, K ≤ centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y) ∧
        ¬ IsSolvable ↥K ∧
        ∀ N : Subgroup Y, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) →
          N ≤ centralizer (K : Set Y)) := by
  intro A hA h27 c hc
  obtain ⟨h1, h2, h3, h4⟩ := loc_points hf hA h27 hc
  refine ⟨exists_point_dvd r hf.prime hc h1 h2 h3, h1.1, h2, h3.1, h1.2.1, h3.2.1, ?_,
    h1.2.2, h3.2.2⟩
  refine sylow_vii ?_ h4
  rw [← hc.1]
  exact ⟨_, rfl⟩

theorem k6d_of_facts (hf : ModelFacts H ζ r π) {A : Subgroup Y} (hA : IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) : IsMulCommutative ↥(centralizer (A : Set Y)) := by
  obtain ⟨π', hπ', _, hA'⟩ := exists_adapted hf hA h27
  have hstd : D₀ ζ ≤ H := hf.conj.1
  have hS : ∀ s ∈ (D₀ ζ).subgroupOf H, s ^ 3 = 1 := by
    intro s hs
    have hs' : ((s : H) : GL (Fin 4) K) ∈ D₀ ζ := (Subgroup.mem_subgroupOf).mp hs
    apply Subtype.ext
    simpa using D₀_pow_three ζ hs'
  have hcent := hπ'.centralizer_map (S := (D₀ ζ).subgroupOf H) hS
  rw [hA'] at hcent
  rw [hcent]
  haveI : IsMulCommutative ↥(Subgroup.centralizer
      (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) := centralizer_D₀_comm ζ hstd
  exact Subgroup.map_isMulCommutative (Subgroup.centralizer
    (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) π'

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
