module

public import CFSG.Quasithin.H13.A6S13834N

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement


theorem sum_zero_of_mem_ev {r : Fin 6 → ZMod 2} (hr : r ∈ evenWeight 6) : ∑ i, r i = 0 := by
  simpa [evenWeight] using hr

theorem mem_ev_of_sum_zero {r : Fin 6 → ZMod 2} (hr : ∑ i, r i = 0) : r ∈ evenWeight 6 := by
  simpa [evenWeight] using hr

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

structure RepRel (ρ : ↥S.G1 →* Perm (Fin 6)) (R : G → (Fin 6 → ZMod 2) → Prop) : Prop where
  exists_rep : ∀ u ∈ conjClosure S.V3 S.G1, ∃ r, R u r
  exists_elt : ∀ r : Fin 6 → ZMod 2, ∑ i, r i = 0 → ∃ u, R u r
  mem : ∀ u r, R u r → u ∈ conjClosure S.V3 S.G1
  sum_zero : ∀ u r, R u r → ∑ i, r i = 0
  mul : ∀ u u' r r', R u r → R u' r' → R (u * u') (r + r')
  inv : ∀ u r, R u r → R u⁻¹ r
  conj : ∀ (h : ↥S.G1) u r, R u r → R ((h : G) * u * (h : G)⁻¹) (vp (ρ h) r)
  inj : ∀ u u' r, R u r → R u' r → u⁻¹ * u' ∈ fsuV1 T V
  uniq : ∀ u r r', R u r → R u r' → r' = r ∨ r' = r + onesV
  zero : ∀ u ∈ fsuV1 T V, R u 0

theorem exists_repRel {ρ : ↥S.G1 →* Perm (Fin 6)} (hβ : UHCoords S ρ) :
    ∃ R : G → (Fin 6 → ZMod 2) → Prop, S.RepRel ρ R := by
  have hUN : ∀ (h : ↥S.G1) (u : G), u ∈ conjClosure S.V3 S.G1 →
      (h : G) * u * (h : G)⁻¹ ∈ conjClosure S.V3 S.G1 := fun h u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 h.2) u).mp hu
  rcases hβ with ⟨β, hβs, hβk, hβe⟩ | ⟨β, hβs, hβk, hβe⟩
  · refine ⟨fun u r => ∃ (hu : u ∈ conjClosure S.V3 S.G1) (hr : r ∈ evenWeight 6),
      (QuotientAddGroup.mk (⟨r, hr⟩ : ↥(evenWeight 6)) : AltHeart 6) =
        Multiplicative.toAdd (β ⟨u, hu⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨u, hu⟩))
      exact ⟨x, hu, x.2, hx⟩
    · intro r hr
      have hr' := mem_ev_of_sum_zero hr
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (QuotientAddGroup.mk ⟨r, hr'⟩))
      exact ⟨u, u.2, hr', by rw [hu]; rfl⟩
    · rintro u r ⟨hu, -, -⟩
      exact hu
    · rintro u r ⟨-, hr, -⟩
      exact sum_zero_of_mem_ev hr
    · rintro u u' r r' ⟨hu, hr, e⟩ ⟨hu', hr', e'⟩
      refine ⟨(conjClosure S.V3 S.G1).mul_mem hu hu', (evenWeight 6).add_mem hr hr', ?_⟩
      have : (⟨u * u', (conjClosure S.V3 S.G1).mul_mem hu hu'⟩ : ↥(conjClosure S.V3 S.G1)) =
          ⟨u, hu⟩ * ⟨u', hu'⟩ := rfl
      rw [this, map_mul, toAdd_mul, ← e, ← e', ← QuotientAddGroup.mk_add]
      rfl
    · rintro u r ⟨hu, hr, e⟩
      refine ⟨(conjClosure S.V3 S.G1).inv_mem hu, hr, ?_⟩
      have : (⟨u⁻¹, (conjClosure S.V3 S.G1).inv_mem hu⟩ : ↥(conjClosure S.V3 S.G1)) =
          (⟨u, hu⟩)⁻¹ := rfl
      rw [this, map_inv, toAdd_inv, ← e, ← QuotientAddGroup.mk_neg]
      congr 1
      apply Subtype.ext
      exact (neg_eq_of_add_eq_zero_left (vadd_self r)).symm
    · rintro h u r ⟨hu, hr, e⟩
      refine ⟨hUN h u hu, (permWeight 6 (ρ h) ⟨r, hr⟩).2, ?_⟩
      exact hβe h ⟨u, hu⟩ ⟨_, hUN h u hu⟩ rfl ⟨r, hr⟩ e
    · rintro u u' r ⟨hu, hr, e⟩ ⟨hu', hr', e'⟩
      have h1 : β ⟨u, hu⟩ = β ⟨u', hu'⟩ := by
        apply Multiplicative.toAdd.injective
        rw [← e, ← e']
      have h2 := (hβk ((⟨u, hu⟩ : ↥(conjClosure S.V3 S.G1))⁻¹ * ⟨u', hu'⟩)).1
        (by rw [map_mul, map_inv, h1, inv_mul_cancel])
      exact h2
    · rintro u r r' ⟨hu, hr, e⟩ ⟨hu', hr', e'⟩
      have h1 : (QuotientAddGroup.mk ⟨r', hr'⟩ : AltHeart 6) = QuotientAddGroup.mk ⟨r, hr⟩ := by
        rw [e, e']
      exact (mk_eq_mk_iff _ _).1 h1
    · intro u hu
      have hu' : u ∈ conjClosure S.V3 S.G1 := S.V3_le_UH (S.V1_le_V3 hu)
      refine ⟨hu', (evenWeight 6).zero_mem, ?_⟩
      rw [(hβk ⟨u, hu'⟩).2 hu, toAdd_one]
      rfl
  · refine ⟨fun u r => ∃ hu : u ∈ conjClosure S.V3 S.G1,
      ((Multiplicative.toAdd (β ⟨u, hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = r,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      exact ⟨_, hu, rfl⟩
    · intro r hr
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ⟨r, mem_ev_of_sum_zero hr⟩)
      exact ⟨u, u.2, by rw [hu]; rfl⟩
    · rintro u r ⟨hu, -⟩
      exact hu
    · rintro u r ⟨hu, rfl⟩
      exact sum_zero_of_mem_ev (Multiplicative.toAdd (β ⟨u, hu⟩)).2
    · rintro u u' r r' ⟨hu, rfl⟩ ⟨hu', rfl⟩
      refine ⟨(conjClosure S.V3 S.G1).mul_mem hu hu', ?_⟩
      have : (⟨u * u', (conjClosure S.V3 S.G1).mul_mem hu hu'⟩ : ↥(conjClosure S.V3 S.G1)) =
          ⟨u, hu⟩ * ⟨u', hu'⟩ := rfl
      rw [this, map_mul, toAdd_mul]
      rfl
    · rintro u r ⟨hu, rfl⟩
      refine ⟨(conjClosure S.V3 S.G1).inv_mem hu, ?_⟩
      have : (⟨u⁻¹, (conjClosure S.V3 S.G1).inv_mem hu⟩ : ↥(conjClosure S.V3 S.G1)) =
          (⟨u, hu⟩)⁻¹ := rfl
      rw [this, map_inv, toAdd_inv]
      exact neg_eq_of_add_eq_zero_left (vadd_self _)
    · rintro h u r ⟨hu, rfl⟩
      refine ⟨hUN h u hu, ?_⟩
      rw [hβe h ⟨u, hu⟩ ⟨_, hUN h u hu⟩ rfl]
      rfl
    · rintro u u' r ⟨hu, e⟩ ⟨hu', e'⟩
      have h1 : β ⟨u, hu⟩ = β ⟨u', hu'⟩ := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        rw [e, e']
      have h2 := (hβk ((⟨u, hu⟩ : ↥(conjClosure S.V3 S.G1))⁻¹ * ⟨u', hu'⟩)).1
        (by rw [map_mul, map_inv, h1, inv_mul_cancel])
      exact h2
    · rintro u r r' ⟨hu, e⟩ ⟨hu', e'⟩
      left
      rw [← e, ← e']
    · intro u hu
      have hu' : u ∈ conjClosure S.V3 S.G1 := S.V3_le_UH (S.V1_le_V3 hu)
      refine ⟨hu', ?_⟩
      rw [(hβk ⟨u, hu'⟩).2 hu, toAdd_one]
      rfl

end Setting4

@[expose] def e02v : Fin 6 → ZMod 2 := ![1, 0, 1, 0, 0, 0]

@[expose] def e04v : Fin 6 → ZMod 2 := ![1, 0, 0, 0, 1, 0]

@[expose] def MovesOff (σ : Perm (Fin 6)) (w : Fin 6 → ZMod 2) : Prop :=
  w + vp σ w ≠ 0 ∧ w + vp σ w ≠ onesV

instance (σ : Perm (Fin 6)) (w : Fin 6 → ZMod 2) : Decidable (MovesOff σ w) := by
  unfold MovesOff; infer_instance

theorem e8_nontv : ∀ σ ∈ e8List, σ ≠ 1 → σ ≠ swap 0 1 → σ ≠ swap 2 3 → σ ≠ swap 4 5 →
    MovesOff σ e02v ∧ MovesOff σ e04v ∧ MovesOff σ (e02v + e04v) := by
  decide +kernel

theorem sum_e02_e04 : ∑ i, e02v i = 0 ∧ ∑ i, e04v i = 0 := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Coords

variable {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {R : G → (Fin 6 → ZMod 2) → Prop} (hR : S.RepRel ρ R)
  {τ : Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
include hR hρ'

theorem rep_comm (x : ↥S.G1) {u : G} {r : Fin 6 → ZMod 2} (hu : R u r) :
    R ((x : G) * u * (x : G)⁻¹ * u⁻¹) (vp τ (vp (ρ' x) (vp τ⁻¹ r)) + r) := by
  have h := hR.mul _ _ _ _ (hR.conj x u r hu) (hR.inv u r hu)
  have e : vp (ρ x) r = vp τ (vp (ρ' x) (vp τ⁻¹ r)) := by
    rw [hρ', ← vp_mul, ← vp_mul]
    congr 1
    group
  rw [e] at h
  exact h

omit hρ' in
theorem rep_one {r : Fin 6 → ZMod 2} (h : R 1 r) : r = 0 ∨ r = onesV := by
  rcases hR.uniq _ _ _ (hR.zero 1 (fsuV1 T V).one_mem) h with h | h
  · exact Or.inl h
  · right
    rw [h, zero_add]

theorem rho_tv_of_centralizes (hab : IsElemAbelian 2 (conjClosure S.V3 S.G1)) {x : ↥S.G1}
    (hx8 : ρ' x ∈ e8List) {D : Subgroup G} (hD2 : D.relIndex (conjClosure S.V3 S.G1) = 2)
    (hxD : ∀ d ∈ D, (x : G) * d * (x : G)⁻¹ = d) :
    ρ' x = 1 ∨ ρ' x = swap 0 1 ∨ ρ' x = swap 2 3 ∨ ρ' x = swap 4 5 := by
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3, n4⟩ := hne
  have hfin := e8_nontv _ hx8 n1 n2 n3 n4
  set U := conjClosure S.V3 S.G1 with hU
  have hUN : ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 x.2) u).mp hu
  have key : ∀ w, MovesOff (ρ' x) w → ∀ u, R u (vp τ w) →
      (x : G) * u * (x : G)⁻¹ * u⁻¹ ≠ 1 := by
    intro w hw u hu he
    have h1 := S.rep_comm hR hρ' x hu
    rw [he, vp_inv_vp] at h1
    obtain ⟨f1, f2⟩ := hw
    rcases S.rep_one hR h1 with h | h
    · apply f1
      apply vp_injective τ
      rw [vp_zero, vp_add, add_comm, ← h]
    · apply f2
      apply vp_injective τ
      rw [vp_add, add_comm]
      exact h.trans (vp_const τ).symm
  obtain ⟨s1, s2⟩ := sum_e02_e04
  obtain ⟨ua, hua⟩ := hR.exists_elt (vp τ e02v) (by rw [sum_vp]; exact s1)
  obtain ⟨ub, hub⟩ := hR.exists_elt (vp τ e04v) (by rw [sum_vp]; exact s2)
  have huaU := hR.mem _ _ hua
  have hubU := hR.mem _ _ hub
  have ka := key _ hfin.1 _ hua
  have kb := key _ hfin.2.1 _ hub
  have kab := key _ hfin.2.2 _ (by rw [vp_add]; exact hR.mul _ _ _ _ hua hub)
  have hnD : ∀ u, (x : G) * u * (x : G)⁻¹ * u⁻¹ ≠ 1 → u ∉ D := fun u hu huD => hu (by
    rw [hxD u huD, mul_inv_cancel])
  have hd := inv_mul_mem_of_relIndex_two hD2 huaU hubU (hnD _ ka) (hnD _ kb)
  have hxd := hxD _ hd
  have hcb : (x : G) * ub * (x : G)⁻¹ * ub⁻¹ = (x : G) * ua * (x : G)⁻¹ * ua⁻¹ := by
    calc (x : G) * ub * (x : G)⁻¹ * ub⁻¹ =
        ((x : G) * ua * (x : G)⁻¹) * ((x : G) * (ua⁻¹ * ub) * (x : G)⁻¹) * ub⁻¹ := by group
      _ = ((x : G) * ua * (x : G)⁻¹) * (ua⁻¹ * ub) * ub⁻¹ := by rw [hxd]
      _ = (x : G) * ua * (x : G)⁻¹ * ua⁻¹ := by group
  apply kab
  set c := (x : G) * ua * (x : G)⁻¹ * ua⁻¹ with hc
  have hcU : c ∈ U := U.mul_mem (hUN _ huaU) (U.inv_mem huaU)
  have hcomm : ua * c * ua⁻¹ = c := by
    rw [isElemAbelian_comm hab huaU hcU]
    group
  calc (x : G) * (ua * ub) * (x : G)⁻¹ * (ua * ub)⁻¹ =
      c * (ua * ((x : G) * ub * (x : G)⁻¹ * ub⁻¹) * ua⁻¹) := by rw [hc]; group
    _ = c * c := by rw [hcb, hcomm]
    _ = 1 := by rw [← pow_two]; exact isElemAbelian_pow_eq_one hab hcU

end Coords

end Setting4


@[expose] def lw4 : List (Fin 6 → ZMod 2) := [0, e02v, e04v, e02v + e04v]

@[expose] def CovB (t s : Perm (Fin 6)) : Prop :=
  ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    ∃ r ∈ lw4, ∃ a ∈ lw4, ∃ b ∈ lw4, x = r + (a + vp t a) + (b + vp s b)

instance (t s : Perm (Fin 6)) : Decidable (CovB t s) := by
  unfold CovB
  infer_instance

theorem covB_45 : CovB (swap 4 5) (swap 0 1 * swap 2 3) := by
  decide +kernel

theorem covB_23 : CovB (swap 2 3) (swap 0 1 * swap 4 5) := by
  decide +kernel

theorem covB_01 : CovB (swap 0 1) (swap 2 3 * swap 4 5) := by
  decide +kernel

theorem lw4_sum : ∀ w ∈ lw4, ∑ i, w i = 0 := by
  decide +kernel

@[expose] def lw4f : Fin 4 → Fin 6 → ZMod 2 := ![0, e02v, e04v, e02v + e04v]

theorem lw4f_mem : ∀ i : Fin 4, lw4f i ∈ lw4 := by
  decide +kernel

theorem lw4_exists_index : ∀ w ∈ lw4, ∃ i : Fin 4, lw4f i = w := by
  decide +kernel

theorem inv_mul_mem_of_count {G : Type} [Group G] [Finite G] {U B D : Subgroup G} (hDB : D ≤ B)
    (hUD : U ⊓ B ≤ D) (hcard : Nat.card B = Nat.card U) (hidx : 4 ≤ D.relIndex B)
    (hle : Nat.card U ≤ 8 * Nat.card ↥(U ⊓ B)) {a a' : G} (ha : a ∈ D) (ha' : a' ∈ D)
    (hna : a ∉ U) (hna' : a' ∉ U) : a⁻¹ * a' ∈ U := by
  have h1 := Subgroup.relIndex_mul_card (U ⊓ B) D
  rw [inf_eq_left.2 hUD] at h1
  have h2 := Subgroup.relIndex_mul_card D B
  rw [inf_eq_left.2 hDB] at h2
  have h2' : 4 * Nat.card D ≤ D.relIndex B * Nat.card D := Nat.mul_le_mul_right _ hidx
  have hpos : 0 < Nat.card ↥(U ⊓ B) := Nat.card_pos
  have hk : (U ⊓ B).relIndex D ≤ 2 := by
    by_contra hk
    push Not at hk
    have h3 : 3 * Nat.card ↥(U ⊓ B) ≤ (U ⊓ B).relIndex D * Nat.card ↥(U ⊓ B) :=
      Nat.mul_le_mul_right _ hk
    omega
  have hk0 : (U ⊓ B).relIndex D ≠ 0 := by
    show ((U ⊓ B).subgroupOf D).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hnaUB : a ∉ U ⊓ B := fun h => hna h.1
  have hnaUB' : a' ∉ U ⊓ B := fun h => hna' h.1
  rcases (by omega : (U ⊓ B).relIndex D = 1 ∨ (U ⊓ B).relIndex D = 2) with h | h
  · exact absurd (Subgroup.relIndex_eq_one.mp h ha) hnaUB
  · exact (inv_mul_mem_of_relIndex_two h ha ha' hnaUB hnaUB').1

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Count

variable {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {R : G → (Fin 6 → ZMod 2) → Prop} (hR : S.RepRel ρ R)
  {τ : Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
include hR hρ'

theorem card_UH_le {B : Subgroup G}
    (hBU : ∀ b ∈ B, ∀ u ∈ conjClosure S.V3 S.G1,
      b * u * b⁻¹ * u⁻¹ ∈ conjClosure S.V3 S.G1 ⊓ B)
    {b₁ b₂ : ↥S.G1} (hb₁ : (b₁ : G) ∈ B) (hb₂ : (b₂ : G) ∈ B) {t s : Perm (Fin 6)}
    (ht : ρ' b₁ = t) (hs : ρ' b₂ = s) (hcov : CovB t s) :
    Nat.card (conjClosure S.V3 S.G1) ≤ 8 * Nat.card ↥(conjClosure S.V3 S.G1 ⊓ B) := by
  set U := conjClosure S.V3 S.G1 with hU
  have hlift : ∀ i : Fin 4, ∃ a, R a (vp τ (lw4f i)) := fun i =>
    hR.exists_elt _ (by rw [sum_vp]; exact lw4_sum _ (lw4f_mem i))
  choose a ha using hlift
  let Φ : ↥(U ⊓ B) × ↥(fsuV1 T V) × Fin 4 → ↥U := fun p =>
    ⟨(p.1 : G) * a p.2.2 * (p.2.1 : G),
      U.mul_mem (U.mul_mem p.1.2.1 (hR.mem _ _ (ha _))) (S.V3_le_UH (S.V1_le_V3 p.2.1.2))⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨u, hu⟩
    obtain ⟨r, hr⟩ := hR.exists_rep u hu
    have hsum : ∑ i, vp τ⁻¹ r i = 0 := by rw [sum_vp]; exact hR.sum_zero _ _ hr
    obtain ⟨r₀, hr₀, a₁, ha₁, a₂, ha₂, hx⟩ := hcov _ hsum
    obtain ⟨i, hi⟩ := lw4_exists_index r₀ hr₀
    obtain ⟨u₁, hu₁⟩ := hR.exists_elt (vp τ a₁) (by rw [sum_vp]; exact lw4_sum _ ha₁)
    obtain ⟨u₂, hu₂⟩ := hR.exists_elt (vp τ a₂) (by rw [sum_vp]; exact lw4_sum _ ha₂)
    set y := ((b₁ : G) * u₁ * (b₁ : G)⁻¹ * u₁⁻¹) * ((b₂ : G) * u₂ * (b₂ : G)⁻¹ * u₂⁻¹)
      with hy
    have hyB : y ∈ U ⊓ B := (U ⊓ B).mul_mem (hBU _ hb₁ _ (hR.mem _ _ hu₁))
      (hBU _ hb₂ _ (hR.mem _ _ hu₂))
    have hRy := hR.mul _ _ _ _ (S.rep_comm hR hρ' b₁ hu₁) (S.rep_comm hR hρ' b₂ hu₂)
    rw [vp_inv_vp, vp_inv_vp, ht, hs] at hRy
    have hRya := hR.mul _ _ _ _ hRy (ha i)
    have hvec : vp τ (vp t a₁) + vp τ a₁ + (vp τ (vp s a₂) + vp τ a₂) + vp τ (lw4f i) = r := by
      conv_rhs => rw [← vp_vp_inv τ r, hx, ← hi]
      simp only [vp_add]
      abel
    rw [hvec] at hRya
    have hw := hR.inj _ _ _ hRya hr
    refine ⟨(⟨y, hyB⟩, ⟨_, hw⟩, i), ?_⟩
    apply Subtype.ext
    show y * a i * ((y * a i)⁻¹ * u) = u
    group
  have h := Nat.card_le_card_of_surjective Φ hsurj
  have h4 : Nat.card (Fin 4) = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
  rw [Nat.card_prod, Nat.card_prod, S.card_V1, h4] at h
  omega

end Count

end Setting4


@[expose] def TypeAB (x y : Perm (Fin 6)) : Prop :=
  (x = swap 0 1 ∧ y = swap 2 3) ∨ (x = swap 2 3 ∧ y = swap 4 5) ∨ (x = swap 4 5 ∧ y = swap 0 1) ∨
    (x = swap 4 5 ∧ y = swap 0 1 * swap 2 3) ∨ (x = swap 2 3 ∧ y = swap 0 1 * swap 4 5) ∨
    (x = swap 0 1 ∧ y = swap 2 3 * swap 4 5)

instance (x y : Perm (Fin 6)) : Decidable (TypeAB x y) := by
  unfold TypeAB
  infer_instance

theorem e8_four_class : ∀ a ∈ e8List, ∀ b ∈ e8List, a ≠ 1 → b ≠ 1 → a ≠ b →
    (¬ ∀ e ∈ e0List, e = 1 ∨ e = a ∨ e = b ∨ e = a * b) →
    ∃ x ∈ [a, b, a * b], ∃ y ∈ [a, b, a * b], TypeAB x y := by
  decide +kernel

theorem e8_sq : ∀ σ ∈ e8List, σ * σ = 1 := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_coords (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) {K : Subgroup G}
    (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K) (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hβ : UHCoords S ρ) :
    ∃ (τ : Perm (Fin 6)) (ρ' : ↥S.G1 →* Perm (Fin 6)), (∀ g, ρ' g = τ⁻¹ * ρ g * τ) ∧
      (∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G)) ∧
      (∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) ∧
      (∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6)) ∧
      (∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ) ∧
      (∀ y : ↥S.G1, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' y ∈ e8List) ∧
      ∀ y : G, y ∈ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) → ∃ hy : y ∈ S.G1, ρ' ⟨y, hy⟩ ∈ e0List := by
  have hL1H : S.L1 ≤ S.G1 := hL1K.trans (hKT ▸ le_sup_left)
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  have hQT : pCoreOf 2 S.G1 ≤ T := isSylowTwoOf_pCoreOf_le hF.toHypF91.sylow_H
  have hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ) :=
    eight_dvd_card_map hF.toHypF91.sylow_H ρ (fun h h1 => hQT ((hker h).1 h1))
      fun σ hσ => (honto σ hσ).elim fun k hk => ⟨k, hk.2⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 6), ∀ g : ↥S.G1,
      τ⁻¹ * ρ g * τ ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
    rcases hβ with ⟨β, -, hβk, hβe⟩ | ⟨β, -, hβk, hβe⟩
    · exact S.exists_tau_nat hβk hβe hT8
    · exact S.exists_tau_cover hβk hβe (sup_le hL1H hTH) hT8
  set ρ' : ↥S.G1 →* Perm (Fin 6) := (MulAut.conj τ⁻¹).toMonoidHom.comp ρ with hρ'def
  have hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ := fun g => by
    simp only [hρ'def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
  have hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    fun g => by rw [hρ']; exact hτ g
  have hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1 := by
    intro h
    rw [hρ', ← hker h]
    constructor
    · intro e
      calc ρ h = τ * (τ⁻¹ * ρ h * τ) * τ⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e
      rw [e]; group
  have hAn := (alternatingGroup.normal : (alternatingGroup (Fin 6)).Normal)
  have hKA' : ∀ k : ↥S.G1, (k : G) ∈ K → ρ' k ∈ alternatingGroup (Fin 6) := fun k hk => by
    rw [hρ']
    have := hAn.conj_mem _ (hKA k hk) τ⁻¹
    rwa [inv_inv] at this
  have honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ := by
    intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := honto _ (hAn.conj_mem σ hσ τ)
    exact ⟨k, hk, by rw [hρ', hkσ]; group⟩
  refine ⟨τ, ρ', hρ', hN', hker', hKA', honto', ?_, ?_⟩
  · have h2el : ∀ z : ↥S.G1, (z : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' z ^ 4 = 1 := by
      intro z hz
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup (r := 2) (S.L1 ⊔ T) ⟨z, hz⟩
      have hk' : z ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      refine pow_four_of_two ((hN' z).2 (S.L1T_le_NV3 (pCoreOf_le 2 _ hz))) (k := k) ?_
      rw [← map_pow, hk', map_one]
    intro y hy
    obtain ⟨c₀, hc₀L, hc₀3, hc₀1⟩ := S.exists_L1_cube
    set C : ↥S.G1 := ⟨c₀, hL1H hc₀L⟩ with hC
    have hC3 : C ^ 3 = 1 := Subtype.ext (by simpa using hc₀3)
    have hC1 : C ≠ 1 := fun h => hc₀1 (congrArg Subtype.val h)
    have hCA : ρ' C ∈ a4List := (mem_preImg.1 (S.L1_le_preA4 hN' hL1H hc₀L)).2
    have hC3' : ρ' C ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
    have hC1' : ρ' C ≠ 1 := S.rho_ne_one_of_cube hker' hC3 hC1
    have hyc : ρ' y ∈ cList := (hN' y).2 (S.L1T_le_NV3 (pCoreOf_le 2 _ hy))
    by_contra hne
    have hcy : ((C * y * C⁻¹ : ↥S.G1) : G) ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) (Subgroup.mem_sup_left hc₀L)) y).mp hy
    have hprod : ((y * (C * y * C⁻¹) : ↥S.G1) : G) ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hy hcy
    have h4 := h2el _ hprod
    rw [map_mul, map_mul, map_mul, map_inv] at h4
    exact mem_E8_of_c3 _ hCA hC3' hC1' _ hyc (h2el y hy) hne h4
  · intro y hy
    have hyL : y ∈ S.L1 ⊔ pCoreOf 2 S.G1 := pCoreOf_le 2 _ hy
    obtain ⟨hyH, hyA⟩ := mem_preImg.1 (S.L1Q_le_preA4 hN' hker' hL1H hyL)
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup (r := 2) (S.L1 ⊔ pCoreOf 2 S.G1) ⟨y, hy⟩
    have hk' : (⟨y, hyH⟩ : ↥S.G1) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact ⟨hyH, mem_e0_of_two hyA (k := k) (by rw [← map_pow, hk', map_one])⟩

theorem card_range_eq {ρ' : ↥S.G1 →* Perm (Fin 6)}
    (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) {X : Subgroup G}
    (hXH : X ≤ S.G1) :
    Nat.card (ρ'.comp (Subgroup.inclusion hXH)).range = (X ⊓ pCoreOf 2 S.G1).relIndex X := by
  rw [Subgroup.inf_relIndex_left]
  have hk : (ρ'.comp (Subgroup.inclusion hXH)).ker = (pCoreOf 2 S.G1).subgroupOf X := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker' _
  rw [Subgroup.relIndex, ← hk, Subgroup.index_ker]

theorem relIndex_conj_inf {c : G} (hc : c ∈ S.G1) (X : Subgroup G) :
    (conjSub c X ⊓ pCoreOf 2 S.G1).relIndex (conjSub c X) =
      (X ⊓ pCoreOf 2 S.G1).relIndex X := by
  have : conjSub c X ⊓ pCoreOf 2 S.G1 = conjSub c (X ⊓ pCoreOf 2 S.G1) := by
    rw [conjSub_inf, F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 S.G1 hc)]
  rw [this]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective

end Setting4


namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem VH_le_pCore (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) :
    conjClosure V S.G1 ≤ pCoreOf 2 S.G1 :=
  conjClosure_le fun _ hk v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 S.G1 hk) v).mp (hF.V_le_pCoreOf hv)

theorem comm_mem_conj (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) {γ γ' : F8.Geom T L S.G1}
    {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g) {X Y : Subgroup G}
    (hX : X = S.V3 ∨ X = V) (hY : Y = S.V3 ∨ Y = V) {c : G} (hc : c ∈ S.G1) {b : G}
    (hb : b ∈ conjSub c (F8.Uγ Y S.G1 (g : G))) {y : G} (hy : y ∈ conjClosure X S.G1) :
    b * y * b⁻¹ * y⁻¹ ∈ conjClosure X S.G1 ⊓ conjSub c (F8.Uγ Y S.G1 (g : G)) := by
  have h3 := hF.F913_3 s (X := X) (Y := Y) hX hY
  have hb' : c⁻¹ * b * c ∈ F8.Uγ Y S.G1 (g : G) := mem_conjSub.mp hb
  have hy' : c⁻¹ * y * c ∈ conjClosure X S.G1 := by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure X S.G1 (S.G1.inv_mem hc)) y).mp hy
    rwa [inv_inv] at this
  have hcomm := h3 (Subgroup.commutator_mem_commutator hy' hb')
  have e : b * y * b⁻¹ * y⁻¹ = c * ⁅c⁻¹ * y * c, c⁻¹ * b * c⁆⁻¹ * c⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e]
  refine ⟨?_, mul_mem_conjSub ((F8.Uγ Y S.G1 (g : G)).inv_mem hcomm.2)⟩
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure X S.G1 hc) _).mp
    ((conjClosure X S.G1).inv_mem hcomm.1)
  exact this

theorem lemma13_8_34_two (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (h13314 : Stmt13_3_14) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K) (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hβ : UHCoords S ρ) {c : G} (hc : c ∈ S.G1)
    (hcV : conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T))
    (hpos : 0 < mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G))) :
    mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) = 1 := by
  by_contra hne1
  have hm2 : 2 ≤ mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) := by
    omega
  obtain ⟨h3a, -⟩ := S.lemma13_8_34_three hNS h13315 h1356two hG1 h13314 hF s hKT hL1K ρ hker
    hKA honto hβ hc hcV
  obtain ⟨τ, ρ', hρ', hN', hker', hKA', honto', hE8, hE0⟩ :=
    S.exists_coords hF hKT hL1K ρ hker hKA honto hβ
  obtain ⟨R, hR⟩ := S.exists_repRel hβ
  set Q := pCoreOf 2 S.G1 with hQdef
  set U := conjClosure S.V3 S.G1 with hUdef
  set Uγ := F8.Uγ S.V3 S.G1 (g : G) with hUγdef
  set Vγ := F8.Uγ V S.G1 (g : G) with hVγdef
  set B := conjSub c Uγ with hBdef
  set W := conjSub c Vγ with hWdef
  have hQT : Q ≤ T := isSylowTwoOf_pCoreOf_le hF.toHypF91.sylow_H
  have hVle : V ≤ S.G1 := hF.toHypF91.V_le_H
  have hconjH : ∀ X : Subgroup G, X ≤ S.G1 → conjSub c X ≤ S.G1 := fun X hX x hx => by
    have h1 := hX (mem_conjSub.mp hx)
    have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [e]
    exact S.G1.mul_mem (S.G1.mul_mem hc h1) (S.G1.inv_mem hc)
  have hBH : B ≤ S.G1 := hconjH _ (hF.Uγ_le_H s)
  have hBW : B ≤ W := conjSub_mono _ hF.Uγ_le_Vγ
  have hBab : IsElemAbelian 2 B := isElemAbelian_conjSub hF.isElemAbelian_Uγ
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => isElemAbelian_comm hBab ha hb
  have hUQ : U ≤ Q := hF.conjClosure_Vp_le_pCoreOf
  have hVQ : conjClosure V S.G1 ≤ Q := S.VH_le_pCore hF
  have hBU : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ * u⁻¹ ∈ U ⊓ B := fun b hb u hu =>
    S.comm_mem_conj hF s (Or.inl rfl) (Or.inl rfl) hc hb hu
  have hBV : ∀ b ∈ B, ∀ y ∈ conjClosure V S.G1, b * y * b⁻¹ * y⁻¹ ∈ conjClosure V S.G1 ⊓ B :=
    fun b hb y hy => S.comm_mem_conj hF s (Or.inr rfl) (Or.inl rfl) hc hb hy
  have hidx : 4 ≤ (B ⊓ Q).relIndex B := by
    rw [hBdef, S.relIndex_conj_inf hc, ← hF.Dγ_eq_inf_pCoreOf s,
      HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm2
  set fB := ρ'.comp (Subgroup.inclusion hBH) with hfB
  have hcardR : 4 ≤ Nat.card fB.range := by rw [S.card_range_eq hker' hBH]; exact hidx
  have hB8 : ∀ z : ↥S.G1, (z : G) ∈ B → ρ' z ∈ e8List := fun z hz => hE8 z (hcV (hBW hz))
  have hfBe : ∀ w : ↥B, fB w = ρ' ⟨(w : G), hBH w.2⟩ := fun w => rfl
  obtain ⟨a, ⟨wa, rfl⟩, ha1⟩ : ∃ a ∈ fB.range, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : fB.range = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hcardR
    omega
  have ha8 : fB wa ∈ e8List := by rw [hfBe]; exact hB8 _ wa.2
  obtain ⟨b, ⟨wb, rfl⟩, hb1, hba⟩ : ∃ b ∈ fB.range, b ≠ 1 ∧ b ≠ fB wa := by
    by_contra hcon
    push Not at hcon
    have hle : fB.range ≤ Subgroup.zpowers (fB wa) := fun b hb => by
      by_cases h1 : b = 1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hcon b hb h1]; exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf (fB wa) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact e8_sq _ ha8)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hb8 : fB wb ∈ e8List := by rw [hfBe]; exact hB8 _ wb.2
  have hlift : ∀ x ∈ [fB wa, fB wb, fB wa * fB wb], ∃ z : ↥S.G1, (z : G) ∈ B ∧ ρ' z = x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨_, wa.2, (hfBe wa).symm⟩
    · exact ⟨_, wb.2, (hfBe wb).symm⟩
    · refine ⟨⟨(wa : G), hBH wa.2⟩ * ⟨(wb : G), hBH wb.2⟩, B.mul_mem wa.2 wb.2, ?_⟩
      rw [map_mul, ← hfBe, ← hfBe]
  have hnE0 : ¬ ∀ e ∈ e0List, e = 1 ∨ e = fB wa ∨ e = fB wb ∨ e = fB wa * fB wb := by
    intro hall
    apply h3a
    intro y hy
    obtain ⟨hyH, hye⟩ := hE0 y hy
    obtain ⟨z, hzB, hz⟩ : ∃ z : ↥S.G1, (z : G) ∈ B ∧ ρ' z = ρ' ⟨y, hyH⟩ := by
      rcases hall _ hye with h | h | h | h
      · exact ⟨1, B.one_mem, by rw [map_one, h]⟩
      · obtain ⟨z, hz, hz'⟩ := hlift (fB wa) (by simp)
        exact ⟨z, hz, by rw [hz', h]⟩
      · obtain ⟨z, hz, hz'⟩ := hlift (fB wb) (by simp)
        exact ⟨z, hz, by rw [hz', h]⟩
      · obtain ⟨z, hz, hz'⟩ := hlift (fB wa * fB wb) (by simp)
        exact ⟨z, hz, by rw [hz', h]⟩
    have hq : ((z⁻¹ * ⟨y, hyH⟩ : ↥S.G1) : G) ∈ Q := (hker' _).1 (by
      rw [map_mul, map_inv, hz, inv_mul_cancel])
    have e : y = (z : G) * ((z⁻¹ * ⟨y, hyH⟩ : ↥S.G1) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact (W ⊔ Q).mul_mem (Subgroup.mem_sup_left (hBW hzB)) (Subgroup.mem_sup_right hq)
  obtain ⟨x, hx, y, hy, hxy⟩ := e8_four_class _ ha8 _ hb8 ha1 hb1 hba.symm hnE0
  obtain ⟨x₁, hx₁B, hx₁⟩ := hlift x hx
  obtain ⟨x₂, hx₂B, hx₂⟩ := hlift y hy
  obtain ⟨v₀, hv₀, hv₀3⟩ := S.exists_V_not_V3
  have hVH := hF.F911_2
  have hVab := hF.toHypF91.elemAbelian
  have hlift' : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ∃ k : ↥S.G1, ρ' k = σ := fun σ hσ =>
    (honto' σ (Perm.mem_alternatingGroup.mpr hσ)).elim fun k hk => ⟨k, hk.2⟩
  have typeA : ∀ {f₁ f₂ g₁ m₁ g₂ m₂ s : Perm (Fin 6)}, QuadCertA f₁ f₂ g₁ m₁ g₂ m₂ s →
      ρ' x₁ = f₁ → ρ' x₂ = f₂ → False := by
    intro f₁ f₂ g₁ m₁ g₂ m₂ s hcert he₁ he₂
    obtain ⟨sg₁, sm₁, sg₂, sm₂, ss, hsC, -⟩ := id hcert
    obtain ⟨G₁, hG₁⟩ := hlift' _ sg₁
    obtain ⟨M₁, hM₁⟩ := hlift' _ sm₁
    obtain ⟨G₂, hG₂⟩ := hlift' _ sg₂
    obtain ⟨M₂, hM₂⟩ := hlift' _ sm₂
    obtain ⟨Y, hY⟩ := hlift' _ ss
    have hfix := S.fix_of_quadA hN' h13315 hv₀ hv₀3 hVH hVab hBc
      (fun b hb y hy => (hBV b hb y hy).2) hx₁B hx₂B hcert he₁ he₂ hG₁ hM₁ hG₂ hM₂ hY
    have hall := S.fix_all_gen hN' h13315 hv₀ hv₀3 hKT honto' hKA' hker' hQT ss hsC hY hfix
    exact S.false_of_fix h13315 hv₀ hv₀3 hNS h1356two hG1 h13314 hVle hall
  have typeB : ∀ {t s : Perm (Fin 6)}, CovB t s →
      (t = swap 0 1 ∨ t = swap 2 3 ∨ t = swap 4 5) → ρ' x₁ = t → ρ' x₂ = s → False := by
    intro t s hcov ht he₁ he₂
    have hle := S.card_UH_le hR hρ' hBU hx₁B hx₂B he₁ he₂ hcov
    have hcard : Nat.card B = Nat.card U :=
      (CosetGeom.card_conjSub _ _).trans (CosetGeom.card_conjSub _ _)
    refine S.false_of_transv hN' h13315 hNS h1356two hG1 h13314 hKT honto' hKA' hker' hQT hVle
      hVH hVab (x := x₁) (by rw [he₁]; exact ht) ?_
    intro y hy y' hy' h1 h2
    have hd : (x₁ : G) * y * (x₁ : G)⁻¹ * y⁻¹ ∈ B ⊓ Q :=
      ⟨(hBV _ hx₁B y hy).2, hVQ (hBV _ hx₁B y hy).1⟩
    have hd' : (x₁ : G) * y' * (x₁ : G)⁻¹ * y'⁻¹ ∈ B ⊓ Q :=
      ⟨(hBV _ hx₁B y' hy').2, hVQ (hBV _ hx₁B y' hy').1⟩
    exact inv_mul_mem_of_count inf_le_left (fun u hu => ⟨hu.2, hUQ hu.1⟩) hcard hidx hle hd hd'
      h1 h2
  unfold TypeAB at hxy
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact typeA quadCertA_0123 (hx₁.trans h1) (hx₂.trans h2)
  · exact typeA quadCertA_2345 (hx₁.trans h1) (hx₂.trans h2)
  · exact typeA quadCertA_4501 (hx₁.trans h1) (hx₂.trans h2)
  · exact typeB covB_45 (Or.inr (Or.inr rfl)) (hx₁.trans h1) (hx₂.trans h2)
  · exact typeB covB_23 (Or.inr (Or.inl rfl)) (hx₁.trans h1) (hx₂.trans h2)
  · exact typeB covB_01 (Or.inl rfl) (hx₁.trans h1) (hx₂.trans h2)

end Setting4

end CFSG.Quasithin.H13.A6
