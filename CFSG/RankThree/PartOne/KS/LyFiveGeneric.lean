module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartOne

open Subgroup

section Fixed

variable {G X : Type*} [Group G] [MulAction G X]

theorem card_centralizer_le_of_fixed [Finite G] (w : G) (d : X) (F : Finset X)
    (hF : ∀ p : X, w • p = p → p ∈ F) (hd : w • d = d) :
    Nat.card (centralizer ({w} : Set G)) ≤
      F.card * Nat.card (centralizer ({w} : Set G) ⊓ MulAction.stabilizer G d : Subgroup G) := by
  classical
  set K : Subgroup G := centralizer ({w} : Set G) with hK
  have horb : ∀ k : K, (k : G) • d ∈ F := by
    intro k
    apply hF
    have hk : (k : G) * w = w * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc w • ((k : G) • d) = (w * (k : G)) • d := (mul_smul w (k : G) d).symm
      _ = ((k : G) * w) • d := by rw [hk]
      _ = (k : G) • (w • d) := mul_smul _ _ _
      _ = (k : G) • d := by rw [hd]
  have hsub : (MulAction.orbit K d : Set X) ⊆ (F : Set X) := by
    rintro _ ⟨k, rfl⟩
    exact horb k
  have h1 : Nat.card (MulAction.orbit K d) ≤ F.card := by
    rw [Nat.card_coe_set_eq]
    calc (MulAction.orbit K d).ncard ≤ (F : Set X).ncard := Set.ncard_le_ncard hsub F.finite_toSet
      _ = F.card := Set.ncard_coe_finset F
  have h2 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K d)
  rw [Nat.card_prod] at h2
  have h3 : Nat.card (MulAction.stabilizer K d) =
      Nat.card (K ⊓ MulAction.stabilizer G d : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1 : G), Subgroup.mem_inf.mpr ⟨k.1.2, MulAction.mem_stabilizer_iff.mpr (by
          have := MulAction.mem_stabilizer_iff.mp k.2
          simpa [Subgroup.smul_def] using this)⟩⟩
        invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩, MulAction.mem_stabilizer_iff.mpr (by
          have := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp g.2).2
          simpa [Subgroup.smul_def] using this)⟩
        left_inv := fun k => rfl
        right_inv := fun g => rfl }
  rw [h3] at h2
  calc Nat.card K = Nat.card (MulAction.orbit K d) *
        Nat.card (K ⊓ MulAction.stabilizer G d : Subgroup G) := h2.symm
    _ ≤ F.card * Nat.card (K ⊓ MulAction.stabilizer G d : Subgroup G) :=
        Nat.mul_le_mul_right _ h1

theorem card_inf_stabilizer_le_of_conj [Finite G] (w τ : G) (d d₀ : X) (hτ : τ • d₀ = d) :
    Nat.card (centralizer ({w} : Set G) ⊓ MulAction.stabilizer G d : Subgroup G) ≤
      Nat.card (centralizer ({τ⁻¹ * w * τ} : Set G) ⊓ MulAction.stabilizer G d₀ : Subgroup G) := by
  have hτ' : τ⁻¹ • d = d₀ := by rw [← hτ, inv_smul_smul]
  refine Nat.card_le_card_of_injective
    (fun k => ⟨τ⁻¹ * (k : G) * τ, Subgroup.mem_inf.mpr ⟨?_, MulAction.mem_stabilizer_iff.mpr ?_⟩⟩) ?_
  · have hk : (k : G) * w = w * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).1
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc τ⁻¹ * (k : G) * τ * (τ⁻¹ * w * τ) = τ⁻¹ * ((k : G) * w) * τ := by group
      _ = τ⁻¹ * (w * (k : G)) * τ := by rw [hk]
      _ = τ⁻¹ * w * τ * (τ⁻¹ * (k : G) * τ) := by group
  · have hk := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp k.2).2
    calc (τ⁻¹ * (k : G) * τ) • d₀ = τ⁻¹ • ((k : G) • (τ • d₀)) := by
          rw [mul_smul, mul_smul]
      _ = d₀ := by rw [hτ, hk, hτ']
  · intro k k' h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp only [mul_left_inj, mul_right_inj] at this
    exact this

theorem card_inf_stabilizer_eq_of_conj [Finite G] (w τ : G) (d d₀ : X) (hτ : τ • d₀ = d) :
    Nat.card (centralizer ({w} : Set G) ⊓ MulAction.stabilizer G d : Subgroup G) =
      Nat.card (centralizer ({τ⁻¹ * w * τ} : Set G) ⊓ MulAction.stabilizer G d₀ : Subgroup G) := by
  refine le_antisymm (card_inf_stabilizer_le_of_conj w τ d d₀ hτ) ?_
  have hτ' : τ⁻¹ • d = d₀ := by rw [← hτ, inv_smul_smul]
  have := card_inf_stabilizer_le_of_conj (τ⁻¹ * w * τ) τ⁻¹ d₀ d hτ'
  have e : τ⁻¹⁻¹ * (τ⁻¹ * w * τ) * τ⁻¹ = w := by group
  rwa [e] at this

theorem orbit_centralizer_subset (w : G) (d : X) (hd : w • d = d) :
    (MulAction.orbit (centralizer ({w} : Set G)) d : Set X) ⊆ {p | w • p = p} := by
  rintro _ ⟨k, rfl⟩
  have hk : (k : G) * w = w * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
  show w • ((k : G) • d) = (k : G) • d
  calc w • ((k : G) • d) = (w * (k : G)) • d := (mul_smul w (k : G) d).symm
    _ = ((k : G) * w) • d := by rw [hk]
    _ = (k : G) • (w • d) := mul_smul _ _ _
    _ = (k : G) • d := by rw [hd]

theorem card_centralizer_eq_orbit_mul [Finite G] (w : G) (d : X) :
    Nat.card (MulAction.orbit (centralizer ({w} : Set G)) d) *
      Nat.card (centralizer ({w} : Set G) ⊓ MulAction.stabilizer G d : Subgroup G) =
        Nat.card (centralizer ({w} : Set G)) := by
  set K : Subgroup G := centralizer ({w} : Set G) with hK
  have h2 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K d)
  rw [Nat.card_prod] at h2
  have h3 : Nat.card (MulAction.stabilizer K d) =
      Nat.card (K ⊓ MulAction.stabilizer G d : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1 : G), Subgroup.mem_inf.mpr ⟨k.1.2, MulAction.mem_stabilizer_iff.mpr (by
          have := MulAction.mem_stabilizer_iff.mp k.2
          simpa [Subgroup.smul_def] using this)⟩⟩
        invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩, MulAction.mem_stabilizer_iff.mpr (by
          have := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp g.2).2
          simpa [Subgroup.smul_def] using this)⟩
        left_inv := fun k => rfl
        right_inv := fun g => rfl }
  rw [h3] at h2
  exact h2

theorem card_centralizer_two_points [Finite G] (w : G) (d d' : X) (F : Finset X)
    (hF : ∀ p : X, w • p = p → p ∈ F) (hd : w • d = d) (hd' : w • d' = d') {α β : ℕ}
    (hα : Nat.card (centralizer ({w} : Set G) ⊓ MulAction.stabilizer G d : Subgroup G) = α)
    (hβ : Nat.card (centralizer ({w} : Set G) ⊓ MulAction.stabilizer G d' : Subgroup G) ≤ β)
    (hβα : β < α) :
    ∃ m m' : ℕ, Nat.card (centralizer ({w} : Set G)) = m * α ∧
      Nat.card (centralizer ({w} : Set G)) ≤ m' * β ∧ 1 ≤ m ∧ m + m' ≤ F.card := by
  classical
  set K : Subgroup G := centralizer ({w} : Set G) with hK
  have e1 := card_centralizer_eq_orbit_mul w d
  have e2 := card_centralizer_eq_orbit_mul w d'
  rw [hα] at e1
  have : Finite (MulAction.orbit K d) := Set.finite_range _
  have : Finite (MulAction.orbit K d') := Set.finite_range _
  have : Nonempty (MulAction.orbit K d) := ⟨⟨d, MulAction.mem_orbit_self d⟩⟩
  have hpos : 0 < Nat.card (MulAction.orbit K d) := Nat.card_pos
  have hdisj : Disjoint (MulAction.orbit K d : Set X) (MulAction.orbit K d' : Set X) := by
    rw [Set.disjoint_left]
    intro p hp hp'
    have h1 : MulAction.orbit K p = MulAction.orbit K d := MulAction.orbit_eq_iff.mpr hp
    have h2 : MulAction.orbit K p = MulAction.orbit K d' := MulAction.orbit_eq_iff.mpr hp'
    have h3 : MulAction.orbit K d = MulAction.orbit K d' := h1.symm.trans h2
    rw [← h3] at e2
    have : Nat.card (K ⊓ MulAction.stabilizer G d' : Subgroup G) = α := by
      have := e1.trans e2.symm
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    omega
  refine ⟨Nat.card (MulAction.orbit K d), Nat.card (MulAction.orbit K d'), e1.symm, ?_, hpos, ?_⟩
  · rw [← e2]
    exact Nat.mul_le_mul_left _ hβ
  · have hsub : (MulAction.orbit K d : Set X) ∪ (MulAction.orbit K d' : Set X) ⊆ (F : Set X) := by
      intro p hp
      rcases hp with hp | hp
      · exact hF p (orbit_centralizer_subset w d hd hp)
      · exact hF p (orbit_centralizer_subset w d' hd' hp)
    have := Set.ncard_le_ncard hsub F.finite_toSet
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_coe_finset] at this
    simpa [Nat.card_coe_set_eq] using this

end Fixed

section Class

theorem card_stabilizer_conjAct' {G : Type*} [Group G] (x : G) :
    Nat.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨ConjAct.ofConjAct g.1, ?_⟩
      invFun := fun g => ⟨ConjAct.toConjAct g.1, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  · obtain ⟨g, hg⟩ := g
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at hg
    exact Subgroup.mem_centralizer_singleton_iff.2 hg
  · obtain ⟨g, hg⟩ := g
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
      mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hg

theorem card_centralizer_mul_le {H : Type*} [Group H] [Finite H] (t : H) {N : ℕ}
    (hN : N ≤ Nat.card (MulAction.orbit (ConjAct H) t)) :
    Nat.card (Subgroup.centralizer ({t} : Set H)) * N ≤ Nat.card H := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct H) t)
  rw [Nat.card_prod, Nat.card_congr ConjAct.toConjAct.symm.toEquiv, card_stabilizer_conjAct'] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_right _ hN

theorem card_centralizer_inf_eq {G : Type*} [Group G] (H : Subgroup G) (t : G) (ht : t ∈ H) :
    Nat.card (centralizer ({t} : Set G) ⊓ H : Subgroup G) =
      Nat.card (centralizer ({(⟨t, ht⟩ : H)} : Set H)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.mp g.2).2⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).1))⟩
      invFun := fun g => ⟨g.1.1, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2)), g.1.2⟩⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

end Class

section Core

variable {T : Type*} [Group T]

@[expose] def FiveCoreAt (w : T) : Prop :=
  ∃ F : Subgroup (centralizer ({w} : Set T)), F.Normal ∧ IsPGroup 5 F ∧
    centralizer (F : Set (centralizer ({w} : Set T))) ≤ F

@[expose] def FiveCore (T : Type*) [Group T] : Prop :=
  ∀ w : T, orderOf w = 5 → FiveCoreAt w

@[expose] def FiveCoreAt' (w : T) : Prop :=
  ∃ Q : Subgroup T, Q ≤ centralizer ({w} : Set T) ∧
    (∀ g ∈ centralizer ({w} : Set T), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧ IsPGroup 5 Q ∧
    ∀ g ∈ centralizer ({w} : Set T), (∀ q ∈ Q, g * q = q * g) → g ∈ Q

theorem fiveCoreAt_of_fiveCoreAt' {w : T} (h : FiveCoreAt' w) : FiveCoreAt w := by
  obtain ⟨Q, hQC, hQn, hQp, hQc⟩ := h
  refine ⟨Q.subgroupOf (centralizer ({w} : Set T)), ⟨fun n hn g => ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g.1 g.2 n.1 hn
  · exact hQp.of_injective (Subgroup.subgroupOfEquivOfLe hQC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQC).injective
  · intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hQc g.1 g.2
    intro q hq
    have := Subgroup.mem_centralizer_iff.mp hg ⟨q, hQC hq⟩
      (show (⟨q, hQC hq⟩ : centralizer ({w} : Set T)) ∈ Q.subgroupOf (centralizer ({w} : Set T))
        from Subgroup.mem_subgroupOf.mpr hq)
    exact congrArg Subtype.val this.symm

theorem fiveCoreAt'_of_fiveCoreAt {w : T} (h : FiveCoreAt w) : FiveCoreAt' w := by
  obtain ⟨F, hFn, hFp, hFc⟩ := h
  refine ⟨F.map (centralizer ({w} : Set T)).subtype, Subgroup.map_subtype_le F, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨f, hf, rfl⟩
    refine ⟨⟨g, hg⟩ * f * ⟨g, hg⟩⁻¹, hFn.conj_mem f hf ⟨g, hg⟩, ?_⟩
    rfl
  · exact hFp.of_surjective ((centralizer ({w} : Set T)).subtype.subgroupMap F)
      ((centralizer ({w} : Set T)).subtype.subgroupMap_surjective F)
  · intro g hg hgc
    have : (⟨g, hg⟩ : centralizer ({w} : Set T)) ∈ F := by
      apply hFc
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      apply Subtype.ext
      exact hgc f.1 ⟨f, hf, rfl⟩ |>.symm
    exact ⟨⟨g, hg⟩, this, rfl⟩

theorem eq_bot_of_fiveCoreAt' [Finite T] {w : T} (h : FiveCoreAt' w) (N : Subgroup T)
    (hNC : N ≤ centralizer ({w} : Set T))
    (hNn : ∀ g ∈ centralizer ({w} : Set T), ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hNp : ¬ 5 ∣ Nat.card N) : N = ⊥ := by
  obtain ⟨Q, hQC, hQn, hQp, hQc⟩ := h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hNQ : N ⊓ Q = ⊥ := by
    have hp : IsPGroup 5 (N ⊓ Q : Subgroup T) := hQp.to_le inf_le_right
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hp
    have hdvd : Nat.card (N ⊓ Q : Subgroup T) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    rw [hm] at hdvd
    have hm0 : m = 0 := by
      by_contra hm0
      exact hNp ((dvd_pow_self 5 hm0).trans hdvd)
    rw [hm0, pow_zero] at hm
    exact Subgroup.eq_bot_of_card_eq _ hm
  refine (Subgroup.eq_bot_iff_forall _).mpr fun n hn => ?_
  have hnQ : n ∈ Q := by
    apply hQc n (hNC hn)
    intro q hq
    have h1 : n * q * n⁻¹ * q⁻¹ ∈ Q :=
      Subgroup.mul_mem _ (hQn n (hNC hn) q hq) (Subgroup.inv_mem _ hq)
    have h2 : n * q * n⁻¹ * q⁻¹ ∈ N := by
      have h3 : q * n⁻¹ * q⁻¹ ∈ N := hNn q (hQC hq) n⁻¹ (Subgroup.inv_mem _ hn)
      have h5 : n * (q * n⁻¹ * q⁻¹) ∈ N := Subgroup.mul_mem _ hn h3
      simpa [mul_assoc] using h5
    have h4 : n * q * n⁻¹ * q⁻¹ = 1 := by
      have : n * q * n⁻¹ * q⁻¹ ∈ N ⊓ Q := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hNQ] at this
      exact Subgroup.mem_bot.mp this
    calc n * q = n * q * n⁻¹ * q⁻¹ * (q * n) := by group
      _ = q * n := by rw [h4, one_mul]
  have : n ∈ N ⊓ Q := Subgroup.mem_inf.mpr ⟨hn, hnQ⟩
  rw [hNQ] at this
  exact this

theorem eq_bot_of_fiveCoreAt [Finite T] {w : T} (h : FiveCoreAt w) (N : Subgroup T)
    (hNC : N ≤ centralizer ({w} : Set T))
    (hNn : ∀ g ∈ centralizer ({w} : Set T), ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hNp : ¬ 5 ∣ Nat.card N) : N = ⊥ :=
  eq_bot_of_fiveCoreAt' (fiveCoreAt'_of_fiveCoreAt h) N hNC hNn hNp

theorem fiveCoreAt'_map {T' : Type*} [Group T'] (e : T ≃* T') {w : T} (h : FiveCoreAt' w) :
    FiveCoreAt' (e w) := by
  obtain ⟨Q, hQC, hQn, hQp, hQc⟩ := h
  refine ⟨Q.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)]
  · rintro g' hg' _ ⟨q, hq, rfl⟩
    have hg : e.symm g' ∈ centralizer ({w} : Set T) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg'
    refine ⟨e.symm g' * q * (e.symm g')⁻¹, hQn _ hg q hq, ?_⟩
    simp
  · exact hQp.of_surjective (e.toMonoidHom.subgroupMap Q) (e.toMonoidHom.subgroupMap_surjective Q)
  · intro g' hg' hc
    have hg : e.symm g' ∈ centralizer ({w} : Set T) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg'
    have := hQc _ hg (fun q hq => by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc (e q) ⟨q, hq, rfl⟩)
    exact ⟨e.symm g', this, by simp⟩

theorem centralizer_pow_eq {w : T} (hw : orderOf w = 5) {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5) :
    centralizer ({w ^ k} : Set T) = centralizer ({w} : Set T) := by
  have hw5 : w ^ 5 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hinv : (w ^ k) ^ (k ^ 3) = w := by
    rw [← pow_mul]
    have : w ^ (k * k ^ 3) = w ^ ((k * k ^ 3) % 5) := by
      rw [← pow_mod_orderOf, hw]
    rw [this]
    have h1 : (k * k ^ 3) % 5 = 1 := by
      interval_cases k <;> norm_num
    rw [h1, pow_one]
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have : g * (w ^ k) ^ (k ^ 3) = (w ^ k) ^ (k ^ 3) * g := (Commute.pow_right h _).eq
    rwa [hinv] at this
  · intro h
    exact (Commute.pow_right h k).eq

theorem fiveCoreAt'_pow {w : T} (hw : orderOf w = 5) {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5)
    (h : FiveCoreAt' w) : FiveCoreAt' (w ^ k) := by
  obtain ⟨Q, hQC, hQn, hQp, hQc⟩ := h
  rw [FiveCoreAt', centralizer_pow_eq hw hk0 hk5]
  exact ⟨Q, hQC, hQn, hQp, hQc⟩

theorem fiveCoreAt'_of_conj_pow {w r : T} (hr : orderOf r = 5) {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5)
    (g : T) (hg : g * w * g⁻¹ = r ^ k) (h : FiveCoreAt' r) : FiveCoreAt' w := by
  have h1 := fiveCoreAt'_pow hr hk0 hk5 h
  rw [← hg] at h1
  have h2 := fiveCoreAt'_map (MulAut.conj g⁻¹) h1
  simpa [MulAut.conj_apply, mul_assoc] using h2

theorem fiveCoreAt'_of_normal_sub {w : T} {Q U : Subgroup T}
    (hC : centralizer ({w} : Set T) = U) (hQU : Q ≤ U) (hn : (Q.subgroupOf U).Normal)
    (hp : IsPGroup 5 Q) (hc : centralizer (Q : Set T) ⊓ U ≤ Q) : FiveCoreAt' w := by
  refine ⟨Q, hC ▸ hQU, ?_, hp, ?_⟩
  · intro g hg q hq
    rw [hC] at hg
    have := hn.conj_mem ⟨q, hQU hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp this
  · intro g hg hcomm
    rw [hC] at hg
    refine hc (Subgroup.mem_inf.mpr ⟨?_, hg⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hcomm q hq).symm

end Core

end CFSG.RankThree.PartOne
