module

public import CFSG.Quasithin.Recognition.M22WittData

public section

namespace CFSG.Quasithin.M22Witt

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open scoped Pointwise

structure WittData (G : Type*) [Group G] where
  K : Subgroup G
  H : Subgroup G
  Φ : K ≃* stabilizer M22 (0 : Fin 22)
  t : G
  ht : ∀ k : K, t⁻¹ * (k : G) * t ∈ K ↔ (Φ k : M22) ∈ m22TwoStab
  hG : ∀ g : G, g ∈ K ∨ ∃ a ∈ K, ∃ b ∈ K, g = a * t * b
  hH : ∀ k : K, (k : G) ∈ H ↔ (Φ k : M22) ∈ m22PtHexStab
  hH6 : K.relIndex H = 6

namespace WittData

variable {G : Type*} [Group G] (D : WittData G)

abbrev infty : G ⧸ D.K := ((1 : G) : G ⧸ D.K)

theorem coe_eq_infty_iff (g : G) : (g : G ⧸ D.K) = D.infty ↔ g ∈ D.K := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem smul_infty (g : G) : g • D.infty = (g : G ⧸ D.K) := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

theorem smul_infty_eq_iff (g : G) : g • D.infty = D.infty ↔ g ∈ D.K := by
  rw [smul_infty, coe_eq_infty_iff]

theorem smul_infty_of_mem {k : G} (hk : k ∈ D.K) : k • D.infty = D.infty :=
  (D.smul_infty_eq_iff k).mpr hk

theorem t_not_mem :
    D.t ∉ D.K := by
  intro htK
  obtain ⟨g, hg, hg2⟩ := exists_stabilizer_zero_not_mem_two
  have h := (D.ht (D.Φ.symm ⟨g, hg⟩)).mp
    (D.K.mul_mem (D.K.mul_mem (D.K.inv_mem htK) (D.Φ.symm ⟨g, hg⟩).2) htK)
  rw [MulEquiv.apply_symm_apply] at h
  exact hg2 h

abbrev pt : G ⧸ D.K := (D.t : G ⧸ D.K)

theorem smul_pt_eq_iff (k : D.K) : (k : G) • D.pt = D.pt ↔ (D.Φ k : M22) ∈ m22TwoStab := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
  have e : ((k : G) * D.t)⁻¹ * D.t = D.t⁻¹ * ((k⁻¹ : D.K) : G) * D.t := by
    rw [Subgroup.coe_inv]
    group
  rw [e, D.ht, map_inv, Subgroup.coe_inv, inv_mem_iff]

theorem pt_ne_infty
    : D.pt ≠ D.infty := fun h => D.t_not_mem ((D.coe_eq_infty_iff _).mp h)

theorem exists_smul_pt {ω : G ⧸ D.K} (hω : ω ≠ D.infty) : ∃ k : D.K, (k : G) • D.pt = ω := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rcases D.hG g with hg | ⟨a, ha, b, hb, rfl⟩
  · exact absurd ((D.coe_eq_infty_iff g).mpr hg) hω
  · refine ⟨⟨a, ha⟩, ?_⟩
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have e : (a * D.t)⁻¹ * (a * D.t * b) = b := by group
    rw [e]
    exact hb

theorem smul_pt_ne_infty
    (k : D.K) : (k : G) • D.pt ≠ D.infty := by
  intro h
  apply D.pt_ne_infty
  have := congrArg (fun ω => (k : G)⁻¹ • ω) h
  simp only [inv_smul_smul] at this
  rw [this, D.smul_infty_of_mem (D.K.inv_mem k.2)]

@[expose] noncomputable def psi (ω : G ⧸ D.K) : Fin 22 := by
  classical
  exact if h : ∃ k : D.K, (k : G) • D.pt = ω then (D.Φ h.choose : M22) • (1 : Fin 22) else 0

theorem smul_zero_eq (k : D.K) : (D.Φ k : M22) • (0 : Fin 22) = 0 :=
  MulAction.mem_stabilizer_iff.mp (D.Φ k).2

theorem eq_of_smul_pt {k k' : D.K} (h : (k : G) • D.pt = (k' : G) • D.pt) :
    (D.Φ k : M22) • (1 : Fin 22) = (D.Φ k' : M22) • 1 := by
  have h1 : ((k⁻¹ * k' : D.K) : G) • D.pt = D.pt := by
    rw [Subgroup.coe_mul, mul_smul, ← h, Subgroup.coe_inv, inv_smul_smul]
  have h2 := (D.smul_pt_eq_iff _).mp h1
  have h3 := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h2).2
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_eq_iff] at h3
  exact h3.symm

theorem psi_smul_pt (k : D.K) : D.psi ((k : G) • D.pt) = (D.Φ k : M22) • (1 : Fin 22) := by
  have hex : ∃ k' : D.K, (k' : G) • D.pt = (k : G) • D.pt := ⟨k, rfl⟩
  unfold psi
  rw [dite_eq_left hex]
  exact D.eq_of_smul_pt hex.choose_spec

theorem psi_infty
    : D.psi D.infty = 0 := by
  have hne : ¬∃ k : D.K, (k : G) • D.pt = D.infty := by
    rintro ⟨k, hk⟩
    exact D.smul_pt_ne_infty k hk
  unfold psi
  rw [dite_eq_right hne]

theorem smul_one_ne_zero (k : D.K) : (D.Φ k : M22) • (1 : Fin 22) ≠ 0 := by
  intro h
  exact absurd (smul_left_cancel _ (h.trans (D.smul_zero_eq k).symm)) (by decide)

theorem psi_smul
    (k : D.K) (ω : G ⧸ D.K) : D.psi ((k : G) • ω) = (D.Φ k : M22) • D.psi ω := by
  by_cases hω : ω = D.infty
  · rw [hω, D.smul_infty_of_mem k.2, D.psi_infty, D.smul_zero_eq]
  · obtain ⟨k₀, rfl⟩ := D.exists_smul_pt hω
    rw [← mul_smul, ← Subgroup.coe_mul, D.psi_smul_pt, D.psi_smul_pt, map_mul, Subgroup.coe_mul,
      mul_smul]

theorem psi_injective
    : Function.Injective D.psi := by
  intro ω ω' h
  by_cases hω : ω = D.infty <;> by_cases hω' : ω' = D.infty
  · rw [hω, hω']
  · obtain ⟨k', rfl⟩ := D.exists_smul_pt hω'
    rw [hω, D.psi_infty, D.psi_smul_pt] at h
    exact absurd h.symm (D.smul_one_ne_zero k')
  · obtain ⟨k, rfl⟩ := D.exists_smul_pt hω
    rw [hω', D.psi_infty, D.psi_smul_pt] at h
    exact absurd h (D.smul_one_ne_zero k)
  · obtain ⟨k, rfl⟩ := D.exists_smul_pt hω
    obtain ⟨k', rfl⟩ := D.exists_smul_pt hω'
    rw [D.psi_smul_pt, D.psi_smul_pt] at h
    have hmem : (D.Φ (k⁻¹ * k') : M22) ∈ m22TwoStab := by
      refine Subgroup.mem_inf.mpr ⟨(D.Φ _).2, MulAction.mem_stabilizer_iff.mpr ?_⟩
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← h, inv_smul_smul]
    have h2 := (D.smul_pt_eq_iff _).mpr hmem
    rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_eq_iff] at h2
    exact h2.symm

theorem psi_surjective
    : Function.Surjective D.psi := by
  intro y
  by_cases hy : y = 0
  · exact ⟨D.infty, by rw [hy, D.psi_infty]⟩
  · obtain ⟨g, hg, hg1⟩ := exists_mem_stabilizer_smul_eq (0 : Fin 22) (x := 1) (y := y)
      (by decide) hy
    refine ⟨((D.Φ.symm ⟨g, hg⟩ : D.K) : G) • D.pt, ?_⟩
    rw [D.psi_smul_pt, MulEquiv.apply_symm_apply]
    exact hg1

@[expose] noncomputable def psiEquiv
    : G ⧸ D.K ≃ Fin 22 :=
  Equiv.ofBijective D.psi ⟨D.psi_injective, D.psi_surjective⟩

theorem psiEquiv_apply
    (ω : G ⧸ D.K) : D.psiEquiv ω = D.psi ω := rfl

theorem card_quotient
    : Nat.card (G ⧸ D.K) = 22 := by
  rw [Nat.card_congr D.psiEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

variable [Finite G]

@[expose] noncomputable def theta : Finset (G ⧸ D.K) :=
  (Set.finite_range fun h : D.H => (h : G) • D.infty).toFinset

theorem mem_theta {ω : G ⧸ D.K} : ω ∈ D.theta ↔ ∃ h : D.H, (h : G) • D.infty = ω := by
  rw [theta, Set.Finite.mem_toFinset, Set.mem_range]

theorem infty_mem_theta : D.infty ∈ D.theta :=
  D.mem_theta.mpr ⟨1, by rw [Subgroup.coe_one, one_smul]⟩

theorem smul_mem_theta {h : G} (hh : h ∈ D.H) {ω : G ⧸ D.K} (hω : ω ∈ D.theta) :
    h • ω ∈ D.theta := by
  obtain ⟨h', rfl⟩ := D.mem_theta.mp hω
  exact D.mem_theta.mpr ⟨⟨h, hh⟩ * h', by rw [Subgroup.coe_mul, mul_smul]⟩

theorem smul_theta [DecidableEq (G ⧸ D.K)] {h : G} (hh : h ∈ D.H) : h • D.theta = D.theta := by
  ext ω
  rw [← Finset.inv_smul_mem_iff]
  constructor
  · intro hω
    have := D.smul_mem_theta hh hω
    rwa [smul_inv_smul] at this
  · intro hω
    exact D.smul_mem_theta (D.H.inv_mem hh) hω

theorem card_theta : D.theta.card = 6 := by
  have hset : (D.theta : Set (G ⧸ D.K)) = orbit D.H D.infty := by
    ext ω
    rw [Finset.mem_coe, D.mem_theta]
    rfl
  have hstab : stabilizer D.H D.infty = D.K.subgroupOf D.H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def,
      D.smul_infty_eq_iff]
  rw [← Set.ncard_coe_finset, hset, ← MulAction.index_stabilizer, hstab]
  exact D.hH6

theorem psi_theta
    : D.theta.map D.psiEquiv.toEmbedding = m22HexadF := by
  apply eq_m22HexadF_of_invariant
  · exact Finset.mem_map.mpr ⟨D.infty, D.infty_mem_theta, D.psi_infty⟩
  · rw [Finset.card_map, D.card_theta]
  · intro p hp x hx
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_map.mp hx
    have hp0 : p ∈ stabilizer M22 (0 : Fin 22) := (Subgroup.mem_inf.mp hp).1
    have hk : (D.Φ (D.Φ.symm ⟨p, hp0⟩) : M22) = p := by rw [MulEquiv.apply_symm_apply]
    have hkH : ((D.Φ.symm ⟨p, hp0⟩ : D.K) : G) ∈ D.H := (D.hH _).mpr (by rw [hk]; exact hp)
    refine Finset.mem_map.mpr ⟨_, D.smul_mem_theta hkH hω, ?_⟩
    rw [Equiv.coe_toEmbedding, psiEquiv_apply, psiEquiv_apply, D.psi_smul, hk]

variable [DecidableEq (G ⧸ D.K)]

@[expose] noncomputable def blocks : Finset (Finset (G ⧸ D.K)) :=
  (Set.finite_range fun g : G => g • D.theta).toFinset

theorem mem_blocks {B : Finset (G ⧸ D.K)} : B ∈ D.blocks ↔ ∃ g : G, g • D.theta = B := by
  rw [blocks, Set.Finite.mem_toFinset, Set.mem_range]

theorem smul_mem_blocks (g : G) {B : Finset (G ⧸ D.K)} (hB : B ∈ D.blocks) :
    g • B ∈ D.blocks := by
  obtain ⟨g', rfl⟩ := D.mem_blocks.mp hB
  exact D.mem_blocks.mpr ⟨g * g', mul_smul _ _ _⟩

theorem smul_mem_blocks_iff (g : G) (B : Finset (G ⧸ D.K)) :
    g • B ∈ D.blocks ↔ B ∈ D.blocks := by
  refine ⟨fun h => ?_, D.smul_mem_blocks g⟩
  have := D.smul_mem_blocks g⁻¹ h
  rwa [inv_smul_smul] at this

theorem theta_mem_blocks : D.theta ∈ D.blocks := D.mem_blocks.mpr ⟨1, one_smul _ _⟩

theorem card_of_mem_blocks {B : Finset (G ⧸ D.K)} (hB : B ∈ D.blocks) : B.card = 6 := by
  obtain ⟨g, rfl⟩ := D.mem_blocks.mp hB
  rw [Finset.card_smul_finset, D.card_theta]

theorem eq_smul_theta_of_infty_mem {B : Finset (G ⧸ D.K)} (hB : B ∈ D.blocks)
    (h : D.infty ∈ B) : ∃ k : D.K, B = (k : G) • D.theta := by
  obtain ⟨g, rfl⟩ := D.mem_blocks.mp hB
  rw [← Finset.inv_smul_mem_iff] at h
  obtain ⟨h', hh'⟩ := D.mem_theta.mp h
  have hgh : g * h' ∈ D.K := by
    rw [← D.smul_infty_eq_iff, mul_smul, hh', smul_inv_smul]
  refine ⟨⟨g * h', hgh⟩, ?_⟩
  rw [mul_smul, D.smul_theta h'.2]

omit [Finite G] in
theorem map_smul_finset
    (k : D.K) (X : Finset (G ⧸ D.K)) :
    ((k : G) • X).map D.psiEquiv.toEmbedding = (D.Φ k : M22) • X.map D.psiEquiv.toEmbedding := by
  ext y
  simp only [Finset.mem_map, Finset.mem_smul_finset, Equiv.coe_toEmbedding, psiEquiv_apply]
  constructor
  · rintro ⟨ω, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨D.psi x, ⟨x, hx, rfl⟩, (D.psi_smul k x).symm⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(k : G) • x, ⟨x, hx, rfl⟩, D.psi_smul k x⟩

theorem map_smul_theta
    (k : D.K) :
    ((k : G) • D.theta).map D.psiEquiv.toEmbedding = (D.Φ k : M22) • m22HexadF := by
  rw [D.map_smul_finset, D.psi_theta]

theorem isSteinerTriple_blocks
    [Fintype (G ⧸ D.K)] : IsSteinerTriple D.blocks := by
  refine ⟨?_, fun B hB => D.card_of_mem_blocks hB, fun T hT => ?_⟩
  · rw [Fintype.card_congr D.psiEquiv, Fintype.card_fin]
  obtain ⟨x, hx⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set T' := g⁻¹ • T with hT'
  have hinf : D.infty ∈ T' := by
    have := Finset.smul_mem_smul_finset (a := g⁻¹) hx
    rwa [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel] at this
  have hcT' : T'.card = 3 := by rw [hT', Finset.card_smul_finset, hT]
  have hcm : (T'.map D.psiEquiv.toEmbedding).card = 3 := by rw [Finset.card_map, hcT']
  obtain ⟨X, ⟨hX, hTX⟩, hXu⟩ := isSteinerTriple_hexads.2.2 _ hcm
  have h0X : (0 : Fin 22) ∈ X := hTX (Finset.mem_map.mpr ⟨D.infty, hinf, D.psi_infty⟩)
  obtain ⟨kb, hkb, hkbX⟩ := exists_stabilizer_zero_smul_eq hX h0X
  have hkΦ : (D.Φ (D.Φ.symm ⟨kb, hkb⟩) : M22) = kb := by rw [MulEquiv.apply_symm_apply]
  set k : D.K := D.Φ.symm ⟨kb, hkb⟩ with hk
  have hBmap : ((k : G) • D.theta).map D.psiEquiv.toEmbedding = X := by
    rw [D.map_smul_theta, hkΦ, hkbX]
  have hT'B : T' ⊆ (k : G) • D.theta := by
    rw [← Finset.map_subset_map (f := D.psiEquiv.toEmbedding), hBmap]
    exact hTX
  have hTeq : T = g • T' := by rw [hT', smul_inv_smul]
  refine ⟨g • ((k : G) • D.theta), ⟨D.smul_mem_blocks g (D.mem_blocks.mpr ⟨k, rfl⟩), ?_⟩, ?_⟩
  · rw [hTeq]
    exact Finset.smul_finset_subset_smul_finset hT'B
  · rintro B ⟨hB, hTB⟩
    have hB' : g⁻¹ • B ∈ D.blocks := D.smul_mem_blocks g⁻¹ hB
    have hTB' : T' ⊆ g⁻¹ • B := Finset.smul_finset_subset_smul_finset hTB
    obtain ⟨k₁, hk₁⟩ := D.eq_smul_theta_of_infty_mem hB' (hTB' hinf)
    have h1 : (g⁻¹ • B).map D.psiEquiv.toEmbedding = X := by
      refine hXu _ ⟨?_, Finset.map_subset_map.mpr hTB'⟩
      rw [hk₁, D.map_smul_theta]
      exact smul_mem_hexads _ m22HexadF_mem_hexads
    have h2 : g⁻¹ • B = (k : G) • D.theta := Finset.map_injective _ (h1.trans hBmap.symm)
    rw [← h2, smul_inv_smul]

end WittData

end CFSG.Quasithin.M22Witt
