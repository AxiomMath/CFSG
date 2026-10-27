module

public import CFSG.Quasithin.Recognition.M22WittSteiner
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut

public section

namespace CFSG.Quasithin.M22Witt

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open scoped Pointwise

theorem card_inf_eq
    {G : Type*} [Group G] {K H : Subgroup G} (Φ : K ≃* stabilizer M22 (0 : Fin 22))
    (hH : ∀ k : K, (k : G) ∈ H ↔ (Φ k : M22) ∈ m22PtHexStab) : Nat.card ↥(K ⊓ H) = 960 := by
  rw [← card_m22PtHexStab]
  refine Nat.card_congr
    { toFun := fun g => ⟨(Φ ⟨g, (Subgroup.mem_inf.mp g.2).1⟩ : M22),
        (hH _).mp (Subgroup.mem_inf.mp g.2).2⟩
      invFun := fun p => ⟨(Φ.symm ⟨p, (Subgroup.mem_inf.mp p.2).1⟩ : G),
        Subgroup.mem_inf.mpr ⟨(Φ.symm _).2, (hH _).mpr (by
          rw [MulEquiv.apply_symm_apply]; exact p.2)⟩⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
      right_inv := fun p => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply] }

namespace WittData

variable {G : Type*} [Group G] [Finite G] (D : WittData G)

omit [Finite G] in
theorem card_K :
    Nat.card D.K = 20160 := by
  rw [Nat.card_congr D.Φ.toEquiv, card_stabilizer_point]

omit [Finite G] in
include D in
theorem card_G
    : Nat.card G = 443520 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.K, D.card_quotient, D.card_K]

omit [Finite G] in
theorem card_K_inf_H
    : Nat.card ↥(D.K ⊓ D.H) = 960 := card_inf_eq D.Φ D.hH

omit [Finite G] in
theorem card_H
    : Nat.card D.H = 5760 := by
  rw [← Subgroup.relIndex_mul_card (H := D.K) (K := D.H), D.hH6, D.card_K_inf_H]

theorem exists_mulEquiv
    : ∃ Ψ : G ≃* M22, D.K.map Ψ.toMonoidHom = stabilizer M22 (0 : Fin 22) ∧
    D.H.map Ψ.toMonoidHom = m22HexStab := by
  classical
  let _ : Fintype (G ⧸ D.K) := Fintype.ofFinite _
  obtain ⟨e, he⟩ := steinerTriple_iso D.isSteinerTriple_blocks isSteinerTriple_hexads
  set ρ : G →* Equiv.Perm (Fin 22) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ D.K)) with hρ
  have hρe : ∀ (g : G) (ω : G ⧸ D.K), ρ g (e ω) = e (g • ω) := by
    intro g ω
    change e (g • e.symm (e ω)) = e (g • ω)
    rw [e.symm_apply_apply]
  have hmapB : ∀ (g : G) (B : Finset (G ⧸ D.K)),
      (B.map e.toEmbedding).map (ρ g).toEmbedding = (g • B).map e.toEmbedding := by
    intro g B
    ext y
    simp only [Finset.mem_map, Finset.mem_smul_finset, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨g • ω, ⟨ω, hω, rfl⟩, (hρe g ω).symm⟩
    · rintro ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨e ω, ⟨ω, hω, rfl⟩, hρe g ω⟩
  have hρmem : ∀ g, ρ g ∈ hexadAut := by
    intro g
    refine mem_blockAut.mpr fun X => ?_
    have hX : X = (X.map e.symm.toEmbedding).map e.toEmbedding := by
      ext y
      simp
    rw [hX, hmapB, ← he, ← he, D.smul_mem_blocks_iff]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hfix : ∀ ω : G ⧸ D.K, g • ω = ω := by
      intro ω
      apply e.injective
      rw [← hρe, hg, Equiv.Perm.one_apply]
    have hgK : g ∈ D.K := (D.smul_infty_eq_iff g).mp (hfix _)
    have hΦ : D.Φ ⟨g, hgK⟩ = 1 := by
      refine Subtype.ext (Subtype.ext (Equiv.ext fun y => ?_))
      obtain ⟨ω, rfl⟩ := D.psi_surjective y
      have h1 := D.psi_smul ⟨g, hgK⟩ ω
      rw [hfix ω, smul_m22_def] at h1
      exact h1.symm
    have h1 : (⟨g, hgK⟩ : D.K) = 1 := D.Φ.injective (hΦ.trans (map_one D.Φ).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hcard : Nat.card ρ.range = Nat.card M22 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, D.card_G, card_M22']
  have hrange : ρ.range = M22 :=
    eq_of_relIndex_le_six (by rintro _ ⟨g, rfl⟩; exact hρmem g)
      (by rw [card_hexadAut.2]; norm_num) hcard CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      (by rw [card_M22']; norm_num)
  set Ψ₀ : G ≃* M22 := (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hrange)
    with hΨ₀def
  have hΨ₀ : ∀ g, ((Ψ₀ g : M22) : Equiv.Perm (Fin 22)) = ρ g := fun g => rfl
  have hθb : D.theta.map e.toEmbedding ∈ hexads := (he _).mp D.theta_mem_blocks
  have hinθ : e D.infty ∈ D.theta.map e.toEmbedding :=
    Finset.mem_map_of_mem _ D.infty_mem_theta
  obtain ⟨m, hm0, hmθ⟩ := exists_smul_flag hθb hinθ
  set Ψ : G ≃* M22 := Ψ₀.trans (MulAut.conj m) with hΨdef
  have hΨapp : ∀ g, Ψ g = m * Ψ₀ g * m⁻¹ := fun g => rfl
  have hΨe : ∀ (g : G) (ω : G ⧸ D.K), Ψ g • (m • e ω) = m • e (g • ω) := by
    intro g ω
    rw [hΨapp, mul_smul, mul_smul, inv_smul_smul, smul_m22_def (Ψ₀ g), hΨ₀, hρe]
  have hΨX : ∀ (g : G) (X : Finset (G ⧸ D.K)),
      Ψ g • (m • X.map e.toEmbedding) = m • ((g • X).map e.toEmbedding) := by
    intro g X
    ext y
    simp only [Finset.mem_smul_finset, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨_, ⟨_, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
      exact ⟨e (g • ω), ⟨g • ω, ⟨ω, hω, rfl⟩, rfl⟩, (hΨe g ω).symm⟩
    · rintro ⟨_, ⟨_, ⟨ω, hω, rfl⟩, rfl⟩, rfl⟩
      exact ⟨m • e ω, ⟨e ω, ⟨ω, hω, rfl⟩, rfl⟩, hΨe g ω⟩
  refine ⟨Ψ, ?_, ?_⟩
  · ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hm0, MulEquiv.coe_toMonoidHom, hΨe,
        D.smul_infty_of_mem hg]
    · intro hx
      refine ⟨Ψ.symm x, ?_, Ψ.apply_symm_apply x⟩
      rw [← D.smul_infty_eq_iff]
      apply e.injective
      apply smul_left_cancel m
      rw [← hΨe, Ψ.apply_symm_apply, hm0]
      exact MulAction.mem_stabilizer_iff.mp hx
  · rw [← stabilizer_m22HexadF]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨h, hh, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hmθ, MulEquiv.coe_toMonoidHom, hΨX,
        D.smul_theta hh]
    · rw [card_stabilizer_hexad m22HexadF_mem_hexads,
        Subgroup.card_map_of_injective Ψ.injective, D.card_H]

end WittData

theorem nonempty_mulEquiv_m22_of_witt
    {G : Type*} [Group G] [Finite G] {K H : Subgroup G}
    (Φ : K ≃* stabilizer M22 (0 : Fin 22)) {t : G}
    (ht : ∀ k : K, t⁻¹ * (k : G) * t ∈ K ↔ (Φ k : M22) ∈ m22TwoStab)
    (hG : ∀ g : G, g ∈ K ∨ ∃ a ∈ K, ∃ b ∈ K, g = a * t * b)
    (hH : ∀ k : K, (k : G) ∈ H ↔ (Φ k : M22) ∈ m22PtHexStab)
    (hH6 : K.relIndex H = 6) :
    ∃ Ψ : G ≃* M22, K.map Ψ.toMonoidHom = stabilizer M22 (0 : Fin 22) ∧
      H.map Ψ.toMonoidHom = m22HexStab :=
  (WittData.mk K H Φ t ht hG hH hH6).exists_mulEquiv

end CFSG.Quasithin.M22Witt
