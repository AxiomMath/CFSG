module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerKernelAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerKernelScalar
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerProjectiveBlocks

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module MulAction

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace MinimalBlock

variable (M : MinimalBlock k F)

theorem isPartition_blocks : Setoid.IsPartition M.blocks := by
  refine ⟨fun h => ?_, fun p => ?_⟩
  · obtain ⟨g, -, hgΔ⟩ := h
    obtain ⟨q, hq⟩ := M.nonempty
    have : g • q ∈ (∅ : Set (ℙ k F)) := hgΔ ▸ Set.smul_mem_smul_set hq
    exact this
  · obtain ⟨Γ, hΓ, hpΓ⟩ := M.exists_mem_blocks p
    exact ⟨Γ, ⟨hΓ, hpΓ⟩, fun Γ' hΓ' => M.eq_of_mem_blocks hΓ'.1 hΓ hΓ'.2 hpΓ⟩

theorem two_le_ncard_blocks [Finite F] : 2 ≤ M.blocks.ncard := by
  obtain ⟨p, hp⟩ : ∃ p, p ∉ M.Δ := by
    by_contra h
    push Not at h
    exact M.ne_univ (Set.eq_univ_iff_forall.mpr h)
  obtain ⟨Γ, hΓ, hpΓ⟩ := M.exists_mem_blocks p
  have hne : M.Δ ≠ Γ := fun e => hp (e ▸ hpΓ)
  exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨M.Δ, Γ, M.Δ_mem_blocks, hΓ, hne⟩

theorem twoTransitive_blocks (h2 : IsMultiplyPretransitive M.permK M.Δ 2) :
    ∀ Γ ∈ M.blocks, ∀ x ∈ Γ, ∀ y ∈ Γ, ∀ x' ∈ Γ, ∀ y' ∈ Γ, x ≠ y → x' ≠ y' →
      ∃ h ∈ M.K, h • x = x' ∧ h • y = y' := by
  have hΔ : ∀ x ∈ M.Δ, ∀ y ∈ M.Δ, ∀ x' ∈ M.Δ, ∀ y' ∈ M.Δ, x ≠ y → x' ≠ y' →
      ∃ h ∈ M.K, h • x = x' ∧ h • y = y' := by
    intro x hx y hy x' hx' y' hy' hxy hxy'
    have h2' : ∀ a b c d : M.Δ, a ≠ b → c ≠ d → ∃ g : M.permK, g • a = c ∧ g • b = d :=
      fun _ _ _ _ => is_two_pretransitive_iff.mp h2
    obtain ⟨σ, hσx, hσy⟩ := h2' ⟨x, hx⟩ ⟨y, hy⟩ ⟨x', hx'⟩ ⟨y', hy'⟩
      (fun e => hxy (congrArg Subtype.val e)) (fun e => hxy' (congrArg Subtype.val e))
    obtain ⟨h, hh⟩ := M.mem_permK.mp σ.2
    refine ⟨h, h.2, ?_, ?_⟩
    · have := congrArg Subtype.val ((hh ⟨x, hx⟩).symm.trans hσx)
      exact this
    · have := congrArg Subtype.val ((hh ⟨y, hy⟩).symm.trans hσy)
      exact this
  rintro Γ ⟨g, hg, rfl⟩ _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩ hab hab'
  obtain ⟨h, hK, hha, hhb⟩ := hΔ a ha b hb a' ha' b' hb'
    (fun e => hab (by simp only [e])) (fun e => hab' (by simp only [e]))
  refine ⟨g * h * g⁻¹, M.conj_mem_K hg hK, ?_, ?_⟩
  · simp only [mul_smul, inv_smul_smul, hha]
  · simp only [mul_smul, inv_smul_smul, hhb]

theorem false_of_isMultiplyPretransitive [Finite F] [CharP F 2] (hn : 3 ≤ finrank k F)
    (hl : M.l = ⊤) (h2 : IsMultiplyPretransitive M.permK M.Δ 2) : False := by
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  have : CharP k 2 := RingHom.charP (algebraMap k F) (algebraMap k F).injective 2
  have : FiniteDimensional k F := Module.Finite.of_finite
  refine not_exists_uniform_doublyTransitive_spanning_blocks hn
    ⟨M.G, M.blocks, M.Δ.ncard, M.K, M.isPartition_blocks, fun g hg Γ hΓ => M.smul_mem_blocks hg hΓ,
      M.two_le_ncard_blocks, M.one_lt_ncard, ?_, M.K_le, ?_, ?_,
      fun h hh Γ hΓ => M.smul_eq_of_mem_K hh hΓ, M.twoTransitive_blocks h2,
      fun Γ hΓ => M.spans_of_eq_top hl hΓ⟩
  · rintro Γ ⟨g, -, rfl⟩
    exact Set.ncard_smul_set g M.Δ
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using M.conj_mem_K g.2 hn
  · rintro Γ ⟨g, hg, rfl⟩ Γ' ⟨g', hg', rfl⟩
    exact ⟨g' * g⁻¹, M.G.mul_mem hg' (M.G.inv_mem hg), by rw [mul_smul, inv_smul_smul]⟩

theorem mem_Bu_of_mem_range {c : Fˣ} (hc : (c : F) ∈ Set.range (algebraMap k F)) : c ∈ M.Bu := by
  rw [mem_Bu]
  ext p
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [units_smul_eq_self_iff.mpr hc]
  · intro hp
    exact ⟨p, hp, units_smul_eq_self_iff.mpr hc⟩

theorem normal_of_affine [Finite F] [CharP F 2] (hl : M.l = ⊤) {p : ℕ} (hp : p.Prime)
    (e : M.Δ ≃ ZMod p)
    (he : e.permCongr '' (M.permBu : Set (Equiv.Perm M.Δ)) = {t | ∃ b, ∀ x, t x = x + b})
    (haff : ∀ g ∈ M.permK, ∃ a ≠ 0, ∃ b, ∀ x, e (g x) = a * e x + b)
    {g : F ≃ₗ[k] F} (hg : g ∈ M.G) {c : Fˣ} (hc : c ∈ M.Bu) :
    ∃ c' ∈ M.Bu, ∀ x, g (c * x) = c' * g x := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hck : (c : F) ∈ Set.range (algebraMap k F)
  · obtain ⟨r, hr⟩ := hck
    refine ⟨c, hc, fun x => ?_⟩
    rw [← hr, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  set u := g * scalarHom k F c * g⁻¹ with hu
  have huK : u ∈ M.K := M.conj_mem_K hg (M.scalarHom_mem_K hc)
  set σ := MulAction.toPermHom M.K M.Δ ⟨u, huK⟩
  have hσ : σ ∈ M.permK := ⟨⟨u, huK⟩, rfl⟩
  obtain ⟨a, -, b, hab⟩ := haff σ hσ
  have ha1 : a = 1 := by
    by_contra ha1
    have h1a : (1 : ZMod p) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    set x₀ := e.symm (b / (1 - a))
    have hfix : σ x₀ = x₀ := by
      apply e.injective
      rw [hab, Equiv.apply_symm_apply]
      field_simp
      ring
    have hfix' : u • (x₀ : ℙ k F) = x₀ := congrArg Subtype.val hfix
    rw [hu, mul_smul, mul_smul, smul_eq_iff_eq_inv_smul, scalarHom_smul] at hfix'
    exact hck (units_smul_eq_self_iff.mp hfix')
  subst ha1
  have htrans : e.permCongr σ ∈ e.permCongr '' (M.permBu : Set (Equiv.Perm M.Δ)) := by
    rw [he]
    refine ⟨b, fun y => ?_⟩
    rw [Equiv.permCongr_apply, hab, one_mul, Equiv.apply_symm_apply]
  obtain ⟨τ, hτ, hτσ⟩ := htrans
  have hτσ' : τ = σ := e.permCongr.injective hτσ
  obtain ⟨c', hc', hc'τ⟩ := M.mem_permBu.mp hτ
  have huΔ : ∀ q ∈ M.Δ, u • q = c' • q := by
    intro q hq
    have := hc'τ ⟨q, hq⟩
    rw [hτσ'] at this
    exact this
  set d := (scalarHom k F c')⁻¹ * u with hd
  have hdK : d ∈ M.K := M.K.mul_mem (M.K.inv_mem (M.scalarHom_mem_K hc')) huK
  have hdΔ : ∀ q ∈ M.Δ, d • q = q := by
    intro q hq
    rw [hd, mul_smul, huΔ q hq, ← scalarHom_smul, inv_smul_smul]
  have hdB : ∀ q : ℙ k F, ∃ b ∈ M.Bu, d • q = b • q := by
    intro q
    obtain ⟨Γ, hΓ, hqΓ⟩ := M.exists_mem_blocks q
    obtain ⟨b, hb, hbq⟩ := M.Bu_transitive hΓ hqΓ ((M.smul_mem_iff_of_mem_K hdK hΓ).mpr hqΓ)
    exact ⟨b, hb, hbq.symm⟩
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_forall_smul_eq (M.spans_of_eq_top hl M.Δ_mem_blocks)
    (fun b hb q hq => M.Bu_smul_mem_blocks M.Δ_mem_blocks hq hb) hdΔ hdB
  have hμ0 : algebraMap k F μ ≠ 0 := by
    intro h0
    have h1 := hμ 1
    rw [Algebra.smul_def, h0, zero_mul] at h1
    exact one_ne_zero (d.injective (h1.trans d.map_zero.symm))
  refine ⟨c' * Units.mk0 (algebraMap k F μ) hμ0,
    M.Bu.mul_mem hc' (M.mem_Bu_of_mem_range ⟨μ, rfl⟩), fun x => ?_⟩
  have hux : u (g x) = g (c * x) := by
    rw [hu, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, scalarHom_apply]
  have hud : u = scalarHom k F c' * d := by rw [hd, mul_inv_cancel_left]
  rw [← hux, hud, LinearEquiv.mul_apply, hμ, scalarHom_apply, Algebra.smul_def, Units.val_mul,
    Units.val_mk0, mul_assoc]

theorem normalizes_of_eq_top [Finite F] [CharP F 2] (hn : 3 ≤ finrank k F) (hl : M.l = ⊤)
    {g : F ≃ₗ[k] F} (hg : g ∈ M.G) : ∀ a ∈ M.l, ∃ a' ∈ M.l, ∀ x, g (a * x) = a' * g x := by
  have hB : ∀ c ∈ M.Bu, ∃ c' ∈ M.Bu, ∀ x, g (c * x) = c' * g x := by
    rcases M.burnside_schur_K with h2 | ⟨p, hp, -, e, he, haff⟩
    · exact (M.false_of_isMultiplyPretransitive hn hl h2).elim
    · exact fun c hc => M.normal_of_affine hl hp e he haff hg hc
  intro a ha
  rw [M.mem_l_iff] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨c', hc', h⟩ := hB c hc
    exact ⟨c', M.coe_mem_l hc', h⟩
  | zero => exact ⟨0, M.l.zero_mem, fun x => by rw [zero_mul, map_zero, zero_mul]⟩
  | add a b _ _ ha hb =>
    obtain ⟨a', ha', h⟩ := ha
    obtain ⟨b', hb', h'⟩ := hb
    exact ⟨a' + b', M.l.add_mem ha' hb', fun x => by rw [add_mul, map_add, h, h', add_mul]⟩
  | smul r a _ ha =>
    obtain ⟨a', ha', h⟩ := ha
    exact ⟨r • a', M.l.smul_mem ha', fun x => by rw [smul_mul_assoc, map_smul, h, smul_mul_assoc]⟩

end MinimalBlock

theorem exists_minimalBlock [Finite F] (G : Subgroup (F ≃ₗ[k] F)) (hS : scalars k F ≤ G)
    (hG : ¬ IsPreprimitive G (ℙ k F)) : ∃ M : MinimalBlock k F, M.G = G := by
  have htrans : IsPretransitive G (ℙ k F) := ⟨fun p q => by
    obtain ⟨c, hc⟩ := exists_units_smul_eq p q
    exact ⟨⟨scalarHom k F c, hS (scalarHom_mem_scalars c)⟩, (scalarHom_smul c p).trans hc⟩⟩
  have hex : ∃ n, ∃ X : Set (ℙ k F), (∀ g ∈ G, g • X = X ∨ Disjoint (g • X) X) ∧
      1 < X.ncard ∧ X ≠ Set.univ ∧ X.ncard = n := by
    by_contra h
    push Not at h
    apply hG
    refine { toIsPretransitive := htrans, isTrivialBlock_of_isBlock := fun {X} hX => ?_ }
    have hX' : ∀ g ∈ G, g • X = X ∨ Disjoint (g • X) X :=
      fun g hg => hX.smul_eq_or_disjoint ⟨g, hg⟩
    by_cases h1 : 1 < X.ncard
    · exact Or.inr (by
        by_contra hne
        exact h _ X hX' h1 hne rfl)
    · exact Or.inl (Set.ncard_le_one_iff_subsingleton.mp (by omega))
  classical
  obtain ⟨Δ, hΔ, h1, hne, hn⟩ := Nat.find_spec hex
  have hmin : ∀ X : Set (ℙ k F), (∀ g ∈ G, g • X = X ∨ Disjoint (g • X) X) → 1 < X.ncard →
      Δ.ncard ≤ X.ncard := by
    intro X hX hX1
    by_cases hXu : X = Set.univ
    · rw [hXu]
      exact Set.ncard_le_ncard (Set.subset_univ _)
    · rw [hn]
      exact Nat.find_min' hex ⟨X, hX, hX1, hXu, rfl⟩
  exact ⟨⟨G, hS, Δ, hΔ, h1, hne, hmin⟩, rfl⟩

theorem exists_intermediateField_normalized_of_not_isPreprimitive [Finite F] [CharP F 2]
    (hn : 3 ≤ finrank k F) (G : Subgroup (F ≃ₗ[k] F)) (hS : scalars k F ≤ G)
    (hG : ¬ IsPreprimitive G (ℙ k F)) :
    ∃ l : IntermediateField k F, l ≠ ⊥ ∧
      (∀ g ∈ G, ∀ a ∈ l, ∃ a' ∈ l, ∀ x, g (a * x) = a' * g x) ∧
      (∀ g ∈ G, ∃ σ : l ≃ₐ[k] l, ∀ (a : l) (x : F), g (a * x) = σ a * g x) ∧
      ∀ s ∈ scalars k F, ∀ (a : l) (x : F), s (a * x) = a * s x := by
  obtain ⟨M, rfl⟩ := exists_minimalBlock G hS hG
  have : FiniteDimensional k F := Module.Finite.of_finite
  have hnorm : ∀ g ∈ M.G, ∀ a ∈ M.l, ∃ a' ∈ M.l, ∀ x, g (a * x) = a' * g x := by
    intro g hg
    by_cases hl : M.l = ⊤
    · exact M.normalizes_of_eq_top hn hl hg
    · exact M.normalizes_of_ne_top hl hg
  refine ⟨M.l, M.l_ne_bot, hnorm, fun g hg => exists_algEquiv_of_normalizes M.l g (hnorm g hg),
    ?_⟩
  rintro s ⟨c, rfl⟩ a x
  rw [scalarHom_apply, scalarHom_apply, mul_left_comm]

end CFSG.ShultStronglyClosedTI.Singer
