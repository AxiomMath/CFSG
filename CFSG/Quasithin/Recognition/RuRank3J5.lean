module

public import CFSG.Quasithin.Recognition.RuRank3Main
public import CFSG.Quasithin.Recognition.RuRank3RuParamData

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open MulAction

theorem ncard_setOf_perm_inv (g : Equiv.Perm (Fin 4060)) (p : Fin 4060 → Prop) :
    {w | p (g⁻¹ w)}.ncard = {w | p w}.ncard := by
  have e : {w | p (g⁻¹ w)} = g '' {w | p w} := by
    ext w
    constructor
    · intro hw
      exact ⟨g⁻¹ w, hw, perm_apply_inv g w⟩
    · rintro ⟨w', hw', rfl⟩
      show p (g⁻¹ (g w'))
      rw [perm_inv_apply]
      exact hw'
  rw [e, Set.ncard_image_of_injective _ g.injective]

theorem ruAdj_iff_inv {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (x y : Fin 4060) :
    ruAdj (g x) y ↔ ruAdj x (g⁻¹ y) := by
  rw [← ruAdj_apply (inv_mem hg), perm_inv_apply]

theorem ncard_ruCntD
    {ti : Array ℕ} {v : Fin 4060} (h : ∀ x : Fin 4060, ruRowA ti x = true ↔
    ruAdj v x) : {w | ruAdj 0 w ∧ ruAdj v w}.ncard = ruCntD ti := by
  unfold ruCntD
  rw [← ncard_setOf_fin]
  congr 1
  ext w
  show (ruAdj 0 w ∧ ruAdj v w) ↔ ((ruQLab[(w : ℕ)]! == ruQLab[1]!) && ruRowA ti w) = true
  rw [Bool.and_eq_true, beq_iff_eq, h, ruAdj_zero_iff, mem_range_ruB_iff]

theorem ncard_ruAdj
    (x : Fin 4060) : {w | ruAdj x w}.ncard = 1755 := by
  obtain ⟨t, htP, hx⟩ : ∃ t ∈ ruP, t 0 = x := ⟨ruTreeElt x, ruTreeElt_mem _, ruTreeElt_apply_zero x⟩
  have e : {w | ruAdj x w} = {w | ruAdj 0 (t⁻¹ w)} := by
    ext w
    show ruAdj x w ↔ ruAdj 0 (t⁻¹ w)
    rw [← hx, ruAdj_iff_inv htP]
  rw [e]
  refine (ncard_setOf_perm_inv t fun v => ruAdj 0 v).trans ?_
  show {v | ruAdj 0 v}.ncard = 1755
  have e2 : {v | ruAdj 0 v} = Set.range ruB := Set.ext ruAdj_zero_iff
  rw [e2, Set.ncard_range_of_injective ruB_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem ncard_not_ruAdj
    (x : Fin 4060) : {w | w ≠ x ∧ ¬ ruAdj x w}.ncard = 2304 := by
  obtain ⟨t, htP, hx⟩ : ∃ t ∈ ruP, t 0 = x := ⟨ruTreeElt x, ruTreeElt_mem _, ruTreeElt_apply_zero x⟩
  have e : {w | w ≠ x ∧ ¬ ruAdj x w} = {w | t⁻¹ w ≠ 0 ∧ ¬ ruAdj 0 (t⁻¹ w)} := by
    ext w
    show (w ≠ x ∧ ¬ ruAdj x w) ↔ (t⁻¹ w ≠ 0 ∧ ¬ ruAdj 0 (t⁻¹ w))
    have h1 : w = x ↔ t⁻¹ w = 0 := by
      rw [← hx]
      constructor
      · rintro rfl
        exact perm_inv_apply t 0
      · intro h
        rw [← h, perm_apply_inv]
    rw [ne_eq, ne_eq, h1, ← hx, ruAdj_iff_inv htP]
  rw [e]
  refine (ncard_setOf_perm_inv t fun v => v ≠ 0 ∧ ¬ ruAdj 0 v).trans ?_
  show {v | v ≠ 0 ∧ ¬ ruAdj 0 v}.ncard = 2304
  have e2 : {v | v ≠ 0 ∧ ¬ ruAdj 0 v} = ruS := by
    ext v
    show (v ≠ 0 ∧ ¬ ruAdj 0 v) ↔ (v ≠ 0 ∧ v ∉ Set.range ruB)
    rw [ruAdj_zero_iff]
  rw [e2, ncard_ruS]

theorem ncard_common_of_ruAdj
    {x y : Fin 4060} (h : ruAdj x y) :
    {w | ruAdj x w ∧ ruAdj y w}.ncard = 730 := by
  obtain ⟨g, hg, rfl, rfl⟩ := h
  have e : {w | ruAdj (g 0) w ∧ ruAdj (g 1) w} = {w | ruAdj 0 (g⁻¹ w) ∧ ruAdj 1 (g⁻¹ w)} := by
    ext w
    show (ruAdj (g 0) w ∧ ruAdj (g 1) w) ↔ (ruAdj 0 (g⁻¹ w) ∧ ruAdj 1 (g⁻¹ w))
    rw [ruAdj_iff_inv hg, ruAdj_iff_inv hg]
  rw [e]
  refine (ncard_setOf_perm_inv g fun v => ruAdj 0 v ∧ ruAdj 1 v).trans ?_
  show {v | ruAdj 0 v ∧ ruAdj 1 v}.ncard = 730
  rw [ncard_ruCntD ruRowA_one, ruParam_check.1]

theorem ncard_common_of_not_ruAdj
    {x y : Fin 4060} (hxy : x ≠ y) (h : ¬ ruAdj x y) :
    {w | ruAdj x w ∧ ruAdj y w}.ncard = 780 := by
  obtain ⟨t, htP, hx⟩ : ∃ t ∈ ruP, t 0 = x := ⟨ruTreeElt x, ruTreeElt_mem _, ruTreeElt_apply_zero x⟩
  have hy0 : t⁻¹ y ≠ 0 := by
    intro h0
    apply hxy
    rw [← hx, ← h0, perm_apply_inv]
  have hyD : t⁻¹ y ∉ Set.range ruB := by
    intro hD
    apply h
    rw [← hx, ruAdj_iff_inv htP, ruAdj_zero_iff]
    exact hD
  obtain ⟨p, hp, hpg⟩ := exists_ruR0_g0 (⟨hy0, hyD⟩ : t⁻¹ y ∈ ruS)
  have hgP : t * p ∈ ruP := mul_mem htP (ruR0_le_ruP hp)
  have hg0 : (t * p) 0 = x := by rw [Equiv.Perm.mul_apply, ruR0_apply_zero hp, hx]
  have hgg : (t * p) ruG0F = y := by rw [Equiv.Perm.mul_apply, hpg, perm_apply_inv]
  have e : {w | ruAdj x w ∧ ruAdj y w} =
      {w | ruAdj 0 ((t * p)⁻¹ w) ∧ ruAdj ruG0F ((t * p)⁻¹ w)} := by
    ext w
    show (ruAdj x w ∧ ruAdj y w) ↔ (ruAdj 0 ((t * p)⁻¹ w) ∧ ruAdj ruG0F ((t * p)⁻¹ w))
    rw [← hg0, ← hgg, ruAdj_iff_inv hgP, ruAdj_iff_inv hgP]
  rw [e]
  refine (ncard_setOf_perm_inv (t * p) fun v => ruAdj 0 v ∧ ruAdj ruG0F v).trans ?_
  show {v | ruAdj 0 v ∧ ruAdj ruG0F v}.ncard = 780
  rw [ncard_ruCntD ruRowA_g0, ruParam_check.2]

section Abstract

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem ncard_setOf_equiv (Φ : Ω ≃ Fin 4060) (p : Fin 4060 → Prop) :
    {z | p (Φ z)}.ncard = {n | p n}.ncard := by
  rw [show {z | p (Φ z)} = Φ ⁻¹' {n | p n} from rfl,
    Set.ncard_preimage_of_injective_subset_range Φ.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)]

theorem IsRudvalisRank3.aut_eq
    (h : IsRudvalisRank3 G Ω) (ω δ : Ω)
    (hδ : Nat.card (stabilizer (stabilizer G ω) δ) = 2 ^ 12 * 5) :
    (∀ (g : G) z y, orbAdj G ω δ (g • z) (g • y) ↔ orbAdj G ω δ z y) ∧
    ∀ π : Equiv.Perm Ω, (∀ z y, orbAdj G ω δ (π z) (π y) ↔ orbAdj G ω δ z y) →
      ∃! g : G, ∀ z, g • z = π z := by
  refine ⟨fun g z y => orbAdj_smul g ω δ z y, fun π hπ => ?_⟩
  have hfaith := h.faithful
  obtain ⟨Φ, hΦ⟩ := h.exists_graph_equiv_of ω δ hδ
  obtain ⟨-, hrange⟩ := h.range_conj_eq hΦ
  have hπP : Φ.permCongr π ∈ ruP := by
    apply mem_ruP_of_adj
    intro a b
    rw [Equiv.permCongr_apply, Equiv.permCongr_apply, ← hΦ, hπ, hΦ, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  rw [← hrange] at hπP
  obtain ⟨g, hg⟩ := hπP
  have hσ : ∀ (g : G) (n : Fin 4060), ((Equiv.permCongrHom Φ).toMonoidHom.comp
      (MulAction.toPermHom G Ω)) g n = Φ (g • Φ.symm n) := fun g n => rfl
  have hgz : ∀ z, g • z = π z := by
    intro z
    have e : ((Equiv.permCongrHom Φ).toMonoidHom.comp (MulAction.toPermHom G Ω)) g (Φ z) =
        Φ.permCongr π (Φ z) := by rw [hg]
    rw [hσ, Equiv.permCongr_apply, Equiv.symm_apply_apply] at e
    exact Φ.injective e
  refine ⟨g, hgz, fun g' hg' => ?_⟩
  apply hfaith.eq_of_smul_eq_smul
  intro z
  rw [hg' z, hgz z]

end Abstract

end CFSG.Quasithin.RuRank3
