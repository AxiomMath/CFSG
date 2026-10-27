module

public import CFSG.Quasithin.Vol2.Ch12Sec4A5Data
public import CFSG.Quasithin.Vol2.Ch6NatFacts
public import CFSG.Quasithin.Vol2.Ch6Hyperplane
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem perm5_exists_fix_of_pow_three : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 →
    ∃ x ∈ A5Mod.ev5, x ≠ 0 ∧ A5Mod.act5 σ x = x := by
  decide +kernel

theorem card_ev5_eq_sixteen : A5Mod.ev5.card = 16 := by
  decide

variable {G : Type} [Group G]

namespace IsA5ModuleUnder

variable {L S : Subgroup G}

theorem data_β_one (d : A5Mod.Data L S) : d.β 1 = 0 := by
  have h1 := d.β_mul 1 S.one_mem 1 S.one_mem
  rw [mul_one] at h1
  linear_combination -h1

theorem card_eq_sixteen (h : IsA5ModuleUnder L S) : Nat.card S = 16 := by
  obtain ⟨d⟩ := A5Mod.exists_data h
  let f : ↥S → ↥A5Mod.ev5 := fun w => ⟨d.β w, d.β_mem w w.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun w₁ w₂ h12 => Subtype.ext (d.β_inj w₁ w₁.2 w₂ w₂.2 (congrArg Subtype.val h12)),
      fun x => ?_⟩
    obtain ⟨w, hw, hwx⟩ := d.β_surj x x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_finsetCard, card_ev5_eq_sixteen]

theorem eq_of_le_of_ne_bot (h : IsA5ModuleUnder L S) {U : Subgroup G} (hUS : U ≤ S)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) : U = S := by
  obtain ⟨d⟩ := A5Mod.exists_data h
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hu1' : u ≠ 1 := fun h0 => hu1 (Subtype.ext h0)
  have hxu : d.β u ≠ 0 := fun h0 =>
    hu1' (d.β_inj u (hUS huU) 1 S.one_mem (h0.trans (data_β_one d).symm))
  have hc : ∀ k : ↥L, (k : G) * u * (k : G)⁻¹ ∈ U := fun k =>
    (Subgroup.mem_normalizer_iff.mp (hLU k.2) u).mp huU
  have hβc : ∀ k : ↥L, d.β ((k : G) * u * (k : G)⁻¹) =
      A5Mod.act5 (d.q k : Equiv.Perm (Fin 5)) (d.β u) := fun k => d.β_conj k u (hUS huU)
  refine le_antisymm hUS fun s hs => ?_
  obtain ⟨g₁, hg₁, g₂, hg₂, hs'⟩ :=
    A5Mod.mem_orbit_sum _ (d.β_mem u (hUS huU)) hxu _ (d.β_mem s hs)
  obtain ⟨k₁, hk₁⟩ := d.q_surj ⟨g₁, Equiv.Perm.mem_alternatingGroup.mpr (A5Mod.mem_alt5.mp hg₁)⟩
  obtain ⟨k₂, hk₂⟩ := d.q_surj ⟨g₂, Equiv.Perm.mem_alternatingGroup.mpr (A5Mod.mem_alt5.mp hg₂)⟩
  rcases hs' with hs' | hs'
  · have e : s = (k₁ : G) * u * (k₁ : G)⁻¹ := by
      refine d.β_inj s hs _ (hUS (hc k₁)) ?_
      rw [hβc, hk₁, hs']
    rw [e]
    exact hc k₁
  · have e : s = ((k₁ : G) * u * (k₁ : G)⁻¹) * ((k₂ : G) * u * (k₂ : G)⁻¹) := by
      refine d.β_inj s hs _ (S.mul_mem (hUS (hc k₁)) (hUS (hc k₂))) ?_
      rw [d.β_mul _ (hUS (hc k₁)) _ (hUS (hc k₂)), hβc, hβc, hk₁, hk₂, hs']
    rw [e]
    exact U.mul_mem (hc k₁) (hc k₂)

theorem exists_fixed_pow_forty (h : IsA5ModuleUnder L S) {g : G} (hg : g ∈ L) :
    ∃ s ∈ S, s ≠ 1 ∧ g ^ 40 * s * (g ^ 40)⁻¹ = s := by
  obtain ⟨d⟩ := A5Mod.exists_data h
  set a : Equiv.Perm (Fin 5) := (d.q ⟨g, hg⟩ : Equiv.Perm (Fin 5)) with ha
  set σ : Equiv.Perm (Fin 5) := (d.q ⟨g ^ 40, L.pow_mem hg 40⟩ : Equiv.Perm (Fin 5)) with hσ
  have hσa : σ = a ^ 40 := by
    rw [hσ, ha, ← SubgroupClass.coe_pow, ← map_pow]
    rfl
  have h120 : a ^ 120 = 1 := by
    have h1 := pow_card_eq_one' (G := Equiv.Perm (Fin 5)) (x := a)
    rwa [Nat.card_perm, Nat.card_fin] at h1
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσa, ← pow_mul]
    exact h120
  obtain ⟨x, hx, hx0, hfix⟩ := perm5_exists_fix_of_pow_three σ hσ3
  obtain ⟨s, hs, hsx⟩ := d.β_surj x hx
  refine ⟨s, hs, ?_, ?_⟩
  · rintro rfl
    exact hx0 (hsx.symm.trans (data_β_one d))
  · have hmem : g ^ 40 * s * (g ^ 40)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (d.normalizes (L.pow_mem hg 40)) s).mp hs
    refine d.β_inj _ hmem _ hs ?_
    have hc : d.β (g ^ 40 * s * (g ^ 40)⁻¹) = A5Mod.act5 σ (d.β s) :=
      d.β_conj ⟨g ^ 40, L.pow_mem hg 40⟩ s hs
    rw [hc, hsx]
    exact hfix

end IsA5ModuleUnder

theorem IsNatModCh5.exists_pow_forty_fixedPointFree {L W : Subgroup G} {n : ℕ}
    (h : IsNatModCh5 L W n) (hn : n ≠ 0) :
    ∃ g ∈ L, g ∈ Subgroup.normalizer (W : Set G) ∧
      ∀ w ∈ W, g ^ 40 * w * (g ^ 40)⁻¹ = w → w = 1 := by
  set D := h.data with hD
  have : CharP D.K 2 := charP_two_of_two_dvd (by rw [D.card]; exact dvd_pow_self 2 hn)
  obtain ⟨g, hgL, hg⟩ := D.exists_mem_of_matrix (SL2Model.c3 D.K)
  refine ⟨(g : G), hgL, g.2, fun w hw hfix => ?_⟩
  have hit : ∀ (k : ℕ) (v : Fin 2 → D.K), (D.conj g)^[k] v =
      Matrix.mulVec ((SL2Model.c3 D.K ^ k : Matrix.SpecialLinearGroup (Fin 2) D.K) :
        Matrix (Fin 2) (Fin 2) D.K) v := by
    intro k
    induction k with
    | zero =>
      intro v
      simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, hg, pow_succ', Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec]
  have h40 : SL2Model.c3 D.K ^ 40 = SL2Model.c3 D.K := by
    rw [show (40 : ℕ) = 3 * 13 + 1 from rfl, pow_succ, pow_mul, SL2Model.c3_pow_three, one_pow,
      one_mul]
  set v := Multiplicative.toAdd (D.E ⟨w, hw⟩) with hv
  have hconj : conjAct W (g ^ 40) ⟨w, hw⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    simpa using hfix
  have hfixv : Matrix.mulVec ((SL2Model.c3 D.K : Matrix.SpecialLinearGroup (Fin 2) D.K) :
      Matrix (Fin 2) (Fin 2) D.K) v = v := by
    have h1 := D.conj_apply (g ^ 40) ⟨w, hw⟩
    rw [hconj, D.conj_pow, hit, h40] at h1
    exact h1
  have e0 := congrFun hfixv 0
  have e1 := congrFun hfixv 1
  rw [SL2Model.c3_coe] at e0 e1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hv0 : v 0 = 0 := by linear_combination e1
  have hv1 : v 1 = 0 := by linear_combination e0 - e1
  have hv' : v = 0 := by
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
  have hE : D.E ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective hv'
  have hw1 : (⟨w, hw⟩ : ↥W) = 1 := D.E.injective (by rw [hE, map_one])
  exact congrArg Subtype.val hw1

theorem false_of_isNatModCh5_le_isA5ModuleSum [Finite G] {L W U : Subgroup G}
    (hW : IsNatModCh5 L W 2) (hWU : W ≤ U) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU : IsA5ModuleSum L U) : False := by
  obtain ⟨g, hgL, -, hfree⟩ := hW.exists_pow_forty_fixedPointFree two_ne_zero
  have hcardW : Nat.card W = 16 := by rw [hW.card_eq]; norm_num
  have hW0 : W ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcardW
    norm_num at hcardW
  have hLW := hW.1
  have hnot : ∀ S : Subgroup G, IsA5ModuleUnder L S → ¬ W ≤ S := by
    intro S hS hle
    have heq := hS.eq_of_le_of_ne_bot hle hLW hW0
    obtain ⟨s, hs, hs1, hsfix⟩ := hS.exists_fixed_pow_forty hgL
    rw [← heq] at hs
    exact hs1 (hfree s hs hsfix)
  rcases hU with hU1 | ⟨W₁, W₂, h₁, h₂, hdisj, hsup⟩
  · exact hnot U hU1 hWU
  · have hW₁U : W₁ ≤ U := hsup ▸ le_sup_left
    have hW₂U : W₂ ≤ U := hsup ▸ le_sup_right
    have hWW₁ : W ⊓ W₁ = ⊥ := by
      rcases hW.irreducible (W ⊓ W₁) inf_le_left (fun l hl =>
          Subgroup.inf_normalizer_le_normalizer_inf ⟨hLW hl, h₁.1 hl⟩) with h0 | h0
      · exact h0
      · exact absurd (by rw [← h0]; exact inf_le_right) (hnot W₁ h₁)
    have hc₁ : ∀ a ∈ W, ∀ b ∈ W₁, a * b = b * a := fun a ha b hb => hUc a (hWU ha) b (hW₁U hb)
    have hc₂ : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hUc a (hW₁U ha) b (hW₂U hb)
    obtain ⟨hcard₁, hset₁⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W W₁ hc₁
    obtain ⟨hcard₂, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W₁ W₂ hc₂
    rw [hWW₁, Subgroup.card_bot, mul_one, hcardW, h₁.card_eq_sixteen] at hcard₁
    rw [hdisj, Subgroup.card_bot, mul_one, hsup, h₁.card_eq_sixteen, h₂.card_eq_sixteen]
      at hcard₂
    have hWW₁U : W ⊔ W₁ = U :=
      Subgroup.eq_of_le_of_card_ge (sup_le hWU hW₁U) (by rw [hcard₁, hcard₂])
    obtain ⟨s, hs, hs1, hsfix⟩ := h₂.exists_fixed_pow_forty hgL
    have hsU : s ∈ ((W ⊔ W₁ : Subgroup G) : Set G) := by
      rw [hWW₁U]
      exact hW₂U hs
    rw [hset₁] at hsU
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hsU
    have hg40 : g ^ 40 ∈ L := L.pow_mem hgL 40
    have hga : g ^ 40 * a * (g ^ 40)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW hg40) a).mp ha
    have hgb : g ^ 40 * b * (g ^ 40)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (h₁.1 hg40) b).mp hb
    have hd : (g ^ 40 * a * (g ^ 40)⁻¹)⁻¹ * a ∈ W ⊓ W₁ := by
      refine Subgroup.mem_inf.mpr ⟨W.mul_mem (W.inv_mem hga) ha, ?_⟩
      have e1 : (g ^ 40 * a * (g ^ 40)⁻¹) * (g ^ 40 * b * (g ^ 40)⁻¹) = a * b := by
        rw [← hsfix]
        group
      have e : (g ^ 40 * a * (g ^ 40)⁻¹)⁻¹ * a = (g ^ 40 * b * (g ^ 40)⁻¹) * b⁻¹ := by
        calc (g ^ 40 * a * (g ^ 40)⁻¹)⁻¹ * a
            = (g ^ 40 * a * (g ^ 40)⁻¹)⁻¹ * (a * b) * b⁻¹ := by group
          _ = (g ^ 40 * a * (g ^ 40)⁻¹)⁻¹ *
              ((g ^ 40 * a * (g ^ 40)⁻¹) * (g ^ 40 * b * (g ^ 40)⁻¹)) * b⁻¹ := by rw [e1]
          _ = (g ^ 40 * b * (g ^ 40)⁻¹) * b⁻¹ := by group
      rw [e]
      exact W₁.mul_mem hgb (W₁.inv_mem hb)
    rw [hWW₁, Subgroup.mem_bot, inv_mul_eq_one] at hd
    have ha1 : a = 1 := hfree a ha hd
    subst ha1
    rw [one_mul] at hs hs1
    have hb2 : b ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.mpr ⟨hb, hs⟩
    rw [hdisj, Subgroup.mem_bot] at hb2
    exact hs1 hb2

end CFSG.Quasithin.H13
