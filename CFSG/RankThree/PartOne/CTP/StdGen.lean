module

public import CFSG.RankThree.PartOne.CTP.StdDiag
public import CFSG.RankThree.PartOne.CTP.SL2Max
public import CFSG.RankThree.PartOne.CTP.StdFacts2

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (subfieldGL subfieldGL_injective coe_subfieldGL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Arith

theorem dvd25_two_pow_five_mul {f : ℕ} (h : 5 ∣ 2 ^ f + 1) : 25 ∣ 2 ^ (5 * f) + 1 := by
  have h1 : 2 ^ f % 5 = 4 := by omega
  have h2 : (2 ^ (5 * f) + 1) % 25 = 0 := by
    rw [mul_comm, pow_mul, Nat.add_mod, Nat.pow_mod]
    have key : ∀ r : Fin 25, r.val % 5 = 4 → ((r.val ^ 5) % 25 + 1 % 25) % 25 = 0 := by decide
    have hr : (2 ^ f % 25) % 5 = 4 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 5 ∣ 25)]
      exact h1
    exact key ⟨2 ^ f % 25, Nat.mod_lt _ (by norm_num)⟩ hr
  omega

theorem not_dvd25_two_pow_two_mul_sub_one {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) (h25 : ¬25 ∣ 2 ^ f + 1) :
    ¬25 ∣ 2 ^ (2 * f) - 1 := by
  intro h
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have e : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have h3 : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by rw [two_mul, pow_add]
    rw [h3]
    have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
    simp only [mul_one] at this
    rw [this, mul_comm]
  have hnd : ¬5 ∣ 2 ^ f - 1 := by
    intro h5'
    have : 5 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h5 h5'
    have h2 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [h2] at this
    omega
  have hcop : Nat.Coprime 5 (2 ^ f - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hnd
  have hcop25 : Nat.Coprime 25 (2 ^ f - 1) := by
    have := Nat.Coprime.pow_left 2 hcop
    simpa using this
  rw [e] at h
  exact h25 (hcop25.dvd_of_dvd_mul_left h)

end Arith

section Mu

variable {f₀ : ℕ} {F : Type} [Field F]

theorem exists_order25 (hF : UnitaryFieldData 2 (5 * f₀) F) (h5 : 5 ∣ 2 ^ f₀ + 1) :
    ∃ μ : Fˣ, orderOf μ = 25 ∧ hF.norm (μ : F) = 1 := by
  have hfin := hF.finite
  have hd : 25 ∣ 2 ^ (5 * f₀) + 1 := dvd25_two_pow_five_mul h5
  have hdvd : 25 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF.card]
    have h2 : 2 ^ (2 * (5 * f₀)) = 2 ^ (5 * f₀) * 2 ^ (5 * f₀) := by rw [two_mul, pow_add]
    have h3 : 2 ^ (5 * f₀) * 2 ^ (5 * f₀) - 1 = (2 ^ (5 * f₀) + 1) * (2 ^ (5 * f₀) - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (2 ^ (5 * f₀)) 1
      simpa using this
    rw [h2, h3]
    exact Dvd.dvd.mul_right hd _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hg0 : orderOf g ≠ 0 := by
    rw [hg]
    exact Nat.card_pos.ne'
  have hm : 25 ∣ orderOf g := by rw [hg]; exact hdvd
  have hord : orderOf (g ^ (orderOf g / 25)) = 25 := orderOf_pow_orderOf_div hg0 hm
  refine ⟨g ^ (orderOf g / 25), hord, ?_⟩
  have h25 : (g ^ (orderOf g / 25)) ^ 25 = 1 := by
    have := pow_orderOf_eq_one (g ^ (orderOf g / 25))
    rwa [hord] at this
  obtain ⟨k, hk⟩ := hd
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
  have : ((g ^ (orderOf g / 25) : Fˣ) : F) ^ (2 ^ (5 * f₀) + 1) = 1 := by
    rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, h25, Units.val_one, one_pow]
  exact this

end Mu

section General

variable {G : Type} [Group G]

theorem tr_zpowers {H : Type} [Group H] {I : Subgroup G} {Ψ : ↥I →* H} (y : ↥I) :
    tr I Ψ (Subgroup.zpowers (y : G)) = Subgroup.zpowers (Ψ y) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxy : x = y ^ k := Subtype.ext (by simpa using hk.symm)
    rw [hxy, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  · rintro ⟨k, rfl⟩
    refine ⟨y ^ k, ?_, by rw [map_zpow]⟩
    show ((y ^ k : ↥I) : G) ∈ Subgroup.zpowers (y : G)
    rw [Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers _ _

theorem exists_inner_of_mem_sup_centralizer {M : Subgroup G} {c : G}
    (hc : c ∈ M ⊔ Subgroup.centralizer (M : Set G)) :
    ∃ m ∈ M, ∀ x ∈ M, c * x * c⁻¹ = m * x * m⁻¹ := by
  let H : Subgroup G :=
    { carrier := {g | ∃ m ∈ M, ∀ x ∈ M, g * x * g⁻¹ = m * x * m⁻¹}
      one_mem' := ⟨1, M.one_mem, fun x _ => rfl⟩
      mul_mem' := by
        rintro g g' ⟨m, hm, hg⟩ ⟨m', hm', hg'⟩
        refine ⟨m * m', M.mul_mem hm hm', fun x hx => ?_⟩
        have h1 := hg (m' * x * m'⁻¹) (M.mul_mem (M.mul_mem hm' hx) (M.inv_mem hm'))
        have h2 := hg' x hx
        calc g * g' * x * (g * g')⁻¹ = g * (g' * x * g'⁻¹) * g⁻¹ := by group
          _ = g * (m' * x * m'⁻¹) * g⁻¹ := by rw [h2]
          _ = m * (m' * x * m'⁻¹) * m⁻¹ := h1
          _ = m * m' * x * (m * m')⁻¹ := by group
      inv_mem' := by
        rintro g ⟨m, hm, hg⟩
        refine ⟨m⁻¹, M.inv_mem hm, fun x hx => ?_⟩
        have h1 := hg (m⁻¹ * x * m) (M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm)
        have h2 : g * (m⁻¹ * x * m) * g⁻¹ = x := by
          rw [h1]
          group
        calc g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * (g * (m⁻¹ * x * m) * g⁻¹) * g := by rw [h2]; group
          _ = m⁻¹ * x * m⁻¹⁻¹ := by group }
  have hMH : M ≤ H := fun g hg => ⟨g, hg, fun x _ => rfl⟩
  have hCH : Subgroup.centralizer (M : Set G) ≤ H := by
    intro g hg
    refine ⟨1, M.one_mem, fun x hx => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hg x hx
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [← this]
      _ = 1 * x * 1⁻¹ := by group
  exact sup_le hMH hCH hc

end General

section Pic

variable {G : Type} [Group G] [Finite G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G}

theorem glAut_subfieldGL_of_iff {F : Type} [Field F] {σ : F ≃+* F} {K₀ : Subfield F}
    (hK : ∀ x, x ∈ K₀ ↔ σ x = x) {n : ℕ} (g : GL (Fin n) K₀) :
    glAut σ (subfieldGL K₀ n g) = subfieldGL K₀ n g := by
  obtain rfl : K₀ = CFSG.LieType.Chevalley.fixSubfield σ :=
    Subfield.ext fun x => (hK x).trans (CFSG.LieType.Chevalley.mem_fixSubfield σ).symm
  exact glAut_subfieldGL_fix g

omit [Finite G] in
theorem exists_pre (pic : StdData c f₀ I K BK J) {g : GL (Fin 3) pic.F}
    (hg : g ∈ unitarySU 2 (5 * f₀) pic.F 3) : ∃ x : ↥I, pic.Ψ x = g := by
  rw [← pic.Ψ_range] at hg
  exact MonoidHom.mem_range.mp hg

variable (cfg : IConfig c f₀ I K BK J) (pic : StdData c f₀ I K BK J)

omit [Finite G] in
include cfg in
theorem not_exists_unit_K₀ {μ : pic.Fˣ} (hμ : orderOf μ = 25) :
    ¬ ∃ μ₀ : Units ↥pic.K₀, Units.map pic.K₀.subtype.toMonoidHom μ₀ = μ := by
  rintro ⟨μ₀, rfl⟩
  have hord : orderOf μ₀ = 25 := by
    rw [← hμ]
    exact (orderOf_injective (Units.map pic.K₀.subtype.toMonoidHom : Units ↥pic.K₀ →* Units pic.F)
      (Units.map_injective Subtype.val_injective) μ₀).symm
  have hdvd : orderOf μ₀ ∣ Nat.card (Units ↥pic.K₀) := orderOf_dvd_natCard μ₀
  rw [Nat.card_units, pic.h₀.card, hord] at hdvd
  exact not_dvd25_two_pow_two_mul_sub_one cfg.dvd5 cfg.ndvd25 hdvd

include cfg in
theorem exists_gen_x {a b : Fin 3} (hab : a ≠ b) :
    ∃ (μ : pic.Fˣ) (x₁ : ↥I), orderOf μ = 25 ∧ pic.hF.norm (μ : pic.F) = 1 ∧
      pic.Ψ x₁ = dg3 a b μ ∧ (x₁ : G) ∈ pairLayer I BK (J a b) := by
  obtain ⟨μ, hμ25, hμN⟩ := exists_order25 pic.hF cfg.dvd5
  have hmem : (dg3 a b μ : GL (Fin 3) pic.F) ∈ unitarySU 2 (5 * f₀) pic.F 3 :=
    blk_le_unitarySU (h := pic.hF) hab (dg3_mem_blk pic.hF hab hμN)
  obtain ⟨x₁, hx₁⟩ := exists_pre pic hmem
  refine ⟨μ, x₁, hμ25, hμN, hx₁, ?_⟩
  refine (mem_tr_iff pic.Ψ_inj x₁).mp ?_
  rw [tr_M cfg pic hab, hx₁]
  exact dg3_mem_blk pic.hF hab hμN

omit [Finite G] in
theorem exists_gen_t {a b : Fin 3} (hab : a ≠ b) :
    ∃ t₁ : ↥I, pic.Ψ t₁ = sw3 hab ∧ (t₁ : G) ∈ J a b := by
  have hmem : (sw3 hab : GL (Fin 3) pic.F) ∈ unitarySU 2 (5 * f₀) pic.F 3 :=
    blk_le_unitarySU (h := pic.hF) hab (sw3_mem_blk pic.hF hab)
  obtain ⟨t₁, ht₁⟩ := exists_pre pic hmem
  refine ⟨t₁, ht₁, ?_⟩
  refine (mem_tr_iff pic.Ψ_inj t₁).mp ?_
  rw [pic.tr_J a b hab, ht₁]
  exact sw3_mem_Jst pic.K₀ pic.h₀ hab

end Pic

section Gen

variable {G : Type} [Group G] [Finite G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G} (cfg : IConfig c f₀ I K BK J) (pic : StdData c f₀ I K BK J)

include cfg pic

noncomputable def JEquiv {a b : Fin 3} (hab : a ≠ b) : ↥(J a b) ≃* ↥(blk pic.h₀ hab) :=
  (mulEquivTr pic.Ψ_inj (cfg_J_le_I cfg hab)).trans
    ((MulEquiv.subgroupCongr (pic.tr_J a b hab)).trans
      (Subgroup.equivMapOfInjective (blk pic.h₀ hab) (subfieldGL pic.K₀ 3)
        (subfieldGL_injective pic.K₀ 3)).symm)

theorem cfg_generation {a b : Fin 3} (hab : a ≠ b) :
    ∃ x t : G, x ∈ pairLayer I BK (J a b) ∧ orderOf x = 25 ∧
      Subgroup.zpowers (x ^ 5) = BK ⊓ J a b ∧ t ∈ J a b ∧ orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ ∧
      pairLayer I BK (J a b) = J a b ⊔ Subgroup.zpowers x := by
  have : CharP pic.F 2 := pic.hF.charP
  obtain ⟨μ, x₁, hμ25, hμN, hx₁, hxM⟩ := exists_gen_x cfg pic hab
  obtain ⟨t₁, ht₁, htJ⟩ := exists_gen_t pic hab
  have hxord : orderOf (x₁ : G) = 25 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective pic.Ψ pic.Ψ_inj, hx₁, orderOf_dg3, hμ25]
  have htord : orderOf (t₁ : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective pic.Ψ pic.Ψ_inj, ht₁]
    exact orderOf_sw3 hab
  have hinv : (t₁ : G) * x₁ * (t₁ : G)⁻¹ = (x₁ : G)⁻¹ := by
    have h : t₁ * x₁ * t₁⁻¹ = x₁⁻¹ := pic.Ψ_inj (by
      rw [map_mul, map_mul, map_inv, map_inv, hx₁, ht₁, sw3_dg3, dg3_inv])
    simpa using congrArg Subtype.val h
  have hμ5 : orderOf (μ ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hμ25]; norm_num), hμ25]
  have hx5 : Subgroup.zpowers ((x₁ : G) ^ 5) = BK ⊓ J a b := by
    refine tr_injective pic.Ψ_inj ?_ (inf_le_left.trans (cfg_BK_le_I cfg)) ?_
    · rw [Subgroup.zpowers_le]
      exact pow_mem x₁.2 5
    · have e1 : ((x₁ : G) ^ 5) = ((x₁ ^ 5 : ↥I) : G) := rfl
      rw [e1, tr_zpowers, tr_inf pic.Ψ_inj, pic.tr_BK, pic.tr_J a b hab,
        Bst_inf_Jst_eq pic.hF pic.K₀ pic.h₀ pic.bar_eq cfg.dvd5 hab hμ5, map_pow, hx₁, dg3_pow]
  have hxJ : (x₁ : G) ∉ J a b := by
    intro hxJ
    have h1 : pic.Ψ x₁ ∈ tr I pic.Ψ (J a b) := (mem_tr_iff pic.Ψ_inj x₁).mpr hxJ
    rw [pic.tr_J a b hab, hx₁] at h1
    obtain ⟨y, -, hy⟩ := h1
    have hent := congrArg (fun g : GL (Fin 3) pic.F => (g : Matrix (Fin 3) (Fin 3) pic.F) a a) hy
    simp only [coe_subfieldGL, Matrix.map_apply, Subfield.coe_subtype] at hent
    have hent2 : ((y : Matrix (Fin 3) (Fin 3) pic.K₀) a a : pic.F) = (μ : pic.F) := by
      rw [hent]
      simp [dg3, diagU_val, dgVec]
    have hy0 : ((y : Matrix (Fin 3) (Fin 3) pic.K₀) a a) ≠ 0 := by
      intro h0
      rw [h0] at hent2
      exact μ.ne_zero (by rw [← hent2]; rfl)
    exact not_exists_unit_K₀ cfg pic hμ25
      ⟨Units.mk0 _ hy0, Units.ext (by simpa using hent2)⟩
  have hMJ : pairLayer I BK (J a b) = J a b ⊔ Subgroup.zpowers (x₁ : G) := by
    set M := pairLayer I BK (J a b) with hM
    have hJM : J a b ≤ M := cfg_J_le_M cfg pic hab
    have hX : StatedClassicalModel ↥M .PSL 2 2 (5 * f₀) := cfg_M_model cfg pic hab
    have hJ' : StatedClassicalModel ↥((J a b).subgroupOf M) .PSL 2 2 f₀ :=
      statedClassicalModel_of_equiv ((Subgroup.subgroupOfEquivOfLe hJM).trans
        (JEquiv cfg pic hab)).symm (blk_model pic.h₀ cfg.f_two hab).2.2
    have hx' : (⟨(x₁ : G), hxM⟩ : ↥M) ∉ (J a b).subgroupOf M := fun h => hxJ h
    have htop := sl2_sup_zpowers_eq_top (k := f₀) cfg.f_two hX hJ' hx'
    have := congrArg (Subgroup.map M.subtype) htop
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hJM, MonoidHom.map_zpowers] at this
    exact this.symm
  exact ⟨x₁, t₁, hxM, hxord, hx5, htJ, htord, hinv, hMJ⟩

theorem cfg_c_outer_M {a b : Fin 3} (hab : a ≠ b) :
    c ∉ pairLayer I BK (J a b) ⊔ Subgroup.centralizer (pairLayer I BK (J a b) : Set G) := by
  intro hc
  have : CharP pic.F 2 := pic.hF.charP
  obtain ⟨m, hmM, hcm⟩ := exists_inner_of_mem_sup_centralizer hc
  have hmI : m ∈ I := pairLayer_le_I _ hmM
  set m₁ : ↥I := ⟨m, hmI⟩ with hm₁
  have hnorm : ∀ x : ↥I, c * (x : G) * c⁻¹ ∈ I := fun x =>
    (Subgroup.mem_normalizer_iff.mp cfg.c_norm x).mp x.2
  have hX : pic.Ψ m₁ ∈ blk pic.hF hab := by
    rw [← tr_M cfg pic hab]
    exact (mem_tr_iff pic.Ψ_inj m₁).mpr hmM
  have hcomm : ∀ g ∈ Jst pic.K₀ pic.h₀ hab, pic.Ψ m₁ * g = g * pic.Ψ m₁ := by
    intro g hg
    rw [← pic.tr_J a b hab] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    have hjJ : (j : G) ∈ J a b := hj
    have hjM : (j : G) ∈ pairLayer I BK (J a b) := cfg_J_le_M cfg pic hab hjJ
    have h1 : pic.Ψ ⟨c * j * c⁻¹, hnorm j⟩ = glAut pic.σ (pic.Ψ j) := pic.Ψ_c j (hnorm j)
    have h2 : glAut pic.σ (pic.Ψ j) = pic.Ψ j := by
      have hjst : pic.Ψ j ∈ Jst pic.K₀ pic.h₀ hab := by
        rw [← pic.tr_J a b hab]
        exact ⟨j, hj, rfl⟩
      obtain ⟨y, -, hy⟩ := hjst
      rw [← hy]
      exact glAut_subfieldGL_of_iff pic.K₀_iff y
    have h3 : (⟨c * j * c⁻¹, hnorm j⟩ : ↥I) = m₁ * j * m₁⁻¹ :=
      Subtype.ext (by simpa using hcm j hjM)
    have h4 : pic.Ψ (m₁ * j * m₁⁻¹) = pic.Ψ j := by rw [← h3, h1, h2]
    rw [map_mul, map_mul, map_inv] at h4
    exact mul_inv_eq_iff_eq_mul.mp h4
  obtain ⟨Y, hY, hXY⟩ := (mem_blk_iff_emb pic.hF hab).mp hX
  obtain ⟨μ, x₁, hμ25, hμN, hx₁, hxM⟩ := exists_gen_x cfg pic hab
  have hζ5 : orderOf (μ ^ 5) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hμ25]; norm_num), hμ25]
  have hζ55 : (μ ^ 5) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (μ ^ 5)
    rwa [hζ5] at this
  obtain ⟨ζ₀, hζ₀, hζ₀5⟩ := exists_mem_K₀ pic.K₀ pic.h₀ cfg.dvd5 hζ55
  have hζJ : (dg3 a b (μ ^ 5) : GL (Fin 3) pic.F) ∈ Jst pic.K₀ pic.h₀ hab := by
    rw [← hζ₀]
    exact dg3_mem_Jst pic.K₀ pic.h₀ hab (norm_eq_one_of_pow_five pic.K₀ pic.h₀ cfg.dvd5 (by
      have := congrArg (fun u : Units ↥pic.K₀ => (u : ↥pic.K₀)) hζ₀5
      simpa using this))
  have e1 := hcomm _ (sw3_mem_Jst pic.K₀ pic.h₀ hab)
  have e2 := hcomm _ hζJ
  rw [hXY] at e1 e2
  unfold sw3 at e1
  rw [dg3_eq_emb hab] at e2
  rw [← map_mul, ← map_mul] at e1 e2
  have c1 := emb_injective hab e1
  have c2 := emb_injective hab e2
  have hdet := ((mem_gramSU_iff_unitary pic.hF).mp hY).2
  have hζne : μ ^ 5 ≠ (μ ^ 5)⁻¹ := by
    intro h
    have h1 : (μ ^ 5) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr h
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hζ5] at this
    omega
  have hY1 : Y = 1 := eq_one_of_commute_swap_diag hdet hζne c1 c2
  have hm1 : m₁ = 1 := pic.Ψ_inj (by rw [hXY, hY1, map_one, map_one])
  have hm : m = 1 := congrArg Subtype.val hm1
  have hcx : c * (x₁ : G) * c⁻¹ = x₁ := by
    rw [hcm x₁ hxM, hm]
    group
  have h5 : pic.Ψ ⟨c * (x₁ : G) * c⁻¹, hnorm x₁⟩ = glAut pic.σ (pic.Ψ x₁) := pic.Ψ_c x₁ (hnorm x₁)
  have h6 : (⟨c * (x₁ : G) * c⁻¹, hnorm x₁⟩ : ↥I) = x₁ := Subtype.ext hcx
  rw [h6, hx₁] at h5
  have h7 := congrArg (fun g : GL (Fin 3) pic.F => (g : Matrix (Fin 3) (Fin 3) pic.F) a a) h5
  simp only [dg3, diagU_val, dgVec, coe_glAut, Matrix.map_apply, Matrix.diagonal_apply_eq,
    ite_true] at h7
  have hmem : (μ : pic.F) ∈ pic.K₀ := (pic.K₀_iff _).mpr h7.symm
  exact not_exists_unit_K₀ cfg pic hμ25 ⟨Units.mk0 ⟨(μ : pic.F), hmem⟩ (by
    intro h0
    exact μ.ne_zero (congrArg Subtype.val h0)), Units.ext rfl⟩

end Gen

end CFSG.RankThree.PartOne.CTP
