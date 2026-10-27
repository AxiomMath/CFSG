module

public import CFSG.RankThree.PartOne.CTP.StdExist
public import CFSG.RankThree.PartOne.CTP.StdBlocks
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.CTP.StdFacts

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (subfieldGL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalCores (isQuasisimple_of_mulEquiv isQuasisimple_nontrivial)

variable {G : Type} [Group G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G}

section Cfg

theorem cfg_J_le_K (cfg : IConfig c f₀ I K BK J) {a b : Fin 3} (hab : a ≠ b) : J a b ≤ K := by
  obtain ⟨Kq, _, hq, φ, hJ, -, -⟩ := cfg.triangle
  exact (hJ a b hab).1

theorem cfg_BK_le_K (cfg : IConfig c f₀ I K BK J) : BK ≤ K := by
  obtain ⟨Kq, _, hq, φ, -, hB, -⟩ := cfg.triangle
  exact hB

theorem cfg_K_perfect (cfg : IConfig c f₀ I K BK J) : Group.IsPerfect ↥K := by
  obtain ⟨Kq, _, hq, φ, -, -, -⟩ := cfg.triangle
  have := isPerfect_unitarySU_three_of_two_le hq cfg.f_two
  exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective

theorem cfg_K_ne_bot (cfg : IConfig c f₀ I K BK J) : K ≠ ⊥ := by
  obtain ⟨Kq, _, hq, φ, -, -, -⟩ := cfg.triangle
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  obtain ⟨hQ, -, -⟩ := blk_model hq cfg.f_two h01
  have := isQuasisimple_nontrivial hQ
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(blk hq h01))
  intro hK
  have hsub : Subsingleton ↥K := by
    rw [hK]
    infer_instance
  apply hx
  have h1 : φ.symm ⟨(x : GL (Fin 3) Kq), blk_le_unitarySU (h := hq) h01 x.2⟩ = φ.symm 1 :=
    Subsingleton.elim _ _
  have h2 := φ.symm.injective h1
  have h3 := congrArg Subtype.val h2
  exact Subtype.ext (by simpa using h3)

theorem cfg_J_le_I (cfg : IConfig c f₀ I K BK J) {a b : Fin 3} (hab : a ≠ b) : J a b ≤ I :=
  (cfg_J_le_K cfg hab).trans cfg.K_le

theorem cfg_BK_le_I (cfg : IConfig c f₀ I K BK J) : BK ≤ I :=
  (cfg_BK_le_K cfg).trans cfg.K_le

theorem pairLayer_le_I (Jab : Subgroup G) : pairLayer I BK Jab ≤ I :=
  (Subgroup.map_subtype_le _).trans inf_le_left

theorem cfg_two_le_five_mul (cfg : IConfig c f₀ I K BK J) : 2 ≤ 5 * f₀ := by
  have := cfg.f_two
  omega

end Cfg

section Model

variable [Finite G]

theorem cfg_center_bot (hGA : CFSG.Open.GriessAllModelsStatement)
    (cfg : IConfig c f₀ I K BK J) : Subgroup.center I = ⊥ :=
  psuThree_center_trivial hGA ((even_of_five_dvd cfg.dvd5).mul_left 5) cfg.perfect cfg.model

theorem cfg_I_model (hGA : CFSG.Open.GriessAllModelsStatement)
    (cfg : IConfig c f₀ I K BK J) : StatedClassicalModel ↥I .PSU 3 2 (5 * f₀) :=
  statedClassicalModel_of_equiv
    ((QuotientGroup.quotientMulEquivOfEq (cfg_center_bot hGA cfg)).trans
      QuotientGroup.quotientBot) cfg.model

end Model

section Pic

variable [Finite G] (cfg : IConfig c f₀ I K BK J) (pic : StdData c f₀ I K BK J)

include cfg pic

theorem tr_M {a b : Fin 3} (hab : a ≠ b) :
    tr I pic.Ψ (pairLayer I BK (J a b)) = blk pic.hF hab :=
  pic.tr_pairLayer cfg.dvd5 cfg.f_two (cfg_BK_le_I cfg) hab (cfg_J_le_I cfg hab)

noncomputable def pairLayerEquiv {a b : Fin 3} (hab : a ≠ b) :
    ↥(pairLayer I BK (J a b)) ≃* ↥(blk pic.hF hab) :=
  (mulEquivTr pic.Ψ_inj (pairLayer_le_I _)).trans (MulEquiv.subgroupCongr (tr_M cfg pic hab))

theorem cfg_M_model {a b : Fin 3} (hab : a ≠ b) :
    StatedClassicalModel ↥(pairLayer I BK (J a b)) .PSL 2 2 (5 * f₀) :=
  statedClassicalModel_of_equiv (pairLayerEquiv cfg pic hab).symm
    (blk_model pic.hF (cfg_two_le_five_mul cfg) hab).2.2

theorem cfg_M_quasi {a b : Fin 3} (hab : a ≠ b) :
    CFSG.IsQuasisimple ↥(pairLayer I BK (J a b)) :=
  isQuasisimple_of_mulEquiv (pairLayerEquiv cfg pic hab).symm
    (blk_model pic.hF (cfg_two_le_five_mul cfg) hab).1

theorem cfg_J_le_M {a b : Fin 3} (hab : a ≠ b) : J a b ≤ pairLayer I BK (J a b) := by
  refine (tr_le_iff pic.Ψ_inj (cfg_J_le_I cfg hab)).mp ?_
  rw [pic.tr_J a b hab, tr_M cfg pic hab]
  exact map_blk_subfield_le pic.hF pic.K₀ pic.h₀ pic.bar_eq hab

theorem cfg_M_sup {a b d : Fin 3} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    pairLayer I BK (J a b) ⊔ pairLayer I BK (J a d) = I := by
  refine tr_injective pic.Ψ_inj (sup_le (pairLayer_le_I _) (pairLayer_le_I _)) le_rfl ?_
  rw [tr_sup (pairLayer_le_I _) (pairLayer_le_I _), tr_M cfg pic hab, tr_M cfg pic had,
    blk_sup_blk_eq_unitarySU pic.hF (cfg_two_le_five_mul cfg) hab had hbd, pic.tr_I]

theorem cfg_K_sup_M {a b : Fin 3} (hab : a ≠ b) : K ⊔ pairLayer I BK (J a b) = I := by
  refine tr_injective pic.Ψ_inj (sup_le cfg.K_le (pairLayer_le_I _)) le_rfl ?_
  rw [tr_sup cfg.K_le (pairLayer_le_I _), pic.tr_K, tr_M cfg pic hab, pic.tr_I]
  exact Kst_sup_blk_eq pic.K₀ pic.hF pic.h₀ pic.bar_eq (cfg_two_le_five_mul cfg) hab

theorem c_conj_mem_M {a b : Fin 3} (hab : a ≠ b) {m : G} (hm : m ∈ pairLayer I BK (J a b)) :
    c * m * c⁻¹ ∈ pairLayer I BK (J a b) := by
  have hmI : m ∈ I := pairLayer_le_I _ hm
  have hcm : c * m * c⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp cfg.c_norm m).mp hmI
  have h1 : pic.Ψ ⟨c * m * c⁻¹, hcm⟩ = glAut pic.σ (pic.Ψ ⟨m, hmI⟩) := pic.Ψ_c ⟨m, hmI⟩ hcm
  have h2 : pic.Ψ ⟨m, hmI⟩ ∈ blk pic.hF hab := by
    rw [← tr_M cfg pic hab]
    exact (mem_tr_iff pic.Ψ_inj ⟨m, hmI⟩).mpr hm
  have h3 := glAut_mem_blk pic.hF pic.σ hab h2
  rw [← h1, ← tr_M cfg pic hab] at h3
  exact (mem_tr_iff pic.Ψ_inj ⟨c * m * c⁻¹, hcm⟩).mp h3

theorem cfg_c_norm_M {a b : Fin 3} (hab : a ≠ b) :
    c ∈ Subgroup.normalizer (pairLayer I BK (J a b) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨c_conj_mem_M cfg pic hab, fun h1 => ?_⟩
  have fwk : ∀ k : ℕ, ∀ m ∈ pairLayer I BK (J a b),
      c ^ k * m * (c ^ k)⁻¹ ∈ pairLayer I BK (J a b) := by
    intro k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      have := c_conj_mem_M cfg pic hab (ih m hm)
      convert this using 1
      group
  have h4 := fwk 4 _ h1
  have e : c ^ 4 * (c * h * c⁻¹) * (c ^ 4)⁻¹ = h := by
    have h5 : c ^ 4 * c = 1 := by rw [← pow_succ]; exact cfg.c_pow
    calc c ^ 4 * (c * h * c⁻¹) * (c ^ 4)⁻¹ = (c ^ 4 * c) * h * (c ^ 4 * c)⁻¹ := by group
      _ = h := by rw [h5]; group
  rwa [e] at h4

end Pic

end CFSG.RankThree.PartOne.CTP
