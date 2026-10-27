module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4Model
public import CFSG.RankThree.PartOne.K1320.Row7Gen
public import CFSG.RankThree.PartOne.SP4C.WeylTorus

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open Matrix CFSG CFSG.RankThree
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor spRev b7 b7' coe_b7 coe_b7' spBlock spBlock'
  coe_spBlock coe_spBlock' blk22 blk4 perfectResidual_centralizer_b7
  perfectResidual_centralizer_b7' d8Vec_four permGL)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD coe_torusD torusD_apply weyl₁ weyl₂ conj_weyl₁
  conj_weyl₂ zpowers_torusD_inv line_cases perfectResidual_conj)

theorem perfCent_zpowers_coe {G : Type} [Group G] [Finite G] (Y : Subgroup G) (y : Y) :
    perfCent Y (Subgroup.zpowers (y : G)) =
      (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set Y))).map Y.subtype := by
  rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ Y.subtype_injective,
    perfCent]
  congr 1
  ext x
  rw [Subgroup.mem_inf, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_map]
  constructor
  · rintro ⟨hxY, hx⟩
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact Subtype.ext hx
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    refine ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hz

section Blocks

variable {K : Type} [Field K]

theorem blk22_mul_conj (A B : Matrix (Fin 2) (Fin 2) K) :
    blk22 A * (blk22 B).submatrix tau₁.symm tau₁.symm =
      (blk22 B).submatrix tau₁.symm tau₁.symm * blk22 A := by
  obtain ⟨hs, -, h0, h1, h2, h3⟩ := tau₁_facts
  rw [hs]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blk22, Matrix.mul_apply, Fin.sum_univ_four, Matrix.submatrix_apply, h0, h1, h2, h3]

theorem blk4_mul_conj (A B : Matrix (Fin 2) (Fin 2) K) :
    blk4 A * (blk4 B).submatrix tau₂.symm tau₂.symm =
      (blk4 B).submatrix tau₂.symm tau₂.symm * blk4 A := by
  obtain ⟨hs, -, h0, h1, h2, h3⟩ := tau₂_facts
  rw [hs]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blk4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.submatrix_apply, h0, h1, h2, h3,
      mul_comm]

variable [CharP K 2]

theorem commutator_spBlock_weyl₁ :
    ⁅((spBlock (K := K)).range.map (spRev K).subtype).map (MulAut.conj weyl₁).toMonoidHom,
      (spBlock (K := K)).range.map (spRev K).subtype⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
  apply Units.ext
  change (((spBlock B : spRev K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((weyl₁ * ((spBlock A : spRev K) : GL (Fin 4) K) * weyl₁⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
    ((weyl₁ * ((spBlock A : spRev K) : GL (Fin 4) K) * weyl₁⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *
      (((spBlock B : spRev K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  rw [weyl₁_eq, coe_permGL_conj, coe_spBlock, coe_spBlock]
  exact blk22_mul_conj _ _

theorem commutator_spBlock'_weyl₂ :
    ⁅(spBlock' (K := K)).range.map (spRev K).subtype,
      ((spBlock' (K := K)).range.map (spRev K).subtype).map (MulAut.conj weyl₂).toMonoidHom⁆ =
      ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩
  apply Units.ext
  change ((weyl₂ * ((spBlock' B : spRev K) : GL (Fin 4) K) * weyl₂⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) *
      (((spBlock' A : spRev K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    (((spBlock' A : spRev K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((weyl₂ * ((spBlock' B : spRev K) : GL (Fin 4) K) * weyl₂⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)
  rw [weyl₂_eq, coe_permGL_conj, coe_spBlock', coe_spBlock']
  exact (blk4_mul_conj _ _).symm

theorem sup_spBlock_spBlock' :
    (spBlock (K := K)).range.map (spRev K).subtype ⊔
      (spBlock' (K := K)).range.map (spRev K).subtype = spRev K := by
  rw [← Subgroup.map_sup, CFSG.RankThree.PartOne.K1320.spBlock_sup_spBlock'_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem entry_one_one_of_mem_spBlock {x : GL (Fin 4) K}
    (hx : x ∈ (spBlock (K := K)).range.map (spRev K).subtype) :
    (x : Matrix (Fin 4) (Fin 4) K) 1 1 = 1 := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
  change blk22 (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
  simp [blk22]

theorem entry_zero_zero_of_mem_spBlock' {x : GL (Fin 4) K}
    (hx : x ∈ (spBlock' (K := K)).range.map (spRev K).subtype) :
    (x : Matrix (Fin 4) (Fin 4) K) 0 0 = (x : Matrix (Fin 4) (Fin 4) K) 2 2 := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
  change blk4 (A : Matrix (Fin 2) (Fin 2) K) 0 0 = blk4 (A : Matrix (Fin 2) (Fin 2) K) 2 2
  simp [blk4]

end Blocks

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b : ℕ}

theorem model_Sp4 (hb : 0 < b) (hbe : Even b) (hK : Nat.card K = 2 ^ b) :
    ∀ ℓ₁ ℓ₂ c₁ c₂ : Subgroup (GL (Fin 4) K), ℓ₁ ≤ d8Tor 3 K 4 → ℓ₂ ≤ d8Tor 3 K 4 →
      c₁ ≤ d8Tor 3 K 4 → c₂ ≤ d8Tor 3 K 4 → Nat.card ℓ₁ = 3 → Nat.card ℓ₂ = 3 →
      Nat.card c₁ = 3 → Nat.card c₂ = 3 → ℓ₁ ≠ ℓ₂ →
      c₁ ≤ perfCent (spRev K) ℓ₁ → c₂ ≤ perfCent (spRev K) ℓ₂ →
        (c₁ = ℓ₂ → c₂ = ℓ₁ ∧ ⁅perfCent (spRev K) ℓ₁, perfCent (spRev K) ℓ₂⁆ = ⊥) ∧
        (c₁ ≠ ℓ₂ → perfCent (spRev K) ℓ₁ ⊔ perfCent (spRev K) ℓ₂ = spRev K) := by
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb2
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_two_pow_sub_one hbe
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd hdvd
  have : Nontrivial (rootsOfUnity 3 K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 K)
  set ζ : Kˣ := (ω : Kˣ) with hζ
  have hζ3 : ζ ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ω.2
  have hζ1 : ζ ≠ 1 := fun h => hω (Subtype.ext h)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply hζ1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hζ3, h, inv_one, one_mul]
  set a : K := ((ω : Kˣ) : K) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have haa : a * a ≠ 1 := by
    intro h
    apply ha1
    calc a = a ^ 3 * (a * a)⁻¹ := by field_simp
      _ = 1 := by rw [ha3, h, inv_one, one_mul]
  have hainv : a ≠ a⁻¹ := fun h => haa (by
    calc a * a = a * a⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ ha0)
  have hainv1 : a⁻¹ ≠ 1 := fun h => ha1 (by rw [← inv_inv a, h, inv_one])
  have hval : (((ω : Kˣ)⁻¹ : Kˣ) : K) = a⁻¹ := Units.val_inv_eq_inv_val _
  have hw₁ : weyl₁ ∈ spRev K := CFSG.RankThree.PartOne.SP4C.hP_spRev _ (by decide)
  have hw₂ : weyl₂ ∈ spRev K := CFSG.RankThree.PartOne.SP4C.hP_spRev _ (by decide)
  obtain ⟨hww₁, hww₂⟩ := weyl_mul_self (F := K)
  set P : Subgroup (GL (Fin 4) K) := (spBlock (K := K)).range.map (spRev K).subtype with hPdef
  set Q : Subgroup (GL (Fin 4) K) := (spBlock' (K := K)).range.map (spRev K).subtype with hQdef
  have e2 : torusD ((1, ω) : D8Mod 3 K) = ((b7 ζ : ↥(spRev K)) : GL (Fin 4) K) := by
    rw [coe_b7, torusD_apply, d8Vec_four]
    rfl
  have e3 : torusD ((ω, ω) : D8Mod 3 K) = ((b7' ζ : ↥(spRev K)) : GL (Fin 4) K) := by
    rw [coe_b7', torusD_apply, d8Vec_four]
  have hL₂ : (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))).map
      (MulAut.conj weyl₁).toMonoidHom = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₁ ((ω, 1) : D8Mod 3 K)
  have hL₁ : (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K))).map
      (MulAut.conj weyl₁).toMonoidHom = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₁ ((1, ω) : D8Mod 3 K)
  have hL₃₁ : (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))).map
      (MulAut.conj weyl₁).toMonoidHom = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₁ ((ω, ω) : D8Mod 3 K)
  have hL₄ : (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₂ ((ω, ω) : D8Mod 3 K)
  have hL₂₂ : (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K)) := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (weyl₂ * torusD ((1, ω) : D8Mod 3 K) * weyl₂⁻¹) = _
    rw [conj_weyl₂, show ((((1, ω) : D8Mod 3 K)).1, ((1, ω) : D8Mod 3 K).2⁻¹) =
      ((1, ω) : D8Mod 3 K)⁻¹ by simp, zpowers_torusD_inv]
  have hL₁₂ : (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change weyl₂ * torusD ((ω, 1) : D8Mod 3 K) * weyl₂⁻¹ = _
    rw [conj_weyl₂, inv_one]
  have hS₂ : perfCent (spRev K) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K))) = P := by
    rw [e2, perfCent_zpowers_coe, perfectResidual_centralizer_b7 hK4 hζ1 hζ2]
  have hS₃ : perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))) = Q := by
    rw [e3, perfCent_zpowers_coe, perfectResidual_centralizer_b7' hK4 hζ2]
  have hS₁ : perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))) =
      P.map (MulAut.conj weyl₁).toMonoidHom := by
    rw [← hL₁, perfCent, perfectResidual_conj hw₁]
    exact congrArg _ hS₂
  have hS₄ : perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K))) =
      Q.map (MulAut.conj weyl₂).toMonoidHom := by
    rw [← hL₄, perfCent, perfectResidual_conj hw₂]
    exact congrArg _ hS₃
  have hP : ∀ v : D8Mod 3 K, torusD v ∈ P → ((v.2 : Kˣ) : K) = 1 := fun v h => by
    have h1 := entry_one_one_of_mem_spBlock h
    rw [coe_torusD] at h1
    simpa using h1
  have hQ : ∀ v : D8Mod 3 K, torusD v ∈ Q → ((v.1 : Kˣ) : K) = (((v.2 : Kˣ)⁻¹ : Kˣ) : K) :=
    fun v h => by
      have h1 := entry_zero_zero_of_mem_spBlock' h
      rw [coe_torusD] at h1
      simpa using h1
  have n₂₂ : torusD ((1, ω) : D8Mod 3 K) ∉ P := fun h => ha1 (hP _ h)
  have n₂₃ : torusD ((ω, ω) : D8Mod 3 K) ∉ P := fun h => ha1 (hP _ h)
  have n₂₄ : torusD ((ω, ω⁻¹) : D8Mod 3 K) ∉ P := fun h => by
    have := hP _ h
    simp only at this
    rw [Subgroup.coe_inv, hval] at this
    exact hainv1 this
  have n₁₁ : torusD ((ω, 1) : D8Mod 3 K) ∉ P.map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj_of_inv hww₁ (by rw [conj_weyl₁]; exact n₂₂)
  have n₁₃ : torusD ((ω, ω) : D8Mod 3 K) ∉ P.map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj_of_inv hww₁ (by rw [conj_weyl₁]; exact n₂₃)
  have n₁₄ : torusD ((ω, ω⁻¹) : D8Mod 3 K) ∉ P.map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj_of_inv hww₁ (by rw [conj_weyl₁]; exact fun h => ha1 (hP _ h))
  have n₃₁ : torusD ((ω, 1) : D8Mod 3 K) ∉ Q := fun h => hω (by simpa using hQ _ h)
  have n₃₂ : torusD ((1, ω) : D8Mod 3 K) ∉ Q := fun h => by
    have := hQ _ h
    simp only [OneMemClass.coe_one, Units.val_one] at this
    rw [hval] at this
    exact hainv1 this.symm
  have n₃₃ : torusD ((ω, ω) : D8Mod 3 K) ∉ Q := fun h => by
    have := hQ _ h
    simp only at this
    rw [hval] at this
    exact hainv this
  have n₄₁ : torusD ((ω, 1) : D8Mod 3 K) ∉ Q.map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj_of_inv hww₂ (by rw [conj_weyl₂, inv_one]; exact n₃₁)
  have n₄₂ : torusD ((1, ω) : D8Mod 3 K) ∉ Q.map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj_of_inv hww₂ (by
      rw [conj_weyl₂]
      intro h
      have := hQ _ h
      simp only [OneMemClass.coe_one, Units.val_one] at this
      exact ha1 this.symm)
  have n₄₄ : torusD ((ω, ω⁻¹) : D8Mod 3 K) ∉ Q.map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj_of_inv hww₂ (by rw [conj_weyl₂, inv_inv]; exact n₃₃)
  have hpartner : ∀ ℓ c : Subgroup (GL (Fin 4) K), ℓ ≤ d8Tor 3 K 4 → Nat.card ℓ = 3 →
      c ≤ d8Tor 3 K 4 → Nat.card c = 3 → c ≤ perfCent (spRev K) ℓ →
      (ℓ = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K)) ∧
          c = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K))) ∨
        (ℓ = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K)) ∧
          c = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))) ∨
        (ℓ = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K)) ∧
          c = Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K))) ∨
        (ℓ = Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K)) ∧
          c = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))) := by
    intro ℓ c hℓ hℓ3 hc hc3 hcS
    rcases line_cases hμ hω hℓ hℓ3 with rfl | rfl | rfl | rfl <;>
      rcases line_cases hμ hω hc hc3 with rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₁₁)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₁₃)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₁₄)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₂₂)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₂₃)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₂₄)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₃₁)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₃₂)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₃₃)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₄₁)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₄₂)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₄₄)
  have hvac : ∀ ℓ c c' : Subgroup (GL (Fin 4) K), c ≤ perfCent (spRev K) ℓ → c = c' →
      ∀ x, c' = Subgroup.zpowers x → x ∈ perfCent (spRev K) ℓ := by
    intro ℓ c c' h e x hx
    rw [e, hx] at h
    exact h (Subgroup.mem_zpowers x)
  have g23 : perfCent (spRev K) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K))) ⊔
      perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))) = spRev K := by
    rw [hS₂, hS₃]
    exact sup_spBlock_spBlock'
  have g13 : perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))) ⊔
      perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))) = spRev K := by
    have h := sup_perfCent_conj hw₁ g23
    rwa [hL₁, hL₃₁] at h
  have g24 : perfCent (spRev K) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K))) ⊔
      perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K))) = spRev K := by
    have h := sup_perfCent_conj hw₂ g23
    rwa [hL₂₂, hL₄] at h
  have g14 : perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))) ⊔
      perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K))) = spRev K := by
    have h := sup_perfCent_conj hw₂ g13
    rwa [hL₁₂, hL₄] at h
  have c12 : ⁅perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 K))),
      perfCent (spRev K) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 K)))⁆ = ⊥ := by
    rw [hS₁, hS₂]
    exact commutator_spBlock_weyl₁
  have c34 : ⁅perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 K))),
      perfCent (spRev K) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 K)))⁆ = ⊥ := by
    rw [hS₃, hS₄]
    exact commutator_spBlock'_weyl₂
  intro ℓ₁ ℓ₂ c₁ c₂ h₁ h₂ hc₁ hc₂ h₁3 h₂3 hc₁3 hc₂3 hne hc₁S hc₂S
  rcases hpartner ℓ₁ c₁ h₁ h₁3 hc₁ hc₁3 hc₁S with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hpartner ℓ₂ c₂ h₂ h₂3 hc₂ hc₂3 hc₂S with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd rfl hne
  · exact ⟨fun _ => ⟨rfl, c12⟩, fun h => absurd rfl h⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₁]; exact n₁₃), fun _ => g13⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₁]; exact n₁₄), fun _ => g14⟩
  · exact ⟨fun _ => ⟨rfl, by rw [Subgroup.commutator_comm]; exact c12⟩, fun h => absurd rfl h⟩
  · exact absurd rfl hne
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₂]; exact n₂₃), fun _ => g23⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₂]; exact n₂₄), fun _ => g24⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₃]; exact n₃₁),
      fun _ => by rw [sup_comm]; exact g13⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₃]; exact n₃₂),
      fun _ => by rw [sup_comm]; exact g23⟩
  · exact absurd rfl hne
  · exact ⟨fun _ => ⟨rfl, c34⟩, fun h => absurd rfl h⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₄]; exact n₄₁),
      fun _ => by rw [sup_comm]; exact g14⟩
  · exact ⟨fun h => absurd (hvac _ _ _ hc₁S h _ rfl) (by rw [hS₄]; exact n₄₂),
      fun _ => by rw [sup_comm]; exact g24⟩
  · exact ⟨fun _ => ⟨rfl, by rw [Subgroup.commutator_comm]; exact c34⟩, fun h => absurd rfl h⟩
  · exact absurd rfl hne

end Model

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
