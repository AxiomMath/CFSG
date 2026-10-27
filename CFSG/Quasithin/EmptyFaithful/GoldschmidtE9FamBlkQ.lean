module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.T1521SL2Aut

public section

namespace CFSG.Quasithin.E9.Blk

open CFSG.Open CFSG.QuasithinUnique CFSG.PSL2Table CFSG.Quasithin CFSG.Quasithin.L21521
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem blockQ_le_blockU [Finite G] {L : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hLL : ⁅L, L⁆ = L)
    {F : Type} [Field F] [Finite F] (hK : Nat.card F = 2 ^ n) (α : ↥L →* SL(2, F))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) :
    blockQ L ≤ blockU L := by
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) := le_normalizer_pCoreOf 2 L
  have hUQ : blockU L ≤ blockQ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hLQ
  have hUL : blockU L ≤ L := hUQ.trans (pCoreOf_le 2 L)
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ L) L
  set N : Subgroup ↥L := (blockU L).subgroupOf L with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr hLU
  have hNker : N ≤ α.ker := by
    intro x hx
    rw [hαk, AppC.mem_pCore_iff_mem_blockQ]
    exact hUQ (Subgroup.mem_subgroupOf.mp hx)
  let η : ↥L ⧸ N →* SL(2, F) := QuotientGroup.lift N α hNker
  have hηs : Function.Surjective η := fun y => by
    obtain ⟨x, rfl⟩ := hαs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hperfL : commutator ↥L = ⊤ := by
    have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    have h2 : (commutator ↥L).map L.subtype = (⊤ : Subgroup ↥L).map L.subtype := by
      rw [h1, hLL, Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective L.subtype_injective h2
  have : Group.IsPerfect ↥L := ⟨hperfL⟩
  have hker : ∀ x : ↥L, η (QuotientGroup.mk x) = 1 → (x : G) ∈ blockQ L := fun x hx => by
    have h1 : α x = 1 := hx
    rw [← MonoidHom.mem_ker, hαk, AppC.mem_pCore_iff_mem_blockQ] at h1
    exact h1
  have hcentral : η.ker ≤ Subgroup.center (↥L ⧸ N) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxQ := hker x hy
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    have h3 : ⁅(x : G)⁻¹, (l : G)⁻¹⁆ ∈ blockU L :=
      Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxQ) (L.inv_mem l.2)
    have e : (((l * x)⁻¹ * (x * l) : ↥L) : G) = ⁅(x : G)⁻¹, (l : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact h3
  have hp : IsPGroup 2 η.ker := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y.1
    have hx' : x ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      have := y.2
      rw [MonoidHom.mem_ker, ← hx] at this
      exact this
    rw [hαk] at hx'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hx'⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    show (y.1) ^ 2 ^ k = 1
    rw [← hx, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have hbot := CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot n hn
    hK η hηs hcentral hp
  intro q hq
  have hqL : q ∈ L := pCoreOf_le 2 L hq
  have h1 : (QuotientGroup.mk (⟨q, hqL⟩ : ↥L) : ↥L ⧸ N) ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    show α ⟨q, hqL⟩ = 1
    rw [← MonoidHom.mem_ker, hαk, AppC.mem_pCore_iff_mem_blockQ]
    exact hq
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem eq_zero_of_fixed_conj_diag {F : Type} [Field F] {a : Fˣ} (ha : (a : F) ≠ 1)
    (A : SL(2, F)) (x : Fin 2 → F)
    (hx : ((A * diag a * A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec x = x) : x = 0 := by
  set Am : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hA
  set Ai : Matrix (Fin 2) (Fin 2) F := ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) with hAi
  set D : Matrix (Fin 2) (Fin 2) F := (diag a : Matrix (Fin 2) (Fin 2) F) with hD
  have hAiA : Ai * Am = 1 := by
    rw [hA, hAi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have hAAi : Am * Ai = 1 := by
    rw [hA, hAi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have hfix' : (Am * D * Ai).mulVec x = x := by
    have : ((A * diag a * A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = Am * D * Ai := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hA, hAi, hD]
    rw [← this]; exact hx
  have hy : D.mulVec (Ai.mulVec x) = Ai.mulVec x := by
    have e : D * Ai = Ai * (Am * D * Ai) := by
      rw [← mul_assoc, ← mul_assoc, hAiA, one_mul]
    calc D.mulVec (Ai.mulVec x) = (D * Ai).mulVec x := by rw [Matrix.mulVec_mulVec]
      _ = (Ai * (Am * D * Ai)).mulVec x := by rw [e]
      _ = Ai.mulVec ((Am * D * Ai).mulVec x) := by rw [← Matrix.mulVec_mulVec]
      _ = Ai.mulVec x := by rw [hfix']
  set w : Fin 2 → F := Ai.mulVec x with hw
  have hD0 : (D.mulVec w) 0 = (a : F) * w 0 := by
    simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hD1 : (D.mulVec w) 1 = (a : F)⁻¹ * w 1 := by
    simp [hD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hw0 : w 0 = 0 := by
    have h0 : (a : F) * w 0 = w 0 := by rw [← hD0]; exact congrFun hy 0
    have : ((a : F) - 1) * w 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha)
  have hw1 : w 1 = 0 := by
    have h1 : (a : F)⁻¹ * w 1 = w 1 := by rw [← hD1]; exact congrFun hy 1
    have hne : (a : F)⁻¹ - 1 ≠ 0 := by
      intro h
      apply ha
      have : (a : F)⁻¹ = 1 := sub_eq_zero.mp h
      simpa using this
    have : ((a : F)⁻¹ - 1) * w 1 = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hne
  have hw' : w = 0 := by
    ext i
    fin_cases i
    · exact hw0
    · exact hw1
  calc x = (Am * Ai).mulVec x := by rw [hAAi, Matrix.one_mulVec]
    _ = Am.mulVec w := by rw [← Matrix.mulVec_mulVec]
    _ = 0 := by rw [hw', Matrix.mulVec_zero]

theorem mem_blockZ_of_commute {L : Subgroup G} {F : Type} [Field F] (α : ↥L →* SL(2, F))
    (β : blockU L →* Multiplicative (Fin 2 → F))
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ ℓ : ↥L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {a : Fˣ} (ha : (a : F) ≠ 1) {A : SL(2, F)} {b : ↥L} (hb : α b = A * diag a * A⁻¹)
    {u : G} (hu : u ∈ blockU L) (hcomm : (b : G) * u = u * (b : G)) : u ∈ blockZ L := by
  have hfix := (hβe b ⟨u, hu⟩ ⟨u, hu⟩ (by
    show u = (b : G) * u * (b : G)⁻¹
    rw [hcomm]; group)).symm
  rw [hb] at hfix
  have h0 := eq_zero_of_fixed_conj_diag ha A _ hfix
  have h1 : β ⟨u, hu⟩ = 1 := by
    rw [← toAdd_eq_zero]
    exact h0
  have hker : (⟨u, hu⟩ : ↥(blockU L)) ∈ β.ker := MonoidHom.mem_ker.mpr h1
  rw [hβk] at hker
  exact Subgroup.mem_subgroupOf.mp hker

theorem commutator_mem_pCoreOf_of_rigid [Finite G] {L : Subgroup G} {Λ : Type} [Group Λ]
    {π : ↥L →* Λ} (hπ : Function.Surjective π) (hker : π.ker = CFSG.pCore 2 ↥L) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hrig : ∀ β : MulAut Λ,
      (∀ x : ↥L, v * (x : G) = (x : G) * v → β (π x) = π x) → β = 1) :
    ∀ l ∈ L, ⁅l, v⁆ ∈ pCoreOf 2 L := by
  classical
  set σ : MulAut ↥L := conjAct L ⟨v, hv⟩ with hσdef
  have hσ : ∀ x : ↥L, ((σ x : ↥L) : G) = v * x * v⁻¹ := fun x => rfl
  have hker' : π.ker.map σ.toMonoidHom = π.ker := by
    rw [hker]
    exact Subgroup.characteristic_iff_map_eq.mp (CFSG.pCore_characteristic (G := ↥L) (p := 2)) σ
  let e : (↥L ⧸ π.ker) ≃* Λ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let σ' : (↥L ⧸ π.ker) ≃* (↥L ⧸ π.ker) := QuotientGroup.congr π.ker π.ker σ hker'
  let β : MulAut Λ := e.symm.trans (σ'.trans e)
  have hβ : ∀ x : ↥L, β (π x) = π (σ x) := by
    intro x
    have h1 : e (QuotientGroup.mk x) = π x := rfl
    have h2 : e.symm (π x) = QuotientGroup.mk x := by rw [← h1]; exact e.symm_apply_apply _
    show e (σ' (e.symm (π x))) = π (σ x)
    rw [h2]
    rfl
  have hβ1 : β = 1 := by
    apply hrig
    intro x hx
    rw [hβ]
    congr 1
    apply Subtype.ext
    rw [hσ]
    have e : v * (x : G) * v⁻¹ = (x : G) := by rw [hx]; group
    exact e
  intro l hl
  have hall : ∀ x : ↥L, π (σ x) = π x := by
    intro x
    have := congrArg (fun γ : MulAut Λ => γ (π x)) hβ1
    simp only [MulAut.one_apply] at this
    rw [← hβ]; exact this
  have hl' : (⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hall]; simp
  have hq : (⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := hker ▸ hl'
  have hmem : (⟨l, hl⟩ : ↥L) * ((⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩)⁻¹ * (⟨l, hl⟩ : ↥L)⁻¹ ∈
      CFSG.pCore 2 ↥L :=
    Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hq) _
  have heq : ⁅l, v⁆ = (((⟨l, hl⟩ : ↥L) * ((⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩)⁻¹ *
      (⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
    group
  rw [heq]
  exact ⟨_, hmem, rfl⟩

end CFSG.Quasithin.E9.Blk
