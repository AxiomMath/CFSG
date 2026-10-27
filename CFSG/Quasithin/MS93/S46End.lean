module

public import CFSG.Quasithin.MS93.S46Fin
public import CFSG.Quasithin.MS93.S46I465

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A

section Transport

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem relIndex_imM {K K' : Subgroup G} (hK' : K' ≤ M) :
    (imM hTM K).relIndex (imM hTM K') = K.relIndex K' := by
  rw [imM, imM, Subgroup.relIndex_map_map_of_injective _ _ (puAmalgam hTM).ofA_injective,
    Subgroup.relIndex_subgroupOf hK']

end Transport

section Index

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem sq_eq_one_of_mem_Xq {x : G} (hx : x ∈ Xq M) : x ^ 2 = 1 := by
  have hle : Xq M ≤ centerOf (pCoreOf 2 M) := PU.omegaOneCenterOf_le_centerOf _
  have hmem : ∀ y ∈ Subgroup.closure {y | y ∈ centerOf (pCoreOf 2 M) ∧ y ^ 2 = 1}, y ∈ Xq M :=
    fun y hy => hy
  have hx' : x ∈ Subgroup.closure {y | y ∈ centerOf (pCoreOf 2 M) ∧ y ^ 2 = 1} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a :=
      Subgroup.mem_centralizer_iff.mp (hle (hmem b hb)).2 a (hle (hmem a ha)).1
    rw [(Commute.mul_pow hab 2), iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

theorem relIndex_Uq_inf_centralizer (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) :
    (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) =
      (omegaOneCenterOf T).relIndex (Z0q M T) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨-, hZM, hXZ, -⟩ := s41_holds G M T L h hfull
  have hX : Xq M = Zq M L ⊔ Uq M T L := hφ.2.2.1
  have hXT : Xq M ≤ T := (PU.omegaOneCenterOf_le _).trans h.pCore_le
  have hcomm : ∀ x ∈ Xq M, ∀ y ∈ Xq M, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (PU.omegaOneCenterOf_le_centerOf _ hy).2 x
      (PU.omegaOneCenterOf_le_centerOf _ hx).1
  have hUX : Uq M T L ≤ Xq M := hX ▸ le_sup_right
  have hZX : Zq M L ≤ Xq M := inf_le_left
  have hZT : Zq M L ≤ omegaOneCenterOf T := by
    intro z hz
    refine Subgroup.subset_closure ⟨⟨hXT (hZX hz), ?_⟩, sq_eq_one_of_mem_Xq (hZX hz)⟩
    exact Subgroup.centralizer_le (h.le) (hZM hz)
  have hinf : omegaOneCenterOf T ⊓ Uq M T L =
      Uq M T L ⊓ Subgroup.centralizer (T : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans ((PU.omegaOneCenterOf_le_centerOf T).trans
        inf_le_right))
    · rintro u ⟨huU, huc⟩
      exact ⟨Subgroup.subset_closure ⟨⟨hXT (hUX huU), huc⟩, sq_eq_one_of_mem_Xq (hUX huU)⟩, huU⟩
  rw [show Z0q M T = Uq M T L ⊔ Zq M L by rw [← hXZ, hX, sup_comm],
    relIndex_sup_of_le_of_comm hcomm hUX hZX hZT, ← hinf, Subgroup.inf_relIndex_right]

end Index

section Struct

@[expose] def I46S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ∃ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F),
      Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 ∧
      centerOf ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ = Uloc c.pu.le L α ∧
      ∃ W₁ W₂ : Subgroup (puAmalgam c.pu.le).Universal,
        W₁ ≤ ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ∧
        W₂ ≤ ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ∧
        W₁ ⊓ W₂ = Uloc c.pu.le L α ∧
        W₁ ⊔ W₂ = ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ∧
        IsSumOfNaturalModulesVia (stab _ α) W₁ (Uloc c.pu.le L α) ψ true 1 ∧
        IsSumOfNaturalModulesVia (stab _ α) W₂ (Uloc c.pu.le L α) ψ true 1

@[expose] def I46SCfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type} [Field F]
    [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → ∃ ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F),
      Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ α) (Uloc c.pu.le L α) ⊥ ψ false 1 ∧
      centerOf ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ = Uloc c.pu.le L α ∧
      ∃ W₁ W₂ : Subgroup (puAmalgam c.pu.le).Universal,
        W₁ ≤ ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ∧
        W₂ ≤ ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ∧
        W₁ ⊓ W₂ = Uloc c.pu.le L α ∧
        W₁ ⊔ W₂ = ⁅Qv (puAmalgam c.pu.le) α, Ltil c.pu.le L α⁆ ∧
        IsSumOfNaturalModulesVia (stab _ α) W₁ (Uloc c.pu.le L α) ψ true 1 ∧
        IsSumOfNaturalModulesVia (stab _ α) W₂ (Uloc c.pu.le L α) ψ true 1

end Struct

theorem case11_of_i46sCfg (h465 : I465) (h466a : I466a) {G : Type} [Group G] [Finite G]
    {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hφ : IsSL3FullVia M T L φ) (hS : I46SCfg M T L φ) : MS93Case11 (Vq M L) T L := by
  have hab := adj_baseA_baseB (puAmalgam h.le)
  have hA := isMVtx_baseA (puAmalgam h.le)
  have hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2 := by
    have := h466a G M T L F φ ⟨h, hmin, hb4, hφ⟩ _ _ hA hab
    rwa [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, puAmalgam.qv_baseB,
      relIndex_imM h.le h.le] at this
  have hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) =
      Fintype.card F := by
    have := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ _ _ hA hab).2.1
    rwa [puAmalgam.zh_baseB, puAmalgam.zm_baseA, relIndex_imM h.le (normalClosureIn_le _ _),
      ← relIndex_Uq_inf_centralizer h hφ] at this
  obtain ⟨ψ₀, hψ₀, hU₀, hZ₀, W₁, W₂, hW₁, hW₂, hinf, hsup, h₁, h₂⟩ :=
    hS ⟨h, hmin, hb4, hφ⟩ _ hA
  exact case11_of_baseA h hφ hT hU hψ₀ hU₀ hZ₀ hW₁ hW₂ hinf hsup h₁ h₂

theorem s46_of_parts (h465 : I465) (h466a : I466a) (hS : I46S) : S46 := by
  intro G _ _ M T L h hmin hb4 hfull
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  exact case11_of_i46sCfg h465 h466a h hmin hb4 hφ (hS G M T L F φ)

end CFSG.Quasithin.MS93.S46
