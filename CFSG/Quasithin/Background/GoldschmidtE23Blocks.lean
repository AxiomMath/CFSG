module

public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Background.GoldschmidtE23Mixed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace GE23

section TwoRes

variable {Y : Type*} [Group Y] [Finite Y]

theorem le_twoResidual_of_perfect {X L : Subgroup Y} (hLX : L ≤ X) (hL : Group.IsPerfect ↥L) :
    L ≤ twoResidual X := by
  have hP : Group.IsPerfect ↥(L.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLX).symm.surjective
  have h1 : L.subgroupOf X ≤ twoResidual (⊤ : Subgroup ↥X) :=
    @B6.perfect_le_twoResidual ↥X _ _ (L.subgroupOf X) hP
  rw [B6.twoResidual_top_eq_subgroupOf] at h1
  intro x hx
  have h2 := h1 (Subgroup.mem_subgroupOf.2 (show ((⟨x, hLX hx⟩ : ↥X) : Y) ∈ L from hx))
  exact Subgroup.mem_subgroupOf.1 h2

end TwoRes

section Types

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def NatBlk (X H : Subgroup (MulAut V)) : Prop :=
  ∃ (L : Subgroup (MulAut V)) (e : ℕ), CFSG.Open.IsComponentOf L X ∧ B69.blk X L = L ∧ H = L ∧
    2 ≤ e ∧ NatData L (commV L) (commV L ⊓ fixV (ffJ X)) e ∧
    ∃ A : Subgroup (MulAut V), IsFFStarMin X A ∧ ⁅L, A⁆ = L ∧ IsSylowTwoOf A L

@[expose] def SymBlk (X H : Subgroup (MulAut V)) (k : ℕ) : Prop :=
  ∃ L A : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X ∧ IsFFStarMin X A ∧ ⁅L, A⁆ = L ∧
    B69.blk X L = L ⊔ A ∧ H = L ⊔ A ∧ 2 ≤ k ∧
    ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A), Function.Surjective π ∧
      (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) (commV L) ⊥ π ∧
      L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
      ∃ i j : Fin (2 * k + 1), i ≠ j ∧
        A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)

theorem isSolvable_of_card_six {G : Type*} [Group G] [Finite G] (h : Nat.card G = 6) :
    Group.IsSolvable G := by
  have : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (a := 1) (b := 1)
    (by rw [← Nat.card_eq_fintype_card, h]; norm_num)

theorem commV_blk {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) : commV (B69.blk X L) = commV L :=
  B69.commV_blk_eq (B69.blk_le_centQuot hB.hV hB.hctx hL (hB.hact L hL))

@[expose] def NatComp (X L : Subgroup (MulAut V)) : Prop :=
  B69.blk X L = L ∧ ∃ e : ℕ, 2 ≤ e ∧ NatData L (commV L) (commV L ⊓ fixV (ffJ X)) e ∧
    ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L → IsSylowTwoOf A L

theorem comp_type' {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    NatComp X L ∨ ∃ k, SymBlk X (B69.blk X L) k := by
  classical
  have hLq := hL.2.2
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  obtain ⟨A₀, hA₀, hLA₀⟩ := hB.hact L hL
  have hW₀ : commV L ∈ IrrPlus L (⊤ : Subgroup V) :=
    B69.commV_mem_irrPlus hB.hV hB.hctx hA₀ hL hLA₀
  by_cases hAlt : ∃ A : Subgroup (MulAut V), IsFFStarMin X A ∧ ⁅L, A⁆ = L ∧
      B69.AltShape M A L (commV L)
  · obtain ⟨A, hA, hLA, hAltA⟩ := hAlt
    have hblk : B69.blk X L = L ⊔ A := le_antisymm
      (B69.blk_le_iff.2 ⟨le_sup_left, fun A' hA' hLA' =>
        hB.hG1 A L hA hL hLA hAltA A' hA' hLA'⟩)
      (sup_le B69.le_blk_self (B69.le_blk_of hA hLA))
    obtain ⟨k, hk, π, hπs, hreal, hLeq, hAsw⟩ := altShape_data hperf hnt hAltA
    exact Or.inr ⟨k, L, A, hL, hA, hLA, hblk, hblk, hk, π, hπs, hreal, hLeq, hAsw⟩
  · push Not at hAlt
    have hnat : ∀ A : Subgroup (MulAut V), IsFFStarMin X A → ⁅L, A⁆ = L →
        B69.NatShape T M A L (commV L) := fun A hA hLA =>
      (B69.compShape_iff.1 (hB.hctx A L hA hL hLA (commV L) hW₀)).resolve_right (hAlt A hA hLA)
    have hblk : B69.blk X L = L := le_antisymm
      (B69.blk_le_iff.2 ⟨le_rfl, fun A hA hLA => (hnat A hA hLA).2.1.1⟩) B69.le_blk_self
    obtain ⟨⟨e, he, hbin⟩, hsyl₀, -⟩ := hnat A₀ hA₀ hLA₀
    have h1 := B69.commV_inf_fixV_ffJ hB hL
    rw [hblk] at h1
    rw [← h1] at hbin
    refine Or.inl ⟨hblk, e, ?_, natData_of_binaryNatural hbin,
      fun A hA hLA => (hnat A hA hLA).2.1⟩
    by_contra hlt
    have he1 : e = 1 := by omega
    subst he1
    obtain ⟨K, instK, instF, hK, π', β', hπs, hβs, hβz, hUinv, hβeq⟩ :=
      natData_of_binaryNatural hbin
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, hK]
      norm_num
    have := isSolvable_of_card_six hcard
    exact Group.IsPerfect.not_isSolvable ↥L (Group.isSolvable_of_surjective hπs)

omit [Finite V] in
theorem NatComp.natBlk {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) (h : NatComp X L) :
    NatBlk X L := by
  obtain ⟨hblk, e, he, hdata, hall⟩ := h
  obtain ⟨A₀, hA₀, hLA₀⟩ := hB.hact L hL
  exact ⟨L, e, hL, hblk, rfl, he, hdata, A₀, hA₀, hLA₀, hall A₀ hA₀ hLA₀⟩

theorem comp_type {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X) :
    (B69.blk X L = L ∧ NatBlk X L) ∨ ∃ k, SymBlk X (B69.blk X L) k :=
  (comp_type' hB hL).imp (fun h => ⟨h.1, h.natBlk hB hL⟩) id

theorem block_type {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) : NatBlk X H ∨ ∃ k, SymBlk X H k := by
  obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hH
  rcases comp_type hB hL with ⟨hblk, hN⟩ | h
  · left
    rw [hblk]
    exact hN
  · exact Or.inr h

end Types

end GE23

end CFSG.Quasithin
