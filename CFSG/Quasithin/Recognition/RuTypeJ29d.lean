module

public import CFSG.Quasithin.Recognition.RuTypeJ29c
public import CFSG.GH74.Uniqueness.SE
public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

noncomputable abbrev L0G (s : G) : Subgroup G :=
  (CFSG.BenderSuzuki.involutionCore (Ls s)).map (Ls s).subtype

omit M in
theorem L0G_le_Ls (s : G) : L0G s ≤ Ls s := Subgroup.map_subtype_le _

omit M in
theorem mem_involutionCore {s x : G} (hx : x ∈ Ls s) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    (⟨x, hx⟩ : Ls s) ∈ CFSG.BenderSuzuki.involutionCore (Ls s) :=
  Subgroup.subset_closure (show (⟨x, hx⟩ : Ls s) ∈ CFSG.BenderSuzuki.involutionsSet (Ls s) from
    ⟨fun h => hx1 (congrArg Subtype.val h), Subtype.ext (by simpa using hx2)⟩)

omit M in
theorem mem_L0G_of_inv {s x : G} (hx : x ∈ Ls s) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) : x ∈ L0G s :=
  ⟨⟨x, hx⟩, mem_involutionCore hx hx1 hx2, rfl⟩

omit M in
theorem conj_mem_L0G {s g x : G} (hg : g ∈ Cen s) (hx : x ∈ L0G s) : g * x * g⁻¹ ∈ L0G s := by
  have hn := CFSG.GorensteinWalter.pResidualOf_subgroupOf_normal (Cen s) 2
  have hconj : ∀ y ∈ Ls s, g * y * g⁻¹ ∈ Ls s := fun y hy => by
    have := hn.conj_mem ⟨y, Ls_le_Cen s hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  let φ : Ls s →* Ls s :=
    { toFun := fun y => ⟨g * y * g⁻¹, hconj y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hle : (CFSG.BenderSuzuki.involutionCore (Ls s)).map φ ≤
      CFSG.BenderSuzuki.involutionCore (Ls s) := by
    rw [Subgroup.map_le_iff_le_comap, CFSG.BenderSuzuki.involutionCore, Subgroup.closure_le]
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    refine Subgroup.subset_closure (show φ y ∈ CFSG.BenderSuzuki.involutionsSet (Ls s) from ?_)
    refine ⟨fun h => hy1 ?_, ?_⟩
    · apply Subtype.ext
      have := congrArg Subtype.val h
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
      calc (y : G) = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    · rw [← map_pow, hy2, map_one]
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨φ y, hle ⟨y, hy, rfl⟩, rfl⟩

theorem twoRank_L0 {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo
      (CFSG.BenderSuzuki.involutionCore (Ls s)) := by
  set w := (M.cel : G) * M.z * (M.cel : G)⁻¹ with hwdef
  have hwV : w ∈ ruV M.L := M.toRuData.conj_mem_V M.cel.2 M.z_mem_V
  have hzw : w ≠ M.z := by
    intro h
    have h' : (M.cel : G) * (⟨M.z, M.z_mem_V⟩ : ruV M.L) * (M.cel : G)⁻¹ =
        (⟨M.z, M.z_mem_V⟩ : ruV M.L) := h
    have h0 := SL3.c0_fix_vec _ ((M.conj_cel_V ⟨M.z, M.z_mem_V⟩).mp h')
    rw [show (⟨M.z, M.z_mem_V⟩ : ruV M.L) = M.zV from rfl, M.ψV_zV] at h0
    exact absurd h0 (by decide)
  have hw1 : w ≠ 1 := fun h => M.z_ne_one (by
    have : M.z = (M.cel : G)⁻¹ * w * M.cel := by rw [hwdef]; group
    rw [this, h]; group)
  have hVLs : ∀ v ∈ ruV M.L, v ∈ Ls s := fun v hv => M.S1_le_Ls hs hs1 (M.V_le_S1 hv)
  set L0 := CFSG.BenderSuzuki.involutionCore (Ls s)
  let zL : L0 := ⟨⟨M.z, hVLs _ M.z_mem_V⟩, mem_involutionCore _ M.z_ne_one M.z_sq⟩
  let wL : L0 := ⟨⟨w, hVLs _ hwV⟩, mem_involutionCore _ hw1 (M.sq_eq_one_of_V hwV)⟩
  have hsq : ∀ (v : G) (hv : v ∈ ruV M.L) (hvL : (⟨v, hVLs v hv⟩ : Ls s) ∈ L0),
      (⟨⟨v, hVLs v hv⟩, hvL⟩ : L0) * ⟨⟨v, hVLs v hv⟩, hvL⟩ = 1 := by
    intro v hv hvL
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_mul, OneMemClass.coe_one]
    rw [← pow_two]
    exact M.sq_eq_one_of_V hv
  have hz2 : zL * zL = 1 := hsq _ M.z_mem_V _
  have hw2 : wL * wL = 1 := hsq _ hwV _
  have hzwc : zL * wL = wL * zL := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (M.V_comm_S M.z_mem_V (M.toRuData.V_le_S hwV)).symm
  have hz1 : zL ≠ 1 := fun h => M.z_ne_one (congrArg (fun x : L0 => ((x : Ls s) : G)) h)
  have hwL1 : wL ≠ 1 := fun h => hw1 (congrArg (fun x : L0 => ((x : Ls s) : G)) h)
  have hne : zL ≠ wL := fun h => hzw (congrArg (fun x : L0 => ((x : Ls s) : G)) h).symm
  have := isKleinFour_fourSub hz2 hw2 hzwc hz1 hwL1 hne
  have hsqE : ∀ x : fourSub zL wL hz2 hw2 hzwc, x ^ 2 = 1 := by
    intro x
    have hx2 : (x : L0) ^ 2 = 1 := by
      rcases mem_fourSub.mp x.2 with h | h | h | h <;> rw [h, pow_two]
      · exact one_mul 1
      · exact hz2
      · exact hw2
      · rw [← mul_assoc, mul_assoc zL wL zL, ← hzwc, ← mul_assoc, hz2, one_mul, hw2]
    exact Subtype.ext (by simpa using hx2)
  exact ⟨fourSub zL wL hz2 hw2 hzwc, IsKleinFour.card_four, hsqE⟩

theorem twoPrimeCore_L0_eq_bot
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    CFSG.BenderSuzuki.twoPrimeCore (CFSG.BenderSuzuki.involutionCore (Ls s)) = ⊥ := by
  set L0 := CFSG.BenderSuzuki.involutionCore (Ls s)
  rw [CFSG.BenderSuzuki.twoPrimeCore, CFSG.pPrimeCore_eq_bot_iff]
  intro K hKn hKc
  set KG : Subgroup G := (K.map L0.subtype).map (Ls s).subtype with hKG
  have hcard : Nat.card KG = Nat.card K := by
    rw [hKG, Subgroup.card_map_of_injective (Ls s).subtype_injective,
      Subgroup.card_map_of_injective L0.subtype_injective]
  have hKGC : KG ≤ Cen s := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact Ls_le_Cen s y.2
  have hodd : Odd (Nat.card KG) := by
    rw [hcard]
    exact Nat.coprime_two_left.mp hKc
  have hVLs : ∀ v ∈ ruV M.L, v ∈ Ls s := fun v hv => M.S1_le_Ls hs hs1 (M.V_le_S1 hv)
  have hXV : ∀ v ∈ ruV M.L, ∀ x ∈ KG, v * x * v⁻¹ ∈ KG := by
    intro v hv x hx
    obtain ⟨y, ⟨k, hk, rfl⟩, rfl⟩ := hx
    by_cases hv1 : v = 1
    · subst hv1
      exact ⟨_, ⟨k, hk, rfl⟩, by simp⟩
    let vL : L0 := ⟨⟨v, hVLs v hv⟩, mem_involutionCore _ hv1 (M.sq_eq_one_of_V hv)⟩
    refine ⟨L0.subtype (vL * k * vL⁻¹), ⟨vL * k * vL⁻¹, hKn.conj_mem k hk vL, rfl⟩, ?_⟩
    simp [vL]
  have hbot := M.eq_bot_of_odd hs hs1 hKGC hodd hXV
  rw [eq_bot_iff]
  intro k hk
  have hkG : (((k : L0) : Ls s) : G) ∈ KG := ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hkG
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext hkG))

theorem bender_L0
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    CFSG.BenderSuzuki.IsSimpleBenderGroup (CFSG.BenderSuzuki.involutionCore (Ls s)) := by
  have hSE := CFSG.BenderSuzuki.theorem_SE _ (M.isStronglyEmbedded_Ls hs hs1)
  rcases hSE with h | h
  · exact absurd (M.twoRank_L0 hs hs1) h
  · obtain ⟨hB, -, -⟩ := h
    exact hB.map_mulEquiv ((QuotientGroup.quotientMulEquivOfEq
      (M.twoPrimeCore_L0_eq_bot hs hs1)).trans QuotientGroup.quotientBot)

theorem exists_benderType_L0
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ∃ n i e, CFSG.GH74.Uniqueness.Bender.BenderType
      (CFSG.BenderSuzuki.involutionCore (Ls s)) n i e :=
  CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp
    (CFSG.GH74.Uniqueness.isBenderGroup_of_isSimpleBenderGroup (M.bender_L0 hs hs1))

end RuDataM

end CFSG.Quasithin.RuType
