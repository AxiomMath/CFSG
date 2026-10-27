module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Model
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Assembly.Subnormal
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Pre
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5SylowOdd
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.QuasithinUnique CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.BorelTits CFSG.LieType.TitsSimplicity

section Generic

variable {X Y : Type} [Group X] [Group Y]

theorem isSylowTwoOf_map_surj (π : X →* Y) (hπ : Function.Surjective π) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) : IsSylowTwoOf (U.map π) ⊤ := by
  obtain ⟨-, hp, hi⟩ := hU
  refine ⟨le_top, hp.map π, ?_⟩
  change ¬ 2 ∣ U.relIndex ⊤ at hi
  change ¬ 2 ∣ (U.map π).relIndex ⊤
  rw [Subgroup.relIndex_top_right] at hi ⊢
  rw [Subgroup.index_map, MonoidHom.range_eq_top.2 hπ, Subgroup.index_top, mul_one]
  exact fun h => hi (h.trans (Subgroup.index_dvd_of_le le_sup_left))

end Generic

section Center

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem un5_center_le_unT :
    Subgroup.center (SU (unitaryInvolution F 2 f) 5) ≤ unT (F := F) (p := 2) (f := f) 5 := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  rw [center_eq_normalCore_borel (un5_isCTGroupDatum hF ζ)
    (steinbergExtras hF 5 (by norm_num) ζ hζ)
    (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ)]
  exact normalCore_borel_le_iSup (un5_isCTGroupDatum hF ζ)
    (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ)

@[expose] def un5Proj : SU (unitaryInvolution F 2 f) 5 →*
    SU (unitaryInvolution F 2 f) 5 ⧸ Subgroup.center (SU (unitaryInvolution F 2 f) 5) :=
  QuotientGroup.mk' _

theorem un5Proj_surjective : Function.Surjective (un5Proj (F := F) (f := f)) :=
  QuotientGroup.mk'_surjective _

theorem ker_un5Proj : (un5Proj (F := F) (f := f)).ker =
    Subgroup.center (SU (unitaryInvolution F 2 f) 5) := QuotientGroup.ker_mk' _

theorem un5_U_inf_ker : unU hF 5 ⊓ (un5Proj (F := F) (f := f)).ker = ⊥ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  rw [eq_bot_iff]
  intro x hx
  have hT : x ∈ unT (F := F) (p := 2) (f := f) 5 :=
    un5_center_le_unT hF (by rw [← ker_un5Proj]; exact hx.2)
  have h0 := (steinbergExtras hF 5 (by norm_num) ζ hζ).torus_inf_posPart
  have h : x ∈ (⨆ i, levelTorus (unitaryInvolution F 2 f) i) ⊓
      ⨆ γ ∈ {γ | γ ∈ (rootDatum hF 5).roots ∧ 0 < ht γ}, (rootDatum hF 5).rootGroup γ :=
    ⟨hT, hx.1⟩
  exact Subgroup.mem_bot.1 (h0.le h)

theorem isSylowTwoOf_unU5 : IsSylowTwoOf (unU hF 5) ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have hT : Nat.Coprime 2 (Nat.card (⨆ i, levelTorus (unitaryInvolution F 2 f) i :
      Subgroup (SU (unitaryInvolution F 2 f) 5))) :=
    Nat.coprime_two_left.2 (odd_card_unT5 hF)
  have hcop : Nat.Coprime 2 (unU hF 5).index :=
    BorelIndex.coprime_index_posUnipotent (un5_isCTGroupDatum hF ζ)
      (steinbergExtras hF 5 (by norm_num) ζ hζ)
      (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ)
      (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
        (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hT
  refine ⟨le_top, isPGroup_unU5 hF, ?_⟩
  change ¬ 2 ∣ (unU hF 5).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop

end Center

section System

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 f)) [hζ : Fact ((ζ : F) ≠ 0)]

theorem un5_ker_le : (un5Proj (F := F) (f := f)).ker ≤ unB hF 5 ⊓ unN hF 5 ζ := by
  rw [ker_un5Proj, un5B_inf_N hF ζ]
  exact un5_center_le_unT hF

@[expose] def un5PreQ : PreRankTwoSystem (SU (unitaryInvolution F 2 f) 5 ⧸
    Subgroup.center (SU (unitaryInvolution F 2 f) 5)) 4 :=
  (un5Pre hF ζ).map un5Proj un5Proj_surjective (un5_ker_le hF ζ) (un5_U_inf_ker hF)

@[expose] def un5System : RankTwoSystem (SU (unitaryInvolution F 2 f) 5 ⧸
    Subgroup.center (SU (unitaryInvolution F 2 f) 5)) 4 :=
  haveI := isSimpleGroup_un5 hF
  (un5PreQ hF ζ).toSystemOfSimple

theorem isSylowTwoOf_un5System : IsSylowTwoOf (un5System hF ζ).U ⊤ :=
  isSylowTwoOf_map_surj un5Proj un5Proj_surjective (isSylowTwoOf_unU5 hF)

end System

end CFSG.Quasithin.H13.F431.Un
