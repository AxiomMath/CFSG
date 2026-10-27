module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnSylowOdd
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.QuasithinUnique CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.BorelTits

section System

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)

theorem isSylowTwoOf_unU : IsSylowTwoOf (unU hF 4) ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have hT : Nat.Coprime 2 (Nat.card (⨆ i, levelTorus (unitaryInvolution F 2 f) i :
      Subgroup (SU (unitaryInvolution F 2 f) 4))) :=
    Nat.coprime_two_left.2 (odd_card_unT hF)
  have hcop : Nat.Coprime 2 (unU hF 4).index :=
    BorelIndex.coprime_index_posUnipotent (un_isCTGroupDatum hF ζ)
      (steinbergExtras hF 4 (by norm_num) ζ hζ)
      (CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ)
      (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
        (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hT
  refine ⟨le_top, isPGroup_unU hF, ?_⟩
  change ¬ 2 ∣ (unU hF 4).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop

@[expose] def unSystem (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)] :
    RankTwoSystem (SU (unitaryInvolution F 2 f) 4) 4 :=
  haveI := isSimpleGroup_unSU hF
  (unPre hF ζ).toSystemOfSimple

end System

end CFSG.Quasithin.H13.F431.Un
