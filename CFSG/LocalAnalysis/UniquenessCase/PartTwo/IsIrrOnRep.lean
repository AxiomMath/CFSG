module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Vol2.Ch10SecI1Dual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.ASInputs.C10KH CFSG.QuasithinUnique.Setup.SL2Modules

theorem isIrreducible_repOf_restrictAut {V : Type*} [CommGroup V] {Γ : Type*} [Group Γ]
    {L : Subgroup (MulAut V)} {J : Subgroup V} (hJ : IsIrrOn L J ⊥)
    (r : Γ →* MulAut V) (hJinv : ∀ g, ∀ w ∈ J, r g w ∈ J)
    (hsurj : ∀ l ∈ L, ∃ g : Γ, r g = l)
    [Module (ZMod 2) (Additive ↥J)] :
    (repOf (restrictAut r J hJinv)).IsIrreducible := by
  classical
  rw [isIrreducible_iff]
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, hvJ, hv⟩ := SetLike.exists_of_lt hJ.1
    refine ⟨0, Additive.ofMul ⟨v, hvJ⟩, fun h => hv ?_⟩
    have h1 : (⟨v, hvJ⟩ : ↥J) = 1 := Additive.ofMul.injective (by simpa using h.symm)
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val h1)
  · let U' : Subgroup ↥J := AddSubgroup.toSubgroup' U.toAddSubgroup
    let Ksub : Subgroup V := U'.map (Subgroup.subtype J)
    have hKstable : StableUnder L Ksub := by
      intro l hl k hk
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
      obtain ⟨g, hg⟩ := hsurj l hl
      have hmemU : (⟨l x, hJ.2.1 l hl x x.2⟩ : ↥J) ∈ U' := by
        change Additive.ofMul ⟨l x, hJ.2.1 l hl x x.2⟩ ∈ U
        have h := hU g (Additive.ofMul x) hx
        rw [repOf_apply] at h
        have hsub : ((restrictAut r J hJinv) g x : ↥J) = ⟨r g x, hJinv g x x.2⟩ :=
          Subtype.ext (restrictAut_apply r J hJinv g x)
        have h' : Additive.ofMul (⟨r g x, hJinv g x x.2⟩ : ↥J) ∈ U := by
          simpa [hsub] using h
        simpa [hg] using h'
      exact Subgroup.mem_map_of_mem (Subgroup.subtype J) hmemU
    have hKle : Ksub ≤ J := Subgroup.map_subtype_le U'
    rcases hJ.2.2.2 Ksub hKstable bot_le hKle with hbot | htop
    · left
      rw [eq_bot_iff]
      intro w hw
      have hw' : Additive.toMul w ∈ U' := hw
      have hmemK : ((Additive.toMul w : ↥J) : V) ∈ Ksub :=
        Subgroup.mem_map_of_mem (Subgroup.subtype J) hw'
      rw [hbot, Subgroup.mem_bot] at hmemK
      rw [Submodule.mem_bot]
      have h2 : Additive.toMul w = 1 := Subtype.ext (by simpa using hmemK)
      change Additive.ofMul (Additive.toMul w) = 0
      rw [h2]
      rfl
    · right
      rw [eq_top_iff]
      intro w _
      have hmemK : ((Additive.toMul w : ↥J) : V) ∈ Ksub := by
        rw [htop]
        exact (Additive.toMul w).2
      obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hmemK
      have hxw : x = Additive.toMul w := Subtype.ext hxval
      rw [hxw] at hx
      change Additive.ofMul (Additive.toMul w) ∈ U
      exact hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
