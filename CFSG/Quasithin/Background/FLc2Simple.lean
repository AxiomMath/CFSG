module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem isSimpleGroup_SLt {n : ℕ} (hn : 3 ≤ n) : IsSimpleGroup (SLt n) := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hmodel : CFSG.Quasithin.IsPSL n 2 1 (SLt n) := by
    refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
    · intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
    · intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
    · exact ⟨(slEquivGLt n).trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK n).symm⟩
  exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ n 2 1 hmodel).2

theorem injective_of_ne_one {X Y : Type*} [Group X] [Group Y] [IsSimpleGroup X] (f : X →* Y)
    (h : ∃ x, f x ≠ 1) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, hx⟩ := h
    apply hx
    have : x ∈ f.ker := by rw [h1]; exact Subgroup.mem_top x
    exact this

end CFSG.Quasithin.FLc
