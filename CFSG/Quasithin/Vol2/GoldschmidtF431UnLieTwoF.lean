module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem isPGroup_A1X : IsPGroup 2 (A1X h) :=
  IsPGroup.of_card (n := 4 * f) (by rw [card_A1X, ← pow_mul, mul_comm])

@[expose] def bX : Xg h :=
  ⟨miyamotoXGL h 0 1 0 0, miyamotoUnipotent_le_SU h true false
    ((miyamotoXGL_mem_A1 h).2 ⟨rfl, map_one _, map_zero _⟩)⟩

theorem coe_bX : ((bX h : Xg h) : GL (Fin 4) K) = miyamotoXGL h 0 1 0 0 := rfl

theorem bX_mem_A1X : bX h ∈ A1X h :=
  (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_one _, map_zero _⟩

theorem pCoreOf_Ln : pCoreOf 2 (Ln h) = A1X h := by
  have := finite_Xg h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun x hx => ?_)
    (le_pCoreOf_of_le_normalizer 2 (A1X_le_Ln h) le_rfl (isPGroup_A1X h))
  have hSyl : IsSylowTwoOf (Psy h) (Ln h) :=
    F7.isSylowTwoOf_mono_right (isSylowTwoOf_Psy h) (Psy_le_Ln h) le_top
  have hxP : x ∈ Psy h := pCoreOf_le_of_isSylowTwoOf hSyl hx
  have hr : r1X h * x * (r1X h)⁻¹ ∈ pCoreOf 2 (Ln h) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ (r1X_mem_Ln h)) x).1 hx
  have hyP : r1X h * x * (r1X h)⁻¹ ∈ Psy h := pCoreOf_le_of_isSylowTwoOf hSyl hr
  obtain ⟨a, b, c, d, hb, hd, hxe⟩ := (mem_P h).1 (show (x : GL (Fin 4) K) ∈ miyamotoP h from hxP)
  obtain ⟨a', b', c', d', hb', hd', hye⟩ := (mem_P h).1
    (show ((r1X h * x * (r1X h)⁻¹ : Xg h) : GL (Fin 4) K) ∈ miyamotoP h from hyP)
  have e1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 1) hye
  have ha : a = 0 := by
    have hc : ((r1X h * x * (r1X h)⁻¹ : Xg h) : GL (Fin 4) K) =
        miyamotoR1 K * (x : GL (Fin 4) K) * (miyamotoR1 K)⁻¹ := rfl
    rw [hc, hxe] at e1
    simpa [miyamotoR1, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] using e1
  have hxP' : miyamotoXGL h a b c d ∈ miyamotoP h := by
    rw [← hxe]
    exact hxP
  have hxA : miyamotoXGL h a b c d ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1_iff_of_mem_P h hxP').2 ha
  show (x : GL (Fin 4) K) ∈ miyamotoA1 h
  rw [hxe]
  exact hxA

end CFSG.Quasithin.H13.F431.Un.OL
