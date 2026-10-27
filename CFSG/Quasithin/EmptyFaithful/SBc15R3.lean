module

public import CFSG.Quasithin.EmptyFaithful.SBc15R3G

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc15

theorem input14616ParabolicThreeA_of_weakW
    (h : WeakW (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5))) : Input14616ParabolicThreeA := by
  intro G _ _ T M S H PQ p hred hp hC H₀ H₁ H₂ t hdec
  obtain ⟨-, K₁, s, hK₁, -, -, hK, ⟨e⟩⟩ := hC
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have := GoldS146P.perm5_quot_solvable
  exact R3.parabolicWeak_of_wreath S hred hp hdec (alternatingGroup (Fin 5)) (by decide) h hK₁ hK
    e

theorem input14616ParabolicThreeB_of_weakW
    (h : WeakW (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ⊤) : Input14616ParabolicThreeB := by
  intro G _ _ T M S H PQ p hred hp hC H₀ H₁ H₂ t hdec
  obtain ⟨-, K₁, s, hK₁, -, -, hK, ⟨e⟩⟩ := hC
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    GoldS146P.sl_simple 3 le_rfl
  have : IsSimpleGroup ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :=
    Subgroup.topEquiv.isSimpleGroup
  have : Subsingleton (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ⧸
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) :=
    QuotientGroup.subsingleton_quotient_top
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ⧸
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) := inferInstance
  have hnc : ∃ a b : ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := GoldS146P.sl_nonabelian 3 le_rfl
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun hh => hab (congrArg Subtype.val hh)⟩
  exact R3.parabolicWeak_of_wreath S hred hp hdec ⊤ hnc h hK₁ hK e

end SBc15

end CFSG.Quasithin
