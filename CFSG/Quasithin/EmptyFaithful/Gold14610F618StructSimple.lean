module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructIso
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace Struct

variable {D : Type} [Group D]

theorem idx2Data_of_isL2_one {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13) (h : F6.IsL2 p 1 D) : Idx2Data D :=
  idx2Data_of_simple (CFSG.LieType.Simplicity.fam_PSL_simplicity D 2 p 1 h).2
    (Or.inl ⟨p, hp, hp24, h⟩)

theorem idx2Data_of_isL2 {p e : ℕ} (hp : p.Prime) (he1 : 1 ≤ e)
    (he2 : e ≤ 2) (h16 : p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) (h : F6.IsL2 p e D) : Idx2Data D :=
  idx2Data_of_simple (CFSG.LieType.Simplicity.fam_PSL_simplicity D 2 p e h).2
    (Or.inr (Or.inl ⟨p, e, hp, he1, he2, h16, h⟩))

theorem isQuasisimple_of_isHatAlt {n : ℕ} (h : F6.IsHatAlt n D) : CFSG.IsQuasisimple D :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff D).2.2.1.mpr h.1

theorem idx2Data_of_isHatAlt_six (h : F6.IsHatAlt 6 D) : Idx2Data D :=
  idx2Data_of_quasisimple (isQuasisimple_of_isHatAlt h) (Or.inr (Or.inr (Or.inl h)))

theorem idx2Data_of_isHatAlt_seven (h : F6.IsHatAlt 7 D) : Idx2Data D :=
  idx2Data_of_quasisimple (isQuasisimple_of_isHatAlt h)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem idx2Data_of_alt_seven (h : Nonempty (D ≃* ↥(alternatingGroup (Fin 7)))) :
    Idx2Data D := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact idx2Data_of_simple e.isSimpleGroup (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))

theorem idx2Data_of_isM12 (h : F6.IsM12 D) : Idx2Data D := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  exact idx2Data_of_simple e.isSimpleGroup
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))))

end Struct

end Gold14610

end CFSG.Quasithin
