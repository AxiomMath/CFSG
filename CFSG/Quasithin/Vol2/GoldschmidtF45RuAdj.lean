module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
public import Certificates.Data.RuF45Geom

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem onLineP_iff {pts : Array ℕ} {p v : ℕ} :
    onLineP pts p v = true ↔ ∃ k < 3, pts[3 * v + k]! = p := by
  simp only [onLineP, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
  · rintro ⟨k, hk, h⟩
    interval_cases k
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem mem_titsLine_iff (p : Fin 1755) (v : Fin 2925) :
    p ∈ titsLine v ↔ ∃ k < 3, titsLinePtArr[3 * (v : ℕ) + k]! = (p : ℕ) :=
  (RuType.J47.titsLine_mem_iff p v).trans onLineP_iff

end CFSG.Quasithin.H13.F45Ru
