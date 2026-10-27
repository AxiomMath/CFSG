module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN2

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ] {B : Subgroup Δ} {s t x : Δ}

theorem InCells.d1 (h : InCell B 1 x) : InCells B s t x := Or.inl h
theorem InCells.d2 (h : InCell B s x) : InCells B s t x := Or.inr (Or.inl h)
theorem InCells.d3 (h : InCell B t x) : InCells B s t x := Or.inr (Or.inr (Or.inl h))
theorem InCells.d4 (h : InCell B (s * t) x) : InCells B s t x :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem InCells.d5 (h : InCell B (t * s) x) : InCells B s t x :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem InCells.d6 (h : InCell B (s * t * s) x) : InCells B s t x :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem InCells.d7 (h : InCell B (t * s * t) x) : InCells B s t x :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem InCells.d8 (h : InCell B (s * t * s * t) x) : InCells B s t x :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

namespace BNPair

variable {P₁ P₂ : Subgroup Δ} {us ut : List Δ}

theorem mul_s (H : BNPair B P₁ P₂ s t us ut) (hx : InCells B s t x) : InCells B s t (s * x) := by
  have hr := H.r1
  have e1 : (1 : Δ) = 1 ∨ (1 : Δ) = t ∨ (1 : Δ) = t * s ∨ (1 : Δ) = t * s * t := Or.inl rfl
  have e2 : t = 1 ∨ t = t ∨ t = t * s ∨ t = t * s * t := Or.inr (Or.inl rfl)
  have e3 : t * s = 1 ∨ t * s = t ∨ t * s = t * s ∨ t * s = t * s * t :=
    Or.inr (Or.inr (Or.inl rfl))
  have e4 : t * s * t = 1 ∨ t * s * t = t ∨ t * s * t = t * s ∨ t * s * t = t * s * t :=
    Or.inr (Or.inr (Or.inr rfl))
  rcases hx with h | h | h | h | h | h | h | h
  · exact InCells.d2 ((hr.up (H.up_us e1) h).congr (mul_one s))
  · rcases hr.down (n' := 1) (H.up_us e1) (h.congr (mul_one s).symm) with h2 | h2
    · exact InCells.d1 h2
    · exact InCells.d2 (h2.congr (mul_one s))
  · exact InCells.d4 (hr.up (H.up_us e2) h)
  · rcases hr.down (n' := t) (H.up_us e2) h with h2 | h2
    · exact InCells.d3 h2
    · exact InCells.d4 h2
  · exact InCells.d6 ((hr.up (H.up_us e3) h).congr (mul_assoc s t s).symm)
  · rcases hr.down (n' := t * s) (H.up_us e3) (h.congr (mul_assoc s t s)) with h2 | h2
    · exact InCells.d5 h2
    · exact InCells.d6 (h2.congr (mul_assoc s t s).symm)
  · exact InCells.d8 ((hr.up (H.up_us e4) h).congr (by group))
  · rcases hr.down (n' := t * s * t) (H.up_us e4) (h.congr (by group)) with h2 | h2
    · exact InCells.d7 h2
    · exact InCells.d8 (h2.congr (by group))

theorem mul_t (H : BNPair B P₁ P₂ s t us ut) (hx : InCells B s t x) : InCells B s t (t * x) := by
  have hr := H.r2
  have hb : t * (s * t * s) = s * t * s * t := by
    calc t * (s * t * s) = t * s * t * s := by group
      _ = s * t * s * t := H.braid.symm
  have f1 : (1 : Δ) = 1 ∨ (1 : Δ) = s ∨ (1 : Δ) = s * t ∨ (1 : Δ) = s * t * s := Or.inl rfl
  have f2 : s = 1 ∨ s = s ∨ s = s * t ∨ s = s * t * s := Or.inr (Or.inl rfl)
  have f3 : s * t = 1 ∨ s * t = s ∨ s * t = s * t ∨ s * t = s * t * s :=
    Or.inr (Or.inr (Or.inl rfl))
  have f4 : s * t * s = 1 ∨ s * t * s = s ∨ s * t * s = s * t ∨ s * t * s = s * t * s :=
    Or.inr (Or.inr (Or.inr rfl))
  rcases hx with h | h | h | h | h | h | h | h
  · exact InCells.d3 ((hr.up (H.up_ut f1) h).congr (mul_one t))
  · exact InCells.d5 (hr.up (H.up_ut f2) h)
  · rcases hr.down (n' := 1) (H.up_ut f1) (h.congr (mul_one t).symm) with h2 | h2
    · exact InCells.d1 h2
    · exact InCells.d3 (h2.congr (mul_one t))
  · exact InCells.d7 ((hr.up (H.up_ut f3) h).congr (by group))
  · rcases hr.down (n' := s) (H.up_ut f2) h with h2 | h2
    · exact InCells.d2 h2
    · exact InCells.d5 h2
  · exact InCells.d8 ((hr.up (H.up_ut f4) h).congr hb)
  · rcases hr.down (n' := s * t) (H.up_ut f3) (h.congr (by group)) with h2 | h2
    · exact InCells.d4 h2
    · exact InCells.d7 (h2.congr (by group))
  · rcases hr.down (n' := s * t * s) (H.up_ut f4) (h.congr hb.symm) with h2 | h2
    · exact InCells.d6 h2
    · exact InCells.d8 (h2.congr hb)

end BNPair

end CFSG.Quasithin.H13.F431.U42Aut
