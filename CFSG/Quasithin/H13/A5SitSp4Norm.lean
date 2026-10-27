module

public import CFSG.Quasithin.H13.A5SitSp4

public section

namespace CFSG.Quasithin.H13.A5.Orth

theorem normPC1_0000 : NormPC1 ![0, 0, 0, 0] := by
  decide +kernel

theorem normPC1_0001 : NormPC1 ![0, 0, 0, 1] := by
  decide +kernel

theorem normPC1_0010 : NormPC1 ![0, 0, 1, 0] := by
  decide +kernel

theorem normPC1_0011 : NormPC1 ![0, 0, 1, 1] := by
  decide +kernel

theorem normPC1_0100 : NormPC1 ![0, 1, 0, 0] := by
  decide +kernel

theorem normPC1_0101 : NormPC1 ![0, 1, 0, 1] := by
  decide +kernel

theorem normPC1_0110 : NormPC1 ![0, 1, 1, 0] := by
  decide +kernel

theorem normPC1_0111 : NormPC1 ![0, 1, 1, 1] := by
  decide +kernel

theorem normPC1_1000 : NormPC1 ![1, 0, 0, 0] := by
  decide +kernel

theorem normPC1_1001 : NormPC1 ![1, 0, 0, 1] := by
  decide +kernel

theorem normPC1_1010 : NormPC1 ![1, 0, 1, 0] := by
  decide +kernel

theorem normPC1_1011 : NormPC1 ![1, 0, 1, 1] := by
  decide +kernel

theorem normPC1_1100 : NormPC1 ![1, 1, 0, 0] := by
  decide +kernel

theorem normPC1_1101 : NormPC1 ![1, 1, 0, 1] := by
  decide +kernel

theorem normPC1_1110 : NormPC1 ![1, 1, 1, 0] := by
  decide +kernel

theorem normPC1_1111 : NormPC1 ![1, 1, 1, 1] := by
  decide +kernel

theorem V4_cases : ∀ c0 : V4,
      c0 = ![0, 0, 0, 0] ∨
      c0 = ![0, 0, 0, 1] ∨
      c0 = ![0, 0, 1, 0] ∨
      c0 = ![0, 0, 1, 1] ∨
      c0 = ![0, 1, 0, 0] ∨
      c0 = ![0, 1, 0, 1] ∨
      c0 = ![0, 1, 1, 0] ∨
      c0 = ![0, 1, 1, 1] ∨
      c0 = ![1, 0, 0, 0] ∨
      c0 = ![1, 0, 0, 1] ∨
      c0 = ![1, 0, 1, 0] ∨
      c0 = ![1, 0, 1, 1] ∨
      c0 = ![1, 1, 0, 0] ∨
      c0 = ![1, 1, 0, 1] ∨
      c0 = ![1, 1, 1, 0] ∨
      c0 = ![1, 1, 1, 1] := by
  decide +kernel

theorem normPC1_all : ∀ c0 : V4, NormPC1 c0 := by
  intro c0
  rcases V4_cases c0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  exacts [normPC1_0000, normPC1_0001, normPC1_0010, normPC1_0011, normPC1_0100, normPC1_0101,
    normPC1_0110, normPC1_0111, normPC1_1000, normPC1_1001, normPC1_1010, normPC1_1011,
    normPC1_1100, normPC1_1101, normPC1_1110, normPC1_1111]

theorem mem_Oq_of_conj {g : MulAut (Multiplicative V4)} (hg : g ∈ Spq)
    (h1 : g * ofOC r1 * g⁻¹ ∈ Oq) (h2 : g * ofOC r2 * g⁻¹ ∈ Oq) : g ∈ Oq :=
  mem_Oq_of_conj_of normPC1_all hg h1 h2

end CFSG.Quasithin.H13.A5.Orth
