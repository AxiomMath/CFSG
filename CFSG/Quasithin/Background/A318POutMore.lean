module

public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.Sporadic.Schreier.PairHSOut
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace A318P

theorem not_dvd_outer_alternating_six {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 6)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer S) := by
  have := finite_outer S
  exact not_dvd_card_of_isPGroup_two
    (isPGroup_two_outer_of_mulEquiv e CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six) hp hp2

theorem not_dvd_outer_psl_binary {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 3 ≤ n)
    (hm : StatedClassicalModel S .PSL n 2 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer S) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  let e' : S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have := finite_outer S
  exact not_dvd_card_of_isPGroup_two (isPGroup_two_outer_of_mulEquiv e'
    (CFSG.LieType.SteinbergBR.BinaryLinear.binary_linear_key hn hK2).2) hp hp2

theorem not_dvd_outer_HS
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .HS)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) :=
  not_dvd_outer_of_carrier e CFSG.Sporadic.Schreier.HS_outer_card_le_two.1 hp hp2

theorem card_outer_eq_of_mulEquiv' {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') :
    Nat.card (Outer T) = Nat.card (Outer T') :=
  Nat.card_congr (equivalence e).toEquiv

theorem not_dvd_outer_Ru
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .Ru)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer S) := by
  refine not_dvd_outer_of_carrier e ?_ hp hp2
  rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
      Nat.card (Outer CFSG.Sporadic.RuSchreier.ruP) from
    card_outer_eq_of_mulEquiv' CFSG.Sporadic.RuSchreier.ruEquivP,
    CFSG.Sporadic.RuSchreier.card_outer_ruP]
  norm_num

end A318P

end CFSG.Quasithin
