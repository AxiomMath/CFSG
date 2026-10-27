module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Fld
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdAmb
public import CFSG.Quasithin.SteinbergBSQTEOddUnitaryThree
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Datum
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem exists_involution_of_isInnerAut {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) {w : MulAut S} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hin : CFSG.QuasithinUnique.Ch1.IsInnerAut w) :
    ∃ t : S, orderOf t = 2 ∧ SBd18.fixedSub w ≤ Subgroup.centralizer ({t} : Set S) := by
  obtain ⟨l, hl⟩ := hin
  have hll : l * l = 1 := by
    have hmem : l * l ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun f : MulAut S => f g) hw2
      simp only [MulAut.mul_apply, MulAut.one_apply, hl] at h1
      calc g * (l * l) = (l * l) * (l⁻¹ * (l⁻¹ * g * l) * l) := by group
        _ = (l * l) * g := by rw [h1]
    rw [center_eq_bot_of_equiv (MulEquiv.refl S) hnab] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hl1 : l ≠ 1 := by
    rintro rfl
    exact hw1 (MulEquiv.ext fun x => by simp [hl])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨l, orderOf_eq_prime (by rw [sq]; exact hll) hl1, fun x hx => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hx' : l⁻¹ * x * l = x := (hl x).symm.trans (SBd18.mem_fixedSub.mp hx)
  calc x * l = l * (l⁻¹ * x * l) := by group
    _ = l * x := by rw [hx']

theorem false_of_perfect_card_168_centralizer_psu3 {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {F : Type} [Field F] (hF : Nat.card F = (p ^ 1) ^ 2)
    {X : Type} [Group X] (e : X ≃* StatedProj (StatedSU 3 (p ^ 1) F)) {t : X}
    (ht : orderOf t = 2) {K : Subgroup X} (hK : Group.IsPerfect K) (hcard : Nat.card K = 168)
    (hKt : K ≤ Subgroup.centralizer ({t} : Set X)) : False := by
  have hU : UnitaryFieldData p 1 F := ⟨hp, le_rfl, by rw [hF]; ring⟩
  let ι : X ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  obtain ⟨z, -, -, -, -, -, -, -, hL, -, ⟨eL⟩, -, -⟩ :=
    (CFSG.Quasithin.SteinbergBS.odd_unitary_three_involution_and_Sylow_structure hU (by omega)
      (by rw [pow_one]; exact hp5) (unitaryScalars hU 3) le_rfl).2 (ι t)
      (by rw [MulEquiv.orderOf_eq]; exact ht)
  have := hK
  have hK' : Group.IsPerfect (K.map ι.toMonoidHom) := Group.IsPerfect.map _
  have hKc : K.map ι.toMonoidHom ≤ Subgroup.centralizer ({ι t} : Set (unitaryPSU hU 3)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hKt hk)
    show ι k * ι t = ι t * ι k
    rw [← map_mul, ← map_mul, h1]
  have hKL := CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect hK' hKc
  rw [hL] at hKL
  exact false_of_perfect_card_168_in_sl2 hp hp5 (by rw [hU.card_fixedField, pow_one]) hKL eL hK'
    (by rw [Subgroup.card_map_of_injective ι.injective, hcard])

end CFSG.Quasithin.SBd19F
