module

public import CFSG.Permutation.FiveTransitive.Degree20SmallSupport

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

@[expose] abbrev FiveCycle := Multiplicative (ZMod 5)

@[expose] abbrev FourFiveBase := Fin 4 → FiveCycle

@[expose] abbrev TwentyFivePoints := Fin 4 × FiveCycle

instance : SMul FourFiveBase TwentyFivePoints where
  smul a x := ⟨x.1, a x.1 * x.2⟩

instance : MulAction FourFiveBase TwentyFivePoints where
  one_smul x := by
    ext
    · rfl
    · change (1 : FiveCycle) * x.2 = x.2
      exact one_mul x.2
  mul_smul a b x := by
    ext
    · rfl
    · change (a x.1 * b x.1) * x.2 =
        a x.1 * (b x.1 * x.2)
      exact mul_assoc _ _ _

instance : FaithfulSMul FourFiveBase TwentyFivePoints where
  eq_of_smul_eq_smul {a b} h := by
    funext i
    have hi := congrArg Prod.snd
      (h (i, (1 : FiveCycle)))
    change a i * 1 = b i * 1 at hi
    simpa using hi

@[expose] def coordinateFive : FourFiveBase :=
  fun i => if i = 0 then Multiplicative.ofAdd (1 : ZMod 5) else 1

theorem card_fiveCycle : Nat.card FiveCycle = 5 := by
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card 5

theorem card_fourFiveBase : Nat.card FourFiveBase = 625 := by
  rw [Nat.card_fun, Nat.card_fin, card_fiveCycle]
  norm_num

theorem card_twentyFivePoints :
    Fintype.card TwentyFivePoints = 20 := by
  rw [Fintype.card_prod, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, card_fiveCycle]

private theorem coordinateFive_support_card :
    ((MulAction.toPermHom FourFiveBase TwentyFivePoints)
      coordinateFive).support.card = 5 := by
  decide

theorem card_support_permCongr
    {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (w : Equiv.Perm A) :
    (e.permCongr w).support.card = w.support.card := by
  have hsupport :
      (e.permCongr w).support =
        w.support.map e.toEmbedding := by
    ext a
    simp [Equiv.Perm.mem_support]
    constructor
    · intro h hw
      apply h
      rw [hw, e.apply_symm_apply]
    · intro h heq
      apply h
      apply e.injective
      simpa using heq
  rw [hsupport, Finset.card_map]

theorem alternatingGroup_le_of_sylow_five_card_eq_six_hundred_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 5 P) (hScard : Nat.card S = 625) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp (S : Subgroup P).subtype
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) := inclusion.range
  have hRcard : Nat.card R = 625 := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr
          (MonoidHom.ofInjective hinclusion).toEquiv.symm
      _ = 625 := hScard
  have hRcardSylow :
      Nat.card R =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [hRcard, Nat.card_perm,
      Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_factorial
      (by norm_num : Nat.Prime 5)
      (show Nat.log 5 20 < 3 by norm_num)]
    rw [Finset.sum_Ico_succ_top
      (by norm_num : 1 ≤ 2)]
    norm_num
  let Q : Sylow 5 (Equiv.Perm X) :=
    Sylow.ofCard R hRcardSylow
  let e : X ≃ TwentyFivePoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_twentyFivePoints.symm)
  let standardMap :
      FourFiveBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom FourFiveBase TwentyFivePoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let R₀ : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hR₀card : Nat.card R₀ = 625 := by
    calc
      Nat.card R₀ = Nat.card FourFiveBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 625 := card_fourFiveBase
  have hR₀cardSylow :
      Nat.card R₀ =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [hR₀card, Nat.card_perm,
      Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_factorial
      (by norm_num : Nat.Prime 5)
      (show Nat.log 5 20 < 3 by norm_num)]
    rw [Finset.sum_Ico_succ_top
      (by norm_num : 1 ≤ 2)]
    norm_num
  let Q₀ : Sylow 5 (Equiv.Perm X) :=
    Sylow.ofCard R₀ hR₀cardSylow
  let w₀ : Equiv.Perm X :=
    standardMap coordinateFive
  have hw₀Q : w₀ ∈ (Q₀ : Subgroup (Equiv.Perm X)) := by
    change w₀ ∈ R₀
    exact ⟨coordinateFive, rfl⟩
  have hw₀support : w₀.support.card = 5 := by
    change
      (e.symm.permCongr
        ((MulAction.toPermHom FourFiveBase TwentyFivePoints)
          coordinateFive)).support.card = 5
    rw [card_support_permCongr,
      coordinateFive_support_card]
  obtain ⟨q, hq⟩ :=
    exists_smul_eq (Equiv.Perm X) Q Q₀
  have hqInv : q⁻¹ • Q₀ = Q :=
    inv_smul_eq_iff.mpr hq.symm
  let w : Equiv.Perm X :=
    MulAut.conj q⁻¹ w₀
  have hwConjugate :
      w ∈ (q⁻¹ • Q₀ :
        Sylow 5 (Equiv.Perm X)) := by
    change ∃ x ∈
      (Q₀ : Subgroup (Equiv.Perm X)),
        MulAut.conj q⁻¹ x = w
    exact ⟨w₀, hw₀Q, rfl⟩
  have hwQ : w ∈ (Q : Subgroup (Equiv.Perm X)) := by
    rwa [hqInv] at hwConjugate
  have hwRange : w ∈ R := by
    exact hwQ
  obtain ⟨v, hv⟩ := hwRange
  have hwMem : w ∈ P := by
    rw [← hv]
    exact ((S : Subgroup P).subtype v).prop
  have hwSupport : w.support.card = 5 := by
    change
      (q⁻¹ * w₀ * (q⁻¹)⁻¹).support.card = 5
    rw [Equiv.Perm.card_support_conj,
      hw₀support]
  have hwNe : w ≠ 1 := by
    intro hw
    rw [hw, Equiv.Perm.support_one] at hwSupport
    norm_num at hwSupport
  exact alternatingGroup_le_of_nontrivial_support_le_seven
    X P hcard h5 hwMem hwNe (by omega)

end FiveTransitive.Degree20

end CFSG
