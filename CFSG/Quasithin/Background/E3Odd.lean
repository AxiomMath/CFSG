module

public import CFSG.Quasithin.Background.E3Basic
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.Quasithin.Background.E1Sec7

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section OddCore

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem oddCoreIn_le (X : Subgroup M) : oddCoreIn X ≤ X := Subgroup.map_subtype_le _

omit [Finite M] in
theorem le_normalizer_oddCoreIn (X : Subgroup M) :
    X ≤ Subgroup.normalizer (oddCoreIn X : Set M) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : (fusionOddCore X).Normal) k hk ⟨h, hh⟩, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : (fusionOddCore X).Normal) k hk ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

theorem odd_card_oddCoreIn' (X : Subgroup M) : Odd (Nat.card (oddCoreIn X)) := by
  rw [oddCoreIn, Nat.card_congr ((fusionOddCore X).equivMapOfInjective X.subtype
    X.subtype_injective).toEquiv.symm]
  exact CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
    (fun _ hmem => hmem.1) (fun _ hmem => hmem.2)

end OddCore

section Hyperplane

variable {M : Type*} [Group M] [Finite M]

theorem le_iSup_hyperplane_inf_centralizer {O A : Subgroup M} (hO : Odd (Nat.card O))
    (hAab : IsElemAbelian 2 A) (hA0 : A ≠ ⊥) (hAO : A ≤ Subgroup.normalizer (O : Set M)) :
    O ≤ ⨆ S ∈ {S : Subgroup M | S ≤ A ∧ Nat.card A = 2 * Nat.card S},
      O ⊓ Subgroup.centralizer (S : Set M) := by
  let : MulDistribMulAction ↥A ↥O := Subgroup.conjMulDistribMulActionOfLeNormalizer A O hAO
  have : CFSG.IsElementaryAbelian 2 ↥A :=
    { toIsMulCommutative := hAab.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hAab.2 x x.2) }
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA0
  have hodd : ¬ 2 ∣ Nat.card ↥O := fun h => (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 h)
  have h := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := ↥A) (H := ↥O) hodd
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥O) ∈ ⨆ (B : Subgroup ↥A) (_ : B.index = 2),
      CFSG.fixedPointSubgroup B ↥O := by
    rw [h]
    exact Subgroup.mem_top _
  have hle : (⨆ (B : Subgroup ↥A) (_ : B.index = 2), CFSG.fixedPointSubgroup B ↥O) ≤
      (⨆ S ∈ {S : Subgroup M | S ≤ A ∧ Nat.card A = 2 * Nat.card S},
        O ⊓ Subgroup.centralizer (S : Set M)).comap O.subtype := by
    refine iSup₂_le fun B hB y hy => ?_
    have hBF : B.map A.subtype ∈ {S : Subgroup M | S ≤ A ∧ Nat.card A = 2 * Nat.card S} := by
      refine ⟨Subgroup.map_subtype_le B, ?_⟩
      rw [Subgroup.card_map_of_injective A.subtype_injective]
      have := B.card_mul_index
      rw [hB] at this
      omega
    have hmem : (y : M) ∈ O ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup M) : Set M) := by
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h1 : (b : M) * (y : M) * (b : M)⁻¹ = (y : M) :=
        congrArg Subtype.val (hy ⟨b, hb⟩)
      show (b : M) * (y : M) = (y : M) * (b : M)
      calc (b : M) * (y : M) = ((b : M) * (y : M) * (b : M)⁻¹) * (b : M) := by group
        _ = (y : M) * (b : M) := by rw [h1]
    exact (le_iSup₂_of_le (f := fun S (_ : S ∈ {S : Subgroup M | S ≤ A ∧
      Nat.card A = 2 * Nat.card S}) => O ⊓ Subgroup.centralizer (S : Set M))
      (B.map A.subtype) hBF le_rfl) hmem
  exact hle hx'

end Hyperplane

section E340

private theorem le_centralizer_iff_comm' {M : Type*} [Group M] {X Y : Subgroup M} :
    X ≤ Subgroup.centralizer (Y : Set M) ↔ Y ≤ Subgroup.centralizer (X : Set M) := by
  constructor <;> intro h a ha <;>
    exact Subgroup.mem_centralizer_iff.2 fun b hb =>
      (Subgroup.mem_centralizer_iff.1 (h hb) a ha).symm

private theorem eq_bot_of_isPGroup_of_odd {M : Type*} [Group M] [Finite M] {Z P : Subgroup M}
    (hP : IsPGroup 2 P) (hPZ : P ≤ Z) (hZ : Odd (Nat.card Z)) : P = ⊥ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hdvd : Nat.card P ∣ Nat.card Z := Subgroup.card_dvd_of_le hPZ
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

variable {W : Type*} [CommGroup W] [Finite W]

theorem e3_40 (hW : ∀ w : W, w ^ 2 = 1) {X A : Subgroup (MulAut W)} (hA : A ∈ aSet 2 X) :
    A ≤ Subgroup.centralizer (oddCoreIn X : Set (MulAut W)) := by
  obtain ⟨hAX, hA1, hAab, hAfix⟩ := hA
  have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian2 hAab
  have hAab' : IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hAab.1 a a.2 b b.2)⟩⟩, fun a ha => hAab.2 a ha⟩
  have hOX : oddCoreIn X ≤ X := oddCoreIn_le X
  have hOodd : Odd (Nat.card (oddCoreIn X)) := odd_card_oddCoreIn' X
  have hAO : A ≤ Subgroup.normalizer (oddCoreIn X : Set (MulAut W)) :=
    hAX.trans (le_normalizer_oddCoreIn X)
  have hgen := le_iSup_hyperplane_inf_centralizer hOodd hAab' hA1 hAO
  suffices key : ∀ S : Subgroup (MulAut W), S ≤ A → Nat.card A = 2 * Nat.card S →
      A ≤ Subgroup.centralizer ((oddCoreIn X ⊓ Subgroup.centralizer (S : Set (MulAut W)) :
        Subgroup (MulAut W)) : Set (MulAut W)) by
    have hZ : (⨆ S ∈ {S : Subgroup (MulAut W) | S ≤ A ∧ Nat.card A = 2 * Nat.card S},
        oddCoreIn X ⊓ Subgroup.centralizer (S : Set (MulAut W))) ≤
        Subgroup.centralizer (A : Set (MulAut W)) :=
      iSup₂_le fun S hS => le_centralizer_iff_comm'.1 (key S hS.1 hS.2)
    exact le_centralizer_iff_comm'.2 (hgen.trans hZ)
  intro S hSA hcard
  by_contra hnot
  have hSX : S ≤ X := hSA.trans hAX
  have hmS : mQuot A S < 2 := by
    have h := card_eq_two_pow_mul hA2 hSA
    rw [hcard] at h
    have hpos : 0 < Nat.card S := Nat.card_pos
    have h2 : 2 = 2 ^ mQuot A S := Nat.eq_of_mul_eq_mul_right hpos h
    have h1 : mQuot A S = 1 :=
      Nat.pow_right_injective (le_refl 2) (h2.symm.trans (pow_one 2).symm)
    omega
  have hfixS : fixV S = fixV A := hAfix S hSA hmS
  set C : Subgroup (MulAut W) := oddCoreIn X ⊓ Subgroup.centralizer (S : Set (MulAut W)) with hC
  have hCO : C ≤ oddCoreIn X := inf_le_left
  have hCS : C ≤ Subgroup.centralizer (S : Set (MulAut W)) := inf_le_right
  have hAS : A ≤ Subgroup.centralizer (S : Set (MulAut W)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun s hs => hAab.1 s (hSA hs) a ha
  set Y : Subgroup (MulAut W) := ⁅C, A⁆ with hY
  have hYO : Y ≤ oddCoreIn X :=
    (Subgroup.commutator_mono hCO le_rfl).trans (E1.commutator_le_of_le_normalizer hAO)
  have hYS : Y ≤ Subgroup.centralizer (S : Set (MulAut W)) :=
    Subgroup.commutator_le.2 fun c hc a ha => by
      have h1 := hCS hc
      have h2 := hAS ha
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
  let Stab : Subgroup (MulAut W) :=
    { carrier := {z | ∀ x ∈ fixV S, z x = x}
      one_mem' := fun x _ => by simp
      mul_mem' := fun {a b} ha hb x hx => by
        rw [MulAut.mul_apply, hb x hx, ha x hx]
      inv_mem' := fun {a} ha x hx => by
        have := ha x hx
        calc a⁻¹ x = a⁻¹ (a x) := by rw [this]
          _ = x := MulAut.inv_apply_self W a x }
  have hYStab : Y ≤ Stab := by
    refine Subgroup.commutator_le.2 fun c hc a ha x hx => ?_
    have hxA : x ∈ fixV A := hfixS ▸ hx
    have h1 : a⁻¹ x = x := hxA a⁻¹ (A.inv_mem ha)
    have hcx : c⁻¹ x ∈ fixV S := by
      intro s hs
      have hcomm : Commute s c := Subgroup.mem_centralizer_iff.1 (hCS hc) s hs
      have h3 : s * c⁻¹ = c⁻¹ * s := hcomm.inv_right.eq
      calc s (c⁻¹ x) = (s * c⁻¹) x := rfl
        _ = (c⁻¹ * s) x := by rw [h3]
        _ = c⁻¹ (s x) := rfl
        _ = c⁻¹ x := by rw [hx s hs]
    have h2 : a (c⁻¹ x) = c⁻¹ x := (hfixS ▸ hcx : c⁻¹ x ∈ fixV A) a ha
    calc (⁅c, a⁆ : MulAut W) x = c (a (c⁻¹ (a⁻¹ x))) := rfl
      _ = c (a (c⁻¹ x)) := by rw [h1]
      _ = c (c⁻¹ x) := by rw [h2]
      _ = x := MulAut.apply_inv_self W c x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW
  have hYX : Y ≤ X := hYO.trans hOX
  have hY'odd : Odd (Nat.card (Y.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv]
    exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hYO)
  have hOp : pCoreOf 2 (Y.subgroupOf X) = ⊥ :=
    eq_bot_of_isPGroup_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hY'odd
  have hcomm : ∀ a ∈ Y.subgroupOf X, ∀ b ∈ S.subgroupOf X,
      X.subtype a * X.subtype b = X.subtype b * X.subtype a := by
    intro a ha b hb
    have ha' : (a : MulAut W) ∈ Y := ha
    have hb' : (b : MulAut W) ∈ S := hb
    exact (Subgroup.mem_centralizer_iff.1 (hYS ha') (b : MulAut W) hb').symm
  have hB : IsPGroup 2 ((S.subgroupOf X).map X.subtype) := by
    rw [Subgroup.map_subgroupOf_eq_of_le hSX]
    exact hA2.to_le hSA
  have hfaith : ∀ a ∈ Y.subgroupOf X, X.subtype a = 1 → a = 1 := fun a _ h => Subtype.ext h
  have hAxB := thompson_AxB_two (p := 2) hW2 X.subtype (A := Y.subgroupOf X)
    (B := S.subgroupOf X) hcomm hB hfaith hOp
  have hY1 : Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X := hy
    have h := hAxB ⟨y, hYX hy⟩ hy' (fun x hx => by
      have hxfix : x ∈ fixV S := fun s hs => hx ⟨s, hSX hs⟩ hs
      exact hYStab hy x hxfix)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h)
  exact hnot (le_centralizer_iff_comm'.2 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hY1))

end E340

end E3

end CFSG.Quasithin
