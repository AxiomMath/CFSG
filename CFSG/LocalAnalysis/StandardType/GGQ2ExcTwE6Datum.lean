module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
import CFSG.LocalAnalysis.StandardType.GGL45NtExcW1

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.QTwoCav
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest CFSG.StandardType.ExcFrames

noncomputable section

@[expose] def zetaDiag {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ModGL Tag.E6 L where
  toFun x := rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x))
  map_one' := by
    change rootDiagUnit Tag.E6 (zetaVec ζ hζ 0) = 1
    have h_zero : zetaVec ζ hζ (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
      funext i
      rw [zetaVec_apply]
      simp only [Pi.zero_apply, ZMod.val_zero, pow_zero]
      rfl
    rw [h_zero, rootDiagUnit_one]
  map_mul' x y := by
    change rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) *
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y))
    rw [CFSG.StandardType.ExcFrames.zetaVec_add, rootDiagUnit_mul]

@[expose] def zetaTorus {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1)
    (U : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) : Subgroup (ModGL Tag.E6 L) :=
  (AddSubgroup.toSubgroup U).map (zetaDiag ζ hζ)

theorem mem_zetaTorus {L : Type} [Field L] {ζ : Lˣ} {hζ : ζ ^ 3 = 1}
    {U : AddSubgroup (Fin Tag.E6.rank → ZMod 3)} {t : ModGL Tag.E6 L} :
    t ∈ zetaTorus ζ hζ U ↔ ∃ x ∈ U, rootDiagUnit Tag.E6 (zetaVec ζ hζ x) = t := by
  constructor
  · intro h
    rw [zetaTorus, Subgroup.mem_map] at h
    obtain ⟨y, hy, h_eq⟩ := h
    refine ⟨Multiplicative.toAdd y, ?_, ?_⟩
    · rwa [Multiplicative.mem_toSubgroup] at hy
    · simpa [zetaDiag] using h_eq
  · rintro ⟨x, hx, h_eq⟩
    rw [zetaTorus, Subgroup.mem_map]
    refine ⟨Multiplicative.ofAdd x, ?_, ?_⟩
    · rwa [Multiplicative.mem_toSubgroup]
    · simpa [zetaDiag] using h_eq

theorem zetaDiag_injective {L : Type} [Field L] {ζ : Lˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3) :
    Function.Injective (zetaDiag ζ hζ) := by
  intro x y h
  have h2 := CFSG.HardMathSupport.C14W1.rootDiagUnit_injective'
    (show rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) from h)
  exact Multiplicative.toAdd.injective (zetaVec_injective hζo hζ h2)

def zetaTorusExp {L : Type} [Field L] {ζ : Lˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3)
    (U : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) : Additive ↥(zetaTorus ζ hζ U) ≃+ ↥U :=
  (MulEquiv.toAdditive ((AddSubgroup.toSubgroup U).equivMapOfInjective (zetaDiag ζ hζ)
    (zetaDiag_injective hζo)).symm).trans
    { toFun := fun z => ⟨Multiplicative.toAdd (Additive.toMul z).1,
        (Multiplicative.mem_toSubgroup U _).mp (Additive.toMul z).2⟩
      invFun := fun x => Additive.ofMul ⟨Multiplicative.ofAdd x.1,
        (Multiplicative.mem_toSubgroup U _).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

theorem rootDiagUnit_zetaTorusExp {L : Type} [Field L] {ζ : Lˣ} {hζ : ζ ^ 3 = 1}
    (hζo : orderOf ζ = 3) (U : AddSubgroup (Fin Tag.E6.rank → ZMod 3))
    (t : ↥(zetaTorus ζ hζ U)) :
    rootDiagUnit Tag.E6 (zetaVec ζ hζ (zetaTorusExp hζo U (Additive.ofMul t) : _)) = t := by
  have h := congrArg Subtype.val
    (((AddSubgroup.toSubgroup U).equivMapOfInjective (zetaDiag ζ hζ)
      (zetaDiag_injective hζo)).apply_symm_apply t)
  rw [Subgroup.coe_equivMapOfInjective_apply] at h
  exact h

theorem rootChar_zetaVec {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) (β : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaVec ζ hζ x) β = ζ ^ (∑ k, ((β k : ℤ) : ZMod 3) * x k).val := by
  rw [rootChar, ← CFSG.RankThree.CentralCover.zmodPowHom_apply ζ hζ, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zetaVec, zmodPowHom_zpow]

theorem zeta_pow_val_intCast {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (n : ℤ) :
    ζ ^ ((n : ZMod 3).val) = ζ ^ n := by
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' n hζ]

theorem nonempty_excCoordDatum_of_zetaTorus
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {U : AddSubgroup (Fin Tag.E6.rank → ZMod 3)} (hT : zetaTorus ζ hζ U ≤ fullThreeTorus S)
    {m : Fin 6} (γ : ExcRaw.Root m → Fin Tag.E6.rank → ℤ) (e : ↥U ≃+ ExcRaw.V m)
    (hγ : ∀ i, IsRoot Tag.E6 (γ i)) (hex : ∀ δ, IsRoot Tag.E6 δ → ∃ i, δ = γ i ∨ δ = -γ i)
    (heq : ∀ i j, (γ i = γ j ∨ γ i = -γ j) → i = j)
    (hpair : ∀ i j, ExcRaw.pairing m i j = corootPair (γ j) (γ i))
    (hroot : ∀ (x : ↥U) (i : ExcRaw.Root m),
      ∑ k, ((γ i k : ℤ) : ZMod 3) * (x : Fin Tag.E6.rank → ZMod 3) k = ExcRaw.root m i (e x))
    (hcor : ∀ i, ∃ h : (fun j => ((corootPair (γ i) (Pi.single j 1) : ℤ) : ZMod 3)) ∈ U,
      e ⟨_, h⟩ = ExcRaw.coroot m i) :
    Nonempty (ExcCoordDatum S (zetaTorus ζ hζ U) m) := by
  choose hmem hcoord using hcor
  have hvec : ∀ i, zetaVec ζ hζ (fun j => ((corootPair (γ i) (Pi.single j 1) : ℤ) : ZMod 3)) =
      fun j => ζ ^ corootPair (γ i) (Pi.single j 1) :=
    fun i => funext fun j => zeta_pow_val_intCast hζ _
  have hcmem : ∀ i, rootDiagUnit Tag.E6 (fun j => ζ ^ corootPair (γ i) (Pi.single j 1)) ∈
      zetaTorus ζ hζ U := fun i => mem_zetaTorus.mpr ⟨_, hmem i, by rw [hvec]⟩
  refine ⟨{
    γ := γ
    ζ := ζ
    coord := (zetaTorusExp hζo U).trans e
    le_fullThreeTorus := hT
    ζ_pow_three := hζ
    ζ_ne_one := ?_
    isRoot := hγ
    exists_eq := hex
    eq_of_eq := heq
    pairing_eq := hpair
    rootChar_eq := ?_
    coroot_mem := hcmem
    coord_coroot := ?_ }⟩
  · rintro rfl
    rw [orderOf_one] at hζo
    omega
  · intro t b ht i
    have hb : b = zetaVec ζ hζ (zetaTorusExp hζo U (Additive.ofMul t) : _) :=
      CFSG.HardMathSupport.C14W1.rootDiagUnit_injective'
        (ht.symm.trans (rootDiagUnit_zetaTorusExp hζo U t).symm)
    rw [hb, rootChar_zetaVec, hroot]
    rfl
  · intro i
    have hx : zetaTorusExp hζo U (Additive.ofMul ⟨_, hcmem i⟩) = ⟨_, hmem i⟩ := by
      refine Subtype.ext (zetaVec_injective hζo hζ
        (CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' ?_))
      rw [rootDiagUnit_zetaTorusExp, hvec]
    rw [AddEquiv.trans_apply, hx, hcoord]

theorem card_zetaTorus {L : Type} [Field L] {ζ : Lˣ} {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3)
    (U : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) : Nat.card (zetaTorus ζ hζ U) = Nat.card U :=
  Nat.card_congr (zetaTorusExp hζo U).toEquiv

@[expose] def twE6Gamma {m : Fin 6} (i : ExcRaw.Root m) : Fin Tag.E6.rank → ℤ :=
  fun k => (ExcRaw.tabF2.getD i.val []).getD k.val 0

private theorem twE6Gamma_facts {m : Fin 6} (hm : m = 2 ∨ m = 3) :
    (∀ i : ExcRaw.Root m, IsRoot Tag.E6 (twE6Gamma i)) ∧
      (∀ δ, IsRoot Tag.E6 δ → ∃ i : ExcRaw.Root m, δ = twE6Gamma i ∨ δ = -twE6Gamma i) ∧
      (∀ i j : ExcRaw.Root m, (twE6Gamma i = twE6Gamma j ∨ twE6Gamma i = -twE6Gamma j) →
        i = j) ∧
      ∀ i j : ExcRaw.Root m, ExcRaw.pairing m i j = corootPair (twE6Gamma j) (twE6Gamma i) := by
  refine ⟨fun i => ?_, fun δ hδ => ?_, fun i j h => ?_, fun i j => ?_⟩
  · rw [← CFSG.Timmesfeld.ExceptionalOrders.mem_rootList]
    revert i
    rcases hm with rfl | rfl
    all_goals
      open scoped CFSG.Decide.Bounded in
      decide +kernel
  · rw [← CFSG.Timmesfeld.ExceptionalOrders.mem_rootList] at hδ
    revert δ
    rcases hm with rfl | rfl
    all_goals
      open scoped CFSG.Decide.Bounded in
      decide +kernel
  · revert i j
    rcases hm with rfl | rfl
    all_goals
      open scoped CFSG.Decide.Bounded in
      decide +kernel
  · revert i j
    rcases hm with rfl | rfl
    all_goals
      open scoped CFSG.Decide.Bounded in
      decide +kernel

private def twE6CorootExp {m : Fin 6} (i : ExcRaw.Root m) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ((corootPair (twE6Gamma i) (Pi.single j 1) : ℤ) : ZMod 3)

private theorem twE6CorootExp_two (i : ExcRaw.Root 2) : twE6CorootExp i = ExcRaw.coroot 2 i := by
  have h : ∀ (i : ExcRaw.Root 2) (j : Fin (ExcRaw.dim 2)),
      ((corootPair (twE6Gamma i) (Pi.single j 1) : ℤ) : ZMod 3) = ExcRaw.coroot 2 i j := by
    decide +kernel
  exact funext (h i)

theorem nonempty_excCoordDatum_two
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    (hT : zetaTorus ζ hζ ⊤ ≤ fullThreeTorus S) :
    Nonempty (ExcCoordDatum S (zetaTorus ζ hζ ⊤) 2) :=
  have h := twE6Gamma_facts (m := 2) (Or.inl rfl)
  nonempty_excCoordDatum_of_zetaTorus S hζ hζo hT twE6Gamma
    (AddSubgroup.topEquiv : ↥(⊤ : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) ≃+ ExcRaw.V 2)
    h.1 h.2.1 h.2.2.1 h.2.2.2 (fun _ _ => rfl)
    (fun i => ⟨AddSubgroup.mem_top _, twE6CorootExp_two i⟩)

private def twE6HypIn (c : ExcRaw.V 3) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ∑ l, c l * ExcRaw.coroot 2 (Fin.castLE (by decide) l) j

private def twE6HypTab : List (List ℕ) :=
  [[0, 2, 2, 1, 1, 1], [0, 2, 0, 0, 1, 2], [0, 1, 0, 2, 0, 1], [0, 0, 0, 0, 2, 1],
    [0, 0, 0, 0, 0, 2]]

private def twE6HypOut (x : Fin Tag.E6.rank → ZMod 3) : ExcRaw.V 3 :=
  fun l => ∑ j, (((twE6HypTab.getD l.val []).getD j.val 0 : ℕ) : ZMod 3) * x j

private theorem twE6HypIn_mem : ∀ c : ExcRaw.V 3, kDotP 3 (twE6HypIn c) = 0 := by
  decide +kernel

private theorem twE6HypIn_out : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
    twE6HypIn (twE6HypOut x) = x := by
  decide +kernel

private theorem twE6HypOut_in : ∀ c : ExcRaw.V 3, twE6HypOut (twE6HypIn c) = c := by
  decide +kernel

private def twE6HypEquiv : ↥hypE6 ≃+ ExcRaw.V 3 where
  toFun x := twE6HypOut x
  invFun c := ⟨twE6HypIn c, twE6HypIn_mem c⟩
  left_inv x := Subtype.ext (twE6HypIn_out x x.2)
  right_inv c := twE6HypOut_in c
  map_add' x y := by
    funext l
    simp only [twE6HypOut, AddSubgroup.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem twE6_root_three_check : ∀ (i : ExcRaw.Root 3) (l : Fin (ExcRaw.dim 3)),
    ∑ k, ((twE6Gamma i k : ℤ) : ZMod 3) * ExcRaw.coroot 2 (Fin.castLE (by decide) l) k =
      (ExcRaw.F 3 i l : ZMod 3) := by
  decide +kernel

private theorem twE6_root_three (c : ExcRaw.V 3) (i : ExcRaw.Root 3) :
    ∑ k, ((twE6Gamma i k : ℤ) : ZMod 3) * twE6HypIn c k = ExcRaw.root 3 i c := by
  simp only [twE6HypIn, Finset.mul_sum, ExcRaw.root_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← twE6_root_three_check i l, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem twE6CorootExp_three : ∀ i : ExcRaw.Root 3,
    kDotP 3 (twE6CorootExp i) = 0 ∧ twE6HypOut (twE6CorootExp i) = ExcRaw.coroot 3 i := by
  decide +kernel

theorem nonempty_excCoordDatum_three
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    (hT : zetaTorus ζ hζ hypE6 ≤ fullThreeTorus S) :
    Nonempty (ExcCoordDatum S (zetaTorus ζ hζ hypE6) 3) :=
  have h := twE6Gamma_facts (m := 3) (Or.inr rfl)
  nonempty_excCoordDatum_of_zetaTorus S hζ hζo hT twE6Gamma twE6HypEquiv
    h.1 h.2.1 h.2.2.1 h.2.2.2
    (fun x i => by
      change _ = ExcRaw.root 3 i (twE6HypOut x)
      conv_lhs => rw [← twE6HypIn_out x x.2]
      exact twE6_root_three _ i)
    (fun i => ⟨(twE6CorootExp_three i).1, (twE6CorootExp_three i).2⟩)

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
