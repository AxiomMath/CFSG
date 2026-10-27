module

public import CFSG.Quasithin.Vol2.Ch3xB513
public import CFSG.Quasithin.Background.B5P4Num

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique

section Good

variable {W : Type*} [CommGroup W]

@[expose] def IsGood (G A : Subgroup (MulAut W)) : Prop :=
  A ≤ G ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
    (Nat.card (commV A) ≤ Nat.card A ∨ (IsQuadratic A ∧ Nat.card (commV A) ≤ Nat.card A ^ 2))

@[expose] def HasGood (G : Subgroup (MulAut W)) : Prop := ∃ A, IsGood G A

end Good

section Offender

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_offender_le {X A : Subgroup (MulAut V)} (hA : IsA2 X A)
    (hw : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ B, IsFFStarOffender X B ∧ Nat.card V ≤ Nat.card B * Nat.card (fixV B) := by
  classical
  let S : Set (Subgroup (MulAut V)) := {B | B ≤ A ∧ B ≠ ⊥}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨A, le_rfl, hA.ne_bot⟩
  obtain ⟨B, ⟨hBA, hBne⟩, hBmax⟩ := hSfin.exists_maximalFor
    (fun B : Subgroup (MulAut V) => Nat.card B * Nat.card (fixV B)) S hSne
  have hle : ∀ C ∈ S, Nat.card C * Nat.card (fixV C) ≤ Nat.card B * Nat.card (fixV B) := by
    intro C hC
    by_contra hlt
    push Not at hlt
    have h' : Nat.card C * Nat.card (fixV C) ≤ Nat.card B * Nat.card (fixV B) := hBmax hC hlt.le
    omega
  have hAB : Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B) :=
    hle A ⟨le_rfl, hA.ne_bot⟩
  refine ⟨B, ⟨hBA.trans hA.le, hBne, (hA.mono hBA hBne).isElemAbelian2, fun C hCB => ?_⟩,
    hw.trans hAB⟩
  by_cases hC : C = ⊥
  · subst hC
    rw [B1.card_bot_mul_card_fixV]
    exact hw.trans hAB
  · exact hle C ⟨hCB.trans hBA, hC⟩

end Offender

section Transport

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
include hV

theorem index_fixV_eq_card_commV_dualSub (A : Subgroup (MulAut V)) :
    (fixV A).index = Nat.card (commV (dualSub A)) := by
  rw [commV_dualSub hV]
  have h1 := dualAnn_card hV (fixV A)
  have h2 := Subgroup.index_mul_card (fixV A)
  have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)

theorem qOf_le_two_of_hasGood {X : Subgroup (MulAut V)} (h : HasGood (dualSub X)) :
    qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨A', hA'G, hA'ne, hA'el, hgood⟩ := h
  have hinj : Function.Injective (dualAct V) := dualAct_injective hV
  set A : Subgroup (MulAut V) := A'.comap (dualAct V) with hAdef
  have hAX : A ≤ X := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := hA'G ha
    rw [← hinj hxa]
    exact hx
  have hdual : dualSub A = A' := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, -, rfl⟩ := hA'G hy
    exact ⟨x, hy, rfl⟩
  have hcard : Nat.card A = Nat.card A' := by
    rw [← hdual]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hidx : (fixV A).index = Nat.card (commV A') := by
    rw [index_fixV_eq_card_commV_dualSub hV, hdual]
  have hAne : A ≠ ⊥ := by
    intro hbot
    apply hA'ne
    rw [← hdual, hbot]
    exact Subgroup.map_bot _
  have hAel : IsElemAbelian2 A := by
    refine ⟨fun a ha b hb => hinj ?_, fun a ha => hinj ?_⟩
    · rw [map_mul, map_mul]
      exact hA'el.1 _ ha _ hb
    · rw [map_pow, map_one]
      exact hA'el.2 _ ha
  have hA2 : IsA2 X A := ⟨hAX, hAne, hAel⟩
  have hVeq : Nat.card V = (fixV A).index * Nat.card (fixV A) := B1.card_eq_index_mul A
  rcases hgood with h1 | ⟨hq, h2⟩
  ·
    have hw : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
      rw [hVeq, hidx, hcard]
      exact Nat.mul_le_mul_right _ h1
    obtain ⟨B, hB, hBw⟩ := exists_offender_le hA2 hw
    have hr : rAV B ≤ 1 := (rAV_le_one_iff hV hB.isA2).2 hBw
    refine (B5.qOf_le_rAV_of_offender hV hB).trans ?_
    exact_mod_cast hr.trans (by norm_num)
  ·
    have hquad : IsQuadratic A := by
      rw [isQuadratic_dualSub_iff hV, hdual]
      exact hq
    have hpow : 2 ^ rkIdx (fixV A) ≤ 2 ^ (2 * rk A) := by
      rw [← B1.index_eq_two_pow hV, hidx, pow_mul', ← B1.card_elemAbelian hAel, hcard]
      exact h2
    have hle : rkIdx (fixV A) ≤ 2 * rk A := (Nat.pow_le_pow_iff_right (by norm_num)).1 hpow
    have hr : rAV A ≤ 2 := by
      have hmul := hA2.rAV_mul
      have hpos : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast hA2.rk_pos
      have h' : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk A : ℚ) := by exact_mod_cast hle
      rw [← hmul] at h'
      exact le_of_mul_le_mul_right h' hpos
    exact qOf_le_iff.2 ⟨A, hA2, hquad, hr⟩

end Transport

section Hyp

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem b53Hyp_of {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 (X.map (dualAct V)) = ⊥)
    (hJ : X.map (dualAct V) =
      @ffJ (V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct V)))
    (hsqtk : ∃ (H : Type) (_ : Group H) (_ : Finite H), SQTKTauCeti.StronglyQuasithin H ∧
      CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥(X.map (dualAct V)), Function.Surjective f) :
    B53Hyp (dualSub X) := by
  obtain ⟨H, _, _, hsq, hk, f, hf⟩ := hsqtk
  exact ⟨hO2, hJ, H, inferInstance, inferInstance, f.ker, inferInstance, ⟨hsq, hk⟩,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

end Hyp

@[expose] def Core : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ G : Subgroup (MulAut W), ¬ Group.IsSolvable ↥G → G ≠ ⊥ → B53Hyp G → HasGood G

theorem dualGrp_sq_eq_one {V : Type*} [CommGroup V] (φ : DualGrp V) : φ ^ 2 = 1 := by
  refine DualGrp.ext fun v => ?_
  have h : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  exact h (φ v)

theorem b513Nonsolvable_of_core (h : Core) : B513Nonsolvable := by
  intro V _ _ hV X hsolv hne hO2 hJ hsqtk
  have hinj : Function.Injective (dualAct V) := dualAct_injective hV
  have hne' : dualSub X ≠ ⊥ := fun h0 =>
    hne ((Subgroup.map_eq_bot_iff_of_injective X hinj).mp h0)
  have hsolv' : ¬ Group.IsSolvable ↥(dualSub X) := by
    intro hs
    have : Group.IsSolvable ↥(X.map (dualAct V)) := hs
    exact hsolv (Group.isSolvable_of_isSolvable_injective (f := (dualAct V).subgroupMap X)
      (fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))))
  exact qOf_le_two_of_hasGood hV (h (DualGrp V) dualGrp_sq_eq_one _ hsolv' hne'
    (b53Hyp_of hO2 hJ hsqtk))

end CFSG.Quasithin.B513N
