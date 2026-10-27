module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Comp
public import CFSG.RankThree.PartTwo.Sec4.Ronan431CBridge
public import CFSG.RankThree.PartTwo.Sec4.Ronan431Open
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoOutHolds
import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431C

open CFSG.RankThree.PartTwo.Sec4.Ronan431
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus f4TwoIndex)
open CFSG.LocalAnalysis.GLTheoremA.S8.L84 (isSp48 isBOfTwo)
open CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed (I1430LieTwoInn i1430LieTwoOut_holds)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem noCfgS431_of_simple_of_card_lt {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (h : Nat.card S < 1080) : NoCfgS431 S := fun _ σ K hc => by
  have hle := le_card_of_isType431 hc.isType
  have hmul := K.card_mul_index
  have hi : K.index = 1 ∨ K.index = 2 := by
    rcases hk : K.index with _ | _ | _ | m
    · rw [hk] at hmul
      have : 0 < Nat.card S := Nat.card_pos
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [hk] at hmul
      nlinarith
  rcases hi with hi | hi
  · have hK : K = ⊤ := Subgroup.index_eq_one.mp hi
    apply hc.ne_one
    ext x
    exact hc.le_autFix (hK ▸ Subgroup.mem_top x)
  · haveI := hs
    haveI := Subgroup.normal_of_index_eq_two hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hb | ht
    · rw [hb, Subgroup.card_bot] at hle
      omega
    · rw [ht, Subgroup.index_top] at hi
      omega

theorem card_ne_two_three {n : ℕ} (hn : 1 ≤ n) (hn2 : 2 ≤ n) :
    (⟨2, n, Nat.prime_two, hn⟩ : TauCeti.PrimePower).card ≠ 2 ∧
      (⟨2, n, Nat.prime_two, hn⟩ : TauCeti.PrimePower).card ≠ 3 ∧
      3 ≤ (⟨2, n, Nat.prime_two, hn⟩ : TauCeti.PrimePower).card := by
  rw [TauCeti.PrimePower.card_def]
  have h4 : 4 ≤ 2 ^ n := Ronan148L.four_le_two_pow hn2
  change 2 ^ n ≠ 2 ∧ 2 ^ n ≠ 3 ∧ 3 ≤ 2 ^ n
  omega

section Lie


theorem noCfgS431_of_lieTwo (hI : I1430LieTwoInn) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hB : ∀ ℓ : ℕ, 3 ≤ ℓ → ¬ isBOfTwo ℓ (.lie d)) (hSp : ¬ isSp48 (.lie d)) :
    NoCfgS431 S := by
  intro A σ K hc
  have hcomp := compOfType_of_cfgS431 hc
  have hσ3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  by_cases hmem : σ ∈ innAutDerived S
  · obtain ⟨ℓ, hℓ, hBℓ⟩ := hI S hs hna d hd he σ hmem hσ3 hc.ne_one hcomp
    exact hB ℓ hℓ hBℓ
  · exact hSp (i1430LieTwoOut_holds S hs hna d hd he σ hmem hσ3 hcomp)

theorem rowSOf431_of_lieTwo (hI : I1430LieTwoInn) {X : Type} [Group X]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hB : ∀ ℓ : ℕ, 3 ≤ ℓ → ¬ isBOfTwo ℓ (.lie d)) (hSp : ¬ isSp48 (.lie d)) : RowSOf431 X :=
  rowSOf431_of_noCfg fun _ _ _ hs hna ⟨e⟩ =>
    noCfgS431_of_lieTwo hI hs hna d hd (hX.map (e.trans ·)) hB hSp

theorem seven_SL3 (hI : I1430LieTwoInn) :
    ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSL 3 (GaloisField 2 n)) := by
  intro n hn
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · refine rowSOf431_of_noCfg fun S _ _ _ _ ⟨e⟩ => noCfgS431_of_card_lt ?_
    rw [Nat.card_congr e.toEquiv, Ronan148L.card_projSL_three_two]
    norm_num
  · have hv : (TauCeti.LieTypeIndex.A 2 ⟨2, n, Nat.prime_two, hn⟩).Valid :=
      Ronan148L.valid_A (by norm_num) (fun h => absurd h (by norm_num))
        (fun _ => (card_ne_two_three hn hn2).1)
    exact rowSOf431_of_lieTwo hI ⟨.A 2 _, hv⟩ (TauCeti.LieTypeIndex.characteristic_A 2 _)
      (nonempty_projSL_equiv_lieA hn hv) (fun _ _ h => h) (fun h => h)

theorem seven_SU3 (hI : I1430LieTwoInn) : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSU 3 2 n) := by
  intro n hn
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · refine rowSOf431_of_noCfg fun S _ _ hs hna ⟨e⟩ => ?_
    exfalso
    haveI := hs
    haveI : Group.IsSolvable (projSU 3 2 1) := CFSG.RankThree.PartTwo.Sec13.isSolvable_projSU_two
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  · have hv : (TauCeti.LieTypeIndex.twistedA 2 ⟨2, n, Nat.prime_two, hn⟩).Valid :=
      Ronan148L.valid_twistedA le_rfl (fun _ => (card_ne_two_three hn hn2).2.2)
    exact rowSOf431_of_lieTwo hI ⟨.twistedA 2 _, hv⟩
      (TauCeti.LieTypeIndex.characteristic_twistedA 2 _) (nonempty_projSU_equiv_lieTwistedA hn hv)
      (fun _ _ h => h) (fun h => h)

theorem seven_Sp4_ne_three (hI : I1430LieTwoInn) :
    ∀ n : ℕ, 1 ≤ n → n ≠ 3 → RowSOf431 (projSp 2 (GaloisField 2 n)) := by
  intro n hn hn3
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · refine rowSOf431_of_noCfg fun S _ _ hs _ ⟨e⟩ => noCfgS431_of_simple_of_card_lt hs ?_
    rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSp_two_two]
    norm_num
  · have hv : (TauCeti.LieTypeIndex.B 2 ⟨2, n, Nat.prime_two, hn⟩).Valid :=
      Ronan148L.valid_B_two (card_ne_two_three hn hn2).1 (card_ne_two_three hn hn2).2.1
    refine rowSOf431_of_lieTwo hI ⟨.B 2 _, hv⟩ (TauCeti.LieTypeIndex.characteristic_B 2 _)
      (nonempty_projSp_two_equiv_lieB2 hn hv) (fun ℓ hℓ h => ?_) (fun h => ?_)
    · obtain ⟨h2, -⟩ : 2 = ℓ ∧ (⟨2, n, Nat.prime_two, hn⟩ : TauCeti.PrimePower).card = 2 := h
      omega
    · have h8 : (⟨2, n, Nat.prime_two, hn⟩ : TauCeti.PrimePower).card = 8 := h
      rw [TauCeti.PrimePower.card_def] at h8
      have h8' : 2 ^ n = 2 ^ 3 := h8
      exact hn3 (Nat.pow_right_injective le_rfl h8')

theorem seven_SU4 (hI : I1430LieTwoInn) : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSU 4 2 n) := by
  intro n hn
  have hv : (TauCeti.LieTypeIndex.twistedA 3 ⟨2, n, Nat.prime_two, hn⟩).Valid :=
    Ronan148L.valid_twistedA (by norm_num) (fun h => absurd h (by norm_num))
  exact rowSOf431_of_lieTwo hI ⟨.twistedA 3 _, hv⟩
    (TauCeti.LieTypeIndex.characteristic_twistedA 3 _) (nonempty_projSU_equiv_lieTwistedA hn hv)
    (fun _ _ h => h) (fun h => h)

theorem seven_G2 (hI : I1430LieTwoInn) :
    ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowSOf431 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  fun q hq2 hq => rowSOf431_of_lieTwo hI ⟨.G2 q, hq⟩
    ((TauCeti.LieTypeIndex.characteristic_G2 q).trans hq2) ⟨MulEquiv.refl _⟩ (fun _ _ h => h)
    (fun h => h)

theorem seven_D4 (hI : I1430LieTwoInn) :
    ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      RowSOf431 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
  fun q hq hq2 => rowSOf431_of_lieTwo hI ⟨.trialityD4 q, hq⟩
    ((TauCeti.LieTypeIndex.characteristic_trialityD4 q).trans hq2) ⟨MulEquiv.refl _⟩
    (fun _ _ h => h) (fun h => h)

theorem seven_F4 (hI : I1430LieTwoInn) :
    ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
      RowSOf431 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group :=
  fun m hm => rowSOf431_of_lieTwo hI ⟨.reeF4 m, hm⟩
    (TauCeti.LieTypeIndex.characteristic_reeF4 m) ⟨MulEquiv.refl _⟩ (fun _ _ h => h) (fun h => h)

theorem eight_SL6 (hI : I1430LieTwoInn) : RowSOf431 (projSL 6 (GaloisField 2 1)) := by
  have hv : (TauCeti.LieTypeIndex.A 5 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid :=
    Ronan148L.valid_A (by norm_num) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num))
  exact rowSOf431_of_lieTwo hI ⟨.A 5 _, hv⟩ (TauCeti.LieTypeIndex.characteristic_A 5 _)
    (nonempty_projSL_equiv_lieA le_rfl hv) (fun _ _ h => h) (fun h => h)

theorem eight_SL7 (hI : I1430LieTwoInn) : RowSOf431 (projSL 7 (GaloisField 2 1)) := by
  have hv : (TauCeti.LieTypeIndex.A 6 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid :=
    Ronan148L.valid_A (by norm_num) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num))
  exact rowSOf431_of_lieTwo hI ⟨.A 6 _, hv⟩ (TauCeti.LieTypeIndex.characteristic_A 6 _)
    (nonempty_projSL_equiv_lieA le_rfl hv) (fun _ _ h => h) (fun h => h)

theorem eight_OmegaMinus (hI : I1430LieTwoInn) :
    ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      RowSOf431 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  intro b c hbc
  have hv : (TauCeti.LieTypeIndex.twistedD (3 + 1) ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, not_false⟩
  exact rowSOf431_of_lieTwo hI ⟨.twistedD (3 + 1) _, hv⟩
    (TauCeti.LieTypeIndex.characteristic_twistedD _ _)
    (nonempty_projOmegaMinus_equiv_lieTwistedD le_rfl hbc hv) (fun _ _ h => h) (fun h => h)

theorem eight_SL4 (hI : I1430LieTwoInn) : RowSOf431 (projSL 4 (GaloisField 2 2)) := by
  have hv : (TauCeti.LieTypeIndex.A 3 ⟨2, 2, Nat.prime_two, by norm_num⟩).Valid :=
    Ronan148L.valid_A (by norm_num) (fun h => absurd h (by norm_num))
      (fun _ => (card_ne_two_three (by norm_num) le_rfl).1)
  exact rowSOf431_of_lieTwo hI ⟨.A 3 _, hv⟩ (TauCeti.LieTypeIndex.characteristic_A 3 _)
    (nonempty_projSL_equiv_lieA (by norm_num) hv) (fun _ _ h => h) (fun h => h)

theorem eight_Sp6_4 (hI : I1430LieTwoInn) : RowSOf431 (projSp 3 (GaloisField 2 2)) := by
  have hv : (TauCeti.LieTypeIndex.B 3 ⟨2, 2, Nat.prime_two, by norm_num⟩).Valid :=
    Ronan148L.valid_B_of_three_le le_rfl (by norm_num)
  refine rowSOf431_of_lieTwo hI ⟨.B 3 _, hv⟩ (TauCeti.LieTypeIndex.characteristic_B 3 _)
    (nonempty_projSp_equiv_lieB le_rfl (by norm_num) hv) (fun ℓ _ h => ?_) (fun h => h)
  obtain ⟨-, h2⟩ : 3 = ℓ ∧ (⟨2, 2, Nat.prime_two, by norm_num⟩ : TauCeti.PrimePower).card = 2 := h
  exact (card_ne_two_three (by norm_num) le_rfl).1 h2

theorem eight_F4 (hI : I1430LieTwoInn) : RowSOf431 (TauCeti.CFSGIndex.lie f4TwoIndex).Group :=
  rowSOf431_of_lieTwo hI f4TwoIndex (TauCeti.LieTypeIndex.characteristic_F4 _) ⟨MulEquiv.refl _⟩
    (fun _ _ h => h) (fun h => h)

end Lie

end CFSG.RankThree.PartTwo.Sec4.Ronan431C

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431


theorem k431OpenC_of_inn (hI : CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed.I1430LieTwoInn) :
    K431OpenC where
  seven_SL3 := Ronan431C.seven_SL3 hI
  seven_SU3 := Ronan431C.seven_SU3 hI
  seven_Sp4_ne_three := Ronan431C.seven_Sp4_ne_three hI
  seven_SU4 := Ronan431C.seven_SU4 hI
  seven_G2 := Ronan431C.seven_G2 hI
  seven_D4 := Ronan431C.seven_D4 hI
  seven_F4 := Ronan431C.seven_F4 hI
  eight_SL6 := Ronan431C.eight_SL6 hI
  eight_SL7 := Ronan431C.eight_SL7 hI
  eight_OmegaMinus := Ronan431C.eight_OmegaMinus hI
  eight_SL4 := Ronan431C.eight_SL4 hI
  eight_Sp6_4 := Ronan431C.eight_Sp6_4 hI
  eight_F4 := Ronan431C.eight_F4 hI

end CFSG.RankThree.PartTwo.Sec4.Ronan431
