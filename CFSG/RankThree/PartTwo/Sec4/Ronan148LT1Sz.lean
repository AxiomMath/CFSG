module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Comp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)

theorem one_le_of_valid_suzuki {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) : 1 ≤ m := by
  have h := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  simp [TauCeti.LieTypeIndex.inStandardRange_iff] at h
  omega

theorem exists_suzuki_of_lie (hb : LieOrderBridge) {X : Type} [Group X] [Finite X]
    (d : TauCeti.ValidLieTypeIndex) (he : Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h3 : ¬ 3 ∣ Nat.card X) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card X = CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) := by
  by_cases hsz : ∃ m, d.1 = .suzuki m
  · obtain ⟨m, hm⟩ := hsz
    obtain ⟨d, hd⟩ := d
    simp only at hm
    subst hm
    refine ⟨m, one_le_of_valid_suzuki hd, ?_⟩
    rw [hb ⟨_, hd⟩ X he]
    rfl
  · exact absurd (three_dvd_card_of_lie hb d (fun m hm => hsz ⟨m, hm⟩) he) h3

theorem exists_suzuki_of_isChevSimple (hb : LieOrderBridge) {X : Type} [Group X] [Finite X]
    (h : IsChevSimple 2 X) (h3 : ¬ 3 ∣ Nat.card X) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card X = CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) := by
  rcases h with ⟨i, hi, hf⟩ | ⟨i, hi, hf⟩
  · cases i with
    | lie d => exact exists_suzuki_of_lie hb d hf h3
    | _ => exact False.elim hi
  · cases i with
    | lie d => exact exists_suzuki_of_lie hb d hf h3
    | alternating n hn =>
      exfalso
      obtain ⟨f⟩ := hf
      apply h3
      rw [Nat.card_congr f.toEquiv]
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        decide
    | _ => exact False.elim hi

theorem three_or_suzuki_of_comps (hb : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {β : MulAut S} (h : LieCompsExport 2 β) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    3 ∣ Nat.card J ∨ ∃ m : ℕ, 1 ≤ m ∧ CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) ∣ Nat.card J := by
  by_cases h3 : 3 ∣ Nat.card J
  · exact Or.inl h3
  right
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps J hJ
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hfk
  have hQJ : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have h3X : ¬ 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [Nat.card_congr e.toEquiv]
    exact fun h' => h3 (h'.trans hQJ)
  obtain ⟨m, hm, hcard⟩ := exists_suzuki_of_isChevSimple hb hX.chev h3X
  refine ⟨m, hm, ?_⟩
  rw [← hcard, Nat.card_congr e.toEquiv]
  exact hQJ

theorem five_dvd_orderSuzuki (m : ℕ) : 5 ∣ CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) := by
  unfold CFSG.Open.orderSuzuki
  have h15 : (16 - 1 : ℕ) ∣ 16 ^ m - 1 := Nat.sub_one_dvd_pow_sub_one 16 m
  have hq : (2 ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
    rw [← pow_mul, show (2 * m + 1) * 2 = 2 + 4 * m by ring, pow_add, pow_mul]
    norm_num
  have h1 : 1 ≤ 16 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have h5 : 5 ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    rw [hq]
    obtain ⟨k, hk⟩ := (show (5 : ℕ) ∣ 16 - 1 by norm_num).trans h15
    have : 4 * 16 ^ m + 1 = 5 * (4 * k + 1) := by omega
    rw [this]
    exact Dvd.intro _ rfl
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h5 _) _

theorem sq_dvd_orderSuzuki (q : ℕ) : q ^ 2 ∣ CFSG.Open.orderSuzuki q := by
  unfold CFSG.Open.orderSuzuki
  exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _

theorem eq_bot_of_comps_noSz (hb : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {β : MulAut S} (h : LieCompsExport 2 β)
    (hno : ∀ m : ℕ, 1 ≤ m → ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
      CFSG.Open.orderSuzuki (2 ^ (2 * m + 1)) ∣ Nat.card J → False)
    {Y : Subgroup S} (hY : Y ≤ Sec4.autFix β)
    (hsn : (Y.subgroupOf (Sec4.autFix β)).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3Y : ¬ 3 ∣ Nat.card Y) : Y = ⊥ :=
  eq_bot_of_layer h.layer (fun J hJ => (three_or_suzuki_of_comps hb h hJ).resolve_right
    fun ⟨m, hm, hd⟩ => hno m hm J hJ hd) hY hsn hp h3Y

theorem false_of_dvd_of_noElt {S : Type} [Group S] [Finite S] {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hno : ∀ g : S, β g = g → g ^ p = 1 → g = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) (hpJ : p ∣ Nat.card J) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpJ
  have hgJ : ((g : S) ∈ fixSubgroup β) := hJ.1 g.2
  have h1 : (g : S) = 1 := hno g hgJ (by rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one]; rfl)
  have h1' : g = 1 := Subtype.ext h1
  rw [h1', orderOf_one] at hg
  exact hp.one_lt.ne hg

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
