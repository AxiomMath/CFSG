module

public import CFSG.Timmesfeld.Transvection.FrameResidue
public import CFSG.Timmesfeld.CorollaryBDegen

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r}

@[expose] def residueElts (Δ : Set (Subgroup H)) (P Q : Fin r → Subgroup H) (k : Fin r) :
    Set ↥(residueGroup Δ P Q k) :=
  {x | (x : H) ≠ 1 ∧ ∃ X ∈ frameResidue Δ P Q k, (x : H) ∈ X}

theorem frameResidue_le_residueGroup {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) :
    X ≤ residueGroup Δ P Q k :=
  le_iSup₂_of_le X hX le_rfl

@[expose] def residueElt {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) {a : H} (ha : a ∈ X)
    (ha1 : a ≠ 1) :
    ↥(residueGroup Δ P Q k) :=
  ⟨a, frameResidue_le_residueGroup hX ha⟩

@[simp] theorem residueElt_coe {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) {a : H}
    (ha : a ∈ X) (ha1 : a ≠ 1) :
    ((residueElt hX ha ha1 : ↥(residueGroup Δ P Q k)) : H) = a := rfl

theorem residueElt_mem {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) {a : H}
    (ha : a ∈ X) (ha1 : a ≠ 1) : residueElt hX ha ha1 ∈ residueElts Δ P Q k :=
  ⟨by simpa using ha1, X, hX, ha⟩


theorem exists_mem_frameResidue_ne (hF : IsMaxFrame Δ P Q) (X : Subgroup H) :
    ∃ Y ∈ frameResidue Δ P Q k, Y ≠ X := by
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  have hQ : Q k ∈ frameResidue Δ P Q k := hF.toIsFrame.memQ_frameResidue k
  have hPneQ : P k ≠ Q k := (hF.opposite k).ne
  by_cases hXk : X = P k
  · exact ⟨Q k, hQ, by rw [hXk]; exact fun h => hPneQ h.symm⟩
  · exact ⟨P k, hP, fun h => hXk h.symm⟩

theorem isOddTransp_residueElts [Finite H] (hΔ : IsTransvectionClass Δ) (hML : MeetsLines Δ)
    (hF : IsMaxFrame Δ P Q) :
    Bridge.Asc72.IsOddTransp (residueElts Δ P Q k) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨hd1, X, hX, hdX⟩ := hd
    have hdd : d * d = 1 := Subtype.ext (hΔ.root.mul_self X hX.1 (d : H) hdX)
    exact orderOf_eq_prime (by rw [pow_two]; exact hdd) (fun h => hd1 (congrArg Subtype.val h))
  · intro d hd e he
    obtain ⟨hd1, X, hX, hdX⟩ := hd
    obtain ⟨he1, Y, hY, heY⟩ := he
    by_cases hXY : X = Y
    · have hdeX : (d : H) * (e : H) ∈ X := by
        rw [← hXY] at heY
        exact X.mul_mem hdX heY
      have hsq : (d * e) * (d * e) = 1 :=
        Subtype.ext (hΔ.root.mul_self X hX.1 ((d : H) * (e : H)) hdeX)
      exact Or.inl (orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two]))
    · have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hXY
      have hsqX : ∀ a ∈ X, a * a = 1 := fun a ha => hΔ.root.mul_self X hX.1 a ha
      have hodd : Odd (orderOf ((d : H) * (e : H))) :=
        Opposite.odd_orderOf_mul (A := X) (B := Y) hsqX hopp hdX hd1 heY he1
      exact Or.inr (by rw [← Subgroup.orderOf_coe]; simpa using hodd)


theorem isNormalSet_residueElts (hΔ : IsTransvectionClass Δ) :
    Connectivity.IsNormalSet (residueElts Δ P Q k) := by
  intro g d hd
  obtain ⟨hd1, X, hX, hdX⟩ := hd
  have hmem : (g : H) * (d : H) * (g : H)⁻¹ ∈ conjSub X (g : H) := by
    simpa [conjSub, MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj (g : H)).toMonoidHom hdX
  refine ⟨?_, conjSub X (g : H), conjSub_mem_frameResidue hΔ hX g.2, hmem⟩
  intro h
  apply hd1
  have h' : (g : H) * (d : H) * (g : H)⁻¹ = 1 := h
  have := congrArg (fun x : H => (g : H)⁻¹ * x * (g : H)) h'
  simpa [mul_assoc] using this

theorem closure_residueElts_eq_top :
    Subgroup.closure (residueElts Δ P Q k) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hle : residueGroup Δ P Q k ≤
      (Subgroup.closure (residueElts Δ P Q k)).map (residueGroup Δ P Q k).subtype := by
    refine iSup₂_le fun X hX y hy => ?_
    rcases eq_or_ne y 1 with rfl | hy1
    · exact Subgroup.mem_map_of_mem _ (Subgroup.one_mem _)
    · have hyL : y ∈ residueGroup Δ P Q k :=
        Subgroup.mem_iSup_of_mem X (Subgroup.mem_iSup_of_mem hX hy)
      have hy' : (⟨y, hyL⟩ : ↥(residueGroup Δ P Q k)) ∈ residueElts Δ P Q k :=
        ⟨hy1, X, hX, hy⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure hy')
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle x.2)
  have hxy : x = y := (Subtype.ext hyx).symm
  rwa [hxy]

theorem mul_mem_residueElts_of_commute [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {d e : ↥(residueGroup Δ P Q k)}
    (hd : d ∈ residueElts Δ P Q k) (he : e ∈ residueElts Δ P Q k) (hc : Commute d e)
    (hne : d ≠ e) : d * e ∈ residueElts Δ P Q k := by
  have hOT := isOddTransp_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  have hdD : d ∈ residueElts Δ P Q k := hd
  have heD : e ∈ residueElts Δ P Q k := he
  obtain ⟨hd1, X, hX, hdX⟩ := hd
  obtain ⟨he1, Y, hY, heY⟩ := he
  have he2 : e * e = 1 := Subtype.ext (hΔ.root.mul_self Y hY.1 (e : H) heY)
  have hprod_ne : d * e ≠ 1 := by
    intro h
    apply hne
    calc d = d * (e * e) := by rw [he2, mul_one]
      _ = (d * e) * e := by group
      _ = e := by rw [h, one_mul]
  have hXY : X = Y := by
    by_contra hXY
    have hsqX : ∀ a ∈ X, a * a = 1 := fun a ha => hΔ.root.mul_self X hX.1 a ha
    have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hXY
    have hodd : Odd (orderOf ((d : H) * (e : H))) :=
      Opposite.odd_orderOf_mul (A := X) (B := Y) hsqX hopp hdX hd1 heY he1
    have hord : orderOf (d * e) = 2 := hOT.orderOf_mul_eq_two hdD heD hne hc
    have hoddL : Odd (orderOf (d * e)) := by
      rw [← Subgroup.orderOf_coe]
      simpa using hodd
    rw [hord] at hoddL
    obtain ⟨m, hm⟩ := hoddL
    omega
  have hmem : (d : H) * (e : H) ∈ X := by
    rw [← hXY] at heY
    exact X.mul_mem hdX heY
  refine ⟨?_, X, hX, hmem⟩
  intro h
  exact hprod_ne (Subtype.ext h)

theorem exists_not_commute_residueElts [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {d : ↥(residueGroup Δ P Q k)}
    (hd : d ∈ residueElts Δ P Q k) :
    ∃ b ∈ residueElts Δ P Q k, ¬ Commute d b ∧ Odd (orderOf (d * b)) := by
  have hOT := isOddTransp_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  have hdD : d ∈ residueElts Δ P Q k := hd
  obtain ⟨hd1, X, hX, hdX⟩ := hd
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  have hQ : Q k ∈ frameResidue Δ P Q k := hF.toIsFrame.memQ_frameResidue k
  have hPneQ : P k ≠ Q k := (hF.opposite k).ne
  have hY : ∃ Y ∈ frameResidue Δ P Q k, Y ≠ X := by
    by_cases hXk : X = P k
    · exact ⟨Q k, hQ, by rw [hXk]; exact fun h => hPneQ h.symm⟩
    · exact ⟨P k, hP, fun h => hXk h.symm⟩
  obtain ⟨Y, hY, hYX⟩ := hY
  obtain ⟨b, hbY, hb1⟩ := hΔ.root.exists_ne_one hY.1
  let bL : ↥(residueGroup Δ P Q k) := residueElt hY hbY hb1
  have hbD : bL ∈ residueElts Δ P Q k := residueElt_mem hY hbY hb1
  have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hYX.symm
  have hsqX : ∀ a ∈ X, a * a = 1 := fun a ha => hΔ.root.mul_self X hX.1 a ha
  have hoddH : Odd (orderOf ((d : H) * (bL : H))) :=
    Opposite.odd_orderOf_mul (A := X) (B := Y) hsqX hopp hdX hd1 hbY hb1
  have hodd : Odd (orderOf (d * bL)) := by
    rw [← Subgroup.orderOf_coe]
    simpa using hoddH
  have hbne : d ≠ bL := by
    intro h
    have hmem : (d : H) ∈ X ⊓ Y := by
      refine ⟨hdX, ?_⟩
      rw [h]
      exact hbY
    rw [hopp.inf_eq_bot] at hmem
    exact hd1 (Subgroup.mem_bot.mp hmem)
  refine ⟨bL, hbD, ?_, hodd⟩
  intro hc
  have hord : orderOf (d * bL) = 2 := hOT.orderOf_mul_eq_two hdD hbD hbne hc
  rw [hord] at hodd
  obtain ⟨m, hm⟩ := hodd
  omega


theorem disconnected_residueElts [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) :
    Connectivity.Disconnected (residueElts Δ P Q k) := by
  have hOT := isOddTransp_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  have hQ : Q k ∈ frameResidue Δ P Q k := hF.toIsFrame.memQ_frameResidue k
  obtain ⟨a, haP, ha1⟩ := hΔ.root.exists_ne_one (hF.memP k)
  obtain ⟨b, hbQ, hb1⟩ := hΔ.root.exists_ne_one (hF.memQ k)
  let da : ↥(residueGroup Δ P Q k) := residueElt hP haP ha1
  let db : ↥(residueGroup Δ P Q k) := residueElt hQ hbQ hb1
  have hda : da ∈ residueElts Δ P Q k := residueElt_mem hP haP ha1
  have hdb : db ∈ residueElts Δ P Q k := residueElt_mem hQ hbQ hb1
  let S : Set ↥(residueGroup Δ P Q k) :=
    {y | y ∈ residueElts Δ P Q k ∧ (y : H) ∈ P k}
  have hdaS : da ∈ S := ⟨hda, haP⟩
  have hS : ∀ x ∈ S, ∀ y ∈ residueElts Δ P Q k, Commute x y → y ∈ S := by
    intro x hxS y hyD hxy
    obtain ⟨hxD, hxP⟩ := hxS
    have hyD' : y ∈ residueElts Δ P Q k := hyD
    obtain ⟨hy1, Y, hY, hyY⟩ := hyD
    have hYeq : Y = P k := by
      by_contra hne
      have hopp : Opposite (P k) Y :=
        hF.opposite_of_mem_frameResidue hΔ hML hP hY (Ne.symm hne)
      by_cases hxy' : x = y
      · have hyYx : (x : H) ∈ Y := by rw [hxy']; exact hyY
        have hmem : (x : H) ∈ P k ⊓ Y := ⟨hxP, hyYx⟩
        rw [hopp.inf_eq_bot] at hmem
        exact hxD.1 (Subgroup.mem_bot.mp hmem)
      · have hsqP : ∀ a ∈ P k, a * a = 1 :=
          fun a ha => hΔ.root.mul_self (P k) (hF.memP k) a ha
        have hoddH : Odd (orderOf ((x : H) * (y : H))) :=
          Opposite.odd_orderOf_mul (A := P k) (B := Y) hsqP hopp hxP hxD.1 hyY hy1
        have hord : orderOf (x * y) = 2 := hOT.orderOf_mul_eq_two hxD hyD' hxy' hxy
        have hoddL : Odd (orderOf (x * y)) := by
          rw [← Subgroup.orderOf_coe]
          simpa using hoddH
        rw [hord] at hoddL
        obtain ⟨m, hm⟩ := hoddL
        omega
    exact ⟨hyD', by rw [hYeq] at hyY; exact hyY⟩
  refine ⟨da, hda, db, hdb, ?_⟩
  intro hreach
  have hdbS : db ∈ S := Connectivity.mem_of_reach hS hdaS hreach
  have hbP : (db : H) ∈ P k := hdbS.2
  have hmem : (db : H) ∈ P k ⊓ Q k := ⟨hbP, hbQ⟩
  rw [(hF.opposite k).inf_eq_bot] at hmem
  exact hb1 (Subgroup.mem_bot.mp hmem)

theorem exists_mul_mem_residueElts [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) :
    ∃ u ∈ residueElts Δ P Q k, ∃ v ∈ residueElts Δ P Q k,
      u ≠ v ∧ Commute u v ∧ u * v ∈ residueElts Δ P Q k := by
  classical
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  letI : Fintype ↥(P k) := Fintype.ofFinite _
  have hcard : 4 ≤ Nat.card ↥(P k) := hq (P k) (hF.memP k)
  have hcard' : 4 ≤ Fintype.card ↥(P k) := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have h2 : 2 < (Finset.univ.erase (1 : ↥(P k))).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, c, hc, hdist⟩ := Finset.two_lt_card.mp h2
  have hab : a ≠ b := hdist.1
  have ha1 : (a : H) ≠ 1 := by
    intro h
    exact (Finset.mem_erase.mp ha).1 (Subtype.ext h)
  have hb1 : (b : H) ≠ 1 := by
    intro h
    exact (Finset.mem_erase.mp hb).1 (Subtype.ext h)
  let u : ↥(residueGroup Δ P Q k) := residueElt hP a.2 ha1
  let v : ↥(residueGroup Δ P Q k) := residueElt hP b.2 hb1
  have hu : u ∈ residueElts Δ P Q k := residueElt_mem hP a.2 ha1
  have hv : v ∈ residueElts Δ P Q k := residueElt_mem hP b.2 hb1
  have huv : u ≠ v := by
    intro h
    apply hab
    apply Subtype.ext
    exact congrArg (fun x : ↥(residueGroup Δ P Q k) => (x : H)) h
  have hcomm : Commute u v := by
    apply Subtype.ext
    change (a : H) * (b : H) = (b : H) * (a : H)
    exact (hΔ.root.commuting_self (hF.memP k) a a.2 b b.2).eq
  exact ⟨u, hu, v, hv, huv, hcomm,
    mul_mem_residueElts_of_commute hΔ hML hF hu hv hcomm huv⟩


theorem zStar_residueGroup_eq_center [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) :
    Bridge.zStar ↥(residueGroup Δ P Q k) = Subgroup.center ↥(residueGroup Δ P Q k) := by
  have hOT := isOddTransp_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  have hN := isNormalSet_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ
  have hgen := closure_residueElts_eq_top (Δ := Δ) (P := P) (Q := Q) (k := k)
  have hsq : ∀ d ∈ residueElts Δ P Q k, ∀ e ∈ residueElts Δ P Q k,
      Commute d e → d ≠ e → d * e ∈ residueElts Δ P Q k := by
    intro d hd e he hc hne
    exact mul_mem_residueElts_of_commute (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hd he hc hne
  have hopp : ∀ d ∈ residueElts Δ P Q k,
      ∃ b ∈ residueElts Δ P Q k, ¬ Commute d b ∧ Odd (orderOf (d * b)) := by
    intro d hd
    exact exists_not_commute_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hd
  exact CorB.zStar_eq_center hOT hN hgen hsq hopp

end CFSG.Timmesfeld.Transvection
