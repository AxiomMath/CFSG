module

public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def restrictAutInvariant {X : Type*} [Group X] (α : MulAut X)
    (P : Subgroup X) (hP : P.map (α : X →* X) = P) : MulAut P :=
  (α.subgroupMap P).trans (MulEquiv.subgroupCongr hP)

private theorem coe_restrictAutInvariant {X : Type*} [Group X] (α : MulAut X) {P : Subgroup X}
    (hP : P.map (α : X →* X) = P) (x : P) :
    ((restrictAutInvariant α P hP x : P) : X) = α x :=
  rfl

private theorem coe_restrictAutInvariant_pow {X : Type*} [Group X] (α : MulAut X)
    {P : Subgroup X} (hP : P.map (α : X →* X) = P) (n : ℕ) (x : P) :
    ((restrictAutInvariant α P hP ^ n) x : X) = (α ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem s16c1614_not_dvd_of_symSumOfConj {W : Type} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {m ℓ : ℕ} (hℓ : ℓ.Prime)
    (h24 : ¬ ℓ ∣ 24) (hGL : ¬ ℓ ∣ ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)))
    (hS : SymSumOfConj A (⊤ : Subgroup W) 3 m) : ¬ ℓ ∣ Nat.card A := by
  classical
  intro hdiv
  obtain ⟨Z, hZrk, _hind, hsup, hXcard, _hS4⟩ := hS
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (congrFun h))
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) ℓ hdiv
  let a' : MulAut W := (a : MulAut W)
  have ha'ord : orderOf a' = ℓ := by
    rw [show a' = A.subtype a from rfl, orderOf_injective A.subtype A.subtype_injective a, ha]
  have hcard4 : Nat.card ↥(conjSubs A Z) = 4 := by
    rw [Nat.card_coe_set_eq]
    omega
  haveI hfinX : Finite ↥(conjSubs A Z) :=
    Finite.of_surjective
      (fun g : ↥A => (⟨Z.map (g : MulAut W).toMonoidHom,
        ⟨(g : MulAut W), g.2, rfl⟩⟩ : ↥(conjSubs A Z)))
      (by
        rintro ⟨Y, hY⟩
        obtain ⟨g, hg, rfl⟩ := hY
        exact ⟨⟨g, hg⟩, rfl⟩)
  let P : Subgroup (MulAut W) := Subgroup.zpowers a'
  have hPA : P ≤ A := by
    show Subgroup.zpowers a' ≤ A
    rw [Subgroup.zpowers_le]
    exact a.2
  have hmem : ∀ (p : ↥P) (Y : ↥(conjSubs A Z)),
      (Y : Subgroup W).map (p : MulAut W).toMonoidHom ∈ conjSubs A Z := by
    intro p Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    refine ⟨(p : MulAut W) * g, A.mul_mem (hPA p.2) hg, ?_⟩
    rw [hgY, Subgroup.map_map]
    rfl
  letI : MulAction ↥P ↥(conjSubs A Z) :=
    { smul := fun p Y => ⟨(Y : Subgroup W).map (p : MulAut W).toMonoidHom, hmem p Y⟩
      one_smul := by
        intro Y
        apply Subtype.ext
        show (Y : Subgroup W).map (MonoidHom.id W) = (Y : Subgroup W)
        rw [Subgroup.map_id]
      mul_smul := by
        intro p q Y
        apply Subtype.ext
        show (Y : Subgroup W).map (((p * q : ↥P) : MulAut W)).toMonoidHom
            = ((Y : Subgroup W).map (q : MulAut W).toMonoidHom).map
                (p : MulAut W).toMonoidHom
        rw [Subgroup.map_map]
        rfl }
  let ρ : ↥P →* Equiv.Perm ↥(conjSubs A Z) := MulAction.toPermHom ↥P ↥(conjSubs A Z)
  let π : Equiv.Perm ↥(conjSubs A Z) := ρ ⟨a', Subgroup.mem_zpowers a'⟩
  have hordPelem : orderOf (⟨a', Subgroup.mem_zpowers a'⟩ : ↥P) = ℓ := by
    have h := orderOf_injective P.subtype P.subtype_injective
      (⟨a', Subgroup.mem_zpowers a'⟩ : ↥P)
    rw [show P.subtype ⟨a', Subgroup.mem_zpowers a'⟩ = a' from rfl, ha'ord] at h
    exact h.symm
  have hdvdℓ : orderOf π ∣ ℓ := by
    have h := orderOf_map_dvd ρ (⟨a', Subgroup.mem_zpowers a'⟩ : ↥P)
    rw [hordPelem] at h
    exact h
  have hdvd24 : orderOf π ∣ 24 := by
    have hcardPerm : Nat.card (Equiv.Perm ↥(conjSubs A Z)) = 24 := by
      rw [Nat.card_perm, hcard4]
      norm_num
    rw [← hcardPerm]
    exact orderOf_dvd_natCard π
  have hπord : orderOf π = 1 := by
    rcases (Nat.dvd_prime hℓ).mp hdvdℓ with h | h
    · exact h
    · exact absurd (h ▸ hdvd24) h24
  have hπ1 : π = 1 := orderOf_eq_one_iff.mp hπord
  have hfix : ∀ Y : ↥(conjSubs A Z), (Y : Subgroup W).map a'.toMonoidHom = Y := by
    intro Y
    have hsmul : (⟨a', Subgroup.mem_zpowers a'⟩ : ↥P) • Y = Y := by
      have h1 : π Y = Y := by rw [hπ1]; rfl
      rw [show π Y = MulAction.toPerm (⟨a', Subgroup.mem_zpowers a'⟩ : ↥P) Y from rfl,
        MulAction.toPerm_apply] at h1
      exact h1
    exact congrArg Subtype.val hsmul
  have haYpowAll : ∀ Y : ↥(conjSubs A Z),
      restrictAutInvariant a' (Y : Subgroup W) (hfix Y) ^ ℓ = 1 := by
    intro Y
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [coe_restrictAutInvariant_pow a' (hfix Y), ← ha'ord, pow_orderOf_eq_one]
    rfl
  have hstep2 : ∀ Y : ↥(conjSubs A Z), ∀ y : W, y ∈ (Y : Subgroup W) → a' y = y := by
    intro Y y hy
    let aY : MulAut ↥(Y : Subgroup W) := restrictAutInvariant a' (Y : Subgroup W) (hfix Y)
    have hrkY : rk ↥(Y : Subgroup W) = m := by
      obtain ⟨g, hg, hgY⟩ := Y.2
      rw [hgY, rk, Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
      exact hZrk
    have hcardY : Nat.card ↥(Y : Subgroup W) = 2 ^ m := by
      rw [card_eq_two_pow h2 (Y : Subgroup W), hrkY]
    have hcomm : ∀ x y : ↥(Y : Subgroup W), x * y = y * x := fun x y => mul_comm x y
    have hpowY : ∀ x : ↥(Y : Subgroup W), x ^ 2 = 1 := fun x => by
      apply Subtype.ext
      simpa using h2 (x : W)
    have hcardAut : Nat.card (MulAut ↥(Y : Subgroup W)) =
        ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) := by
      have := CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary (p := 2) hcomm hpowY
        (n := m) hcardY
      simpa using this
    have hpow1 : aY ^ ℓ = 1 := by
      have h := haYpowAll Y
      simpa [aY] using h
    have hdvdℓ' : orderOf aY ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr hpow1
    have hdvdAut : orderOf aY ∣ Nat.card (MulAut ↥(Y : Subgroup W)) := orderOf_dvd_natCard aY
    have haY1 : aY = 1 := by
      rcases (Nat.dvd_prime hℓ).mp hdvdℓ' with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        rw [h, hcardAut] at hdvdAut
        exact hGL hdvdAut
    have hpt : aY ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [haY1]; rfl
    have hcoe : a' y = y := by
      have h := congrArg Subtype.val hpt
      rw [show ((aY ⟨y, hy⟩ : ↥(Y : Subgroup W)) : W) = a' y from
        coe_restrictAutInvariant a' (hfix Y) ⟨y, hy⟩] at h
      simpa using h
    exact hcoe
  let Fix : Subgroup W := a'.toMonoidHom.eqLocus (MonoidHom.id W)
  have hleFix : sSup (conjSubs A Z) ≤ Fix := by
    rw [sSup_le_iff]
    intro Y hY y hy
    change a' y = y
    exact hstep2 ⟨Y, hY⟩ y hy
  have hFixTop : Fix = ⊤ := top_le_iff.mp (hsup ▸ hleFix)
  have ha'one : a' = 1 := by
    apply MulEquiv.ext
    intro w
    have hw : w ∈ Fix := by rw [hFixTop]; exact Subgroup.mem_top w
    exact hw
  have hcontr : orderOf a' = 1 := by rw [ha'one, orderOf_one]
  rw [ha'ord] at hcontr
  exact hℓ.ne_one hcontr

theorem s16c1614_not_seven_dvd_case168_4_three (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Case168_4At D V₀ V hV L 3 3) :
    ¬ 7 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  have hd : dParam 3 = 2 := orderOf_eq_prime (by decide) (by decide)
  have h2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := fun w => by
    induction w using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]
  have hS := h.2.1
  rw [hd] at hS
  exact s16c1614_not_dvd_of_symSumOfConj h2 (m := 2) (by norm_num) (by norm_num)
    (by norm_num [Fin.prod_univ_succ]) hS

theorem s16c1614_not_five_dvd_case168_4_seven (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Case168_4At D V₀ V hV L 7 3) :
    ¬ 5 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  have hd : dParam 7 = 3 := orderOf_eq_prime (by decide) (by decide)
  have h2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := fun w => by
    induction w using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]
  have hS := h.2.1
  rw [hd] at hS
  exact s16c1614_not_dvd_of_symSumOfConj h2 (m := 3) (by norm_num) (by norm_num)
    (by norm_num [Fin.prod_univ_succ]) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
