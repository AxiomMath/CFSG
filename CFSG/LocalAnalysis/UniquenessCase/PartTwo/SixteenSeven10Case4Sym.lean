module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10CardLem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen
public import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private noncomputable def s16c1610_restrictAut {X : Type*} [Group X] (α : MulAut X)
    (P : Subgroup X) (hP : P.map (α : X →* X) = P) : MulAut P :=
  (α.subgroupMap P).trans (MulEquiv.subgroupCongr hP)

private theorem s16c1610_coe_restrictAut {X : Type*} [Group X] (α : MulAut X) {P : Subgroup X}
    (hP : P.map (α : X →* X) = P) (x : P) :
    ((s16c1610_restrictAut α P hP x : P) : X) = α x :=
  rfl

private theorem s16c1610_coe_restrictAut_pow {X : Type*} [Group X] (α : MulAut X)
    {P : Subgroup X} (hP : P.map (α : X →* X) = P) (n : ℕ) (x : P) :
    ((s16c1610_restrictAut α P hP ^ n) x : X) = (α ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

private theorem s16c1610_finite_conjSubs {W : Type} [CommGroup W] [Finite W]
    (A : Subgroup (MulAut W)) (Z : Subgroup W) : Finite ↥(conjSubs A Z) := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (congrFun h))
  exact Finite.of_surjective
    (fun g : ↥A => (⟨Z.map (g : MulAut W).toMonoidHom,
      ⟨(g : MulAut W), g.2, rfl⟩⟩ : ↥(conjSubs A Z)))
    (by
      rintro ⟨Y, hY⟩
      obtain ⟨g, hg, rfl⟩ := hY
      exact ⟨⟨g, hg⟩, rfl⟩)

theorem s16c1610_not_dvd_of_symSumOfConj {W : Type} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {r m ℓ : ℕ} (hℓ : ℓ.Prime)
    (hperm : ¬ ℓ ∣ (r + 1).factorial) (hGL : ¬ ℓ ∣ ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)))
    (hS : SymSumOfConj A (⊤ : Subgroup W) r m) : ¬ ℓ ∣ Nat.card A := by
  classical
  intro hdiv
  obtain ⟨Z, hZrk, _hind, hsup, hXcard, _hSym⟩ := hS
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (congrFun h))
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) ℓ hdiv
  let a' : MulAut W := (a : MulAut W)
  have ha'ord : orderOf a' = ℓ := by
    rw [show a' = A.subtype a from rfl, orderOf_injective A.subtype A.subtype_injective a, ha]
  have hcardX : Nat.card ↥(conjSubs A Z) = r + 1 := by
    rw [Nat.card_coe_set_eq]
    exact hXcard
  haveI hfinX : Finite ↥(conjSubs A Z) := s16c1610_finite_conjSubs A Z
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
  have hdvdfac : orderOf π ∣ (r + 1).factorial := by
    have hcardPerm : Nat.card (Equiv.Perm ↥(conjSubs A Z)) = (r + 1).factorial := by
      rw [Nat.card_perm, hcardX]
    rw [← hcardPerm]
    exact orderOf_dvd_natCard π
  have hπord : orderOf π = 1 := by
    rcases (Nat.dvd_prime hℓ).mp hdvdℓ with h | h
    · exact h
    · exact absurd (h ▸ hdvdfac) hperm
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
      s16c1610_restrictAut a' (Y : Subgroup W) (hfix Y) ^ ℓ = 1 := by
    intro Y
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [s16c1610_coe_restrictAut_pow a' (hfix Y), ← ha'ord, pow_orderOf_eq_one]
    rfl
  have hstep2 : ∀ Y : ↥(conjSubs A Z), ∀ y : W, y ∈ (Y : Subgroup W) → a' y = y := by
    intro Y y hy
    let aY : MulAut ↥(Y : Subgroup W) := s16c1610_restrictAut a' (Y : Subgroup W) (hfix Y)
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
        s16c1610_coe_restrictAut a' (hfix Y) ⟨y, hy⟩] at h
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

theorem s16c1610_rk_of_symSumOfConj {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {r m : ℕ} (hS : SymSumOfConj A (⊤ : Subgroup W) r m) :
    rk W = (r + 1) * m := by
  classical
  obtain ⟨Z, hZrk, hind, hsup, hXcard, _hSym⟩ := hS
  haveI hfinX : Finite ↥(conjSubs A Z) := s16c1610_finite_conjSubs A Z
  haveI : Fintype ↥(conjSubs A Z) := Fintype.ofFinite _
  have hiSup : iSupIndep (fun Y : ↥(conjSubs A Z) => (Y : Subgroup W)) :=
    (sSupIndep_iff _).1 hind
  have hsum := rk_iSup_biSup_eq_sum (fun Y : ↥(conjSubs A Z) => (Y : Subgroup W)) hiSup
    Finset.univ
  have hrkY : ∀ Y : ↥(conjSubs A Z), rk ↥(Y : Subgroup W) = m := by
    intro Y
    obtain ⟨g, hg, hgY⟩ := Y.2
    rw [hgY, rk, Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
    exact hZrk
  have htop : (⨆ Y ∈ (Finset.univ : Finset ↥(conjSubs A Z)), (Y : Subgroup W)) = ⊤ := by
    rw [← hsup, sSup_eq_iSup']
    simp
  rw [htop, rk_top] at hsum
  rw [hsum, Finset.sum_congr rfl (fun Y _ => hrkY Y), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hXcard]

private theorem s16c1610_card_gl_two_three' :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [s16c1610_card_GL_two]
  decide

private theorem s16c1610_card_gl_four_three :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 2)) = 181440 := by
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Matrix.card_GL_field, hq]
  decide

private theorem s16c1610_card_sl_four_three :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
  have h := s16c1610_card_SL_four 3 (by norm_num)
  have h2 : ∏ i : Fin 3, (4 ^ 3 - 4 ^ (i : ℕ)) = 181440 := by decide
  omega

theorem s16c1610_not_concl614_of_five_seven {W : Type} [CommGroup W] [Finite W]
    {G X : Subgroup (MulAut W)} (hXG : X ≤ G) (hrk : rk W = 6) (h5 : ¬ 5 ∣ Nat.card G)
    (h7 : ¬ 7 ∣ Nat.card G) : ¬ Concl614 W G X := by
  rintro ((⟨m, h⟩ | ⟨m, h⟩ | ⟨hS6, -⟩) | ⟨m, h⟩)
  · have hc := s16c1610_card_of_isTensorS3L2 h
    have hm : m = 3 := by
      have := s16c1610_rk_eq_of_card hc.2
      omega
    subst hm
    apply h7
    rw [hc.1, s16c1610_card_gl_two_three']
    decide
  · have hc := s16c1610_card_of_isNatGL4 h
    have hm : m = 3 := by
      have := s16c1610_rk_eq_of_card hc.2
      omega
    subst hm
    apply h7
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le
      (inf_le_left : G ⊓ Subgroup.centralizer (X : Set (MulAut W)) ≤ G))
    rw [hc.1, s16c1610_card_gl_four_three]
    decide
  · apply h5
    rw [s16c1610_card_of_isS6Cover hXG hS6]
    exact Dvd.dvd.mul_right (by decide) _
  · have hc := s16c1610_card_of_isNatSL4 h
    have hm : m = 3 := by
      have := s16c1610_rk_eq_of_card hc.2
      omega
    subst hm
    apply h7
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le
      (inf_le_left : G ⊓ Subgroup.centralizer (X : Set (MulAut W)) ≤ G))
    rw [hc.1, s16c1610_card_sl_four_three]
    decide

theorem s16c1610_case4_two_card (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Case168_4At D V₀ V hV L 3 2) :
    rk (Vtil V₀ V hV) = 6 ∧ ¬ 5 ∣ Nat.card ↥(Mbar D.M V₀ V hV) ∧
      ¬ 7 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  have hd : dParam 3 = 2 := orderOf_eq_prime (by decide) (by decide)
  have h2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := Vtil_pow_two hV
  have hS := h.2.1
  rw [hd] at hS
  refine ⟨?_, ?_, ?_⟩
  · rw [s16c1610_rk_of_symSumOfConj hS]
  · exact s16c1610_not_dvd_of_symSumOfConj h2 (r := 2) (m := 2) (by norm_num) (by decide)
      (by decide) hS
  · exact s16c1610_not_dvd_of_symSumOfConj h2 (r := 2) (m := 2) (by norm_num) (by decide)
      (by decide) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
