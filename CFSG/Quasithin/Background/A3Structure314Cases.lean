module

public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.A314

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem p_eq_five_of_div {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p * (p ^ 2 - 1) / 2 = 60) :
    p = 5 := by
  have h1 : p * (p ^ 2 - 1) < 122 := by
    have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp (by omega : p * (p ^ 2 - 1) / 2 < 61)
    omega
  have hp5 : 5 ≤ p := A313.five_le_of_prime hp hp3
  by_contra hne
  have h6 : 6 ≤ p := by omega
  have : p ^ 2 ≥ 36 := by nlinarith
  have : p * (p ^ 2 - 1) ≥ 6 * 35 := Nat.mul_le_mul h6 (by omega)
  omega

theorem p_eq_five_of_mul {p : ℕ} (hp : p.Prime) (h : p * (p ^ 2 - 1) = 120) : p = 5 :=
  A313.mul_sq_sub_one_injective hp.one_lt.le (by norm_num) (by rw [h]; norm_num)

theorem isAlt_of_radical_eq {X : Type} [Group X] {V : Subgroup X} [V.Normal]
    (h : CFSG.solvableRadical X = V) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) :
    IsAlt 5 (X ⧸ V) :=
  IsAlt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq h) hA

theorem isAlt_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hna : ∃ a b : X, a * b ≠ b * a) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) :
    IsAlt 5 X := by
  let e : X ⧸ (⊥ : Subgroup X) ≃* X := QuotientGroup.quotientBot
  have hs' : IsSimpleGroup (X ⧸ (⊥ : Subgroup X)) := e.isSimpleGroup
  have hna' : ∃ a b : X ⧸ (⊥ : Subgroup X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have h := solvableRadical_eq_of_simple (V := ⊥) (Group.isSolvable_of_comm fun a b =>
    Subsingleton.elim _ _) hs' hna'
  exact IsAlt.of_mulEquiv e (isAlt_of_radical_eq h hA)

theorem p_eq_five_of_sl2 {X : Type} [Group X] [Finite X] {V : Subgroup X} [V.Normal]
    (hV : Group.IsSolvable ↥V) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hY : IsSL2 p (X ⧸ V)) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : p = 5 := by
  have hp5 : 5 ≤ p := A313.five_le_of_prime hp hp3
  have hq : CFSG.IsQuasisimple (X ⧸ V) := A313.IsSL2.isQuasisimple hp hp5 hY
  obtain ⟨e⟩ := solvableRadical_quotient_equiv hV hq
  have h60 : Nat.card ((X ⧸ V) ⧸ Subgroup.center (X ⧸ V)) = 60 := by
    rw [← Nat.card_congr e.toEquiv]
    exact card_isAlt_five hA
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (X ⧸ V))
  rw [h60, A313.IsSL2.card_center hp (by omega) hY, A313.IsSL2.card_eq hp hY] at hc
  exact p_eq_five_of_mul hp (by omega)

variable {G : Type} [Group G] [Finite G] {T B L : Subgroup G}

abbrev IsModel (X : Type) [Group X] : Prop :=
  IsPSL 3 2 1 X ∨ IsPSL 4 2 1 X ∨ IsPSL 3 2 2 X ∨ IsSporadic .M22 X ∨ IsSporadic .M24 X ∨
    ∃ f, IsSz f X

theorem excl_model_self {X : Type} [Group X] [Finite X] (hM : A314ModelFacts) (h : IsModel X)
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False :=
  let ⟨hs, hna, hn⟩ := hM.1 X h
  excl_simple_self hs hna hn hA

theorem excl_model_mod {X : Type} [Group X] [Finite X] (hM : A314ModelFacts) (V : Subgroup X)
    [V.Normal] (hV : Group.IsSolvable ↥V) (h : IsModel (X ⧸ V))
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False :=
  let ⟨hs, hna, hn⟩ := hM.1 (X ⧸ V) h
  excl_simple hV hs hna hn hA

theorem excl_model_ext {X : Type} [Group X] [Finite X] {PV PY : ∀ (V : Type) [Group V], Prop}
    (hM : A314ModelFacts) (h : IsExt X PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → Group.IsSolvable V)
    (hPY : ∀ (Y : Type) [Group Y], PY Y → IsModel Y)
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False :=
  excl_ext hPV (fun Y _ _ hY => hM.1 Y (hPY Y hY)) h hA

theorem excl_alt_self {n : ℕ} (h6 : 6 ≤ n) (h7 : n ≤ 7) {X : Type} [Group X] [Finite X]
    (h : IsAlt n X) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False :=
  let ⟨hs, hna, hn⟩ := isAlt_facts h6 h7 h
  excl_simple_self hs hna hn hA

theorem excl_alt_ext {n : ℕ} (h6 : 6 ≤ n) (h7 : n ≤ 7) {X : Type} [Group X] [Finite X]
    {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt X PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → Group.IsSolvable V)
    (hPY : ∀ (Y : Type) [Group Y], PY Y → IsAlt n Y)
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False :=
  excl_ext hPV (fun Y _ _ hY => isAlt_facts h6 h7 (hPY Y hY)) h hA

theorem excl_hat_ext {X : Type} [Group X] [Finite X] {PV PY : ∀ (V : Type) [Group V], Prop}
    {S : Type} [Group S] (h : IsExt X PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → Group.IsSolvable V)
    (hPY : ∀ (Y : Type) [Group Y], PY Y → IsHat Y S) (hS : Finite S → Nat.card S ≠ 60)
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  exact excl_hat (hPV _ hpv) (hPY _ hpy) hS hA

theorem hS_alt_six : Finite (alternatingGroup (Fin 6)) → Nat.card (alternatingGroup (Fin 6)) ≠ 60 :=
  fun _ => card_ne_sixty_of_isAlt_six ⟨MulEquiv.refl _⟩

theorem hS_m22 (hM : A314ModelFacts) : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) →
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) ≠ 60 := fun hfin => by
  have := hfin
  exact (hM.1 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))))).2.2

theorem solvable_isE2 (n : ℕ) (V : Type) [Group V] (h : IsE2 n V) : Group.IsSolvable V :=
  solvable_of_isElemAbelianOfRank h

omit [Finite G] in
theorem isBlock2_of_short (hB : B ∈ lFamily T) (hs : IsShort2 B) : IsBlock2 (B ⊔ T) B := by
  refine ⟨hs, le_sup_left, ?_⟩
  have h := A4.subnormal_subgroupOf (B ⊔ T)
    (subnormal_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB))
  rw [Subgroup.subgroupOf_self] at h
  exact A3.subnormal_top_iff.mp h

structure Ctx (T B L : Subgroup G) : Prop where
  hB : B ∈ lFamily T
  hBL : B < L
  hTL : IsSylowTwoOf (T ⊓ L) L
  hB1 : B ∈ lFamily (T ⊓ L)
  hA : IsAlt 5 (↥B ⧸ CFSG.solvableRadical ↥B)

theorem mathieu_data (hF : A314Facts) (c : Ctx T B L)
    (hL : IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥L)
    (hB : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    IsBlock2 (B ⊔ T) B ∧ IsLin2Type B 2 := by
  obtain ⟨hs, hl⟩ := hF.desc.mathieu G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
  exact ⟨isBlock2_of_short c.hB hs, hl⟩

theorem case2 (hF : A314Facts) (c : Ctx T B L) (h : A312C2 B L) : A314Statement T B L := by
  obtain ⟨⟨n, hn⟩, hrk, P, hP, hBP⟩ := h
  obtain ⟨hs, hna⟩ := hF.model.2.1 n _ hn
  have hrad : CFSG.solvableRadical ↥B = CFSG.pCore 2 ↥B :=
    solvableRadical_eq_of_simple (V := CFSG.pCore 2 ↥B) (solvable_pCore_two _) hs hna
  have hA5 : IsAlt 5 (ModO2 B) := isAlt_of_radical_eq hrad c.hA
  subst hBP
  obtain ⟨hF1, hL⟩ := hF.desc.lie G L P hrk hP hA5
  unfold A314Statement
  left
  exact ⟨hF1, hrad.symm, hL, P, hP, rfl⟩

theorem case3 (hF : A314Facts) (c : Ctx T B L) (h : A312C3 B L) : A314Statement T B L := by
  obtain ⟨f, hf, -⟩ := h
  exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hf⟩))))) c.hA).elim

theorem case4 (hF : A314Facts) (c : Ctx T B L) (h : A312C4 B L) : A314Statement T B L := by
  obtain ⟨hB3, -⟩ := h
  exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _) (Or.inl hB3) c.hA).elim

theorem case5 (hF : A314Facts) (c : Ctx T B L) (h : A312C5 B L) : A314Statement T B L := by
  obtain ⟨hB4, -⟩ := h
  exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
    (Or.inr (Or.inl hB4)) c.hA).elim

theorem case6 (hF : A314Facts) (c : Ctx T B L) (h : A312C6 B L) : A314Statement T B L := by
  obtain ⟨hB5 | hB3, hL7⟩ := h
  · unfold A314Statement
    refine Or.inr (Or.inl ⟨hB5, hL7, ?_⟩)
    exact hF.desc.alt7 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL7 hB5
  · exact (excl_model_self hF.model (Or.inl hB3) c.hA).elim

theorem case7 (c : Ctx T B L) (h : A312C7 B L) : A314Statement T B L := by
  rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
  · exact (excl_alt_self (by norm_num) (by norm_num) hB c.hA).elim
  · exact (excl_hat_self hB hS_alt_six c.hA).elim

theorem case8 (hF : A314Facts) (c : Ctx T B L) (h : A312C8 B L) : A314Statement T B L := by
  rcases h with ⟨p, hp, hp3, hBp, hLp⟩ | ⟨hB5, p, hp, hLp, h5, h8⟩
  · obtain ⟨hs, hna, hcard⟩ := hF.model.2.2 p hp hp3 ↥B hBp
    have hB5 : IsAlt 5 ↥B := isAlt_of_simple hs hna c.hA
    have hp5 : p = 5 := p_eq_five_of_div hp hp3 (by rw [← hcard]; exact card_isAlt_five hB5)
    subst hp5
    unfold A314Statement
    exact Or.inr (Or.inr (Or.inl ⟨hB5, Or.inl hLp⟩))
  · unfold A314Statement
    exact Or.inr (Or.inr (Or.inl ⟨hB5, Or.inr ⟨p, hp, h5, h8, hLp⟩⟩))

theorem case9 (hF : A314Facts) (c : Ctx T B L) (h : A312C9 B L) : A314Statement T B L := by
  rcases h with ⟨s, p, hp, hp3, hBp, hLp⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · have hp5 : p = 5 := by
      let e : ↥B ⧸ (⊥ : Subgroup ↥B) ≃* ↥B := QuotientGroup.quotientBot
      exact p_eq_five_of_sl2 (V := ⊥) (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
        hp hp3 (IsSL2.of_mulEquiv e.symm hBp) c.hA
    subst hp5
    have hLs : ∃ s : Bool, IsPSLEps3 s 5 1 ↥L ∨ IsSLEps3 s 5 ↥L := ⟨s, hLp⟩
    unfold A314Statement
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hBp, hLs,
      hF.desc.sl3five G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hLs hBp⟩)))
  · exact (excl_alt_self (by norm_num) (by norm_num) hB c.hA).elim
  · exact (excl_hat_self hB hS_alt_six c.hA).elim

theorem case10 (hF : A314Facts) (c : Ctx T B L) (h : A312C10 B L) : A314Statement T B L := by
  obtain ⟨p, hp, hp3, hBext, hLp⟩ := h
  have hp5 : p = 5 := by
    obtain ⟨V, hVn, hV, hY⟩ := hBext
    exact p_eq_five_of_sl2 (solvable_of_isElemAbelianOfRank hV) hp hp3 hY c.hA
  subst hp5
  unfold A314Statement
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hBext, hLp,
    hF.desc.l3five G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hLp hBext⟩))))

theorem case11 (c : Ctx T B L) (h : A312C11 B L) : A314Statement T B L :=
  (excl_alt_self (by norm_num) (by norm_num) h.1 c.hA).elim

theorem case12 (hF : A314Facts) (c : Ctx T B L) (h : A312C12 B L) : A314Statement T B L := by
  have hPV : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → Group.IsSolvable V :=
    fun V _ _ h => solvable_isE2 4 V h
  rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
  · obtain ⟨hbl, hl2⟩ := mathieu_data hF c (Or.inl hL) hB
    unfold A314Statement
    iterate 5 right
    left
    exact ⟨hB, hbl, hl2, Or.inl hL⟩
  · exact (excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV (fun Y _ hY => hY) c.hA).elim
  · obtain ⟨hbl, hl2⟩ := mathieu_data hF c (Or.inr (Or.inl hL)) hB
    unfold A314Statement
    iterate 5 right
    left
    exact ⟨hB, hbl, hl2, Or.inr hL⟩
  · exact (excl_hat_ext hB hPV (fun Y _ hY => hY) hS_alt_six c.hA).elim

theorem case13 (hF : A314Facts) (c : Ctx T B L) (h : A312C13 B L) : A314Statement T B L := by
  have hPV4 : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → Group.IsSolvable V :=
    fun V _ _ h => solvable_isE2 4 V h
  have hPV3 : ∀ (V : Type) [Group V] [Finite V], IsE2 3 V → Group.IsSolvable V :=
    fun V _ _ h => solvable_isE2 3 V h
  obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
  · exact (excl_model_self hF.model (Or.inr (Or.inr (Or.inr (Or.inl hB)))) c.hA).elim
  · exact (excl_model_self hF.model (Or.inr (Or.inr (Or.inl hB))) c.hA).elim
  · exact (excl_alt_ext (n := 7) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) c.hA).elim
  · exact (excl_model_ext hF.model hB hPV4 (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_model_ext hF.model hB hPV3 (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) c.hA).elim
  · obtain ⟨hbl, hl2⟩ := mathieu_data hF c (Or.inr (Or.inr hL)) hB
    unfold A314Statement
    iterate 6 right
    left
    exact ⟨hB, hbl, hl2, hL⟩

theorem case14 (hF : A314Facts) (c : Ctx T B L) (h : A312C14 B L) : A314Statement T B L := by
  obtain ⟨hB | hB | hB | hB, -⟩ := h
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_isE2 4 V h)
      (fun Y _ hY => Or.inr (Or.inl hY)) c.hA).elim
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_isE2 6 V h)
      (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_of_isExtraspecial2 h)
      (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_hat_ext hB (fun V _ _ h => solvable_isE2 6 V h) (fun Y _ hY => hY)
      hS_alt_six c.hA).elim

theorem case15 (hF : A314Facts) (c : Ctx T B L) (h : A312C15 B L) : A314Statement T B L := by
  obtain ⟨hB, hL⟩ := h
  have hz := hF.desc.j1 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
  unfold A314Statement
  iterate 7 right
  left
  exact ⟨hB, hL, hz⟩

theorem case16 (hF : A314Facts) (c : Ctx T B L) (h : A312C16 B L) : A314Statement T B L := by
  obtain ⟨hB, hL⟩ := h
  have hz := hF.desc.j2 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
  unfold A314Statement
  iterate 8 right
  left
  exact ⟨hB, hL, hz⟩

theorem case17 (hF : A314Facts) (c : Ctx T B L) (h : A312C17 B L) : A314Statement T B L := by
  obtain ⟨hL, hB | hB | hB | hB | hB | hB⟩ := h
  · exact (excl_hat_ext hB (fun V _ _ h => solvable_of_isExtraspecial2 h) (fun Y _ hY => hY)
      (hS_m22 hF.model) c.hA).elim
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_isE2 11 V h)
      (fun Y _ hY => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hY))))) c.hA).elim
  · have hF' := hF.desc.j4 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
    unfold A314Statement
    iterate 9 right
    left
    exact ⟨hB, hF', hL⟩
  · exact (excl_hat (V := CFSG.pCore 2 ↥B) (solvable_pCore_two _) hB hS_alt_six c.hA).elim
  · exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
      (Or.inr (Or.inl hB)) c.hA).elim
  · exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
      (Or.inl hB) c.hA).elim

theorem case18 (hF : A314Facts) (c : Ctx T B L) (h : A312C18 B L) : A314Statement T B L := by
  obtain ⟨hB | hB, hL⟩ := h
  · have hz := hF.desc.hs G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
    unfold A314Statement
    iterate 10 right
    left
    exact ⟨hB, hL, hz⟩
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_of_isZ4Cubed h)
      (fun Y _ hY => Or.inl hY) c.hA).elim

theorem case19 (hF : A314Facts) (c : Ctx T B L) (h : A312C19 B L) : A314Statement T B L := by
  obtain ⟨hB | hB, -⟩ := h
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_of_isExtraspecial2 h)
      (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_hat_ext hB (fun V _ _ h => solvable_isE2 6 V h) (fun Y _ hY => hY)
      hS_alt_six c.hA).elim

theorem case20 (hF : A314Facts) (c : Ctx T B L) (h : A312C20 B L) : A314Statement T B L := by
  obtain ⟨hB | hB, h11, hL⟩ := h
  · have hz := hF.desc.ru G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB h11
    unfold A314Statement
    iterate 11 right
    left
    exact ⟨hB, h11, hL, hz⟩
  · exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
      (Or.inl hB) c.hA).elim

theorem of_case (hF : A314Facts) (c : Ctx T B L) (h : A312Case B L) : A314Statement T B L := by
  unfold A312Case at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact case2 hF c h
  · exact case3 hF c h
  · exact case4 hF c h
  · exact case5 hF c h
  · exact case6 hF c h
  · exact case7 c h
  · exact case8 hF c h
  · exact case9 hF c h
  · exact case10 hF c h
  · exact case11 c h
  · exact case12 hF c h
  · exact case13 hF c h
  · exact case14 hF c h
  · exact case15 hF c h
  · exact case16 hF c h
  · exact case17 hF c h
  · exact case18 hF c h
  · exact case19 hF c h
  · exact case20 hF c h

end CFSG.Quasithin.A314
