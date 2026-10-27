module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BKG
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Quasithin.Vol2.Lie2ParabolicRadical

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint
open CFSG.Quasithin.Ch1Four

theorem false_of_isExt_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt X PV PY)
    (hV : ∀ (V : Type) [Group V] [Finite V], PV V →
      ∃ p : ℕ, p.Prime ∧ IsPGroup p V ∧ 1 < Nat.card V) : False := by
  obtain ⟨V, hVn, hPV, -⟩ := h
  obtain ⟨p, hp, hpV, h1⟩ := hV ↥V hPV
  have : Fact p.Prime := ⟨hp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with hb | ht
  · subst hb
    rw [Subgroup.card_bot] at h1
    exact lt_irrefl 1 h1
  · subst ht
    have hX : IsPGroup p X := hpV.of_equiv Subgroup.topEquiv
    have := Fintype.ofFinite X
    have : Group.IsNilpotent X := hX.isNilpotent
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

theorem pv_isE2 {k : ℕ} (hk : 1 ≤ k) (V : Type) [Group V] [Finite V] (hV : IsE2 k V) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p V ∧ 1 < Nat.card V :=
  ⟨2, Nat.prime_two, isPGroup_of_isE2 hV, by
    rw [card_isE2 hV]
    exact Nat.one_lt_two_pow (by omega)⟩

theorem pv_isExtraspecial2 {m : ℕ} (V : Type) [Group V] [Finite V] (hV : IsExtraspecial2 m V) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p V ∧ 1 < Nat.card V :=
  ⟨2, Nat.prime_two, isPGroup_of_isExtraspecial2 hV, by
    rw [card_isExtraspecial2 hV]
    exact Nat.one_lt_two_pow (by omega)⟩

theorem pv_isZ4Cubed (V : Type) [Group V] [Finite V] (hV : IsZ4Cubed V) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p V ∧ 1 < Nat.card V :=
  ⟨2, Nat.prime_two, isPGroup_of_isZ4Cubed hV, by rw [card_isZ4Cubed hV]; norm_num⟩

theorem pv_isZ4StarExtra2 (V : Type) [Group V] [Finite V] (hV : IsZ4StarExtra2 V) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p V ∧ 1 < Nat.card V := by
  refine ⟨2, Nat.prime_two, isPGroup_of_isZ4StarExtra2 hV, ?_⟩
  obtain ⟨Z, -, hZ, -⟩ := hV
  have h1 : Nat.card Z ≤ Nat.card V := Subgroup.card_le_card_group Z
  omega

section Rows

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {n : ℕ}

omit [Finite Q] in
theorem false_of_card_isSL2 (hn : 2 ≤ n) (hcard : Nat.card ↥B = 2 ^ n * oSL2 n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSL2 p ↥B) : False := by
  have hc := card_of_isSL2 hp h
  obtain ⟨rfl, rfl⟩ := eq_five_of_sl2 hp hp2 hn le_rfl (hc.symm.trans hcard)
  rw [hcard] at hc
  norm_num at hc

theorem rows_simple (hD : BarData B n) (hs : IsSimpleGroup ↥B)
    (hnab : ∃ a b : ↥B, a * b ≠ b * a) (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 1)
    (h : A312Case B L) :
    A312C2 B L ∨ (n = 2 ∧ (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7)) ∨
      IsPSL 2 5 2 ↥L ∨
      (∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 ↥L) ∨
      IsSporadic .J1 ↥L ∨ IsSporadic .J4 ↥L)) := by
  have hcard : Nat.card ↥B = 2 ^ n * oSL2 n := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), hO2, mul_one]
    exact hD.cardQ
  have hext : ∀ {PV PY : ∀ (V : Type) [Group V], Prop}, IsExt ↥B PV PY →
      (∀ (V : Type) [Group V] [Finite V], PV V →
        ∃ p : ℕ, p.Prime ∧ IsPGroup p V ∧ 1 < Nat.card V) → False :=
    fun hB hV => false_of_isExt_of_simple hs hnab hB hV
  have hE4 := pv_isE2 (k := 4) (by norm_num)
  have hE3 := pv_isE2 (k := 3) (by norm_num)
  have hE6 := pv_isE2 (k := 6) (by norm_num)
  have hE11 := pv_isE2 (k := 11) (by norm_num)
  rcases h with h | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, hL⟩ | (⟨hB, -⟩ | ⟨hB, -⟩) | h | h |
      h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exfalso
    apply not_three_dvd_card_of_isSz hf
    rw [hD.cardQ]
    exact dvd_mul_of_dvd_right (three_dvd_oSL2 n) _
  · exact absurd (hD.oSL2_eq' (d := 3) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq' (d := 6) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_315
  · exact Or.inr ⟨hD.eq_two (card_alt5 hB), hL.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  · exact absurd (hD.oSL2_eq (by decide) (card_L32 hB)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq (by decide) (card_alt6 hB)) oSL2_ne_45
  · exact absurd (hD.oSL2_eq (by decide) (card_hat6 hB)) oSL2_ne_135
  ·
    rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨hB, p, hp, hL, hp5, hp8⟩
    · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
      obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, hn⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n + 1) (by omega)
        (by rw [← h2, ha, pow_succ]; ring)
      exact Or.inr ⟨hn, Or.inr (Or.inr (Or.inl hL))⟩
    · exact Or.inr ⟨hD.eq_two (card_alt5 hB),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp5, hp8, hL⟩)))⟩
  ·
    exfalso
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · exact false_of_card_isSL2 hD.two_le hcard hp (by omega) hB
    · exact absurd (hD.oSL2_eq (by decide) (card_alt6 hB)) oSL2_ne_45
    · exact absurd (hD.oSL2_eq (by decide) (card_hat6 hB)) oSL2_ne_135
  ·
    exfalso
    obtain ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ := h
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcardV : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (Nat.card ↥V) := by
      rw [hcardV]
      exact (hp.odd_of_ne_two (by omega)).pow
    have hbot := hD.odd V hV hodd
    rw [hbot, Subgroup.card_bot] at hcardV
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  · exact absurd (hD.oSL2_eq (by decide) (card_alt6 h.1)) oSL2_ne_45
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩ <;> exact hext hB hE4
  ·
    exfalso
    rcases h with ⟨⟨⟨e⟩⟩ | hB | hB | hB | hB | hB | hB, -⟩
    · exact hD.false_of_M22 (k := 0) (m := 1) (one_dvd 3)
        (by rw [Nat.card_congr e.toEquiv, pow_zero, one_mul, one_mul]; rfl)
    · exact absurd (hD.oSL2_eq (by decide) (card_L34 hB)) oSL2_ne_315
    · exact hext hB hE4
    · exact hext hB hE4
    · exact hext hB hE3
    · exact hext hB hE4
    · exact hext hB hE4
  ·
    exfalso
    rcases h with ⟨hB | hB | hB | hB, -⟩
    · exact hext hB hE4
    · exact hext hB hE6
    · exact hext hB (fun V _ _ hV => pv_isExtraspecial2 V hV)
    · exact hext hB hE6
  · exact Or.inr ⟨hD.eq_two (card_alt5 h.1), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))⟩
  · exact (hext h.1 (fun V _ _ hV => pv_isExtraspecial2 V hV)).elim
  ·
    rcases h with ⟨hL, hB | hB | hB | hB | hB | hB⟩
    · exact (hext hB (fun V _ _ hV => pv_isExtraspecial2 V hV)).elim
    · exact (hext hB hE11).elim
    · exact Or.inr ⟨hD.eq_two' (card_alt5 hB), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL))))⟩
    · exact absurd (hD.oSL2_eq' (by decide) (card_hat6 hB)) oSL2_ne_135
    · exact absurd (hD.oSL2_eq' (by decide) (card_L42 hB)) oSL2_ne_315
    · exact absurd (hD.oSL2_eq' (by decide) (card_L32 hB)) oSL2_ne_21
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩
    · exact hext hB (fun V _ _ hV => pv_isZ4StarExtra2 V hV)
    · exact hext hB (fun V _ _ hV => pv_isZ4Cubed V hV)
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩
    · exact hext hB (fun V _ _ hV => pv_isExtraspecial2 V hV)
    · exact hext hB hE6
  ·
    exfalso
    obtain ⟨-, h11, -⟩ := h
    rw [hO2] at h11
    norm_num at h11

theorem surjective_comp_subtype_of_sup {Γ Y : Type} [Group Γ] [Group Y] (φ : Γ →* Y)
    (hφ : Function.Surjective φ) {A C : Subgroup Γ} (hAC : A ⊔ C = ⊤) (hC : C ≤ φ.ker) :
    Function.Surjective (φ.comp A.subtype) := by
  have hCb : C.map φ = ⊥ := (Subgroup.map_eq_bot_iff C).mpr hC
  have htop : A.map φ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective φ hφ, ← hAC, Subgroup.map_sup, hCb, sup_bot_eq]
  intro y
  have hy : y ∈ A.map φ := by rw [htop]; trivial
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨⟨a, ha⟩, rfl⟩

omit [Finite Q] in
theorem false_of_surjective_sl2 (hs : IsSimpleGroup ↥B) (hn : 2 ≤ n)
    (hcard : Nat.card ↥B = 2 ^ n * oSL2 n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hσ : Function.Surjective σ) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with hb | ht
  · have hinj : Function.Injective σ := (MonoidHom.ker_eq_bot_iff σ).mp hb
    exact false_of_card_isSL2 hn hcard hp hp2 ⟨MulEquiv.ofBijective σ ⟨hinj, hσ⟩⟩
  ·
    have h1 : ∀ y : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), y = 1 := fun y => by
      obtain ⟨b, rfl⟩ := hσ y
      exact (MonoidHom.mem_ker).mp (ht ▸ Subgroup.mem_top b)
    have hS : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = 1 := h1 _
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hS
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    have h3 : (2 : ZMod p) = 0 := by
      have := congrArg (· + 1) h2
      simp only [neg_add_cancel] at this
      rw [show (2 : ZMod p) = 1 + 1 by norm_num, ← this]
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.natCast_eq_zero_iff] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

omit [Finite Q] in
theorem false_of_a312Nonquasi_of_simple (hs : IsSimpleGroup ↥B) (hn : 2 ≤ n)
    (hcard : Nat.card ↥B = 2 ^ n * oSL2 n) (hBL : B ≤ L) (h : A312Nonquasi B L) : False := by
  unfold A312Nonquasi at h
  rcases h with ⟨-, hLeq, p, hp, hp2, hSL⟩ | ⟨-, -, N, hNn, hN, hSL⟩
  · obtain ⟨e⟩ : Nonempty (↥L ⧸ CFSG.oddCore ↥L ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := hSL
    set τ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥L)) with hτ
    have hτs : Function.Surjective τ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hOL : (CFSG.oddCore ↥L).map L.subtype ≤ L := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hsup : B.subgroupOf L ⊔ CFSG.oddCore ↥L = ⊤ := by
      have h1 : (B ⊔ (CFSG.oddCore ↥L).map L.subtype).subgroupOf L = ⊤ := by
        rw [← hLeq]
        exact Subgroup.subgroupOf_self L
      rw [Subgroup.subgroupOf_sup hBL hOL] at h1
      have h2 : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rwa [h2] at h1
    have hker : CFSG.oddCore ↥L ≤ τ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
    have hτB := surjective_comp_subtype_of_sup τ hτs hsup hker
    exact false_of_surjective_sl2 hs hn hcard hp hp2
      ((τ.comp (B.subgroupOf L).subtype).comp (Subgroup.subgroupOfEquivOfLe hBL).symm.toMonoidHom)
      (hτB.comp (Subgroup.subgroupOfEquivOfLe hBL).symm.surjective)
  · have := hNn
    obtain ⟨e⟩ : Nonempty (↥(B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⧸ N ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := hSL
    set τ : ↥(B ⊔ (CFSG.oddCore ↥L).map L.subtype) →*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      e.toMonoidHom.comp (QuotientGroup.mk' N) with hτ
    have hτs : Function.Surjective τ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hsup : B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⊔ N = ⊤ := by
      rw [hN, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hker : N ≤ τ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
    have hτB := surjective_comp_subtype_of_sup τ hτs hsup hker
    have hle : B ≤ B ⊔ (CFSG.oddCore ↥L).map L.subtype := le_sup_left
    exact false_of_surjective_sl2 hs hn hcard Nat.prime_five (by norm_num)
      ((τ.comp (B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).subtype).comp
        (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (hτB.comp (Subgroup.subgroupOfEquivOfLe hle).symm.surjective)

omit [Finite Q] in
theorem isMaxParabolic2_top_subgroupOf {P : Subgroup Q} (hP : IsMaxParabolic2 L P) :
    IsMaxParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
  obtain ⟨hpar, hne, hmax⟩ := hP
  have hPL : P ≤ L := hpar.1
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  refine ⟨(A312.isParabolic2_top_iff L _).mpr (hmap.symm ▸ hpar), ?_, ?_⟩
  · intro htop
    apply hne
    rw [← hmap, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · intro Q' hQ' hQ'top hPQ'
    have hQpar := (A312.isParabolic2_top_iff L Q').mp hQ'
    have hQne : Q'.map L.subtype ≠ L := by
      intro hQL
      apply hQ'top
      apply Subgroup.map_injective L.subtype_injective
      rw [hQL, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hle : P ≤ Q'.map L.subtype := hmap ▸ Subgroup.map_mono hPQ'
    have h1 := hmax _ hQpar hQne hle
    apply Subgroup.map_injective L.subtype_injective
    rw [h1, hmap]

omit [Finite Q] in
theorem one_lt_card_pCore_of_classical [Finite Q] {P : Subgroup Q} {f : ℕ} (hf : 2 ≤ f)
    (hL : (IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) ∨ IsPSp4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    1 < Nat.card (CFSG.pCore 2 ↥(perfectCore P)) := by
  have hP' := isMaxParabolic2_top_subgroupOf hP
  have hPL : P ≤ L := hP.1.1
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPL]
  let e : ↥(perfectCore (P.subgroupOf L)) ≃* ↥(perfectCore P) :=
    ((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hcore)
  rw [A312.card_pCore_eq e]
  obtain ⟨a, ha, o, ho, hY⟩ : ∃ a, 3 ≤ a ∧ ∃ o, Odd o ∧ Nat.card ↥L = 2 ^ (a * f) * o := by
    rcases hL with hL | hL
    · exact ⟨3, le_rfl, (Lie2Parabolic.two_part_of_type (Y := ↥L)).1 hL⟩
    · exact ⟨4, by norm_num, (Lie2Parabolic.two_part_of_type (Y := ↥L)).2 hL⟩
  rw [(Lie2Parabolic.card_perfectCore hf hL hP' ho hY).1]
  exact Nat.one_lt_two_pow (Nat.mul_ne_zero (by omega) (by omega))

theorem false_of_a312C2_of_simple (hExc : FactExcParabolicO2Ne) (hD : BarData B n)
    (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 1) (h : A312C2 B L) : False := by
  obtain ⟨⟨m, hm⟩, hrk, P, hP, rfl⟩ := h
  obtain ⟨hm1, hcm⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hm
  have hn := hD.two_le
  obtain ⟨rfl, -⟩ := two_pow_mul_odd_inj (odd_oSL2 hm1) (odd_oSL2 (m := n) (by omega))
    (hcm.symm.trans hD.cardQ)
  have hcard : Nat.card ↥(perfectCore P) = 2 ^ m * oSL2 m := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(perfectCore P)), hO2,
      mul_one]
    exact hcm
  have h168 : Nat.card ↥L = 168 → False := fun hL => by
    have hdvd : 2 ^ m * oSL2 m ∣ 168 := by
      rw [← hcard, ← hL]
      exact Subgroup.card_dvd_of_le ((CFSG.Quasithin.perfectCore_le P).trans hP.1.1)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
    · exact absurd hdvd (by decide)
    · have h8 : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h3
      have h63 : 63 ≤ oSL2 m := by
        have : 64 ≤ 2 ^ (2 * m) := by
          calc 64 = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [oSL2]
        omega
      have := Nat.mul_le_mul h8 h63
      omega
  have h1 : ¬ 1 < Nat.card (CFSG.pCore 2 ↥(perfectCore P)) := by rw [hO2]; exact lt_irrefl 1
  have hbot : CFSG.pCore 2 ↥(perfectCore P) = ⊥ := Subgroup.eq_bot_of_card_eq _ hO2
  rcases hrk with ⟨f, ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hL⟩ | ⟨hf, hf3, hL⟩⟩ | hT
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · exact h168 ((card_L32 hL).trans (by norm_num))
    · exact h1 (one_lt_card_pCore_of_classical hf2 (Or.inl (Or.inl hL)) hP)
  · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
      exact h168 (by rw [Nat.card_congr e.toEquiv, card_sl3, hK]; norm_num)
    · exact h1 (one_lt_card_pCore_of_classical hf2 (Or.inl (Or.inr hL)) hP)
  · exact h1 (one_lt_card_pCore_of_classical hf (Or.inr hL) hP)
  · exact hExc Q L P m hn (Or.inl ⟨f, Or.inl ⟨hf, hL⟩⟩) hP hm hbot
  · exact hExc Q L P m hn (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hL⟩)⟩) hP hm hbot
  · exact hExc Q L P m hn (Or.inl ⟨f, Or.inr (Or.inr ⟨hf, hf3, hL⟩)⟩) hP hm hbot
  · exact hExc Q L P m hn (Or.inr hT) hP hm hbot

end Rows

end CFSG.Quasithin.H13
