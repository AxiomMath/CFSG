module

public import CFSG.Quasithin.EmptyFaithful.S152He6Basic

public section

namespace CFSG.Quasithin.He6

open CFSG.Quasithin
open scoped commutatorElement

structure PairData (W : Type) [CommGroup W] : Type where
  A : Subgroup (MulAut W)
  A' : Subgroup (MulAut W)
  Xb : Subgroup (MulAut W)
  hW : ∀ w : W, w * w = 1
  comm : ∀ x ∈ A, ∀ y ∈ A', x * y = y * x
  simpA : IsSimpleGroup ↥A
  simpA' : IsSimpleGroup ↥A'
  perfA : ⁅A, A⁆ = A
  perfA' : ⁅A', A'⁆ = A'
  irr : ∀ U : Subgroup W, (∀ g ∈ Xb, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤
  norm : ∀ g ∈ Xb,
    ((∀ x, x ∈ A ↔ g * x * g⁻¹ ∈ A) ∧ (∀ x, x ∈ A' ↔ g * x * g⁻¹ ∈ A')) ∨
      ((∀ x, x ∈ A ↔ g * x * g⁻¹ ∈ A') ∧ (∀ x, x ∈ A' ↔ g * x * g⁻¹ ∈ A))

namespace PairData

variable {W : Type} [CommGroup W] (P : PairData W)

theorem comm' {y x : MulAut W} (hy : y ∈ P.A') (hx : x ∈ P.A) : y * x = x * y :=
  (P.comm x hx y hy).symm

theorem fixA_inv {y : MulAut W} (hy : y ∈ P.A') {d : W} (hd : d ∈ fixV P.A) : y d ∈ fixV P.A := by
  rw [mem_fixV] at hd ⊢
  intro x hx
  have h1 : x (y d) = y (x d) := by
    have := congrArg (fun m : MulAut W => m d) (P.comm x hx y hy)
    exact this
  rw [h1, hd x hx]

theorem fixA'_inv {x : MulAut W} (hx : x ∈ P.A) {d : W} (hd : d ∈ fixV P.A') : x d ∈ fixV P.A' := by
  rw [mem_fixV] at hd ⊢
  intro y hy
  have h1 : y (x d) = x (y d) := by
    have := congrArg (fun m : MulAut W => m d) (P.comm' hy hx)
    exact this
  rw [h1, hd y hy]

theorem fix_stay_or_swap {g : MulAut W} (hg : g ∈ P.Xb) :
    ((∀ d ∈ fixV P.A, g d ∈ fixV P.A) ∧ (∀ d ∈ fixV P.A', g d ∈ fixV P.A')) ∨
      ((∀ d ∈ fixV P.A, g d ∈ fixV P.A') ∧ (∀ d ∈ fixV P.A', g d ∈ fixV P.A)) := by
  have key : ∀ B B' : Subgroup (MulAut W), (∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B') →
      ∀ d ∈ fixV B, g d ∈ fixV B' := by
    intro B B' hB d hd
    rw [mem_fixV] at hd ⊢
    intro x hx
    have hx1 : g⁻¹ * x * g ∈ B := by
      rw [hB]
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]
      exact hx
    have h2 := hd _ hx1
    calc x (g d) = (g * (g⁻¹ * x * g)) d := by
          rw [show g * (g⁻¹ * x * g) = x * g by group]; rfl
      _ = g ((g⁻¹ * x * g) d) := rfl
      _ = g d := by rw [h2]
  rcases P.norm g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key _ _ h1, key _ _ h2⟩
  · exact Or.inr ⟨key _ _ h1, key _ _ h2⟩

theorem fixSup_inv {g : MulAut W} (hg : g ∈ P.Xb) {u : W} (hu : u ∈ fixV P.A ⊔ fixV P.A') :
    g u ∈ fixV P.A ⊔ fixV P.A' := by
  have hD : ∀ d ∈ fixV P.A, g d ∈ fixV P.A ⊔ fixV P.A' := by
    intro d hd
    rcases P.fix_stay_or_swap hg with h | h
    · exact Subgroup.mem_sup_left (h.1 d hd)
    · exact Subgroup.mem_sup_right (h.1 d hd)
  have hD' : ∀ d ∈ fixV P.A', g d ∈ fixV P.A ⊔ fixV P.A' := by
    intro d hd
    rcases P.fix_stay_or_swap hg with h | h
    · exact Subgroup.mem_sup_right (h.2 d hd)
    · exact Subgroup.mem_sup_left (h.2 d hd)
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hu
  rw [map_mul]
  exact Subgroup.mul_mem _ (hD y hy) (hD' z hz)


section Alg

variable {a a' : MulAut W}

theorem dsp_dsp_comm (h : a * a' = a' * a) (w : W) : dsp a (dsp a' w) = dsp a' (dsp a w) := by
  have h1 : a (a' w) = a' (a w) := by
    have := congrArg (fun m : MulAut W => m w) h
    exact this
  simp only [dsp_apply, map_mul, map_inv, h1, mul_inv, inv_inv]
  ac_rfl

theorem dsp_dsp_eq_of_sq (hW : ∀ w : W, w * w = 1) (ha : a * a = 1) (w : W) :
    dsp a (dsp a' w) = dsp a (dsp (a * a') w) := by
  have hinv : ∀ v : W, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hW v)
  have haa : ∀ v, a (a v) = v := fun v => by
    have := congrArg (fun m : MulAut W => m v) ha
    exact this
  simp only [dsp_apply, map_mul, MulAut.mul_apply, hinv, haa]
  ac_rfl

end Alg

section Core

variable [Finite W]

theorem eq_of_le_of_card_ne_two {R Pp : Subgroup W} (hle : Pp ≤ R) (hne : Pp ≠ ⊥)
    (h2 : Nat.card Pp ≠ 2) (hR : Nat.card R ≤ 4) : Pp = R := by
  have hdvd : Nat.card Pp ∣ Nat.card R := Subgroup.card_dvd_of_le hle
  have hgt : 1 < Nat.card Pp := (Subgroup.one_lt_card_iff_ne_bot Pp).2 hne
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hle' : Nat.card Pp ≤ Nat.card R := Nat.le_of_dvd hRpos hdvd
  have heq : Nat.card Pp = Nat.card R := by
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hk; omega
      · exact h0
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      rw [hk, this, mul_one]
    · exfalso
      have : Nat.card Pp * 2 ≤ Nat.card Pp * k := Nat.mul_le_mul_left _ hk2
      omega
  exact Subgroup.eq_of_le_of_card_ge hle heq.symm.le

theorem eq_of_le_of_card_le_two {R Pp : Subgroup W} (hle : Pp ≤ R) (hne : Pp ≠ ⊥)
    (hR : Nat.card R ≤ 2) : Pp = R := by
  have hgt : 1 < Nat.card Pp := (Subgroup.one_lt_card_iff_ne_bot Pp).2 hne
  have hle' : Nat.card Pp ≤ Nat.card R := Subgroup.card_le_of_le hle
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

omit [Finite W] in
theorem acts_trivially_of_unipotent {a : MulAut W} (ha : a ∈ P.A) (ha1 : a ≠ 1)
    {Dp : Subgroup W} (hDp : ∀ g ∈ P.A, ∀ u ∈ Dp, g u ∈ Dp)
    {Q : Subgroup W} (hQfix : ∀ g ∈ P.A, ∀ q ∈ Q, g q = q) (haQ : cmt a Dp ≤ Q) :
    ∀ u ∈ Dp, a u = u := by
  let C : Subgroup (MulAut W) :=
    { carrier := {g | g ∈ P.A ∧ ∀ u ∈ Dp, g u * u⁻¹ ∈ Q}
      one_mem' := ⟨P.A.one_mem, fun u _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hgA, hg⟩ ⟨hhA, hh⟩
        refine ⟨P.A.mul_mem hgA hhA, fun u hu => ?_⟩
        have h1 : (g * h) u * u⁻¹ = (g (h u) * (h u)⁻¹) * (h u * u⁻¹) := by
          show g (h u) * u⁻¹ = _
          rw [mul_assoc, ← mul_assoc (h u)⁻¹, inv_mul_cancel, one_mul]
        rw [h1]
        exact Q.mul_mem (hg _ (hDp h hhA u hu)) (hh u hu)
      inv_mem' := by
        rintro g ⟨hgA, hg⟩
        refine ⟨P.A.inv_mem hgA, fun u hu => ?_⟩
        have hv : g⁻¹ u ∈ Dp := hDp g⁻¹ (P.A.inv_mem hgA) u hu
        have h1 := hg _ hv
        have h2 : g (g⁻¹ u) = u := MulAut.apply_inv_self W g u
        rw [h2] at h1
        have : g⁻¹ u * u⁻¹ = (u * (g⁻¹ u)⁻¹)⁻¹ := by
          rw [mul_inv, inv_inv, mul_comm]
        rw [this]
        exact Q.inv_mem h1 }
  have hCA : C ≤ P.A := fun g hg => hg.1
  have hCnorm : ∀ k ∈ P.A, ∀ g ∈ C, k * g * k⁻¹ ∈ C := by
    rintro k hk g ⟨hgA, hg⟩
    refine ⟨P.A.mul_mem (P.A.mul_mem hk hgA) (P.A.inv_mem hk), fun u hu => ?_⟩
    have hv : k⁻¹ u ∈ Dp := hDp k⁻¹ (P.A.inv_mem hk) u hu
    set v := k⁻¹ u with hvdef
    have hq : g v * v⁻¹ ∈ Q := hg v hv
    have hku : k v = u := MulAut.apply_inv_self W k u
    have h1 : (k * g * k⁻¹) u = k (g v) := rfl
    have h2 : g v = (g v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    have h3 : k (g v) = (g v * v⁻¹) * u := by
      conv_lhs => rw [h2]
      rw [map_mul, hQfix k hk _ hq, hku]
    rw [h1, h3, mul_assoc, mul_inv_cancel, mul_one]
    exact hq
  have haC : a ∈ C := ⟨ha, fun u hu => haQ (dsp_mem_cmt hu)⟩
  have hCA' : C = P.A := by
    rcases eq_bot_or_eq_of_normal P.simpA hCA hCnorm with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at haC
      exact ha1 haC
    · exact h
  have hall : ∀ g ∈ P.A, ∀ u ∈ Dp, g u * u⁻¹ ∈ Q := fun g hg u hu => by
    have : g ∈ C := by rw [hCA']; exact hg
    exact this.2 u hu
  have hmul : ∀ g ∈ P.A, ∀ h ∈ P.A, ∀ u ∈ Dp,
      (g * h) u * u⁻¹ = (g u * u⁻¹) * (h u * u⁻¹) := by
    intro g hg h hh u hu
    have hq := hall h hh u hu
    set q := h u * u⁻¹ with hqdef
    have hhu : h u = q * u := by rw [hqdef, inv_mul_cancel_right]
    have : (g * h) u = g (q * u) := by
      show g (h u) = _
      rw [hhu]
    rw [this, map_mul, hQfix g hg q hq]
    ac_rfl
  have hone : ∀ u : W, (1 : MulAut W) u * u⁻¹ = 1 := fun u => by
    show u * u⁻¹ = 1
    exact mul_inv_cancel u
  have hinv : ∀ g ∈ P.A, ∀ u ∈ Dp, g⁻¹ u * u⁻¹ = (g u * u⁻¹)⁻¹ := by
    intro g hg u hu
    have := hmul g hg g⁻¹ (P.A.inv_mem hg) u hu
    rw [mul_inv_cancel, hone] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hcomm : ∀ g ∈ P.A, ∀ h ∈ P.A, ⁅g, h⁆ ∈ fixer Dp := by
    intro g hg h hh u hu
    have hc : ⁅g, h⁆ u * u⁻¹ = 1 := by
      rw [commutatorElement_def]
      have e1 : (g * h * g⁻¹ * h⁻¹) u * u⁻¹ =
          (g * h * g⁻¹) u * u⁻¹ * (h⁻¹ u * u⁻¹) :=
        hmul _ (P.A.mul_mem (P.A.mul_mem hg hh) (P.A.inv_mem hg)) _ (P.A.inv_mem hh) u hu
      have e2 : (g * h * g⁻¹) u * u⁻¹ = (g * h) u * u⁻¹ * (g⁻¹ u * u⁻¹) :=
        hmul _ (P.A.mul_mem hg hh) _ (P.A.inv_mem hg) u hu
      rw [e1, e2, hmul g hg h hh u hu, hinv g hg u hu, hinv h hh u hu]
      generalize g u * u⁻¹ = x
      generalize h u * u⁻¹ = y
      calc x * y * x⁻¹ * y⁻¹ = (x * x⁻¹) * (y * y⁻¹) := by ac_rfl
        _ = 1 := by simp
    have : ⁅g, h⁆ u = u := by
      have := congrArg (· * u) hc
      simpa using this
    exact this
  have hle : ⁅P.A, P.A⁆ ≤ fixer Dp := Subgroup.commutator_le.2 hcomm
  rw [P.perfA] at hle
  exact hle ha

omit [Finite W] in
theorem caseII {a a' : MulAut W} (ha2 : a * a = 1) (ha' : a' ∈ P.A')
    (hnot : ¬ ∀ y ∈ cmt a' ⊤, a y = y) :
    ∃ Y : Subgroup W, (∀ g ∈ P.A, ∀ u ∈ Y, g u ∈ Y) ∧ cmt a Y ≠ ⊥ ∧
      cmt a Y ≤ cmt a (cmt (a * a') ⊤) := by
  refine ⟨cmt a' ⊤, ?_, ?_, ?_⟩
  · intro g hg u hu
    exact cmt_invariant (P.comm g hg a' ha') (fun u _ => Subgroup.mem_top _) u hu
  · intro h
    exact hnot (cmt_eq_bot_iff.1 h)
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := mem_cmt.1 hv
    obtain ⟨w, -, rfl⟩ := mem_cmt.1 hy
    refine mem_cmt.2 ⟨dsp (a * a') w, dsp_mem_cmt (Subgroup.mem_top w), ?_⟩
    have := dsp_dsp_eq_of_sq P.hW ha2 (a' := a') w
    simpa [dsp_apply] using this.symm

omit [Finite W] in
theorem caseI_data {a a' : MulAut W} (ha : a ∈ P.A) (ha' : a' ∈ P.A') (ha1 : a ≠ 1)
    (ha'1 : a' ≠ 1) (hI : ∀ y ∈ cmt a' ⊤, a y = y) :
    ∃ D D' : Subgroup W,
      (∀ g ∈ P.A, ∀ u ∈ D', g u ∈ D') ∧ (∀ g ∈ P.A', ∀ u ∈ D, g u ∈ D) ∧
      cmt a' D ≠ ⊥ ∧ cmt a D' ≠ ⊥ ∧ cmt a' D ≤ cmt (a * a') ⊤ ∧ cmt a D' ≤ cmt (a * a') ⊤ ∧
      cmt a' D ≠ cmt a D' := by
  have haa' : a * a' = a' * a := P.comm a ha a' ha'
  have hne' : cmt a' ⊤ ≠ ⊥ := by
    intro h
    apply ha'1
    have := cmt_eq_bot_iff.1 h
    exact MulEquiv.ext fun w => this w (Subgroup.mem_top w)
  have hne : cmt a ⊤ ≠ ⊥ := by
    intro h
    apply ha1
    have := cmt_eq_bot_iff.1 h
    exact MulEquiv.ext fun w => this w (Subgroup.mem_top w)
  have hU1 : ∀ g ∈ P.A, ∀ u ∈ cmt a' ⊤, g u ∈ cmt a' ⊤ := fun g hg u hu =>
    cmt_invariant (P.comm g hg a' ha') (fun u _ => Subgroup.mem_top _) u hu
  have hAtriv := acts_trivially_of_simple P.simpA hU1 ha ha1 hI
  have hle1 : cmt a' ⊤ ≤ fixV P.A := fun u hu => mem_fixV.2 fun g hg => hAtriv g hg u hu
  have hI' : ∀ y ∈ cmt a ⊤, a' y = y := by
    intro y hy
    obtain ⟨w, -, rfl⟩ := mem_cmt.1 hy
    have h1 := dsp_dsp_comm haa' w
    have h2 : dsp a (dsp a' w) = 1 := by
      have := hI _ (dsp_mem_cmt (x := a') (Subgroup.mem_top w))
      rw [dsp_apply a (dsp a' w), dsp_apply a' w, this, mul_inv_cancel]
    rw [h2] at h1
    have h3 : a' (a w * w⁻¹) * (a w * w⁻¹)⁻¹ = 1 := h1.symm
    exact mul_inv_eq_one.1 h3
  have hU2 : ∀ g ∈ P.A', ∀ u ∈ cmt a ⊤, g u ∈ cmt a ⊤ := fun g hg u hu =>
    cmt_invariant (P.comm' hg ha) (fun u _ => Subgroup.mem_top _) u hu
  have hA'triv := acts_trivially_of_simple P.simpA' hU2 ha' ha'1 hI'
  have hle2 : cmt a ⊤ ≤ fixV P.A' := fun u hu => mem_fixV.2 fun g hg => hA'triv g hg u hu
  have hsup : fixV P.A ⊔ fixV P.A' = ⊤ := by
    refine (P.irr _ fun g hg u hu => P.fixSup_inv hg hu).resolve_left ?_
    intro h
    apply hne'
    exact eq_bot_iff.2 (hle1.trans (le_sup_left.trans h.le))
  have hDinv' : ∀ u ∈ fixV P.A, a' u ∈ fixV P.A := fun u hu => P.fixA_inv ha' hu
  have hD'inv : ∀ u ∈ fixV P.A', a u ∈ fixV P.A' := fun u hu => P.fixA'_inv ha hu
  have haD : ∀ u ∈ fixV P.A, a u = u := fun u hu => mem_fixV.1 hu a ha
  have ha'D' : ∀ u ∈ fixV P.A', a' u = u := fun u hu => mem_fixV.1 hu a' ha'
  have hPne : cmt a' (fixV P.A) ≠ ⊥ := by
    intro h
    have h1 := cmt_eq_bot_iff.1 h
    apply ha'1
    have hle : fixV P.A ⊔ fixV P.A' ≤ fixV (Subgroup.zpowers a') := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [CFSG.QuasithinUnique.Setup.X1.mem_fixV_zpowers]
        exact h1 u hu
      · rw [CFSG.QuasithinUnique.Setup.X1.mem_fixV_zpowers]
        exact ha'D' u hu
    rw [hsup] at hle
    refine MulEquiv.ext fun w => ?_
    exact (CFSG.QuasithinUnique.Setup.X1.mem_fixV_zpowers).1 (hle (Subgroup.mem_top w))
  have hQne : cmt a (fixV P.A') ≠ ⊥ := by
    intro h
    have h1 := cmt_eq_bot_iff.1 h
    apply ha1
    have hle : fixV P.A ⊔ fixV P.A' ≤ fixV (Subgroup.zpowers a) := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [CFSG.QuasithinUnique.Setup.X1.mem_fixV_zpowers]
        exact haD u hu
      · rw [CFSG.QuasithinUnique.Setup.X1.mem_fixV_zpowers]
        exact h1 u hu
    rw [hsup] at hle
    refine MulEquiv.ext fun w => ?_
    exact (CFSG.QuasithinUnique.Setup.X1.mem_fixV_zpowers).1 (hle (Subgroup.mem_top w))
  refine ⟨fixV P.A, fixV P.A', fun g hg u hu => P.fixA'_inv hg hu,
    fun g hg u hu => P.fixA_inv hg hu, hPne, hQne, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_cmt.1 hv
    refine mem_cmt.2 ⟨d, Subgroup.mem_top d, ?_⟩
    show (a * a') d * d⁻¹ = a' d * d⁻¹
    rw [MulAut.mul_apply, haD _ (hDinv' d hd)]
  · intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_cmt.1 hv
    refine mem_cmt.2 ⟨d, Subgroup.mem_top d, ?_⟩
    show (a * a') d * d⁻¹ = a d * d⁻¹
    rw [MulAut.mul_apply, ha'D' d hd]
  · intro h
    have hle : cmt a' (fixV P.A) ≤ fixV P.A :=
      cmt_le_of_invariant hDinv'
    have hQfix : ∀ g ∈ P.A, ∀ q ∈ cmt a (fixV P.A'), g q = q := by
      intro g hg q hq
      rw [← h] at hq
      exact mem_fixV.1 (hle hq) g hg
    have := acts_trivially_of_unipotent P ha ha1 (fun g hg u hu => P.fixA'_inv hg hu) hQfix le_rfl
    exact hQne (cmt_eq_bot_iff.2 this)

omit [Finite W] in
theorem card_cmt_lt_of_card_le_two [Finite W] (hW : ∀ w : W, w * w = 1) {x : MulAut W} (hx : x * x = 1)
    {U : Subgroup W} (hU : ∀ u ∈ U, x u ∈ U) (hcard : Nat.card U ≤ 2) :
    Nat.card (cmt x U) ≤ 1 := by
  by_cases hne : U = ⊥
  · have : cmt x U = ⊥ := by rw [hne]; exact Subgroup.map_bot _
    rw [this]
    simp
  have hlt := cmt_lt_of_sq_eq_one hW hx hU hne
  have hsub : Nat.card (cmt x U) < Nat.card U := Subgroup.card_lt_of_lt hlt
  omega

theorem pair_core_le_four {a a' : MulAut W} (ha : a ∈ P.A) (ha' : a' ∈ P.A') (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (ha'1 : a' ≠ 1) (hz : Nat.card (cmt (a * a') ⊤) ≤ 4) :
    (∃ U : Subgroup W, (∀ g ∈ P.A, ∀ u ∈ U, g u ∈ U) ∧ Nat.card (cmt a U) = 2) ∨
      (∃ U : Subgroup W, (∀ g ∈ P.A', ∀ u ∈ U, g u ∈ U) ∧ Nat.card (cmt a' U) = 2) := by
  by_cases hI : ∀ y ∈ cmt a' ⊤, a y = y
  · obtain ⟨D, D', hD'inv, hDinv, hPne, hQne, hPR, hQR, hPQ⟩ := P.caseI_data ha ha' ha1 ha'1 hI
    by_cases hQ2 : Nat.card (cmt a D') = 2
    · exact Or.inl ⟨D', hD'inv, hQ2⟩
    by_cases hP2 : Nat.card (cmt a' D) = 2
    · exact Or.inr ⟨D, hDinv, hP2⟩
    exact absurd ((eq_of_le_of_card_ne_two hPR hPne hP2 hz).trans
      (eq_of_le_of_card_ne_two hQR hQne hQ2 hz).symm) hPQ
  · obtain ⟨Y, hYinv, hYne, hYle⟩ := P.caseII ha2 ha' hI
    refine Or.inl ⟨Y, hYinv, ?_⟩
    have hcomm : a * (a * a') = (a * a') * a := by
      rw [mul_assoc, ← P.comm a ha a' ha']
    have hRinv : ∀ u ∈ cmt (a * a') ⊤, a u ∈ cmt (a * a') ⊤ :=
      cmt_invariant hcomm (fun u _ => Subgroup.mem_top _)
    have h2 := card_cmt_le_two_of_card_le_four P.hW ha2 hRinv hz
    have h3 : Nat.card (cmt a Y) ≤ 2 := (Subgroup.card_le_of_le hYle).trans h2
    have hgt : 1 < Nat.card (cmt a Y) := (Subgroup.one_lt_card_iff_ne_bot _).2 hYne
    omega

theorem pair_core_le_two {a a' : MulAut W} (ha : a ∈ P.A) (ha' : a' ∈ P.A') (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (ha'1 : a' ≠ 1) (hz : Nat.card (cmt (a * a') ⊤) ≤ 2) : False := by
  by_cases hI : ∀ y ∈ cmt a' ⊤, a y = y
  · obtain ⟨D, D', -, -, hPne, hQne, hPR, hQR, hPQ⟩ := P.caseI_data ha ha' ha1 ha'1 hI
    exact hPQ ((eq_of_le_of_card_le_two hPR hPne hz).trans
      (eq_of_le_of_card_le_two hQR hQne hz).symm)
  · obtain ⟨Y, hYinv, hYne, hYle⟩ := P.caseII ha2 ha' hI
    have hcomm : a * (a * a') = (a * a') * a := by
      rw [mul_assoc, ← P.comm a ha a' ha']
    have hRinv : ∀ u ∈ cmt (a * a') ⊤, a u ∈ cmt (a * a') ⊤ :=
      cmt_invariant hcomm (fun u _ => Subgroup.mem_top _)
    have h2 := card_cmt_lt_of_card_le_two P.hW ha2 hRinv hz
    have h3 : Nat.card (cmt a Y) ≤ 1 := (Subgroup.card_le_of_le hYle).trans h2
    have hgt : 1 < Nat.card (cmt a Y) := (Subgroup.one_lt_card_iff_ne_bot _).2 hYne
    omega

end Core

end PairData

end CFSG.Quasithin.He6
