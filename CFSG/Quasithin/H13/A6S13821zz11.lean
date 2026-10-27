module

public import CFSG.Quasithin.EmptyFaithful.S1565H
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section QSeries

variable {W : Type} [CommGroup W] [Finite W]

theorem fixV_ne_bot_of_two_group (hW2 : ∀ w : W, w ^ 2 = 1) [Nontrivial W]
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 ↥P) : fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints ↥P W) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 W := fun v => ⟨1, by rw [pow_one]; exact hW2 v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card W % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

theorem exists_fixMod_of_lt (hW2 : ∀ w : W, w ^ 2 = 1) {Q : Subgroup (MulAut W)}
    (hQ : IsPGroup 2 ↥Q) {E : Subgroup W} (hQE : Q ≤ CFSG.Quasithin.stabSub E) (hE : E ≠ ⊤) :
    ∃ w : W, w ∉ E ∧ ∀ q ∈ Q, q w * w⁻¹ ∈ E := by
  classical
  set ψ : ↥Q →* MulAut (W ⧸ E) :=
    (CFSG.Quasithin.quotHom E).comp (Subgroup.inclusion hQE) with hψ
  have hnt : Nontrivial (W ⧸ E) := by
    obtain ⟨w, hw⟩ : ∃ w : W, w ∉ E := by
      by_contra h
      push Not at h
      exact hE (eq_top_iff.mpr fun w _ => h w)
    refine ⟨⟨QuotientGroup.mk w, 1, fun h => hw ?_⟩⟩
    rwa [QuotientGroup.eq_one_iff] at h
  have hW2' : ∀ z : W ⧸ E, z ^ 2 = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow, hW2, QuotientGroup.mk_one]
  have hP : IsPGroup 2 ↥ψ.range := hQ.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hfix := fixV_ne_bot_of_two_group hW2' hP
  obtain ⟨z, hzfix, hz1⟩ : ∃ z, z ∈ fixV ψ.range ∧ z ≠ 1 := by
    by_contra h
    push Not at h
    exact hfix (eq_bot_iff.mpr fun z hz => (Subgroup.mem_bot).mpr (h z hz))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨w, fun hw => hz1 ((QuotientGroup.eq_one_iff w).mpr hw), fun q hq => ?_⟩
  have h1 : ψ ⟨q, hq⟩ (QuotientGroup.mk w) = QuotientGroup.mk w := hzfix _ ⟨⟨q, hq⟩, rfl⟩
  have h2 : (QuotientGroup.mk (q w) : W ⧸ E) = QuotientGroup.mk w := h1
  exact (CFSG.Quasithin.mk_eq_mk_iff _ _).mp h2

@[expose] def qSeries (Q : Subgroup (MulAut W)) : ℕ → Subgroup W
  | 0 => ⊥
  | k + 1 => S1565.fixModSub (MonoidHom.id (MulAut W)) Q (qSeries Q k)

omit [Finite W] in
theorem mem_qSeries_succ {Q : Subgroup (MulAut W)} {k : ℕ} {w : W} :
    w ∈ qSeries Q (k + 1) ↔ ∀ q ∈ Q, q w * w⁻¹ ∈ qSeries Q k := Iff.rfl

omit [Finite W] in
theorem qSeries_one (Q : Subgroup (MulAut W)) : qSeries Q 1 = fixV Q := by
  ext w
  rw [mem_qSeries_succ, mem_fixV]
  refine forall₂_congr fun q _ => ?_
  show q w * w⁻¹ ∈ (⊥ : Subgroup W) ↔ q w = w
  rw [Subgroup.mem_bot, mul_inv_eq_one]

omit [Finite W] in
theorem qSeries_mono (Q : Subgroup (MulAut W)) : ∀ k, qSeries Q k ≤ qSeries Q (k + 1)
  | 0 => bot_le
  | k + 1 => fun _ hw => mem_qSeries_succ.mpr fun q hq =>
      qSeries_mono Q k ((mem_qSeries_succ.mp hw) q hq)

omit [Finite W] in
theorem qSeries_le_stabSub {Q : Subgroup (MulAut W)} :
    ∀ k, Q ≤ CFSG.Quasithin.stabSub (qSeries Q k)
  | 0 => fun q _ u => by
      show q u ∈ (⊥ : Subgroup W) ↔ u ∈ (⊥ : Subgroup W)
      rw [Subgroup.mem_bot, Subgroup.mem_bot, map_eq_one_iff _ q.injective]
  | k + 1 => by
    have IH := qSeries_le_stabSub (Q := Q) k
    have hfw : ∀ q' ∈ Q, ∀ w : W, w ∈ qSeries Q (k + 1) → q' w ∈ qSeries Q (k + 1) := by
      intro q' hq' w hw
      refine mem_qSeries_succ.mpr fun q hq => ?_
      have h1 := (mem_qSeries_succ.mp hw) (q'⁻¹ * q * q') (Q.mul_mem (Q.mul_mem (Q.inv_mem hq')
        hq) hq')
      have h2 := (IH hq' _).mpr h1
      have e : q' ((q'⁻¹ * q * q') w * w⁻¹) = q (q' w) * (q' w)⁻¹ := by
        rw [map_mul, map_inv]
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      rwa [e] at h2
    intro q' hq' u
    constructor
    · intro hu
      have := hfw q'⁻¹ (Q.inv_mem hq') _ hu
      rwa [MulAut.inv_apply_self] at this
    · exact hfw q' hq' u

omit [Finite W] in
theorem invSub_qSeries {X : Type} [Group X] (φ : X →* MulAut W) {Q : Subgroup (MulAut W)}
    (hQX : ∀ q ∈ Q, ∀ x : X, q * φ x = φ x * q) : ∀ k, S1565.InvSub φ (qSeries Q k)
  | 0 => fun x a ha => by
      have ha' : a = 1 := ha
      show (φ x) a ∈ (⊥ : Subgroup W)
      rw [ha', map_one]
      exact Subgroup.one_mem _
  | k + 1 => fun x w hw => mem_qSeries_succ.mpr fun q hq => by
      have h1 := invSub_qSeries φ hQX k x _ ((mem_qSeries_succ.mp hw) q hq)
      have e : (φ x) (q w * w⁻¹) = q ((φ x) w) * ((φ x) w)⁻¹ := by
        rw [map_mul, map_inv, ← MulAut.mul_apply, ← hQX q hq x, MulAut.mul_apply]
      rwa [e] at h1

omit [Finite W] in
theorem fixProp_qSeries_succ {X : Type} [Group X] (φ : X →* MulAut W)
    {Q : Subgroup (MulAut W)} (hQX : ∀ q ∈ Q, ∀ x : X, q * φ x = φ x * q) (B : Subgroup X)
    {k : ℕ} (h : S1565.FixProp φ B (qSeries Q k) (qSeries Q (k + 1))) :
    S1565.FixProp φ B (qSeries Q (k + 1)) (qSeries Q (k + 2)) := by
  have key : ∀ q ∈ Q, ∀ (x : X) (w : W), q ((φ x) w * w⁻¹) * ((φ x) w * w⁻¹)⁻¹ =
      (φ x) (q w * w⁻¹) * (q w * w⁻¹)⁻¹ := by
    intro q hq x w
    have e : q ((φ x) w) = (φ x) (q w) := by
      rw [← MulAut.mul_apply, hQX q hq x, MulAut.mul_apply]
    simp only [map_mul, map_inv, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  intro w hw hwB x _ q hq
  have hu : q w * w⁻¹ ∈ qSeries Q (k + 1) := (mem_qSeries_succ.mp hw) q hq
  have huB : S1565.FixMod φ B (qSeries Q k) (q w * w⁻¹) := by
    intro b hb
    rw [← key q hq b w]
    exact (mem_qSeries_succ.mp (hwB b hb)) q hq
  have h1 := h _ hu huB x (Subgroup.mem_top x)
  show q ((φ x) w * w⁻¹) * ((φ x) w * w⁻¹)⁻¹ ∈ qSeries Q k
  rw [key q hq x w]
  exact h1

theorem fixProp_top_of_fixV {X : Type} [Group X] [Finite X] (φ : X →* MulAut W)
    (hW2 : ∀ w : W, w ^ 2 = 1) (B : Subgroup X) (hB : Odd B.index) {Q : Subgroup (MulAut W)}
    (hQ : IsPGroup 2 ↥Q) (hQX : ∀ q ∈ Q, ∀ x : X, q * φ x = φ x * q)
    (h0 : S1565.FixProp φ B ⊥ (fixV Q)) : S1565.FixProp φ B ⊥ ⊤ := by
  classical
  have hbot : S1565.InvSub φ (⊥ : Subgroup W) := invSub_qSeries φ hQX 0
  have hstep : ∀ k, S1565.FixProp φ B (qSeries Q k) (qSeries Q (k + 1)) := by
    intro k
    induction k with
    | zero =>
      rw [qSeries_one]
      exact h0
    | succ k ih => exact fixProp_qSeries_succ φ hQX B ih
  have hall : ∀ k, S1565.FixProp φ B ⊥ (qSeries Q k) := by
    intro k
    induction k with
    | zero =>
      intro w hw _ x _
      have hw' : w = 1 := hw
      rw [hw', map_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    | succ k ih => exact S1565.fixProp_compose φ hW2 B hB hbot bot_le ih (hstep k)
  have hgrow : ∀ k, qSeries Q k = ⊤ ∨ k + 1 ≤ Nat.card ↥(qSeries Q k) := by
    intro k
    induction k with
    | zero =>
      refine Or.inr ?_
      show 0 + 1 ≤ Nat.card ↥(⊥ : Subgroup W)
      rw [Subgroup.card_bot]
    | succ k ih =>
      by_cases htop : qSeries Q (k + 1) = ⊤
      · exact Or.inl htop
      · refine Or.inr ?_
        have hk : qSeries Q k ≠ ⊤ := fun h => htop (eq_top_iff.mpr (h ▸ qSeries_mono Q k))
        obtain ⟨w, hwE, hwQ⟩ := exists_fixMod_of_lt hW2 hQ (qSeries_le_stabSub k) hk
        have hlt : qSeries Q k < qSeries Q (k + 1) := by
          refine lt_of_le_of_ne (qSeries_mono Q k) fun h => hwE ?_
          rw [h]
          exact mem_qSeries_succ.mpr hwQ
        have hc := Subgroup.card_lt_of_lt hlt
        rcases ih with h | h
        · exact absurd h hk
        · omega
  rcases hgrow (Nat.card W) with h | h
  · rw [← h]
    exact hall _
  · exfalso
    have := Subgroup.card_le_card_group (qSeries Q (Nat.card W))
    omega

end QSeries

end CFSG.Quasithin.H13.A6.A6S20
