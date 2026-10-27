module

public import CFSG.Timmesfeld.Transvection.ShortRootPair
public import CFSG.Timmesfeld.Transvection.ShortRootCommSL2
public import CFSG.Timmesfeld.Transvection.ShortRootCommLocal
public import CFSG.Timmesfeld.Transvection.ShortRootCommAlign

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace SL2Coords

variable {A E : Subgroup G} {k : ℕ} (φ : SL2Coords A E k)

theorem elt_diagElt (c : (GaloisField 2 k)ˣ) : φ.elt (diagElt c) = φ.torusElt c :=
  φ.mat_injOn (φ.elt_mem _) (φ.torusElt_mem c) (by rw [mat_elt, mat_torusElt])

@[expose] noncomputable def smulG (c : GaloisField 2 k) (x : G) : G :=
  haveI := Classical.dec (c = 0)
  if h : c = 0 then 1 else φ.torusElt (Units.mk0 c h) * x * (φ.torusElt (Units.mk0 c h))⁻¹

@[simp] theorem smulG_zero (x : G) : φ.smulG 0 x = 1 := by
  simp [smulG]

theorem smulG_of_ne {c : GaloisField 2 k} (hc : c ≠ 0) (x : G) :
    φ.smulG c x = φ.torusElt (Units.mk0 c hc) * x * (φ.torusElt (Units.mk0 c hc))⁻¹ := by
  simp [smulG, hc]

theorem smulG_units (c : (GaloisField 2 k)ˣ) (x : G) :
    φ.smulG c x = φ.torusElt c * x * (φ.torusElt c)⁻¹ := by
  rw [φ.smulG_of_ne c.ne_zero, Units.mk0_val]

@[simp] theorem smulG_one (x : G) : φ.smulG 1 x = x := by
  rw [← Units.val_one, smulG_units, torusElt_one]
  group

@[simp] theorem smulG_one_right (c : GaloisField 2 k) : φ.smulG c 1 = 1 := by
  by_cases hc : c = 0
  · rw [hc, smulG_zero]
  · rw [smulG_of_ne φ hc]
    group

theorem smulG_mul (c c' : GaloisField 2 k) (x : G) :
    φ.smulG (c * c') x = φ.smulG c (φ.smulG c' x) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hc' : c' = 0
  · simp [hc']
  rw [smulG_of_ne φ (mul_ne_zero hc hc'), smulG_of_ne φ hc, smulG_of_ne φ hc',
    show Units.mk0 (c * c') (mul_ne_zero hc hc') = Units.mk0 c hc * Units.mk0 c' hc' from
      Units.ext rfl, torusElt_mul]
  group

@[expose] noncomputable def lowerCoord (x : G) : GaloisField 2 k :=
  (φ.mat x : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)) 1 0

@[simp] theorem lowerCoord_elt_lowerElt (s : GaloisField 2 k) :
    φ.lowerCoord (φ.elt (lowerElt _ s)) = s := by
  simp [lowerCoord, coe_lowerElt]

theorem elt_lowerElt_lowerCoord {a : G} (ha : a ∈ A) : φ.elt (lowerElt _ (φ.lowerCoord a)) = a := by
  obtain ⟨s, rfl⟩ := φ.exists_eq_elt_lowerElt ha
  rw [lowerCoord_elt_lowerElt]

theorem lowerCoord_mul {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A) :
    φ.lowerCoord (a * a') = φ.lowerCoord a + φ.lowerCoord a' := by
  obtain ⟨s, rfl⟩ := φ.exists_eq_elt_lowerElt ha
  obtain ⟨s', rfl⟩ := φ.exists_eq_elt_lowerElt ha'
  rw [← elt_lowerElt_add, lowerCoord_elt_lowerElt, lowerCoord_elt_lowerElt,
    lowerCoord_elt_lowerElt]

theorem eq_one_of_lowerCoord_eq_zero {a : G} (ha : a ∈ A) (h0 : φ.lowerCoord a = 0) : a = 1 := by
  rw [← φ.elt_lowerElt_lowerCoord ha, h0, lowerElt_zero, elt_one]

theorem lowerCoord_torusElt_conj (c : (GaloisField 2 k)ˣ) {a : G} (ha : a ∈ A) :
    φ.lowerCoord (φ.torusElt c * a * (φ.torusElt c)⁻¹) =
      ((c⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) ^ 2 * φ.lowerCoord a := by
  conv_lhs => rw [← φ.elt_lowerElt_lowerCoord ha, ← elt_diagElt, elt_diagElt_conj_lowerElt]
  rw [lowerCoord_elt_lowerElt]

@[expose] noncomputable def quadPart (x : G) (s : GaloisField 2 k) : G :=
  (φ.elt (weylElt _) * φ.smulG s x * (φ.elt (weylElt _))⁻¹)⁻¹ * ⁅x, φ.elt (lowerElt _ s)⁆

theorem commutator_eq_mul_quadPart (x : G) (s : GaloisField 2 k) :
    ⁅x, φ.elt (lowerElt _ s)⁆ =
      φ.elt (weylElt _) * φ.smulG s x * (φ.elt (weylElt _))⁻¹ * φ.quadPart x s := by
  rw [quadPart]
  group

theorem quadPart_eq_of_commutator_eq {y d : G} {s : GaloisField 2 k}
    (h : ⁅y, φ.elt (lowerElt _ s)⁆ =
      φ.elt (weylElt _) * φ.smulG s y * (φ.elt (weylElt _))⁻¹ * d) : φ.quadPart y s = d := by
  rw [quadPart, h, inv_mul_cancel_left]

theorem quadPart_conj {g : G} (hg : ∀ y ∈ A ⊔ E, Commute g y) (x : G) (s : GaloisField 2 k) :
    φ.quadPart (g * x * g⁻¹) s = g * φ.quadPart x s * g⁻¹ := by
  have hw := hg _ (φ.elt_mem (weylElt _))
  have hp := hg _ (φ.elt_mem (lowerElt _ s))
  have hsm : φ.smulG s (g * x * g⁻¹) = g * φ.smulG s x * g⁻¹ := by
    by_cases hs : s = 0
    · simp [hs]
    · have ht := hg _ (φ.torusElt_mem (Units.mk0 s hs))
      rw [φ.smulG_of_ne hs, φ.smulG_of_ne hs]
      calc φ.torusElt (Units.mk0 s hs) * (g * x * g⁻¹) * (φ.torusElt (Units.mk0 s hs))⁻¹ =
            (φ.torusElt (Units.mk0 s hs) * g) * x * (φ.torusElt (Units.mk0 s hs) * g)⁻¹ := by
            group
        _ = (g * φ.torusElt (Units.mk0 s hs)) * x * (g * φ.torusElt (Units.mk0 s hs))⁻¹ := by
            rw [ht.eq]
        _ = g * (φ.torusElt (Units.mk0 s hs) * x * (φ.torusElt (Units.mk0 s hs))⁻¹) * g⁻¹ := by
            group
  refine φ.quadPart_eq_of_commutator_eq ?_
  have hpg : g * φ.elt (lowerElt _ s) * g⁻¹ = φ.elt (lowerElt _ s) := by
    rw [hp.eq, mul_inv_cancel_right]
  have hwg : g * φ.elt (weylElt _) * g⁻¹ = φ.elt (weylElt _) := by
    rw [hw.eq, mul_inv_cancel_right]
  calc ⁅g * x * g⁻¹, φ.elt (lowerElt _ s)⁆ =
        ⁅g * x * g⁻¹, g * φ.elt (lowerElt _ s) * g⁻¹⁆ := by rw [hpg]
    _ = g * ⁅x, φ.elt (lowerElt _ s)⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = g * (φ.elt (weylElt _) * φ.smulG s x * (φ.elt (weylElt _))⁻¹ * φ.quadPart x s) * g⁻¹ := by
        rw [commutator_eq_mul_quadPart]
    _ = (g * φ.elt (weylElt _) * g⁻¹) * (g * φ.smulG s x * g⁻¹) *
          (g * φ.elt (weylElt _) * g⁻¹)⁻¹ * (g * φ.quadPart x s * g⁻¹) := by group
    _ = _ := by rw [hwg, hsm]

theorem torusElt_inv_conj_lowerElt (c : (GaloisField 2 k)ˣ) (s : GaloisField 2 k) :
    (φ.torusElt c)⁻¹ * φ.elt (lowerElt _ s) * φ.torusElt c =
      φ.elt (lowerElt _ ((c : GaloisField 2 k) * c * s)) := by
  have h := φ.elt_diagElt_conj_lowerElt c⁻¹ s
  rw [elt_diagElt, inv_inv, torusElt_inv, inv_inv] at h
  rw [h, pow_two]

theorem torusElt_mul_elt_weylElt (c : (GaloisField 2 k)ˣ) :
    φ.torusElt c * φ.elt (weylElt _) = φ.elt (weylElt _) * φ.torusElt c⁻¹ := by
  have h := φ.elt_weylElt_conj_diagElt c⁻¹
  rw [elt_diagElt, elt_diagElt, inv_inv] at h
  rw [← h]
  group

end SL2Coords

@[expose] noncomputable def SL2Coords.quadCoord {A E D E' : Subgroup G} {k : ℕ}
    (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k) (x : G) (s : GaloisField 2 k) :
    GaloisField 2 k :=
  φ₁.lowerCoord (φ₀.quadPart x s)

namespace PairFrame

variable {A E D E' : Subgroup G} (F : PairFrame Δ A E D E')
include F

theorem A_le_lineGroup : A ≤ lineGroup Δ A D := le_lineGroup (left_mem_lineOf F.memA)

theorem D_le_lineGroup : D ≤ lineGroup Δ A D := le_lineGroup (right_mem_lineOf F.memD)

theorem commute_of_mem_lineGroup_AD (hΔ : IsTransvectionClass Δ) {x y : G}
    (hx : x ∈ lineGroup Δ A D) (hy : y ∈ lineGroup Δ A D) : Commute x y :=
  commute_of_mem_lineGroup hΔ F.memA F.memD F.commuting_AD hx hy

variable [Finite G] (hΔ : IsTransvectionClass Δ) {k : ℕ} (φ₀ : SL2Coords A E k)
include hΔ

theorem conjSub_shortRootGroup_elt_weylElt :
    conjSub (shortRootGroup Δ E A D E') (φ₀.elt (weylElt _)) = shortRootGroup Δ A E D E' := by
  have hc : Nat.card E = Nat.card A := hΔ.root.card_eq F.memE F.memA
  have hw := φ₀.elt_mem (weylElt _)
  have hD : conjSub D (φ₀.elt (weylElt _)) = D :=
    conjSub_of_forall_commute fun d hd => F.comm _ hw d (Subgroup.mem_sup_left hd)
  have hE' : conjSub E' (φ₀.elt (weylElt _)) = E' :=
    conjSub_of_forall_commute fun d hd => F.comm _ hw d (Subgroup.mem_sup_right hd)
  rw [← shortRootGroup_conjSub hΔ.root, φ₀.conjSub_E_elt_weylElt hc,
    φ₀.conjSub_A_elt_weylElt hc, hD, hE']

theorem conj_elt_weylElt_mem {x : G} (hx : x ∈ shortRootGroup Δ E A D E') :
    φ₀.elt (weylElt _) * x * (φ₀.elt (weylElt _))⁻¹ ∈ shortRootGroup Δ A E D E' := by
  have h := conj_mem_conjSub (φ₀.elt (weylElt _)) hx
  rwa [F.conjSub_shortRootGroup_elt_weylElt hΔ φ₀] at h

theorem smulG_mem {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (c : GaloisField 2 k) :
    φ₀.smulG c x ∈ shortRootGroup Δ E A D E' := by
  by_cases hc : c = 0
  · rw [hc, SL2Coords.smulG_zero]
    exact Subgroup.one_mem _
  · rw [φ₀.smulG_of_ne hc]
    exact F.conj_torusElt_mem φ₀ hΔ.root hx _

variable (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A) (hX : ShortRootFieldHyp Δ A E D E')
include hpts hq hX

theorem smulG_add {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (c c' : GaloisField 2 k) :
    φ₀.smulG (c + c') x = φ₀.smulG c x * φ₀.smulG c' x := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hc' : c' = 0
  · simp [hc']
  by_cases hcc : c + c' = 0
  · have hcc' : c' = c := by
      rw [← CharTwo.neg_eq c]
      exact (neg_eq_of_add_eq_zero_right hcc).symm
    rw [hcc, hcc', SL2Coords.smulG_zero]
    exact (F.mul_self_of_mem_shortRootGroup hΔ (F.smulG_mem hΔ φ₀ hx c)).symm
  rw [φ₀.smulG_of_ne hcc, φ₀.smulG_of_ne hc, φ₀.smulG_of_ne hc']
  have h := F.torusElt_add_conj φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX (Units.mk0 c hc)
    (Units.mk0 c' hc') hcc hx
  exact h

theorem quadPart_mem {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (s : GaloisField 2 k) :
    φ₀.quadPart x s ∈ D := by
  by_cases hx1 : x = 1
  · subst hx1
    simp [SL2Coords.quadPart]
  have hiso := F.noIsolated hΔ.root
  obtain ⟨t, S, htY, hxN⟩ := F.exists_setting hΔ hiso hpts hX hx hx1
  obtain ⟨hC, hCA, hCD, -⟩ := hX.1 x hx hx1
  have hD : D ∈ lineOf Δ A (conjSub A x) := (F.toSp4Frame hC hCA hCD).mem_lineOf hΔ hpts
  let c := S.coordsOf htY hq φ₀
  have hy : φ₀.smulG s x ∈ corrN A E t := by
    by_cases hs : s = 0
    · rw [hs, SL2Coords.smulG_zero]
      exact Subgroup.one_mem _
    · rw [φ₀.smulG_of_ne hs]
      exact conj_mem_corrN (φ₀.torusElt_mem _) hxN.1
  have hyv : S.vecOf htY hq φ₀ (φ₀.smulG s x) = ![s * S.vecOf htY hq φ₀ x 0, 0] := by
    by_cases hs : s = 0
    · rw [hs, SL2Coords.smulG_zero, zero_mul]
      have h1 := ((S.vecOf_spec htY hq φ₀).2.2.1 (Subgroup.one_mem (corrN A E t))).2
        (Subgroup.one_mem _)
      rw [h1]
      ext i
      fin_cases i <;> rfl
    · rw [φ₀.smulG_of_ne hs]
      exact (S.vecOf_torusElt htY φ₀ hq hxN (Units.mk0 s hs)).trans (by rw [Units.val_mk0])
  obtain ⟨d, hd, hcomm⟩ := S.commutator_eq_conj_mul htY hq hpts hD F.commuting_ED.symm c
    (φ₀.elt_mem _) (φ₀.mat_elt _) hxN.1 (φ₀.elt_lowerElt_mem s) (φ₀.mat_elt _) hy hyv
  have hcomm' : ⁅x, φ₀.elt (lowerElt _ s)⁆ =
      φ₀.elt (weylElt _) * φ₀.smulG s x * (φ₀.elt (weylElt _))⁻¹ * d := hcomm
  rw [SL2Coords.quadPart, hcomm', inv_mul_cancel_left]
  exact hd

theorem commutator_mem_lineGroup {x : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (s : GaloisField 2 k) : ⁅x, φ₀.elt (lowerElt _ s)⁆ ∈ lineGroup Δ A D := by
  rw [φ₀.commutator_eq_mul_quadPart]
  have hXU : shortRootGroup Δ A E D E' ≤ lineGroup Δ A D := inf_le_left.trans inf_le_left
  exact Subgroup.mul_mem _ (hXU (F.conj_elt_weylElt_mem hΔ φ₀ (F.smulG_mem hΔ φ₀ hx s)))
    (F.D_le_lineGroup (F.quadPart_mem hΔ φ₀ hpts hq hX hx s))

theorem quadPart_add {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (s s' : GaloisField 2 k) :
    φ₀.quadPart x (s + s') = φ₀.quadPart x s * φ₀.quadPart x s' := by
  refine φ₀.quadPart_eq_of_commutator_eq ?_
  have hA : φ₀.elt (lowerElt _ s) ∈ lineGroup Δ A D := F.A_le_lineGroup (φ₀.elt_lowerElt_mem s)
  have hc := F.commute_of_mem_lineGroup_AD hΔ hA (F.commutator_mem_lineGroup hΔ φ₀ hpts hq hX hx s')
  have hXU : shortRootGroup Δ A E D E' ≤ lineGroup Δ A D := inf_le_left.trans inf_le_left
  have hu : φ₀.elt (weylElt _) * φ₀.smulG s' x * (φ₀.elt (weylElt _))⁻¹ ∈ lineGroup Δ A D :=
    hXU (F.conj_elt_weylElt_mem hΔ φ₀ (F.smulG_mem hΔ φ₀ hx s'))
  have hd : φ₀.quadPart x s ∈ lineGroup Δ A D :=
    F.D_le_lineGroup (F.quadPart_mem hΔ φ₀ hpts hq hX hx s)
  have hc' := F.commute_of_mem_lineGroup_AD hΔ hd hu
  have hmr : ∀ a b c : G, ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := fun a b c => by
    simp only [commutatorElement_def]
    group
  rw [φ₀.elt_lowerElt_add, hmr, hc.eq, mul_inv_cancel_right,
    φ₀.commutator_eq_mul_quadPart, φ₀.commutator_eq_mul_quadPart, F.smulG_add hΔ φ₀ hpts hq hX hx]
  calc φ₀.elt (weylElt _) * φ₀.smulG s x * (φ₀.elt (weylElt _))⁻¹ * φ₀.quadPart x s *
        (φ₀.elt (weylElt _) * φ₀.smulG s' x * (φ₀.elt (weylElt _))⁻¹ * φ₀.quadPart x s') =
        φ₀.elt (weylElt _) * φ₀.smulG s x * (φ₀.elt (weylElt _))⁻¹ * (φ₀.quadPart x s *
          (φ₀.elt (weylElt _) * φ₀.smulG s' x * (φ₀.elt (weylElt _))⁻¹)) * φ₀.quadPart x s' := by
        group
    _ = _ := by
        rw [hc'.eq]
        group

theorem quadPart_smulG {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (μ : (GaloisField 2 k)ˣ)
    (s : GaloisField 2 k) :
    φ₀.quadPart (φ₀.smulG μ x) s = φ₀.quadPart x (μ * μ * s) := by
  refine φ₀.quadPart_eq_of_commutator_eq ?_
  set h := φ₀.torusElt μ with hh
  set w := φ₀.elt (weylElt _) with hw
  have hd := F.quadPart_mem hΔ φ₀ hpts hq hX hx (μ * μ * s)
  have hhd : Commute h (φ₀.quadPart x (μ * μ * s)) :=
    F.comm _ (φ₀.torusElt_mem μ) _ (Subgroup.mem_sup_left hd)
  have hsc : ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * (μ * μ * s) = s * μ := by
    rw [show ((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * (μ * μ * s) =
      (((μ⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * μ) * (μ * s) by ring, Units.inv_mul,
      one_mul, mul_comm]
  have h3 : φ₀.smulG s (φ₀.smulG μ x) =
      φ₀.torusElt μ⁻¹ * φ₀.smulG (μ * μ * s) x * (φ₀.torusElt μ⁻¹)⁻¹ := by
    rw [← φ₀.smulG_mul, ← φ₀.smulG_units, ← φ₀.smulG_mul, hsc]
  rw [h3, φ₀.smulG_units μ x]
  calc ⁅h * x * h⁻¹, φ₀.elt (lowerElt _ s)⁆ = h * ⁅x, h⁻¹ * φ₀.elt (lowerElt _ s) * h⁆ * h⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = h * (w * φ₀.smulG (μ * μ * s) x * w⁻¹ * φ₀.quadPart x (μ * μ * s)) * h⁻¹ := by
        rw [hh, φ₀.torusElt_inv_conj_lowerElt, φ₀.commutator_eq_mul_quadPart]
    _ = (h * w) * φ₀.smulG (μ * μ * s) x * (h * w)⁻¹ *
          (h * φ₀.quadPart x (μ * μ * s) * h⁻¹) := by group
    _ = _ := by
        rw [hh, hw, φ₀.torusElt_mul_elt_weylElt, ← hh, hhd.eq, mul_inv_cancel_right]
        group

omit [Finite G] hΔ hpts hq hX in
theorem quadPart_conj_of_mem {g : G} (hg : g ∈ D ⊔ E') (x : G) (s : GaloisField 2 k) :
    φ₀.quadPart (g * x * g⁻¹) s = g * φ₀.quadPart x s * g⁻¹ :=
  φ₀.quadPart_conj (fun y hy => (F.comm y hy g hg).symm) x s

variable (φ₁ : SL2Coords D E' k)

theorem quadCoord_add {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (s s' : GaloisField 2 k) :
    φ₀.quadCoord φ₁ x (s + s') = φ₀.quadCoord φ₁ x s + φ₀.quadCoord φ₁ x s' := by
  rw [SL2Coords.quadCoord, F.quadPart_add hΔ φ₀ hpts hq hX hx,
    φ₁.lowerCoord_mul (F.quadPart_mem hΔ φ₀ hpts hq hX hx s)
      (F.quadPart_mem hΔ φ₀ hpts hq hX hx s')]
  rfl

theorem quadCoord_smulG {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (μ : (GaloisField 2 k)ˣ)
    (s : GaloisField 2 k) :
    φ₀.quadCoord φ₁ (φ₀.smulG μ x) s = φ₀.quadCoord φ₁ x (μ * μ * s) := by
  rw [SL2Coords.quadCoord, F.quadPart_smulG hΔ φ₀ hpts hq hX hx]
  rfl

theorem quadCoord_torusElt {x : G} (hx : x ∈ shortRootGroup Δ E A D E') (ν : (GaloisField 2 k)ˣ)
    (s : GaloisField 2 k) :
    φ₀.quadCoord φ₁ (φ₁.torusElt ν * x * (φ₁.torusElt ν)⁻¹) s =
      ((ν⁻¹ : (GaloisField 2 k)ˣ) : GaloisField 2 k) * ((ν⁻¹ : (GaloisField 2 k)ˣ) :
        GaloisField 2 k) * φ₀.quadCoord φ₁ x s := by
  rw [SL2Coords.quadCoord, F.quadPart_conj_of_mem φ₀ (φ₁.torusElt_mem ν),
    φ₁.lowerCoord_torusElt_conj ν (F.quadPart_mem hΔ φ₀ hpts hq hX hx s), pow_two]
  rfl

theorem coe_smul_eq_smulG (v : Additive ↥(shortRootGroup Δ E A D E')) (c : GaloisField 2 k) :
    letI := F.shortRootAddCommGroup hΔ
    letI := F.shortRootModule φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX
    (((c • v).toMul : ↥(shortRootGroup Δ E A D E')) : G) =
      φ₀.smulG c ((v.toMul : ↥(shortRootGroup Δ E A D E')) : G) := by
  by_cases hc : c = 0
  · rw [hc, SL2Coords.smulG_zero]
    exact F.coe_zero_smul φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX v
  · rw [φ₀.smulG_of_ne hc]
    exact F.coe_smul φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX hc v

theorem exists_monoidHom_torusElt_smulG (hX1 : ∃ x ∈ shortRootGroup Δ E A D E', x ≠ 1) :
    ∃ κ : (GaloisField 2 k)ˣ →* (GaloisField 2 k)ˣ, ∀ (μ : (GaloisField 2 k)ˣ) (x : G),
      x ∈ shortRootGroup Δ E A D E' →
        φ₁.torusElt μ * x * (φ₁.torusElt μ)⁻¹ = φ₀.smulG (κ μ) x := by
  obtain ⟨κ, hκ⟩ := F.exists_monoidHom_torusElt φ₀ hΔ (F.noIsolated hΔ.root) hpts hq hX φ₁ hX1
  refine ⟨κ, fun μ x hx => ?_⟩
  have h := hκ μ (Additive.ofMul ⟨x, hx⟩)
  rw [F.coe_smul_eq_smulG hΔ φ₀ hpts hq hX] at h
  exact h

theorem eq_one_of_quadCoord_eq_zero {x : G} (hx : x ∈ shortRootGroup Δ E A D E')
    (h0 : φ₀.quadCoord φ₁ x 1 = 0) : x = 1 := by
  have hd := F.quadPart_mem hΔ φ₀ hpts hq hX hx 1
  have hd1 : φ₀.quadPart x 1 = 1 := φ₁.eq_one_of_lowerCoord_eq_zero hd h0
  have ha1 : φ₀.elt (lowerElt _ 1) ≠ 1 := by
    intro h1
    have h2 := φ₀.elt_lowerElt_injective (h1.trans (by rw [← φ₀.elt_one, ← lowerElt_zero]))
    exact one_ne_zero h2
  refine F.eq_one_of_commutator_mem_shortRootGroup hΔ hpts hX hx (φ₀.elt_lowerElt_mem 1) ha1 ?_
  rw [φ₀.commutator_eq_mul_quadPart, hd1, mul_one, SL2Coords.smulG_one]
  exact F.conj_elt_weylElt_mem hΔ φ₀ hx

theorem exists_aligned (hX1 : ∃ x ∈ shortRootGroup Δ E A D E', x ≠ 1) :
    ∃ τ : GaloisField 2 k ≃+* GaloisField 2 k, φ₀.Aligned Δ (φ₁.map τ) := by
  obtain ⟨κ, hκ⟩ := F.exists_monoidHom_torusElt_smulG hΔ φ₀ hpts hq hX φ₁ hX1
  obtain ⟨x₀, hx₀, hx₀1⟩ := hX1
  let act : (GaloisField 2 k)ˣ → ↥(shortRootGroup Δ E A D E') → ↥(shortRootGroup Δ E A D E') :=
    fun μ x => ⟨φ₀.smulG μ x, F.smulG_mem hΔ φ₀ x.2 μ⟩
  obtain ⟨τ, hτ⟩ := GaloisAlign.exists_ringEquiv_of_torus act
    (γ := fun x t => φ₀.quadCoord φ₁ x t)
    (fun x s t => F.quadCoord_add hΔ φ₀ hpts hq hX φ₁ x.2 s t)
    (fun μ x t => F.quadCoord_smulG hΔ φ₀ hpts hq hX φ₁ x.2 μ t) κ
    (fun ν x t => by
      show φ₀.quadCoord φ₁ (φ₀.smulG (κ ν) x) t = _
      rw [← hκ ν x x.2]
      exact F.quadCoord_torusElt hΔ φ₀ hpts hq hX φ₁ x.2 ν t)
    ⟨⟨x₀, hx₀⟩, 1, fun h0 => hx₀1 (F.eq_one_of_quadCoord_eq_zero hΔ φ₀ hpts hq hX φ₁ hx₀ h0)⟩
  refine ⟨τ, fun ν x hx => ?_⟩
  set ν' : (GaloisField 2 k)ˣ := Units.map τ.symm.toRingHom.toMonoidHom ν with hν'
  have h1 : (φ₁.map τ).torusElt ν = φ₁.torusElt ν' := by
    rw [← SL2Coords.elt_diagElt, SL2Coords.map_elt, SL2Coords.map_diagElt,
      SL2Coords.elt_diagElt]
  have h2 : κ ν' = ν⁻¹ := by
    apply Units.ext
    rw [hτ ν', hν', Units.coe_map]
    simp [Units.val_inv_eq_inv_val]
  have h3 : φ₁.torusElt ν' * x * (φ₁.torusElt ν')⁻¹ =
      φ₀.torusElt ν⁻¹ * x * (φ₀.torusElt ν⁻¹)⁻¹ := by
    rw [hκ ν' x hx, h2, φ₀.smulG_units]
  rw [h1, Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  calc φ₀.torusElt ν * φ₁.torusElt ν' * x * (φ₀.torusElt ν * φ₁.torusElt ν')⁻¹ =
        φ₀.torusElt ν * (φ₁.torusElt ν' * x * (φ₁.torusElt ν')⁻¹) * (φ₀.torusElt ν)⁻¹ := by group
    _ = (φ₀.torusElt ν * φ₀.torusElt ν⁻¹) * x * (φ₀.torusElt ν * φ₀.torusElt ν⁻¹)⁻¹ := by
        rw [h3]
        group
    _ = x := by
        rw [← SL2Coords.torusElt_mul, mul_inv_cancel, SL2Coords.torusElt_one]
        group

end PairFrame

end CFSG.Timmesfeld.Transvection
