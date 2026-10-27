module

public import CFSG.Sporadic.Co1.Module.CoTwoAutLitInputs
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.CoTwoPerfect
public import CFSG.Sporadic.Co1.Module.OddNative

public section

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Blueprint CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.InvFam
  CFSG.KC.CoTwoAut CFSG.KC.Co1M CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.Module.CoTwo

open CFSG.Monster.GMS (co1Orbit co1Stab)

attribute [local instance] Odd.vecAct Odd.vecSMul

theorem orbit_eq_orbitSet (H : Subgroup NativeSporadic.Co1) (x : Vec24) :
    MulAction.orbit H x = orbitSet co1Act H x := by
  ext y
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem stabilizer_eq (v : Vec24) : MulAction.stabilizer NativeSporadic.Co1 v = co1Stab v := by
  ext g
  rfl

theorem pair_card {i j : Fin 3} {v w : Vec24} (hv : v ∈ co1Orbit i)
    (hw : w ∈ co1Orbit j) :
    (orbitSet co1Act (co1Stab v) w).ncard * (co1Orbit i).ncard =
      (co1Orbit j).ncard * (orbitSet co1Act (co1Stab w) v).ncard := by
  have hfin : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  have h1 := CFSG.Monster.GMS.Leech.card_co1Stab_mul_ncard_co1Orbit hv
  have h2 := CFSG.Monster.GMS.Leech.card_co1Stab_mul_ncard_co1Orbit hw
  have h3 := Pairs.ncard_orbit_mul_card_inf_stabilizer (co1Stab v) w
  have h4 := Pairs.ncard_orbit_mul_card_inf_stabilizer (co1Stab w) v
  erw [orbit_eq_orbitSet, stabilizer_eq] at h3 h4
  rw [inf_comm] at h4
  have hS : 0 < Nat.card ↥(co1Stab v ⊓ co1Stab w) := Nat.card_pos
  have e : (orbitSet co1Act (co1Stab v) w).ncard * (co1Orbit i).ncard *
      Nat.card ↥(co1Stab v ⊓ co1Stab w) =
      (co1Orbit j).ncard * (orbitSet co1Act (co1Stab w) v).ncard *
        Nat.card ↥(co1Stab v ⊓ co1Stab w) := by
    calc _ = Nat.card (co1Stab v) * (co1Orbit i).ncard := by rw [← h3]; ring
      _ = Nat.card (co1Stab w) * (co1Orbit j).ncard := by rw [h1, h2]
      _ = _ := by rw [← h4]; ring
  exact Nat.eq_of_mul_eq_mul_right hS e

theorem getT_map (T : List STree) : ∀ (j : ℕ), j < T.length →
    getT (T.map STree.tab) j = (T.getD j nilA).tab := by
  induction T with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons t T ih =>
    intro j hj
    rcases j with _ | j
    · rfl
    · exact ih j (by simpa using hj)

theorem getL_01 : ∀ l < 2, getL 0 [0, 1] l = l := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

theorem le_ncard_of_inj' {α : Type*} {s : Set α} {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite) : n ≤ s.ncard := by
  have hsub : f '' Set.Iio n ⊆ s := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have hinj' : Set.InjOn f (Set.Iio n) := fun i hi j hj e => hinj i hi j hj e
  have hc : (f '' Set.Iio n).ncard = n := by rw [hinj'.ncard_image, Set.ncard_Iio_nat]
  calc n = (f '' Set.Iio n).ncard := hc.symm
    _ ≤ s.ncard := Set.ncard_le_ncard hsub hs

theorem forest_orbit
    {GT : List ℕ} {T : List STree} {Rt Sz : List ℕ} {P : ℕ → ℕ}
    {bound : ℕ} {ex : ℕ → Bool} (hF : ForestOK GT T Rt Sz P bound ex)
    (gen : ℕ → NativeSporadic.Co1)
    (hact : ∀ l < 2, ∀ v, co1Act (gen l) (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 GT l) v))
    (C : Subgroup NativeSporadic.Co1) (hC : ∀ l < 2, gen l ∈ C) {x : Vec24}
    (hx : x ∈ co1Orbit 0) :
    ∃ j < Sz.length, (∃ h ∈ C, co1Act h x = toVecD 24 (Rt.getD j 0)) ∧
      Sz.getD j 0 ≤ (orbitSet co1Act C x).ncard := by
  have hfin : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  obtain ⟨c, hc, rfl⟩ := Odd.exists_toVecD x
  have hin : inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 c = true := by
    refine (Odd.inPts_iff c hc).2 ?_
    rw [← Pairs.orbit_Co1_eq]
    exact hx
  simp only [inPts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hin
  obtain ⟨hi, hpt⟩ := hin
  obtain ⟨i, hidef⟩ : ∃ i, ((posTable 24 (orbitOf 2 98280).pts)[c]!).toNat = i := ⟨_, rfl⟩
  rw [hidef] at hi
  try rw [hidef] at hpt
  have hcov := hF.cov i hi
  unfold covAt at hcov
  have hib : Nat.blt i 98280 = true := Nat.blt_eq.mpr hi
  rw [hib] at hcov
  change andB _ (andB _ _) = true at hcov
  obtain ⟨hj, hk⟩ := andB_true_iff.1 hcov
  obtain ⟨hk, hv⟩ := andB_true_iff.1 hk
  set j := Nat.land (P i) 7
  set k := Nat.shiftRight (P i) 3
  have hj' : j < Sz.length := by rw [← InvFam.lenL_eq]; exact blt_iff.1 hj
  have hk' : k < Sz.getD j 0 := by
    have := blt_iff.1 hk
    rwa [InvFam.getL_eq, ← List.getD_eq_getElem?_getD] at this
  have hv' : valF 24 ((T.getD j nilA).tab k) = c := by
    rw [← getT_map T j (by rw [hF.lenT]; exact hj'), beq_iff.1 hv]
    exact hpt
  have hjR : j < Rt.length := by rw [hF.lenR]; exact hj'
  have hroot : Rt.getD j 0 < 2 ^ 24 := by
    refine InvFam.bnd_spec hF.roots _ ?_
    rw [List.getD_eq_getElem _ _ hjR]
    exact List.getElem_mem hjR
  have h2 : ∀ l, l < lenL [0, 1] → l < 2 := fun l hl => hl
  obtain ⟨t, ht, hinj⟩ := InvFam.vec_family C (hF.trees j hj') hroot gen
    (fun l hl => hC l (h2 l hl))
    (fun l hl v => by rw [getL_01 l (h2 l hl)]; exact hact l (h2 l hl) v)
  obtain ⟨htk, -, htk'⟩ := ht k hk'
  rw [hv'] at htk'
  refine ⟨j, hj', ⟨(t k)⁻¹, C.inv_mem htk, ?_⟩, ?_⟩
  · rw [htk', ← Odd.co1Act_mul', inv_mul_cancel, Odd.co1Act_one']
  · refine le_ncard_of_inj' (fun i => co1Act (t i) (toVecD 24 (Rt.getD j 0)))
      (fun i hi => ?_) hinj (Set.toFinite _)
    refine ⟨t i * (t k)⁻¹, C.mul_mem (ht i hi).1 (C.inv_mem htk), ?_⟩
    rw [htk', Odd.co1Act_mul', ← Odd.co1Act_mul' (t k)⁻¹, inv_mul_cancel, Odd.co1Act_one']

theorem aut_gens {D : AutW} (hD : AutOK D) {W : List (List ℕ)}
    {G GT : List ℕ} (hlen : W.length = 2) (hlet : ∀ w ∈ W, ∀ l ∈ w, l < 2)
    (hw : ∀ l < 2, wK [D.R0, D.R1] (W.getD l []) = getL 0 G l)
    (htr : ∀ l < 2, trK 24 (getL 0 G l) = getL 0 GT l) :
    ∃ x : ℕ → NativeSporadic.Co1, ∀ l < 2, ∀ v,
      co1Act (x l) (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 GT l) v) := by
  obtain ⟨a, ha⟩ := exists_co1_matA
  obtain ⟨b, hb⟩ := exists_co1_matB
  have hpa : PM a D.R0 := by
    unfold PM
    rw [← hD.rA]
    exact ha
  have hpb : PM b D.R1 := by
    unfold PM
    rw [← hD.rB]
    exact hb
  let gens : ℕ → NativeSporadic.Co1 := fun l => if l = 0 then a else b
  have hg : ∀ l < 2, PM (gens l) (getL 0 [D.R0, D.R1] l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hpa
    · exact hpb
  refine ⟨fun l => ((W.getD l []).map gens).prod, fun l hl v => ?_⟩
  have hmem : W.getD l [] ∈ W := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hpm := pm_wK [D.R0, D.R1] gens 2 hg (W.getD l []) (hlet _ hmem)
  rw [hw l hl] at hpm
  exact pm_act hpm (htr l hl) v

theorem v₂_mem_orbit0 : v₂ ∈ co1Orbit 0 :=
  ⟨1, by simp only [map_one, Module.End.one_apply]; rfl⟩

theorem mem_stab_of_act {x : NativeSporadic.Co1} {c : ℕ} {GT : List ℕ} {l : ℕ}
    (hx : ∀ v, co1Act x (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 GT l) v))
    (hfix : vmF 24 (getL 0 GT l) c = c) : x ∈ co1Stab (toVecD 24 c) := by
  have h := hx c
  rw [hfix] at h
  exact h

theorem conj_mem_stab {g s : NativeSporadic.Co1} {w c : Vec24} (hg : co1Act g w = c)
    (hs : s ∈ co1Stab c) : g⁻¹ * s * g ∈ co1Stab w := by
  have hs' : co1Act s c = c := hs
  change co1Act (g⁻¹ * s * g) w = w
  rw [Odd.co1Act_mul', Odd.co1Act_mul', hg, hs', ← hg, ← Odd.co1Act_mul', inv_mul_cancel,
    Odd.co1Act_one']

theorem stab_orbit_ge
    {GT : List ℕ} {T : List STree} {Rt Sz : List ℕ} {P : ℕ → ℕ}
    {bound : ℕ} {ex : ℕ → Bool} (hF : ForestOK GT T Rt Sz P bound ex) {c : ℕ}
    (gen : ℕ → NativeSporadic.Co1)
    (hact : ∀ l < 2, ∀ v, co1Act (gen l) (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 GT l) v))
    (hfix : ∀ l < 2, vmF 24 (getL 0 GT l) c = c) {w : Vec24} {g : NativeSporadic.Co1}
    (hg : co1Act g w = toVecD 24 c)
    (hex : ∀ r < 2 ^ 24, ∀ h ∈ co1Stab (toVecD 24 c), co1Act h (co1Act g v₂) = toVecD 24 r →
      ex r = false) :
    bound ≤ (orbitSet co1Act (co1Stab w) v₂).ncard := by
  have hfin : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  have hx : co1Act g v₂ ∈ co1Orbit 0 :=
    CFSG.Monster.GMS.Leech.co1Act_mem_co1Orbit v₂_mem_orbit0 g
  obtain ⟨j, hj, ⟨h, hh, hroot⟩, hsz⟩ := forest_orbit hF gen hact (co1Stab (toVecD 24 c))
    (fun l hl => mem_stab_of_act (hact l hl) (hfix l hl)) hx
  have hjR : j < Rt.length := by rw [hF.lenR]; exact hj
  have hr : Rt.getD j 0 < 2 ^ 24 := by
    refine InvFam.bnd_spec hF.roots _ ?_
    rw [List.getD_eq_getElem _ _ hjR]
    exact List.getElem_mem hjR
  have hb : bound ≤ Sz.getD j 0 := by
    rcases hF.big j hj with hb | hb
    · exact hb
    · rw [hex _ hr h hh hroot] at hb
      exact absurd hb Bool.false_ne_true
  refine hb.trans (hsz.trans ?_)
  have hsub : (fun y => co1Act g⁻¹ y) '' orbitSet co1Act (co1Stab (toVecD 24 c)) (co1Act g v₂) ⊆
      orbitSet co1Act (co1Stab w) v₂ := by
    rintro _ ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨g⁻¹ * s * g, conj_mem_stab hg hs, ?_⟩
    rw [Odd.co1Act_mul', Odd.co1Act_mul']
  have hinj : Function.Injective fun y => co1Act g⁻¹ y := by
    intro y z e
    have e' := congrArg (co1Act g) e
    simp only [← Odd.co1Act_mul', mul_inv_cancel, Odd.co1Act_one'] at e'
    exact e'
  rw [← Set.ncard_image_of_injective _ hinj]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem bil_of_stab
    {g h : NativeSporadic.Co1} {w : Vec24} {c r : ℕ} (hg : co1Act g w = toVecD 24 c)
    (hh : h ∈ co1Stab (toVecD 24 c)) (hr : co1Act h (co1Act g v₂) = toVecD 24 r)
    (hP : bil₀ w v₂ = 0) : bilN (transposeRows 24 f0Rows) r c = false := by
  have hh' : co1Act h (toVecD 24 c) = toVecD 24 c := hh
  have e : bil₀ (toVecD 24 r) (toVecD 24 c) = 0 := by
    rw [← hr, ← hh', ← hg]
    have i1 : bil₀ (co1Act h (co1Act g v₂)) (co1Act h (co1Act g w)) =
        bil₀ (co1Act g v₂) (co1Act g w) := CFSG.Monster.GMS.Leech.bil₀_co1Act h _ _
    have i2 : bil₀ (co1Act g v₂) (co1Act g w) = bil₀ v₂ w := CFSG.Monster.GMS.Leech.bil₀_co1Act g _ _
    rw [i1, i2, bil₀_comm, hP]
  rw [Odd.bil₀_toVecD] at e
  cases hb : bilN (transposeRows 24 f0Rows) r c
  · rfl
  · rw [hb] at e
    exact absurd e (by decide)

theorem lab_orbit0
    {c : ℕ} (hc : c < 2 ^ 24) (h : labA c = 3) :
    toVecD 24 c ∈ co1Orbit 0 := by
  have hm := (Pairs.tyLab_spec c hc 3 (by norm_num)).1 h
  rw [Pairs.co1Orbit_zero, Pairs.orbit_Co1_eq]
  exact hm

theorem lab_orbit1
    {c : ℕ} (hc : c < 2 ^ 24) (h : labA c = 2) :
    toVecD 24 c ∈ co1Orbit 1 := by
  have hm := (Pairs.tyLab_spec c hc 2 (by norm_num)).1 h
  rw [Pairs.co1Orbit_one, Pairs.orbit_Co1_eq]
  exact hm

theorem lab_orbit2
    {c : ℕ} (hc : c < 2 ^ 24) (h : labA c = 1) :
    toVecD 24 c ∈ co1Orbit 2 := by
  have hm := (Pairs.tyLab_spec c hc 1 (by norm_num)).1 h
  rw [Pairs.co1Orbit_two, Pairs.orbit_Co1_eq]
  exact hm

theorem co1Act_add' (x : NativeSporadic.Co1) (a b : Vec24) :
    co1Act x (a + b) = co1Act x a + co1Act x b :=
  Matrix.mulVec_add _ _ _

theorem ncard_orbitSet_gt_lit
    (hD : ∃ D : AutW, AutOK D)
    {w : Vec24} (hP : bil₀ w v₂ = 0) (h0 : w ≠ 0) (_h2 : w ≠ v₂)
    (hw : w ∉ co1Orbit 0) (hw' : v₂ + w ∉ co1Orbit 0) :
    46575 < (orbitSet co1Act kc w).ncard := by
  obtain ⟨D, hD⟩ := hD
  have hv : v₂ ∈ co1Orbit 0 := v₂_mem_orbit0
  obtain ⟨i, hi, -⟩ := CFSG.Monster.GMS.Leech.existsUnique_co1Orbit h0
  have hpair := pair_card hv hi
  rw [CFSG.Monster.GMS.Leech.ncard_co1Orbit_zero] at hpair
  have hkc : orbitSet co1Act kc w = orbitSet co1Act (co1Stab v₂) w := rfl
  rw [hkc]
  fin_cases i
  · exact absurd hi hw
  · change w ∈ co1Orbit 1 at hi
    change _ = (co1Orbit 1).ncard * _ at hpair
    have hc : toVecD 24 code3 ∈ co1Orbit 1 := lab_orbit1 (by decide) hD.l3
    obtain ⟨g, hg⟩ := CFSG.Monster.GMS.Leech.exists_co1Act_eq hi hc
    have hg' : co1Act g w = toVecD 24 code3 := hg
    obtain ⟨x, hx⟩ := aut_gens hD hD.lenW.1 (fun w hw l hl => hD.letters w
      (List.mem_append_left _ hw) l hl) hD.words3 hD.tr3
    have hb := stab_orbit_ge hD.f3 x hx hD.fix3 hg' (fun r _ h hh hr => bil_of_stab hg' hh hr hP)
    rw [CFSG.Monster.GMS.Leech.ncard_co1Orbit_one] at hpair
    omega
  · change w ∈ co1Orbit 2 at hi
    change _ = (co1Orbit 2).ncard * _ at hpair
    have hc : toVecD 24 code4 ∈ co1Orbit 2 := lab_orbit2 (by decide) hD.l4
    obtain ⟨g, hg⟩ := CFSG.Monster.GMS.Leech.exists_co1Act_eq hi hc
    have hg' : co1Act g w = toVecD 24 code4 := hg
    obtain ⟨x, hx⟩ := aut_gens hD hD.lenW.2.1 (fun w hw l hl => hD.letters w
      (List.mem_append_right _ hw) l hl) hD.words4 hD.tr4
    have hb := stab_orbit_ge hD.f4 x hx hD.fix4 hg' (fun r hr h hh hrr => by
      unfold ex4
      rw [bil_of_stab hg' hh hrr hP, Bool.false_or]
      cases hl : labA (r ^^^ code4) == 3
      · rfl
      · exfalso
        have hl' : labA (r ^^^ code4) = 3 := beq_iff_eq.1 hl
        have hm := lab_orbit0 (Nat.xor_lt_two_pow hr (by decide)) hl'
        have hh' : co1Act h (toVecD 24 code4) = toVecD 24 code4 := hh
        have e : toVecD 24 (r ^^^ code4) = co1Act (h * g) (v₂ + w) := by
          rw [toVecD_xor, ← hrr, ← hh', ← hg', Odd.co1Act_mul', co1Act_add', co1Act_add']
        rw [e] at hm
        have hm' := CFSG.Monster.GMS.Leech.co1Act_mem_co1Orbit hm (h * g)⁻¹
        have e2 : CFSG.Monster.GMS.co1Act (h * g)⁻¹ (co1Act (h * g) (v₂ + w)) = v₂ + w := by
          change co1Act (h * g)⁻¹ (co1Act (h * g) (v₂ + w)) = v₂ + w
          rw [← Odd.co1Act_mul', inv_mul_cancel, Odd.co1Act_one']
        rw [e2] at hm'
        exact hw' hm')
    rw [CFSG.Monster.GMS.Leech.ncard_co1Orbit_two] at hpair
    omega

end CFSG.Sporadic.Co1.Module.CoTwoAut

end
