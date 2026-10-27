module

public import CFSG.Quasithin.H13.AS91Sec4FourModel
public import Certificates.Certificate89406

public section

namespace CFSG.Quasithin.H13.AS91.Two

open Subgroup CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem w1OK46_spec :
    (∀ a ∈ w1List, ∀ b ∈ w1List, a ^^^ b ∈ w1List) ∧ ∀ a ∈ w1List, q0b a = false := by
  have h := Certificates.certificate89406
  simp only [ok46, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  simp only [w1OK46, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.not_eq_true'] at h1
  exact h1

theorem ebOK46_spec :
    gensOKb ebRows = true ∧ (∀ e ∈ ebRows, ∀ c ∈ w1List, appN e c = c) ∧
      (∀ e ∈ ebRows, (Std.HashSet.ofList (enumGrp pRows)).contains e = true) ∧
      (∀ e ∈ ebRows, mulR e omegaRows = mulR omegaRows e) ∧
      idR ∈ enumGrp ebRows ∧ closedCheck ebRows (enumGrp ebRows) = true ∧
      (enumGrp ebRows).dedup.length = 16 ∧
      (∀ x ∈ enumGrp (stab1Gens ()), (∀ c ∈ w1List, appN x c = c) →
        (Std.HashSet.ofList (enumGrp ebRows)).contains x = true) ∧
      (∀ g ∈ g13Gens (), imgMask g (w1Mask ()) = w1Mask ()) ∧
      (∀ x ∈ enumGrp ebRows, ∀ y ∈ enumGrp ebRows, mulR x y = mulR y x) ∧
      ∀ x ∈ enumGrp ebRows, mulR x x = idR := by
  have h := Certificates.certificate89406
  simp only [ok46, Bool.and_eq_true] at h
  have h2 := h.1.1.2
  simp only [ebOK46, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩, g10⟩, g11⟩ := h2
  refine ⟨g1, g2, g3, g4, g5, g6, g7, fun x hx hfix => ?_, g9, g10, g11⟩
  rcases g8 x hx with h' | h'
  · obtain ⟨c, hc, hcf⟩ := List.all_eq_false.mp h'
    exact absurd (hfix c hc) (by simpa using hcf)
  · exact h'

theorem transOK46_spec :
    gensOKb (g13Gens ()) = true ∧ ∀ x ∈ enumGrp ebRows, x = idR ∨
      (Std.HashSet.ofList (ebOrbit ())).contains x = true := by
  have h := Certificates.certificate89406
  simp only [ok46, Bool.and_eq_true] at h
  have h3 := h.1.2
  simp only [transOK46, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h3
  exact h3

theorem jOK46_spec :
    (∀ F ∈ fixClosure (), ∀ rf ∈ fixPairs (),
      (Std.HashSet.ofList ((fixClosure ()).map mkey)).contains (mkey (F &&& rf.2)) = true) ∧
      ∀ F ∈ fixClosure (), jF (fixPairs ()) (w1Mask ()) F = true := by
  have h := Certificates.certificate89406
  simp only [ok46, Bool.and_eq_true] at h
  have h4 := h.2
  simp only [jOK46, Bool.and_eq_true, List.all_eq_true] at h4
  exact h4

theorem mem_W1_iff {v : V12} : v ∈ W1 ↔ codeOf v ∈ w1List := by
  rw [mem_setOfMask, w1Mask, testBit_maskOf]

theorem w1List_lt : ∀ c ∈ w1List, c < 4096 := by decide

theorem vecOf_mem_W1 {c : ℕ} (hc : c < 4096) : vecOf c ∈ W1 ↔ c ∈ w1List := by
  rw [mem_W1_iff, codeOf_vecOf hc]

theorem add_mem_W1 {v w : V12} (hv : v ∈ W1) (hw : w ∈ W1) :
    v + w ∈ W1 := by
  rw [mem_W1_iff] at hv hw ⊢
  rw [← vecOf_codeOf v, ← vecOf_codeOf w, ← vecOf_xor,
    codeOf_vecOf (Nat.xor_lt_two_pow (n := 12) (codeOf_lt v) (codeOf_lt w))]
  exact w1OK46_spec.1 _ hv _ hw

theorem zero_mem_W1 : (0 : V12) ∈ W1 := by
  rw [← vecOf_zero, vecOf_mem_W1 (by norm_num)]
  decide

@[expose] def W1sub : Submodule (ZMod 2) V12 where
  carrier := W1
  add_mem' := add_mem_W1
  zero_mem' := zero_mem_W1
  smul_mem' c v hv := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]
      exact zero_mem_W1
    · rw [one_smul]
      exact hv

theorem q0_of_mem_W1 {v : V12} (hv : v ∈ W1) : q0 v = 0 := by
  rw [← vecOf_codeOf v, q0_vecOf, w1OK46_spec.2 _ (mem_W1_iff.mp hv)]
  rfl

theorem card_W1sub : Nat.card W1sub = 64 := by
  have e : Nat.card ↥(W1sub : Submodule (ZMod 2) V12) = (W1 : Set V12).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [e]
  have hW : W1 = vecOf '' {c | c ∈ w1List} := by
    ext v
    constructor
    · intro hv
      exact ⟨codeOf v, mem_W1_iff.mp hv, vecOf_codeOf v⟩
    · rintro ⟨c, hc, rfl⟩
      exact (vecOf_mem_W1 (w1List_lt c hc)).mpr hc
  have hinj : Set.InjOn vecOf {c | c ∈ w1List} := fun a ha b hb he =>
    vecOf_inj (w1List_lt a ha) (w1List_lt b hb) he
  have e2 : {c | c ∈ w1List} = (w1List.toFinset : Set ℕ) := by
    ext c
    simp
  rw [hW, hinj.ncard_image, e2, Set.ncard_coe_finset, List.toFinset_card_of_nodup (by decide)]
  rfl

abbrev ebGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp ebRows

theorem gensOK_eb : GensOK ebRows :=
  gensOK_of_gensOKb ebOK46_spec.1

theorem card_ebGrp : Nat.card ebGrp = 16 := by
  obtain ⟨-, -, -, -, hid, hc, hn, -⟩ := ebOK46_spec
  rw [card_genGrp (enumGrp_sound gensOK_eb) hid hc, hn]

theorem ebGrp_le_pGrp :
    ebGrp ≤ pGrp :=
  genGrp_le_of_rep fun e he => rep_of_contains gensOK_pRows (ebOK46_spec.2.2.1 e he)

theorem ebGrp_fix {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ ebGrp)
    {v : V12} (hv : v ∈ W1) : U v = v := by
  have hU' : U ∈ Submonoid.closure (GenSet ebRows) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction (motive := fun (U : V12 ≃ₗ[ZMod 2] V12) _ => U v = v)
    ?_ ?_ ?_ hU'
  · rintro x ⟨r, hr, hx⟩
    rw [hx, ← vecOf_codeOf v, ← vecOf_appN, ebOK46_spec.2.1 r hr _ (mem_W1_iff.mp hv)]
  · rfl
  · intro x y _ _ hx hy
    rw [LinearEquiv.mul_apply, hy, hx]

theorem ebGrp_theta0 {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ ebGrp)
    (v : V12) : U (theta0 v) = theta0 (U v) := by
  have hU' : U ∈ Submonoid.closure (GenSet ebRows) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction
    (motive := fun (U : V12 ≃ₗ[ZMod 2] V12) _ => ∀ v, U (theta0 v) = theta0 (U v)) ?_ ?_ ?_ hU' v
  · rintro x ⟨r, hr, hx⟩ v
    rw [hx, hx, ← linOfRows_omegaRows, ← linOfRows_omegaRows, ← linOfRows_mulR, ← linOfRows_mulR,
      ebOK46_spec.2.2.2.1 r hr]
  · intro v
    rfl
  · intro x y _ _ hx hy v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hy, hx]

theorem ebGrp_comm {x y : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ ebGrp)
    (hy : y ∈ ebGrp) : x * y = y * x := by
  obtain ⟨-, -, -, -, hid, hc, -, -, -, hcomm, -⟩ := ebOK46_spec
  obtain ⟨rx, hrx, hxr⟩ := complete hid hc x hx
  obtain ⟨ry, hry, hyr⟩ := complete hid hc y hy
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxr, hyr, hxr, hyr, ← linOfRows_mulR,
    ← linOfRows_mulR, hcomm rx hrx ry hry]

theorem ebGrp_sq {x : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ ebGrp) :
    x * x = 1 := by
  obtain ⟨-, -, -, -, hid, hc, -, -, -, -, hsq⟩ := ebOK46_spec
  obtain ⟨rx, hrx, hxr⟩ := complete hid hc x hx
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, hxr, hxr, ← linOfRows_mulR, hsq rx hrx, linOfRows_idR]
  rfl

theorem stab1_enum :
    idR ∈ enumGrp (stab1Gens ()) ∧ closedCheck (stab1Gens ()) (enumGrp (stab1Gens ())) = true := by
  have h := Data41.stabOK42_spec.1
  simp only [stabOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hidX⟩, hcX⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨by simpa using hidX, hcX⟩

theorem mem_ebGrp_of_fix
    (hst : stabIn nGrp (vecOf 3) = genGrp (stab1Gens ())) {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ nGrp)
    (hfix : ∀ v ∈ W1, U v = v) : U ∈ ebGrp := by
  have h3 : U ∈ genGrp (stab1Gens ()) := by
    rw [← hst]
    exact mem_stabIn.mpr ⟨hU, hfix _ ((vecOf_mem_W1 (by norm_num)).mpr (by decide))⟩
  have hgs := (stabOK_spec Data41.stabOK42_spec.1).1
  obtain ⟨hidX, hcX⟩ := stab1_enum
  obtain ⟨x, hxX, hUx⟩ := complete hidX hcX U h3
  have hxfix : ∀ c ∈ w1List, appN x c = c := fun c hc => by
    have h1 := hfix (vecOf c) ((vecOf_mem_W1 (w1List_lt c hc)).mpr hc)
    rw [hUx, ← vecOf_appN] at h1
    exact vecOf_inj (appN_lt (okRows_lt (enumGrp_sound hgs x hxX).1) _) (w1List_lt c hc) h1
  obtain ⟨-, V, hV, hVx⟩ := rep_of_contains gensOK_eb (ebOK46_spec.2.2.2.2.2.2.2.1 x hxX hxfix)
  rw [show U = V from LinearEquiv.ext fun v => (hUx v).trans (hVx v).symm]
  exact hV

theorem gensOK_g13 : GensOK (g13Gens ()) :=
  gensOK_of_gensOKb transOK46_spec.1

theorem g13Gens_le_nGrp : genGrp (g13Gens ()) ≤ nGrp :=
  Data41.genGrp_stabGens_le (ws := g13Words) (by decide)

theorem g13Gens_image_W1 {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ genGrp (g13Gens ())) : ⇑U '' W1 = W1 := by
  have hU' : U ∈ Submonoid.closure (GenSet (g13Gens ())) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction (motive := fun (U : V12 ≃ₗ[ZMod 2] V12) _ => ⇑U '' W1 = W1)
    ?_ ?_ ?_ hU'
  · rintro x ⟨r, hr, hx⟩
    have e : ⇑x = ⇑(linOfRows r) := funext hx
    rw [e]
    exact image_W1_of_imgMask (okRows_lt (gensOK_g13 r hr).1) (ebOK46_spec.2.2.2.2.2.2.2.2.1 r hr)
  · exact Set.image_id' _
  · intro x y _ _ hx hy
    rw [image_mul, hy, hx]

theorem g13Gens_le_g13Grp : genGrp (g13Gens ()) ≤ g13Grp :=
  fun _ hU => mem_g13Grp.mpr ⟨g13Gens_le_nGrp hU, g13Gens_image_W1 hU⟩

@[expose] noncomputable def e0 : V12 ≃ₗ[ZMod 2] V12 :=
  eqvOf (ebRows.headD idR) (invR (ebRows.headD idR))
    (gensOK_eb _ (by simp [ebRows])).2.2.1 (gensOK_eb _ (by simp [ebRows])).2.2.2

theorem exists_conj_eb {x : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ ebGrp)
    (hx1 : x ≠ 1) : ∃ U ∈ genGrp (g13Gens ()), U * e0 * U⁻¹ = x := by
  have horb : ∀ o ∈ ebOrbit (), ∃ U ∈ genGrp (g13Gens ()),
      ∀ v, linOfRows o v = (U * e0 * U⁻¹) v := by
    intro o ho
    unfold ebOrbit at ho
    refine bfsClosure_inv _ _ (P := fun o => ∃ U ∈ genGrp (g13Gens ()),
      ∀ v, linOfRows o v = (U * e0 * U⁻¹) v) ?_ _ _ _ _ ?_ (by simp) o ho
    · intro f hf o ⟨U, hU, hoU⟩
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      obtain ⟨-, -, h1, h2⟩ := gensOK_g13 g hg
      set G := eqvOf g (invR g) h1 h2 with hG
      refine ⟨G * U, mul_mem (gen_mem gensOK_g13 hg) hU, fun v => ?_⟩
      show linOfRows (mulR g (mulR o (invR g))) v = _
      rw [linOfRows_mulR, linOfRows_mulR, hoU]
      have hGi : ∀ w, G⁻¹ w = linOfRows (invR g) w := fun w => eqvOf_inv_apply g (invR g) h1 h2 w
      simp only [LinearEquiv.mul_apply, mul_inv_rev]
      rw [hGi]
      rfl
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨1, one_mem _, fun v => ?_⟩
      simp only [one_mul, inv_one, mul_one]
      rfl
  obtain ⟨-, -, -, -, hid, hc, -⟩ := ebOK46_spec
  obtain ⟨r, hr, hxr⟩ := complete hid hc x hx
  rcases transOK46_spec.2 r hr with h0 | hO
  · exact absurd (LinearEquiv.ext fun v => by rw [hxr, h0, linOfRows_idR]; rfl) hx1
  · rw [Std.HashSet.contains_ofList, List.contains_iff_mem] at hO
    obtain ⟨U, hU, hrU⟩ := horb r hO
    exact ⟨U, hU, LinearEquiv.ext fun v => by rw [← hrU, hxr]⟩

theorem testBit_and_iff (a b c : ℕ) :
    (a &&& b).testBit c = true ↔ a.testBit c = true ∧ b.testBit c = true := by
  rw [Nat.testBit_and, Bool.and_eq_true]

theorem testBit_fixMask {r : Array ℕ} {c : ℕ} :
    (fixMask r).testBit c = true ↔ c < 4096 ∧ appN r c = c := by
  rw [fixMask, testBit_maskOf, List.mem_filter, List.mem_range, beq_iff_eq]

theorem fix_iff_appN {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096) (v : V12) :
    linOfRows r v = v ↔ appN r (codeOf v) = codeOf v := by
  constructor
  · intro h
    have e : vecOf (appN r (codeOf v)) = vecOf (codeOf v) := by rw [vecOf_appN, vecOf_codeOf, h]
    exact vecOf_inj (appN_lt hr _) (codeOf_lt v) e
  · intro h
    rw [← vecOf_codeOf v, ← vecOf_appN, h]

theorem setOfMask_and_fixMask {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096) (F : ℕ) :
    setOfMask (F &&& fixMask r) = setOfMask F ∩ {v | linOfRows r v = v} := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_setOfMask, testBit_and_iff, testBit_fixMask,
    fix_iff_appN hr]
  exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, codeOf_lt v, h2⟩⟩

theorem setOfMask_fullMask : setOfMask (fullMask ()) = Set.univ := by
  ext v
  simp only [mem_setOfMask, fullMask, testBit_maskOf, List.mem_range, Set.mem_univ, iff_true]
  exact codeOf_lt v

theorem isMask_fullMask : IsMask (fullMask ()) :=
  isMask_maskOf fun x hx => List.mem_range.mp hx

theorem isMask_and {F : ℕ} (hF : IsMask F) (m : ℕ) : IsMask (F &&& m) := fun i hi => by
  rw [Nat.testBit_and, hF i hi, Bool.false_and]

theorem mem_fixPairs {rf : Array ℕ × ℕ} :
    rf ∈ fixPairs () ↔ ∃ r ∈ pList (), rf = (r, fixMask r) := by
  simp only [fixPairs, List.mem_map]
  exact ⟨fun ⟨r, hr, he⟩ => ⟨r, hr, he.symm⟩, fun ⟨r, hr, he⟩ => ⟨r, hr, he.symm⟩⟩

theorem isMask_of_mem_fixClosure {F : ℕ} (hF : F ∈ fixClosure ()) : IsMask F := by
  unfold fixClosure at hF
  refine bfsClosure_inv _ _ (P := IsMask) ?_ _ _ _ _ ?_ (by simp) F hF
  · intro f hf F hF
    obtain ⟨rf, -, rfl⟩ := List.mem_map.1 hf
    exact isMask_and hF _
  · simp only [List.mem_singleton, forall_eq]
    exact isMask_fullMask

theorem fullMask_mem_fixClosure : fullMask () ∈ fixClosure () := by
  unfold fixClosure
  exact mem_bfsClosure _ _ _ _ _ _ _ (by simp)

theorem mem_of_contains_mkey {L : List ℕ} {x : ℕ}
    (h : (Std.HashSet.ofList (L.map mkey)).contains (mkey x) = true) : x ∈ L := by
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map] at h
  obtain ⟨y, hy, he⟩ := h
  have e : y = x := congrArg Prod.snd he
  rw [← e]
  exact hy

theorem jOK46_closed :
    ∀ F ∈ fixClosure (), ∀ r ∈ pList (),
      (Std.HashSet.ofList ((fixClosure ()).map mkey)).contains (mkey (F &&& fixMask r)) = true := by
  intro F hF r hr
  have h := jOK46_spec.1 F hF
  rw [fixPairs, List.forall_mem_map] at h
  have h' := h r hr
  dsimp only at h'
  exact h'

theorem and_mem_fixClosure {F : ℕ} (hF : F ∈ fixClosure ())
    {r : Array ℕ} (hr : r ∈ pList ()) : F &&& fixMask r ∈ fixClosure () :=
  mem_of_contains_mkey (jOK46_closed F hF r hr)

theorem rowsOf_mem_pList {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ pGrp) : rowsOf U ∈ pList () := by
  obtain ⟨-, -, hid, hc, -⟩ := pOK45_spec
  obtain ⟨x, hx, hUx⟩ := complete hid hc U hU
  rw [rowsOf_eq (enumGrp_sound gensOK_pRows x hx).1 hUx]
  exact List.mem_dedup.mpr hx

theorem okRows_of_mem_pList {r : Array ℕ} (hr : r ∈ pList ()) :
    okRows r = true :=
  (enumGrp_sound gensOK_pRows r (List.mem_dedup.mp hr)).1

@[expose] def fixSet (X : Set (V12 ≃ₗ[ZMod 2] V12)) : Set V12 := {v | ∀ U ∈ X, U v = v}

theorem exists_fixClosure
    (S : Finset (V12 ≃ₗ[ZMod 2] V12)) (hS : ∀ U ∈ S, U ∈ pGrp) :
    ∃ F ∈ fixClosure (), setOfMask F = {v | ∀ U ∈ S, U v = v} := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fullMask (), fullMask_mem_fixClosure, ?_⟩
    rw [setOfMask_fullMask]
    ext v
    simp
  | insert U S hUS ih =>
    obtain ⟨F, hF, hFe⟩ := ih fun V hV => hS V (Finset.mem_insert_of_mem hV)
    have hU := hS U (Finset.mem_insert_self U S)
    have hr := rowsOf_mem_pList hU
    refine ⟨F &&& fixMask (rowsOf U), and_mem_fixClosure hF hr, ?_⟩
    rw [setOfMask_and_fixMask (okRows_lt (okRows_of_mem_pList hr)), hFe]
    ext v
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp,
      linOfRows_rowsOf]
    tauto

theorem exists_fixClosure_subgroup
    {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hX : X ≤ pGrp) :
    ∃ F ∈ fixClosure (), setOfMask F = fixSet X := by
  obtain ⟨F, hF, hFe⟩ := exists_fixClosure (Set.toFinite (X : Set (V12 ≃ₗ[ZMod 2] V12))).toFinset
    fun U hU => hX ((Set.Finite.mem_toFinset _).mp hU)
  refine ⟨F, hF, hFe.trans ?_⟩
  ext v
  simp [fixSet]

theorem popc_eq {F : ℕ} (hF : IsMask F) : popc F = (setOfMask F).ncard := by
  have e : setOfMask F = vecOf '' {c | c ∈ (List.range 4096).filter F.testBit} := by
    ext v
    constructor
    · intro hv
      exact ⟨codeOf v, List.mem_filter.mpr ⟨List.mem_range.mpr (codeOf_lt v), hv⟩, vecOf_codeOf v⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
      rw [mem_setOfMask, codeOf_vecOf (List.mem_range.mp hc1)]
      exact hc2
  have hinj : Set.InjOn vecOf {c | c ∈ (List.range 4096).filter F.testBit} := fun a ha b hb he =>
    vecOf_inj (List.mem_range.mp (List.mem_filter.mp ha).1)
      (List.mem_range.mp (List.mem_filter.mp hb).1) he
  have e2 : {c | c ∈ (List.range 4096).filter F.testBit} =
      (((List.range 4096).filter F.testBit).toFinset : Set ℕ) := by
    ext c
    simp
  rw [e, hinj.ncard_image, e2, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup ((List.nodup_range).filter _), popc]

@[expose] def ptRows (F : ℕ) : List (Array ℕ) :=
  ((fixPairs ()).filter fun rf => F &&& rf.2 == F).map Prod.fst

theorem and_eq_self_iff {F m : ℕ} : F &&& m = F ↔ ∀ i, F.testBit i = true → m.testBit i = true := by
  constructor
  · intro h i hi
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : F.testBit i
    · rfl
    · rw [h i hi]
      rfl

theorem mem_filter_map_iff {L : List (Array ℕ × ℕ)} {F : ℕ} {r : Array ℕ} :
    r ∈ (L.filter fun rf => F &&& rf.2 == F).map Prod.fst ↔ ∃ m, (r, m) ∈ L ∧ F &&& m = F := by
  rw [List.mem_map]
  constructor
  · rintro ⟨rf, hrf, rfl⟩
    rw [List.mem_filter, beq_iff_eq] at hrf
    exact ⟨rf.2, hrf.1, hrf.2⟩
  · rintro ⟨m, hm, he⟩
    exact ⟨(r, m), List.mem_filter.mpr ⟨hm, beq_iff_eq.mpr he⟩, rfl⟩

theorem mem_ptRows {F : ℕ} (hF : IsMask F) {r : Array ℕ} :
    r ∈ ptRows F ↔ r ∈ pList () ∧ ∀ v ∈ setOfMask F, linOfRows r v = v := by
  rw [ptRows, mem_filter_map_iff]
  constructor
  · rintro ⟨m, hm, hand⟩
    obtain ⟨r', hr', he⟩ := mem_fixPairs.mp hm
    have h1 : r = r' := (Prod.mk.inj he).1
    have h2 : m = fixMask r' := (Prod.mk.inj he).2
    rw [h2] at hand
    rw [h1]
    refine ⟨hr', fun v hv => ?_⟩
    rw [fix_iff_appN (okRows_lt (okRows_of_mem_pList hr'))]
    exact (testBit_fixMask.mp (and_eq_self_iff.mp hand _ hv)).2
  · rintro ⟨hr, hfix⟩
    refine ⟨fixMask r, mem_fixPairs.mpr ⟨r, hr, rfl⟩, and_eq_self_iff.mpr fun i hi => ?_⟩
    have hi4 : i < 4096 := by
      by_contra h4
      rw [hF i (not_lt.mp h4)] at hi
      exact Bool.false_ne_true hi
    have hv := hfix (vecOf i) (by rw [mem_setOfMask, codeOf_vecOf hi4]; exact hi)
    rw [fix_iff_appN (okRows_lt (okRows_of_mem_pList hr)), codeOf_vecOf hi4] at hv
    exact testBit_fixMask.mpr ⟨hi4, hv⟩

theorem card_le_ptRows {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : X ≤ pGrp) {F : ℕ} (hF : IsMask F) (hFX : setOfMask F = fixSet X) :
    Nat.card X ≤ (ptRows F).length ∧ (Nat.card X = (ptRows F).length →
      ∀ r ∈ ptRows F, ∃ U ∈ X, rowsOf U = r) := by
  classical
  have hmem : ∀ U : ↥X, rowsOf (U : V12 ≃ₗ[ZMod 2] V12) ∈ (ptRows F).toFinset := fun U => by
    rw [List.mem_toFinset, mem_ptRows hF]
    refine ⟨rowsOf_mem_pList (hX U.2), fun v hv => ?_⟩
    rw [linOfRows_rowsOf]
    rw [hFX] at hv
    exact hv _ U.2
  let f : ↥X → ↥(ptRows F).toFinset := fun U => ⟨_, hmem U⟩
  have hinj : Function.Injective f := fun U V he => by
    have he' : rowsOf (U : V12 ≃ₗ[ZMod 2] V12) = rowsOf V := congrArg Subtype.val he
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [← linOfRows_rowsOf, he', linOfRows_rowsOf]
  have h1 : Nat.card X ≤ (ptRows F).toFinset.card := by
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_eq_finsetCard] at this
  have h2 := List.toFinset_card_le (ptRows F)
  refine ⟨h1.trans h2, fun heq r hr => ?_⟩
  have hbij : Function.Bijective f := by
    refine ⟨hinj, ?_⟩
    have hcard : Nat.card ↥X = Nat.card ↥(ptRows F).toFinset := by
      rw [Nat.card_eq_finsetCard]
      omega
    exact (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2
  obtain ⟨U, hU⟩ := hbij.2 ⟨r, List.mem_toFinset.mpr hr⟩
  exact ⟨U, U.2, congrArg Subtype.val hU⟩

theorem card_mul_le
    {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hX : X ≤ pGrp) (hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X * min 64 (fixSet X).ncard ≤ 512 ∨ (fixSet X = W1 ∧ Nat.card X ≤ 16) := by
  obtain ⟨F, hF, hFe⟩ := exists_fixClosure_subgroup hX
  have hmask := isMask_of_mem_fixClosure hF
  obtain ⟨hle, hall⟩ := card_le_ptRows hX hmask hFe
  have hj := jOK46_spec.2 F hF
  have hpop := popc_eq hmask
  rw [hFe] at hpop
  rw [← hpop]
  unfold jF at hj
  change (if F == w1Mask () then (ptRows F).length == 16 else
    (ptRows F).length * min 64 (popc F) ≤ 512 ||
      ((ptRows F).length * min 64 (popc F) ≤ 1024 && (ptRows F).length == 64 &&
        (ptRows F).any fun a => (ptRows F).any fun b => mulR a b != mulR b a)) = true at hj
  by_cases hFw : F = w1Mask ()
  · rw [if_pos (by rw [hFw]; exact beq_self_eq_true _), beq_iff_eq] at hj
    right
    exact ⟨by rw [← hFe, hFw], hj ▸ hle⟩
  · rw [if_neg (by rw [beq_iff_eq]; exact hFw)] at hj
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
      bne_iff_ne, ne_eq] at hj
    left
    rcases hj with h512 | ⟨⟨h1024, h64⟩, a, ha, b, hb, hab'⟩
    · exact (Nat.mul_le_mul_right _ hle).trans h512
    ·
      have hlt : Nat.card X < 64 := by
        rcases lt_or_eq_of_le (h64 ▸ hle) with h | h
        · exact h
        · exfalso
          obtain ⟨U, hU, rfl⟩ := hall (h.trans h64.symm) a ha
          obtain ⟨V, hV, rfl⟩ := hall (h.trans h64.symm) b hb
          apply hab'
          have e1 := linOfRows_rowsOf (U * V)
          have e2 := linOfRows_rowsOf (V * U)
          refine rows_eq (by simp [size_mulR, rowsOf_size]) (by simp [size_mulR, rowsOf_size])
            (lt_of_mem_mulR (rowsOf_lt U)) (lt_of_mem_mulR (rowsOf_lt V)) fun v => ?_
          rw [linOfRows_mulR, linOfRows_mulR, linOfRows_rowsOf, linOfRows_rowsOf,
            linOfRows_rowsOf, linOfRows_rowsOf, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply,
            hab U hU V hV]
      have hdvd : Nat.card X ∣ 2 ^ 8 := by
        have := Subgroup.card_dvd_of_le hX
        rwa [card_pGrp] at this
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have h32 : Nat.card X ≤ 32 := by
        rw [hk] at hlt ⊢
        have : k < 6 := by
          by_contra h6
          have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h6)
          omega
        have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this
      rw [h64] at h1024
      have hmin : min 64 (popc F) ≤ 16 := by omega
      calc Nat.card X * min 64 (popc F) ≤ 32 * 16 := Nat.mul_le_mul h32 hmin
        _ = 512 := by norm_num

end CFSG.Quasithin.H13.AS91.Two
