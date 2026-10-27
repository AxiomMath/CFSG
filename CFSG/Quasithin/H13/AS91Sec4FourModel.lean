module

public import CFSG.Quasithin.H13.AS91Sec4Five
public import Certificates.Certificate89405

public section

namespace CFSG.Quasithin.H13.AS91.Two

open Subgroup CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb
open scoped Pointwise

theorem zGrpOK44_spec :
    gensOKb gZRows = true ∧ gensOKb p2Rows = true ∧
      (∀ g ∈ gZRows, (Std.HashSet.ofList (enumGrp (stab1Gens ()))).contains g = true ∧
        appN g 192 = 192) ∧
      appN ((stab1Gens ()).getD 4 idR) 192 ≠ 192 ∧
      idR ∈ enumGrp gZRows ∧ closedCheck gZRows (enumGrp gZRows) = true ∧
      (enumGrp gZRows).dedup.length = 1920 ∧
      idR ∈ enumGrp p2Rows ∧ closedCheck p2Rows (enumGrp p2Rows) = true ∧
      (enumGrp p2Rows).dedup.length = 16 ∧
      (∀ p ∈ p2Rows, (Std.HashSet.ofList (enumGrp gZRows)).contains p = true) ∧
      (∀ x ∈ enumGrp p2Rows, ∀ y ∈ enumGrp p2Rows, mulR x y = mulR y x) ∧
      ∀ x ∈ enumGrp p2Rows, mulR x x = idR := by
  have h := Certificates.certificate89405
  simp only [ok44, Bool.and_eq_true] at h
  have h1 := h.1.1
  simp only [zGrpOK44, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.contains_iff_mem] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩, g10⟩, g11⟩, g12⟩, g13⟩ := h1
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩

theorem zW5OK44_spec :
    (w5 ()).length = 5 ∧
      (∀ p ∈ p2Rows, ∀ m ∈ w5 (), mapsInto p m (codesOf m) = true) ∧
      ∀ x ∈ enumGrp gZRows, (∀ m ∈ w5 (), mapsInto x m (codesOf m) = true) →
        (Std.HashSet.ofList (enumGrp p2Rows)).contains x = true := by
  have h := Certificates.certificate89405
  simp only [ok44, Bool.and_eq_true] at h
  have h2 := h.1.2
  simp only [zW5OK44, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.all_map,
    Function.comp_def, Bool.or_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨hl, hp⟩, hx⟩ := h2
  refine ⟨hl, fun p hp' m hm => hp p hp' m hm, fun x hxX hxW => ?_⟩
  rcases hx x hxX with h' | h'
  · obtain ⟨m, hm, hmf⟩ := List.all_eq_false.mp h'
    exact absurd (hxW m hm) (by simpa using hmf)
  · exact h'

theorem zPerpOK44_spec :
    ∀ x ∈ enumGrp p2Rows, appN x 4 = 4 → appN x 24 = 24 → x = idR := by
  have h := Certificates.certificate89405
  simp only [ok44, Bool.and_eq_true] at h
  have h3 := h.2
  simp only [zPerpOK44, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', perpWit,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_false_iff, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq] at h3
  intro x hx h4 h24
  rcases h3 x hx with (h' | h') | h'
  · exact absurd h4 h'
  · exact absurd h24 h'
  · exact h'

abbrev gZGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp gZRows

abbrev p2Grp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp p2Rows

@[expose] def gammaZ : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  stabIn (stabIn nGrp (vecOf 3)) (vecOf 192)

theorem mem_gammaZ {U : V12 ≃ₗ[ZMod 2] V12} :
    U ∈ gammaZ ↔ U ∈ nGrp ∧ U (vecOf 3) = vecOf 3 ∧ U (vecOf 192) = vecOf 192 := by
  rw [gammaZ, mem_stabIn, mem_stabIn, and_assoc]

theorem gensOK_gZ : GensOK gZRows :=
  gensOK_of_gensOKb zGrpOK44_spec.1

theorem gensOK_p2 : GensOK p2Rows :=
  gensOK_of_gensOKb zGrpOK44_spec.2.1

theorem gZGrp_le_stab1 :
    gZGrp ≤ genGrp (stab1Gens ()) :=
  genGrp_le_of_rep fun g hg =>
    rep_of_contains (stabOK_spec Data41.stabOK42_spec.1).1 (zGrpOK44_spec.2.2.1 g hg).1

theorem fix192_gZ {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ gZGrp) :
    U (vecOf 192) = vecOf 192 := by
  have hU' : U ∈ Submonoid.closure (GenSet gZRows) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction (motive := fun U _ => U (vecOf 192) = vecOf 192) ?_ ?_ ?_ hU'
  · rintro x ⟨r, hr, hx⟩
    rw [hx, ← vecOf_appN, (zGrpOK44_spec.2.2.1 r hr).2]
  · rfl
  · intro x y _ _ hx hy
    rw [LinearEquiv.mul_apply, hy, hx]

theorem card_gZGrp : Nat.card gZGrp = 1920 := by
  obtain ⟨-, -, -, -, hid, hc, hn, -⟩ := zGrpOK44_spec
  rw [card_genGrp (enumGrp_sound gensOK_gZ) hid hc, hn]

theorem card_p2Grp : Nat.card p2Grp = 16 := by
  obtain ⟨-, -, -, -, -, -, -, hid, hc, hn, -⟩ := zGrpOK44_spec
  rw [card_genGrp (enumGrp_sound gensOK_p2) hid hc, hn]

theorem p2Grp_le_gZGrp : p2Grp ≤ gZGrp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hP, -⟩ := zGrpOK44_spec
  exact genGrp_le_of_rep fun p hp => rep_of_contains gensOK_gZ (hP p hp)

theorem p2Grp_comm {x y : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ p2Grp)
    (hy : y ∈ p2Grp) : x * y = y * x := by
  obtain ⟨-, -, -, -, -, -, -, hid, hc, -, -, hcomm, -⟩ := zGrpOK44_spec
  obtain ⟨rx, hrx, hxr⟩ := complete hid hc x hx
  obtain ⟨ry, hry, hyr⟩ := complete hid hc y hy
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxr, hyr, hxr, hyr, ← linOfRows_mulR,
    ← linOfRows_mulR, hcomm rx hrx ry hry]

theorem p2Grp_sq {x : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ p2Grp) :
    x * x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hid, hc, -, -, -, hsq⟩ := zGrpOK44_spec
  obtain ⟨rx, hrx, hxr⟩ := complete hid hc x hx
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, hxr, hxr, ← linOfRows_mulR, hsq rx hrx, linOfRows_idR]
  rfl

theorem exists_stab1_moves :
    ∃ U ∈ genGrp (stab1Gens ()), U (vecOf 192) ≠ vecOf 192 := by
  obtain ⟨-, -, -, h4, -⟩ := zGrpOK44_spec
  have hgs := (stabOK_spec Data41.stabOK42_spec.1).1
  have hlen : 4 < (stab1Gens ()).length := by simp [stab1Gens, stab1Words]
  rw [List.getD_eq_getElem _ _ hlen] at h4
  have hmem := List.getElem_mem hlen
  refine ⟨eqvOf _ _ (hgs _ hmem).2.2.1 (hgs _ hmem).2.2.2, gen_mem hgs hmem, fun he => h4 ?_⟩
  rw [eqvOf_apply, ← vecOf_appN] at he
  exact vecOf_inj (appN_lt (okRows_lt (hgs _ hmem).1) _) (by norm_num) he

theorem gZGrp_eq_gammaZ
    (hst : stabIn nGrp (vecOf 3) = genGrp (stab1Gens ())) : gZGrp = gammaZ := by
  have hle : gZGrp ≤ gammaZ := fun U hU => by
    have h1 : U ∈ stabIn nGrp (vecOf 3) := by rw [hst]; exact gZGrp_le_stab1 hU
    obtain ⟨hUN, hU3⟩ := mem_stabIn.mp h1
    exact mem_gammaZ.mpr ⟨hUN, hU3, fix192_gZ hU⟩
  have hle' : gammaZ ≤ genGrp (stab1Gens ()) := by
    rw [← hst]
    exact fun U hU => mem_stabIn.mpr ⟨(mem_gammaZ.mp hU).1, (mem_gammaZ.mp hU).2.1⟩
  have h3840 : Nat.card (genGrp (stab1Gens ())) = 3840 :=
    (stabOK_spec Data41.stabOK42_spec.1).2.2.1
  have hne : Nat.card gammaZ ≠ 3840 := by
    intro he
    obtain ⟨U, hU, hU192⟩ := exists_stab1_moves
    have heq := Subgroup.eq_of_le_of_card_ge hle' (by rw [he, h3840])
    rw [← heq] at hU
    exact hU192 (mem_gammaZ.mp hU).2.2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle'
  rw [h3840] at hk
  have hge := Subgroup.card_le_of_le hle
  rw [card_gZGrp] at hge
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_gZGrp]
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

@[expose] def W5 : Set (Set V12) := setOfMask '' {m | m ∈ w5 ()}

theorem mem_w5 {m : ℕ} : m ∈ w5 () ↔ m ∈ w1Orbit () ∧ m.testBit 3 = true ∧
    m.testBit 192 = true ∧ m.testBit 195 = true := by
  simp [w5, List.mem_filter, and_assoc]

theorem ncard_W5 :
    W5.ncard = 5 := by
  obtain ⟨-, hnd, -⟩ := orbitOK45_spec
  have hnd5 : (w5 ()).Nodup := hnd.filter _
  have e : {m | m ∈ w5 ()} = ((w5 ()).toFinset : Set ℕ) := by
    ext m
    simp
  have hinj : Set.InjOn setOfMask ((w5 ()).toFinset : Set ℕ) := fun m hm m' hm' he =>
    eq_of_setOfMask_eq (isMask_of_mem_w1Orbit (mem_w5.mp (by simpa using hm)).1)
      (isMask_of_mem_w1Orbit (mem_w5.mp (by simpa using hm')).1) he
  rw [W5, e, hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd5,
    zW5OK44_spec.1]

theorem vecOf_mem_setOfMask {m n : ℕ} (hn : n < 4096) :
    vecOf n ∈ setOfMask m ↔ m.testBit n = true := by
  rw [mem_setOfMask, codeOf_vecOf hn]

theorem image_mul (U V : V12 ≃ₗ[ZMod 2] V12) (W : Set V12) : ⇑(U * V) '' W = ⇑U '' (⇑V '' W) := by
  rw [Set.image_image]
  rfl

theorem image_mem_W5 {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ gammaZ)
    {W : Set V12} (hW : W ∈ W5) : ⇑U '' W ∈ W5 := by
  obtain ⟨m, hm, rfl⟩ := hW
  obtain ⟨hmO, h3, h192, h195⟩ := mem_w5.mp hm
  obtain ⟨hUN, hU3, hU192⟩ := mem_gammaZ.mp hU
  obtain ⟨V, hV, hmV⟩ := exists_of_mem_w1Orbit hmO
  obtain ⟨m', hm', hm'e⟩ := exists_mem_w1Orbit (mul_mem hUN hV)
  have hm'U : setOfMask m' = ⇑U '' setOfMask m := by rw [hm'e, hmV, image_mul]
  have hU195 : U (vecOf 195) = vecOf 195 := by
    rw [show (195 : ℕ) = 3 ^^^ 192 by decide, vecOf_xor, map_add, hU3, hU192]
  have hbit : ∀ n < 4096, m.testBit n = true → U (vecOf n) = vecOf n → m'.testBit n = true :=
    fun n hn hb hUn => by
      rw [← vecOf_mem_setOfMask hn, hm'U, ← hUn]
      exact Set.mem_image_of_mem _ ((vecOf_mem_setOfMask hn).mpr hb)
  exact ⟨m', mem_w5.mpr ⟨hm', hbit 3 (by norm_num) h3 hU3, hbit 192 (by norm_num) h192 hU192,
    hbit 195 (by norm_num) h195 hU195⟩, hm'U⟩

theorem image_eq_of_mapsInto {U : V12 ≃ₗ[ZMod 2] V12} {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096)
    (hU : ∀ v, U v = linOfRows r v) {m : ℕ} (h : mapsInto r m (codesOf m) = true) :
    ⇑U '' setOfMask m = setOfMask m := by
  have hsub : ⇑U '' setOfMask m ⊆ setOfMask m := by
    rintro _ ⟨v, hv, rfl⟩
    have hc : codeOf v ∈ codesOf m := by
      simp only [codesOf, List.mem_filter, List.mem_range]
      exact ⟨codeOf_lt v, hv⟩
    have e : codeOf (U v) = appN r (codeOf v) := by
      rw [hU, ← vecOf_codeOf v, ← vecOf_appN, codeOf_vecOf (appN_lt hr _), codeOf_vecOf
        (codeOf_lt v)]
    rw [mem_setOfMask, e]
    exact List.all_eq_true.mp h _ hc
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_image_of_injective _ U.injective])
    (Set.toFinite _)

theorem p2Grp_fix_W5 {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ p2Grp)
    {W : Set V12} (hW : W ∈ W5) : ⇑U '' W = W := by
  obtain ⟨m, hm, rfl⟩ := hW
  have hU' : U ∈ Submonoid.closure (GenSet p2Rows) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction
    (motive := fun (U : V12 ≃ₗ[ZMod 2] V12) _ => ⇑U '' setOfMask m = setOfMask m) ?_ ?_ ?_ hU'
  · rintro x ⟨r, hr, hx⟩
    exact image_eq_of_mapsInto (okRows_lt (gensOK_p2 r hr).1) hx (zW5OK44_spec.2.1 r hr m hm)
  · exact Set.image_id' _
  · intro x y _ _ hx hy
    rw [image_mul, hy, hx]

theorem mem_p2Grp_of_fix {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ gZGrp) (hfix : ∀ W ∈ W5, ⇑U '' W = W) : U ∈ p2Grp := by
  obtain ⟨-, -, -, -, hid, hc, -⟩ := zGrpOK44_spec
  obtain ⟨x, hxX, hUx⟩ := complete hid hc U hU
  have hxok : ∀ y ∈ x, y < 4096 := okRows_lt (enumGrp_sound gensOK_gZ x hxX).1
  have hmaps : ∀ m ∈ w5 (), mapsInto x m (codesOf m) = true := by
    intro m hm
    refine List.all_eq_true.mpr fun c hc => ?_
    simp only [codesOf, List.mem_filter, List.mem_range] at hc
    have hfm := hfix _ ⟨m, hm, rfl⟩
    have hv : U (vecOf c) ∈ setOfMask m := by
      rw [← hfm]
      exact Set.mem_image_of_mem _ ((vecOf_mem_setOfMask hc.1).mpr hc.2)
    rw [hUx, ← vecOf_appN, vecOf_mem_setOfMask (appN_lt hxok _)] at hv
    exact hv
  obtain ⟨-, V, hV, hVx⟩ := rep_of_contains gensOK_p2 (zW5OK44_spec.2.2 x hxX hmaps)
  rw [show U = V from LinearEquiv.ext fun v => (hUx v).trans (hVx v).symm]
  exact hV

@[expose] def w5Action : SubMulAction ↥gammaZ (Set V12) where
  carrier := W5
  smul_mem' U W hW := by
    change ⇑(U : V12 ≃ₗ[ZMod 2] V12) '' W ∈ W5
    exact image_mem_W5 U.2 hW

theorem finite_W5 : W5.Finite := (List.finite_toSet (w5 ())).image setOfMask

instance : Finite ↥(w5Action) := finite_W5.to_subtype

theorem card_w5Action :
    Nat.card ↥(w5Action) = 5 := by
  rw [← ncard_W5, ← Nat.card_coe_set_eq]
  rfl

@[expose] noncomputable def chi :
    ↥gammaZ →* Equiv.Perm (Fin 5) :=
  (Finite.equivFinOfCardEq card_w5Action).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom ↥gammaZ ↥(w5Action))

theorem chi_eq_one_iff
    (U : ↥gammaZ) : chi U = 1 ↔ ∀ W ∈ W5, ⇑(U : V12 ≃ₗ[ZMod 2] V12) '' W = W := by
  rw [chi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  constructor
  · intro h1 W hW
    have := congrArg (fun σ : Equiv.Perm ↥(w5Action) => ((σ ⟨W, hW⟩ : ↥(w5Action)) : Set V12)) h1
    exact this
  · intro h1
    ext ⟨W, hW⟩ : 1
    exact Subtype.ext (h1 W hW)

theorem chi_ker
    (hst : stabIn nGrp (vecOf 3) = genGrp (stab1Gens ()))
    (U : ↥gammaZ) : chi U = 1 ↔ (U : V12 ≃ₗ[ZMod 2] V12) ∈ p2Grp := by
  rw [chi_eq_one_iff]
  constructor
  · intro h1
    exact mem_p2Grp_of_fix (by rw [gZGrp_eq_gammaZ hst]; exact U.2) h1
  · intro h1 W hW
    exact p2Grp_fix_W5 h1 hW

theorem chi_surjective
    (hst : stabIn nGrp (vecOf 3) = genGrp (stab1Gens ())) :
    Function.Surjective chi := by
  have hker : chi.ker = p2Grp.subgroupOf gammaZ := by
    ext U
    rw [MonoidHom.mem_ker, chi_ker hst, mem_subgroupOf]
  have hcard : Nat.card ↥gammaZ = 1920 := by rw [← gZGrp_eq_gammaZ hst, card_gZGrp]
  have h1 := Subgroup.card_mul_index chi.ker
  rw [Subgroup.index_ker, hker, card_subgroupOf_eq, inf_of_le_right
    (by rw [← gZGrp_eq_gammaZ hst]; exact p2Grp_le_gZGrp), card_p2Grp, hcard] at h1
  have h120 : Nat.card chi.range = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from rfl]
    omega
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ h120

theorem perm5_eq_one_of_commute (σ : Equiv.Perm (Fin 5))
    (h1 : σ * Equiv.swap 0 1 = Equiv.swap 0 1 * σ) (h2 : σ * finRotate 5 = finRotate 5 * σ) :
    σ = 1 := by
  revert σ
  decide +kernel

theorem eq_one_of_fix_perp {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ p2Grp) (h4 : U (vecOf 4) = vecOf 4) (h24 : U (vecOf 24) = vecOf 24) : U = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hid, hc, -⟩ := zGrpOK44_spec
  obtain ⟨r, hr, hUr⟩ := complete hid hc U hU
  have hok := okRows_lt (enumGrp_sound gensOK_p2 r hr).1
  have e4 : appN r 4 = 4 :=
    vecOf_inj (appN_lt hok _) (by norm_num) (by rw [vecOf_appN, ← hUr, h4])
  have e24 : appN r 24 = 24 :=
    vecOf_inj (appN_lt hok _) (by norm_num) (by rw [vecOf_appN, ← hUr, h24])
  have hr1 := zPerpOK44_spec r hr e4 e24
  refine LinearEquiv.ext fun v => ?_
  rw [hUr, hr1, linOfRows_idR]
  rfl

end CFSG.Quasithin.H13.AS91.Two
