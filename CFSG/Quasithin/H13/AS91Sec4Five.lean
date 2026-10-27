module

public import CFSG.Quasithin.H13.AS91Sec4Three
public import Certificates.Certificate89404

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22 Module
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb
open scoped Pointwise

namespace Two

theorem testBit_or_one_shiftLeft (acc k y : ℕ) :
    (acc ||| 1 <<< k).testBit y = (acc.testBit y || decide (k = y)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_foldl_or (L : List ℕ) (acc y : ℕ) :
    (L.foldl (fun acc x => acc ||| 1 <<< x) acc).testBit y = true ↔
      acc.testBit y = true ∨ y ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih, testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro ((h | rfl) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr h

theorem testBit_maskOf (L : List ℕ) (y : ℕ) : (maskOf L).testBit y = true ↔ y ∈ L := by
  rw [maskOf, testBit_foldl_or]
  simp

theorem testBit_foldl_img (g : Array ℕ) (m : ℕ) (L : List ℕ) (acc y : ℕ) :
    (L.foldl (fun acc x => if m.testBit x then acc ||| 1 <<< appN g x else acc) acc).testBit y =
        true ↔ acc.testBit y = true ∨ ∃ x ∈ L, m.testBit x = true ∧ appN g x = y := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    by_cases hx : m.testBit x = true
    · rw [if_pos hx, testBit_or_one_shiftLeft, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((h | h) | ⟨x', hx', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, hx, h⟩
        · exact Or.inr ⟨x', List.mem_cons_of_mem x hx', h⟩
      · rintro (h | ⟨x', hx', h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hx' with rfl | hx'
          · exact Or.inl (Or.inr h.2)
          · exact Or.inr ⟨x', hx', h⟩
    · rw [if_neg hx]
      constructor
      · rintro (h | ⟨x', hx', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x', List.mem_cons_of_mem x hx', h⟩
      · rintro (h | ⟨x', hx', h⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hx' with rfl | hx'
          · exact absurd h.1 hx
          · exact Or.inr ⟨x', hx', h⟩

theorem testBit_imgMask (g : Array ℕ) (m y : ℕ) :
    (imgMask g m).testBit y = true ↔ ∃ x < 4096, m.testBit x = true ∧ appN g x = y := by
  rw [imgMask, testBit_foldl_img]
  simp [List.mem_range]

@[expose] def setOfMask (m : ℕ) : Set V12 := {v | m.testBit (codeOf v) = true}

theorem mem_setOfMask {m : ℕ} {v : V12} : v ∈ setOfMask m ↔ m.testBit (codeOf v) = true :=
  Iff.rfl

theorem setOfMask_imgMask {g : Array ℕ} (hg : ∀ x ∈ g, x < 4096) (m : ℕ) :
    setOfMask (imgMask g m) = linOfRows g '' setOfMask m := by
  ext v
  rw [mem_setOfMask, testBit_imgMask]
  constructor
  · rintro ⟨x, hx, hmx, hgx⟩
    refine ⟨vecOf x, by rw [mem_setOfMask, codeOf_vecOf hx]; exact hmx, ?_⟩
    rw [← vecOf_appN, hgx, vecOf_codeOf]
  · rintro ⟨u, hu, rfl⟩
    have e : linOfRows g u = vecOf (appN g (codeOf u)) := by rw [vecOf_appN, vecOf_codeOf]
    exact ⟨codeOf u, codeOf_lt u, hu, by rw [e, codeOf_vecOf (appN_lt hg _)]⟩

@[expose] def IsMask (m : ℕ) : Prop := ∀ i, 4096 ≤ i → m.testBit i = false

theorem isMask_maskOf {L : List ℕ} (hL : ∀ x ∈ L, x < 4096) : IsMask (maskOf L) := by
  intro i hi
  by_contra hne
  have := (testBit_maskOf L i).mp (Bool.not_eq_false _ ▸ hne)
  exact absurd (hL i this) (not_lt.mpr hi)

theorem isMask_imgMask {g : Array ℕ} (hg : ∀ x ∈ g, x < 4096) (m : ℕ) : IsMask (imgMask g m) := by
  intro i hi
  by_contra hne
  obtain ⟨x, -, -, rfl⟩ := (testBit_imgMask g m i).mp (Bool.not_eq_false _ ▸ hne)
  exact absurd (appN_lt hg x) (not_lt.mpr hi)

theorem eq_of_setOfMask_eq {m m' : ℕ} (hm : IsMask m) (hm' : IsMask m')
    (h : setOfMask m = setOfMask m') : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 4096
  · have e : vecOf i ∈ setOfMask m ↔ vecOf i ∈ setOfMask m' := by rw [h]
    rw [mem_setOfMask, mem_setOfMask, codeOf_vecOf hi] at e
    exact Bool.eq_iff_iff.mpr e
  · rw [hm i (not_lt.mp hi), hm' i (not_lt.mp hi)]

abbrev W1 : Set V12 := setOfMask (w1Mask ())

theorem orbitOK45_spec :
    (w1Orbit ()).length = 77 ∧ (w1Orbit ()).Nodup ∧
      ∀ m ∈ w1Orbit (), ∀ g ∈ nGensI, imgMask g m ∈ w1Orbit () := by
  have h := Certificates.certificate89404
  simp only [ok45, orbitOK45, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
  exact ⟨h1, h2, h3⟩

theorem okRows_lt {g : Array ℕ} (hg : okRows g = true) : ∀ x ∈ g, x < 4096 :=
  (okRows_spec hg).2

theorem image_mul_eq {x y : V12 ≃ₗ[ZMod 2] V12} {r : Array ℕ} (hx : ∀ v, x v = linOfRows r v)
    (W : Set V12) : linOfRows r '' (y '' W) = (x * y) '' W := by
  rw [Set.image_image]
  congr 1
  funext v
  rw [LinearEquiv.mul_apply, hx]

theorem exists_of_mem_w1Orbit {m : ℕ} (hm : m ∈ w1Orbit ()) :
    ∃ U ∈ nGrp, setOfMask m = U '' W1 := by
  unfold w1Orbit at hm
  refine bfsClosure_inv _ _ (P := fun m => ∃ U ∈ nGrp, setOfMask m = U '' W1) ?_ _ _ _ _ ?_
    (by simp) m hm
  · intro f hf m ⟨U, hU, hmU⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hgok, -, h1, h2⟩ := gensOK_nGensI g hg
    refine ⟨eqvOf g (invR g) h1 h2 * U, mul_mem (gen_mem gensOK_nGensI hg) hU, ?_⟩
    rw [setOfMask_imgMask (okRows_lt hgok), hmU]
    exact image_mul_eq (fun v => eqvOf_apply g (invR g) h1 h2 v) W1
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨1, one_mem _, by simp⟩

theorem isMask_of_mem_w1Orbit {m : ℕ} (hm : m ∈ w1Orbit ()) : IsMask m := by
  unfold w1Orbit at hm
  refine bfsClosure_inv _ _ (P := IsMask) ?_ _ _ _ _ ?_ (by simp) m hm
  · intro f hf m _
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact isMask_imgMask (okRows_lt (gensOK_nGensI g hg).1) m
  · simp only [List.mem_singleton, forall_eq]
    exact isMask_maskOf (by decide)

theorem mem_bfsClosure {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ)) :
    ∀ (fuel : ℕ) (frontier : List σ) (seen : Std.HashSet κ) (visited : List σ),
      ∀ s ∈ frontier ++ visited, s ∈ bfsClosure key fs fuel frontier seen visited
  | 0, _, _, _ => fun _ hs => hs
  | fuel + 1, frontier, seen, visited => fun s hs => by
    simp only [bfsClosure]
    split_ifs
    · exact hs
    · exact mem_bfsClosure key fs fuel _ _ _ s (List.mem_append_right _ hs)

theorem w1Mask_mem_w1Orbit : w1Mask () ∈ w1Orbit () := by
  unfold w1Orbit
  exact mem_bfsClosure _ _ _ _ _ _ _ (by simp)

theorem exists_mem_w1Orbit {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ nGrp) : ∃ m ∈ w1Orbit (), setOfMask m = U '' W1 := by
  obtain ⟨-, -, hcl⟩ := orbitOK45_spec
  have hU' : U ∈ Submonoid.closure (GenSet nGensI) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hU
  refine Submonoid.closure_induction_left (s := GenSet nGensI)
    (motive := fun U _ => ∃ m ∈ w1Orbit (), setOfMask m = U '' W1) ?_ ?_ hU'
  · exact ⟨w1Mask (), w1Mask_mem_w1Orbit, by simp⟩
  · rintro x ⟨r, hr, hx⟩ y _ ⟨m, hm, hmy⟩
    refine ⟨imgMask r m, hcl m hm r hr, ?_⟩
    rw [setOfMask_imgMask (okRows_lt (gensOK_nGensI r hr).1), hmy]
    exact image_mul_eq hx W1

theorem orbit_W1 :
    MulAction.orbit ↥nGrp W1 = setOfMask '' {m | m ∈ w1Orbit ()} := by
  ext S
  constructor
  · rintro ⟨U, rfl⟩
    obtain ⟨m, hm, hmU⟩ := exists_mem_w1Orbit U.2
    exact ⟨m, hm, by rw [hmU]; rfl⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨U, hU, hmU⟩ := exists_of_mem_w1Orbit hm
    exact ⟨⟨U, hU⟩, by rw [hmU]; rfl⟩

theorem ncard_orbit_W1 :
    (MulAction.orbit ↥nGrp W1).ncard = 77 := by
  obtain ⟨hlen, hnd, -⟩ := orbitOK45_spec
  have e : {m | m ∈ w1Orbit ()} = ((w1Orbit ()).toFinset : Set ℕ) := by
    ext m
    simp
  have hinj : Set.InjOn setOfMask ((w1Orbit ()).toFinset : Set ℕ) := fun m hm m' hm' he =>
    eq_of_setOfMask_eq (isMask_of_mem_w1Orbit (by simpa using hm))
      (isMask_of_mem_w1Orbit (by simpa using hm')) he
  rw [orbit_W1, e, hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]

@[expose] def g13Grp : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  (MulAction.stabilizer ↥nGrp W1).map nGrp.subtype

theorem mem_g13Grp {U : V12 ≃ₗ[ZMod 2] V12} : U ∈ g13Grp ↔ U ∈ nGrp ∧ U '' W1 = W1 := by
  constructor
  · rintro ⟨⟨V, hV⟩, hVs, rfl⟩
    exact ⟨hV, hVs⟩
  · rintro ⟨hU, hUW⟩
    exact ⟨⟨U, hU⟩, hUW, rfl⟩

theorem g13Grp_le_nGrp : g13Grp ≤ nGrp := fun _ hU => (mem_g13Grp.mp hU).1

theorem card_g13Grp_mul :
    Nat.card g13Grp * 77 = Nat.card nGrp := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥nGrp W1)
  rw [MulAction.index_stabilizer, ncard_orbit_W1] at h1
  rw [g13Grp, Subgroup.card_map_of_injective nGrp.subtype_injective, h1]

abbrev pGrp : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp pRows

theorem pOK45_spec :
    gensOKb pRows = true ∧
      (∀ p ∈ pRows, (Std.HashSet.ofList (enumGrp (stab1Gens ()))).contains p = true) ∧
      idR ∈ enumGrp pRows ∧ closedCheck pRows (enumGrp pRows) = true ∧
      (enumGrp pRows).dedup.length = 256 ∧
      (∀ n ∈ List.range 4096, (pRows.all fun g => appN g n == n) = (n == 0 || n == 3)) ∧
      (∀ g ∈ pRows, ∀ n ∈ zList, appN g n ∈ zList) ∧
      (∀ g ∈ pRows, imgMask g (w1Mask ()) = w1Mask ()) ∧
      imgMask omegaRows (w1Mask ()) = w1Mask () := by
  have h := Certificates.certificate89404
  simp only [ok45, pOK45, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩⟩ := h
  exact ⟨by simpa [gensOKb, List.all_eq_true] using h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem gensOK_pRows : GensOK pRows :=
  gensOK_of_gensOKb pOK45_spec.1

theorem pGrp_le_stab1 :
    pGrp ≤ genGrp (stab1Gens ()) :=
  genGrp_le_of_rep fun p hp =>
    rep_of_contains (stabOK_spec Data41.stabOK42_spec.1).1 (pOK45_spec.2.1 p hp)

theorem pGrp_le_nGrp :
    pGrp ≤ nGrp :=
  pGrp_le_stab1.trans (Data41.genGrp_stabGens_le (ws := stab1Words) (by decide))

theorem card_pGrp : Nat.card pGrp = 256 := by
  obtain ⟨-, -, hid, hc, hn, -⟩ := pOK45_spec
  rw [card_genGrp (enumGrp_sound gensOK_pRows) hid hc, hn]

theorem fix_codes {n : ℕ} (hn : n < 4096) :
    (∀ g ∈ pRows, appN g n = n) ↔ n = 0 ∨ n = 3 := by
  have h := pOK45_spec.2.2.2.2.2.1 n (List.mem_range.2 hn)
  have h' : (pRows.all fun g => appN g n == n) = true ↔ (n == 0 || n == 3) = true := by rw [h]
  simpa [List.all_eq_true] using h'

theorem pGrp_fix_three {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ pGrp) : U (vecOf 3) = vecOf 3 := by
  have h3 : ∀ g ∈ pRows, appN g 3 = 3 := (fix_codes (by norm_num)).mpr (Or.inr rfl)
  have := invariant_of_gens gensOK_pRows (P := fun n => n == 3) (fun n _ hn g hg => by
    simp only [beq_iff_eq] at hn ⊢
    subst hn
    exact h3 g hg) U hU 3 (by norm_num) (by decide)
  simp only [beq_iff_eq] at this
  rw [← vecOf_codeOf (U (vecOf 3)), this]

theorem eq_of_fix_pGrp {v : V12} (hv : ∀ U ∈ pGrp, U v = v) :
    v = 0 ∨ v = vecOf 3 := by
  have hg : ∀ g ∈ pRows, appN g (codeOf v) = codeOf v := by
    intro g hg
    obtain ⟨hok, -, h1, h2⟩ := gensOK_pRows g hg
    have hfix := hv _ (gen_mem gensOK_pRows hg)
    rw [eqvOf_apply] at hfix
    have e : vecOf (appN g (codeOf v)) = vecOf (codeOf v) := by
      rw [vecOf_appN, vecOf_codeOf, hfix]
    exact vecOf_inj (appN_lt (okRows_lt hok) _) (codeOf_lt v) e
  rcases (fix_codes (codeOf_lt v)).mp hg with h0 | h3
  · left
    rw [← vecOf_codeOf v, h0, vecOf_zero]
  · right
    rw [← vecOf_codeOf v, h3]

theorem inZ_pGrp {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ pGrp)
    {v : V12} (hv : InZ v) : InZ (U v) := by
  have hz := pOK45_spec.2.2.2.2.2.2.1
  have := invariant_of_gens gensOK_pRows (P := inZb) (fun n _ hn g hg => by
    simp only [inZb, List.contains_iff_mem] at hn ⊢
    exact hz g hg n hn) U hU (codeOf v) (codeOf_lt v) hv
  rwa [vecOf_codeOf] at this

theorem image_W1_of_imgMask {g : Array ℕ} (hg : ∀ x ∈ g, x < 4096)
    (h : imgMask g (w1Mask ()) = w1Mask ()) : linOfRows g '' W1 = W1 := by
  rw [← setOfMask_imgMask hg, h]

theorem pGrp_le_g13Grp :
    pGrp ≤ g13Grp := by
  refine (Subgroup.closure_le _).2 ?_
  rintro l ⟨r, hr, hl⟩
  refine mem_g13Grp.mpr ⟨pGrp_le_nGrp (Subgroup.subset_closure ⟨r, hr, hl⟩), ?_⟩
  have e : (⇑l : V12 → V12) = ⇑(linOfRows r) := funext hl
  rw [e]
  exact image_W1_of_imgMask (okRows_lt (gensOK_pRows r hr).1) (pOK45_spec.2.2.2.2.2.2.2.1 r hr)

theorem theta0_image_W1 : ⇑theta0 '' W1 = W1 := by
  have h := image_W1_of_imgMask (okRows_lt okRows_omegaRows) pOK45_spec.2.2.2.2.2.2.2.2
  have e : ⇑(linOfRows omegaRows) = ⇑theta0 := funext linOfRows_omegaRows
  rwa [e] at h

end Two

variable {G : Type} [Group G] [Finite G]

theorem pre_le_pre {S : Setting G} {K K' : Subgroup S.O} (hle : K ≤ K') : pre S K ≤ pre S K' :=
  Subgroup.map_mono (Subgroup.comap_mono hle)

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem comap_le_Mbar
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hK : K ≤ Two.nGrp) : K.comap D.Φo ≤ h.setting.Mbar := by
  intro m hm
  have hmN : D.Φo m ∈ Two.nGrp := hK hm
  rw [← D.map_Mbar_Φo hOut hTw] at hmN
  obtain ⟨m', hm', he⟩ := hmN
  rwa [D.Φo_injective he] at hm'

theorem card_comap
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hK : K ≤ Two.nGrp) : Nat.card (K.comap D.Φo) = Nat.card K := by
  rw [← Subgroup.card_map_of_injective D.Φo_injective, Subgroup.map_comap_eq_self]
  intro U hU
  have hUN := hK hU
  rw [← D.map_Mbar_Φo hOut hTw] at hUN
  obtain ⟨m, -, rfl⟩ := hUN
  exact ⟨m, rfl⟩

include D in
theorem card_M : Nat.card h.setting.M = 2 ^ 13 * 2661120 := by
  rw [card_eq_card_quotient_mul_card_subgroup h.setting.ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange h.setting.ρ).toEquiv, h.setting.ker_ρ,
    ← h.setting.card_QG_eq_card_Q, D.card_QG, mul_comm]
  congr 1
  exact D.card_Mbar

@[expose] noncomputable def g13bar : Subgroup h.setting.O := Two.g13Grp.comap D.Φo

@[expose] noncomputable def G13 : Subgroup G := pre h.setting D.g13bar

theorem card_g13bar
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    Nat.card D.g13bar = 34560 := by
  have h1 := Two.card_g13Grp_mul
  rw [D.card_nGrp hOut hTw] at h1
  rw [g13bar, D.card_comap hOut hTw Two.g13Grp_le_nGrp]
  omega

theorem card_G13
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    Nat.card D.G13 = 2 ^ 13 * 3 * (2 ^ 4 * 720) := by
  rw [G13, card_pre (K := D.g13bar) (D.comap_le_Mbar hOut hTw Two.g13Grp_le_nGrp),
    D.card_g13bar hOut hTw, D.card_QG]
  norm_num

theorem G13_le : D.G13 ≤ H z := pre_le_M _

theorem θ_mem_g13bar
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    D.θ ∈ D.g13bar := by
  show D.Φo D.θ ∈ Two.g13Grp
  refine Two.mem_g13Grp.mpr ⟨D.Φo_mem_nGrp hOut hTw D.θ_mem, ?_⟩
  rcases D.Φ_θ with hθ | hθ
  · have e : ⇑(D.Φo D.θ) = ⇑theta0 := funext hθ
    rw [e, Two.theta0_image_W1]
  · have e : ⇑(D.Φo D.θ) = ⇑theta0 ∘ ⇑theta0 := funext hθ
    rw [e, Set.image_comp, Two.theta0_image_W1, Two.theta0_image_W1]

theorem QX_le
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    Q z ⊔ zpowers (D.c : G) ≤ D.G13 := by
  rw [← h.setting_QG, sup_eq_pre D.ρ_c]
  exact pre_le_pre (zpowers_le.mpr (D.θ_mem_g13bar hOut hTw))

@[expose] noncomputable def Tbar : Subgroup h.setting.O := Two.pGrp.comap D.Φo

@[expose] noncomputable def T : Subgroup G := pre h.setting D.Tbar

theorem card_T
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) : Nat.card D.T = 2 ^ 21 := by
  rw [T, card_pre (K := D.Tbar) (D.comap_le_Mbar hOut hTw Two.pGrp_le_nGrp), Tbar,
    D.card_comap hOut hTw Two.pGrp_le_nGrp, Two.card_pGrp, D.card_QG]
  norm_num

theorem isPGroup_T
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) : IsPGroup 2 D.T :=
  IsPGroup.of_card (n := 21) (D.card_T hOut hTw)

theorem T_le_G13 :
    D.T ≤ D.G13 :=
  pre_le_pre (Subgroup.comap_mono Two.pGrp_le_g13Grp)

theorem QG_le_T : h.setting.QG ≤ D.T := QG_le_pre _

theorem eq_T_of_le
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) {T' : Subgroup G} (hT' : IsPGroup 2 T') (hle : D.T ≤ T') :
    T' = D.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : h.setting.QG ≤ T' := D.QG_le_T.trans hle
  have hzT : h.setting.z ∈ T' := hQT h.setting.z_mem_QG
  have hT'M : T' ≤ h.setting.M := by
    have : Nontrivial T' :=
      ⟨⟨⟨h.setting.z, hzT⟩, 1, fun he => h.setting.z_ne_one (congrArg Subtype.val he)⟩⟩
    have hcen := hT'.center_nontrivial
    obtain ⟨w, hw⟩ := exists_ne (1 : center T')
    have hwc : ∀ p ∈ T', ((w : T') : G) * p = p * (w : T') := fun p hp => by
      have := mem_center_iff.mp w.2 ⟨p, hp⟩
      exact (congrArg Subtype.val this).symm
    have hwM : ((w : T') : G) ∈ h.setting.M := h.setting.mem_M_iff.mpr (hwc _ hzT)
    have hwQ := h.setting.mem_QG_of_commute hwM fun x hx => hwc x (hQT hx)
    rcases h.setting.eq_one_or_z_of_commute hwQ (fun y hy => hwc y (hQT hy)) with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hw
    · intro p hp
      have := hwc p hp
      rw [h1] at this
      exact h.setting.mem_M_iff.mpr this.symm
  obtain ⟨k, hk⟩ := hT'.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 ^ 21 * 10395 := by
    have := Subgroup.card_dvd_of_le hT'M
    rw [D.card_M, hk] at this
    norm_num at this ⊢
    exact this
  have hk21 : 2 ^ k ∣ 2 ^ 21 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 10395)).dvd_of_dvd_mul_right hdvd
  have hcard : Nat.card T' ≤ Nat.card D.T := by
    rw [hk, D.card_T hOut hTw]
    exact Nat.le_of_dvd (by positivity) hk21
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

@[expose] noncomputable def sylowT
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) : Sylow 2 G where
  toSubgroup := D.T
  isPGroup' := D.isPGroup_T hOut hTw
  is_maximal' := fun hQ hle => D.eq_T_of_le hOut hTw hQ hle

theorem center_T : (center D.T).map D.T.subtype = zpowers z := by
  have hzT : z ∈ D.T := D.QG_le_T h.setting.z_mem_QG
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxc : ∀ y ∈ D.T, (x : G) * y = y * x := fun y hy => by
      have := mem_center_iff.mp hx ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    have hxM : (x : G) ∈ h.setting.M := h.setting.mem_M_iff.mpr (hxc z hzT)
    have hxQ := h.setting.mem_QG_of_commute hxM fun y hy => hxc y (D.QG_le_T hy)
    rcases h.setting.eq_one_or_z_of_commute hxQ (fun y hy => hxc y (D.QG_le_T hy)) with h1 | h1
    · change (x : G) ∈ zpowers z
      rw [h1]
      exact one_mem _
    · change (x : G) ∈ zpowers z
      rw [h1]
      exact mem_zpowers _
  · rw [zpowers_le]
    refine ⟨⟨z, hzT⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact h.setting.mem_M_iff.mp (pre_le_M _ g.2)

theorem fix_T
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) (v : h.setting.Qt) :
    (∀ t : h.setting.M, (t : G) ∈ D.T →
      (h.setting.ρ t : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v = v) ↔
      v = 0 ∨ v = h.setting.cl (D.rep 3) := by
  constructor
  · intro hv
    have hfix : ∀ U ∈ Two.pGrp, U (D.ψV v) = D.ψV v := by
      intro U hU
      have hUN := Two.pGrp_le_nGrp hU
      rw [← D.map_Mbar_Φo hOut hTw] at hUN
      obtain ⟨m, hmM, rfl⟩ := hUN
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hmM
      rw [Φo_apply_ψV, hv t (mem_pre_of_rho t hU)]
    rcases Two.eq_of_fix_pGrp hfix with h0 | h3
    · left
      exact D.ψV.injective (by rw [h0, map_zero])
    · right
      exact D.ψV.injective (by rw [h3, ψV_cl_rep])
  · rintro (rfl | rfl) t ht
    · exact map_zero _
    · have hρ : h.setting.ρ t ∈ D.Tbar := rho_mem_of_mem_pre ht t.2
      apply D.ψV.injective
      rw [← Φo_apply_ψV, ψV_cl_rep]
      exact Two.pGrp_fix_three hρ

theorem T_le_normalizer
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G}
    (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE) :
    D.T ≤ normalizer (Zinf (h := h) g₁ s₀ : Set G) := by
  intro t ht
  obtain ⟨htM, hρ⟩ := mem_pre.mp ht
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨hyQ, hyZ⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hy
  refine (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mpr ⟨h.setting.conj_mem_QG htM hyQ, ?_⟩
  rw [← h.setting.ρ_cl ⟨t, htM⟩ hyQ, ← Φo_apply_ψV]
  exact Two.inZ_pGrp hρ hyZ

end Data41

end CFSG.Quasithin.H13.AS91
