module

public import CFSG.Sporadic.Schreier.LySylow
public import CFSG.Sporadic.Schreier.LyGLQCertificate

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose] def gW : Array (List ℕ) := glqWords sTab

@[expose] def gA : List (ℕ × ℕ × ℕ) := glqAuts sTab gW

@[expose] def gP : List (ℕ × ℕ) := glqPairs sTab

theorem glq_parts : gW.size = 256 ∧ (∀ x < 256, ∀ k ∈ gW[x]!, k < 3) ∧
    (∀ x < 256, evalY sTab glqGens gW[x]! = x) ∧ gW[1]! = [0] ∧ gW[3]! = [1] ∧
    gW[5]! = [2] ∧ gA.length = 512 ∧
    (gA.filter fun y => isInvoT (fmapY sTab gW y)).length = 176 ∧
    (∀ p ∈ gP, isInv sTab p.1 = true ∧ isInv sTab p.2 = true ∧ p.1 ≠ p.2 ∧
      tm sTab p.1 p.2 = tm sTab p.2 p.1) ∧
    ∀ y ∈ gA, isInvoT (fmapY sTab gW y) = true →
      ∃ p ∈ gP, (fmapY sTab gW y)[p.1]! = p.1 ∧ (fmapY sTab gW y)[p.2]! = p.2 := by
  have h := ly_glq_certificate
  unfold glqCertificate glqWithGens glqWithEnum glqWithTable glqWithWords glqChecks at h
  rw [← csArr_def, show sylowGens csArr = syGenArr from rfl,
    show sylowBFS syGenArr 256 = sBFS from rfl,
    show mulTabOf 256 sBFS.2.1 sBFS.2.2.1 sBFS.2.2.2 = sTab from rfl,
    show glqWords sTab = gW from rfl, show glqAuts sTab gW = gA from rfl,
    show glqPairs sTab = gP from rfl] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, hlt⟩, hev⟩, h1⟩, h3⟩, h5⟩, hA⟩, hI⟩, hP⟩, hF⟩ := h
  refine ⟨hsz, fun x hx k hk => ?_, fun x hx => ?_, h1, h3, h5, hA, hI, fun p hp => ?_,
    fun y hy hinv => ?_⟩
  · have := (allIn_eq_true.1 hlt) x (Nat.zero_le _) hx
    rw [List.all_eq_true] at this
    simpa using this k hk
  · have := (allIn_eq_true.1 hev) x (Nat.zero_le _) hx
    simpa using this
  · have := (List.all_eq_true.1 hP) p hp
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    exact ⟨h1, h2, h3, h4⟩
  · have := (List.all_eq_true.1 hF) y hy
    simp only [Bool.or_eq_true, Bool.not_eq_true', hinv, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at this
    rcases this with h | h
    · exact absurd h (by decide)
    · exact h

@[expose] def sIdx (g : lyS) : ℕ := (sEquiv.symm g).val

theorem sIdx_lt (g : lyS) : sIdx g < 256 := (sEquiv.symm g).isLt

theorem sE_sIdx (g : lyS) : sE (sIdx g) = g := sEquiv.apply_symm_apply g

theorem sIdx_sE {i : ℕ} (hi : i < 256) : sIdx (sE i) = i :=
  sE_inj (sIdx_lt _) hi (sE_sIdx _)

theorem stm_lt {a b : ℕ} (ha : a < 256) (hb : b < 256) : stm a b < 256 :=
  mulTab_parts.1 a ha b hb

theorem sE_eq_one_iff {i : ℕ} (hi : i < 256) : sE i = 1 ↔ i = 0 := by
  constructor
  · intro h
    rw [← sE_zero] at h
    exact sE_inj hi (by norm_num) h
  · rintro rfl
    exact sE_zero

theorem stm_zero_right {a : ℕ} (ha : a < 256) : stm a 0 = a := by
  apply sE_inj (stm_lt ha (by norm_num)) ha
  rw [← sE_mul ha (by norm_num), sE_zero, mul_one]

theorem glqGens_pick {k : ℕ} (hk : k < 3) : pickY glqGens k < 256 := by
  interval_cases k <;> decide

theorem sE_evalY {y : ℕ × ℕ × ℕ} (hy : ∀ k < 3, pickY y k < 256) (w : List ℕ)
    (hw : ∀ k ∈ w, k < 3) :
    evalY sTab y w < 256 ∧ sE (evalY sTab y w) = (w.map fun k => sE (pickY y k)).prod := by
  induction w with
  | nil => exact ⟨by simp [evalY], by simp [evalY, sE_zero]⟩
  | cons k w ih =>
    obtain ⟨h1, h2⟩ := ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))
    have hk := hy k (hw k List.mem_cons_self)
    have e : evalY sTab y (k :: w) = stm (pickY y k) (evalY sTab y w) := rfl
    refine ⟨by rw [e]; exact stm_lt hk h1, ?_⟩
    rw [e, ← sE_mul hk h1, h2, List.map_cons, List.prod_cons]

@[expose] def autTriple (β : MulAut lyS) : ℕ × ℕ × ℕ :=
  (sIdx (β (sE 1)), sIdx (β (sE 3)), sIdx (β (sE 5)))

theorem autTriple_pick (β : MulAut lyS) {k : ℕ} (hk : k < 3) :
    pickY (autTriple β) k = sIdx (β (sE (pickY glqGens k))) := by
  interval_cases k <;> rfl

theorem autTriple_pick_lt (β : MulAut lyS) {k : ℕ} (hk : k < 3) : pickY (autTriple β) k < 256 := by
  rw [autTriple_pick β hk]
  exact sIdx_lt _

theorem evalY_autTriple (β : MulAut lyS) (w : List ℕ) (hw : ∀ k ∈ w, k < 3) :
    evalY sTab (autTriple β) w = sIdx (β (sE (evalY sTab glqGens w))) := by
  obtain ⟨h1, h2⟩ := sE_evalY (fun k hk => autTriple_pick_lt β hk) w hw
  obtain ⟨-, g2⟩ := sE_evalY (fun k hk => glqGens_pick hk) w hw
  apply sE_inj h1 (sIdx_lt _)
  rw [sE_sIdx, h2, g2, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp_apply]
  rw [autTriple_pick β (hw k hk), sE_sIdx]

theorem fmapY_get (y : ℕ × ℕ × ℕ) {x : ℕ} (hx : x < 256) :
    (fmapY sTab gW y)[x]! = evalY sTab y gW[x]! := by
  rw [fmapY, getElem!_pos _ x (by simp [hx]), Array.getElem_ofFn]

theorem fmapY_autTriple (β : MulAut lyS) {x : ℕ} (hx : x < 256) :
    (fmapY sTab gW (autTriple β))[x]! = sIdx (β (sE x)) := by
  rw [fmapY_get _ hx, evalY_autTriple β _ (glq_parts.2.1 x hx), glq_parts.2.2.1 x hx]

theorem isHomT_autTriple (β : MulAut lyS) : isHomT sTab (fmapY sTab gW (autTriple β)) = true := by
  unfold isHomT
  simp only [Bool.and_eq_true, allIn_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨fun x _ hx => ?_, fun x hx1 hx => ?_⟩, fun a _ ha b _ hb => ?_⟩
  · rw [fmapY_autTriple β hx]
    exact sIdx_lt _
  · rw [fmapY_autTriple β (by omega)]
    intro h0
    have h1 : β (sE x) = 1 := by rw [← sE_sIdx (β (sE x)), h0, sE_zero]
    rw [MulEquiv.map_eq_one_iff, sE_eq_one_iff (by omega)] at h1
    omega
  · rw [tm_sTab, fmapY_autTriple β (stm_lt ha hb), tm_sTab, fmapY_autTriple β ha,
      fmapY_autTriple β hb]
    apply sE_inj (sIdx_lt _) (stm_lt (sIdx_lt _) (sIdx_lt _))
    rw [sE_sIdx, ← sE_mul (sIdx_lt _) (sIdx_lt _), sE_sIdx, sE_sIdx, ← map_mul, sE_mul ha hb]

theorem tpow_sIdx_eq_zero (β : MulAut lyS) {x : ℕ} (hx : x < 256) (n : ℕ) :
    tpow sTab (sIdx (β (sE x))) n = 0 ↔ tpow sTab x n = 0 := by
  obtain ⟨h1, h2⟩ := sE_pow (sIdx_lt (β (sE x))) n
  obtain ⟨g1, g2⟩ := sE_pow hx n
  rw [← sE_eq_one_iff h1, ← sE_eq_one_iff g1, ← h2, ← g2, sE_sIdx, ← map_pow,
    MulEquiv.map_eq_one_iff]

theorem sigT_sIdx (β : MulAut lyS) {x : ℕ} (hx : x < 256) :
    sigT sTab (sIdx (β (sE x))) = sigT sTab x := by
  unfold sigT
  have h2 := tpow_sIdx_eq_zero β hx 2
  have h4 := tpow_sIdx_eq_zero β hx 4
  ext
  · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact h2
  · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact h4

theorem autTriple_mem_level (β : MulAut lyS) {k : ℕ} (hk : k < 3) :
    pickY (autTriple β) k ∈ glqLevel sTab k := by
  rw [glqLevel, List.mem_filter, autTriple_pick β hk]
  refine ⟨List.mem_range.2 (sIdx_lt _), ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨fun h0 => ?_, sigT_sIdx β (glqGens_pick hk)⟩
  have h1 : β (sE (pickY glqGens k)) = 1 := by
    rw [← sE_sIdx (β (sE (pickY glqGens k))), h0, sE_zero]
  rw [MulEquiv.map_eq_one_iff, sE_eq_one_iff (glqGens_pick hk)] at h1
  interval_cases k <;> simp [pickY, glqGens] at h1

theorem glqTests_lt : ∀ w ∈ glqTests, ∀ k ∈ w, k < 3 := by decide

theorem autTriple_mem_cands (β : MulAut lyS) : autTriple β ∈ glqCands sTab := by
  rw [glqCands, List.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [prodL, List.mem_flatMap, List.mem_map]
    exact ⟨_, autTriple_mem_level β (k := 0) (by norm_num), _,
      ⟨_, autTriple_mem_level β (k := 1) (by norm_num), _,
        autTriple_mem_level β (k := 2) (by norm_num), rfl⟩, rfl⟩
  · rw [List.all_eq_true]
    intro w hw
    rw [beq_iff_eq, evalY_autTriple β w (glqTests_lt w hw),
      sigT_sIdx β (sE_evalY (fun k hk => glqGens_pick hk) w (glqTests_lt w hw)).1]

theorem autTriple_mem (β : MulAut lyS) : autTriple β ∈ gA := by
  rw [gA, glqAuts, List.mem_filter]
  exact ⟨autTriple_mem_cands β, isHomT_autTriple β⟩

theorem isHomT_spec {f : Array ℕ} (h : isHomT sTab f = true) :
    (∀ x < 256, f[x]! < 256) ∧ (∀ x, 1 ≤ x → x < 256 → f[x]! ≠ 0) ∧
      ∀ a < 256, ∀ b < 256, f[stm a b]! = stm f[a]! f[b]! := by
  unfold isHomT at h
  simp only [Bool.and_eq_true, allIn_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun x hx => h1 x (Nat.zero_le _) (by omega), fun x hx1 hx => h2 x hx1 hx,
    fun a ha b hb => ?_⟩
  have := h3 a (Nat.zero_le _) (by omega) b (Nat.zero_le _) (by omega)
  rw [tm_sTab, tm_sTab] at this
  exact this

theorem isHomT_zero {f : Array ℕ} (h : isHomT sTab f = true) : f[0]! = 0 := by
  obtain ⟨h1, -, h3⟩ := isHomT_spec h
  have e := h3 0 (by norm_num) 0 (by norm_num)
  rw [mulTab_parts.2.1 0 (by norm_num)] at e
  have h0 := h1 0 (by norm_num)
  have : sE f[0]! = 1 := by
    have e2 := sE_mul h0 h0
    rw [← e] at e2
    calc sE f[0]! = sE f[0]! * sE f[0]! * (sE f[0]!)⁻¹ := by group
      _ = 1 := by rw [e2, mul_inv_cancel]
  exact (sE_eq_one_iff h0).1 this

@[expose] def homOfT (f : Array ℕ) (h : isHomT sTab f = true) : lyS →* lyS where
  toFun g := sE f[sIdx g]!
  map_one' := by
    rw [show sIdx 1 = 0 from by rw [← sE_zero, sIdx_sE (by norm_num)], isHomT_zero h, sE_zero]
  map_mul' g g' := by
    have e : sIdx (g * g') = stm (sIdx g) (sIdx g') := by
      rw [← sIdx_sE (stm_lt (sIdx_lt g) (sIdx_lt g')), ← sE_mul (sIdx_lt g) (sIdx_lt g'),
        sE_sIdx, sE_sIdx]
    rw [e, (isHomT_spec h).2.2 _ (sIdx_lt g) _ (sIdx_lt g'),
      sE_mul ((isHomT_spec h).1 _ (sIdx_lt g)) ((isHomT_spec h).1 _ (sIdx_lt g'))]

theorem homOfT_apply (f : Array ℕ) (h : isHomT sTab f = true) (g : lyS) :
    homOfT f h g = sE f[sIdx g]! := rfl

theorem homOfT_injective (f : Array ℕ) (h : isHomT sTab f = true) :
    Function.Injective (homOfT f h) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [homOfT_apply, sE_eq_one_iff ((isHomT_spec h).1 _ (sIdx_lt g))] at hg
  by_contra hne
  have h1 : sIdx g ≠ 0 := fun h0 => hne (by rw [← sE_sIdx g, h0, sE_zero])
  exact (isHomT_spec h).2.1 _ (Nat.one_le_iff_ne_zero.2 h1) (sIdx_lt g) hg

@[expose] def autOfT (f : Array ℕ) (h : isHomT sTab f = true) : MulAut lyS :=
  MulEquiv.ofBijective (homOfT f h)
    ⟨homOfT_injective f h, Finite.surjective_of_injective (homOfT_injective f h)⟩

theorem autOfT_sE (f : Array ℕ) (h : isHomT sTab f = true) {x : ℕ} (hx : x < 256) :
    autOfT f h (sE x) = sE f[x]! := by
  show homOfT f h (sE x) = _
  rw [homOfT_apply, sIdx_sE hx]

theorem gA_isHom {y : ℕ × ℕ × ℕ} (hy : y ∈ gA) : isHomT sTab (fmapY sTab gW y) = true := by
  rw [gA, glqAuts, List.mem_filter] at hy
  exact hy.2

theorem gA_lt {y : ℕ × ℕ × ℕ} (hy : y ∈ gA) : ∀ k < 3, pickY y k < 256 := by
  rw [gA, glqAuts, List.mem_filter, glqCands, List.mem_filter] at hy
  obtain ⟨⟨hy, -⟩, -⟩ := hy
  simp only [prodL, List.mem_flatMap, List.mem_map] at hy
  obtain ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩ := hy
  intro k hk
  rw [glqLevel, List.mem_filter, List.mem_range] at ha hb hc
  interval_cases k
  · exact ha.1
  · exact hb.1
  · exact hc.1

theorem autTriple_autOfT {y : ℕ × ℕ × ℕ} (hy : y ∈ gA) :
    autTriple (autOfT (fmapY sTab gW y) (gA_isHom hy)) = y := by
  have hlt := gA_lt hy
  have key : ∀ x < 256, sIdx (autOfT (fmapY sTab gW y) (gA_isHom hy) (sE x)) =
      evalY sTab y gW[x]! := by
    intro x hx
    rw [autOfT_sE _ _ hx, sIdx_sE ((isHomT_spec (gA_isHom hy)).1 x hx), fmapY_get y hx]
  have hev : ∀ k < 3, evalY sTab y [k] = pickY y k := fun k hk =>
    stm_zero_right (hlt k hk)
  have e1 := key 1 (by norm_num)
  have e3 := key 3 (by norm_num)
  have e5 := key 5 (by norm_num)
  rw [glq_parts.2.2.2.1, hev 0 (by norm_num)] at e1
  rw [glq_parts.2.2.2.2.1, hev 1 (by norm_num)] at e3
  rw [glq_parts.2.2.2.2.2.1, hev 2 (by norm_num)] at e5
  show (sIdx _, sIdx _, sIdx _) = y
  rw [e1, e3, e5]
  obtain ⟨y1, y3, y5⟩ := y
  rfl

theorem autOfT_autTriple (β : MulAut lyS) :
    autOfT (fmapY sTab gW (autTriple β)) (gA_isHom (autTriple_mem β)) = β := by
  apply MulEquiv.ext
  intro g
  rw [← sE_sIdx g, autOfT_sE _ _ (sIdx_lt g), fmapY_autTriple β (sIdx_lt g), sE_sIdx]

@[expose] def autEquiv : MulAut lyS ≃ {y // y ∈ gA} where
  toFun β := ⟨autTriple β, autTriple_mem β⟩
  invFun y := autOfT (fmapY sTab gW y.1) (gA_isHom y.2)
  left_inv β := autOfT_autTriple β
  right_inv y := Subtype.ext (autTriple_autOfT y.2)

theorem card_subtype_mem_list {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) :
    Nat.card {x // x ∈ l} = l.length := by
  rw [← List.toFinset_card_of_nodup hl, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm)

theorem gA_nodup : gA.Nodup := by
  rw [gA, glqAuts, glqCands]
  apply List.Nodup.filter
  apply List.Nodup.filter
  have hl : ∀ k, (glqLevel sTab k).Nodup := fun k => (List.nodup_range).filter _
  exact List.Nodup.product (hl 0) (List.Nodup.product (hl 1) (hl 2))

theorem card_mulAut_lyS : Nat.card (MulAut lyS) = 512 := by
  rw [Nat.card_congr autEquiv, card_subtype_mem_list gA_nodup, glq_parts.2.2.2.2.2.2.1]

theorem sq_eq_one_iff_isInvoT (β : MulAut lyS) :
    β ^ 2 = 1 ↔ isInvoT (fmapY sTab gW (autTriple β)) = true := by
  unfold isInvoT
  rw [allIn_eq_true]
  constructor
  · intro h x _ hx
    rw [beq_iff_eq, fmapY_autTriple β hx, fmapY_autTriple β (sIdx_lt _), sE_sIdx]
    have := DFunLike.congr_fun h (sE x)
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply] at this
    rw [this, sIdx_sE hx]
  · intro h
    apply MulEquiv.ext
    intro g
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    have hx := h (sIdx g) (Nat.zero_le _) (by simpa using sIdx_lt g)
    rw [beq_iff_eq, fmapY_autTriple β (sIdx_lt g), fmapY_autTriple β (sIdx_lt _), sE_sIdx,
      sE_sIdx] at hx
    rw [← sE_sIdx (β (β g)), hx, sE_sIdx]

theorem card_involutory : Nat.card {β : MulAut lyS // β ^ 2 = 1} = 176 := by
  have e : {β : MulAut lyS // β ^ 2 = 1} ≃
      {y // y ∈ gA.filter fun y => isInvoT (fmapY sTab gW y)} :=
    { toFun := fun β => ⟨autTriple β.1, List.mem_filter.2 ⟨autTriple_mem β.1,
        (sq_eq_one_iff_isInvoT β.1).1 β.2⟩⟩
      invFun := fun y => ⟨autOfT (fmapY sTab gW y.1) (gA_isHom (List.mem_filter.1 y.2).1), by
        rw [sq_eq_one_iff_isInvoT, autTriple_autOfT (List.mem_filter.1 y.2).1]
        exact (List.mem_filter.1 y.2).2⟩
      left_inv := fun β => Subtype.ext (autOfT_autTriple β.1)
      right_inv := fun y => Subtype.ext (autTriple_autOfT (List.mem_filter.1 y.2).1) }
  rw [Nat.card_congr e, card_subtype_mem_list (gA_nodup.filter _), glq_parts.2.2.2.2.2.2.2.1]

@[expose] def fourSub {G : Type*} [Group G] (u v : G) (hu : u * u = 1) (hv : v * v = 1)
    (huv : u * v = v * u) : Subgroup G where
  carrier := {1, u, v, u * v}
  mul_mem' := by
    have e1 : u * (u * v) = v := by rw [← mul_assoc, hu, one_mul]
    have e2 : v * (u * v) = u := by rw [← mul_assoc, ← huv, mul_assoc, hv, mul_one]
    have e3 : u * v * u = v := by rw [huv, mul_assoc, hu, mul_one]
    have e4 : u * v * v = u := by rw [mul_assoc, hv, mul_one]
    have e5 : u * v * (u * v) = 1 := by
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [← huv]
        _ = (u * u) * (v * v) := by group
        _ = 1 := by rw [hu, hv, one_mul]
    have e6 : v * u = u * v := huv.symm
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, hu, hv, e1, e2,
        e3, e4, e5, e6, true_or, or_true]
  one_mem' := Or.inl rfl
  inv_mem' := by
    have iu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have iv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
    have iuv : (u * v)⁻¹ = u * v := by rw [mul_inv_rev, iu, iv, huv]
    rintro a (rfl | rfl | rfl | rfl) <;>
      simp only [inv_one, iu, iv, iuv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        or_true]

theorem gP_lt {p : ℕ × ℕ} (hp : p ∈ gP) : p.1 < 256 ∧ p.2 < 256 := by
  rw [gP, glqPairs, List.mem_filter] at hp
  obtain ⟨hp, -⟩ := hp
  simp only [prodL, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  rw [List.mem_filter, List.mem_range] at ha hb
  exact ⟨ha.1, hb.1⟩

theorem fixed_pair (β : MulAut lyS) (hβ : β ^ 2 = 1) :
    ∃ u v : lyS, u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ β u = u ∧
      β v = v := by
  obtain ⟨p, hp, ha, hb⟩ := glq_parts.2.2.2.2.2.2.2.2.2 _ (autTriple_mem β)
    ((sq_eq_one_iff_isInvoT β).1 hβ)
  obtain ⟨hia, hib, hne, hcomm⟩ := glq_parts.2.2.2.2.2.2.2.2.1 p hp
  obtain ⟨halt, hblt⟩ := gP_lt hp
  simp only [isInv, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, tm_sTab] at hia hib
  rw [tm_sTab, tm_sTab] at hcomm
  refine ⟨sE p.1, sE p.2, by rw [sE_mul halt halt, hia.2, sE_zero],
    by rw [sE_mul hblt hblt, hib.2, sE_zero], by rw [sE_mul halt hblt, sE_mul hblt halt, hcomm],
    fun h => hia.1 ((sE_eq_one_iff halt).1 h), fun h => hib.1 ((sE_eq_one_iff hblt).1 h),
    fun h => hne (sE_inj halt hblt h), ?_, ?_⟩
  · rw [fmapY_autTriple β halt] at ha
    rw [← sE_sIdx (β (sE p.1)), ha]
  · rw [fmapY_autTriple β hblt] at hb
    rw [← sE_sIdx (β (sE p.2)), hb]

theorem fixed_four_group (β : MulAut lyS) (hβ : β ^ 2 = 1) :
    ∃ E : Subgroup lyS, (∀ x ∈ E, β x = x) ∧ CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 4 := by
  classical
  obtain ⟨p, hp, ha, hb⟩ := glq_parts.2.2.2.2.2.2.2.2.2 _ (autTriple_mem β)
    ((sq_eq_one_iff_isInvoT β).1 hβ)
  obtain ⟨hia, hib, hne, hcomm⟩ := glq_parts.2.2.2.2.2.2.2.2.1 p hp
  obtain ⟨halt, hblt⟩ := gP_lt hp
  simp only [isInv, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, tm_sTab] at hia hib
  rw [tm_sTab, tm_sTab] at hcomm
  have hu : sE p.1 * sE p.1 = 1 := by rw [sE_mul halt halt, hia.2, sE_zero]
  have hv : sE p.2 * sE p.2 = 1 := by rw [sE_mul hblt hblt, hib.2, sE_zero]
  have huv : sE p.1 * sE p.2 = sE p.2 * sE p.1 := by
    rw [sE_mul halt hblt, sE_mul hblt halt, hcomm]
  have hu1 : sE p.1 ≠ 1 := fun h => hia.1 ((sE_eq_one_iff halt).1 h)
  have hv1 : sE p.2 ≠ 1 := fun h => hib.1 ((sE_eq_one_iff hblt).1 h)
  have hne' : sE p.1 ≠ sE p.2 := fun h => hne (sE_inj halt hblt h)
  have hfa : β (sE p.1) = sE p.1 := by
    rw [fmapY_autTriple β halt] at ha
    rw [← sE_sIdx (β (sE p.1)), ha]
  have hfb : β (sE p.2) = sE p.2 := by
    rw [fmapY_autTriple β hblt] at hb
    rw [← sE_sIdx (β (sE p.2)), hb]
  obtain ⟨E, hE⟩ : ∃ E : Subgroup lyS, ∀ x, x ∈ E ↔
      x = 1 ∨ x = sE p.1 ∨ x = sE p.2 ∨ x = sE p.1 * sE p.2 :=
    ⟨fourSub (sE p.1) (sE p.2) (by exact hu) (by exact hv) (by exact huv), fun _ => Iff.rfl⟩
  have e5 : sE p.1 * sE p.2 * (sE p.1 * sE p.2) = 1 := by
    calc sE p.1 * sE p.2 * (sE p.1 * sE p.2) = sE p.1 * (sE p.2 * sE p.1) * sE p.2 := by group
      _ = sE p.1 * (sE p.1 * sE p.2) * sE p.2 := by rw [← huv]
      _ = (sE p.1 * sE p.1) * (sE p.2 * sE p.2) := by group
      _ = 1 := by rw [hu, hv, one_mul]
  have hcu : ∀ x ∈ E, x * sE p.1 = sE p.1 * x := by
    intro x hx
    rcases (hE x).1 hx with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · rfl
    · exact huv.symm
    · rw [mul_assoc, ← huv]
  have hcv : ∀ x ∈ E, x * sE p.2 = sE p.2 * x := by
    intro x hx
    rcases (hE x).1 hx with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact huv
    · rfl
    · calc sE p.1 * sE p.2 * sE p.2 = sE p.2 * sE p.1 * sE p.2 := by rw [huv]
        _ = sE p.2 * (sE p.1 * sE p.2) := by group
  have hea : CFSG.IsElementaryAbelian 2 E := by
    apply mk_ea
    · intro x hx y hy
      rcases (hE y).1 hy with rfl | rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · exact hcu x hx
      · exact hcv x hx
      · calc x * (sE p.1 * sE p.2) = (x * sE p.1) * sE p.2 := (mul_assoc _ _ _).symm
          _ = (sE p.1 * x) * sE p.2 := by rw [hcu x hx]
          _ = sE p.1 * (x * sE p.2) := mul_assoc _ _ _
          _ = sE p.1 * (sE p.2 * x) := by rw [hcv x hx]
          _ = sE p.1 * sE p.2 * x := (mul_assoc _ _ _).symm
    · intro x hx
      rcases (hE x).1 hx with rfl | rfl | rfl | rfl
      · exact one_mul 1
      · exact hu
      · exact hv
      · exact e5
  have h1 : sE p.1 * sE p.2 ≠ 1 := by
    intro h
    apply hne'
    calc sE p.1 = sE p.1 * (sE p.2 * sE p.2) := by rw [hv, mul_one]
      _ = (sE p.1 * sE p.2) * sE p.2 := by rw [mul_assoc]
      _ = sE p.2 := by rw [h, one_mul]
  have h2 : sE p.1 * sE p.2 ≠ sE p.1 := fun h => hv1 (by
    calc sE p.2 = (sE p.1)⁻¹ * (sE p.1 * sE p.2) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have h3 : sE p.1 * sE p.2 ≠ sE p.2 := fun h => hu1 (by
    calc sE p.1 = (sE p.1 * sE p.2) * (sE p.2)⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have hcard : Nat.card E = 4 := by
    have e : (E : Set lyS) = (({1, sE p.1, sE p.2, sE p.1 * sE p.2} : Finset lyS) : Set lyS) := by
      ext x
      rw [SetLike.mem_coe, hE x]
      simp
    rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h3.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne', h2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hu1, Ne.symm hv1, Ne.symm h1⟩
  refine ⟨E, fun x hx => ?_, hea, hcard⟩
  rcases (hE x).1 hx with rfl | rfl | rfl | rfl
  · exact map_one β
  · exact hfa
  · exact hfb
  · rw [map_mul, hfa, hfb]

theorem closure_e135 : Subgroup.closure ({sylowElt 1, sylowElt 3, sylowElt 5} : Set J) = lyS := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · rw [sylowElt_eq (by norm_num)]; exact sTree_mem 1 (by norm_num)
    · rw [sylowElt_eq (by norm_num)]; exact sTree_mem 3 (by norm_num)
    · rw [sylowElt_eq (by norm_num)]; exact sTree_mem 5 (by norm_num)
  · intro g hg
    obtain ⟨x, hx, hxg⟩ := exists_sE ⟨g, hg⟩
    have hw := glq_parts.2.1 x hx
    obtain ⟨-, h2⟩ := sE_evalY (fun k hk => glqGens_pick hk) gW[x]! hw
    rw [glq_parts.2.2.1 x hx] at h2
    have hg' : g = ((sE x : lyS) : J) := by rw [hxg]
    rw [hg', h2, ← Subgroup.coe_subtype, map_list_prod]
    apply Subgroup.list_prod_mem
    intro z hz
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hk3 := hw k hk
    apply Subgroup.subset_closure
    interval_cases k
    · left; rw [sylowElt_eq (by norm_num), ← sE_val (by norm_num)]; rfl
    · right; left; rw [sylowElt_eq (by norm_num), ← sE_val (by norm_num)]; rfl
    · right; right; rw [sylowElt_eq (by norm_num), ← sE_val (by norm_num)]; rfl

theorem sylow_involutory_automorphisms_fixed_four_group :
    Nat.card (MulAut lyS) = 512 ∧ Nat.card {β : MulAut lyS // β ^ 2 = 1} = 176 ∧
    (∀ β : MulAut lyS, β ^ 2 = 1 → ∃ E : Subgroup lyS, (∀ x ∈ E, β x = x) ∧
      CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4) ∧
    Subgroup.closure ({sylowElt 1, sylowElt 3, sylowElt 5} : Set J) = lyS :=
  ⟨card_mulAut_lyS, card_involutory, fixed_four_group, closure_e135⟩

end CFSG.Sporadic.LySchreier
