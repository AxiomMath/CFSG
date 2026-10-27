module

public import CFSG.Timmesfeld.Moufang.J2
public import CFSG.Timmesfeld.Moufang.P3Check
public import CFSG.Timmesfeld.Moufang.P3MatCheck

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open CFSG.Sporadic.Bridge.J2 (seedGroup uA uB val_wordProd_of_lwordL le_card_seedGroup nativeEquiv)
open CFSG.Timmesfeld.Moufang.J2 (genL_wf unitGen unitGen_val unitGen_inv nativeGens
  coe_signedProd_nativeGens nativeGens_relators signedProd_comp)

section Generic

variable {G : Type*} [Group G]

theorem lineGens_self {α : Type*} {n : ℕ} (y : Fin (n + 2) → α) :
    lineGens (y 0) (y 1) (fun i => y (i.addNat 2)) = y := by
  funext j
  unfold lineGens
  split_ifs with h1 h2
  · exact congrArg y (Fin.ext (by rw [Fin.val_zero]; omega))
  · exact congrArg y (Fin.ext (by rw [Fin.val_one]; omega))
  · exact congrArg y (Fin.ext (by rw [Fin.val_addNat]; dsimp only; omega))

theorem lineConfig_of_signedProd {n : ℕ} {ov : Bool} {d c : G} {x : Fin n → G}
    (h : ∀ w ∈ lineRels n ov, signedProd (lineGens d c x) w = 1) : LineConfig d c x := by
  have hbase : ∀ w ∈ [[letterD, letterD], [letterC, letterC],
      (List.replicate 5 [letterD, letterC]).flatten], signedProd (lineGens d c x) w = 1 :=
    fun w hw => h w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw)))
  have hline : ∀ i : Fin n, ∀ w ∈ [[letterX i, letterX i], [letterD, letterX i, letterD, letterX i],
      (List.replicate 3 [letterC, letterX i]).flatten,
      (List.replicate 5 [letterC, letterD, letterX i]).flatten],
      signedProd (lineGens d c x) w = 1 := fun i w hw =>
    h w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨i, List.mem_finRange i, hw⟩))))
  have hpair : ∀ i j : Fin n, i < j →
      signedProd (lineGens d c x) [letterX i, letterX j, letterX i, letterX j, letterD] = 1 :=
    fun i j hij => h _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨i, List.mem_finRange i,
        List.mem_filterMap.2 ⟨j, List.mem_finRange j, by simp [hij]⟩⟩)))
  have hd2 : d * d = 1 := by simpa using hbase [letterD, letterD] (by simp)
  have hc2 : c * c = 1 := by simpa using hbase [letterC, letterC] (by simp)
  have hx2 : ∀ i, x i * x i = 1 := fun i => by simpa using hline i [letterX i, letterX i] (by simp)
  have hpq : ∀ i j : Fin n, i < j → (x i * x j) ^ 2 = d := by
    intro i j hij
    have := hpair i j hij
    simp only [signedProd_letterD, signedProd_letterX, signedProd_nil, mul_one] at this
    rw [← inv_eq_of_mul_eq_one_right hd2, eq_inv_iff_mul_eq_one, ← this, pow_two]
    group
  refine ⟨hd2, hc2, hx2, ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · have := hbase (List.replicate 5 [letterD, letterC]).flatten (by simp)
    rw [signedProd_replicate] at this
    simpa using this
  · have := hline i [letterD, letterX i, letterD, letterX i] (by simp)
    simp only [signedProd_letterD, signedProd_letterX, signedProd_nil, mul_one] at this
    rw [commute_iff_mul_sq_eq_one hd2 (hx2 i), pow_two, mul_assoc]
    exact this
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hpq i j hlt
    · have h1 := hpq j i hgt
      have hinv : x i * x j = (x j * x i)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hx2 i), inv_eq_of_mul_eq_one_right (hx2 j)]
      rw [hinv, inv_pow, h1, inv_eq_of_mul_eq_one_right hd2]
  · have := hline i (List.replicate 3 [letterC, letterX i]).flatten (by simp)
    rw [signedProd_replicate] at this
    simpa using this
  · have := hline i (List.replicate 5 [letterC, letterD, letterX i]).flatten (by simp)
    rw [signedProd_replicate] at this
    simpa using this

theorem lineConfig_presented (n : ℕ) (ov : Bool) :
    LineConfig (PresentedGroup.of (rels := wordRels (lineRels n ov)) 0) (PresentedGroup.of 1)
      (fun i => PresentedGroup.of (i.addNat 2)) :=
  lineConfig_of_signedProd (ov := ov) (fun w hw => by
    rw [lineGens_self]
    exact signedProd_of_eq_one hw)

theorem commutator_presented_eq_top {n : ℕ} (hn : 2 ≤ n) (ov : Bool) :
    commutator (PresentedGroup (wordRels (lineRels n ov))) = ⊤ := by
  refine (lineConfig_presented n ov).commutator_eq_top hn ?_
  rw [← range_lineGens, lineGens_self, PresentedGroup.closure_range_of]

end Generic

namespace P3

abbrev Pres : Type := PresentedGroup (wordRels (lineRels 3 false))

@[expose] def emb2 : Fin 4 → Fin 5 := Fin.castLE (by norm_num)

theorem map_lineRels_two :
    ∀ w ∈ lineRels 2 false, (w.map fun l => (emb2 l.1, l.2)) ∈ lineRels 3 false := by
  decide +kernel

noncomputable def fromA6 : A6.Pres →* Pres :=
  wordsHom (lineRels 2 false) (fun j => PresentedGroup.of (emb2 j)) (fun w hw => by
    rw [show (fun j => (PresentedGroup.of (emb2 j) : Pres)) = PresentedGroup.of ∘ emb2 from rfl,
      signedProd_comp]
    exact signedProd_of_eq_one (map_lineRels_two w hw))

noncomputable abbrev sub : Subgroup Pres := fromA6.range

theorem card_sub_le : Finite sub ∧ Nat.card sub ≤ 1080 := by
  obtain ⟨hfin, hcard⟩ := A6.card_pres_le
  exact ⟨Finite.of_surjective _ fromA6.rangeRestrict_surjective,
    (Nat.card_le_card_of_surjective _ fromA6.rangeRestrict_surjective).trans hcard⟩

@[expose] def subWords : List (List (Fin 5 × Bool)) :=
  [[(0, true)], [(1, true)], [(2, true)], [(3, true)]]

theorem codes_subWords : codes subWords = [[0], [2], [4], [6]] := by decide

theorem subWords_mem :
    ∀ w ∈ subWords, PresentedGroup.mk (wordRels (lineRels 3 false)) (FreeGroup.mk w) ∈ sub := by
  intro w hw
  simp only [subWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨PresentedGroup.of 0, by rw [fromA6, wordsHom_of]; rfl⟩
  · exact ⟨PresentedGroup.of 1, by rw [fromA6, wordsHom_of]; rfl⟩
  · exact ⟨PresentedGroup.of 2, by rw [fromA6, wordsHom_of]; rfl⟩
  · exact ⟨PresentedGroup.of 3, by rw [fromA6, wordsHom_of]; rfl⟩

theorem index_sub_le : sub.FiniteIndex ∧ sub.index ≤ 1120 := by
  have h := index_le_of_facts_presented (H := sub) (N := 1120) (F := 5600)
    (fx := P3Data.fx) (fc := P3Data.fc) (fy := P3Data.fy) (kind := P3Data.kind)
    (wi := P3Data.wi) (fs := P3Data.fs) (ft := P3Data.ft) (fo := P3Data.fo)
    (refs := P3Data.refs) (pl := P3Data.pl) (ffi := P3Data.ffi) (live := P3Data.live)
    (lineRels 3 false) subWords P3Data.words (fun w hw => ⟨w, hw, rfl⟩) subWords_mem
    (by decide +kernel) P3Data.live_zero (by norm_num)
    (by rw [codes_subWords]; exact P3Data.facts_all) P3Data.cover_all
  rw [P3Data.liveCount_eq] at h
  exact h

theorem card_pres_le : Finite Pres ∧ Nat.card Pres ≤ 1209600 := by
  obtain ⟨hfi, hidx⟩ := index_sub_le
  obtain ⟨hfin, hcard⟩ := card_sub_le
  have h := sub.card_mul_index
  have hpos : 0 < Nat.card sub := Nat.card_pos
  have hne : Nat.card Pres ≠ 0 := by
    rw [← h]
    exact Nat.mul_ne_zero hpos.ne' hfi.index_ne_zero
  refine ⟨Nat.finite_of_card_ne_zero hne, ?_⟩
  rw [← h]
  calc Nat.card sub * sub.index ≤ 1080 * 1120 := Nat.mul_le_mul hcard hidx
    _ = 1209600 := by norm_num

@[expose] def emb5 : Fin 5 → Fin 7 := Fin.castLE (by norm_num)

theorem map_lineRels_three :
    ∀ w ∈ lineRels 3 false, (w.map fun l => (emb5 l.1, l.2)) ∈ lineRels 5 true := by
  decide +kernel

noncomputable def toSeed : Pres →* ↥seedGroup :=
  wordsHom (lineRels 3 false) (nativeGens ∘ emb5) (fun w hw => by
    rw [signedProd_comp]
    exact nativeGens_relators _ (map_lineRels_three w hw))

theorem toSeed_of (j : Fin 5) : toSeed (PresentedGroup.of j) = nativeGens (emb5 j) :=
  wordsHom_of _ _ _ j

theorem coe_toSeed_signedProd (w : List (Fin 5 × Bool)) :
    ((toSeed (signedProd PresentedGroup.of w) : ↥seedGroup) : GL (Fin 14) (ZMod 5)) =
      CFSG.Sporadic.Bridge.wordProd unitGen (codes5 w) := by
  rw [toSeed, wordsHom_signedProd, signedProd_comp, coe_signedProd_nativeGens, List.map_map]
  rfl

theorem uA_eq : uA = CFSG.Sporadic.Bridge.wordProd unitGen (codes5 wordA) :=
  Units.ext (val_wordProd_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv lwordL_wordA).symm

theorem uB_eq : uB = CFSG.Sporadic.Bridge.wordProd unitGen (codes5 wordB) :=
  Units.ext (val_wordProd_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv lwordL_wordB).symm

theorem toSeed_surjective : Function.Surjective toSeed := by
  have hw : ∀ w : List (Fin 5 × Bool), ∃ x, ((toSeed x : ↥seedGroup) : GL (Fin 14) (ZMod 5)) =
      CFSG.Sporadic.Bridge.wordProd unitGen (codes5 w) := fun w =>
    ⟨signedProd PresentedGroup.of w, coe_toSeed_signedProd w⟩
  have key : ∀ z ∈ seedGroup, ∃ x, ((toSeed x : ↥seedGroup) : GL (Fin 14) (ZMod 5)) = z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · obtain ⟨x, hx⟩ := hw wordA
        exact ⟨x, hx.trans uA_eq.symm⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨x, hx⟩ := hw wordB
        exact ⟨x, hx.trans uB_eq.symm⟩
    | one => exact ⟨1, by rw [map_one, Subgroup.coe_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, by rw [map_mul, Subgroup.coe_mul, ha, hb]⟩
    | inv x _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨a⁻¹, by rw [map_inv, Subgroup.coe_inv, ha]⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := key y hy
  exact ⟨x, Subtype.ext hx⟩

theorem card_ker_le : Nat.card toSeed.ker ≤ 2 := by
  have h1 := toSeed.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr toSeed_surjective, Subgroup.card_top] at h1
  have h2 := card_pres_le.2
  have h3 := le_card_seedGroup
  have hs : 0 < Nat.card ↥seedGroup := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hs
  rw [h1]
  omega

theorem finite_ker : Finite toSeed.ker := by
  have := card_pres_le.1
  infer_instance

theorem mem_ker_mul_self {p : Pres} (hp : p ∈ toSeed.ker) : p * p = 1 := by
  have := finite_ker
  have hdvd : orderOf (⟨p, hp⟩ : toSeed.ker) ∣ Nat.card toSeed.ker := orderOf_dvd_natCard _
  have hpos : 0 < orderOf (⟨p, hp⟩ : toSeed.ker) := orderOf_pos _
  have hle := (Nat.le_of_dvd (Nat.card_pos) hdvd).trans card_ker_le
  rw [Subgroup.orderOf_mk] at hpos hle
  rw [← pow_two]
  interval_cases h : orderOf p
  · rw [orderOf_eq_one_iff] at h
    rw [h, one_pow]
  · have := pow_orderOf_eq_one p
    rw [h] at this
    exact this

theorem mem_ker_commute {p : Pres} (hp : p ∈ toSeed.ker) (q : Pres) : Commute p q := by
  have := finite_ker
  have hc := le_center_of_card_le_three (commutator_presented_eq_top (by norm_num) false)
    (card_ker_le.trans (by norm_num)) hp
  rw [Subgroup.mem_center_iff] at hc
  exact (hc q).symm

open CFSG.Sporadic.Bridge.J2 (idL lwordL) in
@[expose] noncomputable def conjPoint (w : List (Fin 5 × Bool)) : Pres :=
  signedProd PresentedGroup.of w * PresentedGroup.of 0 * (signedProd PresentedGroup.of w)⁻¹

theorem conjPoint_def (w : List (Fin 5 × Bool)) :
    conjPoint w =
      signedProd PresentedGroup.of w * PresentedGroup.of 0 * (signedProd PresentedGroup.of w)⁻¹ :=
  rfl

theorem wordProd_append {M : Type*} [Group M] (x : ℕ → M) (u v : List (ℕ × Bool)) :
    CFSG.Sporadic.Bridge.wordProd x (u ++ v) =
      CFSG.Sporadic.Bridge.wordProd x u * CFSG.Sporadic.Bridge.wordProd x v := by
  simp [CFSG.Sporadic.Bridge.wordProd]

theorem wordProd_cons_true {M : Type*} [Group M] (x : ℕ → M) (k : ℕ) (v : List (ℕ × Bool)) :
    CFSG.Sporadic.Bridge.wordProd x ((k, true) :: v) = x k * CFSG.Sporadic.Bridge.wordProd x v := by
  simp [CFSG.Sporadic.Bridge.wordProd]

open CFSG.Sporadic.Bridge.J2 (idL lwordL) in
theorem toSeed_conjPoint {w : List (Fin 5 × Bool)} {k : ℕ} (hk : k < 7)
    (hw : lwordL J2.genL J2.genL (codes5 w ++ [(0, true)]) idL =
      lwordL J2.genL J2.genL ((k, true) :: codes5 w) idL) :
    toSeed (conjPoint w) = nativeGens ⟨k, hk⟩ := by
  have hm : CFSG.Sporadic.Bridge.wordProd unitGen (codes5 w ++ [(0, true)]) =
      CFSG.Sporadic.Bridge.wordProd unitGen ((k, true) :: codes5 w) := by
    apply Units.ext
    rw [val_wordProd_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv rfl,
      val_wordProd_of_lwordL genL_wf genL_wf unitGen_val unitGen_inv rfl, hw]
  rw [wordProd_append, wordProd_cons_true unitGen 0, wordProd_cons_true unitGen k,
    show CFSG.Sporadic.Bridge.wordProd unitGen [] = 1 from rfl, mul_one] at hm
  apply Subtype.ext
  rw [conjPoint, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_toSeed_signedProd, toSeed_of, mul_inv_eq_iff_eq_mul]
  exact hm

theorem toSeed_conjX3 : toSeed (conjPoint conjX3) = nativeGens 5 :=
  toSeed_conjPoint (by norm_num) lwordL_conjX3

theorem toSeed_conjX4 : toSeed (conjPoint conjX4) = nativeGens 6 :=
  toSeed_conjPoint (by norm_num) lwordL_conjX4

section Quotient

variable {H : Type*} [Group H] (φ : Pres →* H)

theorem ker_le_ker_toSeed (hdc : ¬ Commute (φ (PresentedGroup.of 0)) (φ (PresentedGroup.of 1))) :
    φ.ker ≤ toSeed.ker := by
  have hsimple : IsSimpleGroup ↥seedGroup :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 nativeEquiv.symm
  have hN : (φ.ker.map toSeed).Normal := φ.normal_ker.map toSeed toSeed_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map toSeed) with h | h
  · intro k hk
    have := Subgroup.mem_map_of_mem toSeed hk
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply hdc
    have key : ∀ p : Pres, ∃ k ∈ toSeed.ker, φ p = φ k := by
      intro p
      have hp : toSeed p ∈ φ.ker.map toSeed := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnp⟩ := hp
      refine ⟨n⁻¹ * p, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hnp, inv_mul_cancel]
      · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hn, inv_one, one_mul]
    obtain ⟨k₀, hk₀, e₀⟩ := key (PresentedGroup.of 0)
    obtain ⟨k₁, hk₁, e₁⟩ := key (PresentedGroup.of 1)
    rw [e₀, e₁]
    exact (mem_ker_commute hk₀ k₁).map φ

theorem toSeed_eq_of_eq (hdc : ¬ Commute (φ (PresentedGroup.of 0)) (φ (PresentedGroup.of 1)))
    {p q : Pres} (h : φ p = φ q) : toSeed p = toSeed q := by
  have hk : p * q⁻¹ ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have := ker_le_ker_toSeed φ hdc hk
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
  exact this

theorem mul_self_eq_one_of_toSeed {p : Pres} (hp : toSeed p = 1) : φ p * φ p = 1 := by
  rw [← map_mul, mem_ker_mul_self hp, map_one]

theorem commute_of_toSeed {p : Pres} (hp : toSeed p = 1) (q : Pres) : Commute (φ p) (φ q) :=
  (mem_ker_commute hp q).map φ

end Quotient

end P3

end CFSG.Timmesfeld.Moufang
