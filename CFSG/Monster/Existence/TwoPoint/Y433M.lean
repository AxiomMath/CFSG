module

public import CFSG.Monster.Existence.TwoPoint.Fi22Iso
public import CFSG.Monster.Existence.TwoPoint.Fi23S4
public import CFSG.Monster.Existence.TwoPoint.Y433MSpider
public import CFSG.Monster.Existence.TwoPoint.Y433MF213
public import CFSG.Monster.Existence.TwoPoint.Y433MF312
public import CFSG.YGroups.Y433.MarkedQuotient
public import Certificates.Certificate16007

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels powWord)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem y433M_wordProd_replicate {G : Type*} [Group G] (x : ℕ → G) (v : List (ℕ × Bool))
    (k : ℕ) : wordProd x (List.replicate k v).flatten = wordProd x v ^ k := by
  induction k with
  | zero => simp [wordProd]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, pow_succ']
    unfold wordProd at ih ⊢
    rw [List.map_append, List.prod_append, ih]

theorem y433M_fiE_rels :
    ∀ v ∈ rels, wordProd fiE v = 1 := by
  intro v hv
  rw [wordProd_fiE (fiRels_lt v hv) (fiRels_pos v hv), fiMkW_eq_one_iff]
  exact fiRelCheck_all v hv

theorem y433M_square_mem_rels :
    ∀ i < 10, [(i, true), (i, true)] ∈ rels :=
  Certificates.certificate16007.1

theorem y433M_fiE_mul_self
    {i : ℕ} (hi : i < 10) : fiE i * fiE i = 1 := by
  have := y433M_fiE_rels _ (y433M_square_mem_rels i hi)
  simpa [wordProd] using this

theorem y433M_fiE_inv
    {i : ℕ} (hi : i < 10) : (fiE i)⁻¹ = fiE i :=
  inv_eq_of_mul_eq_one_right (y433M_fiE_mul_self hi)

theorem y433M_fiCox_mem_rels_aux :
    ∀ i ∈ List.range 10, ∀ j ∈ List.range 10, i < j →
      powWord [(i, true), (j, true)] (fiCox i j) ∈ rels :=
  Certificates.certificate16007.2

theorem y433M_fiCox_mem_rels
    {i j : ℕ} (hi : i < 10) (hj : j < 10) (hij : i < j) :
    powWord [(i, true), (j, true)] (fiCox i j) ∈ rels :=
  y433M_fiCox_mem_rels_aux i (List.mem_range.2 hi) j (List.mem_range.2 hj) hij

theorem y433M_fiE_cox_lt
    {i j : ℕ} (hi : i < 10) (hj : j < 10) (hij : i < j) :
    (fiE i * fiE j) ^ fiCox i j = 1 := by
  have h := y433M_fiE_rels _ (y433M_fiCox_mem_rels hi hj hij)
  have e : wordProd fiE [(i, true), (j, true)] = fiE i * fiE j := by simp [wordProd]
  rwa [powWord, y433M_wordProd_replicate, e] at h

theorem y433M_fiE_cox
    {i j : ℕ} (hi : i < 10) (hj : j < 10) (hij : i ≠ j) :
    (fiE i * fiE j) ^ fiCox i j = 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact y433M_fiE_cox_lt hi hj h
  · have h1 := y433M_fiE_cox_lt hj hi h
    have hc : fiCox j i = fiCox i j := by
      unfold fiCox
      rw [min_comm, max_comm]
    rw [hc] at h1
    have e : fiE i * fiE j = (fiE j * fiE i)⁻¹ := by
      rw [mul_inv_rev, y433M_fiE_inv hi, y433M_fiE_inv hj]
    rw [e, inv_pow, h1, inv_one]

@[expose] noncomputable def y433Img (c : ℕ) : MGriess :=
  if c < 10 then fiE (y433Sigma c) else if c = 10 then gammaZero else 1

theorem y433Img_of_lt {c : ℕ} (hc : c < 10) : y433Img c = fiE (y433Sigma c) := by
  unfold y433Img
  rw [ite_eq_left hc]

theorem y433Img_ten : y433Img 10 = gammaZero := by
  unfold y433Img
  rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem y433Img_of_ge {c : ℕ} (hc : 11 ≤ c) : y433Img c = 1 := by
  unfold y433Img
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem y433Img_eq_fiMkW {c : ℕ} (hc : c < 11) : y433Img c = fiMkW (y433W c) := by
  by_cases h10 : c = 10
  · subst h10
    rw [y433Img_ten]
    unfold y433W gammaZero
    rw [ite_eq_left rfl]
  · rw [y433Img_of_lt (by omega)]
    unfold y433W fiE
    rw [ite_eq_right h10]

theorem y433Img_mul_self
    {c : ℕ} (hc : c < 11) : y433Img c * y433Img c = 1 := by
  by_cases h10 : c = 10
  · subst h10
    rw [y433Img_ten]
    exact gammaZero_mul_self
  · rw [y433Img_of_lt (by omega)]
    exact y433M_fiE_mul_self (y433Sigma_lt (by omega))

theorem y433Img_inv
    {c : ℕ} (hc : c < 11) : (y433Img c)⁻¹ = y433Img c :=
  inv_eq_of_mul_eq_one_right (y433Img_mul_self hc)

theorem evalWord_y433Img (R : List ℕ) (hR : ∀ c ∈ R, c < 11) :
    evalWord y433Img R = fiMkW (y433RelW R) := by
  induction R with
  | nil => simp [y433RelW, fiMkW_nil]
  | cons c R ih =>
    have hc : c < 11 := hR c List.mem_cons_self
    have hR' : ∀ c' ∈ R, c' < 11 := fun c' hc' => hR c' (List.mem_cons_of_mem _ hc')
    have e : y433RelW (c :: R) = y433RelW R ++ y433W c := by
      simp [y433RelW]
    rw [e, fiMkW_append, evalWord_cons, ih hR', y433Img_eq_fiMkW hc]

theorem y433Sigma_injOn : ∀ s < 10, ∀ t < 10, y433Sigma s = y433Sigma t → s = t := by decide

theorem y433_pairExp_lt :
    ∀ s < 10, ∀ t < 10, s < t → pairExp 4 3 3 s t = fiCox (y433Sigma s) (y433Sigma t) := by
  decide

theorem y433_pairExp_ten : ∀ s < 10, pairExp 4 3 3 s 10 = if s = 9 then 3 else 2 := by decide

theorem y433_sigma_nine : y433Sigma 9 = 8 := rfl

theorem y433_sigma_ne_eight : ∀ s < 10, s ≠ 9 → y433Sigma s ≠ 8 := by decide

theorem y433M_sq_of_commute {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y = y * x) : (x * y) ^ 2 = 1 := by
  calc (x * y) ^ 2 = x * y * (x * y) := by rw [pow_two]
    _ = x * (y * x) * y := by simp only [mul_assoc]
    _ = x * (x * y) * y := by rw [← h]
    _ = (x * x) * (y * y) := by simp only [mul_assoc]
    _ = 1 := by rw [hx, hy, one_mul]

theorem y433_pair
    {s t : ℕ} (hs : s < 11) (ht : t < 11) (hst : s < t) :
    (y433Img s * y433Img t) ^ pairExp 4 3 3 s t = 1 := by
  by_cases ht10 : t = 10
  · subst ht10
    have hs10 : s < 10 := by omega
    rw [y433Img_ten, y433Img_of_lt hs10, y433_pairExp_ten s hs10]
    by_cases hs9 : s = 9
    · subst hs9
      rw [ite_eq_left rfl, y433_sigma_nine]
      exact fiE_eight_mul_gammaZero_pow_three
    · rw [ite_eq_right hs9]
      exact y433M_sq_of_commute (y433M_fiE_mul_self (y433Sigma_lt hs10)) gammaZero_mul_self
        (fiE_commute_gammaZero (y433Sigma_lt hs10) (y433_sigma_ne_eight s hs10 hs9))
  · have ht10' : t < 10 := by omega
    have hs10 : s < 10 := by omega
    rw [y433Img_of_lt hs10, y433Img_of_lt ht10', y433_pairExp_lt s hs10 t ht10' hst]
    exact y433M_fiE_cox (y433Sigma_lt hs10) (y433Sigma_lt ht10')
      fun h => absurd (y433Sigma_injOn s hs10 t ht10' h) (by omega)

theorem y433_evalWord_pairWord {s t : ℕ} :
    evalWord y433Img (pairWord 4 3 3 s t) = (y433Img s * y433Img t) ^ pairExp 4 3 3 s t := by
  rw [pairWord, Y443.evalWord_replicate_flatten, evalWord_cons, evalWord_cons, evalWord_nil,
    mul_one]

theorem y433_spider_word : (List.replicate 10 (spiderWord 4 3)).flatten = y433SpiderR := by
  decide

theorem y433_spider :
    evalWord y433Img (List.replicate 10 (spiderWord 4 3)).flatten = 1 := by
  rw [y433_spider_word, evalWord_y433Img _ (by decide), fiMkW_eq_one_iff]
  exact y433SpiderCheck_ok

theorem y433_rels :
    ∀ w ∈ yRels 4 3 3, evalWord y433Img w = 1 := by
  intro w hw
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hsp
  · have hs' : s < 11 := hs
    rw [evalWord_cons, evalWord_cons, evalWord_nil, mul_one]
    exact y433Img_mul_self hs'
  · rw [y433_evalWord_pairWord]
    exact y433_pair hs ht hst
  · split_ifs at hsp with hpqr
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
      subst hsp
      exact y433_spider
    · simp at hsp

noncomputable def y433M :
    YGroup 4 3 3 →* MGriess := yModelHom y433Img y433_rels

theorem y433M_yGen_of_lt
    {c : ℕ} (hc : c < 11) : y433M (yGen 4 3 3 c) = y433Img c :=
  yModelHom_yGen hc

theorem y433M_yGen
    (c : ℕ) : y433M (yGen 4 3 3 c) = y433Img c := by
  by_cases hc : c < 11
  · exact y433M_yGen_of_lt hc
  · rw [yGen_of_le (by unfold ngen; omega), map_one, y433Img_of_ge (by omega)]

theorem y433M_evalWord
    (w : List ℕ) :
    y433M (evalWord (yGen 4 3 3) w) = evalWord y433Img w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, y433M_yGen, ih, evalWord_cons]

theorem range_y433M :
    y433M.range = Subgroup.closure (y433Img '' Set.Iio 11) :=
  range_yModelHom (p := 4) (q := 3) (r := 3)

theorem y433M_evalWord_replicate
    (w : List ℕ) (n : ℕ) :
    y433M (evalWord (yGen 4 3 3) w ^ n) = evalWord y433Img (List.replicate n w).flatten := by
  rw [map_pow, y433M_evalWord, Y443.evalWord_replicate_flatten]

theorem y433M_F433_213 :
    y433M (F433 2 1 3) = 1 := by
  rw [F433_eq_evalWord, y433M_evalWord_replicate]
  change evalWord y433Img y433F213R = 1
  rw [evalWord_y433Img _ (by decide), fiMkW_eq_one_iff]
  exact y433F213Check_ok

theorem y433M_F433_312 :
    y433M (F433 3 1 2) = fiBeta := by
  rw [F433_eq_evalWord, y433M_evalWord_replicate]
  change evalWord y433Img y433F312R = fiBeta
  rw [evalWord_y433Img _ (by decide)]
  exact Subtype.ext y433F312Check_ok

theorem fiBeta_mem_range_y433M :
    fiBeta ∈ y433M.range :=
  ⟨F433 3 1 2, y433M_F433_312⟩

theorem y433Img_commute_fiBeta
    {c : ℕ} (hc : c < 11) : y433Img c * fiBeta = fiBeta * y433Img c := by
  by_cases h10 : c = 10
  · subst h10
    rw [y433Img_ten]
    exact fiBeta_commute_gammaZero.symm
  · rw [y433Img_of_lt (by omega)]
    exact fiE_commute_beta (y433Sigma_lt (by omega))

theorem range_y433M_le_cent_fiBeta :
    y433M.range ≤ cent fiBeta := by
  rw [range_y433M, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact y433Img_commute_fiBeta hc

theorem y433Sigma_surj : ∀ i < 10, ∃ c < 10, y433Sigma c = i := by decide

theorem y433M_image_Iio_ten :
    y433M '' (yGen 4 3 3 '' Set.Iio 10) = fiE '' Set.Iio 10 := by
  ext x
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨y433Sigma c, y433Sigma_lt hc, ?_⟩
    rw [y433M_yGen, y433Img_of_lt hc]
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨c, hc, rfl⟩ := y433Sigma_surj i hi
    exact ⟨_, ⟨c, hc, rfl⟩, by rw [y433M_yGen, y433Img_of_lt hc]⟩

theorem closure_fiE_Iio_ten :
    Subgroup.closure (fiE '' Set.Iio 10) = fiK := by
  rw [fiK, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨PresentedGroup.of ⟨i, by rw [fiGenEq]; exact hi⟩, ⟨_, rfl⟩, ?_⟩
    exact fiHom_of _ fiRelEq _
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨(i : ℕ), i.2.trans_eq fiGenEq, ?_⟩
    exact (fiHom_of _ fiRelEq i).symm

theorem closure_y433M_Iio_ten :
    Subgroup.closure (y433M '' (yGen 4 3 3 '' Set.Iio 10)) = fiK := by
  rw [y433M_image_Iio_ten, closure_fiE_Iio_ten]

theorem fiK_le_range_y433M :
    fiK ≤ y433M.range := by
  rw [← closure_y433M_Iio_ten, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨yGen 4 3 3 c, rfl⟩

end CFSG.Monster.Existence
