module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Pair
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43CoverCheck
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverFinal

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank CFSG.Quasithin.G2U Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434Cover (LiftData)

attribute [local irreducible] sAt

theorem exists_conj_elemAbelian (hsyl : uSylCheck = true) {P : Subgroup UX}
    (hPe : IsElemAbelian 3 P) {n : ℕ} (hPn : Nat.card P = n) :
    ∃ (g : UX) (Pt : Subgroup SUg), Pt ≤ sylS ∧ IsElemAbelian 3 Pt ∧ Nat.card Pt = n ∧
      P.map (MulAut.conj g).toMonoidHom = Pt.map piU := by
  obtain ⟨g, Pt, hPt, hmap⟩ := exists_conj_sylS hsyl (Sec5.isPGroup_of_isElemAbelian hPe)
  have hPe' : IsElemAbelian 3 (P.map (MulAut.conj g).toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hPe
  rw [hmap] at hPe'
  refine ⟨g, Pt, hPt, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_, hmap⟩
  · apply piU_injOn_sylS hsyl (Pt.mul_mem x.2 y.2 |> hPt) (Pt.mul_mem y.2 x.2 |> hPt)
    have := congrArg Subtype.val (hPe'.1.is_comm.comm ⟨piU x, x, x.2, rfl⟩ ⟨piU y, y, y.2, rfl⟩)
    simpa [map_mul] using this
  · apply piU_injOn_sylS hsyl (Pt.pow_mem hx 3 |> hPt) (Pt.one_mem |> hPt)
    rw [map_pow, map_one]
    exact hPe'.2 _ ⟨x, hx, rfl⟩
  · rw [← card_map_piU_of_le hsyl hPt, ← hmap, Subgroup.card_map_of_injective
      (MulAut.conj g).injective, hPn]

theorem exists_pair9 (hsyl : uSylCheck = true) {Ut : Subgroup SUg} (hU : Ut ≤ sylS)
    (hUe : IsElemAbelian 3 Ut) (hU9 : Nat.card Ut = 9) :
    ∃ (ia ib : ℕ) (a b : SUg), ia < ib ∧ ib < 729 ∧ a = sAt ia ∧ b = sAt ib ∧ a ∈ Ut ∧ b ∈ Ut ∧
      a ≠ 1 ∧ b ∉ Subgroup.zpowers a := by
  obtain ⟨a, haU, ha1⟩ : ∃ a ∈ Ut, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Ut = ⊥ := (Subgroup.eq_bot_iff_forall Ut).mpr hall
    rw [this, Subgroup.card_bot] at hU9
    omega
  have ha3 : a ^ 3 = 1 := hUe.2 a haU
  obtain ⟨b, hbU, hba⟩ : ∃ b ∈ Ut, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (show Ut ≤ Subgroup.zpowers a from fun x hx => hall x hx)
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1, hU9] at h
    omega
  have hb3 : b ^ 3 = 1 := hUe.2 b hbU
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  obtain ⟨ia, hia, hae⟩ := exists_sAt_of_mem hsyl (hU haU)
  obtain ⟨ib, hib, hbe⟩ := exists_sAt_of_mem hsyl (hU hbU)
  have hab : a ≠ b := fun h => hba (h ▸ Subgroup.mem_zpowers a)
  rcases lt_trichotomy ia ib with h | h | h
  · exact ⟨ia, ib, a, b, h, hib, hae, hbe, haU, hbU, ha1, hba⟩
  · exact absurd (by rw [hae, hbe, h]) hab
  ·
    have hab' : a ∉ Subgroup.zpowers b := by
      intro hmem
      have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).mpr hmem
      have hc1 : Nat.card (Subgroup.zpowers a) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime ha3 ha1
      have hc2 : Nat.card (Subgroup.zpowers b) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime hb3 hb1
      have := Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
      exact hba (this ▸ Subgroup.mem_zpowers b)
    exact ⟨ib, ia, b, a, h, hia, hbe, hae, hbU, haU, hb1, hab'⟩

theorem size_e9Elems (a b : List ℕ) : (e9Elems a b).size = 9 := by
  simp [e9Elems]

theorem cover_cases (hcover : uCoverCheck = true) {ia ib : ℕ} (hia : ia < 729) (hib : ib < 729)
    (hlt : ia < ib) (h1 : isOrd3 ia = true) (h2 : isOrd3 ib = true)
    (hc : commutes4 (uAt ia) (uAt ib) = true) (hdep : dependent9 (uAt ia) (uAt ib) = false) :
    cover1 (e9Elems (uAt ia) (uAt ib)) = true ∨ cover2 (e9Elems (uAt ia) (uAt ib)) = true := by
  simp only [uCoverCheck, List.all_eq_true, List.mem_range] at hcover
  have h := hcover ia hia
  simp only [coverRow, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h ib hib with h' | h'
  · omega
  · simp only [coverOK, Bool.or_eq_true, Bool.not_eq_true'] at h'
    rw [isOrd3Arr_getD hia, isOrd3Arr_getD hib] at h'
    rcases h' with ((((h' | h') | h') | h') | h') | h'
    · rw [h1] at h'; exact absurd h' (by simp)
    · rw [h2] at h'; exact absurd h' (by simp)
    · rw [hc] at h'; exact absurd h' (by simp)
    · rw [hdep] at h'; exact absurd h' (by simp)
    · exact Or.inl h'
    · exact Or.inr h'

theorem dependent9_false (hsyl : uSylCheck = true) {ia ib : ℕ} (hia : ia < 729) (hib : ib < 729)
    (hba : sAt ib ∉ Subgroup.zpowers (sAt ia)) :
    dependent9 (uAt ia) (uAt ib) = false := by
  have h1 : (uAt ib == uAt ia) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    apply hba
    have : sAt ib = sAt ia := toMat_injective (by
      rw [toMat_sAt hsyl hia, toMat_sAt hsyl hib, e])
    rw [this]
    exact Subgroup.mem_zpowers _
  have h2 : (uAt ib == sq4 (uAt ia)) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    apply hba
    have : sAt ib = sAt ia * sAt ia := toMat_injective (by
      rw [toMat_sAt hsyl hib, map_mul, toMat_sAt hsyl hia, e, sq4, dec4_mul4])
    rw [this]
    exact mul_self_mem_zpowers _
  simp [dependent9, h1, h2]

theorem cover1_spec (hsyl : uSylCheck = true) (hrt : uRtCheck = true) (hk : uKindCheck = true)
    {H : Subgroup SUg} {a b : List ℕ} (hall : ∀ c ∈ e9Elems a b, InSub H c)
    (h : cover1 (e9Elems a b) = true) :
    ∃ (u : SUg) (w : List ℕ), u ∈ H ∧ u ≠ 1 ∧ (∀ l ∈ w, l < 4) ∧
      wordElem w * u * (wordElem w)⁻¹ ∈ rtS := by
  unfold cover1 at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨t, ht, hne, hrtp⟩ := h
  obtain ⟨w, hw, hgp⟩ := convPairArr_getD hk (posOf ((e9Elems a b).getD (t + 1) []))
  rw [hgp] at hrtp
  have hmem : (e9Elems a b).getD (t + 1) [] ∈ e9Elems a b :=
    getD_mem_array _ _ (by rw [size_e9Elems]; omega)
  obtain ⟨hcu, ue, hue, hue_dec⟩ := hall _ hmem
  refine ⟨ue, w, hue, ?_, hw, conj_mem_rtS hsyl hrt hw hue_dec.symm hrtp⟩
  intro e
  exact hne (dec4_injective hcu canon4_one4 (by rw [hue_dec, e, map_one, dec4_one4]))

theorem length_yEls (n : ℕ) : (yEls n).length = 27 := by
  simp [yEls]

theorem yOK_spec {n : ℕ} (h : yOK n = true) :
    (yTriple n).length = 3 ∧ (∀ l ∈ yWord n, l < 4) ∧
      (∀ i < 3, ∀ j < 3, commutes4 (uAt ((yTriple n).getD i 0)) (uAt ((yTriple n).getD j 0)) =
        true) ∧ (∀ i < 3, cube4 (uAt ((yTriple n).getD i 0)) = one4) ∧
      distinctCheck (yEls n).toArray = true ∧
      (∀ q ∈ yTriple n, inRt (posOf (conjStep (wordPair (yWord n)) (uAt q))) = true) := by
  simp only [yOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, wordOK] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, fun l hl => ?_, h4, h5, h6, h7⟩
  simpa using h3 l hl

theorem yOK_of_check (hy : uYCheck = true) {n : ℕ} (hn : n < 13) : yOK n = true := by
  simp only [uYCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hy
  exact hy.2 n hn

theorem yTriple_lt (hy : uYCheck = true) {n : ℕ} (hn : n < 13) (i : ℕ) :
    (yTriple n).getD i 0 < 729 := by
  have h := yOK_of_check hy hn
  simp only [yOK, Bool.and_eq_true] at h
  exact getD_lt_of_all h.1.1.1.1.1.2 i

@[expose] noncomputable def yGrp (n : ℕ) : Subgroup SUg :=
  Subgroup.closure ({sAt ((yTriple n).getD 0 0), sAt ((yTriple n).getD 1 0),
    sAt ((yTriple n).getD 2 0)} : Set SUg)

theorem isElemAbelian_closure_triple {g0 g1 g2 : SUg} (hc01 : g0 * g1 = g1 * g0)
    (hc02 : g0 * g2 = g2 * g0) (hc12 : g1 * g2 = g2 * g1) (h0 : g0 ^ 3 = 1) (h1 : g1 ^ 3 = 1)
    (h2 : g2 ^ 3 = 1) : IsElemAbelian 3 (Subgroup.closure ({g0, g1, g2} : Set SUg)) := by
  refine Item434SporE81.isElemAbelian_closure_of_comm ?_ ?_
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy]
    · exact Commute.refl _
    · exact hc01
    · exact hc02
    · exact hc01.symm
    · exact Commute.refl _
    · exact hc12
    · exact hc02.symm
    · exact hc12.symm
    · exact Commute.refl _
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact h0
    · rw [hx]; exact h1
    · rw [hx]; exact h2

theorem conj_closure_triple_le {g0 g1 g2 w : SUg} {R : Subgroup SUg} (h0 : w * g0 * w⁻¹ ∈ R)
    (h1 : w * g1 * w⁻¹ ∈ R) (h2 : w * g2 * w⁻¹ ∈ R) :
    ∀ y ∈ Subgroup.closure ({g0, g1, g2} : Set SUg), w * y * w⁻¹ ∈ R := by
  have hle : Subgroup.closure ({g0, g1, g2} : Set SUg) ≤ R.comap (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact h0
    · rw [hx]; exact h1
    · rw [hx]; exact h2
  exact fun y hy => hle hy

theorem yGrp_spec (hsyl : uSylCheck = true) (hrt : uRtCheck = true) (hy : uYCheck = true)
    {n : ℕ} (hn : n < 13) :
    yGrp n ≤ sylS ∧ IsElemAbelian 3 (yGrp n) ∧
      (∃ w : List ℕ, (∀ l ∈ w, l < 4) ∧ ∀ y ∈ yGrp n, wordElem w * y * (wordElem w)⁻¹ ∈ rtS) := by
  obtain ⟨hlen, hw, hcomm, hcube, -, hconj⟩ := yOK_spec (yOK_of_check hy hn)
  have hp : ∀ i, (yTriple n).getD i 0 < 729 := yTriple_lt hy hn
  have hmemq : ∀ i < 3, (yTriple n).getD i 0 ∈ yTriple n := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hc : ∀ i < 3, ∀ j < 3, sAt ((yTriple n).getD i 0) * sAt ((yTriple n).getD j 0) =
      sAt ((yTriple n).getD j 0) * sAt ((yTriple n).getD i 0) := fun i hi j hj =>
    commute_of_commutes4 hsyl (hp i) (hp j) (hcomm i hi j hj)
  have h3 : ∀ i < 3, sAt ((yTriple n).getD i 0) ^ 3 = 1 := fun i hi =>
    pow_three_of_cube4 hsyl (hp i) (hcube i hi)
  refine ⟨?_, ?_, yWord n, hw, ?_⟩
  · rw [yGrp, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx <;> rw [hx] <;> exact sAt_mem hsyl (hp _)
  · exact isElemAbelian_closure_triple (hc 0 (by norm_num) 1 (by norm_num))
      (hc 0 (by norm_num) 2 (by norm_num)) (hc 1 (by norm_num) 2 (by norm_num))
      (h3 0 (by norm_num)) (h3 1 (by norm_num)) (h3 2 (by norm_num))
  · exact conj_closure_triple_le
      (conj_mem_rtS hsyl hrt hw (toMat_sAt hsyl (hp 0)) (hconj _ (hmemq 0 (by norm_num))))
      (conj_mem_rtS hsyl hrt hw (toMat_sAt hsyl (hp 1)) (hconj _ (hmemq 1 (by norm_num))))
      (conj_mem_rtS hsyl hrt hw (toMat_sAt hsyl (hp 2)) (hconj _ (hmemq 2 (by norm_num))))

theorem inSub_triple {H : Subgroup SUg} {c : List ℕ} (hc : InSub H c) :
    ∀ x ∈ [one4, c, sq4 c], InSub H x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h
  · rw [h]; exact InSub.one H
  · rw [h]; exact hc
  · rw [h]; exact hc.sq

theorem card_yGrp_ge (hsyl : uSylCheck = true) (hy : uYCheck = true) {n : ℕ} (hn : n < 13) :
    27 ≤ Nat.card (yGrp n) := by
  obtain ⟨-, -, -, -, hdist, -⟩ := yOK_spec (yOK_of_check hy hn)
  have hp : ∀ i, (yTriple n).getD i 0 < 729 := yTriple_lt hy hn
  have hgen : ∀ i < 3, InSub (yGrp n) (uAt ((yTriple n).getD i 0)) := fun i hi =>
    (inSub_uAt_iff hsyl (hp i)).mpr (by
      apply Subgroup.subset_closure
      interval_cases i <;> simp)
  have hall : ∀ c ∈ yEls n, InSub (yGrp n) c := by
    intro c hc
    simp only [yEls, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨x, hx, y, hy', w, hw, rfl⟩ := hc
    exact ((inSub_triple (hgen 0 (by norm_num)) x hx).mul
      (inSub_triple (hgen 1 (by norm_num)) y hy')).mul
      (inSub_triple (hgen 2 (by norm_num)) w hw)
  have hsz : (yEls n).toArray.size = 27 := by simpa using length_yEls n
  have hmemt : ∀ t : Fin 27, (yEls n).toArray.getD t [] ∈ yEls n := fun t =>
    List.mem_toArray.mp (getD_mem_array _ [] (by rw [hsz]; exact t.2))
  have hex : ∀ t : Fin 27, ∃ g ∈ yGrp n, dec4 ((yEls n).toArray.getD t []) = toMat g := fun t =>
    (hall _ (hmemt t)).2
  choose f hfY hf using hex
  have hinj : Function.Injective fun t : Fin 27 => (⟨f t, hfY t⟩ : yGrp n) := by
    intro t t' h
    have h1 : f t = f t' := congrArg Subtype.val h
    exact Fin.ext (distinctCheck_spec hdist (by rw [hsz]; exact t.2) (by rw [hsz]; exact t'.2)
      (dec4_injective (hall _ (hmemt t)).1 (hall _ (hmemt t')).1 (by rw [hf t, hf t', h1])))
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem yCommArr_spec {m p : ℕ} (hm : m < 39) (h : (yCommArr.getD m #[]).getD p false = true) :
    p < 729 ∧ commutes4 (uAt ((yTriple (m / 3)).getD (m % 3) 0)) (uAt p) = true := by
  have hp : p < 729 := by
    by_contra hp
    unfold yCommArr at h
    simp [Array.getD_eq_getD_getElem?, hm, hp] at h
  refine ⟨hp, ?_⟩
  unfold yCommArr at h
  simpa [Array.getD_eq_getD_getElem?, hm, hp] using h

theorem cover2_spec (hsyl : uSylCheck = true) (hy : uYCheck = true) {H : Subgroup SUg}
    {a b : List ℕ} (hall : ∀ c ∈ e9Elems a b, InSub H c) (h : cover2 (e9Elems a b) = true) :
    ∃ n < 13, ∀ i < 3, ∃ u ∈ H, u ≠ 1 ∧
      sAt ((yTriple n).getD i 0) * u = u * sAt ((yTriple n).getD i 0) := by
  unfold cover2 at h
  simp only [List.any_eq_true, List.mem_range, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨n, hn, hi⟩ := h
  refine ⟨n, hn, fun i hi3 => ?_⟩
  obtain ⟨t, ht, hne, hcomm⟩ := hi i hi3
  have hm : 3 * n + i < 39 := by omega
  obtain ⟨hp, hc⟩ := yCommArr_spec hm hcomm
  have hdiv : (3 * n + i) / 3 = n := by omega
  have hmod : (3 * n + i) % 3 = i := by omega
  rw [hdiv, hmod] at hc
  have hmem : (e9Elems a b).getD (t + 1) [] ∈ e9Elems a b :=
    getD_mem_array _ _ (by rw [size_e9Elems]; omega)
  obtain ⟨hcu, ue, hue, hue_dec⟩ := hall _ hmem
  have hpos : uAt (posOf ((e9Elems a b).getD (t + 1) [])) = (e9Elems a b).getD (t + 1) [] :=
    posOf_spec hp
  rw [hpos] at hc
  refine ⟨ue, hue, ?_, ?_⟩
  · intro e
    exact hne (dec4_injective hcu canon4_one4 (by rw [hue_dec, e, map_one, dec4_one4]))
  · have hyp := yTriple_lt hy hn i
    have : sAt ((yTriple n).getD i 0) * ue = ue * sAt ((yTriple n).getD i 0) := by
      apply toMat_injective
      rw [map_mul, map_mul, toMat_sAt hsyl hyp, ← hue_dec, ← dec4_mul4, ← dec4_mul4]
      exact congrArg dec4 (beq_iff_eq.mp hc)
    exact this

theorem uLiftCheck_parts (h : uLiftCheck = true) :
    (∀ j < 2, ∀ l ∈ uLiftG.getD j [], l < 4) ∧ (∀ j < 2, ∀ k < 4, ∀ i < 4, liftMat j k i < 3) ∧
      (∀ j < 2, ∀ i < 4, conjStep (wordPair (uLiftG.getD j [])) (liftEl i) = liftRhs j i) := by
  simp only [uLiftCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hG2⟩, -⟩, hGok⟩, hMlt⟩, hrel⟩ := h
  refine ⟨fun j hj l hl => ?_, fun j hj k hk i hi => hMlt j hj k hk i hi,
    fun j hj i hi => hrel j hj i hi⟩
  have hmem : uLiftG.getD j [] ∈ uLiftG := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have := hGok _ hmem
  simp only [wordOK, List.all_eq_true, decide_eq_true_eq] at this
  exact this l hl

theorem prod_ofFn_four {Y : Type*} [Group Y] (f : Fin 4 → Y) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * (f 3 * 1))) := by
  simp [List.ofFn_succ]

theorem rt_rel (hsyl : uSylCheck = true) (hrt : uRtCheck = true) (hlift : uLiftCheck = true)
    {j i : ℕ} (hj : j < 2) (hi : i < 4) :
    wordElem (uLiftG.getD j []) * sAt (uLiftBasis.getD i 0) * (wordElem (uLiftG.getD j []))⁻¹ =
      sAt (uLiftBasis.getD 0 0) ^ liftMat j 0 i * (sAt (uLiftBasis.getD 1 0) ^ liftMat j 1 i *
        (sAt (uLiftBasis.getD 2 0) ^ liftMat j 2 i *
          (sAt (uLiftBasis.getD 3 0) ^ liftMat j 3 i * 1))) := by
  obtain ⟨hG, hMlt, hrelC⟩ := uLiftCheck_parts hlift
  apply toMat_injective
  have hrC : conjStep (wordPair (uLiftG.getD j [])) (uAt (uLiftBasis.getD i 0)) = liftRhs j i :=
    hrelC j hj i hi
  rw [toMat_conj_word (hG j hj) (toMat_xS hsyl hrt hi), hrC, liftRhs]
  have e : ∀ k < 4, toMat (sAt (uLiftBasis.getD k 0) ^ liftMat j k i) =
      dec4 (pow4 (liftEl k) (liftMat j k i)) := fun k hk =>
    toMat_pow4 (toMat_xS hsyl hrt hk) (hMlt j hj k hk i hi)
  rw [map_mul, map_mul, map_mul, map_mul, e 0 (by norm_num), e 1 (by norm_num),
    e 2 (by norm_num), e 3 (by norm_num), map_one, dec4_mul4, dec4_mul4, dec4_mul4, dec4_mul4,
    dec4_one4]

theorem closure_range_rt : Subgroup.closure
    (Set.range fun i : Fin 4 => piU (sAt (uLiftBasis.getD (i : ℕ) 0))) = rtS.map piU := by
  rw [rtS, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_range, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Fin.exists_fin_succ]
  simp
  constructor <;> rintro (h | h | h | h) <;> simp [h]

theorem exists_liftData_rt (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hcover : uCoverAll = true) :
    ∃ d : LiftData UX, (∀ i, d.x i ∈ rtS.map piU) ∧
      Subgroup.closure (Set.range d.x) = rtS.map piU := by
  obtain ⟨hrt, -, -, -, -⟩ := uClassCheck_parts hcls
  have hlift : uLiftCheck = true := by
    simp only [uCoverAll, Bool.and_eq_true] at hcover
    exact hcover.2
  have hx27 : 27 ≤ Nat.card (Subgroup.closure
      (Set.range fun i : Fin 4 => piU (sAt (uLiftBasis.getD (i : ℕ) 0)))) := by
    rw [closure_range_rt, card_map_piU_of_le hsyl (rtS_le_sylS hsyl hrt)]
    exact (by norm_num : 27 ≤ 81).trans (card_rtS hsyl hrt)
  refine ⟨⟨4, 2, fun i => piU (sAt (uLiftBasis.getD (i : ℕ) 0)),
    fun j => piU (wordElem (uLiftG.getD (j : ℕ) [])), fun j k i => liftMat j k i, 0, 0,
    fun k l => (uLiftCs.getD k []).getD l [], fun i => uLiftCs'.getD i [], ?_, ?_, ?_, ?_, ?_,
    hx27⟩, ?_, closure_range_rt⟩
  · intro i
    rw [← map_pow, xS_cube hsyl hrt i.2, map_one]
  · intro i j
    rw [← map_mul, ← map_mul, (xS_comm hsyl hrt i.2 j.2).eq]
  · intro j i
    have h := congrArg piU (rt_rel hsyl hrt hlift j.2 i.2)
    rw [prod_ofFn_four]
    simpa [map_mul, map_pow, map_inv, map_one] using h
  · decide +kernel
  · decide +kernel
  · intro i
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by
      fin_cases i <;> simp))

@[expose] def conjLD {X : Type*} [Group X] (d : LiftData X) (h : X) : LiftData X where
  n := d.n
  m := d.m
  x i := h⁻¹ * d.x i * h
  g j := h⁻¹ * d.g j * h
  M := d.M
  k₀ := d.k₀
  l₀ := d.l₀
  cs := d.cs
  cs' := d.cs'
  hx3 i := by
    have e : (h⁻¹ * d.x i * h) ^ 3 = h⁻¹ * d.x i ^ 3 * h := by
      have := conj_pow (a := h⁻¹) (b := d.x i) (i := 3)
      rwa [inv_inv] at this
    rw [e, d.hx3 i]
    group
  hxc i j := by
    have e := d.hxc i j
    calc h⁻¹ * d.x i * h * (h⁻¹ * d.x j * h) = h⁻¹ * (d.x i * d.x j) * h := by group
      _ = h⁻¹ * (d.x j * d.x i) * h := by rw [e]
      _ = h⁻¹ * d.x j * h * (h⁻¹ * d.x i * h) := by group
  hrel j i := by
    set φ : X →* X := (MulAut.conj h⁻¹).toMonoidHom with hφdef
    have hφ : ∀ y, φ y = h⁻¹ * y * h := fun y => by simp [hφdef]
    have h1 := congrArg φ (d.hrel j i)
    rw [map_mul, map_mul, map_inv, map_list_prod, List.map_ofFn] at h1
    rw [show (⇑φ ∘ fun k => d.x k ^ d.M j k i) = fun k => (h⁻¹ * d.x k * h) ^ d.M j k i from by
      funext k
      simp only [Function.comp_apply]
      rw [map_pow, hφ]] at h1
    simp only [hφ] at h1
    exact h1
  hlin := d.hlin
  hlin' := d.hlin'
  hx27 := by
    set φ : X →* X := (MulAut.conj h⁻¹).toMonoidHom with hφdef
    have hφ : ∀ y, φ y = h⁻¹ * y * h := fun y => by simp [hφdef]
    have hmap : Subgroup.closure (Set.range fun i => h⁻¹ * d.x i * h) =
        (Subgroup.closure (Set.range d.x)).map φ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      congr 2
      funext i
      simp [hφ]
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact d.hx27

theorem conj_mem_closure_conj {X : Type*} [Group X] (d : LiftData X) (k : X) {z : X}
    (hz : z ∈ Subgroup.closure (Set.range d.x)) :
    k⁻¹ * z * k ∈ Subgroup.closure (Set.range (conjLD d k).x) := by
  set φ : X →* X := (MulAut.conj k⁻¹).toMonoidHom with hφ
  have h1 : φ z ∈ (Subgroup.closure (Set.range d.x)).map φ := Subgroup.mem_map_of_mem φ hz
  rw [MonoidHom.map_closure, ← Set.range_comp] at h1
  have h2 : φ z = k⁻¹ * z * k := by simp [hφ]
  have h3 : (⇑φ ∘ d.x) = (conjLD d k).x := by
    funext i
    simp [hφ, conjLD]
  rw [h2, h3] at h1
  exact h1

theorem conjLD_x_mem_cent {X : Type*} [Group X] (d : LiftData X) (h g u' : X)
    (hx : ∀ i, d.x i * (h * u' * h⁻¹) = (h * u' * h⁻¹) * d.x i) :
    ∀ i, (conjLD d (h * g)).x i ∈ Subgroup.centralizer ({g⁻¹ * u' * g} : Set X) := by
  intro i
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (h * g)⁻¹ * d.x i * (h * g) * (g⁻¹ * u' * g) =
    (g⁻¹ * u' * g) * ((h * g)⁻¹ * d.x i * (h * g))
  have e1 := hx i
  calc (h * g)⁻¹ * d.x i * (h * g) * (g⁻¹ * u' * g)
      = (h * g)⁻¹ * (d.x i * (h * u' * h⁻¹)) * (h * g) := by group
    _ = (h * g)⁻¹ * ((h * u' * h⁻¹) * d.x i) * (h * g) := by rw [e1]
    _ = (g⁻¹ * u' * g) * ((h * g)⁻¹ * d.x i * (h * g)) := by group

theorem rt_map_comm (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {x y : UX}
    (hx : x ∈ rtS.map piU) (hy : y ∈ rtS.map piU) : x * y = y * x := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  rw [← map_mul, ← map_mul]
  exact congrArg piU (congrArg Subtype.val ((rtS_isElemAbelian hsyl hrt).1.is_comm.comm
    ⟨x', hx'⟩ ⟨y', hy'⟩))

theorem map_closure_triple_le (ψ : SUg →* UX) {g0 g1 g2 : SUg}
    {T : Subgroup UX} (h0 : ψ g0 ∈ T) (h1 : ψ g1 ∈ T) (h2 : ψ g2 ∈ T) :
    ∀ y ∈ Subgroup.closure ({g0, g1, g2} : Set SUg), ψ y ∈ T := by
  have hle : Subgroup.closure ({g0, g1, g2} : Set SUg) ≤ T.comap ψ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact h0
    · rw [hx]; exact h1
    · rw [hx]; exact h2
  exact fun y hy => hle hy

theorem mem_closure_cent {us : Set UX} {v x : UX} (hv : v ∈ us)
    (hx : x ∈ Subgroup.centralizer ({v} : Set UX)) :
    x ∈ Subgroup.closure (⋃ u ∈ us, (Subgroup.centralizer ({u} : Set UX) : Set UX)) :=
  Subgroup.subset_closure (Set.mem_biUnion hv hx)

theorem map_mem_cent (ψ : SUg →* UX) {a b : SUg}
    (h : a * b = b * a) : ψ a ∈ Subgroup.centralizer ({ψ b} : Set UX) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]

@[expose] noncomputable def psiConj (g : UX) : SUg →* UX :=
  (MulAut.conj g⁻¹).toMonoidHom.comp piU

theorem psiConj_apply (g : UX) (x : SUg) : psiConj g x = g⁻¹ * piU x * g := by
  simp [psiConj]

theorem cover2_final (hsyl : uSylCheck = true) (hrt : uRtCheck = true) (hy : uYCheck = true)
    {n : ℕ} (hn : n < 13) {d₀ : LiftData UX}
    (hd₀cl : Subgroup.closure (Set.range d₀.x) = rtS.map piU) (g : UX) (U : Subgroup UX)
    (uc : ℕ → SUg) (hUS : ∀ i < 3, psiConj g (uc i) ∈ U ∧ psiConj g (uc i) ≠ 1)
    (hcomm : ∀ i < 3, sAt ((yTriple n).getD i 0) * uc i = uc i * sAt ((yTriple n).getD i 0)) :
    ∃ us : Set UX, (∀ u ∈ us, u ∈ U ∧ u ≠ 1) ∧ ∃ d : LiftData UX, ∃ Y : Subgroup UX,
      Y ≤ Subgroup.closure (Set.range d.x) ∧ 27 ≤ Nat.card Y ∧
        Y ≤ Subgroup.closure (⋃ u ∈ us, (Subgroup.centralizer ({u} : Set UX) : Set UX)) := by
  obtain ⟨hYle, hYe, w, hw, hwconj⟩ := yGrp_spec hsyl hrt hy hn
  have hYn : ∀ y ∈ yGrp n, psiConj g y ∈ Subgroup.closure
      (⋃ u ∈ ((fun i => psiConj g (uc i)) '' {i : ℕ | i < 3}),
        (Subgroup.centralizer ({u} : Set UX) : Set UX)) := by
    have key : ∀ i < 3, psiConj g (sAt ((yTriple n).getD i 0)) ∈ Subgroup.closure
        (⋃ u ∈ ((fun i => psiConj g (uc i)) '' {i : ℕ | i < 3}),
          (Subgroup.centralizer ({u} : Set UX) : Set UX)) := fun i hi =>
      mem_closure_cent (Set.mem_image_of_mem _ (show i ∈ {i : ℕ | i < 3} from hi))
        (map_mem_cent (psiConj g) (hcomm i hi))
    exact map_closure_triple_le (psiConj g) (key 0 (by norm_num)) (key 1 (by norm_num))
      (key 2 (by norm_num))
  refine ⟨(fun i => psiConj g (uc i)) '' {i : ℕ | i < 3}, ?_,
    conjLD d₀ (piU (wordElem w) * g), (yGrp n).map (psiConj g), ?_, ?_, ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact hUS i hi
  · rintro _ ⟨y, hy, rfl⟩
    have hz : piU (wordElem w) * piU y * (piU (wordElem w))⁻¹ ∈
        Subgroup.closure (Set.range d₀.x) := by
      rw [hd₀cl, ← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem _ (hwconj y hy)
    have := conj_mem_closure_conj d₀ (piU (wordElem w) * g) hz
    have e : (piU (wordElem w) * g)⁻¹ * (piU (wordElem w) * piU y * (piU (wordElem w))⁻¹) *
        (piU (wordElem w) * g) = psiConj g y := by
      rw [psiConj_apply]
      group
    rw [e] at this
    exact this
  · have h27 : 27 ≤ Nat.card (yGrp n) := card_yGrp_ge hsyl hy hn
    have hcard : Nat.card ((yGrp n).map (psiConj g)) = Nat.card (yGrp n) := by
      have e : (yGrp n).map (psiConj g) =
          ((yGrp n).map piU).map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [psiConj, Subgroup.map_map]
      rw [e, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
        card_map_piU_of_le hsyl hYle]
    rw [hcard]
    exact h27
  · rintro _ ⟨y, hy, rfl⟩
    exact hYn y hy

theorem hX_UX (hsyl : uSylCheck = true) (hcls : uClassCheck = true) (hcover : uCoverAll = true) :
    ∀ U : Subgroup UX, IsElemAbelian 3 U → Nat.card U = 9 →
      ∃ us : Set UX, (∀ u ∈ us, u ∈ U ∧ u ≠ 1) ∧ ∃ d : LiftData UX, ∃ Y : Subgroup UX,
        Y ≤ Subgroup.closure (Set.range d.x) ∧ 27 ≤ Nat.card Y ∧
          Y ≤ Subgroup.closure (⋃ u ∈ us, (Subgroup.centralizer ({u} : Set UX) : Set UX)) := by
  intro U hUe hU9
  obtain ⟨hrt, hk, -, -, -⟩ := uClassCheck_parts hcls
  have hparts : uYCheck = true ∧ uCoverCheck = true ∧ uLiftCheck = true := by
    simp only [uCoverAll, Bool.and_eq_true] at hcover
    exact ⟨hcover.1.1, hcover.1.2, hcover.2⟩
  obtain ⟨hy, hcc, -⟩ := hparts
  obtain ⟨d₀, hd₀mem, hd₀cl⟩ := exists_liftData_rt hsyl hcls hcover
  obtain ⟨g, Ut, hUt, hUte, hUt9, hmap⟩ := exists_conj_elemAbelian hsyl hUe hU9
  obtain ⟨ia, ib, a, b, hlt, hib, hae, hbe, haU, hbU, ha1, hba⟩ :=
    exists_pair9 hsyl hUt hUte hUt9
  have hia : ia < 729 := hlt.trans hib
  have hUab : ∀ x ∈ Ut, ∀ y ∈ Ut, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUte.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha3 := hUte.2 a haU
  have hb3 := hUte.2 b hbU
  have hab := hUab a haU b hbU
  subst hae hbe
  have hord1 : isOrd3 ia = true := isOrd3_of_elem hsyl hia ha1 ha3
  have hb1 : sAt ib ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hord2 : isOrd3 ib = true := isOrd3_of_elem hsyl hib hb1 hb3
  have hcomm : commutes4 (uAt ia) (uAt ib) = true := commutes4_of_comm hsyl hia hib hab
  have hdep := dependent9_false hsyl hia hib hba
  have hall : ∀ c ∈ e9Elems (uAt ia) (uAt ib), InSub Ut c :=
    inSub_e9Elems ((inSub_uAt_iff hsyl hia).mpr haU) ((inSub_uAt_iff hsyl hib).mpr hbU)
  have hback : ∀ u ∈ Ut, g⁻¹ * piU u * g ∈ U := fun u hu => by
    have hmem : piU u ∈ U.map (MulAut.conj g).toMonoidHom := by
      rw [hmap]
      exact Subgroup.mem_map_of_mem _ hu
    obtain ⟨v, hvU, hv⟩ := hmem
    have : g⁻¹ * piU u * g = v := by
      rw [← hv]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hvU
  have hbackne : ∀ u ∈ Ut, u ≠ 1 → g⁻¹ * piU u * g ≠ 1 := fun u hu hu1 h => by
    apply hu1
    have h1 : piU u = 1 := by
      have : piU u = g * (g⁻¹ * piU u * g) * g⁻¹ := by group
      rw [this, h]
      group
    exact piU_injOn_sylS hsyl (hUt hu) (Subgroup.one_mem _) (by rw [h1, map_one])
  rcases cover_cases hcc hia hib hlt hord1 hord2 hcomm hdep with h1 | h2
  ·
    obtain ⟨u, w, huU, hu1, hw, hconj⟩ := cover1_spec hsyl hrt hk hall h1
    have hx : ∀ i, d₀.x i * (piU (wordElem w) * piU u * (piU (wordElem w))⁻¹) =
        (piU (wordElem w) * piU u * (piU (wordElem w))⁻¹) * d₀.x i := fun i => by
      refine rt_map_comm hsyl hrt (hd₀mem i) ?_
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hconj
    have hcent := conjLD_x_mem_cent d₀ (piU (wordElem w)) g (piU u) hx
    refine ⟨{g⁻¹ * piU u * g}, ?_, conjLD d₀ (piU (wordElem w) * g),
      Subgroup.closure (Set.range (conjLD d₀ (piU (wordElem w) * g)).x), le_rfl,
      (conjLD d₀ (piU (wordElem w) * g)).hx27, ?_⟩
    · intro x hx'
      rw [Set.mem_singleton_iff] at hx'
      rw [hx']
      exact ⟨hback u huU, hbackne u huU hu1⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure (Set.mem_biUnion (Set.mem_singleton _) (hcent i))
  ·
    obtain ⟨n, hn, hcn⟩ := cover2_spec hsyl hy hall h2
    obtain ⟨hYle, hYe, w, hw, hwconj⟩ := yGrp_spec hsyl hrt hy hn
    choose! uc huc using hcn
    obtain ⟨hYle, hYe, w, hw, hwconj⟩ := yGrp_spec hsyl hrt hy hn
    exact cover2_final hsyl hrt hy hn hd₀cl g U uc
      (fun i hi => by
        rw [psiConj_apply]
        exact ⟨hback _ (huc i hi).1, hbackne _ (huc i hi).1 (huc i hi).2.1⟩)
      (fun i hi => (huc i hi).2.2)

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
