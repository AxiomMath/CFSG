module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Sylow
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43ClassCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Gen
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank CFSG.Quasithin.G2U Matrix

local notation "Mat4" => Matrix (Fin 4) (Fin 4) F9

attribute [local irreducible] uGenWords uPar uRt uKind uConvR uConvD uBad uY uLiftBasis uLiftG
  uLiftM uLiftCs uLiftCs' uElems uIdx uKindArr uRtArr

open _root_.Classical in
@[expose] noncomputable def sAt (t : ℕ) : SUg :=
  if h : ∃ g ∈ sylS, dec4 (uAt t) = toMat g then Classical.choose h else 1

theorem sAt_spec (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) :
    sAt t ∈ sylS ∧ toMat (sAt t) = dec4 (uAt t) := by
  have h := exists_elem_of_code hsyl ht
  have e : sAt t = Classical.choose h := by
    unfold sAt
    simp only [h, dite_true]
  rw [e]
  exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.symm⟩

attribute [local irreducible] sAt

theorem toMat_sAt (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) :
    toMat (sAt t) = dec4 (uAt t) := (sAt_spec hsyl ht).2

theorem sAt_mem (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) : sAt t ∈ sylS :=
  (sAt_spec hsyl ht).1

theorem sAt_eq_of_code (hsyl : uSylCheck = true) {s t : ℕ} (hs : s < 729) (ht : t < 729)
    (h : uAt s = uAt t) : sAt s = sAt t :=
  toMat_injective (by rw [toMat_sAt hsyl hs, toMat_sAt hsyl ht, h])

theorem sAt_injective (hsyl : uSylCheck = true) {s t : ℕ} (hs : s < 729) (ht : t < 729)
    (h : sAt s = sAt t) : s = t := by
  have h1 : dec4 (uAt s) = dec4 (uAt t) := by
    rw [← toMat_sAt hsyl hs, ← toMat_sAt hsyl ht, h]
  exact uAt_inj hsyl hs ht (dec4_injective (canon4_uAt hsyl hs) (canon4_uAt hsyl ht) h1)

theorem sAt_mul (hsyl : uSylCheck = true) {p q r : ℕ} (hp : p < 729) (hq : q < 729)
    (hr : r < 729) (h : mul4 (uAt p) (uAt q) = uAt r) : sAt p * sAt q = sAt r := by
  apply toMat_injective
  rw [map_mul, toMat_sAt hsyl hp, toMat_sAt hsyl hq, toMat_sAt hsyl hr, ← dec4_mul4, h]

theorem posOf_spec {c : List ℕ} (h : posOf c < 729) : uAt (posOf c) = c := by
  unfold posOf at h ⊢
  split_ifs at h ⊢ with hf
  · unfold found at hf
    split at hf
    · rename_i t ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      rw [ht, Option.getD_some]
      exact hf.2
    · exact absurd hf Bool.false_ne_true
  · omega

noncomputable def gOf (c : List ℕ) : SUg := sAt (posOf c)

theorem toMat_gOf (hsyl : uSylCheck = true) {c : List ℕ} (h : posOf c < 729) :
    toMat (gOf c) = dec4 c := by
  rw [gOf, toMat_sAt hsyl h, posOf_spec h]

theorem toMat_pow4 {g : SUg} {c : List ℕ} (h : toMat g = dec4 c) {k : ℕ} (hk : k < 3) :
    toMat (g ^ k) = dec4 (pow4 c k) := by
  unfold pow4
  interval_cases k
  · simp [dec4_one4]
  · simpa using h
  · rw [pow_two, map_mul, h]
    simp [sq4, dec4_mul4]

theorem commute_of_commutes4 (hsyl : uSylCheck = true) {p q : ℕ} (hp : p < 729) (hq : q < 729)
    (h : commutes4 (uAt p) (uAt q) = true) : sAt p * sAt q = sAt q * sAt p := by
  apply toMat_injective
  rw [map_mul, map_mul, toMat_sAt hsyl hp, toMat_sAt hsyl hq, ← dec4_mul4, ← dec4_mul4]
  exact congrArg dec4 (beq_iff_eq.mp h)

theorem pow_three_of_cube4 (hsyl : uSylCheck = true) {p : ℕ} (hp : p < 729)
    (h : cube4 (uAt p) = one4) : sAt p ^ 3 = 1 := by
  apply toMat_injective
  have := dec4_cube4 (uAt p)
  rw [h, dec4_one4, ← toMat_sAt hsyl hp] at this
  rw [map_pow, map_one]
  simpa [pow_succ, mul_assoc] using this.symm

theorem conj_pos_spec (hsyl : uSylCheck = true) {w : List ℕ} (hw : ∀ l ∈ w, l < 4) {p : ℕ}
    (hp : p < 729) (hq : posOf (conjStep (wordPair w) (uAt p)) < 729) :
    wordElem w * sAt p * (wordElem w)⁻¹ = sAt (posOf (conjStep (wordPair w) (uAt p))) := by
  apply toMat_injective
  have h1 := dec4_conjStep w hw (uAt p)
  have h2 : dec4 (conjStep (wordPair w) (uAt p)) =
      toMat (sAt (posOf (conjStep (wordPair w) (uAt p)))) := by
    rw [toMat_sAt hsyl hq, posOf_spec hq]
  rw [map_mul, map_mul, toMat_sAt hsyl hp, ← h2, h1]
  rfl

theorem uRtCheck_parts (h : uRtCheck = true) :
    uLiftBasis.length = 4 ∧ (∀ p ∈ uLiftBasis, p < 729) ∧
      (∀ a < 4, ∀ b < 4,
        commutes4 (uAt (uLiftBasis.getD a 0)) (uAt (uLiftBasis.getD b 0)) = true) ∧
      (∀ a < 4, cube4 (uAt (uLiftBasis.getD a 0)) = one4) ∧ uRt.length = 81 ∧
      (∀ p ∈ uRt, p < 729) ∧ (∀ e < 81, uRt.contains (posOf (rtProd e)) = true) ∧
      distinctCheck ((List.range 81).map rtProd).toArray = true := by
  simp only [uRtCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

local notation "xS[" i "]" => sAt (uLiftBasis.getD i 0)

theorem basis_lt (hrt : uRtCheck = true) {i : ℕ} (hi : i < 4) : uLiftBasis.getD i 0 < 729 := by
  obtain ⟨hlen, hlt, -⟩ := uRtCheck_parts hrt
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hlt _ (List.getElem_mem _)

theorem xS_mem (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {i : ℕ} (hi : i < 4) :
    xS[i] ∈ sylS := sAt_mem hsyl (basis_lt hrt hi)

theorem xS_comm (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {i j : ℕ} (hi : i < 4)
    (hj : j < 4) : Commute xS[i] xS[j] := by
  obtain ⟨-, -, hc, -⟩ := uRtCheck_parts hrt
  exact commute_of_commutes4 hsyl (basis_lt hrt hi) (basis_lt hrt hj) (hc i hi j hj)

theorem xS_cube (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {i : ℕ} (hi : i < 4) :
    xS[i] ^ 3 = 1 := by
  obtain ⟨-, -, -, hc, -⟩ := uRtCheck_parts hrt
  exact pow_three_of_cube4 hsyl (basis_lt hrt hi) (hc i hi)

theorem toMat_xS (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {i : ℕ} (hi : i < 4) :
    toMat (xS[i]) = dec4 (uAt (uLiftBasis.getD i 0)) := toMat_sAt hsyl (basis_lt hrt hi)

@[expose] noncomputable def rtS : Subgroup SUg :=
  Subgroup.closure {xS[0], xS[1], xS[2], xS[3]}

theorem rtS_isElemAbelian (hsyl : uSylCheck = true) (hrt : uRtCheck = true) :
    CFSG.Assembly.IsElemAbelian 3 rtS := by
  have hc : ∀ i j : ℕ, i < 4 → j < 4 → Commute xS[i] xS[j] := fun i j hi hj =>
    xS_comm hsyl hrt hi hj
  refine Item434SporE81.isElemAbelian_closure_of_comm ?_ ?_
  · rintro _ (rfl | rfl | rfl | rfl) _ (rfl | rfl | rfl | rfl) <;> exact hc _ _ (by norm_num)
      (by norm_num)
  · rintro _ (rfl | rfl | rfl | rfl) <;> exact xS_cube hsyl hrt (by norm_num)

theorem rtS_le_sylS (hsyl : uSylCheck = true) (hrt : uRtCheck = true) : rtS ≤ sylS := by
  rw [rtS, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl) <;> exact xS_mem hsyl hrt (by norm_num)

@[expose] noncomputable def prodX (e : ℕ) : SUg :=
  xS[0] ^ (e % 3) * xS[1] ^ (e / 3 % 3) * xS[2] ^ (e / 9 % 3) * xS[3] ^ (e / 27 % 3)

theorem toMat_prodX (hsyl : uSylCheck = true) (hrt : uRtCheck = true) (e : ℕ) :
    toMat (prodX e) = dec4 (rtProd e) := by
  unfold prodX rtProd
  rw [map_mul, map_mul, map_mul,
    toMat_pow4 (toMat_xS hsyl hrt (by norm_num : 0 < 4)) (Nat.mod_lt _ (by norm_num)),
    toMat_pow4 (toMat_xS hsyl hrt (by norm_num : 1 < 4)) (Nat.mod_lt _ (by norm_num)),
    toMat_pow4 (toMat_xS hsyl hrt (by norm_num : 2 < 4)) (Nat.mod_lt _ (by norm_num)),
    toMat_pow4 (toMat_xS hsyl hrt (by norm_num : 3 < 4)) (Nat.mod_lt _ (by norm_num)),
    dec4_mul4, dec4_mul4, dec4_mul4]

theorem prodX_mem (e : ℕ) : prodX e ∈ rtS := by
  have h0 : xS[0] ∈ rtS := Subgroup.subset_closure (by simp)
  have h1 : xS[1] ∈ rtS := Subgroup.subset_closure (by simp)
  have h2 : xS[2] ∈ rtS := Subgroup.subset_closure (by simp)
  have h3 : xS[3] ∈ rtS := Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem (mul_mem (pow_mem h0 _) (pow_mem h1 _)) (pow_mem h2 _)) (pow_mem h3 _)

theorem canon4_rtProd (e : ℕ) : canon4 (rtProd e) = true := canon4_mul4 _ _

theorem rtProd_injective (hrt : uRtCheck = true) {e e' : ℕ} (he : e < 81) (he' : e' < 81)
    (h : rtProd e = rtProd e') : e = e' := by
  obtain ⟨-, -, -, -, -, -, -, hd⟩ := uRtCheck_parts hrt
  refine distinctCheck_spec hd (t := e) (t' := e') (by simpa using he) (by simpa using he') ?_
  simp [Array.getD_eq_getD_getElem?, he, he', h]

theorem card_rtS (hsyl : uSylCheck = true) (hrt : uRtCheck = true) : 81 ≤ Nat.card rtS := by
  have hinj : Function.Injective fun e : Fin 81 => (⟨prodX e, prodX_mem e⟩ : rtS) := by
    intro e e' h
    have h1 : prodX e = prodX e' := congrArg Subtype.val h
    have h2 : rtProd e = rtProd e' := by
      refine dec4_injective (canon4_rtProd e) (canon4_rtProd e') ?_
      rw [← toMat_prodX hsyl hrt, ← toMat_prodX hsyl hrt, h1]
    exact Fin.ext (rtProd_injective hrt e.2 e'.2 h2)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem inRt_spec {t : ℕ} (h : inRt t = true) : t < 729 ∧ t ∈ uRt := by
  unfold inRt uRtArr at h
  by_cases ht : t < 729
  · refine ⟨ht, ?_⟩
    simpa [Array.getD_eq_getD_getElem?, ht] using h
  · exfalso
    simp [Array.getD_eq_getD_getElem?, ht] at h

theorem sAt_mem_rtS_of_mem_uRt (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {t : ℕ}
    (ht : t ∈ uRt) : sAt t ∈ rtS := by
  obtain ⟨-, -, -, -, hlen, hlt', hcont, -⟩ := uRtCheck_parts hrt
  have hmem : ∀ e < 81, posOf (rtProd e) ∈ uRt := fun e he => by
    simpa using hcont e he
  have hpos : ∀ e < 81, posOf (rtProd e) < 729 := fun e he => hlt' _ (hmem e he)
  have hinj : Set.InjOn (fun e => posOf (rtProd e)) (Finset.range 81 : Set ℕ) := by
    intro e he e' he' h
    have he1 : e < 81 := by simpa using he
    have he1' : e' < 81 := by simpa using he'
    have h1 := posOf_spec (hpos e he1)
    have h2 := posOf_spec (hpos e' he1')
    exact rtProd_injective hrt he1 he1' (h1.symm.trans ((congrArg uAt h).trans h2))
  have hcardT : ((Finset.range 81).image fun e => posOf (rtProd e)).card = 81 := by
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hsub : ((Finset.range 81).image fun e => posOf (rtProd e)) ⊆ uRt.toFinset := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (hmem e (by simpa using he))
  have hcard : uRt.toFinset.card ≤ 81 := (List.toFinset_card_le uRt).trans hlen.le
  have heq : (Finset.range 81).image (fun e => posOf (rtProd e)) = uRt.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hT : t ∈ (Finset.range 81).image fun e => posOf (rtProd e) := by
    rw [heq]
    exact List.mem_toFinset.mpr ht
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hT
  have he81 : e < 81 := by simpa using he
  have e1 : sAt (posOf (rtProd e)) = prodX e := by
    apply toMat_injective
    rw [toMat_sAt hsyl (hpos e he81), posOf_spec (hpos e he81), toMat_prodX hsyl hrt]
  rw [e1]
  exact prodX_mem e

theorem sAt_mem_rtS_of_inRt (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {t : ℕ}
    (h : inRt t = true) : sAt t ∈ rtS :=
  sAt_mem_rtS_of_mem_uRt hsyl hrt (inRt_spec h).2

theorem toMat_conj_word {w : List ℕ} (hw : ∀ l ∈ w, l < 4) {g : SUg} {x : List ℕ}
    (hx : toMat g = dec4 x) :
    toMat (wordElem w * g * (wordElem w)⁻¹) = dec4 (conjStep (wordPair w) x) := by
  rw [dec4_conjStep w hw x, ← hx, map_mul, map_mul]
  rfl

theorem conj_mem_rtS (hsyl : uSylCheck = true) (hrt : uRtCheck = true) {w : List ℕ}
    (hw : ∀ l ∈ w, l < 4) {g : SUg} {x : List ℕ} (hx : toMat g = dec4 x)
    (h : inRt (posOf (conjStep (wordPair w) x)) = true) :
    wordElem w * g * (wordElem w)⁻¹ ∈ rtS := by
  obtain ⟨hlt, -⟩ := inRt_spec h
  have e : wordElem w * g * (wordElem w)⁻¹ = sAt (posOf (conjStep (wordPair w) x)) := by
    apply toMat_injective
    rw [toMat_conj_word hw hx, toMat_sAt hsyl hlt, posOf_spec hlt]
  rw [e]
  exact sAt_mem_rtS_of_inRt hsyl hrt h

theorem exists_sAt_of_mem (hsyl : uSylCheck = true) {g : SUg} (hg : g ∈ sylS) :
    ∃ t < 729, g = sAt t := by
  obtain ⟨t, ht, e⟩ := exists_code_sylS hsyl hg
  exact ⟨t, ht, toMat_injective (e.symm.trans (toMat_sAt hsyl ht).symm)⟩

theorem lt_four_of_wordOK {w : List ℕ} (h : wordOK w = true) : ∀ l ∈ w, l < 4 := by
  simpa [wordOK] using h

theorem kind3_conj (hsyl : uSylCheck = true) (hk : uKindCheck = true) {p : ℕ} (hp : p < 729)
    (h3 : kindAt p = 3) :
    ∃ w : List ℕ, (∀ l ∈ w, l < 4) ∧ wordElem w * sAt p * (wordElem w)⁻¹ = sAt uB0 := by
  simp only [uKindCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hk
  obtain ⟨⟨⟨hlen, hB0⟩, hall⟩, -⟩ := hk
  have hkind : uKind.getD p 0 = 3 := by
    have : kindAt p = uKind.getD p 0 := by
      unfold kindAt uKindArr
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [← this]
    exact h3
  have h := hall p hp
  unfold kindOK at h
  rw [hkind] at h
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨convDWord p, lt_four_of_wordOK h.1, ?_⟩
  apply toMat_injective
  rw [toMat_conj_word (lt_four_of_wordOK h.1) (toMat_sAt hsyl hp), h.2, toMat_sAt hsyl hB0]

theorem one_conj_eq (b : SUg) : (1 : SUg) * b * (1 : SUg)⁻¹ = b := by
  group

theorem conj_conj_eq (u g b : SUg) : u * (g * b * g⁻¹) * u⁻¹ = u * g * b * (u * g)⁻¹ := by
  group

theorem orbitBuild_mem {P : List ℕ → Prop} {x₀ : List ℕ} {gens : List (List ℕ)}
    (hP0 : P x₀) (hstep : ∀ x, P x → ∀ c, c ∈ gens ∨ c = wordPair [] → P (conjStep c x))
    (par : List (ℕ × ℕ)) : ∀ x ∈ orbitBuild x₀ gens par, P x := by
  have key : ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)), (∀ x ∈ acc, P x) →
      ∀ x ∈ par.foldl (fun acc ps =>
        acc.push (conjStep (gens.getD ps.2 (wordPair [])) (acc.getD ps.1 x₀))) acc, P x := by
    intro par
    induction par with
    | nil => exact fun acc h => h
    | cons ps par ih =>
      intro acc h
      rw [List.foldl_cons]
      refine ih _ fun x hx => ?_
      rcases Array.mem_push.mp hx with hx | rfl
      · exact h x hx
      · refine hstep _ ?_ _ ?_
        · rw [Array.getD]
          split_ifs with hi
          · exact h _ (Array.getElem_mem hi)
          · exact hP0
        · rw [List.getD_eq_getElem?_getD]
          cases hi : gens[ps.2]? with
          | none => exact Or.inr rfl
          | some c => exact Or.inl (List.mem_of_getElem? hi)
  exact key par #[x₀] (fun x hx => by rw [Array.mem_singleton.mp hx]; exact hP0)

theorem conj_step_spec {x : List ℕ} {g : SUg} (hg : dec4 x = toMat (g * sAt uB0 * g⁻¹))
    {w : List ℕ} (hw : ∀ l ∈ w, l < 4) :
    ∃ g' : SUg, dec4 (conjStep (wordPair w) x) = toMat (g' * sAt uB0 * g'⁻¹) :=
  ⟨wordElem w * g, by rw [← conj_conj_eq]; exact (toMat_conj_word hw hg.symm).symm⟩

theorem uOrbit_spec (hsyl : uSylCheck = true) (hB0 : uB0 < 729) :
    ∀ x ∈ uOrbit, canon4 x = true ∧ ∃ g : SUg, dec4 x = toMat (g * sAt uB0 * g⁻¹) := by
  refine orbitBuild_mem (P := fun x => canon4 x = true ∧
    ∃ g : SUg, dec4 x = toMat (g * sAt uB0 * g⁻¹)) ?_ ?_ _
  · exact ⟨canon4_uAt hsyl hB0, 1, by rw [one_conj_eq]; exact (toMat_sAt hsyl hB0).symm⟩
  · rintro x ⟨-, g, hg⟩ c hc
    refine ⟨canon4_mul4 _ _, ?_⟩
    rcases hc with hc | hc
    · simp only [orbGens, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact conj_step_spec hg (w := [0]) (by simp)
      · exact conj_step_spec hg (w := [1]) (by simp)
    · rw [hc]
      exact conj_step_spec hg (w := []) (by simp)

theorem piU_injOn_order3 {x y : SUg} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (h : piU x = piU y) :
    x = y := by
  have h1 : piU (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := piU_eq_one_iff.mp h1
  have hs' : toMat (x⁻¹ * y) = Matrix.scalar (Fin 4) (c : F9) := by
    rw [toMat_apply, ← hc]
    rfl
  have hxs : Commute x (x⁻¹ * y) := by
    apply toMat_injective
    have e1 : toMat (x * (x⁻¹ * y)) = toMat x * Matrix.scalar (Fin 4) (c : F9) := by
      rw [map_mul, hs']
    have e2 : toMat ((x⁻¹ * y) * x) = Matrix.scalar (Fin 4) (c : F9) * toMat x := by
      rw [map_mul, hs']
    exact e1.trans ((Matrix.scalar_commute (c : F9) (fun _ => Commute.all _ _)
      (toMat x)).eq.symm.trans e2.symm)
  have hs3 : (x⁻¹ * y) ^ 3 = 1 := by
    have e : y ^ 3 = x ^ 3 * (x⁻¹ * y) ^ 3 := by
      have := hxs.mul_pow 3
      rwa [mul_inv_cancel_left] at this
    rw [hy, hx, one_mul] at e
    exact e.symm
  have hc3 : c ^ 729 = 1 := by
    have h3 : (Matrix.GeneralLinearGroup.scalar (Fin 4) c) ^ 3 = 1 := by
      rw [hc]
      exact congrArg Subtype.val hs3
    have h729 : (Matrix.GeneralLinearGroup.scalar (Fin 4) c) ^ 729 = 1 := by
      rw [show (729 : ℕ) = 3 * 243 by norm_num, pow_mul, h3, one_pow]
    rw [← map_pow] at h729
    exact scalar_injective (by rw [h729, map_one])
  have hc1 := eq_one_of_scalar_pow hc3
  rw [hc1, map_one] at hc
  have hs1 : x⁻¹ * y = 1 := Subtype.ext hc.symm
  exact inv_mul_eq_one.mp hs1

instance finiteUX : Finite UX :=
  Nat.finite_of_card_ne_zero (by rw [card_UX]; norm_num)

theorem uClassCheck_parts (h : uClassCheck = true) :
    uRtCheck = true ∧ uKindCheck = true ∧ uCentCheck = true ∧ uOrbitCheck = true ∧
      uZCheck = true := by
  simp only [uClassCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem uB0_lt (hk : uKindCheck = true) : uB0 < 729 := by
  simp only [uKindCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  exact hk.1.1.2

theorem sAt_uB0_cube (hsyl : uSylCheck = true) (hk : uKindCheck = true)
    (hc : uCentCheck = true) : sAt uB0 ^ 3 = 1 := by
  simp only [uCentCheck, Bool.and_eq_true, beq_iff_eq] at hc
  exact pow_three_of_cube4 hsyl (uB0_lt hk) (by simpa using hc.1)

theorem conj_pow_three_eq_one {b : SUg} (hb : b ^ 3 = 1) (g : SUg) : (g * b * g⁻¹) ^ 3 = 1 := by
  rw [conj_pow, hb, mul_one, mul_inv_cancel]

theorem card_conjugates_ge (hsyl : uSylCheck = true) (hcls : uClassCheck = true) :
    40320 ≤ (conjugatesOf (piU (sAt uB0))).ncard := by
  obtain ⟨-, hk, hc, ho, -⟩ := uClassCheck_parts hcls
  have hB0 := uB0_lt hk
  have hb3 := sAt_uB0_cube hsyl hk hc
  simp only [uOrbitCheck, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨hsize, hdist⟩ := ho
  have hspec := uOrbit_spec hsyl hB0
  choose! G hG using fun x hx => (hspec x hx).2
  let y : ℕ → SUg := fun t => G (uOrbit.getD t []) * sAt uB0 * (G (uOrbit.getD t []))⁻¹
  have hmem : ∀ t < 40320, uOrbit.getD t [] ∈ uOrbit := fun t ht => by
    have ht' : t < uOrbit.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht', Option.getD_some]
    exact Array.getElem_mem ht'
  have hy3 : ∀ t, y t ^ 3 = 1 := fun t => conj_pow_three_eq_one hb3 _
  have hycode : ∀ t < 40320, toMat (y t) = dec4 (uOrbit.getD t []) := fun t ht =>
    (hG _ (hmem t ht)).symm
  have hinj : Set.InjOn (fun t => piU (y t)) (Finset.range 40320 : Set ℕ) := by
    intro t ht t' ht' e
    have ht1 : t < 40320 := by simpa using ht
    have ht1' : t' < 40320 := by simpa using ht'
    have e1 := piU_injOn_order3 (hy3 t) (hy3 t') e
    have e2 : dec4 (uOrbit.getD t []) = dec4 (uOrbit.getD t' []) := by
      rw [← hycode t ht1, ← hycode t' ht1', e1]
    have c1 := (uOrbit_spec hsyl hB0 _ (hmem t ht1)).1
    have c2 := (uOrbit_spec hsyl hB0 _ (hmem t' ht1')).1
    exact distinctCheck_spec hdist (by omega) (by omega) (dec4_injective c1 c2 e2)
  have hsub : (fun t => piU (y t)) '' (Finset.range 40320 : Set ℕ) ⊆
      conjugatesOf (piU (sAt uB0)) := by
    rintro _ ⟨t, -, rfl⟩
    show IsConj _ _
    rw [isConj_iff]
    refine ⟨piU (G (uOrbit.getD t [])), ?_⟩
    simp only [y, map_mul, map_inv]
  calc 40320 = (Finset.range 40320 : Set ℕ).ncard := by rw [Set.ncard_coe_finset]; simp
    _ = ((fun t => piU (y t)) '' (Finset.range 40320 : Set ℕ)).ncard :=
        ((Set.ncard_image_iff (Finset.finite_toSet _)).mpr hinj).symm
    _ ≤ (conjugatesOf (piU (sAt uB0))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_centralizer_b0_le (hsyl : uSylCheck = true) (hcls : uClassCheck = true) :
    Nat.card (Subgroup.centralizer ({piU (sAt uB0)} : Set UX)) ≤ 81 := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({piU (sAt uB0)} : Set UX))
  rw [Subgroup.index_centralizer_eq_ncard, card_UX] at h
  have h2 := card_conjugates_ge hsyl hcls
  by_contra hlt
  push Not at hlt
  have : 82 * 40320 ≤ Nat.card (Subgroup.centralizer ({piU (sAt uB0)} : Set UX)) *
      (conjugatesOf (piU (sAt uB0))).ncard := Nat.mul_le_mul hlt h2
  omega

theorem card_centralizer_b0_ge (hsyl : uSylCheck = true) (hcls : uClassCheck = true) :
    81 ≤ Nat.card (Subgroup.centralizer ({piU (sAt uB0)} : Set UX)) := by
  obtain ⟨-, hk, hc, -, -⟩ := uClassCheck_parts hcls
  simp only [uCentCheck, Bool.and_eq_true, beq_iff_eq] at hc
  set L := (List.range 729).filter fun q => commutes4 (uAt q) (uAt uB0) with hL
  have hLlen : L.length = 81 := hc.2
  have hnd : L.Nodup := List.nodup_range.filter _
  have hmemL : ∀ q ∈ L, q < 729 ∧ commutes4 (uAt q) (uAt uB0) = true := fun q hq => by
    simpa [hL] using hq
  have hinj : Set.InjOn (fun q => piU (sAt q)) (L.toFinset : Set ℕ) := by
    intro q hq q' hq' e
    have hq1 := (hmemL q (by simpa using hq)).1
    have hq1' := (hmemL q' (by simpa using hq')).1
    exact sAt_injective hsyl hq1 hq1'
      (piU_injOn_sylS hsyl (sAt_mem hsyl hq1) (sAt_mem hsyl hq1') e)
  have hmaps : ∀ q ∈ (L.toFinset : Set ℕ), piU (sAt q) ∈
      (Subgroup.centralizer ({piU (sAt uB0)} : Set UX) : Set UX) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hmemL q (by simpa using hq)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [← map_mul, ← map_mul, (commute_of_commutes4 hsyl hq1 (uB0_lt hk) hq2)]
  calc 81 = L.toFinset.card := by rw [List.toFinset_card_of_nodup hnd, hLlen]
    _ = (L.toFinset : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (Subgroup.centralizer ({piU (sAt uB0)} : Set UX) : Set UX).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
    _ = Nat.card (Subgroup.centralizer ({piU (sAt uB0)} : Set UX)) :=
        (Nat.card_coe_set_eq _).symm

theorem isPGroup_centralizer_b0 (hsyl : uSylCheck = true) (hcls : uClassCheck = true) :
    IsPGroup 3 (Subgroup.centralizer ({piU (sAt uB0)} : Set UX)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h81 : Nat.card (Subgroup.centralizer ({piU (sAt uB0)} : Set UX)) = 3 ^ 4 :=
    le_antisymm (card_centralizer_b0_le hsyl hcls) (card_centralizer_b0_ge hsyl hcls)
  exact IsPGroup.of_card h81

theorem pow_eq_one_of_conj_pow {X : Type*} [Group X] {t x : X} {n : ℕ}
    (h : (t * x * t⁻¹) ^ n = 1) : x ^ n = 1 := by
  rw [conj_pow] at h
  have h2 := congrArg (fun z => t⁻¹ * z * t) h
  simpa [mul_assoc] using h2

theorem isPGroup_centralizer_kind3 (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    {p : ℕ} (hp : p < 729) (h3 : kindAt p = 3) :
    IsPGroup 3 (Subgroup.centralizer ({piU (sAt p)} : Set UX)) := by
  obtain ⟨-, hk, -, -, -⟩ := uClassCheck_parts hcls
  obtain ⟨w, -, hw⟩ := kind3_conj hsyl hk hp h3
  have hC0 := isPGroup_centralizer_b0 hsyl hcls
  intro x
  set t : UX := piU (wordElem w) with ht
  have hconj : t * piU (sAt p) * t⁻¹ = piU (sAt uB0) := by
    rw [ht, ← map_inv, ← map_mul, ← map_mul, hw]
  have hx : t * (x : UX) * t⁻¹ ∈ Subgroup.centralizer ({piU (sAt uB0)} : Set UX) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have hxc : piU (sAt p) * (x : UX) = (x : UX) * piU (sAt p) :=
      (Subgroup.mem_centralizer_iff.mp x.2) _ rfl
    rw [← hconj]
    calc t * piU (sAt p) * t⁻¹ * (t * (x : UX) * t⁻¹)
        = t * (piU (sAt p) * (x : UX)) * t⁻¹ := by group
      _ = t * ((x : UX) * piU (sAt p)) * t⁻¹ := by rw [hxc]
      _ = t * (x : UX) * t⁻¹ * (t * piU (sAt p) * t⁻¹) := by group
  obtain ⟨k, hk'⟩ := hC0 ⟨_, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  exact pow_eq_one_of_conj_pow (congrArg Subtype.val hk')

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
