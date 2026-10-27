module

public import CFSG.LieType.Chevalley.RootOps.Sparse
public import TauCeti.Algebra.Lie.F4.ShortRoot.AdmissibleLattice

public section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.LieType.Chevalley.RootOps

abbrev SpMat : Type := List (Fin 26 × Fin 26 × ℤ)

@[expose] def ent (L : SpMat) (r c : Fin 26) : ℤ :=
  (L.map fun e => if e.1 = r ∧ e.2.1 = c then e.2.2 else 0).sum

@[expose] def smat (L : SpMat) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun r c => ent L r c

@[expose] def negL (L : SpMat) : SpMat :=
  L.map fun e => (e.1, e.2.1, -e.2.2)

@[expose] def scaleL (z : ℤ) (L : SpMat) : SpMat :=
  L.map fun e => (e.1, e.2.1, z * e.2.2)

@[expose] def mulL (A B : SpMat) : SpMat :=
  A.flatMap fun a => (B.filter fun b => b.1 == a.2.1).map fun b => (a.1, b.2.1, a.2.2 * b.2.2)

@[expose] def keyed (L : SpMat) : List (ℕ × ℤ) :=
  L.map fun e => (26 * (e.1 : ℕ) + e.2.1, e.2.2)

@[expose] def kval (v : List (ℕ × ℤ)) (k : ℕ) : ℤ :=
  (v.map fun x => if x.1 = k then x.2 else 0).sum

@[simp] theorem ent_nil (r c : Fin 26) : ent [] r c = 0 :=
  rfl

theorem ent_cons (e : Fin 26 × Fin 26 × ℤ) (L : SpMat) (r c : Fin 26) :
    ent (e :: L) r c = (if e.1 = r ∧ e.2.1 = c then e.2.2 else 0) + ent L r c := by
  simp [ent]

theorem ent_append (L L' : SpMat) (r c : Fin 26) : ent (L ++ L') r c = ent L r c + ent L' r c := by
  simp [ent]

theorem ent_negL (L : SpMat) (r c : Fin 26) : ent (negL L) r c = -ent L r c := by
  induction L with
  | nil => simp [negL]
  | cons e L ih =>
    simp only [negL, List.map_cons] at ih ⊢
    rw [ent_cons, ent_cons, ih]
    dsimp only
    split_ifs <;> ring

theorem ent_scaleL (z : ℤ) (L : SpMat) (r c : Fin 26) : ent (scaleL z L) r c = z * ent L r c := by
  induction L with
  | nil => simp [scaleL]
  | cons e L ih =>
    simp only [scaleL, List.map_cons] at ih ⊢
    rw [ent_cons, ent_cons, ih]
    dsimp only
    split_ifs <;> ring

theorem ent_flatMap {ι : Type*} (l : List ι) (f : ι → SpMat) (r c : Fin 26) :
    ent (l.flatMap f) r c = (l.map fun i => ent (f i) r c).sum := by
  induction l with
  | nil => simp [ent]
  | cons i l ih => rw [List.flatMap_cons, ent_append, ih, List.map_cons, List.sum_cons]

theorem ent_mulL_single (a : Fin 26 × Fin 26 × ℤ) (B : SpMat) (r c : Fin 26) :
    ent ((B.filter fun b => b.1 == a.2.1).map fun b => (a.1, b.2.1, a.2.2 * b.2.2)) r c =
      if a.1 = r then a.2.2 * ent B a.2.1 c else 0 := by
  induction B with
  | nil => simp [ent]
  | cons b B ih =>
    rw [List.filter_cons, ent_cons]
    by_cases hb : b.1 = a.2.1
    · rw [ite_eq_left (by simpa using hb), List.map_cons, ent_cons, ih]
      dsimp only
      by_cases ha : a.1 = r
      · by_cases hc : b.2.1 = c
        · simp only [ha, hc, hb, and_self, ite_true]
          ring
        · simp only [ha, hc, hb, and_false, ite_false, ite_true, zero_add]
      · simp only [ha, false_and, ite_false, add_zero]
    · rw [ite_eq_right (by simpa using hb), ih]
      by_cases ha : a.1 = r
      · simp only [ha, hb, false_and, ite_false, ite_true, zero_add]
      · simp only [ha, ite_false]

theorem ent_mulL (A B : SpMat) (r c : Fin 26) :
    ent (mulL A B) r c = (A.map fun a => if a.1 = r then a.2.2 * ent B a.2.1 c else 0).sum := by
  rw [mulL, ent_flatMap]
  congr 1
  exact List.map_congr_left fun a _ => ent_mulL_single a B r c

@[simp] theorem smat_nil : smat [] = 0 := by
  ext r c
  rfl

theorem smat_append (L L' : SpMat) : smat (L ++ L') = smat L + smat L' := by
  ext r c
  simp [smat, ent_append]

theorem smat_negL (L : SpMat) : smat (negL L) = -smat L := by
  ext r c
  simp [smat, ent_negL]

theorem smat_scaleL (z : ℤ) (L : SpMat) : smat (scaleL z L) = z • smat L := by
  ext r c
  simp [smat, ent_scaleL]

theorem smat_flatMap {ι : Type*} (l : List ι) (f : ι → SpMat) :
    smat (l.flatMap f) = (l.map fun i => smat (f i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.flatMap_cons, smat_append, ih, List.map_cons, List.sum_cons]

theorem smat_mulL (A B : SpMat) : smat (mulL A B) = smat A * smat B := by
  ext r c
  simp only [smat, Matrix.of_apply, Matrix.mul_apply, ent_mulL]
  induction A with
  | nil => simp [ent]
  | cons a A ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [ent_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single a.2.1]
    · split_ifs with h1 h2 h2 <;> simp_all
    · intro k _ hk
      split_ifs with h
      · exact absurd h.2 (Ne.symm hk)
      · simp
    · simp

theorem kval_nil (k : ℕ) : kval [] k = 0 :=
  rfl

theorem kval_cons (x : ℕ × ℤ) (v : List (ℕ × ℤ)) (k : ℕ) :
    kval (x :: v) k = (if x.1 = k then x.2 else 0) + kval v k := by
  simp [kval]

theorem kval_insertCoeff (x : ℕ × ℤ) (v : List (ℕ × ℤ)) (k : ℕ) :
    kval (insertCoeff x v) k = (if x.1 = k then x.2 else 0) + kval v k := by
  induction v with
  | nil => simp [insertCoeff, kval]
  | cons y v ih =>
    unfold insertCoeff
    by_cases h₁ : x.1 < y.1
    · rw [ite_eq_left h₁, kval_cons]
    · rw [ite_eq_right h₁]
      by_cases h₂ : x.1 = y.1
      · rw [ite_eq_left h₂, kval_cons, kval_cons]
        dsimp only
        by_cases hk : x.1 = k
        · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left (h₂ ▸ hk)]
          ring
        · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right (fun h => hk (h₂.trans h))]
          ring
      · rw [ite_eq_right h₂, kval_cons, ih, kval_cons]
        ring

theorem kval_filter (v : List (ℕ × ℤ)) (k : ℕ) :
    kval (v.filter fun x => x.2 != 0) k = kval v k := by
  induction v with
  | nil => rfl
  | cons y v ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [kval_cons, ih, kval_cons]
    · simp only [bne_iff_ne, ne_eq, not_not] at h
      rw [ih, kval_cons, h, ite_self, zero_add]

theorem kval_normalize (v : List (ℕ × ℤ)) (k : ℕ) : kval (normalize v) k = kval v k := by
  rw [CFSG.LieType.Chevalley.RootOps.normalize, kval_filter]
  induction v with
  | nil => rfl
  | cons x v ih => rw [List.foldr_cons, kval_insertCoeff, ih, kval_cons]

theorem kval_keyed (L : SpMat) (r c : Fin 26) : kval (keyed L) (26 * (r : ℕ) + c) = ent L r c := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [keyed, List.map_cons, kval_cons, ← keyed, ih, ent_cons]
    congr 1
    have hiff : 26 * (e.1 : ℕ) + e.2.1 = 26 * (r : ℕ) + c ↔ e.1 = r ∧ e.2.1 = c := by
      constructor
      · intro h
        have h1 := e.2.1.2
        have h2 := c.2
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [hiff]

theorem smat_eq_of_normalize_eq {A B : SpMat} (h : normalize (keyed A) = normalize (keyed B)) :
    smat A = smat B := by
  ext r c
  simp only [smat, Matrix.of_apply]
  rw [← kval_keyed, ← kval_keyed, ← kval_normalize, h, kval_normalize]

@[expose] def eqB (A B : SpMat) : Bool :=
  normalize (keyed A) == normalize (keyed B)

theorem smat_eq_of_eqB {A B : SpMat} (h : eqB A B = true) : smat A = smat B :=
  smat_eq_of_normalize_eq (beq_iff_eq.mp h)

@[expose] def tcE : Fin 4 ⊕ Fin 4 → Matrix (Fin 26) (Fin 26) ℤ
  | .inl i => TauCeti.F4ShortRoot.raisingMatrix i
  | .inr i => TauCeti.F4ShortRoot.loweringMatrix i

@[expose] def tcE2 : Fin 4 ⊕ Fin 4 → Matrix (Fin 26) (Fin 26) ℤ
  | .inl i => TauCeti.F4ShortRoot.raisingDividedSquareMatrix i
  | .inr i => TauCeti.F4ShortRoot.loweringDividedSquareMatrix i

theorem rootMatrix_eq_tcE (k : Fin 4 ⊕ Fin 4) : TauCeti.F4ShortRoot.rootMatrix k = tcE k := by
  rcases k with i | i
  · exact TauCeti.F4ShortRoot.rootMatrix_inl i
  · exact TauCeti.F4ShortRoot.rootMatrix_inr i

theorem rootDividedSquareMatrix_eq_tcE2 (k : Fin 4 ⊕ Fin 4) :
    TauCeti.F4ShortRoot.rootDividedSquareMatrix k = tcE2 k := by
  rcases k with i | i
  · exact TauCeti.F4ShortRoot.rootDividedSquareMatrix_inl i
  · exact TauCeti.F4ShortRoot.rootDividedSquareMatrix_inr i

@[expose] def stepL (t : Fin 26 → Fin 26) (z : Fin 26 → ℤ) : SpMat :=
  (List.finRange 26).filterMap fun b => if z b = 0 then none else some (t b, b, z b)

@[expose] def spE : Fin 4 ⊕ Fin 4 → SpMat
  | .inl i => stepL (TauCeti.F4ShortRoot.raisingTarget i) (TauCeti.F4ShortRoot.raisingCoeff i)
  | .inr i => stepL (TauCeti.F4ShortRoot.loweringTarget i) (TauCeti.F4ShortRoot.loweringCoeff i)

@[expose] def spE2 : Fin 4 ⊕ Fin 4 → SpMat
  | .inl i => stepL (TauCeti.F4ShortRoot.raisingDividedSquareTarget i)
      (TauCeti.F4ShortRoot.raisingDividedSquareCoeff i)
  | .inr i => stepL (TauCeti.F4ShortRoot.loweringDividedSquareTarget i)
      (TauCeti.F4ShortRoot.loweringDividedSquareCoeff i)

theorem ent_stepL_check : ∀ (i : Fin 4) (a b : Fin 26),
    ent (spE (.inl i)) a b = (if a = TauCeti.F4ShortRoot.raisingTarget i b then
        TauCeti.F4ShortRoot.raisingCoeff i b else 0) ∧
      ent (spE (.inr i)) a b = (if a = TauCeti.F4ShortRoot.loweringTarget i b then
        TauCeti.F4ShortRoot.loweringCoeff i b else 0) ∧
      ent (spE2 (.inl i)) a b = (if a = TauCeti.F4ShortRoot.raisingDividedSquareTarget i b then
        TauCeti.F4ShortRoot.raisingDividedSquareCoeff i b else 0) ∧
      ent (spE2 (.inr i)) a b = (if a = TauCeti.F4ShortRoot.loweringDividedSquareTarget i b then
        TauCeti.F4ShortRoot.loweringDividedSquareCoeff i b else 0) := by
  decide +kernel

theorem smat_spE (k : Fin 4 ⊕ Fin 4) : smat (spE k) = tcE k := by
  ext a b
  rcases k with i | i
  · rw [tcE, TauCeti.F4ShortRoot.raisingMatrix_apply]
    exact (ent_stepL_check i a b).1
  · rw [tcE, TauCeti.F4ShortRoot.loweringMatrix_apply]
    exact (ent_stepL_check i a b).2.1

theorem smat_spE2 (k : Fin 4 ⊕ Fin 4) : smat (spE2 k) = tcE2 k := by
  ext a b
  rcases k with i | i
  · rw [tcE2, TauCeti.F4ShortRoot.raisingDividedSquareMatrix_apply]
    exact (ent_stepL_check i a b).2.2.1
  · rw [tcE2, TauCeti.F4ShortRoot.loweringDividedSquareMatrix_apply]
    exact (ent_stepL_check i a b).2.2.2

@[expose] def decodeL : ℕ → ℕ → SpMat
  | 0, _ => []
  | fuel + 1, code =>
    if code = 0 then []
    else
      (⟨code % 2 ^ 14 / 32 % 32 % 26, Nat.mod_lt _ (by norm_num)⟩,
        ⟨code % 2 ^ 14 % 32 % 26, Nat.mod_lt _ (by norm_num)⟩,
        ((code % 2 ^ 14 / 1024 : ℕ) : ℤ) - 8) :: decodeL fuel (code / 2 ^ 14)

@[expose] def basisCodes : List ℕ := [
  227046102449195444267357207353248179427630697749603,
  181034537150006070663050786994285509690414429955138,
  4420865083933349649432445343925033260895601691769043276998540841523126246433,
  3530871975221443945169744591476511722312096763424101089232291385573913420800,
  11700372339131153277101156,
  9321327956391364962425923,
  13905355009710195717101542636375470534238495778,
  11096675060895999373529155748376439745453612033,
  9318973691241906660531331,
  9283696679554569682428996,
  11775929986666727662003298,
  11664945429474974097384485,
  13860579379478907238756076916929808654956321827,
  11093898357612721803402406728626360921027566657,
  181080030836438344720850710981199425959568602686466,
  13994557650196009157752959128644336741584036896,
  9356900061940685765436546,
  11627019004732999464557606,
  9393352989664063924542625,
  9172704997524178487991303,
  13815975156194928349217163849180927429602026532,
  180346426910728915589713451201449258358141116079107,
  13947002679332128425290217116361931573378456673,
  182496033391564531147310560756616177152901923791936,
  11810026343396538793909441,
  11551608786736344170931240,
  9096999622900458727400457,
  11846622008628168705516768,
  179615586714953807103911379851173723799961231057924,
  10918443674308352175901915095015598946316313605,
  11091287637012735931401908336396469205218663553,
  229241294250166145513318432952312419311894409028704,
  9389815817752876634119425,
  9426411492141771756463392,
  9021589404902703922142219,
  10873836728764139804390723336942588583920425990,
  182447548612237820135622997609672258639463505765504,
  11134497973153880215016254953403096589330310304,
  11841904262971024804980064,
  8908100504467871820962830,
  10784628314091142517323678294763499185389626376,
  13987425167444008473518461008958417299176973504,
  11838512215054229936039360,
  8832538020053129305580560,
  175230949561236361139108520607848055711781068938250,
  11130316243479116044558444796123659426017600768,
  9418151674657045988533760,
  8756977850342918759193618,
  10561435747668083083749171749538123240704272396,
  229081480149077256584582703103095327900050634335552,
  11833789641542674952513088,
  11124482256639279447696000030599628750719575424]

@[expose] def coordCodes : List ℕ := [
  119069762,
  2491769447424,
  117988352,
  9216,
  9316,
  7235,
  9250,
  7169,
  7299,
  9284,
  9314,
  9253,
  7203,
  7233,
  9218,
  9248,
  9346,
  7206,
  7329,
  7175,
  9252,
  7171,
  7265,
  9280,
  7361,
  9256,
  9225,
  9440,
  9220,
  9221,
  7297,
  9312,
  7425,
  9504,
  7179,
  7174,
  9344,
  9376,
  9568,
  7182,
  9224,
  9408,
  9664,
  9232,
  7178,
  9472,
  9728,
  7186,
  9229,
  9536,
  9792,
  9600]

@[expose] def bL (p : ℕ) : SpMat :=
  decodeL 32 (basisCodes.getD p 0)

@[expose] def cL (p : ℕ) : SpMat :=
  decodeL 32 (coordCodes.getD p 0)

@[expose] def bMat (p : ℕ) : Matrix (Fin 26) (Fin 26) ℤ :=
  smat (bL p)

variable {R : Type*} [CommRing R]

@[expose] def coord (p : ℕ) (Y : Matrix (Fin 26) (Fin 26) R) : R :=
  ((cL p).map fun e => (e.2.2 : R) * Y e.1 e.2.1).sum

theorem coord_bMat_check :
    ∀ p < 52, ∀ q < 52, coord p (bMat q) = if p = q then 1 else 0 := by
  decide +kernel

abbrev bMatR (R : Type*) [CommRing R] (p : ℕ) : Matrix (Fin 26) (Fin 26) R :=
  (bMat p).map (Int.cast : ℤ → R)

theorem coord_add (p : ℕ) (Y Z : Matrix (Fin 26) (Fin 26) R) :
    coord p (Y + Z) = coord p Y + coord p Z := by
  simp only [coord, Matrix.add_apply, mul_add, List.sum_map_add]

theorem coord_smul (p : ℕ) (a : R) (Y : Matrix (Fin 26) (Fin 26) R) :
    coord p (a • Y) = a * coord p Y := by
  simp only [coord, Matrix.smul_apply, smul_eq_mul, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun e _ => by ring

theorem coord_zero (p : ℕ) : coord p (0 : Matrix (Fin 26) (Fin 26) R) = 0 := by
  simp [coord]

theorem coord_sum {ι : Type*} (S : Finset ι) (p : ℕ) (Y : ι → Matrix (Fin 26) (Fin 26) R) :
    coord p (∑ i ∈ S, Y i) = ∑ i ∈ S, coord p (Y i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coord_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, ih]

theorem map_coord {S : Type*} [CommRing S] (f : R →+* S) (p : ℕ)
    (Y : Matrix (Fin 26) (Fin 26) R) : f (coord p Y) = coord p (Y.map f) := by
  simp only [coord, map_list_sum, List.map_map, Function.comp_def, map_mul, map_intCast,
    Matrix.map_apply]

theorem coord_bMatR {p q : ℕ} (hp : p < 52) (hq : q < 52) :
    coord p (bMatR R q) = if p = q then 1 else 0 := by
  change coord p ((bMat q).map (Int.castRingHom R)) = _
  rw [← map_coord (Int.castRingHom R), coord_bMat_check p hp q hq]
  split_ifs <;> simp

theorem coord_sum_smul_bMatR (a : Fin 52 → R) (p : Fin 52) :
    coord p (∑ u : Fin 52, a u • bMatR R u) = a p := by
  rw [coord_sum]
  simp only [coord_smul, coord_bMatR p.2 (Fin.is_lt _), mul_ite, mul_one, mul_zero,
    Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

@[expose] def InSpan (Y : Matrix (Fin 26) (Fin 26) R) : Prop :=
  ∃ a : Fin 52 → R, Y = ∑ u : Fin 52, a u • bMatR R u

theorem InSpan.eq_sum {Y : Matrix (Fin 26) (Fin 26) R} (h : InSpan Y) :
    Y = ∑ u : Fin 52, coord u Y • bMatR R u := by
  obtain ⟨a, rfl⟩ := h
  simp only [coord_sum_smul_bMatR]

theorem inSpan_iff {Y : Matrix (Fin 26) (Fin 26) R} :
    InSpan Y ↔ Y = ∑ u : Fin 52, coord u Y • bMatR R u :=
  ⟨InSpan.eq_sum, fun h => ⟨_, h⟩⟩

theorem inSpan_bMatR (p : Fin 52) : InSpan (bMatR R p) :=
  ⟨fun u => if u = p then 1 else 0, by simp [ite_smul]⟩

end CFSG.TauCetiBridge.ReeF4
