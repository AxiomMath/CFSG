module

public import Certificates.Certificate617001
public import Certificates.Data.LieSylRootWt
public import CFSG.Blueprint.ChevalleyRootsInputs
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

@[expose] def wt (τ : Tag) (ℓ : ℕ) (β : Fin τ.rank → ℤ) : Fin τ.rank → ZMod ℓ :=
  (τ.cartan.map (Int.cast : ℤ → ZMod ℓ)).mulVec (fun j => (β j : ZMod ℓ))

def cvL (ℓ r : ℕ) (v : List ℤ) : Fin r → ZMod ℓ := fun i => ((v.getD i 0 : ℤ) : ZMod ℓ)

def gmat (ℓ r : ℕ) (gs : List (List ℤ)) : Matrix (Fin r) (Fin r) (ZMod ℓ) :=
  Matrix.of fun i j => (((gs.getD j []).getD i 0 : ℤ) : ZMod ℓ)

theorem sum_listRange_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem getD_combo (r : ℕ) (b : List ℤ) (gs : List (List ℤ)) (i : ℕ) :
    (Certificates.Data.LieSylRootWt.combo r b gs).getD i 0 =
      if i < r then Certificates.Data.LieSylRootWt.comboAt r b gs i else 0 := by
  unfold Certificates.Data.LieSylRootWt.combo
  by_cases hi : i < r
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

theorem cast_comboAt (ℓ r : ℕ) (b : List ℤ) (gs : List (List ℤ)) (i : ℕ) :
    ((Certificates.Data.LieSylRootWt.comboAt r b gs i : ℤ) : ZMod ℓ) =
      ∑ j ∈ Finset.range r, ((gs.getD j []).getD i 0 : ZMod ℓ) * ((b.getD j 0 : ℤ) : ZMod ℓ) := by
  unfold Certificates.Data.LieSylRootWt.comboAt
  rw [Int.cast_list_sum, List.map_map, sum_listRange_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

theorem cvL_combo (ℓ r : ℕ) (b : List ℤ) (gs : List (List ℤ)) :
    cvL ℓ r (Certificates.Data.LieSylRootWt.combo r b gs) = Matrix.mulVec (gmat ℓ r gs) (cvL ℓ r b) := by
  funext i
  have hi : (i : ℕ) < r := i.2
  simp only [cvL, getD_combo, if_pos hi, cast_comboAt, Matrix.mulVec, dotProduct, gmat,
    Matrix.of_apply]
  rw [Finset.sum_range]

theorem cvL_redV (ℓ r : ℕ) (v : List ℤ) :
    cvL ℓ r (Certificates.Data.LieSylRootWt.redV ℓ v) = cvL ℓ r v := by
  funext i
  have key : (v.map (Certificates.Data.LieSylRootWt.red ℓ)).getD i 0 =
      Certificates.Data.LieSylRootWt.red ℓ (v.getD i 0) := by
    have h := List.getD_map (Certificates.Data.LieSylRootWt.red ℓ) (l := v) (n := (i : ℕ))
      (d := 0)
    rwa [show Certificates.Data.LieSylRootWt.red ℓ 0 = 0 by simp [Certificates.Data.LieSylRootWt.red]]
      at h
  simp only [cvL, Certificates.Data.LieSylRootWt.redV, key, Certificates.Data.LieSylRootWt.red]
  exact ZMod.intCast_mod _ _

theorem cvL_unitVec (ℓ r : ℕ) (i : Fin r) :
    cvL ℓ r (Certificates.Data.LieSylRootWt.unitVec r (i : ℕ)) = Pi.single i 1 := by
  funext j
  have hj : (j : ℕ) < r := j.2
  simp only [cvL, Certificates.Data.LieSylRootWt.unitVec, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  rw [Pi.single_apply]
  by_cases h : (j : ℕ) = (i : ℕ)
  · have hji : j = i := Fin.ext h
    subst hji
    simp
  · have hji : j ≠ i := fun e => h (congrArg Fin.val e)
    simp [hji, h]

theorem redV_eq_of_cvL_eq (ℓ r : ℕ) {X Y : List ℤ} (hX : X.length = r) (hY : Y.length = r)
    (h : cvL ℓ r X = cvL ℓ r Y) : Certificates.Data.LieSylRootWt.redV ℓ X =
      Certificates.Data.LieSylRootWt.redV ℓ Y := by
  apply List.ext_getElem
  · simp [Certificates.Data.LieSylRootWt.redV, hX, hY]
  · intro n h1 h2
    simp only [Certificates.Data.LieSylRootWt.redV, List.getElem_map]
    have hn : n < r := by simpa [Certificates.Data.LieSylRootWt.redV, hX] using h1
    have := congrFun h ⟨n, hn⟩
    simp only [cvL, Fin.val_mk] at this
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    have hmod := (ZMod.intCast_eq_intCast_iff _ _ ℓ).1 this
    simp only [Certificates.Data.LieSylRootWt.red]
    exact hmod

theorem le_level_foldl (b : List ℤ) (n : ℕ) : ∀ (acc j : ℕ), j < n → b.getD j 0 ≠ 0 →
    j ≤ (List.range n).foldl (fun acc i => if b.getD i 0 ≠ 0 then i else acc) acc := by
  induction n with
  | zero => intro acc j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro acc j hj hb
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hn : b.getD n 0 ≠ 0
    · rw [if_pos hn]
      omega
    · rw [if_neg hn]
      have hjn : j ≠ n := fun h => hn (h ▸ hb)
      exact ih acc j (by omega) hb

theorem getD_eq_zero_of_level {r : ℕ} {b : List ℤ} {k : ℕ}
    (hk : Certificates.Data.LieSylRootWt.level r b = k) {j : ℕ} (hkj : k < j) (hjr : j < r) :
    b.getD j 0 = 0 := by
  by_contra hne
  have h1 := le_level_foldl b r 0 j hjr hne
  unfold Certificates.Data.LieSylRootWt.level at hk
  omega

theorem combo_congr (r : ℕ) (b : List ℤ) (gs gs' : List (List ℤ)) (k : ℕ)
    (hgs : ∀ j, j ≤ k → gs'.getD j [] = gs.getD j [])
    (hb : ∀ j, k < j → j < r → b.getD j 0 = 0) :
    Certificates.Data.LieSylRootWt.combo r b gs' = Certificates.Data.LieSylRootWt.combo r b gs := by
  unfold Certificates.Data.LieSylRootWt.combo
  congr 1
  funext i
  unfold Certificates.Data.LieSylRootWt.comboAt
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  by_cases hjk : j ≤ k
  · rw [hgs j hjk]
  · rw [hb j (by omega) hj]
    simp

theorem search_sound (ℓ e r : ℕ) (R gs : List (List ℤ)) (hlen : gs.length = r)
    (hmem : ∀ c ∈ gs, c ∈ R)
    (hclo : ∀ b ∈ R, ∃ c ∈ R, Certificates.Data.LieSylRootWt.redV ℓ
      (Certificates.Data.LieSylRootWt.combo r b gs) = Certificates.Data.LieSylRootWt.redV ℓ c) :
    ∀ (fuel k : ℕ) (p : List (List ℤ)), k + fuel = r → p = gs.take k →
      Certificates.Data.LieSylRootWt.searchOK ℓ e r R (R.map (Certificates.Data.LieSylRootWt.redV ℓ))
        ((List.range r).map fun k => R.filter fun b => Certificates.Data.LieSylRootWt.level r b == k)
        fuel k p = true →
      Certificates.Data.LieSylRootWt.orderOK ℓ e r gs = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro k p hk hp hs
    have hkr : k = r := by omega
    subst hkr
    have hpg : p = gs := by rw [hp, List.take_of_length_le (by omega)]
    subst hpg
    simpa [Certificates.Data.LieSylRootWt.searchOK] using hs
  | succ fuel ih =>
    intro k p hk hp hs
    have hkr : k < r := by omega
    rw [Certificates.Data.LieSylRootWt.searchOK, if_pos hkr] at hs
    have hgk : gs.getD k [] ∈ gs := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h1 := List.all_eq_true.1 hs (gs.getD k []) (hmem _ hgk)
    have hpt : p ++ [gs.getD k []] = gs.take (k + 1) := by
      have hk' : k < gs.length := by omega
      rw [hp, List.take_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      simp
    have hcl : (((List.range r).map fun k => R.filter fun b =>
        Certificates.Data.LieSylRootWt.level r b == k).getD k []).all
        (fun b => (R.map (Certificates.Data.LieSylRootWt.redV ℓ)).contains
          (Certificates.Data.LieSylRootWt.redV ℓ
            (Certificates.Data.LieSylRootWt.combo r b (p ++ [gs.getD k []])))) = true := by
      rw [List.all_eq_true]
      intro b hb
      have hlev : ((List.range r).map fun k => R.filter fun b =>
          Certificates.Data.LieSylRootWt.level r b == k).getD k [] =
          R.filter fun b => Certificates.Data.LieSylRootWt.level r b == k := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkr]
        simp
      rw [hlev, List.mem_filter] at hb
      obtain ⟨hbR, hbk⟩ := hb
      have hbk' : Certificates.Data.LieSylRootWt.level r b = k := by simpa using hbk
      have hgs : ∀ j, j ≤ k → (p ++ [gs.getD k []]).getD j [] = gs.getD j [] := by
        intro j hj
        rw [hpt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
          if_pos (by omega)]
      rw [combo_congr r b gs (p ++ [gs.getD k []]) k hgs
        (fun j h1 h2 => getD_eq_zero_of_level hbk' h1 h2)]
      obtain ⟨c, hcR, hc⟩ := hclo b hbR
      rw [hc]
      exact List.contains_iff.2 (List.mem_map.2 ⟨c, hcR, rfl⟩)
    simp only [hcl, Bool.not_true, Bool.false_or] at h1
    exact ih (k + 1) (p ++ [gs.getD k []]) (by omega) hpt h1

theorem cvL_iterN (ℓ r : ℕ) (gs : List (List ℤ)) (n : ℕ) (v : List ℤ) :
    cvL ℓ r (Certificates.Data.LieSylRootWt.iterN (fun v =>
      Certificates.Data.LieSylRootWt.redV ℓ (Certificates.Data.LieSylRootWt.combo r v gs)) n v) =
      Matrix.mulVec (gmat ℓ r gs ^ n) (cvL ℓ r v) := by
  induction n generalizing v with
  | zero => simp [Certificates.Data.LieSylRootWt.iterN]
  | succ n ih =>
    simp only [Certificates.Data.LieSylRootWt.iterN]
    rw [ih, cvL_redV, cvL_combo, Matrix.mulVec_mulVec, pow_succ]

theorem gmat_pow_eq_one (ℓ e r : ℕ) (gs : List (List ℤ))
    (h : Certificates.Data.LieSylRootWt.orderOK ℓ e r gs = true) : gmat ℓ r gs ^ e = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [Matrix.one_mulVec]
  have hi : (i : ℕ) ∈ List.range r := List.mem_range.2 i.2
  unfold Certificates.Data.LieSylRootWt.orderOK at h
  have hb := List.all_eq_true.1 h (i : ℕ) hi
  have heq := eq_of_beq hb
  have := congrArg (cvL ℓ r) heq
  rw [cvL_iterN, cvL_redV, cvL_unitVec] at this
  exact this

theorem conj_pow_aux {ℓ r : ℕ} (A G : Matrix (Fin r) (Fin r) (ZMod ℓ)) (hA : IsUnit A.det)
    (n : ℕ) : (A * G * A⁻¹) ^ n = A * G ^ n * A⁻¹ := by
  induction n with
  | zero => simp [Matrix.mul_nonsing_inv A hA]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    have hinv := Matrix.nonsing_inv_mul A hA
    calc A * G ^ n * A⁻¹ * (A * G * A⁻¹) = A * G ^ n * (A⁻¹ * A) * G * A⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = A * (G ^ n * G) * A⁻¹ := by
          rw [hinv]
          simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem mulVec_cancel {ℓ r : ℕ} (A : Matrix (Fin r) (Fin r) (ZMod ℓ)) (hA : IsUnit A.det)
    {x y : Fin r → ZMod ℓ} (h : Matrix.mulVec A x = Matrix.mulVec A y) : x = y := by
  have := congrArg (Matrix.mulVec A⁻¹) h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA,
    Matrix.one_mulVec, Matrix.one_mulVec] at this

theorem core_pow {ℓ r e : ℕ} (A : Matrix (Fin r) (Fin r) (ZMod ℓ)) (hA : IsUnit A.det)
    (P : (Fin r → ℤ) → Prop) (R : List (List ℤ)) (hR : ∀ v, P v ↔ List.ofFn v ∈ R)
    (hRlen : ∀ b ∈ R, b.length = r) (hsimple : ∀ j : Fin r, P (Pi.single j 1))
    (hcheck : Certificates.Data.LieSylRootWt.stabCheck ℓ e r R = true)
    (B : Matrix (Fin r) (Fin r) (ZMod ℓ))
    (hB : ∀ β, P β → ∃ γ, P γ ∧
      Matrix.mulVec B (Matrix.mulVec A (fun j => ((β j : ℤ) : ZMod ℓ))) =
        Matrix.mulVec A (fun j => ((γ j : ℤ) : ZMod ℓ))) :
    B ^ e = 1 := by
  choose γ hγP hγeq using fun j : Fin r => hB _ (hsimple j)
  obtain ⟨gs, hgs_def⟩ : ∃ gs : List (List ℤ),
      gs = List.ofFn fun j : Fin r => List.ofFn (γ j) := ⟨_, rfl⟩
  have hlen : gs.length = r := by rw [hgs_def]; simp
  have hgetD : ∀ j : Fin r, gs.getD j [] = List.ofFn (γ j) := by
    intro j
    subst hgs_def
    simp [List.getD_eq_getElem?_getD]
  have hmem : ∀ c ∈ gs, c ∈ R := by
    intro c hc
    rw [hgs_def, List.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    exact (hR _).1 (hγP j)
  have hcast1 : ∀ j : Fin r,
      (fun k => (((Pi.single j (1 : ℤ) : Fin r → ℤ) k : ℤ) : ZMod ℓ)) = Pi.single j 1 := by
    intro j
    funext k
    simp [Pi.single_apply]
  have hBA : B * A = A * gmat ℓ r gs := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h1 := hγeq j
    rw [hcast1 j] at h1
    have hGe : Matrix.mulVec (gmat ℓ r gs) (Pi.single j 1) =
        fun i => ((γ j i : ℤ) : ZMod ℓ) := by
      funext i
      rw [Matrix.mulVec_single_one]
      show (((gs.getD (j : ℕ) []).getD (i : ℕ) 0 : ℤ) : ZMod ℓ) = _
      rw [hgetD j]
      simp [List.getD_eq_getElem?_getD]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, hGe]
  have hclo : ∀ b ∈ R, ∃ c ∈ R, Certificates.Data.LieSylRootWt.redV ℓ
      (Certificates.Data.LieSylRootWt.combo r b gs) = Certificates.Data.LieSylRootWt.redV ℓ c := by
    intro b hbR
    set β : Fin r → ℤ := fun i => b.getD i 0 with hβ
    have hbeq : List.ofFn β = b := by
      apply List.ext_getElem
      · simp [hβ, hRlen b hbR]
      · intro n h1 h2
        rw [List.getElem_ofFn]
        show b.getD n 0 = b[n]
        exact List.getD_eq_getElem _ _ h2
    have hPβ : P β := (hR β).2 (by rw [hbeq]; exact hbR)
    obtain ⟨γ', hγ'P, hγ'eq⟩ := hB β hPβ
    have hc' : List.ofFn γ' ∈ R := (hR γ').1 hγ'P
    have hcb : cvL ℓ r b = fun j => ((β j : ℤ) : ZMod ℓ) := by
      funext j
      simp [cvL, hβ]
    have hcc : cvL ℓ r (List.ofFn γ') = fun j => ((γ' j : ℤ) : ZMod ℓ) := by
      funext j
      simp [cvL, List.getD_eq_getElem?_getD]
    have hkey : Matrix.mulVec A (Matrix.mulVec (gmat ℓ r gs) (cvL ℓ r b)) =
        Matrix.mulVec A (cvL ℓ r (List.ofFn γ')) := by
      rw [Matrix.mulVec_mulVec, ← hBA, ← Matrix.mulVec_mulVec, hcb, hγ'eq, hcc]
    have hinj := mulVec_cancel A hA hkey
    have hcomb : cvL ℓ r (Certificates.Data.LieSylRootWt.combo r b gs) =
        cvL ℓ r (List.ofFn γ') := by
      rw [cvL_combo]
      exact hinj
    refine ⟨List.ofFn γ', hc', redV_eq_of_cvL_eq ℓ r ?_ ?_ hcomb⟩
    · simp [Certificates.Data.LieSylRootWt.combo]
    · simp
  have hord : Certificates.Data.LieSylRootWt.orderOK ℓ e r gs = true :=
    search_sound ℓ e r R gs hlen hmem hclo r 0 [] (by omega) (by simp) hcheck
  have hG := gmat_pow_eq_one ℓ e r gs hord
  have hBeq : B = A * gmat ℓ r gs * A⁻¹ := by
    calc B = B * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hA, Matrix.mul_one]
      _ = B * A * A⁻¹ := by rw [Matrix.mul_assoc]
      _ = A * gmat ℓ r gs * A⁻¹ := by rw [hBA]
  rw [hBeq, conj_pow_aux A _ hA, hG, Matrix.mul_one, Matrix.mul_nonsing_inv A hA]

theorem rootCert_check_G2 : (Tag.rootCertificate .G2).check = true := by decide +kernel

theorem rootCert_check_D4 : (Tag.rootCertificate .D4).check = true := by decide +kernel

theorem rootCert_check_F4 : (Tag.rootCertificate .F4).check = true := by decide +kernel

theorem isRoot_iff_mem_of_check {τ : Tag} (R : List (List ℤ))
    (hcheck : τ.rootCertificate.check = true)
    (hR : R = τ.rootCertificate.roots.map fun c => List.ofFn (decodeVec (τ := τ) c))
    (v : Fin τ.rank → ℤ) : IsRoot τ v ↔ List.ofFn v ∈ R := by
  rw [RootCertificate.isRoot_iff hcheck, hR, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨τ.rootCertificate.roots.getD k 0, ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem _
  · rintro ⟨c, hc, hv⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
    refine ⟨k, hk, ?_⟩
    show decodeVec (τ.rootCertificate.roots.getD k 0) = v
    rw [List.getD_eq_getElem _ _ hk]
    exact List.ofFn_injective hv

theorem length_of_mem_roots {τ : Tag} (R : List (List ℤ))
    (hR : R = τ.rootCertificate.roots.map fun c => List.ofFn (decodeVec (τ := τ) c)) :
    ∀ b ∈ R, b.length = τ.rank := by
  intro b hb
  rw [hR, List.mem_map] at hb
  obtain ⟨c, _, rfl⟩ := hb
  simp

theorem isUnit_det_map_cartan (τ : Tag) (d : ℤ) (hd : τ.cartan.det = d)
    (hu : IsUnit (d : ZMod 11)) : IsUnit ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).det) := by
  have h := RingHom.map_det (Int.castRingHom (ZMod 11)) τ.cartan
  rw [RingHom.mapMatrix_apply, hd] at h
  have h' : (τ.cartan.map (Int.cast : ℤ → ZMod 11)).det = (d : ZMod 11) := h.symm
  rw [h']
  exact hu

theorem rootWeight_stab_pow (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4)
    (B : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod 11))
    (hB : ∀ β, IsRoot τ β → ∃ γ, IsRoot τ γ ∧ B.mulVec (wt τ 11 β) = wt τ 11 γ) :
    B ^ (if τ = .G2 then 6 else 24) = 1 := by
  have hcert := Certificates.certificate617001
  obtain ⟨hG2, hD4, hF4⟩ := hcert
  have hu1 : IsUnit ((1 : ℤ) : ZMod 11) := by simp
  have hu4 : IsUnit ((4 : ℤ) : ZMod 11) := isUnit_iff_exists_inv.2 ⟨((3 : ℤ) : ZMod 11), by decide⟩
  rcases hτ with rfl | rfl | rfl
  · rw [if_pos rfl]
    exact core_pow (ℓ := 11) (e := 6) (r := Tag.G2.rank)
      (Tag.G2.cartan.map (Int.cast : ℤ → ZMod 11))
      (isUnit_det_map_cartan Tag.G2 1 det_cartan_G2 hu1) (IsRoot Tag.G2)
      (Certificates.Data.LieSylRootWt.Ty.G2.roots)
      (isRoot_iff_mem_of_check _ rootCert_check_G2 rfl)
      (length_of_mem_roots _ rfl) (fun j => isRoot_single Tag.G2 j) hG2 B hB
  · rw [if_neg (by decide)]
    exact core_pow (ℓ := 11) (e := 24) (r := Tag.D4.rank)
      (Tag.D4.cartan.map (Int.cast : ℤ → ZMod 11))
      (isUnit_det_map_cartan Tag.D4 4 det_cartan_D4 hu4) (IsRoot Tag.D4)
      (Certificates.Data.LieSylRootWt.Ty.D4.roots)
      (isRoot_iff_mem_of_check _ rootCert_check_D4 rfl)
      (length_of_mem_roots _ rfl) (fun j => isRoot_single Tag.D4 j) hD4 B hB
  · rw [if_neg (by decide)]
    exact core_pow (ℓ := 11) (e := 24) (r := Tag.F4.rank)
      (Tag.F4.cartan.map (Int.cast : ℤ → ZMod 11))
      (isUnit_det_map_cartan Tag.F4 1 det_cartan_F4 hu1) (IsRoot Tag.F4)
      (Certificates.Data.LieSylRootWt.Ty.F4.roots)
      (isRoot_iff_mem_of_check _ rootCert_check_F4 rfl)
      (length_of_mem_roots _ rfl) (fun j => isRoot_single Tag.F4 j) hF4 B hB

end CFSG.Quasithin.KGC31
