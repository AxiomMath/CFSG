module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Class
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6RefS

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS (c7Sub c7Sub_eq pairs107 c7_ok107 c7P)
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv (fl2C)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

section Cen

variable {H : Type*} [Group H]

theorem cen_pow_two_eq {x : H} (hx : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set H) = Subgroup.centralizer {x} := by
  have hxx : (x ^ 2) ^ 2 = x := by
    calc (x ^ 2) ^ 2 = x ^ 3 * x := by rw [← pow_mul, pow_succ]
      _ = x := by rw [hx, one_mul]
  ext y
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← hxx]
    exact Commute.pow_right (show Commute y (x ^ 2) from h) 2
  · intro h
    exact Commute.pow_right (show Commute y x from h) 2

theorem cen_eq_of_sq {a x : H} (hx : x ^ 3 = 1) (h : a = x ^ 2) :
    Subgroup.centralizer ({a} : Set H) = Subgroup.centralizer {x} := by
  rw [h]
  exact cen_pow_two_eq hx

theorem map_conj_cen (g a : H) :
    (Subgroup.centralizer ({a} : Set H)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹} : Set H) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx]
      _ = a * (g⁻¹ * x * g) := by group

theorem card_cen_cen_conj (g a t : H) :
    Nat.card ↥(Subgroup.centralizer ({g * a * g⁻¹} : Set H) ⊓ Subgroup.centralizer {t}) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set H) ⊓ Subgroup.centralizer {g⁻¹ * t * g}) := by
  have h : (Subgroup.centralizer ({a} : Set H) ⊓ Subgroup.centralizer {g⁻¹ * t * g}).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹} : Set H) ⊓ Subgroup.centralizer {t} := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_cen, map_conj_cen]
    congr 2
    group
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Cen

section D

def dPairs : List (List ℕ × List ℕ) := [(a2DA, a2DAI), (a2DB, a2DB)]

theorem dPairs_all : dPairs.all pairCheck = true := by decide +kernel

noncomputable def Dsub : Subgroup H6 := Subgroup.closure (genSet dPairs dPairs_all)

def k2Pairs : List (List ℕ × List ℕ) := [(a2P, a2P), (a2Q, a2Q)]

theorem k2Pairs_all : k2Pairs.all pairCheck = true := by decide +kernel

noncomputable def K2star : Subgroup H6 := Subgroup.closure (genSet k2Pairs k2Pairs_all)

theorem dGroup_parts : closureOK (dPairs.map Prod.fst) (closureT (dPairs.map Prod.fst)) 36 = true ∧
    commutes6 a2DA a2V = true ∧ commutes6 a2DA lsSig = true ∧ commutes6 a2DB a2V = true ∧
    commutes6 a2DB lsSig = true := by
  have h := a2_parts.2.2.2.2.1
  simp only [dCheck, dGroup, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hcl, -⟩, -⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩, -⟩ := h
  exact ⟨hcl, hc1, hc2, hc3, hc4⟩

theorem closureOK_K2 :
    closureOK (k2Pairs.map Prod.fst) (closureT (k2Pairs.map Prod.fst)) 6 = true := by
  have h := a2_parts.2.2.2.2.2
  simp only [chainCheck, chainK2, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, ⟨hcl, -⟩⟩, -⟩, -⟩ := h
  exact hcl

theorem card_Dsub : Nat.card Dsub = 36 :=
  card_closure_genSet _ dPairs_all 36 dGroup_parts.1

theorem cen_K4s_eq : Subgroup.centralizer (K4s : Set H6) =
    Subgroup.centralizer {zH 0 * zH 1 ^ 2} ⊓ Subgroup.centralizer {sigH} := by
  rw [K4s, Subgroup.centralizer_closure, centralizer_pair']

theorem Dsub_le : Dsub ≤ Subgroup.centralizer (K4s : Set H6) := by
  obtain ⟨-, hc1, hc2, hc3, hc4⟩ := dGroup_parts
  rw [Dsub, Subgroup.closure_le, cen_K4s_eq]
  rintro _ ⟨cc, hm, rfl⟩
  simp only [dPairs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rw [SetLike.mem_coe, Subgroup.mem_inf]
  rcases hm with rfl | rfl
  · exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_commutes6 (mat6_ofCode _ _) mat6_v hc1),
      Subgroup.mem_centralizer_singleton_iff.2
        (commute_of_commutes6 (mat6_ofCode _ _) mat6_sigH hc2)⟩
  · exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_commutes6 (mat6_ofCode _ _) mat6_v hc3),
      Subgroup.mem_centralizer_singleton_iff.2
        (commute_of_commutes6 (mat6_ofCode _ _) mat6_sigH hc4)⟩

theorem Dsub_eq : Dsub = Subgroup.centralizer (K4s : Set H6) :=
  Subgroup.eq_of_le_of_card_ge Dsub_le (by rw [card_cen_K4s, card_Dsub])

end D

section CenCount

theorem eq_of_code {a : H6} {x y z : ℕ} (h : mat6 a = dec6 (vecCode x y z)) :
    a = zH 0 ^ x * zH 1 ^ y * zH 2 ^ z :=
  mat6_injective (h.trans (mat6_pow_mul x y z).symm)

theorem card_cen_cen_table (l : List (List ℕ × List ℕ)) (hl : l.all pairCheck = true) (n : ℕ)
    (hok : closureOK (l.map Prod.fst) (closureT (l.map Prod.fst)) n = true)
    {a t : H6} (hW : Subgroup.closure (genSet l hl) = Subgroup.centralizer {a}) {ct : List ℕ}
    (hct : mat6 t = dec6 ct) :
    Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) =
      countP (fun y => commutes6 y ct) (closureT (l.map Prod.fst)) := by
  rw [← hW]
  exact card_inf_eq_count l hl n hok (Subgroup.centralizer {t}) (fun y => commutes6 y ct)
    (fun x y hx _ => ⟨fun hxR => commutes6_of_commute hx hct
      (Subgroup.mem_centralizer_singleton_iff.1 hxR), fun hcm =>
        Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commutes6 hx hct hcm)⟩)

theorem lsAElt_two : aElt 2 = zH 2 := by
  have h : aVec 2 = ![0, 0, 1] := by
    ext i
    fin_cases i <;> rfl
  rw [aElt, h]
  simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (0 : ZMod 3).val = 0 from rfl, show (1 : ZMod 3).val = 1 from rfl, pow_zero,
    pow_zero, one_mul, one_mul, pow_one]

theorem count_110 {a t : H6} {ct : List ℕ} (ha : mat6 a = dec6 (vecCode 1 1 0))
    (hct : mat6 t = dec6 ct) :
    Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) =
      countP (fun y => commutes6 y ct) (closureT ((centGens 3).map Prod.fst)) := by
  have ha' : a = zH 0 * zH 1 := by
    rw [eq_of_code ha]
    simp
  refine card_cen_cen_table (centGens 3) (pairs_spec.2.2.2 3) (centOrder 3) (cent_spec 3).2.1 ?_ hct
  rw [ha']
  exact (centSub_eq 3).trans (by rw [lsAElt_three])

theorem count_001 {a t : H6} {ct : List ℕ} (ha : mat6 a = dec6 (vecCode 0 0 1))
    (hct : mat6 t = dec6 ct) :
    Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) =
      countP (fun y => commutes6 y ct) (closureT ((centGens 2).map Prod.fst)) := by
  have ha' : a = zH 2 := by
    rw [eq_of_code ha]
    simp
  refine card_cen_cen_table (centGens 2) (pairs_spec.2.2.2 2) (centOrder 2) (cent_spec 2).2.1 ?_ hct
  rw [ha']
  exact (centSub_eq 2).trans (by rw [lsAElt_two])

theorem count_111 {a t : H6} {ct : List ℕ} (ha : mat6 a = dec6 (vecCode 1 1 1))
    (hct : mat6 t = dec6 ct) :
    Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) =
      countP (fun y => commutes6 y ct) (closureT (c7P.map Prod.fst)) := by
  have hok : closureOK (c7P.map Prod.fst) (closureT (c7P.map Prod.fst)) 648 = true := c7_ok107
  have ha' : a = vecElt zH ![1, 1, 1] := by
    rw [eq_of_code ha]
    simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [show (1 : ZMod 3).val = 1 from rfl]
  refine card_cen_cen_table c7P pairs107.2 648 hok ?_ hct
  rw [ha']
  exact c7Sub_eq

theorem count_112 {a t : H6} {ct : List ℕ} (ha : mat6 a = dec6 (vecCode 1 1 2))
    (hct : mat6 t = dec6 ct) :
    Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) =
      countP (fun y => commutes6 y (cj fl2C ct fl2C)) (closureT (c7P.map Prod.fst)) := by
  have hpair : pairCheck (fl2C, fl2C) = true := by decide +kernel
  have mw : mat6 (vecElt zH ![1, 1, 1]) = dec6 (vecCode 1 1 1) := by
    have h := mat6_vecElt ![1, 1, 1]
    rw [show vecCodeZ ![1, 1, 1] = vecCode 1 1 1 from rfl] at h
    exact h
  have hfl : ofCode (fl2C, fl2C) hpair * vecElt zH ![1, 1, 1] * (ofCode (fl2C, fl2C) hpair)⁻¹ =
      a := conj_eq_of_code (mat6_ofCode _ _) (mat6_ofCode_inv _ _) mw ha (by decide +kernel)
  have ht' : mat6 ((ofCode (fl2C, fl2C) hpair)⁻¹ * t * ofCode (fl2C, fl2C) hpair) =
      dec6 (cj fl2C ct fl2C) := by
    rw [map_mul, map_mul, mat6_ofCode_inv, hct, mat6_ofCode, cj, dec6_mul6, dec6_mul6]
  rw [← hfl, card_cen_cen_conj]
  exact count_111 mw ht'

end CenCount

section CenCountEq

theorem cenCount_110 (ct : List ℕ) : cenCount (vecCode 1 1 0) ct =
    countP (fun y => commutes6 y ct) (closureT ((centGens 3).map Prod.fst)) := by
  unfold cenCount
  rw [if_pos (by decide +kernel)]

theorem cenCount_220 (ct : List ℕ) : cenCount (vecCode 2 2 0) ct =
    countP (fun y => commutes6 y ct) (closureT ((centGens 3).map Prod.fst)) := by
  unfold cenCount
  rw [if_pos (by decide +kernel)]

theorem cenCount_001 (ct : List ℕ) : cenCount (vecCode 0 0 1) ct =
    countP (fun y => commutes6 y ct) (closureT ((centGens 2).map Prod.fst)) := by
  unfold cenCount
  rw [if_neg (by decide +kernel), if_pos (by decide +kernel)]

theorem cenCount_002 (ct : List ℕ) : cenCount (vecCode 0 0 2) ct =
    countP (fun y => commutes6 y ct) (closureT ((centGens 2).map Prod.fst)) := by
  unfold cenCount
  rw [if_neg (by decide +kernel), if_pos (by decide +kernel)]

theorem cenCount_111 (ct : List ℕ) : cenCount (vecCode 1 1 1) ct =
    countP (fun y => commutes6 y ct) (closureT (c7P.map Prod.fst)) := by
  unfold cenCount
  rw [if_neg (by decide +kernel), if_neg (by decide +kernel), if_pos (by decide +kernel)]

theorem cenCount_222 (ct : List ℕ) : cenCount (vecCode 2 2 2) ct =
    countP (fun y => commutes6 y ct) (closureT (c7P.map Prod.fst)) := by
  unfold cenCount
  rw [if_neg (by decide +kernel), if_neg (by decide +kernel), if_pos (by decide +kernel)]

theorem cenCount_112 (ct : List ℕ) : cenCount (vecCode 1 1 2) ct =
    countP (fun y => commutes6 y (cj fl2C ct fl2C)) (closureT (c7P.map Prod.fst)) := by
  unfold cenCount
  rw [if_neg (by decide +kernel), if_neg (by decide +kernel), if_neg (by decide +kernel),
    if_pos (by decide +kernel)]

theorem cenCount_221 (ct : List ℕ) : cenCount (vecCode 2 2 1) ct =
    countP (fun y => commutes6 y (cj fl2C ct fl2C)) (closureT (c7P.map Prod.fst)) := by
  unfold cenCount
  rw [if_neg (by decide +kernel), if_neg (by decide +kernel), if_neg (by decide +kernel),
    if_pos (by decide +kernel)]

end CenCountEq

section Spec

theorem cube_eq_one_of_code {x : H6} {cx : List ℕ} (hx : mat6 x = dec6 cx)
    (h : mul6 (mul6 cx cx) cx = one6) : x ^ 3 = 1 := by
  apply mat6_injective
  rw [map_pow, hx, map_one, ← dec6_one6, ← h, dec6_mul6, dec6_mul6, pow_succ, pow_two]

theorem eq_sq_of_code {a x : H6} {cx ca : List ℕ} (hx : mat6 x = dec6 cx)
    (ha : mat6 a = dec6 ca) (h : mul6 cx cx = ca) : a = x ^ 2 := by
  apply mat6_injective
  rw [ha, map_pow, hx, pow_two, ← dec6_mul6, h]

theorem mat6_z2_code : mat6 (zH 2) = dec6 (vecCode 0 0 1) := by
  have h := mat6_pow_mul 0 0 1
  simpa using h

theorem mat6_w112_code : mat6 (zH 0 * zH 1 * zH 2 ^ 2) = dec6 (vecCode 1 1 2) := by
  have h := mat6_pow_mul 1 1 2
  simpa using h

theorem mat6_w111_code : mat6 (zH 0 * zH 1 * zH 2) = dec6 (vecCode 1 1 1) := by
  have h := mat6_pow_mul 1 1 1
  simpa using h

theorem spec_220 {a t : H6} {ct : List ℕ} (hca : mat6 a = dec6 (vecCode 2 2 0))
    (hct : mat6 t = dec6 ct) :
    cenCount (vecCode 2 2 0) ct =
      Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) := by
  have hx3 : (zH 0 * zH 1) ^ 3 = 1 := cube_eq_one_of_code mat6_u (by decide +kernel)
  have hsq : a = (zH 0 * zH 1) ^ 2 := eq_sq_of_code mat6_u hca (by decide +kernel)
  rw [cenCount_220, cen_eq_of_sq hx3 hsq, count_110 mat6_u hct]

theorem spec_002 {a t : H6} {ct : List ℕ} (hca : mat6 a = dec6 (vecCode 0 0 2))
    (hct : mat6 t = dec6 ct) :
    cenCount (vecCode 0 0 2) ct =
      Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) := by
  have hx3 : (zH 2) ^ 3 = 1 := cube_eq_one_of_code mat6_z2_code (by decide +kernel)
  have hsq : a = (zH 2) ^ 2 := eq_sq_of_code mat6_z2_code hca (by decide +kernel)
  rw [cenCount_002, cen_eq_of_sq hx3 hsq, count_001 mat6_z2_code hct]

theorem spec_222 {a t : H6} {ct : List ℕ} (hca : mat6 a = dec6 (vecCode 2 2 2))
    (hct : mat6 t = dec6 ct) :
    cenCount (vecCode 2 2 2) ct =
      Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) := by
  have hx3 : (zH 0 * zH 1 * zH 2) ^ 3 = 1 :=
    cube_eq_one_of_code mat6_w111_code (by decide +kernel)
  have hsq : a = (zH 0 * zH 1 * zH 2) ^ 2 :=
    eq_sq_of_code mat6_w111_code hca (by decide +kernel)
  rw [cenCount_222, cen_eq_of_sq hx3 hsq, count_111 mat6_w111_code hct]

theorem spec_221 {a t : H6} {ct : List ℕ} (hca : mat6 a = dec6 (vecCode 2 2 1))
    (hct : mat6 t = dec6 ct) :
    cenCount (vecCode 2 2 1) ct =
      Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) := by
  have hx3 : (zH 0 * zH 1 * zH 2 ^ 2) ^ 3 = 1 :=
    cube_eq_one_of_code mat6_w112_code (by decide +kernel)
  have hsq : a = (zH 0 * zH 1 * zH 2 ^ 2) ^ 2 :=
    eq_sq_of_code mat6_w112_code hca (by decide +kernel)
  rw [cenCount_221, cen_eq_of_sq hx3 hsq, count_112 mat6_w112_code hct]

theorem cenCount_spec {a t : H6} {ca ct : List ℕ} (hca : mat6 a = dec6 ca)
    (hct : mat6 t = dec6 ct) (hlist : cenListed ca = true) :
    cenCount ca ct = Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {t}) := by
  simp only [cenListed, Bool.or_eq_true, beq_iff_eq] at hlist
  rcases hlist with ((((((h | h) | h) | h) | h) | h) | h) | h
  · subst h
    rw [cenCount_110, count_110 hca hct]
  · subst h
    exact spec_220 hca hct
  · subst h
    rw [cenCount_001, count_001 hca hct]
  · subst h
    exact spec_002 hca hct
  · subst h
    rw [cenCount_111, count_111 hca hct]
  · subst h
    exact spec_222 hca hct
  · subst h
    rw [cenCount_112, count_112 hca hct]
  · subst h
    exact spec_221 hca hct

end Spec

section K2

theorem cond_true {a t : H6} {ca ct : List ℕ} (hca : mat6 a = dec6 ca) (hct : mat6 t = dec6 ct)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hta : t * a * t = a ^ 2) :
    (mul6 (mul6 ca ca) ca == one6 && !(ca == one6) && mul6 ct ct == one6 && !(ct == one6) &&
      mul6 (mul6 ct ca) ct == mul6 ca ca) = true := by
  have h1 : mul6 (mul6 ca ca) ca = one6 := by
    refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
    rw [dec6_mul6, dec6_mul6, ← hca, ← map_mul, ← map_mul, ← pow_three', ha3, map_one,
      dec6_one6]
  have h3 : mul6 ct ct = one6 := by
    refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
    rw [dec6_mul6, ← hct, ← map_mul, ht2, map_one, dec6_one6]
  have h5 : mul6 (mul6 ct ca) ct = mul6 ca ca := by
    refine dec6_injective (canon6_mul6 _ _) (canon6_mul6 _ _) ?_
    have e1 : dec6 (mul6 (mul6 ct ca) ct) = mat6 (t * a * t) := by
      rw [map_mul, map_mul, hct, hca, dec6_mul6, dec6_mul6]
    have e2 : dec6 (mul6 ca ca) = mat6 (a ^ 2) := by
      rw [pow_two, map_mul, hca, dec6_mul6]
    rw [e1, e2, hta]
  have hne_a : (ca == one6) = false := by
    by_contra hcon
    have : ca = one6 := by simpa using hcon
    apply ha1
    apply mat6_injective
    rw [hca, this, dec6_one6, map_one]
  have hne_t : (ct == one6) = false := by
    by_contra hcon
    have : ct = one6 := by simpa using hcon
    apply ht1
    apply mat6_injective
    rw [hct, this, dec6_one6, map_one]
  simp [h1, h3, h5, hne_a, hne_t]

theorem classify_K2 {a t : H6} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hta : t * a * t = a ^ 2) (haD : a ∈ Dsub) (htD : t ∈ Dsub)
    (hC : Nat.card ↥(Subgroup.centralizer
      ((Subgroup.closure ({a, t} : Set H6) : Subgroup H6) : Set H6)) = 36) :
    a ∈ K2star ∧ t ∈ K2star := by
  have hD := dGroup_parts.1
  obtain ⟨ka, hka, hcodea, hcana⟩ := exists_code_closure dPairs dPairs_all 36 hD haD
  obtain ⟨kt, hkt, hcodet, hcant⟩ := exists_code_closure dPairs dPairs_all 36 hD htD
  have hcl : dClass = true := by
    have h := a2_parts.2.2.2.2.1
    simp only [dCheck, Bool.and_eq_true] at h
    exact h.2
  have hmap : dPairs.map Prod.fst = a2DGens := rfl
  rw [hmap] at hka hkt hcodea hcodet
  have hpair := allCheck_spec (allCheck_spec hcl hka) hkt
  set ca := (closureT a2DGens).getD ka [] with hca
  set ct := (closureT a2DGens).getD kt [] with hct
  have hcond := cond_true hcodea.symm hcodet.symm ha3 ha1 ht2 ht1 hta
  simp only [dPair, hcond, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at hpair
  rcases hpair with ⟨hfa, hft⟩ | ⟨hlist, hne⟩
  · have key : ∀ (u : H6) (c : List ℕ), mat6 u = dec6 c →
        found (closureT a2K2Gens) (indexMap (closureT a2K2Gens)) c = true → u ∈ K2star := by
      intro u c hu hf
      obtain ⟨k, hk, hck⟩ := found_spec hf
      have hmem : c ∈ closureT (k2Pairs.map Prod.fst) := by
        show c ∈ closureT a2K2Gens
        rw [← hck, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
        exact Array.getElem_mem hk
      exact CFSG.Quasithin.H13.U3.mem_closure_of_mem_table k2Pairs k2Pairs_all 6 closureOK_K2
        hmem hu
    exact ⟨key a ca hcodea.symm hfa, key t ct hcodet.symm hft⟩
  · exfalso
    apply hne
    rw [cenCount_spec hcodea.symm hcodet.symm hlist, ← card_cen_closure_pair a t]
    exact hC

end K2

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
