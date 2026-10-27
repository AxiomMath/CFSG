module

public import Certificates.Certificate8036
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open Item434Kit Subgroup


theorem sp62_434_pairs_check : pairsCheck8036 = true :=
  Certificates.certificate8036.1

theorem sp62_434_wreath_check : wreathCheck8036 = true :=
  Certificates.certificate8036.2.1

theorem sp62_434_cent_check : centCheck8036 = true :=
  Certificates.certificate8036.2.2.1

theorem sp62_434_hyp_check : hypCheck8036 = true :=
  Certificates.certificate8036.2.2.2

theorem pairs_spec : genP.all pairCheck = true ∧ (∀ i, pairCheck (zPair i) = true) ∧
    pairCheck tPair = true ∧ ∀ j, (centGens j).all pairCheck = true := by
  have h := sp62_434_pairs_check
  simp only [pairsCheck8036, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun i => List.all_eq_true.mp h2 i (List.mem_finRange i), h3,
    fun j => List.all_eq_true.mp h4 j (List.mem_finRange j)⟩

theorem gpsH_spec' :
    ∀ gp ∈ gpsH, ∃ g : H6, dec6 (gp.take 36) = mat6 g ∧ dec6 (gp.drop 36) = mat6 g⁻¹ := by
  have hg := List.all_eq_true.mp pairs_spec.1
  intro gp hgp
  simp only [gpsH, List.mem_cons, List.not_mem_nil, or_false] at hgp
  rcases hgp with rfl | rfl
  · refine ⟨ofCode (aC, aI) (hg _ (List.mem_cons_self ..)), ?_, ?_⟩
    · rw [List.take_left' (by rfl), mat6_ofCode]
    · rw [List.drop_left' (by rfl), mat6_ofCode_inv]
  · refine ⟨ofCode (bC, bI) (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), ?_, ?_⟩
    · rw [List.take_left' (by rfl), mat6_ofCode]
    · rw [List.drop_left' (by rfl), mat6_ofCode_inv]

@[expose] noncomputable def zH (i : Fin 3) : H6 :=
  ofCode (zPair i) (pairs_spec.2.1 i)

@[expose] noncomputable def tH : H6 :=
  ofCode tPair pairs_spec.2.2.1

theorem mat6_zH (i : Fin 3) : mat6 (zH i) = dec6 (zCode i) :=
  mat6_ofCode _ _

theorem mat6_zH_inv (i : Fin 3) : mat6 (zH i)⁻¹ = dec6 (mul6 (zCode i) (zCode i)) :=
  mat6_ofCode_inv _ _

theorem mat6_tH : mat6 tH = dec6 tCode :=
  mat6_ofCode _ _

theorem mat6_tH_inv : mat6 tH⁻¹ = dec6 tCodeInv :=
  mat6_ofCode_inv _ _

theorem dec6_powCode (c : List ℕ) (n : ℕ) : dec6 (powCode c n) = dec6 c ^ n := by
  induction n with
  | zero => simp [powCode, dec6_one6]
  | succ n ih =>
    rw [powCode, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, dec6_mul6,
      ← powCode, ih, pow_succ]

theorem mat6_pow_mul (a b c : ℕ) :
    mat6 (zH 0 ^ a * zH 1 ^ b * zH 2 ^ c) = dec6 (vecCode a b c) := by
  rw [vecCode, dec6_mul6, dec6_mul6, dec6_powCode, dec6_powCode, dec6_powCode, map_mul, map_mul,
    map_pow, map_pow, map_pow, mat6_zH, mat6_zH, mat6_zH]

theorem mat6_vecElt (v : Fin 3 → ZMod 3) : mat6 (vecElt zH v) = dec6 (vecCodeZ v) :=
  mat6_pow_mul _ _ _

theorem canon6_vecCode (a b c : ℕ) : canon6 (vecCode a b c) = true :=
  canon6_mul6 _ _

theorem canon6_zCode_tCode : (∀ i, canon6 (zCode i) = true) ∧ canon6 tCode = true :=
  ⟨fun i => (pairCheck_spec (pairs_spec.2.1 i)).1, (pairCheck_spec pairs_spec.2.2.1).1⟩

theorem wreath_spec : (∀ i, mul6 (mul6 (zCode i) (zCode i)) (zCode i) = one6) ∧
    (∀ i j, commutes6 (zCode i) (zCode j) = true) ∧ mul6 (mul6 tCode tCode) tCode = one6 ∧
    (∀ i, conjStep6 (tCode ++ tCodeInv) (zCode i) = zCode (i + 1)) ∧
    ∀ a < 3, ∀ b < 3, ∀ c < 3,
      ((a = 0 ∧ b = 0 ∧ c = 0) ∨ vecCode a b c ≠ one6) ∧ vecCode a b c ≠ tCode := by
  have h := sp62_434_wreath_check
  simp only [wreathCheck8036, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun i => ?_, fun i j => ?_, h3, fun i => ?_, fun a ha b hb c hc => ?_⟩
  · simpa using List.all_eq_true.mp h1 i (List.mem_finRange i)
  · exact List.all_eq_true.mp (List.all_eq_true.mp h2 i (List.mem_finRange i)) j
      (List.mem_finRange j)
  · simpa using List.all_eq_true.mp h4 i (List.mem_finRange i)
  · have h6 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h5 a
      (List.mem_range.mpr ha)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at h6
    exact ⟨h6.1.imp_left fun h => ⟨h.1.1, h.1.2, h.2⟩, h6.2⟩

theorem zH_pow_three (i : Fin 3) : zH i ^ 3 = 1 := by
  apply mat6_injective
  rw [map_pow, pow_three', mat6_zH, ← dec6_mul6, ← dec6_mul6, wreath_spec.1 i, dec6_one6,
    map_one]

theorem zH_comm (i j : Fin 3) : zH i * zH j = zH j * zH i :=
  commute_of_commutes6 (mat6_zH i) (mat6_zH j) (wreath_spec.2.1 i j)

theorem tH_pow_three : tH ^ 3 = 1 := by
  apply mat6_injective
  rw [map_pow, pow_three', mat6_tH, ← dec6_mul6, ← dec6_mul6, wreath_spec.2.2.1, dec6_one6,
    map_one]

theorem tH_conj (i : Fin 3) : tH * zH i * tH⁻¹ = zH (i + 1) := by
  apply mat6_injective
  have hc := wreath_spec.2.2.2.1 i
  rw [conjStep6, List.take_left' (by rfl), List.drop_left' (by rfl)] at hc
  rw [map_mul, map_mul, mat6_tH, mat6_tH_inv, mat6_zH, mat6_zH, ← dec6_mul6, ← dec6_mul6, hc]

theorem vecElt_zH_eq_one {v : Fin 3 → ZMod 3} (hv : vecElt zH v = 1) : v = 0 := by
  have hm := congrArg mat6 hv
  rw [map_one, mat6_vecElt, ← dec6_one6] at hm
  have he := dec6_injective (canon6_vecCode _ _ _) canon6_one6 hm
  rcases (wreath_spec.2.2.2.2 _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _
      (ZMod.val_lt (v 2))).1 with ⟨e0, e1, e2⟩ | hne
  · funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp e0
    · exact (ZMod.val_eq_zero _).mp e1
    · exact (ZMod.val_eq_zero _).mp e2
  · exact absurd he hne

theorem vecElt_zH_ne_tH (v : Fin 3 → ZMod 3) : vecElt zH v ≠ tH := by
  intro hv
  have hm := congrArg mat6 hv
  rw [mat6_vecElt, mat6_tH] at hm
  exact (wreath_spec.2.2.2.2 _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _
    (ZMod.val_lt (v 2))).2 (dec6_injective (canon6_vecCode _ _ _) canon6_zCode_tCode.2 hm)

theorem wreathFacts_zH : WreathFacts zH tH :=
  ⟨zH_pow_three, zH_comm, fun _ hv => vecElt_zH_eq_one hv, tH_pow_three, tH_conj 0, tH_conj 1,
    tH_conj 2, vecElt_zH_ne_tH⟩

theorem factorization_card_H6 : (Nat.card H6).factorization 3 = 4 := by
  rw [card_H6, show (1451520 : ℕ) = 3 ^ 4 * 17920 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW_zH : Nat.card (wreathW zH tH) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts_zH)
  rw [factorization_card_H6] at hle
  have := le_card_wreathW wreathFacts_zH
  norm_num at hle
  omega

@[expose] noncomputable def aElt (j : Fin 5) : H6 :=
  vecElt zH (aVec j)

theorem cent_spec (j : Fin 5) :
    (centGens j).all (fun cc => commutes6 cc.1 (vecCodeZ (aVec j))) = true ∧
      closureOK ((centGens j).map Prod.fst) (closureT ((centGens j).map Prod.fst))
        (centOrder j) = true ∧
      orbitOK (orbitTable (vecCodeZ (aVec j))) (classSize j) = true := by
  have h := List.all_eq_true.mp sp62_434_cent_check j (List.mem_finRange j)
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] noncomputable def centSub (j : Fin 5) : Subgroup H6 :=
  Subgroup.closure (genSet (centGens j) (pairs_spec.2.2.2 j))

theorem centSub_le (j : Fin 5) : centSub j ≤ Subgroup.centralizer {aElt j} := by
  rw [centSub, Subgroup.closure_le]
  rintro _ ⟨cc, hm, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_commutes6 (mat6_ofCode _ _) (mat6_vecElt _)
    (List.all_eq_true.mp (cent_spec j).1 cc hm)

theorem card_centSub (j : Fin 5) : Nat.card (centSub j) = centOrder j :=
  card_closure_genSet _ _ _ (cent_spec j).2.1

theorem card_centralizer_mul_le_of_orbit {x : H6} {c : List ℕ} (hc : mat6 x = dec6 c) {n : ℕ}
    (hok : orbitOK (orbitTable c) n = true) :
    Nat.card (Subgroup.centralizer {x}) * n ≤ Nat.card H6 := by
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hsize, hdist⟩, hcanon⟩ := hok
  have hspec := orbitBuild6_spec mat6 hc.symm gpsH gpsH_spec' (orbitParents6 c gpsH 13440)
  have hmem : ∀ k : Fin n, (orbitTable c).getD k [] ∈ orbitTable c := fun k => by
    have hk : (k : ℕ) < (orbitTable c).size := by rw [hsize]; exact k.2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    exact Array.getElem_mem hk
  choose g hg using fun k : Fin n => hspec _ (hmem k)
  refine CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_centralizer_mul_le
    (fun k => g k * x * (g k)⁻¹) ?_ fun k => ⟨g k, rfl⟩
  intro k k' e
  have hk : (k : ℕ) < (orbitTable c).size := by rw [hsize]; exact k.2
  have hk' : (k' : ℕ) < (orbitTable c).size := by rw [hsize]; exact k'.2
  have e' : dec6 ((orbitTable c).getD k []) = dec6 ((orbitTable c).getD k' []) := by
    rw [hg k, hg k']
    exact congrArg mat6 e
  exact Fin.ext (distinctCheck_spec hdist hk hk'
    (dec6_injective (allCheck_spec hcanon hk) (allCheck_spec hcanon hk') e'))

theorem centSub_eq (j : Fin 5) : centSub j = Subgroup.centralizer {aElt j} := by
  refine Subgroup.eq_of_le_of_card_ge (centSub_le j) ?_
  have h1 := card_centralizer_mul_le_of_orbit (x := aElt j) (mat6_vecElt (aVec j))
    (cent_spec j).2.2
  rw [card_H6] at h1
  rw [card_centSub]
  have hprod : centOrder j * classSize j = 1451520 := by fin_cases j <;> rfl
  have hpos : 0 < classSize j := by fin_cases j <;> decide
  exact Nat.le_of_mul_le_mul_right (h1.trans hprod.ge) hpos

set_option synthInstance.maxSize 2048 in
theorem hyperplane_basis : ∀ u w : Fin 3 → ZMod 3, u ≠ 0 → (∀ c : ZMod 3, w ≠ c • u) →
    ∃ k : Fin 13, (∃ i j : ZMod 3, i • u + j • w = aVec (hypJ k)) ∧
      ∃ i j : ZMod 3, i • u + j • w = hypB k := by
  decide +kernel

theorem vecElt_smul {H : Type*} [Group H] {z : Fin 3 → H} {t : H} (hf : WreathFacts z t)
    (k : ZMod 3) (v : Fin 3 → ZMod 3) : vecElt z (k • v) = vecElt z v ^ k.val := by
  have hk : k • v = k.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  have h := map_pow (vecHom hf) (Multiplicative.ofAdd v) k.val
  rw [← ofAdd_nsmul] at h
  rw [hk]
  exact h

theorem vecElt_smul_add {H : Type*} [Group H] {z : Fin 3 → H} {t : H} (hf : WreathFacts z t)
    (i j : ZMod 3) (u w : Fin 3 → ZMod 3) :
    vecElt z (i • u + j • w) = vecElt z u ^ i.val * vecElt z w ^ j.val := by
  rw [vecElt_add hf, vecElt_smul hf, vecElt_smul hf]

theorem dec6_pow2k (x : List ℕ) (k : ℕ) : dec6 (pow2k x k) = dec6 x ^ 2 ^ k := by
  induction k with
  | zero => simp [pow2k]
  | succ k ih =>
    rw [pow2k, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← pow2k,
      dec6_mul6, ih, ← pow_add, ← two_mul, pow_succ, mul_comm]

theorem pow2k_succ (x : List ℕ) (k : ℕ) : pow2k x (k + 1) = mul6 (pow2k x k) (pow2k x k) := by
  rw [pow2k, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← pow2k]

theorem dec6_pow17920 (x : List ℕ) : dec6 (pow17920 x) = dec6 x ^ 17920 := by
  rw [pow17920, dec6_pow2k, dec6_mul6, dec6_mul6, dec6_pow2k, dec6_mul6, ← sq, ← pow_add,
    ← pow_succ, ← pow_mul]
  norm_num

theorem canon6_pow17920 (x : List ℕ) : canon6 (pow17920 x) = true := by
  rw [pow17920, pow2k_succ]
  exact canon6_mul6 _ _

theorem pow_17920_eq_one_of_mem {Y : Subgroup H6} (hY : ¬ 3 ∣ Nat.card Y) {y : H6}
    (hy : y ∈ Y) : y ^ 17920 = 1 := by
  have h1 : orderOf y ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hy
  have h2 : orderOf y ∣ 17920 * 81 := by
    rw [show 17920 * 81 = Nat.card H6 by rw [card_H6]]
    exact orderOf_dvd_natCard y
  have h3 : ¬ 3 ∣ orderOf y := fun h => hY (h.trans h1)
  have hcop : Nat.Coprime (orderOf y) 81 := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.Coprime.pow_right 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h2)

theorem eq_one_of_hyp (k : Fin 13) {Y : Subgroup H6} (hY : ¬ 3 ∣ Nat.card Y)
    (hA : baseA zH ≤ normalizer (Y : Set H6)) {y : H6} (hyY : y ∈ Y)
    (hya : y ∈ Subgroup.centralizer {aElt (hypJ k)})
    (hyb : y * vecElt zH (hypB k) = vecElt zH (hypB k) * y) : y = 1 := by
  rw [← centSub_eq] at hya
  obtain ⟨t, ht, hcode, -⟩ := exists_code_closure _ _ _ (cent_spec (hypJ k)).2.1 hya
  have hcheck := allCheck_spec (List.all_eq_true.mp sp62_434_hyp_check k (List.mem_finRange k)) ht
  set c := (closureT ((centGens (hypJ k)).map Prod.fst)).getD t [] with hc
  have hcomm : commutes6 c (vecCodeZ (hypB k)) = true :=
    commutes6_of_commute hcode.symm (mat6_vecElt _) hyb
  have hpow : pow17920 c = one6 := by
    refine dec6_injective (canon6_pow17920 c) canon6_one6 ?_
    rw [dec6_pow17920, hcode, ← map_pow, pow_17920_eq_one_of_mem hY hyY, map_one, dec6_one6]
  simp only [hypPred, hcomm, hpow, beq_self_eq_true, Bool.and_self, Bool.not_true,
    Bool.false_or, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hcheck
  rcases hcheck with h1 | ⟨i, -, hi⟩
  · apply mat6_injective
    rw [← hcode, h1, dec6_one6, map_one]
  · exfalso
    have hconjY : zH i * y * (zH i)⁻¹ ∈ Y :=
      (mem_normalizer_iff.mp (hA (z_mem_baseA i)) y).mp hyY
    have hw1 := pow_17920_eq_one_of_mem hY (mul_mem hyY hconjY)
    apply hi
    have hlen : (zCode i).length = 36 := by
      have h := canon6_zCode_tCode.1 i
      simp only [canon6, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    refine dec6_injective (canon6_pow17920 _) canon6_one6 ?_
    rw [dec6_pow17920, zPair, conjStep6, List.take_left' hlen, List.drop_left' hlen, dec6_mul6,
      dec6_mul6, dec6_mul6, ← mat6_zH, ← mat6_zH_inv, hcode, ← map_mul, ← map_mul, ← map_mul,
      ← map_pow, hw1, map_one, dec6_one6]

theorem eq_bot_of_baseA_le_normalizer {Y : Subgroup H6} (hY : ¬ 3 ∣ Nat.card Y)
    (hA : baseA zH ≤ normalizer (Y : Set H6)) : Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts_zH
  have hab := isElemAbelian_baseA hf
  have hY3 : Nat.Coprime 3 (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hab
    (by rw [card_baseA hf]; norm_num) hA hY3 fun H hHA hH9 => ?_
  have hH1 : H ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hH9
    norm_num at hH9
  obtain ⟨⟨x, hxH⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hzx : ¬ H ≤ zpowers x := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hH9, Nat.card_zpowers] at h1
    have h2 : orderOf x ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hab.2 _ (hHA hxH)))
    omega
  obtain ⟨w, hwH, hwx⟩ : ∃ w ∈ H, w ∉ zpowers x := by
    by_contra hc
    push Not at hc
    exact hzx hc
  obtain ⟨u, rfl⟩ := (mem_baseA_iff hf).mp (hHA hxH)
  obtain ⟨w', rfl⟩ := (mem_baseA_iff hf).mp (hHA hwH)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx1' (by simp [vecElt])
  have hw0 : ∀ c : ZMod 3, w' ≠ c • u := by
    rintro c rfl
    apply hwx
    rw [vecElt_smul hf]
    exact pow_mem (mem_zpowers _) _
  have hmemH : ∀ i j : ZMod 3, vecElt zH (i • u + j • w') ∈ H := fun i j => by
    rw [vecElt_smul_add hf]
    exact mul_mem (pow_mem hxH _) (pow_mem hwH _)
  obtain ⟨k, ⟨i, j, hij⟩, ⟨i', j', hij'⟩⟩ := hyperplane_basis u w' hu0 hw0
  have haH : aElt (hypJ k) ∈ H := by
    rw [aElt, ← hij]
    exact hmemH i j
  have hbH : vecElt zH (hypB k) ∈ H := by
    rw [← hij']
    exact hmemH i' j'
  intro y hy
  obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_bot]
  refine eq_one_of_hyp k hY hA hyY ?_ (Subgroup.mem_centralizer_iff.mp hyC _ hbH).symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hyC _ haH).symm

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
