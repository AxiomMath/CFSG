module

public import CFSG.RankThree.Co2.Pairs
public import CFSG.RankThree.Co2.SylowInv
public import CFSG.RankThree.Co2.JFusion
public import CFSG.RankThree.Co2.SylM

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv


theorem factorization_two_eq {n k m : ℕ} (h : n = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    n.factorization 2 = k := by
  subst h
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]


@[expose] def sylowOf {ws : Array (List ℕ)} {x : Cr}
    (hle : subW ws ≤ Subgroup.centralizer ({x} : Set Cr))
    (hcard : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({x} : Set Cr))).factorization 2) :
    Sylow 2 (Subgroup.centralizer ({x} : Set Cr)) :=
  Sylow.ofCard ((subW ws).subgroupOf _) (by rw [card_subgroupOf_eq hle, hcard])


theorem mem_sylowOf {ws : Array (List ℕ)} {x : Cr}
    {hle : subW ws ≤ Subgroup.centralizer ({x} : Set Cr)}
    {hcard : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({x} : Set Cr))).factorization 2}
    {y : Subgroup.centralizer ({x} : Set Cr)} :
    y ∈ (sylowOf hle hcard : Subgroup (Subgroup.centralizer ({x} : Set Cr))) ↔
      (y : Cr) ∈ subW ws :=
  Subgroup.mem_subgroupOf


theorem selfC_central (x : Cr) (y : Subgroup.centralizer ({x} : Set Cr)) :
    y * selfC x = selfC x * y :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)


theorem centralC_central (x : Cr) (y : Subgroup.centralizer ({x} : Set Cr)) :
    y * centralC rCr_mem_center x = centralC rCr_mem_center x * y :=
  Subtype.ext (Subgroup.mem_center_iff.1 rCr_mem_center (y : Cr))


theorem PartnerPair.sqrtCount_eq {i j : ℕ} (hp : PartnerPair i j)
    (P : Sylow 2 (Subgroup.centralizer ({rep i} : Set Cr)))
    (Q : Sylow 2 (Subgroup.centralizer ({rep j} : Set Cr))) :
    sqrtCount (Q : Subgroup _) (centralC rCr_mem_center (rep j)) =
        sqrtCount (P : Subgroup _) (selfC (rep i)) ∧
      sqrtCount (Q : Subgroup _) (selfC (rep j)) =
        sqrtCount (P : Subgroup _) (centralC rCr_mem_center (rep i)) := by
  obtain ⟨Ψ, h1, h2⟩ := hp
  exact ⟨sqrtCount_sylow Ψ P Q (centralC_central _) h1,
    sqrtCount_sylow Ψ P Q (selfC_central _) h2⟩


theorem PartnerPair.exConjMul_iff {i j : ℕ} (hp : PartnerPair i j)
    (P : Sylow 2 (Subgroup.centralizer ({rep i} : Set Cr)))
    (Q : Sylow 2 (Subgroup.centralizer ({rep j} : Set Cr))) :
    (ExConjMul (Q : Subgroup _) (centralC rCr_mem_center (rep j)) ↔
      ExConjMul (P : Subgroup _) (selfC (rep i))) := by
  obtain ⟨Ψ, h1, -⟩ := hp
  exact exConjMul_sylow Ψ P Q (centralC_central _) h1


theorem card_C (i : ℕ) (hi : i < 10) {m : ℕ} (hm : m * classSizes[i]! = 743178240)
    (hpos : 0 < classSizes[i]!) : Nat.card (Subgroup.centralizer ({rep i} : Set Cr)) = m := by
  have h := card_centralizer_rep hi
  rw [← hm] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h


theorem fact_C {i : ℕ} (hi : i < 10) {m k o : ℕ} (hm : m * classSizes[i]! = 743178240)
    (hpos : 0 < classSizes[i]!) (hmo : m = 2 ^ k * o) (ho : ¬ 2 ∣ o) :
    (Nat.card (Subgroup.centralizer ({rep i} : Set Cr))).factorization 2 = k := by
  rw [card_C i hi hm hpos]
  exact factorization_two_eq hmo ho


section SylMat

variable
  {ws : Array (List ℕ)} {x : Cr}

theorem sqrtCount_sylowOf_mat (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42)
    (hle : subW ws ≤ Subgroup.centralizer ({x} : Set Cr))
    (hcard : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({x} : Set Cr))).factorization 2)
    (a : Subgroup.centralizer ({x} : Set Cr)) :
    sqrtCount (sylowOf hle hcard : Subgroup (Subgroup.centralizer ({x} : Set Cr))) a =
      Nat.card {y : matGrp ws // (y : Matrix (Fin 22) (Fin 22) (ZMod 2)) * y = crMat (a : Cr)} := by
  unfold sqrtCount
  have e1 : Nat.card {y : (sylowOf hle hcard : Subgroup (Subgroup.centralizer ({x} : Set Cr))) //
      ((y : Subgroup.centralizer ({x} : Set Cr))) ^ 2 = a} =
      Nat.card {y : subW ws // (y : Cr) ^ 2 = (a : Cr)} :=
    Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hle).toEquiv.subtypeEquiv fun y => by
      change _ ↔ ((y : Subgroup.centralizer ({x} : Set Cr)) : Cr) ^ 2 = (a : Cr)
      rw [← Subgroup.coe_pow]
      exact Subtype.ext_iff)
  have e2 : Nat.card {y : subW ws // (y : Cr) ^ 2 = (a : Cr)} =
      Nat.card {j : subW ws // crMat (j : Cr) * crMat (j : Cr) = crMat (a : Cr)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [sq, ← map_mul, crMat_injective.eq_iff])
  rw [e1, e2, card_subW_crMat hws (fun z => z * z = crMat (a : Cr))]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun z => z ∈ matGrp ws)
    (fun z => z * z = crMat (a : Cr))).symm

theorem exConjMul_sylowOf_iff (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42)
    (hle : subW ws ≤ Subgroup.centralizer ({x} : Set Cr))
    (hcard : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({x} : Set Cr))).factorization 2)
    (c : Subgroup.centralizer ({x} : Set Cr)) :
    ExConjMul (sylowOf hle hcard : Subgroup (Subgroup.centralizer ({x} : Set Cr))) c ↔
      ConjMul ws (crMat (c : Cr)) := by
  constructor
  · rintro ⟨u, hu, hu2, hu1, w, hw, e⟩
    have huS : (u : Cr) ∈ subW ws := mem_sylowOf.1 hu
    have hwS : (w : Cr) ∈ subW ws := mem_sylowOf.1 hw
    have hu2' : (u : Cr) * u = 1 := congrArg Subtype.val hu2
    have e' : (w : Cr) * u * (w : Cr)⁻¹ = u * c := congrArg Subtype.val e
    have e'' : (w : Cr) * u = u * c * w := by
      rw [← e', inv_mul_cancel_right]
    refine ⟨crMat u, (mem_subW_iff_crMat hws).1 huS, crMat w, (mem_subW_iff_crMat hws).1 hwS,
      ?_, ?_, ?_⟩
    · rw [← map_mul, hu2', map_one]
    · intro e1
      apply hu1
      apply Subtype.ext
      apply crMat_injective
      rw [e1, OneMemClass.coe_one, map_one]
    · rw [← map_mul, ← map_mul, ← map_mul, e'']
  · rintro ⟨_, hx, _, hy, hx2, hx1, e⟩
    obtain ⟨u, hu, rfl⟩ := matGrp_le_map hws hx
    obtain ⟨w, hw, rfl⟩ := matGrp_le_map hws hy
    have e' : w * u = u * c * w := crMat_injective (by rw [map_mul, map_mul, map_mul]; exact e)
    refine ⟨⟨u, hle hu⟩, mem_sylowOf.2 hu, ?_, ?_, ⟨w, hle hw⟩, mem_sylowOf.2 hw, ?_⟩
    · apply Subtype.ext
      change u * u = 1
      exact crMat_injective (by rw [map_mul, map_one]; exact hx2)
    · intro e1
      apply hx1
      have hu1 : u = 1 := congrArg Subtype.val e1
      rw [hu1, map_one]
    · apply Subtype.ext
      change w * u * w⁻¹ = u * (c : Cr)
      rw [e', mul_inv_cancel_right]

end SylMat

theorem exists_sylow_counts_mat {ws : Array (List ℕ)} {n : ℕ} {cls : List ℕ} {i b : ℕ}
    (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) (h : SylGrp ws n cls)
    (hb : SqCount ws n 0 b) (hi : i ∈ cls) (hi10 : i < 10)
    (hn : n = 2 ^ (Nat.card (Subgroup.centralizer ({rep i} : Set Cr))).factorization 2) :
    ∃ P : Sylow 2 (Subgroup.centralizer ({rep i} : Set Cr)),
      (∀ a, SqCount ws n i a → sqrtCount (P : Subgroup _) (selfC (rep i)) = a) ∧
        sqrtCount (P : Subgroup _) (centralC rCr_mem_center (rep i)) = b := by
  have hle := le_centralizer_of_sylGrp hws h hi hi10
  have hcS := card_subW_of_sylGrp hws h hi hi10 hn
  have hcard : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({rep i} : Set Cr))).factorization 2 := hcS.trans hn
  have hM : Nat.card (matGrp ws) ≤ n := by rw [← card_subW_eq_card_matGrp hws, hcS]
  refine ⟨sylowOf hle hcard, fun a ha => ?_, ?_⟩
  · rw [sqrtCount_sylowOf_mat hws, coe_selfC, crMat_rep hi10]
    exact ha hM
  · rw [sqrtCount_sylowOf_mat hws, coe_centralC, ← rep_zero, crMat_rep (by norm_num)]
    exact hb hM

theorem not_partnerPair_of_conjMul {ws : Array (List ℕ)} {i i' : ℕ}
    (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) (hS : SylGrp ws (2 ^ 14) [i', i])
    (hex : ConjMul ws (repMat 0))
    (hnot : Nat.card (matGrp ws) ≤ 2 ^ 14 → ¬ ConjMul ws (repMat i)) (hi10 : i < 10)
    (hi'10 : i' < 10)
    (hfi : (Nat.card (Subgroup.centralizer ({rep i} : Set Cr))).factorization 2 = 14)
    (hfi' : (Nat.card (Subgroup.centralizer ({rep i'} : Set Cr))).factorization 2 = 14)
    {j : ℕ} (hj : j = i ∨ j = i') : ¬ PartnerPair i j := by
  intro hp
  have hcS : Nat.card (subW ws) = 2 ^ 14 :=
    card_subW_of_sylGrp hws hS (j := i) (by simp) hi10 (by rw [hfi])
  have hleI := le_centralizer_of_sylGrp hws hS (j := i) (by simp) hi10
  have hcardI : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({rep i} : Set Cr))).factorization 2 := by
    rw [hcS, hfi]
  have hM : Nat.card (matGrp ws) ≤ 2 ^ 14 := by rw [← card_subW_eq_card_matGrp hws, hcS]
  have hn : ¬ ExConjMul (sylowOf hleI hcardI : Subgroup _) (selfC (rep i)) := by
    rw [exConjMul_sylowOf_iff hws, coe_selfC, crMat_rep hi10]
    exact hnot hM
  have hj10 : j < 10 := by rcases hj with rfl | rfl <;> assumption
  have hfj : (Nat.card (Subgroup.centralizer ({rep j} : Set Cr))).factorization 2 = 14 := by
    rcases hj with rfl | rfl <;> assumption
  have hleJ := le_centralizer_of_sylGrp hws hS (j := j) (by rcases hj with rfl | rfl <;> simp)
    hj10
  have hcardJ : Nat.card (subW ws) =
      2 ^ (Nat.card (Subgroup.centralizer ({rep j} : Set Cr))).factorization 2 := by
    rw [hcS, hfj]
  have hx : ExConjMul (sylowOf hleJ hcardJ : Subgroup _) (centralC rCr_mem_center (rep j)) := by
    rw [exConjMul_sylowOf_iff hws, coe_centralC, ← rep_zero, crMat_rep (by norm_num)]
    exact hex
  exact hn ((hp.exConjMul_iff (sylowOf hleI hcardI) (sylowOf hleJ hcardJ)).1 hx)

theorem classSizes_pos {i : ℕ} (hi : i < 10) : 0 < classSizes[i]! := by
  interval_cases i <;> decide


theorem classSizes_eq_of_partnerPair {i j : ℕ} (hi : i < 10) (hj : j < 10)
    (hp : PartnerPair i j) : classSizes[i]! = classSizes[j]! := by
  have h1 := card_centralizer_rep hi
  have h2 := card_centralizer_rep hj
  rw [PartnerElts.card_eq ((PartnerPair.iff i j).1 hp)] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)


theorem fact_C1 : (Nat.card (Subgroup.centralizer ({rep 1} : Set Cr))).factorization 2 = 17 :=
  fact_C (by norm_num) (m := 2752512) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 2752512 = 2 ^ 17 * 21) (by decide)


theorem fact_C2 : (Nat.card (Subgroup.centralizer ({rep 2} : Set Cr))).factorization 2 = 16 :=
  fact_C (by norm_num) (m := 589824) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 589824 = 2 ^ 16 * 9) (by decide)


theorem fact_C3 : (Nat.card (Subgroup.centralizer ({rep 3} : Set Cr))).factorization 2 = 16 :=
  fact_C (by norm_num) (m := 589824) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 589824 = 2 ^ 16 * 9) (by decide)


theorem fact_C4 : (Nat.card (Subgroup.centralizer ({rep 4} : Set Cr))).factorization 2 = 15 :=
  fact_C (by norm_num) (m := 32768) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 32768 = 2 ^ 15 * 1) (by decide)


theorem fact_C5 : (Nat.card (Subgroup.centralizer ({rep 5} : Set Cr))).factorization 2 = 14 :=
  fact_C (by norm_num) (m := 49152) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 49152 = 2 ^ 14 * 3) (by decide)


theorem fact_C6 : (Nat.card (Subgroup.centralizer ({rep 6} : Set Cr))).factorization 2 = 14 :=
  fact_C (by norm_num) (m := 49152) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 49152 = 2 ^ 14 * 3) (by decide)


theorem fact_C7 : (Nat.card (Subgroup.centralizer ({rep 7} : Set Cr))).factorization 2 = 14 :=
  fact_C (by norm_num) (m := 737280) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 737280 = 2 ^ 14 * 45) (by decide)


theorem fact_C8 : (Nat.card (Subgroup.centralizer ({rep 8} : Set Cr))).factorization 2 = 14 :=
  fact_C (by norm_num) (m := 737280) (by decide) (classSizes_pos (by norm_num))
    (by norm_num : 737280 = 2 ^ 14 * 45) (by decide)


theorem not_partnerPair_one {j : ℕ} (hj : j < 10) : ¬ PartnerPair 1 j := by
  intro hp
  have hs := classSizes_eq_of_partnerPair (by norm_num) hj hp
  obtain rfl : j = 1 := by interval_cases j <;> simp_all [classSizes]
  have F := sylFacts_cert.1
  obtain ⟨P, hP1, hP2⟩ := exists_sylow_counts_mat sylLetters1 F.1 F.2.2 (i := 1) (by simp)
    (by norm_num) (by rw [fact_C1])
  have h := (hp.sqrtCount_eq P P).1
  rw [hP2, hP1 _ F.2.1] at h
  omega


theorem not_partnerPair_three {j : ℕ} (hj : j < 10) : ¬ PartnerPair 3 j := by
  intro hp
  have hs := classSizes_eq_of_partnerPair (by norm_num) hj hp
  have F := sylFacts_cert.2.1
  obtain ⟨P, hP1, -⟩ := exists_sylow_counts_mat sylLetters3 F.1 F.2.2 (i := 3) (by simp)
    (by norm_num) (by rw [fact_C3])
  have hj23 : j = 2 ∨ j = 3 := by interval_cases j <;> simp_all [classSizes]
  rcases hj23 with rfl | rfl
  · obtain ⟨Q, -, hQ2⟩ := exists_sylow_counts_mat sylLetters3 F.1 F.2.2 (i := 2) (by simp)
      (by norm_num) (by rw [fact_C2])
    have h := (hp.sqrtCount_eq P Q).1
    rw [hP1 _ F.2.1, hQ2] at h
    omega
  · obtain ⟨Q, -, hQ2⟩ := exists_sylow_counts_mat sylLetters3 F.1 F.2.2 (i := 3) (by simp)
      (by norm_num) (by rw [fact_C3])
    have h := (hp.sqrtCount_eq P Q).1
    rw [hP1 _ F.2.1, hQ2] at h
    omega


theorem not_partnerPair_four {j : ℕ} (hj : j < 10) : ¬ PartnerPair 4 j := by
  intro hp
  have hs := classSizes_eq_of_partnerPair (by norm_num) hj hp
  obtain rfl : j = 4 := by interval_cases j <;> simp_all [classSizes]
  have F := sylFacts_cert.2.2.1
  obtain ⟨P, hP1, hP2⟩ := exists_sylow_counts_mat sylLetters4 F.1 F.2.2 (i := 4) (by simp)
    (by norm_num) (by rw [fact_C4])
  have h := (hp.sqrtCount_eq P P).1
  rw [hP2, hP1 _ F.2.1] at h
  omega


theorem not_partnerPair_five {j : ℕ} (hj : j < 10) : ¬ PartnerPair 5 j := by
  intro hp
  have hs := classSizes_eq_of_partnerPair (by norm_num) hj hp
  have F := sylFacts_cert.2.2.2.1
  obtain ⟨P, hP1, -⟩ := exists_sylow_counts_mat sylLetters5 F.1 F.2.2 (i := 5) (by simp)
    (by norm_num) (by rw [fact_C5])
  have hj56 : j = 5 ∨ j = 6 := by interval_cases j <;> simp_all [classSizes]
  rcases hj56 with rfl | rfl
  · obtain ⟨Q, -, hQ2⟩ := exists_sylow_counts_mat sylLetters5 F.1 F.2.2 (i := 5) (by simp)
      (by norm_num) (by rw [fact_C5])
    have h := (hp.sqrtCount_eq P Q).1
    rw [hP1 _ F.2.1, hQ2] at h
    omega
  · obtain ⟨Q, -, hQ2⟩ := exists_sylow_counts_mat sylLetters5 F.1 F.2.2 (i := 6) (by simp)
      (by norm_num) (by rw [fact_C6])
    have h := (hp.sqrtCount_eq P Q).1
    rw [hP1 _ F.2.1, hQ2] at h
    omega


theorem not_partnerPair_six {j : ℕ} (hj : j < 10) : ¬ PartnerPair 6 j := by
  intro hp
  have hs := classSizes_eq_of_partnerPair (by norm_num) hj hp
  have hj' : j = 6 ∨ j = 5 := by interval_cases j <;> simp_all [classSizes]
  have F := sylFacts_cert.2.2.2.2.1
  exact not_partnerPair_of_conjMul sylLetters6 F.1 F.2.1 F.2.2 (by norm_num) (by norm_num)
    fact_C6 fact_C5 hj' hp


theorem not_partnerPair_eight {j : ℕ} (hj : j < 10) : ¬ PartnerPair 8 j := by
  intro hp
  have hs := classSizes_eq_of_partnerPair (by norm_num) hj hp
  have hj' : j = 8 ∨ j = 7 := by interval_cases j <;> simp_all [classSizes]
  have F := sylFacts_cert.2.2.2.2.2
  exact not_partnerPair_of_conjMul sylLetters8 F.1 F.2.1 F.2.2 (by norm_num) (by norm_num)
    fact_C8 fact_C7 hj' hp


theorem not_partnerPair {i j : ℕ} (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 8)
    (hj : j < 10) : ¬ PartnerPair i j := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_partnerPair_one hj
  · exact not_partnerPair_three hj
  · exact not_partnerPair_four hj
  · exact not_partnerPair_five hj
  · exact not_partnerPair_six hj
  · exact not_partnerPair_eight hj


end CFSG.RankThree.Co2
