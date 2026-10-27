module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Perm
public import Certificates.Certificate1383009
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iCoreA
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

private noncomputable def sA : Equiv.Perm (Fin 65) := permOfArr 65 minusSylowA

private noncomputable def sB : Equiv.Perm (Fin 65) := permOfArr 65 minusSylowB

private theorem hValidCheck : minusLocalValid () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.1.1.1

private theorem hOrderCheck : minusSylowAOrder () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.1.1.2

private theorem hBSqCheck : minusSylowBSq () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.1.2.1

private theorem hConjCheck : minusSylowConj () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.1.2.2

private theorem hNotMemCheck : minusSylowNotMem () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.2.1.1

private theorem hCommuteCheck : minusA5Commute () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.2.1.2

private theorem hEnumCheck : minusA5EnumOK () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.2.2.1

private theorem hSimpleCheck : minusA5Simple () = true := by
  have h := Certificates.certificate1383009
  simp only [minusLocalCheck, Bool.and_eq_true] at h
  exact h.2.2.2

private theorem validTable : validA 65 minusTable[0]! = true := by
  have h := hValidCheck
  simp only [minusLocalValid, Bool.and_eq_true] at h
  exact h.1.1.1.1

private theorem validSylowA : validA 65 minusSylowA = true := by
  have h := hValidCheck
  simp only [minusLocalValid, Bool.and_eq_true] at h
  exact h.1.1.1.2

private theorem validSylowB : validA 65 minusSylowB = true := by
  have h := hValidCheck
  simp only [minusLocalValid, Bool.and_eq_true] at h
  exact h.1.1.2

private theorem minusBase_lt : ∀ p ∈ minusBase, p < 65 := by
  intro p hp
  simp only [minusBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

private theorem a5EnumOK : enumOK 65 minusA5Gens minusBase (minusA5Enum ()) = true := by
  have h := hEnumCheck
  simp only [minusA5EnumOK, Bool.and_eq_true] at h
  exact h.1

private theorem a5EnumSize : (minusA5Enum ()).pts.size = 60 := by
  have h := hEnumCheck
  simp only [minusA5EnumOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

@[expose] noncomputable def minusSylowP : Subgroup (Equiv.Perm (Fin 65)) :=
  Subgroup.zpowers (permOfArr 65 minusSylowA) ⊔ Subgroup.zpowers (permOfArr 65 minusSylowB)

private theorem pow_four_sA : sA ^ 4 = 1 := by
  have hA : Rep 65 minusSylowA sA := rep_of_validA validSylowA
  have h4 : eqA 65 (compA 65 (compA 65 minusSylowA minusSylowA)
      (compA 65 minusSylowA minusSylowA)) (idA 65) = true := by
    have h := hOrderCheck
    simp only [minusSylowAOrder, Bool.and_eq_true] at h
    exact h.1
  have h := (eqA_iff (rep_compA (rep_compA hA hA) (rep_compA hA hA)) rep_idA).1 h4
  have h4' : sA ^ 4 = (sA * sA) * (sA * sA) := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
  rw [h4', h]

private theorem sq_ne_one_sA : sA ^ 2 ≠ 1 := by
  have hA : Rep 65 minusSylowA sA := rep_of_validA validSylowA
  have h2ne : eqA 65 (compA 65 minusSylowA minusSylowA) (idA 65) = false := by
    have h := hOrderCheck
    simp only [minusSylowAOrder, Bool.and_eq_true] at h
    have h2 := h.2
    rwa [beq_iff_eq] at h2
  intro h2
  have h2' : sA * sA = 1 := by rwa [pow_two] at h2
  have he : eqA 65 (compA 65 minusSylowA minusSylowA) (idA 65) = true :=
    (eqA_iff (rep_compA hA hA) rep_idA).2 h2'
  rw [h2ne] at he
  exact Bool.false_ne_true he

private theorem orderOf_sA : orderOf sA = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  refine ⟨pow_four_sA, ?_⟩
  intro m hm4 hm0
  interval_cases m
  · rw [pow_one]
    intro h
    exact sq_ne_one_sA (by rw [pow_two, h, one_mul])
  · exact sq_ne_one_sA
  · intro h3
    have hmul : sA * sA ^ 3 = 1 := by
      have h : sA * sA ^ 3 = sA ^ 4 := by
        rw [show (4 : ℕ) = 1 + 3 by norm_num, pow_add, pow_one]
      rw [h, pow_four_sA]
    rw [h3, mul_one] at hmul
    exact sq_ne_one_sA (by rw [hmul, one_pow])

private theorem notMem_sA : sB ∉ Subgroup.zpowers sA := by
  have hA : Rep 65 minusSylowA sA := rep_of_validA validSylowA
  have hB : Rep 65 minusSylowB sB := rep_of_validA validSylowB
  have hNotMem := hNotMemCheck
  simp only [minusSylowNotMem, Bool.and_eq_true] at hNotMem
  have n0 : eqA 65 minusSylowB (idA 65) = false := by
    have h := hNotMem.1.1.1
    rwa [beq_iff_eq] at h
  have n1 : eqA 65 minusSylowB minusSylowA = false := by
    have h := hNotMem.1.1.2
    rwa [beq_iff_eq] at h
  have n2 : eqA 65 minusSylowB (compA 65 minusSylowA minusSylowA) = false := by
    have h := hNotMem.1.2
    rwa [beq_iff_eq] at h
  have n3 : eqA 65 minusSylowB
      (compA 65 (compA 65 minusSylowA minusSylowA) minusSylowA) = false := by
    have h := hNotMem.2
    rwa [beq_iff_eq] at h
  have hb1 : sB ≠ 1 := by
    intro h
    have he : eqA 65 minusSylowB (idA 65) = true := (eqA_iff hB rep_idA).2 h
    rw [n0] at he
    exact Bool.false_ne_true he
  have hbA : sB ≠ sA := by
    intro h
    have he : eqA 65 minusSylowB minusSylowA = true := (eqA_iff hB hA).2 h
    rw [n1] at he
    exact Bool.false_ne_true he
  have hbA2 : sB ≠ sA * sA := by
    intro h
    have he : eqA 65 minusSylowB (compA 65 minusSylowA minusSylowA) = true :=
      (eqA_iff hB (rep_compA hA hA)).2 h
    rw [n2] at he
    exact Bool.false_ne_true he
  have hbA3 : sB ≠ (sA * sA) * sA := by
    intro h
    have he : eqA 65 minusSylowB
        (compA 65 (compA 65 minusSylowA minusSylowA) minusSylowA) = true :=
      (eqA_iff hB (rep_compA (rep_compA hA hA) hA)).2 h
    rw [n3] at he
    exact Bool.false_ne_true he
  intro hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hred : sA ^ k = sA ^ (k % ((4 : ℕ) : ℤ)) := zpow_eq_zpow_emod' k pow_four_sA
  rw [hred] at hk
  have hr0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have hr4 : k % ((4 : ℕ) : ℤ) < ((4 : ℕ) : ℤ) := Int.emod_lt_of_pos k (by norm_num)
  have hr : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨
      k % ((4 : ℕ) : ℤ) = 2 ∨ k % ((4 : ℕ) : ℤ) = 3 := by omega
  rcases hr with h | h | h | h
  · rw [h, zpow_zero] at hk
    exact hb1 hk.symm
  · rw [h, zpow_one] at hk
    exact hbA hk.symm
  · rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two] at hk
    exact hbA2 hk.symm
  · rw [h, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at hk
    exact hbA3 (hk.symm.trans (by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]))

private theorem inv_sA_sB : sB * sA * sB⁻¹ = sA⁻¹ := by
  have hA : Rep 65 minusSylowA sA := rep_of_validA validSylowA
  have hB : Rep 65 minusSylowB sB := rep_of_validA validSylowB
  have hb2 : sB ^ 2 = 1 := by
    have h := (eqA_iff (rep_compA hB hB) rep_idA).1 hBSqCheck
    rwa [pow_two]
  have hbab : sB * sA * sB = sA ^ 3 := by
    have h := (eqA_iff (rep_compA (rep_compA hB hA) hB)
      (rep_compA (rep_compA hA hA) hA)).1 hConjCheck
    rw [h]
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]
  have hsB : sB⁻¹ = sB := inv_eq_of_mul_eq_one_right hb2
  have ha3 : sA ^ 3 = sA⁻¹ := by
    have hmul : sA * sA ^ 3 = 1 := by
      have h : sA * sA ^ 3 = sA ^ 4 := by
        rw [show (4 : ℕ) = 1 + 3 by norm_num, pow_add, pow_one]
      rw [h, pow_four_sA]
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  rw [hsB, hbab, ha3]

private theorem sq_sB : sB ^ 2 = 1 := by
  have hB : Rep 65 minusSylowB sB := rep_of_validA validSylowB
  have h := (eqA_iff (rep_compA hB hB) rep_idA).1 hBSqCheck
  rwa [pow_two]

theorem nonempty_minusSylowP_mulEquiv : Nonempty (minusSylowP ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Lemma31iCoreA.nonempty_dihedral sq_sB inv_sA_sB notMem_sA
  rw [orderOf_sA] at e
  exact ⟨e⟩

theorem card_minusSylowP : Nat.card minusSylowP = 8 := by
  obtain ⟨e⟩ := nonempty_minusSylowP_mulEquiv
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem hasDihedralSylowTwo_of_minusSylow {L : Subgroup (Equiv.Perm (Fin 65))}
    (hcard : Nat.card L = 7800) (ha : permOfArr 65 minusSylowA ∈ L)
    (hb : permOfArr 65 minusSylowB ∈ L) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo L := by
  have hle : minusSylowP ≤ L := by
    rw [minusSylowP]
    exact sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  have hQcard : Nat.card (minusSylowP.subgroupOf L) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_minusSylowP]
  have hPgroup : IsPGroup 2 (minusSylowP.subgroupOf L) :=
    IsPGroup.of_card (p := 2) (n := 3) hQcard
  have hindex : (minusSylowP.subgroupOf L).index = 975 := by
    have h := Subgroup.card_mul_index (minusSylowP.subgroupOf L)
    rw [hQcard, hcard] at h
    omega
  have hnotdvd : ¬ 2 ∣ (minusSylowP.subgroupOf L).index := by
    rw [hindex]; norm_num
  let Q : Sylow 2 L := IsPGroup.toSylow hPgroup hnotdvd
  have hQcoe : (Q : Subgroup L) = minusSylowP.subgroupOf L :=
    IsPGroup.toSylow_coe hPgroup hnotdvd
  have hQdihedral : Nonempty ((Q : Subgroup L) ≃* DihedralGroup 4) := by
    obtain ⟨e⟩ := nonempty_minusSylowP_mulEquiv
    exact ⟨(MulEquiv.subgroupCongr hQcoe).trans
      ((Subgroup.subgroupOfEquivOfLe hle).trans e)⟩
  intro S
  refine ⟨2, by norm_num, ?_⟩
  obtain ⟨eQ⟩ := hQdihedral
  exact ⟨(Sylow.equiv S Q).trans eQ⟩

@[expose] noncomputable def minusA5Perm : Subgroup (Equiv.Perm (Fin 65)) :=
  Subgroup.closure (permsA 65 minusA5Gens)

theorem card_minusA5Perm : Nat.card minusA5Perm = 60 := by
  have hspec := enumOK_spec (n := 65) (gs := minusA5Gens) (ps := minusBase)
    (c := minusA5Enum ()) minusBase_lt a5EnumOK
  rw [minusA5Perm, hspec.2.1, a5EnumSize]

theorem isSimpleGroup_minusA5Perm : IsSimpleGroup minusA5Perm :=
  isSimpleGroup_of_conjSimpleOK (n := 65) (gs := minusA5Gens) (ps := minusBase)
    (c := minusA5Enum ()) minusBase_lt a5EnumOK (by rw [a5EnumSize]; norm_num) hSimpleCheck

theorem nonempty_minusA5Perm_mulEquiv :
    Nonempty (minusA5Perm ≃* alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup minusA5Perm := isSimpleGroup_minusA5Perm
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := minusA5Perm) card_minusA5Perm

theorem commute_minusRefl_zero_of_mem_minusA5Perm {x : Equiv.Perm (Fin 65)}
    (hx : x ∈ minusA5Perm) : x * minusRefl 0 = minusRefl 0 * x := by
  have hle : minusA5Perm ≤ Subgroup.centralizer ({minusRefl 0} :
      Set (Equiv.Perm (Fin 65))) := by
    rw [minusA5Perm, Subgroup.closure_le]
    rintro g ⟨k, hk, rfl⟩
    refine (Subgroup.mem_centralizer_singleton_iff).2 ?_
    have hgen := allLt_spec hCommuteCheck hk
    have hxr : Rep 65 minusA5Gens[k]! (permOfArr 65 minusA5Gens[k]!) :=
      rep_of_validA (enumOK_gens_valid a5EnumOK hk)
    have hr0 : Rep 65 minusTable[0]! (permOfArr 65 minusTable[0]!) :=
      rep_of_validA validTable
    have h := (eqA_iff (rep_compA hxr hr0) (rep_compA hr0 hxr)).1 hgen
    simpa [minusRefl] using h
  exact (Subgroup.mem_centralizer_singleton_iff).1 (hle hx)

theorem minusA5Perm_le {L : Subgroup (Equiv.Perm (Fin 65))}
    (hx : permOfArr 65 minusA5Gens[0]! ∈ L) (hy : permOfArr 65 minusA5Gens[1]! ∈ L) :
    minusA5Perm ≤ L := by
  rw [minusA5Perm, Subgroup.closure_le]
  rintro g ⟨k, hk, rfl⟩
  have hsize : minusA5Gens.size = 2 := by simp [minusA5Gens]
  have hk2 : k < 2 := by rwa [hsize] at hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · exact hx
  · exact hy

end CFSG.OddTranspositions.PartThree
