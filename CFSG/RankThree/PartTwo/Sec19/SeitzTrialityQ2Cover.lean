module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Generic
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Sylow

public section

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.AGLEmbedding.ChevOuter HuppertD4Q2

namespace CFSG.RankThree.PartTwo.Sec19.TrialityTwo

section Cover

theorem planeCoverCheck_parts (h : planeCoverCheck () = true) :
    sylowCheck () = true ∧ rowsCheck () = true ∧ coverCheck () = true := by
  simp only [planeCoverCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem row_spec (hZ : Subgroup.center lineGroup = ⊥) (h : rowsCheck () = true)
    {row : ℕ × ℕ × ℕ × List ℕ} (hrow : row ∈ planeRows) :
    ∃ (ua va : MulAut lineGroup) (u v : Pr), u ∈ sElems () ∧ v ∈ sElems () ∧ Rep u ua ∧ Rep v va ∧
      u = (sElems ()).getD row.1 oneP ∧ v = (sElems ()).getD row.2.1 oneP ∧
      ua ≠ 1 ∧ ua ^ 3 = 1 ∧ va ^ 3 = 1 ∧ ua * va = va * ua ∧
        va ∉ ({1, ua, ua * ua} : Set (MulAut lineGroup)) ∧
      row.2.2.1 < 6 ∧
      (wordAut row.2.2.2 * repLine1 row.2.2.1 * (wordAut row.2.2.2)⁻¹ ∈ Subgroup.closure {ua, va}) ∧
      (wordAut row.2.2.2 * repLine2 row.2.2.1 * (wordAut row.2.2.2)⁻¹ ∈ Subgroup.closure {ua, va}) := by
  simp only [rowsCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hr := h.2 row hrow
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at hr
  obtain ⟨⟨⟨⟨⟨⟨hi1, hi2⟩, hcls⟩, hpair⟩, hbi⟩, hm1⟩, hm2⟩ := hr
  have hu : (sElems ()).getD row.1 oneP ∈ sElems () := by
    rw [List.getD_eq_getElem _ _ hi1]
    exact List.getElem_mem hi1
  have hv : (sElems ()).getD row.2.1 oneP ∈ sElems () := by
    rw [List.getD_eq_getElem _ _ hi2]
    exact List.getElem_mem hi2
  obtain ⟨ua, -, hua⟩ := rep_of_mem_sElems hu
  obtain ⟨va, -, hva⟩ := rep_of_mem_sElems hv
  obtain ⟨hne, hu3, hv3, hcomm, hnot⟩ := (rep_isPairP hZ hua hva).mp hpair
  have hb := rep_wordP row.2.2.2
  have hbi' := rep_wordP (invW row.2.2.2)
  have hinv : wordAut (invW row.2.2.2) = (wordAut row.2.2.2)⁻¹ := rep_inv_eq hb hbi' hbi
  have hR1 : (classR1P ()).getD row.2.2.1 oneP = wordP (classR1.getD row.2.2.1 []) := by
    have := List.getD_map (f := wordP) (l := classR1) (n := row.2.2.1) (d := [])
    exact this
  have hR2 : (classR2P ()).getD row.2.2.1 oneP = wordP (classR2.getD row.2.2.1 []) := by
    have := List.getD_map (f := wordP) (l := classR2) (n := row.2.2.1) (d := [])
    exact this
  rw [hR1] at hm1
  rw [hR2] at hm2
  have hrep1 : Rep (mulP (mulP (wordP row.2.2.2) (wordP (classR1.getD row.2.2.1 [])))
      (wordP (invW row.2.2.2))) (wordAut row.2.2.2 * repLine1 row.2.2.1 * (wordAut row.2.2.2)⁻¹) := by
    have := rep_mul (rep_mul hb (rep_wordP (classR1.getD row.2.2.1 []))) hbi'
    rwa [hinv] at this
  have hrep2 : Rep (mulP (mulP (wordP row.2.2.2) (wordP (classR2.getD row.2.2.1 [])))
      (wordP (invW row.2.2.2))) (wordAut row.2.2.2 * repLine2 row.2.2.1 * (wordAut row.2.2.2)⁻¹) := by
    have := rep_mul (rep_mul hb (rep_wordP (classR2.getD row.2.2.1 []))) hbi'
    rwa [hinv] at this
  obtain ⟨k1, l1, -, -, hc1⟩ := (rep_mem_planeP hZ hua hva hrep1).mp hm1
  obtain ⟨k2, l2, -, -, hc2⟩ := (rep_mem_planeP hZ hua hva hrep2).mp hm2
  refine ⟨ua, va, _, _, hu, hv, hua, hva, rfl, rfl, hne, hu3, hv3, hcomm, hnot, hcls, ?_, ?_⟩
  · rw [hc1]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) k1)
      (pow_mem (Subgroup.subset_closure (by simp)) l1)
  · rw [hc2]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) k2)
      (pow_mem (Subgroup.subset_closure (by simp)) l2)

theorem cover_spec (h : coverCheck () = true) {p q : Pr} (hp : p ∈ sElems ()) (hq : q ∈ sElems ())
    (hp3 : cube1P p = true) (hq3 : cube1P q = true) (hp1 : p ≠ oneP) (hq1 : q ≠ oneP)
    (hpq : q ∉ powsP p) (hcomm : commP p q = true) :
    ∃ row ∈ planeRows, p ∈ planeP ((sElems ()).getD row.1 oneP) ((sElems ()).getD row.2.1 oneP) ∧
      q ∈ planeP ((sElems ()).getD row.1 oneP) ((sElems ()).getD row.2.1 oneP) := by
  simp only [coverCheck, List.all_eq_true, List.mem_filter, bne_iff_ne, ne_eq] at h
  have h1 := h p ⟨⟨hp, hp3⟩, hp1⟩ q ⟨⟨hq, hq3⟩, hq1⟩
  simp only [coveredP, Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true', List.any_eq_true,
    Bool.and_eq_true, List.mem_map] at h1
  rcases h1 with (hmem | hncomm) | ⟨P, ⟨row, hrow, rfl⟩, hpP, hqP⟩
  · exact absurd hmem hpq
  · rw [hcomm] at hncomm
    exact absurd hncomm (by simp)
  · exact ⟨row, hrow, hpP, hqP⟩

theorem factorization_three_aut : (3 * 211341312 : ℕ).factorization 3 = 5 := by
  have h : (3 * 211341312 : ℕ) = 3 ^ 5 * 2609152 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), Nat.add_zero]

theorem planeCover_of_sylow_check (hZ : Subgroup.center lineGroup = ⊥)
    (h : planeCoverCheck () = true) {E : Subgroup (MulAut lineGroup)} (hES : E ≤ sGrp)
    (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    ∃ i : ℕ, i < 6 ∧ ∃ β : MulAut lineGroup, β * repLine1 i * β⁻¹ ∈ E ∧
      β * repLine2 i * β⁻¹ ∈ E := by
  obtain ⟨hsyl, hrows, hcov⟩ := planeCoverCheck_parts h
  obtain ⟨x, y, hxE, hyE, hx1, hx3, hy3, hxy, hyset, hEeq⟩ := exists_gen_pair hE hcard
  obtain ⟨p, hp, hpx⟩ := exists_rep_of_mem_sGrp hsyl (hES hxE)
  obtain ⟨q, hq, hqy⟩ := exists_rep_of_mem_sGrp hsyl (hES hyE)
  have hy1 : y ≠ 1 := fun h1 => hyset (Or.inl h1)
  obtain ⟨row, hrow, hpP, hqP⟩ := cover_spec hcov hp hq ((rep_cube1P hZ hpx).mpr hx3)
    ((rep_cube1P hZ hqy).mpr hy3) (fun h0 => hx1 ((rep_eq_oneP_iff hZ hpx).mp h0))
    (fun h0 => hy1 ((rep_eq_oneP_iff hZ hqy).mp h0))
    (fun hmem => hyset ((rep_mem_powsP hZ hpx hqy).mp hmem)) ((rep_commP hZ hpx hqy).mpr hxy)
  obtain ⟨ua, va, u, v, hu, hv, hua, hva, hue, hve, hne, hu3, hv3, hcomm, hnot, hcls, hc1, hc2⟩ :=
    row_spec hZ hrows hrow
  rw [← hue, ← hve] at hpP hqP
  obtain ⟨i1, j1, -, -, hxij⟩ := (rep_mem_planeP hZ hua hva hpx).mp hpP
  obtain ⟨i2, j2, -, -, hyij⟩ := (rep_mem_planeP hZ hua hva hqy).mp hqP
  have hxP : x ∈ Subgroup.closure {ua, va} := by
    rw [hxij]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  have hyP : y ∈ Subgroup.closure {ua, va} := by
    rw [hyij]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  have hle : E ≤ Subgroup.closure {ua, va} := by
    rw [hEeq, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hxP
    · exact hyP
  obtain ⟨-, -, hcardP⟩ := CFSG.AGLEmbedding.ChevOuter.closure_pair ua va hu3 hv3 hcomm
    (hind_of_pair hne hu3 hv3 hnot)
  have hEP : E = Subgroup.closure {ua, va} :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hcard])
  exact ⟨row.2.2.1, hcls, wordAut row.2.2.2, hEP ▸ hc1, hEP ▸ hc2⟩

theorem planeCover_of_check (hZ : Subgroup.center lineGroup = ⊥)
    (hAut : Nat.card (MulAut lineGroup) = 3 * 211341312) (h : planeCoverCheck () = true)
    {E : Subgroup (MulAut lineGroup)} (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ i : ℕ, i < 6 ∧ ∃ α : MulAut lineGroup, α * repLine1 i * α⁻¹ ∈ E ∧
      α * repLine2 i * α⁻¹ ∈ E := by
  obtain ⟨hsyl, -, -⟩ := planeCoverCheck_parts h
  have hS : Nat.card sGrp = 3 ^ (Nat.card (MulAut lineGroup)).factorization 3 := by
    rw [card_sGrp hZ hsyl, hAut, factorization_three_aut]
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hcard
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hS hE3
  obtain ⟨hE', hcard'⟩ := isElementaryAbelian_map_conj hE hcard g
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ sGrp := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using hg z hz
  obtain ⟨i, hi, β, hβ1, hβ2⟩ := planeCover_of_sylow_check hZ h hle hE' hcard'
  refine ⟨i, hi, g⁻¹ * β, ?_, ?_⟩
  · have e : (g⁻¹ * β) * repLine1 i * (g⁻¹ * β)⁻¹ = g⁻¹ * (β * repLine1 i * β⁻¹) * g := by group
    rw [e]
    obtain ⟨z, hz, hzeq⟩ := hβ1
    rw [← hzeq]
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · have e : (g⁻¹ * β) * repLine2 i * (g⁻¹ * β)⁻¹ = g⁻¹ * (β * repLine2 i * β⁻¹) * g := by group
    rw [e]
    obtain ⟨z, hz, hzeq⟩ := hβ2
    rw [← hzeq]
    simpa [MulAut.conj_apply, mul_assoc] using hz

end Cover

end CFSG.RankThree.PartTwo.Sec19.TrialityTwo
