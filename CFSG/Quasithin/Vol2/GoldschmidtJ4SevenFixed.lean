module

public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenOrb
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenNum

public section

namespace CFSG.Quasithin.J4Seven

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open scoped Classical Matrix

theorem vorb_wf {O : VOrb} {r : V2} {m : ℕ} (hok : vorbOK locTabs r O m = true) {q : ℕ}
    (hq : q < m) : (O.pts[q]!).wf = true := by
  have h := vorb_at hok hq
  unfold vorbAt at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem Dlt_five_eq
    (hF : J4Facts) : Dlt 5 = ↑((Finset.range 15180).image (vecP orbS5)) := by
  have hM := hF.mat
  obtain ⟨-, -, -, hok, -⟩ := chkSeven_parts
  have hrep : rep 5 = toRow rep5S.toVec := rep_toVec hM (by norm_num)
  have hsub : Dlt 5 ⊆ ↑((Finset.range 15180).image (vecP orbS5)) := by
    rintro v ⟨h, hh, hvh⟩
    exact Finset.mem_coe.2 (vorb_orbit_subset hM hok ⟨h, hh, by rw [hvh, hrep]⟩)
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Dlt_ncard (ℓ := 5) (by norm_num)]
  exact Finset.card_image_le.trans (by simp)

theorem smul_vecP_eq_iff (hM : MatFacts) {q : ℕ} (hq : q < 15180) :
    sevenElt • vecP orbS5 q = vecP orbS5 q ↔
      (frApply (frTable sevenR) (orbS5.pts[q]!)).beq (orbS5.pts[q]!) = true := by
  obtain ⟨-, -, ⟨-, hw⟩, hok, -⟩ := chkSeven_parts
  have hv : (orbS5.pts[q]!).wf = true := vorb_wf hok hq
  have hw' : (frApply (frTable sevenR) (orbS5.pts[q]!)).wf = true := frApply_frTable_wf hw _
  have e1 : sevenElt • vecP orbS5 q = vecP orbS5 q ↔ sevenElt⁻¹ • vecP orbS5 q = vecP orbS5 q := by
    rw [inv_smul_eq_iff, eq_comm]
  rw [e1, ← ofRow_inj, inv_smul_row, ← Mx_apply, Mx_sevenElt hM]
  show (orbS5.pts[q]!).toVec ᵥ* rowsMatrix sevenR = (orbS5.pts[q]!).toVec ↔ _
  rw [← frApply_toVec_eq_vecMul, V2.toVec_inj hw' hv, V2.beq_iff]

@[expose] noncomputable def fixPt (i : Fin 4) : Row := toRow (sevenFix.getD i.val rootV).toVec

theorem mem_fixedS_iff {M : Array V2} {O : VOrb} {v : V2} :
    v ∈ fixedS M O ↔ v ∈ O.pts ∧ (frApply (frTable M) v).beq v = true := by
  simp [fixedS]

theorem sevenFix_length : sevenFix.length = 4 := rfl

theorem getD_wf {i : ℕ} (hi : i < 4) :
    (sevenFix.getD i rootV).wf = true := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := chkSeven_parts
  have hl : i < sevenFix.length := by rw [sevenFix_length]; exact hi
  rw [List.getD_eq_getElem _ _ hl]
  exact h6 _ (List.getElem_mem hl)

theorem fixed_orbit_eq
    (hF : J4Facts) :
    {p : Row | (∃ j : J, j • w₀ = p) ∧ sevenElt • p = p} = insert w₀ (Set.range fixPt) := by
  have hM := hF.mat
  obtain ⟨-, -, -, hok, hfixS, -⟩ := chkSeven_parts
  have hsz : orbS5.pts.size = 15180 := vorb_size hok
  ext p
  constructor
  · rintro ⟨hp, hfix⟩
    rcases fixed_seven_subset hF sevenElt_mem_Hj (orderOf_sevenElt hM) hp hfix with rfl | h5
    · exact Set.mem_insert _ _
    · right
      rw [Dlt_five_eq hF, Finset.mem_coe, Finset.mem_image] at h5
      obtain ⟨q, hq, rfl⟩ := h5
      have hq' : q < 15180 := Finset.mem_range.1 hq
      have hqs : q < orbS5.pts.size := by rw [hsz]; exact hq'
      have hmem : orbS5.pts[q]! ∈ fixedS sevenR orbS5 := by
        refine mem_fixedS_iff.2 ⟨?_, (smul_vecP_eq_iff hM hq').1 hfix⟩
        rw [getElem!_pos _ q hqs]
        exact Array.getElem_mem hqs
      obtain ⟨i, hi, hv⟩ := List.getElem_of_mem ((hfixS _).1 hmem)
      refine ⟨⟨i, by rw [← sevenFix_length]; exact hi⟩, ?_⟩
      show toRow (sevenFix.getD i rootV).toVec = vecP orbS5 q
      rw [List.getD_eq_getElem _ _ hi, hv]
      rfl
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨⟨1, one_smul J w₀⟩, smul_root_of_mem_Hj hM sevenElt_mem_Hj⟩
    · have hl : (i : ℕ) < sevenFix.length := by rw [sevenFix_length]; exact i.2
      have hmem : sevenFix.getD i rootV ∈ fixedS sevenR orbS5 := by
        refine (hfixS _).2 ?_
        rw [List.getD_eq_getElem _ _ hl]
        exact List.getElem_mem hl
      obtain ⟨hin, hbeq⟩ := mem_fixedS_iff.1 hmem
      obtain ⟨q, hq, hqv⟩ := Array.mem_iff_getElem.1 hin
      have hq' : q < 15180 := by rw [← hsz]; exact hq
      have hvq : orbS5.pts[q]! = sevenFix.getD i rootV := by
        rw [getElem!_pos _ q hq]
        exact hqv
      have hpt : fixPt i = vecP orbS5 q := by
        show toRow (sevenFix.getD i rootV).toVec = toRow (orbS5.pts[q]!).toVec
        rw [hvq]
      rw [hpt]
      refine ⟨?_, (smul_vecP_eq_iff hM hq').2 (by rw [hvq]; exact hbeq)⟩
      have hD : vecP orbS5 q ∈ Dlt 5 := by
        rw [Dlt_five_eq hF, Finset.mem_coe, Finset.mem_image]
        exact ⟨q, Finset.mem_range.2 hq', rfl⟩
      exact Dlt_orbit hD

theorem fixPt_injective : Function.Injective fixPt := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := chkSeven_parts
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  have h := h9 i i.2 j j.2 hne'
  have heq : (sevenFix.getD i rootV).toVec = (sevenFix.getD j rootV).toVec := hij
  rw [V2.toVec_inj (getD_wf i.2) (getD_wf j.2)] at heq
  rw [heq, V2.beq_iff.2 rfl] at h
  exact Bool.noConfusion h

theorem root_notMem_range_fixPt : w₀ ∉ Set.range fixPt := by
  obtain ⟨-, -, -, -, -, h6, h7, h8, -⟩ := chkSeven_parts
  rintro ⟨i, hi⟩
  have hl : (i : ℕ) < sevenFix.length := by rw [sevenFix_length]; exact i.2
  have heq : (sevenFix.getD i rootV).toVec = rootV.toVec := hi
  rw [V2.toVec_inj (getD_wf i.2) h7] at heq
  have hmem : sevenFix.getD i rootV ∈ sevenFix := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have h := h8 _ hmem
  rw [heq, V2.beq_iff.2 rfl] at h
  exact Bool.noConfusion h

theorem ncard_fixed
    (hF : J4Facts) :
    {p : Row | (∃ j : J, j • w₀ = p) ∧ sevenElt • p = p}.ncard = 5 := by
  rw [fixed_orbit_eq hF, Set.ncard_insert_of_notMem root_notMem_range_fixPt (Set.finite_range _),
    Set.ncard_range_of_injective fixPt_injective]
  simp

theorem finite_fixed
    (hF : J4Facts) :
    {p : Row | (∃ j : J, j • w₀ = p) ∧ sevenElt • p = p}.Finite := by
  rw [fixed_orbit_eq hF]
  exact (Set.finite_range _).insert _

end CFSG.Quasithin.J4Seven
