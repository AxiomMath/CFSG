module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNorm
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNst

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin.H13.F431.Un CFSG.Quasithin CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem orderOf_cj5 (s : hypPSU h 2 1) : orderOf (cj5 h s) = orderOf s :=
  orderOf_injective (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1))
    (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective (u5_center_eq_bot h)) s

include h in
theorem orderOf_cj5_z5Y : orderOf (cj5 h (z5Y h)) = 2 := by
  rw [orderOf_cj5 h, orderOf_z5Y]

include h in
theorem orderOf_cj5_t5Y : orderOf (cj5 h (t5Y h)) = 2 := by
  rw [orderOf_cj5 h, orderOf_t5Y]

theorem cj5_z5Y_mem_S :
    cj5 h (z5Y h) ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ :=
  cj5_mem_Ssd5 h z5Y_mem_U

theorem cj5_t5Y_mem_S :
    cj5 h (t5Y h) ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ :=
  cj5_mem_Ssd5 h t5Y_mem_U

include h in
theorem zt_not_conj5 (k : MulAut (hypPSU h 2 1)) :
    k * cj5 h (z5Y h) * k⁻¹ ≠ cj5 h (t5Y h) := by
  intro e
  rw [aut5_mul_cj5_mul_inv] at e
  exact noconj_Y k (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective (u5_center_eq_bot h) e)

include h in
theorem z_ZN5 (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀) :
    cj5 h (z5Y h) ∈ centerOf (perfectCore (K₀ ⊓ autStab (u5PtP h))) := by
  rw [centerOf_perfectCore_N5 h hf hinn]
  exact ⟨z₁SU h, z₁SU_mem_ZPsub, rfl⟩

include h in
theorem Z_sq5 (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    {x : MulAut (hypPSU h 2 1)} (hx : x ∈ centerOf (perfectCore (K₀ ⊓ autStab (u5PtP h)))) :
    x ^ 2 = 1 := by
  rw [centerOf_perfectCore_N5 h hf hinn] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  rw [sq, ← map_mul, Vsub_sq (ZPsub_le_Vsub hw), map_one]

include h in
theorem ZN_trans5 (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    {x : MulAut (hypPSU h 2 1)} (hx : x ∈ centerOf (perfectCore (K₀ ⊓ autStab (u5PtP h))))
    (hx1 : x ≠ 1) :
    ∃ m ∈ K₀ ⊓ autStab (u5PtP h), m * cj5 h (z5Y h) * m⁻¹ = x := by
  rw [centerOf_perfectCore_N5 h hf hinn] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hwZ : hypProj h 2 1 w ∈ centerOf (perfectCore (u5PtP h)) := by
    rw [centerOf_perfectCore_u5PtP h hf]
    exact Subgroup.mem_map_of_mem _ hw
  have hw1 : hypProj h 2 1 w ≠ 1 := fun e => hx1 (by
    change MulAut.conj (hypProj h 2 1 w) = 1
    rw [e, map_one])
  obtain ⟨m, hm, e⟩ := ZP_trans_Y hf hwZ hw1
  refine ⟨cj5 h m, ⟨hinn ⟨m, rfl⟩, cj5_mem_autStab h hm⟩, ?_⟩
  rw [← cj5_inv, ← cj5_mul, ← cj5_mul, e]
  rfl

include h in
theorem center_T5 (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))} (hinn : Pi h ≤ K₀)
    {F₂ : Subgroup (K ≃+* K)}
    (hT2 : IsPGroup 2 ↥(Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂))
    {w : MulAut (hypPSU h 2 1)} (hw : w ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂)
    (hc : ∀ y ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂, y * w = w * y)
    (hw1 : w ≠ 1) :
    ∃ m ∈ K₀ ⊓ autStab (u5PtP h), m * cj5 h (z5Y h) * m⁻¹ = w := by
  have hZ := u5_center_eq_bot h
  have hinj := CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ
  obtain ⟨k, hk⟩ := hT2 ⟨w, hw⟩
  have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hVT : ∀ v ∈ Vh h, v ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ := by
    intro v hv
    have : v ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥ := by
      rw [Ssd5_bot_eq_Uh]
      exact Sh_le_Uh (Vh_le_Sh hv)
    exact Ssd5_mono h le_rfl bot_le this
  have hwS : w ∈ Sh h := twoCentralizerV h hf hZ w ⟨k, hk'⟩ (fun v hv => (hc v (hVT v hv)).symm)
  obtain ⟨g, hg, rfl⟩ := hwS
  set y : hypPSU h 2 1 := hypProj h 2 1 g with hy
  have hyU : y ∈ hypProjUnitriangular h 2 1 := ⟨g, Ssub_le_Usub hg, rfl⟩
  have hcomm : ∀ u ∈ hypProjUnitriangular h 2 1, u * y = y * u := by
    intro u hu
    have hcu : cj5 h u ∈ Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂ :=
      cj5_mem_Ssd5 h hu
    have := hc _ hcu
    apply hinj
    rw [map_mul, map_mul]
    exact this
  have hy1 : y ≠ 1 := fun e => hw1 (by
    change MulAut.conj y = 1
    rw [e, map_one])
  obtain ⟨b, hb, e⟩ := center_Y hyU hcomm hy1
  refine ⟨cj5 h b, ⟨hinn ⟨b, rfl⟩, cj5_mem_autStab h hb.1⟩, ?_⟩
  rw [← cj5_inv, ← cj5_mul, ← cj5_mul, e]
  rfl

end CFSG.Quasithin.H13.F431.Un.OL5
