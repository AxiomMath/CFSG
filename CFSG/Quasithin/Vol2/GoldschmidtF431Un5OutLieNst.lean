module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieF
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSet

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin.H13.F431 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem nst5_normalizer_eq_of_isCoatom {Y : Type*} [Group Y] [IsSimpleGroup Y] {B : Subgroup Y}
    (hB : IsCoatom B) (hB1 : B ≠ ⊥) : Subgroup.normalizer (B : Set Y) = B := by
  rcases hB.le_iff.1 (Subgroup.le_normalizer (H := B)) with hN | hN
  · exfalso
    have : B.Normal := Subgroup.normalizer_eq_top_iff.1 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with e | e
    · exact hB1 e
    · exact hB.1 e
  · exact hN

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem cj5_mem_autStab_iff {B : Subgroup (hypPSU h 2 1)} {y : hypPSU h 2 1} :
    cj5 h y ∈ autStab B ↔ y ∈ Subgroup.normalizer (B : Set (hypPSU h 2 1)) := by
  rw [Subgroup.mem_normalizer_iff]
  exact Iff.rfl

include h in
theorem u5PtP_normalizer : Subgroup.normalizer (u5PtP h : Set (hypPSU h 2 1)) = u5PtP h := by
  have := isSimpleGroup_hypPSU_five h
  have hY := u5_yamStd (h := h)
  refine nst5_normalizer_eq_of_isCoatom hY.coatom₀ fun e => z5Y_ne_one (h := h) ?_
  have hz : z5Y h ∈ u5PtP h := hY.le₀ (Subgroup.le_normalizer z5Y_mem_U)
  rw [e] at hz
  exact Subgroup.mem_bot.1 hz

include h in
theorem u5LnP_normalizer : Subgroup.normalizer (u5LnP h : Set (hypPSU h 2 1)) = u5LnP h := by
  have := isSimpleGroup_hypPSU_five h
  have hY := u5_yamStd (h := h)
  refine nst5_normalizer_eq_of_isCoatom hY.coatom₁ fun e => z5Y_ne_one (h := h) ?_
  have hz : z5Y h ∈ u5LnP h := hY.le₁ (Subgroup.le_normalizer z5Y_mem_U)
  rw [e] at hz
  exact Subgroup.mem_bot.1 hz

include h in
theorem nst5_perfectCore_eq (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))}
    (hinn : Pi h ≤ K₀) {B : Subgroup (hypPSU h 2 1)}
    (hB : Subgroup.normalizer (B : Set (hypPSU h 2 1)) = B) :
    perfectCore (K₀ ⊓ autStab B) =
      (perfectCore B).map (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have hZ := u5_center_eq_bot h
  set N := K₀ ⊓ autStab B with hN
  set N₀ := B.map (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)) with hN₀
  have hN₀N : N₀ ≤ N := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨hinn ⟨b, rfl⟩, (cj5_mem_autStab_iff h).2 (Subgroup.le_normalizer hb)⟩
  have hNPi : N ⊓ Pi h ≤ N₀ := by
    rintro α ⟨hαN, ⟨y, rfl⟩⟩
    refine ⟨y, ?_, rfl⟩
    rw [← hB]
    exact (cj5_mem_autStab_iff h).1 hαN.2
  have hperf := perfectLeInn h hf hZ (perfectCore N) (perfectCore_perfect N)
  have h1 : perfectCore N ≤ N₀ := fun x hx => hNPi ⟨perfectCore_le N hx, hperf hx⟩
  have h2 : perfectCore N ≤ perfectCore N₀ := le_perfectCore_of_perfect h1 (perfectCore_perfect N)
  have h3 : perfectCore N₀ ≤ perfectCore N := perfectCore_mono hN₀N
  rw [le_antisymm h2 h3, hN₀]
  exact perfectCore_map_of_injective (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1))
    (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ) B

include h in
theorem nst5_centerOf_perfectCore_eq (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))}
    (hinn : Pi h ≤ K₀) {B : Subgroup (hypPSU h 2 1)}
    (hB : Subgroup.normalizer (B : Set (hypPSU h 2 1)) = B) :
    centerOf (perfectCore (K₀ ⊓ autStab B)) =
      (centerOf (perfectCore B)).map
        (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [nst5_perfectCore_eq h hf hinn hB]
  exact centerOf_map_of_injective (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1))
    (CFSG.RankThree.PartOne.U5K.Hyp.conj_injective (u5_center_eq_bot h)) (perfectCore B)

theorem nst5_conj_mem_centerOf {Y : Type*} [Group Y] [Finite Y] {H : Subgroup Y} {p c : Y}
    (hp : p ∈ H) (hc : c ∈ centerOf (perfectCore H)) :
    p * c * p⁻¹ ∈ centerOf (perfectCore H) := by
  have hcore : p * c * p⁻¹ ∈ perfectCore H :=
    (perfectCore_normal H).conj_mem ⟨c, perfectCore_le H hc.1⟩ hc.1 ⟨p, hp⟩
  refine ⟨hcore, ?_⟩
  show p * c * p⁻¹ ∈ Subgroup.centralizer ((perfectCore H : Subgroup Y) : Set Y)
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : p⁻¹ * d * p ∈ perfectCore H := by
    have h1 : p⁻¹ * d * p⁻¹⁻¹ ∈ perfectCore H :=
      (perfectCore_normal H).conj_mem ⟨d, perfectCore_le H hd⟩ hd ⟨p⁻¹, H.inv_mem hp⟩
    rwa [inv_inv] at h1
  have e := Subgroup.mem_centralizer_iff.1 hc.2 _ hd'
  calc d * (p * c * p⁻¹) = p * ((p⁻¹ * d * p) * c) * p⁻¹ := by group
    _ = p * (c * (p⁻¹ * d * p)) * p⁻¹ := by rw [e]
    _ = (p * c * p⁻¹) * d := by group

include h in
theorem centerOf_perfectCore_u5PtP (hf : 2 ≤ f) :
    centerOf (perfectCore (u5PtP h)) = (ZPsub h).map (hypProj h 2 1) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  refine le_antisymm (centerOf_u5PtP_le hf) ?_
  rintro _ ⟨w, hw, rfl⟩
  by_cases hw1 : w = 1
  · rw [hw1, map_one]
    exact one_mem _
  · obtain ⟨m, hm, e⟩ := exists_conj_ZPsub z₁SU_mem_ZPsub hw z₁SU_ne_one hw1
    have hmP : hypProj h 2 1 m ∈ u5PtP h :=
      Subgroup.mem_map_of_mem _ (hypBorel_le_isoStabilizer h le_rfl (by norm_num)
        (hypTorus_le_hypBorel h hm))
    have := nst5_conj_mem_centerOf hmP (z5Y_mem_centerOf hf)
    rw [← e, map_mul, map_mul, map_inv]
    exact this

include h in
theorem centerOf_perfectCore_N5 (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))}
    (hinn : Pi h ≤ K₀) :
    centerOf (perfectCore (K₀ ⊓ autStab (u5PtP h))) = (ZPsub h).map (innM h) := by
  rw [nst5_centerOf_perfectCore_eq h hf hinn (u5PtP_normalizer h),
    centerOf_perfectCore_u5PtP h hf, Subgroup.map_map]
  rfl

end CFSG.Quasithin.H13.F431.Un.OL5
