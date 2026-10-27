module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Cent
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Ln
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Pt
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open scoped Pointwise commutatorElement
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

noncomputable abbrev u5PtP (h : UnitaryFieldData 2 f K) : Subgroup (hypPSU h 2 1) :=
  projIsoStabilizer h 2 1 (hypFlag h 2 1 1)

noncomputable abbrev u5LnP (h : UnitaryFieldData 2 f K) : Subgroup (hypPSU h 2 1) :=
  projIsoStabilizer h 2 1 (hypFlag h 2 1 2)

theorem U_le_perfectCore_u5PtP (hf : 2 ≤ f) :
    hypProjUnitriangular h 2 1 ≤ perfectCore (u5PtP h) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [u5PtP, projIsoStabilizer, ← map_perfectCore]
  exact Subgroup.map_mono (U_le_perfectCore_u5PtStab hf)

theorem U_le_perfectCore_u5LnP (hf : 2 ≤ f) :
    hypProjUnitriangular h 2 1 ≤ perfectCore (u5LnP h) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [u5LnP, projIsoStabilizer, ← map_perfectCore]
  exact Subgroup.map_mono (U_le_perfectCore_u5LnStab hf)

theorem centerOf_u5PtP_le (hf : 2 ≤ f) :
    centerOf (perfectCore (u5PtP h)) ≤ (ZPsub h).map (hypProj h 2 1) := fun _ ha =>
  centralizer_le_map_ZPsub (Subgroup.centralizer_le (fun _ hx => U_le_perfectCore_u5PtP hf hx) ha.2)

theorem centerOf_u5LnP_le (hf : 2 ≤ f) :
    centerOf (perfectCore (u5LnP h)) ≤ (ZPsub h).map (hypProj h 2 1) := fun _ ha =>
  centralizer_le_map_ZPsub (Subgroup.centralizer_le (fun _ hx => U_le_perfectCore_u5LnP hf hx) ha.2)

theorem trans_u5PtP (hf : 2 ≤ f) {a a' : hypPSU h 2 1} (ha : a ∈ centerOf (perfectCore (u5PtP h)))
    (ha' : a' ∈ centerOf (perfectCore (u5PtP h))) (h1 : a ≠ 1) (h1' : a' ≠ 1) :
    ∃ m ∈ u5PtP h, m * a * m⁻¹ = a' := by
  obtain ⟨z, hz, rfl⟩ := centerOf_u5PtP_le hf ha
  obtain ⟨z', hz', rfl⟩ := centerOf_u5PtP_le hf ha'
  obtain ⟨m, hm, e⟩ := exists_conj_ZPsub hz hz' (fun e => h1 (by rw [e, map_one]))
    (fun e => h1' (by rw [e, map_one]))
  refine ⟨hypProj h 2 1 m, Subgroup.mem_map_of_mem _
    (hypBorel_le_isoStabilizer h le_rfl (by norm_num) (hypTorus_le_hypBorel h hm)), ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, e]

theorem centerOf_u5LnP_eq_bot (hf : 2 ≤ f) : centerOf (perfectCore (u5LnP h)) = ⊥ := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨z, hz, rfl⟩ := centerOf_u5LnP_le hf ha
  obtain ⟨t, htI, htN, hne⟩ := exists_torus_line (h := h) hf
  have htP : hypProj h 2 1 t ∈ perfectCore (u5LnP h) := by
    rw [u5LnP, projIsoStabilizer, ← map_perfectCore]
    exact Subgroup.mem_map_of_mem _ (N₁sub_le_perfectCore_u5LnStab htN)
  have hc := Subgroup.mem_centralizer_iff.mp ha.2 _ htP
  have htz : t * z * t⁻¹ = z := by
    have hZ : t * z * t⁻¹ * z⁻¹ ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, hc, mul_inv_cancel_right]
    have hzc := torus_conj_mem_patSub isPattern_sZP htI hz
    have hU : t * z * t⁻¹ * z⁻¹ ∈ hypUnitriangular h 2 1 :=
      mul_mem hzc.1 (inv_mem (ZPsub_le_U hz))
    have hmem : t * z * t⁻¹ * z⁻¹ ∈ (⊥ : Subgroup (hypSU h 2 1)) := by
      rw [← hypUnitriangular_inf_hypScalars h (r := 2) (ε := 1) (by norm_num) (by norm_num)]
      exact ⟨hU, hZ⟩
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at hmem
  have e : mat (t * z * t⁻¹) ιe₁ ιf₁ = mat z ιe₁ ιf₁ := by rw [htz]
  rw [torus_conj_apply htI] at e
  have hb := torus_ne_zero htI ιf₁
  have h0 : mat z ιe₁ ιf₁ * (mat t ιe₁ ιe₁ - mat t ιf₁ ιf₁) = 0 := by
    field_simp at e
    linear_combination e
  have hz0 : mat z ιe₁ ιf₁ = 0 :=
    (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 (hne ιe₁ ιf₁ (by decide)))
  have hz1 : z = 1 := eq_of_mem_ZPsub hz (one_mem _) (by
    rw [hz0, mat_one, one_apply_ne (by decide)])
  rw [hz1, map_one]
  exact Subgroup.one_mem _

theorem u5PtP_inf_u5LnP : u5PtP h ⊓ u5LnP h = hypProjBorel h 2 1 := by
  have hB : u5PtStab h ⊓ u5LnStab h = hypBorel h 2 1 := by
    ext g
    rw [Subgroup.mem_inf, mem_hypBorel]
    constructor
    · rintro ⟨g1, g2⟩ i hi1 hi2
      interval_cases i
      · exact mem_isoStabilizer.mp g1
      · exact mem_isoStabilizer.mp g2
    · intro hg
      exact ⟨mem_isoStabilizer.mpr (hg 1 le_rfl (by norm_num)),
        mem_isoStabilizer.mpr (hg 2 (by norm_num) le_rfl)⟩
  have hc : (u5PtP h ⊓ u5LnP h).comap (hypProj h 2 1) = hypBorel h 2 1 := by
    rw [Subgroup.comap_inf, u5PtP, u5LnP, comap_projIsoStabilizer, comap_projIsoStabilizer]
    exact hB
  rw [← Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective h 2 1) (u5PtP h ⊓ u5LnP h),
    hc]
  rfl

theorem u5PtP_le_normalizer :
    u5PtP h ≤ Subgroup.normalizer (((ZPsub h).map (hypProj h 2 1) : Subgroup (hypPSU h 2 1)) :
      Set (hypPSU h 2 1)) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g * z * g⁻¹, conj_mem_ZPsub_of_mem_u5PtStab hg hz, by simp⟩
  · rintro ⟨z', hz', e⟩
    refine ⟨g⁻¹ * z' * g, ?_, ?_⟩
    · simpa using conj_mem_ZPsub_of_mem_u5PtStab (inv_mem hg) hz'
    · simp only [map_mul, map_inv, e]
      group

theorem u5LnP_le_normalizer :
    u5LnP h ≤ Subgroup.normalizer (((Vsub h).map (hypProj h 2 1) : Subgroup (hypPSU h 2 1)) :
      Set (hypPSU h 2 1)) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨g * v * g⁻¹, conj_mem_Vsub_of_mem_u5LnStab hg hv, by simp⟩
  · rintro ⟨v', hv', e⟩
    refine ⟨g⁻¹ * v' * g, ?_, ?_⟩
    · simpa using conj_mem_Vsub_of_mem_u5LnStab (inv_mem hg) hv'
    · simp only [map_mul, map_inv, e]
      group

theorem map_ZPsub_ne_bot : (ZPsub h).map (hypProj h 2 1) ≠ ⊥ := by
  intro hbot
  have hz := z₁SU_mem_ZPsub (h := h)
  have h1 : hypProj h 2 1 (z₁SU h) = 1 := by
    have : hypProj h 2 1 (z₁SU h) ∈ (ZPsub h).map (hypProj h 2 1) :=
      Subgroup.mem_map_of_mem _ hz
    rwa [hbot, Subgroup.mem_bot] at this
  have h2 : z₁SU h ∈ (⊥ : Subgroup (hypSU h 2 1)) := by
    rw [← hypUnitriangular_inf_hypScalars h (r := 2) (ε := 1) (by norm_num) (by norm_num)]
    exact ⟨ZPsub_le_U hz, by rw [← ker_hypProj]; exact h1⟩
  exact z₁SU_ne_one (h := h) (Subgroup.mem_bot.mp h2)

theorem map_Vsub_ne_bot : (Vsub h).map (hypProj h 2 1) ≠ ⊥ := fun hbot =>
  map_ZPsub_ne_bot (h := h) (eq_bot_iff.mpr (hbot ▸ Subgroup.map_mono ZPsub_le_Vsub))

theorem isPGroup_map_ZPsub : IsPGroup 2 ((ZPsub h).map (hypProj h 2 1)) :=
  (u5_sylow h).2.1.to_le (Subgroup.map_mono (ZPsub_le_U (h := h) |>.trans le_rfl))

theorem isPGroup_map_Vsub : IsPGroup 2 ((Vsub h).map (hypProj h 2 1)) :=
  (u5_sylow h).2.1.to_le (Subgroup.map_mono (Vsub_le_Ssub.trans Ssub_le_Usub))

end CFSG.Quasithin.H13.Sec53F.Unit
