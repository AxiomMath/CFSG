module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieVB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieIso
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpAbs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.Quasithin.H13.Sec53F CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K

section Generic

variable {G : Type*} [Group G]

theorem un5v_normalizer_center_pCore {H : Subgroup G} {α : G}
    (hα : α ∈ Subgroup.normalizer (H : Set G)) :
    α ∈ Subgroup.normalizer ((centerOf (pCoreOf 2 H) : Subgroup G) : Set G) := by
  have h1 : H.map (MulAut.conj α).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hα y).1 hy
    · intro hx
      refine ⟨α⁻¹ * x * α, ?_, by show α * (α⁻¹ * x * α) * α⁻¹ = x; group⟩
      have := (Subgroup.mem_normalizer_iff.1 hα (α⁻¹ * x * α)).2 (by simpa [mul_assoc] using hx)
      exact this
  have h2 := CFSG.Quasithin.H13.F431.Un.unOut_centerOf_pCoreOf_map (MulAut.conj α) H
  rw [h1] at h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj α).toMonoidHom x ∈ (centerOf (pCoreOf 2 H)).map
        (MulAut.conj α).toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [← h2] at this
    simpa [MulAut.conj_apply] using this
  · intro hx
    rw [h2] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj α).injective (by simpa [MulAut.conj_apply] using hyx)
    rwa [this] at hy

end Generic

section Main

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] def un5vQ : Subgroup (MulAut (hypPSU hK 2 1)) :=
  (u5LnP hK).map (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1))

theorem un5v_mem_Q {g : hypPSU hK 2 1} : MulAut.conj g ∈ un5vQ hK ↔ g ∈ u5LnP hK :=
  Subgroup.mem_map_iff_mem (conj_injective (u5_center_eq_bot hK))

theorem un5v_V'_le (hf : 2 ≤ f) : (Vsub hK).map (hypProj hK 2 1) ≤ u5LnP hK :=
  (Subgroup.map_mono (Vsub_le_Ssub.trans Ssub_le_Usub)).trans
    ((U_le_perfectCore_u5LnP hf).trans (CFSG.Quasithin.perfectCore_le _))

theorem un5v_Vh_le_Q (hf : 2 ≤ f) : Vh hK ≤ un5vQ hK := by
  rw [un5v_Vh_eq]
  exact Subgroup.map_mono (un5v_V'_le hK hf)

theorem un5v_Q_le_normalizer : un5vQ hK ≤
    Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have inj := conj_injective (u5_center_eq_bot hK)
  intro x
  rw [un5v_Vh_eq]
  have hN := u5LnP_le_normalizer (h := hK) hg
  rw [Subgroup.mem_normalizer_iff] at hN
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (hN y).1 hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have := (hN (g⁻¹ * y * g)).2 (by simpa [mul_assoc] using hy)
      exact this
    · have := congrArg (fun a => (MulAut.conj g)⁻¹ * a * MulAut.conj g) hyx
      simp only [map_inv, map_mul] at this ⊢
      rw [this]
      group

theorem un5v_isPGroup_Vh : IsPGroup 2 ↥(Vh hK) := fun g =>
  ⟨1, Subtype.ext (by
    show (g : MulAut (hypPSU hK 2 1)) ^ 2 ^ 1 = 1
    simpa [sq] using Vh_sq g.2)⟩

theorem un5v_centerOf_eq_zOf (S : Subgroup (MulAut (hypPSU hK 2 1))) : centerOf S = zOf S := by
  ext x
  rw [mem_centerOf_iff, mem_zOf_iff]

theorem un5v_four_le (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem un5v_pCore_Q_le (hf : 2 ≤ f) : pCoreOf 2 (un5vQ hK) ≤ Sh hK := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_hyp hK
  refine core_Sh (u5_center_eq_bot hK) (un5v_four_le hf)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
  intro ρ hρP hρS
  obtain ⟨g, rfl⟩ := hρP
  have hg := un5v_cj_mem_normalizer_Vh hK (mem_normalizer_Vh_of_Sh (u5_center_eq_bot hK) hρS)
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ ((un5v_mem_Q hK).2 hg)

theorem un5v_innM_lev_mem_Q (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    innM hK (lev A hA) ∈ un5vQ hK :=
  ⟨hypProj hK 2 1 (lev A hA), ⟨lev A hA, un5v_lev_mem_u5LnStab hK A hA, rfl⟩, rfl⟩

theorem un5v_center_pCore_Q (hf : 2 ≤ f) : centerOf (pCoreOf 2 (un5vQ hK)) = Vh hK := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_hyp hK
  have hVR : Vh hK ≤ pCoreOf 2 (un5vQ hK) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (un5v_Vh_le_Q hK hf)
      (un5v_Q_le_normalizer hK) (un5v_isPGroup_Vh hK)
  rcases un5v_irr hK (un5v_pCore_Q_le hK hf) hVR (fun A hA =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (un5v_innM_lev_mem_Q hK A hA)) with h | h
  · rw [h]
    ext x
    rw [mem_centerOf_iff]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun s hs => Vh_comm hs hx⟩⟩
  · rw [h, un5v_centerOf_eq_zOf, zOf_Sh (u5_center_eq_bot hK)]

end Main

end CFSG.Quasithin.H13.F431.Un.OL5
