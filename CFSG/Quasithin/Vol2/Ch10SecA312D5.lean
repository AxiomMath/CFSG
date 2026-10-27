module

public import CFSG.Quasithin.Vol2.Ch10SecA312D1
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312D

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X] {T B₁ B₂ : Subgroup X}

omit [Finite X] in
theorem ne_top_of_le_normalizer (hq : CFSG.IsQuasisimple X) (hB₁ : B₁ ∈ lFamily T)
    (hne₁ : B₁ ≠ ⊤) {M : Subgroup X} (hM : M ≤ Subgroup.normalizer (B₁ : Set X)) : M ≠ ⊤ := by
  rintro rfl
  have hn : B₁.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hM)
  have hB : B₁ ∈ cComp (B₁ ⊔ T) := hB₁
  rcases A3.eq_top_or_le_center_of_subnormal hq hn.isSubnormal with h | h
  · exact hne₁ h
  · apply ne_bot_of_mem_cComp hB
    rw [← perfect_of_mem_cComp hB, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y _ => Subgroup.mem_center_iff.mp (h hx) y

theorem not_isSolvable_of_le (hB₁ : B₁ ∈ lFamily T) {M : Subgroup X} (hM : B₁ ≤ M) :
    ¬ Group.IsSolvable ↥M := fun _ =>
  not_isSolvable_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ T) from hB₁)
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hM)
      (Subgroup.inclusion_injective _))

theorem dInf_sup_eq (hB : B₁ ∈ lFamily T) (hT : IsPGroup 2 T)
    (hN : T ≤ Subgroup.normalizer (B₁ : Set X)) : Setup.X6.dInf (B₁ ⊔ T) = B₁ := by
  rw [Vol2Native.A312L.dInf_eq_perfectCore,
    H13.perfectCore_sup_eq (perfect_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ T) from hB)) hT hN]

theorem false_of_residual (hq : CFSG.IsQuasisimple X) (hT : IsSylowTwoOf T ⊤)
    {P : Fin 2 → Subgroup X} (hP : Setup.X6.ResidualOvergroupsAt X T P) (hB₁ : B₁ ∈ lFamily T)
    (hB₂ : B₂ ∈ lFamily T) (hne₁ : B₁ ≠ ⊤) (hne : B₁ ≠ B₂)
    (hN₁ : T ≤ Subgroup.normalizer (B₁ : Set X)) (hN₂ : T ≤ Subgroup.normalizer (B₂ : Set X))
    (hc : ⁅B₁, B₂⁆ ≤ B₁) : False := by
  have hM : B₁ ⊔ B₂ ⊔ T ≠ ⊤ := ne_top_of_le_normalizer hq hB₁ hne₁
    (sup_le (sup_le Subgroup.le_normalizer (le_normalizer_of_commutator_le hc)) hN₁)
  have hres := hP.2.2.2.2.1
  obtain ⟨j, hj, hdj⟩ := hres _ le_sup_right hM
    (not_isSolvable_of_le hB₁ (le_sup_left.trans le_sup_left))
  have key : ∀ {B : Subgroup X}, B ∈ lFamily T → T ≤ Subgroup.normalizer (B : Set X) →
      B ≤ B₁ ⊔ B₂ ⊔ T → B = Setup.X6.dInf (B₁ ⊔ B₂ ⊔ T) := by
    intro B hB hNB hBM
    have hBT : B ⊔ T ≤ B₁ ⊔ B₂ ⊔ T := sup_le hBM le_sup_right
    obtain ⟨k, hk, hdk⟩ := hres (B ⊔ T) le_sup_right
      (fun h => hM (top_le_iff.mp (h ▸ hBT))) (not_isSolvable_of_le hB le_sup_left)
    have hkj : j = k := (hk j).mp (hBT.trans ((hj j).mpr rfl))
    rw [← dInf_sup_eq hB hT.2.1 hNB, hdk, ← hkj, ← hdj]
  exact hne ((key hB₁ hN₁ (le_sup_left.trans le_sup_left)).trans
    (key hB₂ hN₂ (le_sup_right.trans le_sup_left)).symm)

theorem false_of_tits
    (hq : CFSG.IsQuasisimple X) (hX : IsTits X) (hT : IsSylowTwoOf T ⊤) (hB₁ : B₁ ∈ lFamily T)
    (hne₁ : B₁ ≠ ⊤) (hN₁ : T ≤ Subgroup.normalizer (B₁ : Set X)) : False := by
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := Setup.X6.titsSylowOvergroupLattice X hX T hT
  have hM : B₁ ⊔ T ≠ ⊤ :=
    ne_top_of_le_normalizer hq hB₁ hne₁ (sup_le Subgroup.le_normalizer hN₁)
  have hns := not_isSolvable_of_le hB₁ (le_sup_left : B₁ ≤ B₁ ⊔ T)
  rcases hlat (B₁ ⊔ T) le_sup_right with h | h | h | h
  · rw [h] at hns
    have := hT.2.1.isNilpotent
    exact hns inferInstance
  · exact hns (h ▸ hHs)
  · exact hns (h ▸ hNs)
  · exact hM h

theorem false_of_rank2
    (hq : CFSG.IsQuasisimple X) (hR : IsRank2LieChar2 ↥(⊤ : Subgroup X)) (hT : IsSylowTwoOf T ⊤)
    (hB₁ : B₁ ∈ lFamily T) (hB₂ : B₂ ∈ lFamily T) (hne₁ : B₁ ≠ ⊤) (hne : B₁ ≠ B₂)
    (hN₁ : T ≤ Subgroup.normalizer (B₁ : Set X)) (hN₂ : T ≤ Subgroup.normalizer (B₂ : Set X))
    (hc : ⁅B₁, B₂⁆ ≤ B₁) : False := by
  by_cases hTits : IsTits X
  · exact false_of_tits hq hTits hT hB₁ hne₁ hN₁
  · obtain ⟨P, hP⟩ :=
      H13.residualOvergroups_of_rank2 (hR.of_mulEquiv Subgroup.topEquiv) hTits hT
    exact false_of_residual hq hT hP hB₁ hB₂ hne₁ hne hN₁ hN₂ hc

end CFSG.Quasithin.Vol2.Ch10.A312D
