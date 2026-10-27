module

public import CFSG.Quasithin.Vol2.Ch11SecFStep2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
theorem conjClosure_le_centralizer_of {Z H W : Subgroup G}
    (hZ : Z ≤ Subgroup.centralizer (W : Set G)) (hH : H ≤ Subgroup.normalizer (W : Set G)) :
    conjClosure Z H ≤ Subgroup.centralizer (W : Set G) := by
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : h⁻¹ * w * h ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hH hh)) w).mp hw
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp (hZ hz) _ hw'
  calc w * (h * z * h⁻¹) = h * ((h⁻¹ * w * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * w * h)) * h⁻¹ := by rw [hc]
    _ = h * z * h⁻¹ * w := by group

omit [Finite G] in
theorem isMulCommutative_of_le_centralizer {W : Subgroup G}
    (hW : W ≤ Subgroup.centralizer (W : Set G)) : IsMulCommutative ↥W :=
  ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hW b.2) a a.2)⟩⟩

theorem conjClosure_le_centralizer_V₃ (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) :
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.centralizer (V₃ : Set G) := by
  have hS2 := commutator_V₃_conj_eq_bot hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
    hV₃ hk
  refine conjClosure_le fun g hg z hz => ?_
  have hmem : g * z * g⁻¹ ∈ conjSubgroup (fsuV T I) g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hz
  have hle : V₃ ≤ Subgroup.centralizer (conjSubgroup (fsuV T I) g⁻¹ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hS2 _ (Subgroup.inv_mem _ hg))
  exact (Subgroup.le_centralizer_iff.mp hle) hmem

theorem conjClosure_V₃_le_centralizer (hF : Sp4Facts) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) :
    conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.centralizer
        (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) : Set G) :=
  conjClosure_le_centralizer_of (Subgroup.le_centralizer_iff.mp
    (conjClosure_le_centralizer_V₃ hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃
      hk)) (le_normalizer_conjClosure _ _)

omit [Finite G] in
theorem conjClosure_le_pCoreOf (hQ : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤
      pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
  conjClosure_le fun _ hg z hz => (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg) z).mp (hQ hz)

theorem commutator_fsuV_conjClosure_le (hF : Sp4Facts) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) :
    ⁅fsuV T I, conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))⁆ ≤ V₁ := by
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  refine hF.z G T L I n V₁ V₃ (SecD.natSetting11_of h1102 h1141 h hV₁) hk hV₁ hV₃ _
    ((conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_ROf h hV₁)) ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
  exact conjClosure_le_centralizer_V₃ hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃
    hk

omit [Finite G] in
theorem commutator_fsuV_conjClosure_ne_bot {V : Subgroup G} {H : Subgroup G}
    (hW : ¬ IsMulCommutative ↥(conjClosure V H)) : ⁅V, conjClosure V H⁆ ≠ ⊥ := by
  intro hbot
  apply hW
  refine isMulCommutative_of_le_centralizer (conjClosure_le_centralizer_of ?_
    (le_normalizer_conjClosure _ _))
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

end CFSG.Quasithin.Vol2.Ch11.SecF
