module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec311Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_conj_Rt_le (h56 : Stroth56NatStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2) {ν : G} (hνM : ν ∈ M)
    (hνV : ν ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) :
    conjSubgroup ν (conjSubgroup ρ (LB M Q B)) ≤ Rt M (LB M Q B) t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hνρM : ν * ρ ∈ M := M.mul_mem hνM hρM
  have hsub : conjSubgroup (ν * ρ) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    refine sup_le ?_ sec39_Z_le_Vt
    have h1 : conjSubgroup ρ B ≤ Vt M (LB M Q B) B Z t :=
      le_sup_left.trans (hc.conj_Rt_le_Vt ht hρ)
    have h2 : conjSubgroup ν (conjSubgroup ρ B) ≤ conjSubgroup ν (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono h1
    rw [conjSubgroup_eq_self_iff.mpr hνV] at h2
    rwa [conjSubgroup_mul]
  obtain ⟨ρ', hρ', hBZ⟩ := h56 G M Q Z B hc n t hs hnom (ν * ρ) hνρM hsub
  have hρ'M : ρ' ∈ M := hc.Rt_le_M t hρ'
  rw [← conjSubgroup_mul, hc.conj_LB_eq_of_conj_BZ hνρM hρ'M hBZ]
  exact hc.conj_LB_le_Rt ht hρ'

theorem sec7ctr_conj_Rt_eq (h56 : Stroth56NatStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2) {r : G} (hr : Sec7A hc t r) {ν : G}
    (hνM : ν ∈ M) (hνV : ν ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)) :
    conjSubgroup ν (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hle : conjSubgroup ν (Rt M (LB M Q B) t) ≤ Rt M (LB M Q B) t := by
    have e : Rt M (LB M Q B) t = conjSubgroup 1 (LB M Q B) ⊔ conjSubgroup r (LB M Q B) := by
      rw [conjSubgroup_one, ← hc.LB_conj hrM]
      exact hr.gen
    calc conjSubgroup ν (Rt M (LB M Q B) t)
        = conjSubgroup ν (conjSubgroup 1 (LB M Q B)) ⊔
            conjSubgroup ν (conjSubgroup r (LB M Q B)) := by
          rw [e, conjSubgroup_sup']
      _ ≤ Rt M (LB M Q B) t :=
          sup_le (sec7ctr_conj_Rt_le h56 hc hs hnom hνM hνV (Subgroup.one_mem _))
            (sec7ctr_conj_Rt_le h56 hc hs hnom hνM hνV hr.mem)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem sec7NormZ0_of_inputs (h56 : Stroth56NatStatement) (hA : Sec7AExistsStatement) :
    Sec7NormZ0Statement := by
  intro G _ _ M Q Z B hc n t hs hnom Z0 hZ0 ν hνM hνV
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hRν := sec7ctr_conj_Rt_eq h56 hc hs hnom hr hνM hνV
  have hνR : ν ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) :=
    conjSubgroup_eq_self_iff.mp hRν
  have hνQ : ∀ y ∈ Q, ν * y * ν⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hνM) y).mp hy
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hzZ : z ∈ Z0 := hz
  obtain ⟨hzR, hzc⟩ := (hZ0 z).mp hzZ
  refine (hZ0 (ν * z * ν⁻¹)).mpr ⟨(Subgroup.mem_normalizer_iff.mp hνR z).mp hzR, fun ρ hρ => ?_⟩
  have hρ' : ν⁻¹ * ρ * ν ∈ Rt M (LB M Q B) t := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hνR) ρ).mp hρ
    simpa using this
  have e : ⁅ν * z * ν⁻¹, ρ⁆ = ν * ⁅z, ν⁻¹ * ρ * ν⁆ * ν⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hνQ _ (hzc _ hρ')

end CFSG.RankThree.GF2n.Stroth80
