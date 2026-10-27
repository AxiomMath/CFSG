module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_eq_conjSubgroup_iff_mul_inv_mem {K : Subgroup G} {x y : G} :
    conjSubgroup K x = conjSubgroup K y ↔ x * y⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  constructor
  · intro hxy
    calc conjSubgroup K (x * y⁻¹) = conjSubgroup (conjSubgroup K x) y⁻¹ :=
          (CFSG.Quasithin.conjSubgroup_conjSubgroup K x y⁻¹).symm
      _ = conjSubgroup (conjSubgroup K y) y⁻¹ := by rw [hxy]
      _ = K := by
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  · intro hK
    calc conjSubgroup K x = conjSubgroup (conjSubgroup K (x * y⁻¹)) y := by
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel_right]
      _ = conjSubgroup K y := by rw [hK]

theorem mem_centralizer_of_mul_eq_mul {K₁ K₂ K₃ K₄ : Subgroup G}
    (h2 : K₂ ≤ Subgroup.centralizer (K₁ : Set G)) (h3 : K₃ ≤ Subgroup.centralizer (K₁ : Set G))
    (h4 : K₄ ≤ Subgroup.centralizer (K₁ : Set G)) {a b c d : G} (hb : b ∈ K₂) (hc : c ∈ K₃)
    (hd : d ∈ K₄) (habcd : a * b = c * d) : a ∈ Subgroup.centralizer (K₁ : Set G) := by
  have ha : a = c * d * b⁻¹ := by rw [← habcd]; group
  rw [ha]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h3 hc) (h4 hd)) (Subgroup.inv_mem _ (h2 hb))

namespace Hyp83

variable {V H T : Subgroup G}

theorem eSub_inf_eq_bot_of_inf_centralizer_eq_bot (h : Hyp83 V H T) {U : Subgroup G}
    (hUE : U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥) : eSub V H T ⊓ U = ⊥ := by
  refine le_bot_iff.mp fun e he => ?_
  have hc : e ∈ Subgroup.centralizer (eSub V H T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact h.isElemAbelian_eSub.comm hy he.1
  have hmem : e ∈ U ⊓ Subgroup.centralizer (eSub V H T : Set G) := ⟨he.2, hc⟩
  rw [hUE] at hmem
  exact hmem

theorem commutator_conjSubgroup_kGen_eq_bot (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (hne : conjSubgroup (kGen V H T) x ≠ conjSubgroup (kGen V H T) y) :
    ⁅conjSubgroup (kGen V H T) x, conjSubgroup (kGen V H T) y⁆ = ⊥ := by
  rw [h.conjSubgroup_kGen hOmH hx, h.conjSubgroup_kGen hOmH hy]
  refine commutator_kOrbSub_eq_bot h.elemAbelian h.isTI h.isMulCommutative_eSub h.eSub_le_H
    h.eSub_subgroupOf_normal hOmH (h.conjSubgroup_self_mem_omegaSet hx)
    (h.conjSubgroup_self_mem_omegaSet hy) ?_
  intro k hk hyk
  apply hne
  rw [h.conjSubgroup_kGen hOmH hx, h.conjSubgroup_kGen hOmH hy, hyk, kOrbSub_conjSubgroup hk]

theorem eSub_mul_conj_eq (h : Hyp83 V H T) {U : Subgroup G}
    (hUV : ∃ g, U = conjSubgroup V g) (hUH : U ≤ H)
    (hUE : U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥) {u u' z : G} (hu : u ∈ U)
    (hu' : u' ∈ U) (hu1 : u ≠ 1) (hz : z ∈ eSub V H T) :
    z * (u⁻¹ * z * u) = (u'⁻¹ * z * u') * ((u * u')⁻¹ * z * (u * u')) := by
  obtain ⟨g, hg⟩ := hUV
  have hUel : IsElemAbelian 2 U := hg ▸ isElemAbelian_conjSubgroup' h.elemAbelian g
  have hTI : CFSG.CGT.Timmesfeld75.IsTI U := hg ▸ isTI_conj h.isTI g
  have hHN : H ≤ Subgroup.normalizer (eSub V H T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.eSub_le_H).mp h.eSub_subgroupOf_normal
  have hUN : U ≤ Subgroup.normalizer (eSub V H T : Set G) := hUH.trans hHN
  have hEU : eSub V H T ⊓ U = ⊥ := h.eSub_inf_eq_bot_of_inf_centralizer_eq_bot hUE
  have h81 := eight_one hTI le_rfl hUN hEU hu hu1
  have hu2 : u * u = 1 := hUel.mul_self_eq_one hu
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hw : u⁻¹ * z * u ∈ eSub V H T := (Subgroup.mem_normalizer_iff''.mp (hUN hu) z).mp hz
  have hyE : z * (u⁻¹ * z * u) ∈ eSub V H T := (eSub V H T).mul_mem hz hw
  have hcomm : z * (u⁻¹ * z * u) = (u⁻¹ * z * u) * z := h.isElemAbelian_eSub.comm hz hw
  have hyc : z * (u⁻¹ * z * u) ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    rw [hinv] at hcomm ⊢
    calc v * (z * (v * z * v)) = v * ((v * z * v) * z) := by rw [hcomm]
      _ = (v * v) * z * v * z := by group
      _ = z * v * z := by rw [hu2, one_mul]
      _ = z * v * z * (v * v) := by rw [hu2, mul_one]
      _ = (z * (v * z * v)) * v := by group
  have hy : z * (u⁻¹ * z * u) ∈ eSub V H T ⊓ Subgroup.centralizer (U : Set G) := by
    rw [h81]
    exact Subgroup.mem_inf.mpr ⟨hyE, hyc⟩
  have hu'y : u' * (z * (u⁻¹ * z * u)) = (z * (u⁻¹ * z * u)) * u' :=
    Subgroup.mem_centralizer_iff.mp hy.2 u' hu'
  calc z * (u⁻¹ * z * u) = u'⁻¹ * (u' * (z * (u⁻¹ * z * u))) := by group
    _ = u'⁻¹ * ((z * (u⁻¹ * z * u)) * u') := by rw [hu'y]
    _ = (u'⁻¹ * z * u') * ((u * u')⁻¹ * z * (u * u')) := by group

end Hyp83

end CFSG.LocalAnalysis.WeakClosure81
