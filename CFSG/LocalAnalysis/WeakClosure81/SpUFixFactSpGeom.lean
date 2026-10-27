module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactDefs
public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRoot
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpPerp
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRootEq
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpAut
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactCore
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {k : ℕ} {F : Type} [Field F]

private theorem spUFixSp_spEnd_injective (x : ↥(StatedSp k F)) : Function.Injective (spEnd x) := by
  intro u v h
  have h1 := congrArg (spEnd x⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
    Module.End.one_apply, Module.End.one_apply] at h1

noncomputable def spUFixGeomSp [Finite F] [CharP F 2] (hk : 2 ≤ k) {a : Fin k ⊕ Fin k → F}
    (ha : a ≠ 0) : SpUFixGeom ↥(StatedSp k F) (spUFixRootSp a) F (Fin k ⊕ Fin k → F) where
  τ := RingEquiv.refl F
  β u v := spForm k F u v
  β_add_left u u' v := by simp only [map_add, LinearMap.add_apply]
  β_smul_left c u v := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; rfl
  β_add_right u v v' := map_add _ v v'
  β_smul_right c u v := by simp only [map_smul, smul_eq_mul]
  X := spUFixRootSp
  X_smul c v hc _ := spUFixRootSp_smul hc v
  X_inj _ _ hv hw _ _ h := exists_smul_of_spUFixRootSp_eq hv hw h
  X_invol _ _ _ hx := mul_self_of_mem_spUFixRootSp hx
  X_comm _ _ _ _ hvw _ hx _ hy := commute_of_mem_spUFixRootSp hvw hx hy
  X_order_three _ _ _ _ _ _ hvw := exists_mul_pow_three_spUFixRootSp hvw
  conj x := ⟨spEnd x, spUFixSp_spEnd_injective x,
    fun v w => CFSG.RankThree.PartOne.CTP.spEnd_isometry x v w,
    fun v _ => map_conj_spUFixRootSp x v, fun hx => ⟨1, fun v => by
      rw [one_smul, ← Module.End.mul_apply, ← spEnd_mul, hx, spEnd_one, Module.End.one_apply]⟩⟩
  a := a
  a_ne := ha
  a_iso := spForm_isAlt a
  R_eq := rfl
  trans _ hv _ := exists_spUFixRootSp_eq_map ha hv
  second := by
    obtain ⟨v, hv, hva⟩ := spUFix_exists_spForm_eq_zero_not_smul hk ha
    exact ⟨v, spForm_isAlt v, hv, hva⟩
  aut α _ hαR hout := by
    obtain ⟨σ, ψ, hσ, hψ, hψi, hψβ, hψX⟩ := spUFix_exists_semilinear_statedSp hk ha α hαR hout
    exact ⟨σ, ψ, hσ, hψ, hψi, hψβ, fun v _ => hψX v⟩

theorem spUFixConclusion_statedSp [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 2 ≤ k)
    (R : Subgroup ↥(StatedSp k F)) (hR : Nat.card R = 2 ^ n)
    (hRt : ∀ x ∈ R, x ≠ 1 → IsSymplecticTransvectionIn k x) {Sy : Subgroup ↥(StatedSp k F)}
    (hSy : ∃ P : Sylow 2 ↥(StatedSp k F), (P : Subgroup ↥(StatedSp k F)) = Sy) (hRSy : R ≤ Sy)
    (hSyR : Sy ≤ Subgroup.normalizer (R : Set ↥(StatedSp k F))) :
    SpUFixConclusion ↥(StatedSp k F) R Sy := by
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hF
  obtain ⟨a, ha, rfl⟩ := exists_eq_spUFixRootSp hF R hR hRt
  exact (spUFixGeomSp hk ha).spUFixConclusion hSy hRSy hSyR

end CFSG.LocalAnalysis.WeakClosure81

end
