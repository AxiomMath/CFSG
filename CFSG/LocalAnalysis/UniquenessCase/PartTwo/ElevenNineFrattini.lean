module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

private theorem le_normalizer_centralizer {A V : Subgroup G}
    (h : A ≤ normalizer (V : Set G)) :
    A ≤ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_set_normalizer_iff] at h ⊢
  intro a ha v hv
  change ∀ w ∈ (V : Set G), w * v = v * w at hv
  change ∀ w ∈ (V : Set G), w * (a * v * a⁻¹) = (a * v * a⁻¹) * w
  intro w hw
  have haw : a⁻¹ * w * a ∈ V := by
    simpa using h a⁻¹ (A.inv_mem ha) w hw
  have hv' : (a⁻¹ * w * a) * v = v * (a⁻¹ * w * a) := hv _ haw
  calc w * (a * v * a⁻¹) = a * ((a⁻¹ * w * a) * v) * a⁻¹ := by group
    _ = a * (v * (a⁻¹ * w * a)) * a⁻¹ := by rw [hv']
    _ = (a * v * a⁻¹) * w := by group

private theorem map_conj_mul (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  refine congrArg (fun f : G →* G => H.map f) ?_
  ext x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  group

private theorem exists_conj_map_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {P Q H : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P H)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    ∃ g ∈ H, P.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨P', hP'⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨Q', hQ'⟩ := hQ.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) P' Q'
  have hsub : (P' : Subgroup ↥H).map (MulAut.conj g).toMonoidHom = (Q' : Subgroup ↥H) := by
    have h := congrArg (fun S : Sylow p ↥H => (S : Subgroup ↥H)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    convert h using 2
    ext x
    rfl
  have hleft : ((P' : Subgroup ↥H).map (MulAut.conj g).toMonoidHom).map H.subtype =
      P.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hP', Subgroup.map_subgroupOf_eq_of_le hP.le]
  refine ⟨(g : G), g.2, ?_⟩
  calc P.map (MulAut.conj (g : G)).toMonoidHom
      = ((P' : Subgroup ↥H).map (MulAut.conj g).toMonoidHom).map H.subtype := hleft.symm
    _ = (Q' : Subgroup ↥H).map H.subtype := by rw [hsub]
    _ = Q := by rw [hQ', Subgroup.map_subgroupOf_eq_of_le hQ.le]

theorem le_centralizer_sup_normalizer_of_sylow {M T Y V₀ : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hYM : Y ≤ M)
    (hYn : M ≤ normalizer (Y : Set G)) (hV₀n : M ≤ normalizer (V₀ : Set G)) :
    Y ≤ (Y ⊓ centralizer (V₀ : Set G)) ⊔
      (Y ⊓ normalizer ((T ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup G := centralizer (V₀ : Set G)
  let Q : Subgroup G := T ⊓ Z
  let W : Subgroup G := Y ⊓ Z
  let C : Subgroup G := M ⊓ Z
  let H : Subgroup G := W ⊔ Q
  change Y ≤ W ⊔ (Y ⊓ normalizer (Q : Set G))
  have hMZ : M ≤ normalizer (Z : Set G) := le_normalizer_centralizer hV₀n
  have hMC : M ≤ normalizer (C : Set G) := by
    change M ≤ normalizer ((M ⊓ Z : Subgroup G) : Set G)
    exact (le_inf (Subgroup.le_normalizer : M ≤ normalizer (M : Set G)) hMZ).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hMW : M ≤ normalizer (W : Set G) := by
    change M ≤ normalizer ((Y ⊓ Z : Subgroup G) : Set G)
    exact (le_inf hYn hMZ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hWC : W ≤ C := by
    intro w hw
    exact ⟨hYM hw.1, hw.2⟩
  have hQC : Q ≤ C := by
    intro q hq
    exact ⟨hT.le hq.1, hq.2⟩
  have hHC : H ≤ C := sup_le hWC hQC
  have hQeqC : T ⊓ C = Q := by
    change T ⊓ (M ⊓ Z) = T ⊓ Z
    rw [← inf_assoc, inf_eq_left.mpr hT.le]
  have hQC' : CFSG.ABGLocalTools.IsSylowOf 2 Q C := by
    have h := hT.inf_of_le_normalizer (N := C) inf_le_left hMC
    rwa [hQeqC] at h
  have hQH : CFSG.ABGLocalTools.IsSylowOf 2 Q H := hQC'.of_le le_sup_right hHC
  intro y hyY
  have hyM : y ∈ M := hYM hyY
  have hQyH_le : Q.map (MulAut.conj y).toMonoidHom ≤ H := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hqM : q ∈ M := hT.le hq.1
    have hcY : y * q * y⁻¹ * q⁻¹ ∈ Y := by
      have hqy : q * y⁻¹ * q⁻¹ ∈ Y :=
        (Subgroup.le_set_normalizer_iff.mp hYn) q hqM y⁻¹ (Y.inv_mem hyY)
      simpa only [mul_assoc] using Y.mul_mem hyY hqy
    have hcZ : y * q * y⁻¹ * q⁻¹ ∈ Z := by
      have hyq : y * q * y⁻¹ ∈ C :=
        (Subgroup.le_set_normalizer_iff.mp hMC) y hyM q (hQC'.le hq)
      exact Z.mul_mem hyq.2 (Z.inv_mem hq.2)
    have hcW : y * q * y⁻¹ * q⁻¹ ∈ W := ⟨hcY, hcZ⟩
    have hyq_eq : y * q * y⁻¹ = (y * q * y⁻¹ * q⁻¹) * q := by group
    change y * q * y⁻¹ ∈ W ⊔ Q
    rw [hyq_eq]
    exact (W ⊔ Q).mul_mem ((le_sup_left : W ≤ W ⊔ Q) hcW)
      ((le_sup_right : Q ≤ W ⊔ Q) hq)
  have hQyC : CFSG.ABGLocalTools.IsSylowOf 2 (Q.map (MulAut.conj y).toMonoidHom) C := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (hQyH_le.trans hHC) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hQC'.card_eq]
  have hQyH : CFSG.ABGLocalTools.IsSylowOf 2 (Q.map (MulAut.conj y).toMonoidHom) H :=
    hQyC.of_le hQyH_le hHC
  obtain ⟨g, hgH, hgmap⟩ := exists_conj_map_eq_of_isSylowOf (p := 2) hQH hQyH
  have hQNW : Q ≤ normalizer (W : Set G) := fun q hq => hMW (hT.le hq.1)
  have hgWQ : g ∈ (W : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left W Q hQNW]
    exact hgH
  obtain ⟨w, hwW, q, hqQ, hwq⟩ := Set.mem_mul.mp hgWQ
  have hqmap : Q.map (MulAut.conj q).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hqQ)
  have hgw : Q.map (MulAut.conj g).toMonoidHom = Q.map (MulAut.conj w).toMonoidHom := by
    rw [← hwq, ← map_conj_mul Q q w, hqmap]
  have hwy : Q.map (MulAut.conj w).toMonoidHom = Q.map (MulAut.conj y).toMonoidHom :=
    hgw.symm.trans hgmap
  have hww : (Q.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom = Q := by
    rw [map_conj_mul Q w w⁻¹, inv_mul_cancel, map_one]
    exact Subgroup.map_id Q
  have hn : w⁻¹ * y ∈ normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Q.map (MulAut.conj (w⁻¹ * y)).toMonoidHom = Q
    rw [← map_conj_mul Q y w⁻¹, ← hwy]
    exact hww
  have hyW : w⁻¹ * y ∈ Y ⊓ normalizer (Q : Set G) :=
    ⟨Y.mul_mem (Y.inv_mem hwW.1) hyY, hn⟩
  have hy_eq : y = w * (w⁻¹ * y) := by group
  rw [hy_eq]
  exact (W ⊔ (Y ⊓ normalizer (Q : Set G))).mul_mem
    ((le_sup_left : W ≤ W ⊔ (Y ⊓ normalizer (Q : Set G))) hwW)
    ((le_sup_right : Y ⊓ normalizer (Q : Set G) ≤
      W ⊔ (Y ⊓ normalizer (Q : Set G))) hyW)

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
