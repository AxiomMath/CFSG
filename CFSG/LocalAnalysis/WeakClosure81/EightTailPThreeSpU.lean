module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUStep0
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUExists
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUFix
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUFrattini
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

section RootData

variable {S : Type} [Group S] {ψ : ↥(kGenIn V H) →* S} {ρ : ↥H →* MulAut S}
  {R Sy : Subgroup S} {e : ℕ}

theorem rootData_card_U (D : RootData V H T S ψ ρ R Sy e) {U : Subgroup G}
    (hU : ∃ g : G, U = conjSubgroup V g) : (Nat.card R) ^ e < Nat.card U := by
  obtain ⟨g, rfl⟩ := hU
  rw [E3.card_conjSubgroup]
  exact D.card_V

end RootData

private theorem w85g_map_rho_barSub {S : Type} [Group S] {ψ : ↥(kGenIn V H) →* S}
    {ρ : ↥H →* MulAut S} {R Sy : Subgroup S} {e : ℕ}
    (D : RootData V H T S ψ ρ R Sy e) (h : ↥H) (A : Subgroup G) :
    Subgroup.map (ρ h).toMonoidHom (barSub (kGenIn V H) ψ A) =
      barSub (kGenIn V H) ψ (conjSubgroup A (h : G)⁻¹) := by
  have hhn : (h : G) ∈ Subgroup.normalizer (kGenIn V H : Set G) :=
    D.hyp.le_normalizer_kGenIn_of_eq_sup D.eq_sup h.2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hkA, rfl⟩ := mem_barSub.mp hx
    have hconjK : (h : G) * (k : G) * (h : G)⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp hhn k).1 k.2
    have hconjA : (h : G) * (k : G) * (h : G)⁻¹ ∈ conjSubgroup A (h : G)⁻¹ :=
      mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hkA)
    exact mem_barSub.mpr ⟨⟨(h : G) * (k : G) * (h : G)⁻¹, hconjK⟩, hconjA,
      (D.act h k ⟨_, hconjK⟩ rfl).symm⟩
  · rintro ⟨k, hk, rfl⟩
    have hkA : (h : G)⁻¹ * (k : G) * (h : G) ∈ A := by
      simpa using mem_conjSubgroup_iff.mp hk
    have hhn' : (h : G)⁻¹ ∈ Subgroup.normalizer (kGenIn V H : Set G) :=
      (Subgroup.normalizer (kGenIn V H : Set G)).inv_mem hhn
    have haK : (h : G)⁻¹ * (k : G) * (h : G) ∈ kGenIn V H := by
      simpa using (Subgroup.mem_normalizer_iff.mp hhn' k).1 k.2
    refine ⟨ψ ⟨(h : G)⁻¹ * (k : G) * (h : G), haK⟩,
      mem_barSub.mpr ⟨⟨_, haK⟩, hkA, rfl⟩, ?_⟩
    have hx : (k : G) = (h : G) * ((h : G)⁻¹ * (k : G) * (h : G)) * (h : G)⁻¹ := by
      group
    exact D.act h ⟨_, haK⟩ k hx

private theorem w85g_isSpGp_quot_of_kBarCenterShape (d : ShapeData V H T φ) {m n : ℕ}
    (h : KBarCenterShape V H T (fun Y _ => IsSpGp Y m n)) :
    IsSpGp (X ⧸ Subgroup.center X) m n := by
  obtain ⟨Y, _, hY, ⟨e⟩⟩ := nonempty_mulEquiv_of_kBarCenterShape d.hyp83 d.eq_sup h d.bar
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨eY⟩⟩ := hY
  exact ⟨k, hk, F, hFld, hFin, hFcard, ⟨e.trans eY⟩⟩

private theorem w85g_isPSUGp_quot_of_kBarCenterShape (d : ShapeData V H T φ) {m n : ℕ}
    (h : KBarCenterShape V H T (fun Y _ => IsPSUGp Y m n)) :
    IsPSUGp (X ⧸ Subgroup.center X) m n := by
  obtain ⟨Y, _, hY, ⟨e⟩⟩ := nonempty_mulEquiv_of_kBarCenterShape d.hyp83 d.eq_sup h d.bar
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hY

section CertifiedThree


theorem threeFirst_spu (hLie : SpPSULieFacts) (hRU : UnitaryRootCommutatorRank)
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (g4 : W3Lem85TwoGap4) (g6 : W3Lem85TwoGap6) :
    ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
      IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
      ((∃ m n : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∧
          rankBarV V H T = n) ∨
        (∃ m n : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsPSUGp X m n) ∧
          rankBarV V H T = n)) →
        H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
  intro V H T hV hH hH0 hT hKT hyp
  obtain ⟨X, _, _, φ, d, halt⟩ := exists_shapeData h711 hV hH hH0 hT hKT
  haveI : Finite X := d.finite
  have finish : ∀ {m n : ℕ}, 4 ≤ m →
      ((IsSpGp (X ⧸ Subgroup.center X) m n ∧
          IsSymplecticRootGroup X m n (barSub (kGenIn V H) φ V)) ∨
        (IsPSUGp (X ⧸ Subgroup.center X) m n ∧
          IsUnitaryRootGroup X m n (barSub (kGenIn V H) φ V))) →
      H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
    intro m n hm4 hroot
    obtain ⟨S, hSgrp, hSfin, ψ, ρ, R, Sy, e, D⟩ := exists_rootData hLie hRU d hm4 hroot
    letI := hSgrp
    haveI := hSfin
    obtain ⟨X₂, Pα, hP⟩ := D.lie.parabolic
    refine rootData_frattini D hP ?_
    intro U hU hUT u hu huH
    have hUH : U ≤ H := hUT.trans D.hyp.T_le_H
    let inc : ↥U →* ↥H := Subgroup.inclusion hUH
    let α : ↥U →* MulAut S := ρ.comp inc
    have hα : ∀ u : ↥U, α u = ρ ⟨(u : G), hUH u.2⟩ := fun _ => rfl
    have hexp : ∀ u : ↥U, u * u = 1 := by
      intro u
      obtain ⟨g, rfl⟩ := hU
      have hu2 : ((u : G)) ^ 2 = 1 :=
        (isElemAbelian_conjSubgroup' D.hyp.elemAbelian g).2 (u : G) u.2
      apply Subtype.ext
      simpa [pow_two] using hu2
    have hSy : ∀ u : ↥U, Subgroup.map (α u).toMonoidHom Sy = Sy := by
      intro u
      rw [hα u, ← D.sylow, w85g_map_rho_barSub D ⟨(u : G), hUH u.2⟩ T]
      rw [show conjSubgroup T ((⟨(u : G), hUH u.2⟩ : ↥H) : G)⁻¹ = T from
        conjSubgroup_eq_iff_mem_normalizer.mpr
          ((Subgroup.normalizer (T : Set G)).inv_mem (Subgroup.le_normalizer (hUT u.2)))]
    have hR : ∀ u : ↥U, Subgroup.map (α u).toMonoidHom R = R := by
      intro u
      rw [hα u, ← D.root, w85g_map_rho_barSub D ⟨(u : G), hUH u.2⟩ V]
      rw [show conjSubgroup V ((⟨(u : G), hUH u.2⟩ : ↥H) : G)⁻¹ = V from
        conjSubgroup_eq_iff_mem_normalizer.mpr
          ((Subgroup.normalizer (V : Set G)).inv_mem (D.hyp.T_le_normalizer (hUT u.2)))]
    have hcard : (Nat.card R) ^ e < Nat.card ↥U := rootData_card_U D hU
    have hstar : ∀ u : ↥U, u ≠ 1 → ∀ X ∈ rootGroupsIn R Sy,
        Subgroup.map (α u).toMonoidHom X = X → ∀ u' : ↥U,
        Subgroup.map (α u').toMonoidHom X = X := by
      intro u hu1 X hX hfix u'
      rw [hα u] at hfix
      rw [hα u']
      exact rootData_fix_const D hU hUT u.2 (hUH u.2) (fun h => hu1 (Subtype.ext h)) hX hfix
        (u' : G) u'.2 (hUH u'.2)
    obtain ⟨g, hg, hgα⟩ :=
      steps_four_five D.lie hP D.sylow_normalizes.1 α hexp hSy hR hcard hstar ⟨u, hu⟩
    refine ⟨g, hg, ?_⟩
    have hAB : (⟨u, hUH hu⟩ : ↥H) = ⟨u, huH⟩ := Subtype.ext rfl
    calc ρ ⟨u, huH⟩ = ρ ⟨u, hUH hu⟩ := (congrArg ρ hAB).symm
      _ = α ⟨u, hu⟩ := (hα ⟨u, hu⟩).symm
      _ = MulAut.conj g := hgα
  rcases hyp with ⟨m, n, hm, hshape, hr⟩ | ⟨m, n, hm, hshape, hr⟩
  · have hm4 : 4 ≤ m := by
      obtain ⟨k, hk, -⟩ := w85g_isSpGp_quot_of_kBarCenterShape d hshape
      omega
    exact finish hm4 (step0_root g4 g6 d halt hm hr
      (Or.inl (w85g_isSpGp_quot_of_kBarCenterShape d hshape)))
  · have hm4 : 4 ≤ m := by omega
    exact finish hm4 (step0_root g4 g6 d halt hm hr
      (Or.inr (w85g_isPSUGp_quot_of_kBarCenterShape d hshape)))

end CertifiedThree

end CFSG.LocalAnalysis.WeakClosure81

end
