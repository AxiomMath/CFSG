module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22xa_omegaZJ_le_centralizer_of_not_strict {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hU : IsElemAbelian 2 U) (A : Subgroup ↥T)
    (hA : A ∈ CFSG.elemThompsonFamily ↥T 2)
    (hoff : (centralizer (U : Set G)).relIndex (A.map T.subtype) ≤
      (centralizer ((A.map T.subtype : Subgroup G) : Set G)).relIndex U) :
    omegaZJ22 T ≤ centralizer (U : Set G) := by
  classical
  have _ := hT
  have hmax : CFSG.Quasithin.IsMaxElemAbelian T (A.map T.subtype) := by
    rw [CFSG.Quasithin.BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily,
      CFSG.Quasithin.BlueprintB2.subgroupOf_map_subtype_self]
    exact ⟨CFSG.Quasithin.BlueprintB2.map_subtype_le_self A, hA⟩
  generalize A.map T.subtype = A' at hmax hoff
  obtain ⟨hA'T, hA'el, hA'max⟩ := hmax
  have hext : ∀ X : Subgroup G, A' ≤ X → X ≤ T → IsElemAbelian 2 X → X = A' := fun X hAX hXT hXel =>
    (Subgroup.eq_of_le_of_card_ge hAX (hA'max X hXT hXel)).symm
  have hUc : U ≤ centralizer (U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun v hv => hU.comm hv hu
  have hCUle : centralizer (A' : Set G) ⊓ U ≤ A' := by
    have hX := hext (A' ⊔ (centralizer (A' : Set G) ⊓ U)) le_sup_left
      (sup_le hA'T (inf_le_right.trans hUT))
      (hA'el.sup_of_commute (hU.mono inf_le_right) fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 hb.1 a ha)
    exact le_sup_right.trans hX.le
  have hA₁U : ∀ a ∈ centralizer (U : Set G) ⊓ A', ∀ u ∈ U, a * u = u * a := fun a ha u hu =>
    (Subgroup.mem_centralizer_iff.1 ha.1 u hu).symm
  have hX₂el : IsElemAbelian 2 (centralizer (U : Set G) ⊓ A' ⊔ U) :=
    (hA'el.mono inf_le_right).sup_of_commute hU hA₁U
  have hX₂T : centralizer (U : Set G) ⊓ A' ⊔ U ≤ T := sup_le (inf_le_right.trans hA'T) hUT
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (centralizer (U : Set G) ⊓ A') U hA₁U
  have hinf : (centralizer (U : Set G) ⊓ A') ⊓ U = centralizer (A' : Set G) ⊓ U := by
    ext x
    constructor
    · rintro ⟨⟨_, hxA⟩, hxU⟩
      exact ⟨Subgroup.mem_centralizer_iff.2 fun h hh => hA'el.comm hh hxA, hxU⟩
    · rintro ⟨hxc, hxU⟩
      exact ⟨⟨hUc hxU, hCUle ⟨hxc, hxU⟩⟩, hxU⟩
  rw [hinf] at hprod
  have h1 := Subgroup.relIndex_mul_card (H := centralizer (U : Set G)) (K := A')
  have h2 := Subgroup.relIndex_mul_card (H := centralizer (A' : Set G)) (K := U)
  have hc_pos : 0 < Nat.card ↥(centralizer (A' : Set G) ⊓ U) := Nat.card_pos
  have hge : Nat.card A' ≤ Nat.card ↥(centralizer (U : Set G) ⊓ A' ⊔ U) := by
    refine Nat.le_of_mul_le_mul_right ?_ hc_pos
    calc Nat.card A' * Nat.card ↥(centralizer (A' : Set G) ⊓ U)
        = (centralizer (U : Set G)).relIndex A' * Nat.card ↥(centralizer (U : Set G) ⊓ A') *
            Nat.card ↥(centralizer (A' : Set G) ⊓ U) := by rw [h1]
      _ ≤ (centralizer (A' : Set G)).relIndex U * Nat.card ↥(centralizer (U : Set G) ⊓ A') *
            Nat.card ↥(centralizer (A' : Set G) ⊓ U) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hoff)
      _ = Nat.card ↥(centralizer (U : Set G) ⊓ A') *
            ((centralizer (A' : Set G)).relIndex U * Nat.card ↥(centralizer (A' : Set G) ⊓ U)) := by
          ring
      _ = Nat.card ↥(centralizer (U : Set G) ⊓ A') * Nat.card U := by rw [h2]
      _ = Nat.card ↥(centralizer (U : Set G) ⊓ A' ⊔ U) *
            Nat.card ↥(centralizer (A' : Set G) ⊓ U) := hprod.symm
  have hmaxX₂ : CFSG.Quasithin.IsMaxElemAbelian T (centralizer (U : Set G) ⊓ A' ⊔ U) :=
    ⟨hX₂T, hX₂el, fun B hB hBel => (hA'max B hB hBel).trans hge⟩
  intro z hz
  obtain ⟨hzT, hzc, hz2⟩ := uc22p22e_mem_omegaZJ'.1 hz
  have hX₂J : centralizer (U : Set G) ⊓ A' ⊔ U ≤ jOf T := by
    rw [show jOf T = CFSG.Quasithin.thompsonJ T from
      CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ T]
    exact le_iSup₂_of_le _ hmaxX₂ le_rfl
  have hzcent : z ∈ centralizer ((centralizer (U : Set G) ⊓ A' ⊔ U : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun j hj => hzc j (hX₂J hj)
  have hcomm : ∀ a ∈ centralizer (U : Set G) ⊓ A' ⊔ U, ∀ b ∈ Subgroup.zpowers z, a * b = b * a :=
    fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 ((Subgroup.zpowers_le.2 hzcent) hb) a ha
  have hX₃el : IsElemAbelian 2 ((centralizer (U : Set G) ⊓ A' ⊔ U) ⊔ Subgroup.zpowers z) :=
    hX₂el.sup_of_commute (isElemAbelian_zpowers hz2) hcomm
  have hX₃T : (centralizer (U : Set G) ⊓ A' ⊔ U) ⊔ Subgroup.zpowers z ≤ T :=
    sup_le hX₂T (Subgroup.zpowers_le.2 hzT)
  have heq : (centralizer (U : Set G) ⊓ A' ⊔ U) ⊔ Subgroup.zpowers z =
      centralizer (U : Set G) ⊓ A' ⊔ U :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left ((hA'max _ hX₃T hX₃el).trans hge)).symm
  have hzX : z ∈ centralizer (U : Set G) ⊓ A' ⊔ U := by
    have h3 : z ∈ (centralizer (U : Set G) ⊓ A' ⊔ U) ⊔ Subgroup.zpowers z :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    rwa [heq] at h3
  exact (sup_le inf_le_left hUc) hzX

end CFSG.LocalAnalysis.UniquenessCase.UC22
