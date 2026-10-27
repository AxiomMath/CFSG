module

public import CFSG.Monster.GMS.S31Three

public section

namespace CFSG.Monster.GMS.S4Fusion

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Intrinsic

variable {G : Type*} [Group G]

theorem card_centralizer_subtype {t : G} (x : ↥(Subgroup.centralizer ({t} : Set G))) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥(Subgroup.centralizer ({t} : Set G)))) =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({(x : G)} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨((y : ↥(Subgroup.centralizer ({t} : Set G))) : G),
        Subgroup.mem_inf.mpr ⟨(y : ↥(Subgroup.centralizer ({t} : Set G))).2,
          Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.2))⟩⟩
      invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2))⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }

@[expose] def HasNormalTwoCommutator (t s : G) : Prop :=
  ∃ N : Subgroup G,
    N ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) ∧
      IsPGroup 2 N ∧
      (∀ h ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G),
        ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
      ∃ p ∈ N, ∃ q ∈ N, ⁅p, q⁆ = s

theorem HasNormalTwoCommutator.map {G' : Type*} [Group G'] {t : G} {t' : G'}
    (φ : ↥(Subgroup.centralizer ({t} : Set G)) ≃* ↥(Subgroup.centralizer ({t'} : Set G')))
    {s : ↥(Subgroup.centralizer ({t} : Set G))} (h : HasNormalTwoCommutator t (s : G)) :
    HasNormalTwoCommutator t' ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') := by
  obtain ⟨N, hNle, hNp, hNn, p, hp, q, hq, hpq⟩ := h
  let ψ : ↥(Subgroup.centralizer ({t} : Set G)) →* G' :=
    (Subgroup.centralizer ({t'} : Set G')).subtype.comp φ.toMonoidHom
  have hψ : ∀ x, ψ x = ((φ x : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') := fun x => rfl
  let N₀ : Subgroup ↥(Subgroup.centralizer ({t} : Set G)) :=
    N.subgroupOf (Subgroup.centralizer ({t} : Set G))
  have hN₀ : ∀ x : ↥(Subgroup.centralizer ({t} : Set G)), x ∈ N₀ ↔ (x : G) ∈ N := fun x => Iff.rfl
  have hcomm : ∀ x : ↥(Subgroup.centralizer ({t} : Set G)), x ∈ N₀ → x * s = s * x := by
    intro x hx
    have hx' : (x : G) ∈ Subgroup.centralizer ({(s : G)} : Set G) := (hNle hx).2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx')
  refine ⟨N₀.map ψ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(φ x).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := congrArg (fun y => ((φ y : ↥(Subgroup.centralizer ({t'} : Set G'))) : G'))
      (hcomm x hx)
    simp only [map_mul, Subgroup.coe_mul] at this
    exact this
  · exact (hNp.comap_subtype (K := Subgroup.centralizer ({t} : Set G))).map ψ
  · intro h' hh' n' hn'
    obtain ⟨x, hx, rfl⟩ := hn'
    obtain ⟨hh't, hh'c⟩ := Subgroup.mem_inf.mp hh'
    let k : ↥(Subgroup.centralizer ({t} : Set G)) := φ.symm ⟨h', hh't⟩
    have hkφ : φ k = ⟨h', hh't⟩ := φ.apply_symm_apply _
    have hkc : (k : G) ∈ Subgroup.centralizer ({(s : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (⟨h', hh't⟩ : ↥(Subgroup.centralizer ({t'} : Set G'))) * φ s =
          φ s * ⟨h', hh't⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hh'c)
      rw [← hkφ, ← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (φ.injective h1)
    have hkN : ((k * x * k⁻¹ : ↥(Subgroup.centralizer ({t} : Set G))) : G) ∈ N :=
      hNn k (Subgroup.mem_inf.mpr ⟨k.2, hkc⟩) x ((hN₀ x).mp hx)
    refine ⟨k * x * k⁻¹, (hN₀ _).mpr hkN, ?_⟩
    rw [hψ, hψ, map_mul, map_mul, map_inv, hkφ]
    rfl
  · refine ⟨ψ ⟨p, (hNle hp).1⟩, ⟨⟨p, (hNle hp).1⟩, (hN₀ _).mpr hp, rfl⟩,
      ψ ⟨q, (hNle hq).1⟩, ⟨⟨q, (hNle hq).1⟩, (hN₀ _).mpr hq, rfl⟩, ?_⟩
    rw [← map_commutatorElement, hψ]
    congr 2
    exact Subtype.ext hpq

end Intrinsic

section Classes

variable {G : Type} [Group G] {t z₀ b z u : G}

theorem tableVOrder_ne :
    tableVOrderB ≠ tableVOrderZ ∧ tableVOrderB ≠ tableVOrderU ∧ tableVOrderZ ≠ tableVOrderU := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tableVOrderB, tableVOrderZ, tableVOrderU]

theorem eq_of_forall_comm (h : TwoClasses t z₀ b z u) {x : G}
    (hx : x ∈ Subgroup.centralizer ({t} : Set G)) (hx2 : orderOf x = 2)
    (hcomm : ∀ y ∈ Subgroup.centralizer ({t} : Set G), y * x = x * y) : x = t := by
  by_contra hxt
  obtain ⟨g, hg, hcase⟩ := h.tableV.cover x hx hx2 hxt
  have hgx : g * x * g⁻¹ = x := by rw [hcomm g hg, mul_inv_cancel_right]
  have hinf : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    ext y
    simp only [Subgroup.mem_inf, and_iff_left_iff_imp]
    intro hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy)
  have hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) = twoBabyOrder := by
    rw [hinf]
    exact h.tableV.card_centralizer
  rw [hgx] at hcase
  rcases hcase with rfl | rfl | rfl | rfl
  · rw [h.tableV.card_b] at hcard
    norm_num [tableVOrderB, twoBabyOrder] at hcard
  · rw [h.tableV.card_z] at hcard
    norm_num [tableVOrderZ, twoBabyOrder] at hcard
  · rw [centralizer_inf_mul_eq, h.tableV.card_z] at hcard
    norm_num [tableVOrderZ, twoBabyOrder] at hcard
  · rw [h.tableV.card_u] at hcard
    norm_num [tableVOrderU, twoBabyOrder] at hcard

theorem fusion_cases (h : TwoClasses t z₀ b z u) {s : G}
    (hs : s ∈ Subgroup.centralizer ({t} : Set G)) (hs2 : orderOf s = 2) (hst : s ≠ t) :
    (IsConj t s ∧ Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({s} : Set G)) = tableVOrderB) ∨
      (¬ IsConj t s ∧ Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({s} : Set G)) = tableVOrderU) ∨
      (Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) =
        tableVOrderZ ∧ ((IsConj z₀ s ∧ IsConj t (t * s)) ∨ (IsConj t s ∧ IsConj z₀ (t * s)))) := by
  obtain ⟨g, hg, hcase⟩ := h.tableV.cover s hs hs2 hst
  have hcard := card_inf_centralizer_conj hg s
  have hconj : IsConj s (g * s * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf h.orderOf_a
  have hgts : g * (t * s) * g⁻¹ = t * (g * s * g⁻¹) := conj_mul_of_mem_centralizer hg s
  have hnot : IsConj z₀ s → ¬ IsConj t s := fun hz hts => h.not_isConj (hts.trans hz.symm)
  rcases hcase with e | e | e | e
  · left
    rw [e] at hconj hcard
    exact ⟨h.isConj_b.trans hconj.symm, by rw [← hcard]; exact h.tableV.card_b⟩
  · right; right
    rw [e] at hconj hcard hgts
    refine ⟨by rw [← hcard]; exact h.tableV.card_z, Or.inl ⟨h.isConj_z.trans hconj.symm, ?_⟩⟩
    exact h.isConj_az.trans (isConj_iff.mpr ⟨g, hgts⟩).symm
  · right; right
    rw [e] at hconj hcard hgts
    refine ⟨by rw [← hcard, centralizer_inf_mul_eq]; exact h.tableV.card_z,
      Or.inr ⟨h.isConj_az.trans hconj.symm, ?_⟩⟩
    have : g * (t * s) * g⁻¹ = z := by rw [hgts, ← mul_assoc, htt, one_mul]
    exact h.isConj_z.trans (isConj_iff.mpr ⟨g, this⟩).symm
  · right; left
    rw [e] at hconj hcard
    have hz : IsConj z₀ s := h.isConj_u.trans hconj.symm
    exact ⟨hnot hz, by rw [← hcard]; exact h.tableV.card_u⟩

end Classes

end CFSG.Monster.GMS.S4Fusion
