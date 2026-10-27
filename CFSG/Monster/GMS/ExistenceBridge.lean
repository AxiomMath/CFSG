module

public import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.GMS

open CFSG CFSG.Blueprint.NativeSporadic CFSG.Monster.Existence

variable {G : Type} [Group G]

theorem GMSLeechCentralizer.of_isTwoBCentralizer {z : G} (hz : orderOf z = 2)
    (h : IsTwoBCentralizer z) : GMSLeechCentralizer z := by
  obtain ⟨hQ, hcard, hcen, ⟨e⟩, -, -⟩ := h
  refine ⟨hz, hQ, hcard,
    ⟨(MonoidHom.ofClass e).comp (QuotientGroup.mk' _), ?_, ?_⟩, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨c, rfl⟩
  · ext c
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · intro c hc
    have hcG : (c : G) ∈ Subgroup.centralizer
        (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hc q hq
      simpa using congrArg Subtype.val this
    obtain ⟨q, hq, hqc⟩ := Subgroup.mem_map.mp (hcen hcG)
    rw [show c = q from Subtype.ext hqc.symm]
    exact hq

theorem GMSDoubleF2Centralizer.of_isTwoACentralizer {a : G} (ha : orderOf a = 2)
    (hB : IsSimpleGroup B) {d₀ : B} (hd₀ : orderOf d₀ = 2) (h : IsTwoACentralizer a) :
    GMSDoubleF2Centralizer d₀ a := by
  obtain ⟨hperf, hcenter, ⟨e⟩⟩ := h
  refine ⟨ha, Group.isPerfect_def.mp hperf, B, inferInstance,
    (MonoidHom.ofClass e).comp (QuotientGroup.mk' _), ?_, ?_, hB, d₀, hd₀, ⟨MulEquiv.refl _⟩⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨c, rfl⟩
  have hker : ((MonoidHom.ofClass e).comp (QuotientGroup.mk' (Subgroup.center
      (Subgroup.centralizer ({a} : Set G))))).ker =
        Subgroup.center (Subgroup.centralizer ({a} : Set G)) := by
    ext c
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hker]
  exact hcenter

theorem gmsF1Type_of_monsterExistenceStatement {X : Type} [Group X]
    (hX : MonsterExistenceStatement X) (hB : IsSimpleGroup B) {d₀ : B} (hd₀ : orderOf d₀ = 2) :
    ∃ a₀ z₀ : X, GMSF1Type d₀ a₀ z₀ ∧ ∀ t : X, orderOf t = 2 → IsConj a₀ t ∨ IsConj z₀ t := by
  obtain ⟨-, a₀, z₀, ha₀, hz₀, -, hcl, hA, hZ, -⟩ := hX
  exact ⟨a₀, z₀, ⟨GMSDoubleF2Centralizer.of_isTwoACentralizer ha₀ hB hd₀ (hA a₀ (IsConj.refl _)),
    GMSLeechCentralizer.of_isTwoBCentralizer hz₀ (hZ z₀ (IsConj.refl _))⟩, hcl⟩

theorem nonempty_mulEquiv_of_isTwoBCentralizer
    [Finite G] {X : Type} [Group X] {a₀ z₀ : X}
    (hz₀ : orderOf z₀ = 2) (hZ : IsTwoBCentralizer z₀)
    (hcl : ∀ t : X, orderOf t = 2 → IsConj a₀ t ∨ IsConj z₀ t)
    {d₀ : B} {a z : G} (hG : GMSF1Type d₀ a z)
    (H : Subgroup G) (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (e : H ≃* X)
    (hea : IsConj a₀ (e ⟨a, haH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩)) :
    Nonempty (G ≃* X) := by
  refine nonempty_mulEquiv_of_centralizer_le hG (GMSLeechCentralizer.of_isTwoBCentralizer hz₀ hZ)
    (fun t ht => ?_) H haH e rfl
  rcases hcl t ht with h | h
  · exact Or.inl (hea.symm.trans h)
  · exact Or.inr h

theorem nonempty_mulEquiv_of_monsterExistenceStatement
    [Finite G] {X : Type} [Group X]
    (hX : MonsterExistenceStatement X) {d₀ : B} {a z : G} (hG : GMSF1Type d₀ a z)
    (H : Subgroup G) (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (e : H ≃* X)
    (hea : ∀ z₀ : X, IsTwoBCentralizer z₀ →
      ¬ IsConj z₀ (e ⟨a, haH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩)) :
    Nonempty (G ≃* X) := by
  obtain ⟨-, a₀, z₀, -, hz₀, -, hcl, -, hZ, -⟩ := hX
  have ha2 : orderOf (e ⟨a, haH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hG.1.1
  refine nonempty_mulEquiv_of_isTwoBCentralizer hz₀ (hZ z₀ (IsConj.refl _)) hcl hG H haH e ?_
  rcases hcl _ ha2 with h | h
  · exact h
  · exact absurd h (hea z₀ (hZ z₀ (IsConj.refl _)))

end CFSG.Monster.GMS
