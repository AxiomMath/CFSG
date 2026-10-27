module

public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedNoncentralSolvable
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.Monster.B.E6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std

theorem card_K : Nat.card K = (2 ^ 1) ^ TwistTag.E6.order := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem barHom_eq_pow (c : K) : barHom c = c ^ (2 ^ 1) := by
  rw [barHom_apply]
  show c ^ 2 = c ^ (2 ^ 1)
  norm_num

theorem barHom_bijective : Function.Bijective barHom :=
  (Finite.injective_iff_bijective).1 barHom.injective

@[expose] noncomputable def barEquiv : K ≃+* K := RingEquiv.ofBijective barHom barHom_bijective

theorem barEquiv_toRingHom : (barEquiv : K ≃+* K).toRingHom = barHom := RingHom.ext fun _ => rfl

theorem standard_twisted_e6_group_simple :
    Finite stdGroup ∧ (∃ x y : stdGroup, x * y ≠ y * x) ∧ IsSimpleGroup stdGroup := by
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two le_rfl K card_K barHom
    barHom_eq_pow
  obtain ⟨hcomm, ⟨x, hx, y, hy, hxy⟩, -⟩ := hperf
  have hfin : Finite stdGroup := inferInstance
  have hnc : ∃ a b : stdGroup, a * b ≠ b * a :=
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hperf' : Group.IsPerfect stdGroup := Subgroup.isPerfect_iff.2 hcomm
  have hZ : Subgroup.center stdGroup = ⊥ := by
    have h := exceptional_fixed_center_trivial TwistTag.E6 K barEquiv
    rw [barEquiv_toRingHom] at h
    exact h
  have : Nontrivial stdGroup := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  refine ⟨hfin, hnc, IsSimpleGroup.mk fun M hM => ?_⟩
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center stdGroup := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv : Group.IsSolvable (stdGroup ⧸ M) := by
      have h := fixed_noncentral_normal_solvable_quotient TwistTag.E6 K barEquiv
      rw [barEquiv_toRingHom] at h
      exact @h M hM hnot
    by_contra htop
    have : Nontrivial (stdGroup ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

end CFSG.Monster.B.E6
