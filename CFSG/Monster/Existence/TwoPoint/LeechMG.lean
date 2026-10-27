module

public import CFSG.Monster.Existence.ELevelDef
public import CFSG.Monster.Existence.TwoPoint.LeechStab

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.B Subgroup

theorem leech_exists_short_rep {v : L2} (hv : v ∈ shortSet) :
    ∃ r : Q, IsShortCoord (coordOf r) ∧ phi0 (coordOf r) = v :=
  (phiQ_surjective (Multiplicative.ofAdd v)).elim fun q hq =>
    have h : phi0 (coordOf q) = v := by rw [← toAdd_phiQ, hq, toAdd_ofAdd]
    ⟨q, hv.elim fun u hu => ⟨u, hu.1, hu.2.trans h.symm⟩, h⟩

theorem isShortCoord_of_phi0_mem {q : Q} (h : phi0 (coordOf q) ∈ shortSet) :
    IsShortCoord (coordOf q) := h

theorem leech_isConj_tGriess_rhoGriess
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    IsConj tGriess (rhoGriess r) :=
  (exists_Gvis_conj_short isShortCoord_rStar hr).elim fun g hg =>
    isConj_iff.2 ⟨⟨g, Gvis_le_AutO hg.1⟩, Subtype.ext hg.2.1⟩

theorem leech_rhoGriess_comm_iff {q q' : Q} :
    rhoGriess q * rhoGriess q' = rhoGriess q' * rhoGriess q ↔ q' * q = q * q' :=
  ⟨fun h => rhoGriess_injective ((rhoGriess_mul q' q).trans (h.trans (rhoGriess_mul q q').symm)),
    fun h => (rhoGriess_mul q' q).symm.trans ((congrArg rhoGriess h).trans (rhoGriess_mul q q'))⟩

theorem leech_rhoGriess_mul_self {q : Q} (h : q * q = 1) : rhoGriess q * rhoGriess q = 1 :=
  (rhoGriess_mul q q).symm.trans ((congrArg rhoGriess h).trans rhoGriess_one)

theorem map_eq_leechJ {r₁ r₂ : Q} {H : Subgroup MGriess}
    (hH : ∀ g : MGriess, g ∈ H ↔ g * rhoGriess r₁ = rhoGriess r₁ * g ∧
      g * rhoGriess r₂ = rhoGriess r₂ * g ∧ g * xGriess = xGriess * g) :
    H.map AutO.subtype = leechJ r₁ r₂ := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (hH g).1 hg
    have hx : g ∈ cent xGriess := mem_centralizer_singleton_iff.2 h3
    exact mem_leechJ_iff.2 ⟨(SetLike.ext_iff.1 map_cent_xGriess _).1 ⟨g, hx, rfl⟩,
      congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  · intro hf
    obtain ⟨hv, h1, h2⟩ := mem_leechJ_iff.1 hf
    obtain ⟨g, hg, rfl⟩ := (SetLike.ext_iff.1 map_cent_xGriess f).2 hv
    exact ⟨g, (hH g).2 ⟨Subtype.ext h1, Subtype.ext h2,
      mem_centralizer_singleton_iff.1 hg⟩, rfl⟩

@[expose] def equivLeechJ {r₁ r₂ : Q} {H : Subgroup MGriess}
    (hH : ∀ g : MGriess, g ∈ H ↔ g * rhoGriess r₁ = rhoGriess r₁ * g ∧
      g * rhoGriess r₂ = rhoGriess r₂ * g ∧ g * xGriess = xGriess * g) :
    H ≃* leechJ r₁ r₂ :=
  (H.equivMapOfInjective AutO.subtype AutO.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_eq_leechJ hH))

theorem leech_exists_extraspecial_shape_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    {k : ℕ} {X : Type} [Group X]
    (h : ∃ (N : Subgroup H) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧ Nat.card N = 2 ^ k ∧
      Nonempty (H ⧸ N ≃* X)) :
    ∃ (N : Subgroup H') (_ : N.Normal), IsExtraspecialPGroup 2 N ∧ Nat.card N = 2 ^ k ∧
      Nonempty (H' ⧸ N ≃* X) := by
  obtain ⟨N, hN, hX, hc, ⟨q⟩⟩ := h
  have : (N.map (e : H →* H')).Normal := hN.map _ e.surjective
  exact ⟨N.map (e : H →* H'), inferInstance,
    IsExtraspecialPGroup.of_mulEquiv (N.equivMapOfInjective (e : H →* H') e.injective) hX,
    by rw [Subgroup.card_map_of_injective e.injective, hc],
    ⟨(QuotientGroup.congr N _ e rfl).symm.trans q⟩⟩

section Generic

variable {G : Type*} [Group G]

theorem leech_mul_self_ab {z a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = z * (b * a)) : a * b * (a * b) = z := by
  calc a * b * (a * b) = z * (b * a) * (a * b) := by rw [← hab]
    _ = z * (b * (a * a) * b) := by simp only [mul_assoc]
    _ = z := by rw [ha, mul_one, hb, mul_one]

theorem leech_mul_eq_of_inv_mul_mul {z r q : G} (hz : z ∈ center G) (hq : q * q = 1)
    (h : q⁻¹ * r * q = z * r) : r * q = z * (q * r) := by
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  rw [hqi] at h
  calc r * q = q * (q * r * q) := by rw [← mul_assoc, ← mul_assoc, hq, one_mul]
    _ = q * (z * r) := by rw [h]
    _ = z * (q * r) := by rw [← mul_assoc, ← mul_assoc, mem_center_iff.1 hz q]

theorem leech_orderOf_eq_four_of_sq {c x : G} (h : c ^ 2 = x) (hx : x * x = 1) (hx1 : x ≠ 1) :
    orderOf c = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c)
    (by rw [pow_one, h]; exact hx1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h, pow_two, hx])
  rw [h4]
  norm_num

theorem leech_commute_sq {a b g : G} (ha : g * a = a * g) (hb : g * b = b * g) :
    g * (a * b) ^ 2 = (a * b) ^ 2 * g :=
  ((Commute.mul_right (show Commute g a from ha) (show Commute g b from hb)).pow_right 2).eq

end Generic

section Triangles

variable {G : Type} [Group G]

theorem leech_isLongTriangle {a α β γ : G} (hα : IsConj a α) (hβ : IsConj a β)
    (hγ : IsConj a γ) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (p₁ : IsConj a (α * β)) (p₂ : IsConj a (β * α)) (p₃ : IsConj a (α * γ))
    (p₄ : IsConj a (γ * α)) (p₅ : IsConj a (β * γ)) (p₆ : IsConj a (γ * β))
    (n₁ : α * β ≠ α) (n₂ : α * β ≠ β) (n₃ : α * β ≠ γ) : IsLongTriangle a {α, β, γ} := by
  have hT : IsTriangle a {α, β, γ} := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Set.ncard_insert_of_notMem, Set.ncard_pair hβγ]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hαβ, hαγ⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro x (rfl | rfl | rfl) <;> assumption
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy <;>
        first
          | exact absurd rfl hxy
          | assumption
  refine ⟨hT, fun hS => ?_⟩
  have h := hS.2 α (by simp) β (by simp) hαβ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h
  · exact n₁ h
  · exact n₂ h
  · exact n₃ h

end Triangles

end CFSG.Monster.Existence
