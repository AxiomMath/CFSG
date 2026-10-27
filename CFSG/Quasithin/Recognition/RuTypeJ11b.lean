module

public import CFSG.Quasithin.Recognition.RuTypeJ11a
public import CFSG.Quasithin.Recognition.RuTypeJ44f
public import CFSG.Quasithin.Recognition.RuTypeJ44e

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits
open MulAction

namespace J11

variable {G : Type*} [Group G]

theorem stabilizer_mk (F : Subgroup G) (g : G) :
    stabilizer G (g : G ⧸ F) = F.map (MulAut.conj g).toMonoidHom := by
  have e : (g : G ⧸ F) = g • ((1 : G) : G ⧸ F) := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  rw [e, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_quotient]

theorem card_stabilizer_subgroup {Ω : Type*} [MulAction G Ω] (S : Subgroup G) (γ : Ω) :
    Nat.card (stabilizer S γ) = Nat.card ↥(S ⊓ stabilizer G γ) := by
  have e : (stabilizer S γ).map S.subtype = S ⊓ stabilizer G γ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨y.2, hy⟩
    · intro hx
      obtain ⟨hxS, hx⟩ := Subgroup.mem_inf.mp hx
      exact ⟨⟨x, hxS⟩, hx, rfl⟩
  rw [← e, Subgroup.card_map_of_injective S.subtype_injective]

theorem faithfulSMul_of_core (F : Subgroup G)
    (h : ∀ g : G, (∀ x : G, x * g * x⁻¹ ∈ F) → g = 1) : FaithfulSMul G (G ⧸ F) := by
  refine ⟨fun {g₁ g₂} hg => ?_⟩
  have key : ∀ x : G, x * (g₁⁻¹ * g₂) * x⁻¹ ∈ F := by
    intro x
    have h1 := hg ((x⁻¹ : G) : G ⧸ F)
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul,
      QuotientGroup.eq] at h1
    have e : x * (g₁⁻¹ * g₂) * x⁻¹ = (g₁ * x⁻¹)⁻¹ * (g₂ * x⁻¹) := by group
    rw [e]
    exact h1
  exact inv_mul_eq_one.mp (h _ key)

theorem card_orbitRel_quotient_eq_three {S X : Type*} [Group S] [MulAction S X] [Finite X]
    (x : Fin 3 → X) (n : Fin 3 → ℕ) (hn : Function.Injective n)
    (hx : ∀ i, (orbit S (x i)).ncard = n i) (hsum : n 0 + n 1 + n 2 = Nat.card X) :
    Nat.card (orbitRel.Quotient S X) = 3 := by
  have hne : ∀ i j, x j ∈ orbit S (x i) → i = j := by
    intro i j hj
    apply hn
    rw [← hx i, ← hx j, orbit_eq_iff.2 hj]
  have hdisj : ∀ i j, i ≠ j → Disjoint (orbit S (x i)) (orbit S (x j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    apply hij
    apply hn
    rw [← hx i, ← hx j, ← orbit_eq_iff.2 hzi, ← orbit_eq_iff.2 hzj]
  have h01 : Disjoint (orbit S (x 0)) (orbit S (x 1)) := hdisj 0 1 (by decide)
  have h012 : Disjoint (orbit S (x 0) ∪ orbit S (x 1)) (orbit S (x 2)) :=
    Set.disjoint_union_left.mpr ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩
  have hcard : (orbit S (x 0) ∪ orbit S (x 1) ∪ orbit S (x 2)).ncard = Nat.card X := by
    rw [Set.ncard_union_eq h012 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq h01 (Set.toFinite _) (Set.toFinite _), hx, hx, hx, hsum]
  have hcover : orbit S (x 0) ∪ orbit S (x 1) ∪ orbit S (x 2) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ, hcard])
      (Set.toFinite _)
  let q : Fin 3 → orbitRel.Quotient S X := fun i => Quotient.mk'' (x i)
  have hq : Function.Injective q := by
    intro i j hij
    have := Quotient.exact' hij
    rw [orbitRel_apply] at this
    exact (hne j i this).symm
  have hs : Function.Surjective q := by
    intro w
    refine Quotient.inductionOn' w fun z => ?_
    have hz : z ∈ orbit S (x 0) ∪ orbit S (x 1) ∪ orbit S (x 2) := by
      rw [hcover]
      exact Set.mem_univ z
    have key : ∀ i, z ∈ orbit S (x i) → q i = Quotient.mk'' z := fun i hi =>
      Quotient.sound' (orbitRel_apply.mpr (mem_orbit_symm.mp hi))
    rcases hz with (hz | hz) | hz
    · exact ⟨0, key 0 hz⟩
    · exact ⟨1, key 1 hz⟩
    · exact ⟨2, key 2 hz⟩
  rw [← Nat.card_eq_of_bijective q ⟨hq, hs⟩, Nat.card_eq_fintype_card, Fintype.card_fin]

end J11

namespace RuDataM

variable {G : Type} [Group G] [Finite G] (M : RuDataM G)

theorem Q_conj_mem_F1 {q f : G} (hq : q ∈ ruQ M.T)
    (hf : f ∈ M.F1) : q * f * q⁻¹ ∈ M.F1 := by
  have hnorm : M.F1 ≤ Subgroup.normalizer (ruQ M.T : Set G) := fun _ hf =>
    mem_normalizer_of_conj_mem fun _ hq => M.conj_mem_Q (M.F1_le_H hf) hq
  have hcard : Nat.card ↥(M.F1 ⊔ ruQ M.T) = 2 ^ 13 * 5 := by
    have h := card_sup_mul_inf_of_normalizes hnorm
    rw [M.F1_inf_Q, M.card_Y, M.card_F1, M.toRuData.card_Q] at h
    norm_num at h ⊢
    omega
  have hidx : (M.F1.subgroupOf (M.F1 ⊔ ruQ M.T)).index = 2 := by
    have h := Subgroup.card_mul_index (M.F1.subgroupOf (M.F1 ⊔ ruQ M.T))
    rw [card_subgroupOf_of_le le_sup_left, hcard, M.card_F1] at h
    omega
  have hN := Subgroup.normal_of_index_eq_two hidx
  have h := hN.conj_mem ⟨f, Subgroup.mem_sup_left hf⟩ (by rw [Subgroup.mem_subgroupOf]; exact hf)
    ⟨q, Subgroup.mem_sup_right hq⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem exists_mem_Q_not_mem_F1 :
    ∃ h ∈ ruQ M.T, h ∉ M.F1 := by
  by_contra hcon
  have hQ : ruQ M.T ≤ M.F1 := fun q hq => by
    by_contra hq'
    exact hcon ⟨q, hq, hq'⟩
  have e := M.F1_inf_Q
  rw [inf_eq_right.mpr hQ] at e
  have h1 := M.card_Y
  rw [← e, M.toRuData.card_Q] at h1
  norm_num at h1

theorem z_mem_F1 : M.z ∈ M.F1 :=
  M.Agrp_le_F1 (M.W_le_Agrp (M.U_le_W (M.V_le_U M.z_mem_V)))

theorem inf_H_eq_F1
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) : (M.F1 ⊔ M.F2) ⊓ ruH M.T = M.F1 := by
  have hle : M.F1.subgroupOf (M.F1 ⊔ M.F2) ≤ (ruH M.T).subgroupOf (M.F1 ⊔ M.F2) :=
    fun x hx => M.F1_le_H hx
  have hcard : Nat.card (M.F1.subgroupOf (M.F1 ⊔ M.F2)) = 2 ^ 12 * 5 := by
    rw [card_subgroupOf_of_le le_sup_left, M.card_F1]
  rcases RuRank3.eq_or_eq_top_of_card_eq' φ hcard hle with h | h
  · have e := Subgroup.subgroupOf_inj.mp h
    rw [inf_comm, e, inf_eq_left.mpr le_sup_left]
  · exfalso
    have hFH : M.F1 ⊔ M.F2 ≤ ruH M.T := Subgroup.subgroupOf_eq_top.mp h
    apply M.z_ne_one
    exact eq_one_of_mem_F_of_comm_Fd φ (Subgroup.mem_sup_left M.z_mem_F1)
      fun y hy => M.Z_comm_H M.z_mem_Z (hFH (Fd_le φ hy))

theorem inf_conj_eq_F1
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) (hC : Subgroup.centralizer (Fd φ : Set G) = ⊥) {h : G}
    (hhQ : h ∈ ruQ M.T) (hhF1 : h ∉ M.F1) :
    (M.F1 ⊔ M.F2) ⊓ (M.F1 ⊔ M.F2).map (MulAut.conj h).toMonoidHom = M.F1 := by
  have hconj : ∀ x : G, x ∈ (M.F1 ⊔ M.F2).map (MulAut.conj h).toMonoidHom ↔
      h⁻¹ * x * h ∈ M.F1 ⊔ M.F2 := fun x => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hle : M.F1.subgroupOf (M.F1 ⊔ M.F2) ≤
      ((M.F1 ⊔ M.F2).map (MulAut.conj h).toMonoidHom).subgroupOf (M.F1 ⊔ M.F2) := by
    intro f hf
    rw [Subgroup.mem_subgroupOf] at hf ⊢
    rw [hconj]
    have h1 := M.Q_conj_mem_F1 (inv_mem hhQ) hf
    rw [inv_inv] at h1
    exact Subgroup.mem_sup_left h1
  have hcard : Nat.card (M.F1.subgroupOf (M.F1 ⊔ M.F2)) = 2 ^ 12 * 5 := by
    rw [card_subgroupOf_of_le le_sup_left, M.card_F1]
  rcases RuRank3.eq_or_eq_top_of_card_eq' φ hcard hle with e | e
  · have e' := Subgroup.subgroupOf_inj.mp e
    rw [inf_comm, e', inf_eq_left.mpr le_sup_left]
  · exfalso
    have hFle : M.F1 ⊔ M.F2 ≤ (M.F1 ⊔ M.F2).map (MulAut.conj h).toMonoidHom :=
      Subgroup.subgroupOf_eq_top.mp e
    have hN : h⁻¹ ∈ Subgroup.normalizer ((M.F1 ⊔ M.F2 : Subgroup G) : Set G) :=
      mem_normalizer_of_conj_mem fun x hx => by
        rw [inv_inv]
        exact (hconj x).mp (hFle hx)
    have hhF : h ∈ M.F1 ⊔ M.F2 := by
      have := inv_mem (normalizer_F_le φ hC hN)
      rwa [inv_inv] at this
    apply hhF1
    have hH : h ∈ (M.F1 ⊔ M.F2) ⊓ ruH M.T :=
      Subgroup.mem_inf.mpr ⟨hhF, Subgroup.map_subtype_le _ hhQ⟩
    rwa [M.inf_H_eq_F1 φ] at hH

theorem centralizer_Fd_F_eq_bot
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) : Subgroup.centralizer (Fd φ : Set G) = ⊥ :=
  M.centralizer_Fd_eq_bot φ (Subgroup.mem_sup_left M.b5el_mem_F1) M.b5el_mem_H M.orderOf_b5el

theorem faithfulSMul_quotient
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) : FaithfulSMul G (G ⧸ (M.F1 ⊔ M.F2)) := by
  have hG : Nat.card ↥(M.F1 ⊔ M.F2) < Nat.card G := by
    rw [card_F_of φ, M.card_eq]
    norm_num
  exact J11.faithfulSMul_of_core _ fun g hg =>
    eq_one_of_forall_conj_mem φ (M.centralizer_Fd_F_eq_bot φ) hG hg

theorem card_quotient_F
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) : Nat.card (G ⧸ (M.F1 ⊔ M.F2)) = 4060 := by
  have h := Subgroup.card_mul_index (M.F1 ⊔ M.F2)
  rw [card_F_of φ, M.card_eq] at h
  rw [← Subgroup.index_eq_card]
  norm_num at h
  omega

end RuDataM

end CFSG.Quasithin.RuType
