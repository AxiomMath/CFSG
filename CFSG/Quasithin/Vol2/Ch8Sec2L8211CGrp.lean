module

public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin.H13.L8211C

open CFSG.Open

@[expose] def IsQS (Q : Type) [Group Q] : Prop :=
  ∀ K : Subgroup Q, K ≠ ⊥ → ⁅K, K⁆ = K → IsSubnormal K ⊤ → K = ⊤

theorem isQS_of_isSimpleGroup (R : Type) [Group R] [IsSimpleGroup R] : IsQS R := by
  intro K hK _ hKs
  rcases IsSubnormal.eq_bot_or_top hKs with h | h
  · exact absurd h hK
  · exact h

theorem perfect_map_of_surjective {Q R : Type} [Group Q] [Group R] (f : Q →* R)
    (hf : Function.Surjective f) (hQ : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) :
    ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊤ := by
  have h := Subgroup.map_commutator (⊤ : Subgroup Q) (⊤ : Subgroup Q) f
  rw [hQ, Subgroup.map_top_of_surjective f hf] at h
  exact h.symm

theorem perfect_top_subgroup {Q : Type} [Group Q] {K : Subgroup Q} (hK : ⁅K, K⁆ = K) :
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
  have h1 : Subgroup.map K.subtype (⊤ : Subgroup K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine Subgroup.map_injective (f := K.subtype) K.subtype_injective ?_
  rw [Subgroup.map_commutator, h1, hK]

theorem subsingleton_of_perfect_solvable (R : Type) [Group R] [Group.IsSolvable R]
    (hR : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊤) : Subsingleton R := by
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial R
  have h2 : commutator R = ⊤ := hR
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem eq_top_of_normal {Q : Type} [Group Q] (H N : Subgroup Q) [H.Normal]
    [Group.IsSolvable N] (hQ : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) (hHN : H ⊔ N = ⊤) : H = ⊤ := by
  let φ : N →* Q ⧸ H := (QuotientGroup.mk' H).comp N.subtype
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq : q ∈ H ⊔ N := by
      rw [hHN]
      exact Subgroup.mem_top q
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hq
    refine ⟨⟨z, hz⟩, ?_⟩
    subst hyz
    show (QuotientGroup.mk z : Q ⧸ H) = QuotientGroup.mk (y * z)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul]
  haveI : Group.IsSolvable (Q ⧸ H) := Group.isSolvable_of_surjective hφ
  have hperf := perfect_map_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H) hQ
  have hsub := subsingleton_of_perfect_solvable (Q ⧸ H) hperf
  rw [eq_top_iff]
  intro q _
  have h1 : (QuotientGroup.mk q : Q ⧸ H) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff q).mp h1

theorem eq_top_of_isSubnormal_sup {Q : Type} [Group Q] (N : Subgroup Q) [Group.IsSolvable N]
    (hQ : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) {K : Subgroup Q} (hK : IsSubnormal K ⊤)
    (hKN : K ⊔ N = ⊤) : K = ⊤ := by
  have key : ∀ A B : Subgroup Q, IsSubnormal A B → B = ⊤ → A ⊔ N = ⊤ → A = ⊤ := by
    intro A B h
    induction h with
    | refl H => exact fun hB _ => hB
    | @step H M B' hle hN hMB ih =>
      intro hB hHN
      have hMN : M ⊔ N = ⊤ := by
        rw [eq_top_iff, ← hHN]
        exact sup_le_sup_right hle N
      have hM : M = ⊤ := ih hB hMN
      subst hM
      have hH : H.Normal := by
        have h2 : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (H : Set Q) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN
        exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h2)
      exact eq_top_of_normal H N hQ hHN
  exact key K ⊤ hK rfl hKN

theorem eq_bot_of_perfect_le {Q : Type} [Group Q] {N K : Subgroup Q} [Group.IsSolvable N]
    (hKN : K ≤ N) (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  haveI : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKN)
  have hsub := subsingleton_of_perfect_solvable K (perfect_top_subgroup hK)
  ext x
  constructor
  · intro hx
    have h1 : (⟨x, hx⟩ : K) = 1 := Subsingleton.elim _ _
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val h1
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact K.one_mem

theorem isQS_of_surjective {Q R : Type} [Group Q] [Group R] (f : Q →* R)
    (hf : Function.Surjective f) (hQ : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) [Group.IsSolvable f.ker]
    (hR : IsQS R) : IsQS Q := by
  intro K hK0 hKp hKs
  have hmap : K.map f = ⊤ := by
    have hsub : IsSubnormal (K.map f) ⊤ := by
      have h := CFSG.Open.IsSubnormal.map f hKs
      rwa [Subgroup.map_top_of_surjective f hf] at h
    have hperf : ⁅K.map f, K.map f⁆ = K.map f := by
      rw [← Subgroup.map_commutator, hKp]
    have hne : K.map f ≠ ⊥ := by
      intro hbot
      have hle : K ≤ f.ker := by
        intro k hk
        have hmem : f k ∈ K.map f := Subgroup.mem_map_of_mem f hk
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      exact hK0 (eq_bot_of_perfect_le hle hKp)
    exact hR (K.map f) hne hperf hsub
  apply eq_top_of_isSubnormal_sup f.ker hQ hKs
  rw [eq_top_iff]
  intro q _
  have hq : f q ∈ K.map f := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hq
  have hker : k⁻¹ * q ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkq, inv_mul_cancel]
  have h := Subgroup.mul_mem_sup hk hker
  rwa [mul_inv_cancel_left] at h

theorem eq_of_isQS {G : Type} [Group G] {L : Subgroup G} (hL : IsQS ↥L) {K : Subgroup G}
    (hKL : K ≤ L) (hK0 : K ≠ ⊥) (hKp : ⁅K, K⁆ = K) (hKs : IsSubnormal K L) : K = L := by
  have hK' : K.subgroupOf L = ⊤ := by
    refine hL (K.subgroupOf L) ?_ ?_ ?_
    · intro hb
      apply hK0
      have h := Subgroup.map_subgroupOf_eq_of_le hKL
      rw [hb, Subgroup.map_bot] at h
      exact h.symm
    · refine Subgroup.map_injective (f := L.subtype) L.subtype_injective ?_
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKL, hKp]
    · exact CFSG.Open.IsSubnormal.top_iff.mpr hKs.subgroupOf
  exact le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp hK')

theorem mem_cComp_of_isQS {G : Type} [Group G] {L X : Subgroup G} (hLX : IsSubnormal L X)
    (hne : L ≠ ⊥) (hperf : ⁅L, L⁆ = L) (hL : IsQS ↥L) :
    L ∈ CFSG.Quasithin.cComp X := by
  refine CFSG.Quasithin.mem_cComp_iff.mpr ⟨hne, hperf, hLX, fun K hKlt hK0 hKp hKs => ?_⟩
  exact hKlt.ne (eq_of_isQS hL hKlt.le hK0 hKp
    (CFSG.Quasithin.A3.subnormal_of_le_of_le hKs hKlt.le hLX.le))

end CFSG.Quasithin.H13.L8211C
