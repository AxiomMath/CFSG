module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped Pointwise

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D]

namespace SubData

variable [Finite D] {H T N W : Subgroup D} {w : D} (d : SubData H T N W w)

include d

theorem card_H' : Nat.card ↥((N ⊔ Subgroup.zpowers w) ⊔ W) = 6 * Nat.card ↥N := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer' d.W_norm_M
  rw [d.W_inf_M, d.card_M, d.card_W] at h1
  have hpos : 0 < Nat.card ↥(W ⊓ N) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  linarith

theorem relIndex_H' : ((N ⊔ Subgroup.zpowers w) ⊔ W).relIndex H = 2 := by
  have h1 := card_eq_relIndex_mul d.H'_le_H
  rw [d.card_H, d.card_H'] at h1
  have hpos : 0 < 6 * Nat.card ↥N := by have := Nat.card_pos (α := ↥N); omega
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  linarith

theorem card_T' : Nat.card ↥(N ⊔ W) = 2 * Nat.card ↥N := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer' d.W_norm_N
  rw [d.card_W] at h1
  have hpos : 0 < Nat.card ↥(W ⊓ N) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  linarith

set_option linter.unusedSectionVars false in
theorem N_le_H' : N ≤ (N ⊔ Subgroup.zpowers w) ⊔ W := le_sup_left.trans le_sup_left

theorem T'_le_H' : N ⊔ W ≤ (N ⊔ Subgroup.zpowers w) ⊔ W :=
  sup_le d.N_le_H' le_sup_right

theorem H'_inf_T : ((N ⊔ Subgroup.zpowers w) ⊔ W) ⊓ T = N ⊔ W := by
  apply le_antisymm
  · rintro x ⟨hxH', hxT⟩
    have hx : x ∈ ((N ⊔ Subgroup.zpowers w : Subgroup D) : Set D) * (W : Set D) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ d.W_norm_M]; exact hxH'
    obtain ⟨m, hm, t, ht, hmt⟩ := Set.mem_mul.mp hx
    subst hmt
    have hmT : m ∈ T := by
      have := T.mul_mem hxT (T.inv_mem (d.W_le ht))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (d.M_inf_T_le ⟨hm, hmT⟩))
      (Subgroup.mem_sup_right ht)
  · exact le_inf d.T'_le_H' (sup_le d.N_le_T d.W_le)

theorem H'_inf_Q : ((N ⊔ Subgroup.zpowers w) ⊔ W) ⊓ pCoreOf 2 H = N := by
  apply le_antisymm
  · rintro x ⟨hxH', hxQ⟩
    have hxT' : x ∈ N ⊔ W := by
      rw [← d.H'_inf_T]; exact ⟨hxH', d.vertex.pCoreOf_le hxQ⟩
    have hx : x ∈ (N : Set D) * (W : Set D) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N W d.W_norm_N]; exact hxT'
    obtain ⟨n, hn, t, ht, hnt⟩ := Set.mem_mul.mp hx
    subst hnt
    have htQ : t ∈ pCoreOf 2 H := by
      have := (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem (d.N_le hn)) hxQ
      simpa using this
    exact N.mul_mem hn (d.W_inf_Q ⟨ht, htQ⟩)
  · exact le_inf d.N_le_H' d.N_le

theorem exists_hom_H' : ∃ ψ : ↥((N ⊔ Subgroup.zpowers w) ⊔ W) →* Equiv.Perm (Fin 3),
    Function.Surjective ψ ∧ ∀ x : ↥((N ⊔ Subgroup.zpowers w) ⊔ W), ψ x = 1 ↔ (x : D) ∈ N := by
  obtain ⟨π, hπ, hπk⟩ := d.vertex.exists_hom
  let ψ : ↥((N ⊔ Subgroup.zpowers w) ⊔ W) →* Equiv.Perm (Fin 3) :=
    π.comp (Subgroup.inclusion d.H'_le_H)
  have hker : ∀ x : ↥((N ⊔ Subgroup.zpowers w) ⊔ W), ψ x = 1 ↔ (x : D) ∈ N := by
    intro x
    change π (Subgroup.inclusion d.H'_le_H x) = 1 ↔ _
    rw [hπk]
    constructor
    · intro hxQ
      exact d.H'_inf_Q.le ⟨x.2, hxQ⟩
    · intro hxN
      exact d.N_le hxN
  refine ⟨ψ, ?_, hker⟩
  have hkerN : ψ.ker = N.subgroupOf ((N ⊔ Subgroup.zpowers w) ⊔ W) := by
    ext x
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hc1 : Nat.card ↥ψ.ker = Nat.card ↥N := by
    rw [hkerN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.N_le_H').toEquiv
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hc1, d.card_H'] at hmul
  have hpos : 0 < Nat.card ↥N := Nat.card_pos
  have hrange : Nat.card ↥ψ.range = 6 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    linarith
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hperm])
  exact MonoidHom.range_eq_top.mp htop

theorem pCore_H' {ψ : ↥((N ⊔ Subgroup.zpowers w) ⊔ W) →* Equiv.Perm (Fin 3)}
    (hψ : Function.Surjective ψ) (hker : ∀ x, ψ x = 1 ↔ (x : D) ∈ N) :
    CFSG.Open.pCore 2 ↥((N ⊔ Subgroup.zpowers w) ⊔ W) = ψ.ker := by
  apply le_antisymm
  · have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 ψ hψ
    rw [pCore_perm_three] at h1
    exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp h1)
  · have hkerN : ψ.ker = N.subgroupOf ((N ⊔ Subgroup.zpowers w) ⊔ W) := by
      ext x
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hN2 : IsPGroup 2 ↥N := d.vertex.isPGroup.to_le d.N_le_T
    have hp : IsPGroup 2 ↥ψ.ker := by
      rw [hkerN]
      exact hN2.of_equiv (Subgroup.subgroupOfEquivOfLe d.N_le_H').symm
    exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hp

theorem pCoreOf_H' : pCoreOf 2 ((N ⊔ Subgroup.zpowers w) ⊔ W) = N := by
  obtain ⟨ψ, hψ, hker⟩ := d.exists_hom_H'
  have hkerN : ψ.ker = N.subgroupOf ((N ⊔ Subgroup.zpowers w) ⊔ W) := by
    ext x
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  unfold pCoreOf
  rw [d.pCore_H' hψ hker, hkerN]
  exact Subgroup.map_subgroupOf_eq_of_le d.N_le_H'

theorem vertex_H' : Vertex ((N ⊔ Subgroup.zpowers w) ⊔ W) (N ⊔ W) := by
  obtain ⟨ψ, hψ, hker⟩ := d.exists_hom_H'
  have hidx : (N ⊔ W).relIndex ((N ⊔ Subgroup.zpowers w) ⊔ W) = 3 := by
    have h1 := card_eq_relIndex_mul d.T'_le_H'
    rw [d.card_H', d.card_T'] at h1
    have hpos : 0 < 2 * Nat.card ↥N := by have := Nat.card_pos (α := ↥N); omega
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    linarith
  have : (CFSG.Open.pCore 2 ↥((N ⊔ Subgroup.zpowers w) ⊔ W)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal 2
  refine ⟨⟨d.T'_le_H', d.vertex.isPGroup.to_le (sup_le d.N_le_T d.W_le), ?_⟩, hidx, ?_, ?_⟩
  · have : ((N ⊔ W).subgroupOf ((N ⊔ Subgroup.zpowers w) ⊔ W)).index = 3 := hidx
    rw [this]
    omega
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq (d.pCore_H' hψ hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩
  · unfold CharTwo
    rw [d.pCoreOf_H']
    rintro x ⟨hxH', hxC⟩
    have hxQ : x ∈ pCoreOf 2 H := d.centralizer_le ⟨d.H'_le_H hxH', hxC⟩
    exact d.H'_inf_Q.le ⟨hxH', hxQ⟩

end SubData

end GoldAmL2T

end F6

end CFSG.Quasithin
