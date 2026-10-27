module

public import CFSG.Quasithin.Vol2.Ch4Sec4F4411A
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs

public section

namespace CFSG.Quasithin.H13.Ch4.E443.F4411

open Subgroup

variable {G : Type*} [Group G]

theorem normalizer_le_of_stronglyEmbedded [Finite G] {M U : Subgroup G}
    (hM : CFSG.Open.fusionStronglyEmbedded M) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hUM : U ≤ M) :
    normalizer (U : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hodd := hM.2.2 g hgM
  have hle : U ≤ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro u hu
    refine ⟨hUM hu, g * u * g⁻¹, hUM ((mem_normalizer_iff.mp hg u).mp hu), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hU1 (Subgroup.eq_bot_of_card_eq U (by rw [hn, pow_zero]))
  have h2 : 2 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (hn ▸ dvd_pow_self 2 hn0).trans (Subgroup.card_dvd_of_le hle)
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)

theorem commutator_normalizer_le {Q D : Subgroup G} (hD : IsCyclic D)
    (hQD : Q ⊔ D = normalizer (Q : Set G)) :
    ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆ ≤ Q := by
  set N := normalizer (Q : Set G)
  have hQN : Q ≤ N := le_normalizer
  have hDN : D ≤ N := hQD ▸ le_sup_right
  have : (Q.subgroupOf N).Normal := normal_in_normalizer
  have hsup : Q.subgroupOf N ⊔ D.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQN hDN, hQD, Subgroup.subgroupOf_self]
  have hcomm : IsMulCommutative (D.subgroupOf N) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (congrArg (fun x : D => (x : G))
      ((IsCyclic.isMulCommutative (α := D)).is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)))⟩⟩
  have h := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  rw [← Subgroup.map_subtype_commutator]
  calc (commutator N).map N.subtype ≤ (Q.subgroupOf N).map N.subtype := Subgroup.map_mono h
    _ ≤ Q := by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

theorem perfCentral_of_fusionBenderBorel [Finite G] {q k : ℕ}
    (h : CFSG.Open.fusionBenderBorel G q k) : PerfCentral G := by
  intro U Y hU hY hYU
  rcases eq_or_ne U ⊥ with rfl | hU1
  · exact commutator_bot_left Y
  obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
  obtain ⟨hM, ⟨D, hDc, -, -, hQD⟩, -⟩ := h Q
  have hYN : Y ≤ normalizer ((Q : Subgroup G) : Set G) :=
    hYU.trans (normalizer_le_of_stronglyEmbedded hM hU hU1 (hUQ.trans le_normalizer))
  have hYQ : Y ≤ Q := calc
    Y = ⁅Y, Y⁆ := hY.symm
    _ ≤ _ := commutator_mono hYN hYN
    _ ≤ Q := commutator_normalizer_le hDc hQD
  have : Group.IsNilpotent (Q : Subgroup G) := Q.isPGroup'.isNilpotent
  rw [eq_bot_of_perfect_of_le hY hYQ, commutator_bot_right]

end CFSG.Quasithin.H13.Ch4.E443.F4411
