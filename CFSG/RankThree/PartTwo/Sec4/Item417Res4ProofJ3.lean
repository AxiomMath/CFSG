module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open scoped Pointwise

theorem isElementaryAbelian_of_isElemAbelian_three {X : Type*} [Group X] {V : Subgroup X}
    (h : CFSG.Assembly.IsElemAbelian 3 V) : IsElementaryAbelian 3 V :=
  { toIsMulCommutative := h.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using h.2 x x.2) }

theorem pRank_carrier_J3 :
    CFSG.pRank 3 (NativeSporadic.Carrier .J3) = 3 :=
  (CFSG.RankThree.Asc83Table.J3.native_J3).1

theorem bddAbove_ranks_J3 :
    BddAbove {r : ℕ | ∃ A : Subgroup (NativeSporadic.Carrier .J3), IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ r} := by
  by_contra h
  have h0 := Nat.sSup_of_not_bddAbove h
  have h3 := pRank_carrier_J3
  unfold CFSG.pRank at h3
  omega

theorem exists_e27_J3 :
    ∃ B : Subgroup (NativeSporadic.Carrier .J3), IsElementaryAbelian 3 B ∧ Nat.card B = 27 := by
  have h3 := pRank_carrier_J3
  unfold CFSG.pRank at h3
  have hne : {r : ℕ | ∃ A : Subgroup (NativeSporadic.Carrier .J3), IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ r}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, csSup_empty] at h3
    exact absurd h3 (by decide)
  have h := Nat.sSup_mem hne bddAbove_ranks_J3
  rw [h3] at h
  obtain ⟨B, hB, hB27⟩ := h
  exact ⟨B, hB, by rw [hB27]; norm_num⟩

theorem exists_card_eq_of_isElemAbelian_J3
    {D : Subgroup (NativeSporadic.Carrier .J3)}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) : ∃ k ≤ 3, Nat.card D = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (NativeSporadic.Carrier .J3) := CFSG.Sporadic.J3.fam_j3_simplicity.1
  have hp : IsPGroup 3 D := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hD.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hmem : k ∈ {r : ℕ | ∃ A : Subgroup (NativeSporadic.Carrier .J3),
      IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ r} :=
    ⟨D, isElementaryAbelian_of_isElemAbelian_three hD, hk⟩
  have hle := le_csSup bddAbove_ranks_J3 hmem
  have h3 := pRank_carrier_J3
  unfold CFSG.pRank at h3
  exact ⟨k, h3 ▸ hle, hk⟩

theorem k417OutJ3_holds :
    Res417Three.K417OutJ3 := by
  intro D hD
  obtain ⟨hDe, hmax, F, hFD, hF9, -⟩ := hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (NativeSporadic.Carrier .J3) := CFSG.Sporadic.J3.fam_j3_simplicity.1
  obtain ⟨k, hk3, hk⟩ := exists_card_eq_of_isElemAbelian_J3 hDe
  have hge : 9 ≤ Nat.card D := hF9.trans (Subgroup.card_le_of_le hFD)
  rw [hk] at hge ⊢
  have hk2 : 2 ≤ k := by
    by_contra h
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  · exfalso
    have hD9 : Nat.card D = 9 := by rw [hk]; norm_num
    have hp : IsPGroup 3 D := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hDe.2 g g.2)⟩
    obtain ⟨S, hDS⟩ := hp.exists_le_sylow
    obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .J3 ≃*
        (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    have hS := CFSG.AGLEmbedding.kFactJ3Sylow (NativeSporadic.Carrier .J3) ⟨b⟩ S
    obtain ⟨hZe, hZ9⟩ := hS.center_elem
    have hZD : CFSG.Quasithin.centerOf (S : Subgroup (NativeSporadic.Carrier .J3)) ≤ D := by
      intro z hz
      refine hmax z (hZe.2 z hz) fun d hd => ?_
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 d (hDS hd)).symm
    have hDZ : CFSG.Quasithin.centerOf (S : Subgroup (NativeSporadic.Carrier .J3)) = D :=
      Subgroup.eq_of_le_of_card_ge hZD (by rw [hD9, hZ9])
    obtain ⟨B, hB, hB27⟩ := exists_e27_J3
    have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 3) (by rw [hB27]; norm_num)
    obtain ⟨S', hBS'⟩ := hBp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (NativeSporadic.Carrier .J3) S' S
    have hBD : B.map (MulAut.conj g).toMonoidHom ≤ D := by
      rintro _ ⟨x, hx, rfl⟩
      have hxS : MulAut.conj g • x ∈ (S : Subgroup (NativeSporadic.Carrier .J3)) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ (hBS' hx)
      have hx3 : (MulAut.conj g).toMonoidHom x ^ 3 = 1 := by
        rw [← map_pow]
        have h := congrArg Subtype.val
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p ⟨x, hx⟩)
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
        rw [h, map_one]
      refine hmax _ hx3 fun d hd => ?_
      rw [← hDZ] at hd
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 _ hxS
    have h27 := Subgroup.card_le_of_le hBD
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom := by
      rw [MulEquiv.coe_toMonoidHom]
      exact (MulAut.conj g).injective
    rw [Subgroup.card_map_of_injective hinj, hB27, hD9] at h27
    omega
  · norm_num
