module

public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.Quasithin.EmptyFaithful.S143Five
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Recognition.CertSzZero

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace F112RR

variable {G : Type} [Group G] [Finite G]

theorem sup_facts {L T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (T ⊓ L) L) {k r : ℕ}
    (hk : 1 ≤ k) (hr : r.Prime) (hr2 : Odd r) (hcard : Nat.card (OTwoQuot L) = 2 ^ k * r) :
    IsSylowTwoOf T (L ⊔ T) ∧ T.relIndex (L ⊔ T) = r ∧
      ¬ (L ⊔ T) ≤ Subgroup.normalizer (T : Set G) := by
  set I := T ⊓ L with hI
  have hIL : I ≤ L := inf_le_right
  have hIT : I ≤ T := inf_le_left
  have hLX : L ≤ L ⊔ T := le_sup_left
  have hTX : T ≤ L ⊔ T := le_sup_right
  have hidx : (I.subgroupOf L).index = r := index_sylow_eq_of_card_quot hsyl hr2 hcard
  have h1 : L.relIndex (T ⊔ L) = L.relIndex T := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hTL
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTL
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient T L hTL).toEquiv.symm
  rw [sup_comm] at h1
  have h2 : I.relIndex T = L.relIndex T := by
    rw [hI, inf_comm]
    exact Subgroup.inf_relIndex_right L T
  have hm1 := Subgroup.relIndex_mul_relIndex I L (L ⊔ T) hIL hLX
  have hm2 := Subgroup.relIndex_mul_relIndex I T (L ⊔ T) hIT hTX
  have hpos : 0 < I.relIndex T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : T.relIndex (L ⊔ T) = I.relIndex L := by
    have ha : L.relIndex (L ⊔ T) = I.relIndex T := by rw [h2, h1]
    have e1 : I.relIndex L * L.relIndex (L ⊔ T) = I.relIndex T * T.relIndex (L ⊔ T) :=
      hm1.trans hm2.symm
    rw [ha] at e1
    have e2 : I.relIndex T * I.relIndex L = I.relIndex T * T.relIndex (L ⊔ T) := by
      rw [mul_comm (I.relIndex T), e1]
    exact (Nat.eq_of_mul_eq_mul_left hpos e2).symm
  have h5 : T.relIndex (L ⊔ T) = r := by
    rw [h3]
    exact hidx
  refine ⟨⟨hTX, hT2, ?_⟩, h5, ?_⟩
  · rw [show (T.subgroupOf (L ⊔ T)).index = T.relIndex (L ⊔ T) from rfl, h5]
    intro h2r
    exact (Nat.not_even_iff_odd.mpr hr2) (even_iff_two_dvd.mpr h2r)
  · intro hXN
    have hLN : L ≤ Subgroup.normalizer (T : Set G) := hLX.trans hXN
    have hLI : L ≤ Subgroup.normalizer (I : Set G) :=
      le_normalizer_inf151 hLN Subgroup.le_normalizer
    have hB := inf_normalizer_eq_of_card_quot hsyl hk hr hr2 hcard
    have hLle : L ≤ I := by
      have : L ≤ L ⊓ Subgroup.normalizer (I : Set G) := le_inf le_rfl hLI
      rw [hB] at this
      exact this
    have h1' : (I.subgroupOf L).index = 1 := Subgroup.index_eq_one.mpr (by
      rw [Subgroup.subgroupOf_eq_top]; exact hLle)
    rw [hidx] at h1'
    exact hr.one_lt.ne' h1'

theorem card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 2 ^ 1 * 3 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

theorem oTwoQuot_sup_of_perm3 {L T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (T ⊓ L) L)
    (hq : Nonempty (OTwoQuot L ≃* Equiv.Perm (Fin 3))) :
    IsSylowTwoOf T (L ⊔ T) ∧ T.relIndex (L ⊔ T) = 3 ∧
      ¬ (L ⊔ T) ≤ Subgroup.normalizer (T : Set G) ∧
      Nonempty (OTwoQuot (L ⊔ T) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := hq
  have hc : Nat.card (OTwoQuot L) = 2 ^ 1 * 3 := by
    rw [Nat.card_congr e.toEquiv, card_perm_fin_three]
  obtain ⟨hs, hr, hnn⟩ := sup_facts hT2 hTL hsyl le_rfl (by norm_num) (by decide) hc
  obtain ⟨S, hS, hSi, hS1⟩ := exists_isPGroup_index_quot_of_relIndex le_sup_right hT2 hr
    (by norm_num) hnn
  obtain ⟨e'⟩ := nonempty_mulEquiv_perm_three (OTwoQuot.eq_bot_of_normal_of_isPGroup (L ⊔ T))
    hS hS1 hSi
  exact ⟨hs, hr, hnn, ⟨e'⟩⟩

theorem oTwoQuot_sup_of_five {L T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (T ⊓ L) L)
    (hq : Nonempty (OTwoQuot L ≃* DihedralGroup 5) ∨
      Nonempty (OTwoQuot L ≃* ↥(CFSG.Open.Sz 0))) :
    IsSylowTwoOf T (L ⊔ T) ∧ T.relIndex (L ⊔ T) = 5 ∧
      ¬ (L ⊔ T) ≤ Subgroup.normalizer (T : Set G) ∧
      (Nonempty (OTwoQuot (L ⊔ T) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (L ⊔ T) ≃* ↥(CFSG.Open.Sz 0))) := by
  obtain ⟨k, hk, hc⟩ : ∃ k : ℕ, 1 ≤ k ∧ Nat.card (OTwoQuot L) = 2 ^ k * 5 := by
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine ⟨1, le_rfl, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
      norm_num
    · refine ⟨2, by norm_num, ?_⟩
      rw [Nat.card_congr e.toEquiv, card_sz_zero_eq_twenty]
      norm_num
  obtain ⟨hs, hr, hnn⟩ := sup_facts hT2 hTL hsyl hk (by norm_num) (by decide) hc
  obtain ⟨S, hS, hSi, hS1⟩ := exists_isPGroup_index_quot_of_relIndex le_sup_right hT2 hr
    (by norm_num) hnn
  have hX2 := OTwoQuot.eq_bot_of_normal_of_isPGroup (L ⊔ T)
  refine ⟨hs, hr, hnn, ?_⟩
  rcases nonempty_mulEquiv_dihedralGroup_five_or_card_twenty hX2 hS hS1 hSi with hD | hc20
  · exact Or.inl hD
  · have : Finite ↥(CFSG.Open.Sz 0) :=
      Nat.finite_of_card_ne_zero (by rw [card_sz_zero_eq_twenty]; norm_num)
    obtain ⟨e⟩ := nonempty_mulEquiv_of_card_twenty hX2
      (fun N hN hp => le_bot_iff.mp (pCore_two_sz_zero_eq_bot ▸ le_pCore 2 hN hp))
      hc20 card_sz_zero_eq_twenty
    exact Or.inr ⟨e⟩

end F112RR

end CFSG.Quasithin
