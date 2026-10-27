module

public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.EmptyFaithful.S143FiveAux
public import CFSG.Quasithin.EmptyFaithful.S142Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem isHStar_of_relIndex_prime {G : Type*} [Group G] {T M H : Subgroup G} (hTM : T ≤ M)
    (hH : InH T H) (hHM : ¬ H ≤ M) {r : ℕ} (hr : r.Prime) (hidx : T.relIndex H = r) :
    IsHStar T M H := by
  refine ⟨hH, hHM, fun Y hY hYH hYM => ?_⟩
  have h1 : T.relIndex H = T.relIndex Y * Y.relIndex H :=
    (Subgroup.relIndex_mul_relIndex T Y H hY.1 hYH).symm
  rw [hidx] at h1
  rcases Nat.prime_mul_iff.mp (h1 ▸ hr) with ⟨-, hb⟩ | ⟨-, ha⟩
  · exact le_antisymm hYH (Subgroup.relIndex_eq_one.mp hb)
  · exact absurd ((Subgroup.relIndex_eq_one.mp ha).trans hTM) hYM

theorem OTwoQuot.eq_bot_of_normal_of_isPGroup {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (N : Subgroup (OTwoQuot H)) (hN : N.Normal) (hp : IsPGroup 2 N) : N = ⊥ := by
  have h0 : CFSG.Open.pCore 2 (OTwoQuot H) = ⊥ := by
    exact pCore_two_quot_eq_bot H
  exact le_bot_iff.mp (h0 ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)

theorem exists_isPGroup_index_quot_of_relIndex {G : Type*} [Group G] [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (hT : IsPGroup 2 T) {r : ℕ} (hr : T.relIndex H = r) (hodd : ¬ 2 ∣ r)
    (hnn : ¬ H ≤ Subgroup.normalizer (T : Set G)) :
    ∃ S : Subgroup (OTwoQuot H), IsPGroup 2 S ∧ S.index = r ∧ S ≠ ⊥ := by
  have hSyl : IsSylowTwoOf T H :=
    ⟨hTH, hT, by rw [show (T.subgroupOf H).index = r from hr]; exact hodd⟩
  set N : Subgroup H := CFSG.Open.pCore 2 ↥H with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hOT : pCoreOf 2 H ≤ T :=
    A4.le_of_normal_of_isSylowTwoOf hSyl (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (by rw [pCoreOf, A4.subgroupOf_map_subtype']; exact hNn)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hNle : N ≤ T.subgroupOf H := fun n hn => hOT ⟨n, hn, rfl⟩
  let π : H →* OTwoQuot H := QuotientGroup.mk' N
  refine ⟨(T.subgroupOf H).map π, (A4.isPGroup_subgroupOf_of_le hTH hT).map π, ?_, ?_⟩
  · have hcomap : ((T.subgroupOf H).map π).comap π = T.subgroupOf H := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hNle
    rw [← Subgroup.index_comap_of_surjective _ (f := π) (QuotientGroup.mk'_surjective N), hcomap]
    exact hr
  · intro hbot
    have hle : T.subgroupOf H ≤ π.ker := Subgroup.map_eq_bot_iff _ |>.mp hbot
    rw [QuotientGroup.ker_mk'] at hle
    have hn : (T.subgroupOf H).Normal := (le_antisymm hle hNle) ▸ hNn
    exact hnn ((Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mp hn)

theorem lemma_14_3_5
    (h14220 : StageTheorem14220)
    (hSz : Nat.card ↥(CFSG.Open.Sz 0) = 20) (hSzO2 : CFSG.Open.pCore 2 ↥(CFSG.Open.Sz 0) = ⊥)
    {G : Type} [Group G] [Finite G] {T M : Subgroup G} (h : Hyp1421 G T M) (hnot : ¬ SixModels G)
    {H : Subgroup G} (hH : InH T H) (hidx : T.relIndex H = 3 ∨ T.relIndex H = 5) : H ≤ M := by
  by_contra hHM
  have hTM : T ≤ M := h.m_max.1.2
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hprime : (T.relIndex H).Prime := by
    rcases hidx with h3 | h5
    · rw [h3]; norm_num
    · rw [h5]; norm_num
  have hstar : IsHStar T M H := isHStar_of_relIndex_prime hTM hH hHM hprime rfl
  have hN : Subgroup.normalizer (T : Set G) ≤ M := h.normalizer_le.trans inf_le_left
  have hnn : ¬ H ≤ Subgroup.normalizer (T : Set G) := hstar.not_le_normalizer hN
  have hX2 := OTwoQuot.eq_bot_of_normal_of_isPGroup H
  obtain ⟨hDS, hPerm⟩ := h14220 G T M h H hstar
  rcases hidx with h3 | h5
  · obtain ⟨S, hS, hSi, hS1⟩ :=
      exists_isPGroup_index_quot_of_relIndex hH.1 hT2 h3 (by norm_num) hnn
    obtain ⟨e⟩ := nonempty_mulEquiv_perm_three hX2 hS hS1 hSi
    rcases hPerm ⟨e⟩ with hM12 | hU33
    · exact hnot ((sixModels_iff G).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hM12))))))
    · exact hnot ((sixModels_iff G).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU33))))))
  · obtain ⟨S, hS, hSi, hS1⟩ :=
      exists_isPGroup_index_quot_of_relIndex hH.1 hT2 h5 (by norm_num) hnn
    have htits : Nonempty (G ≃* quasithinTits) := by
      rcases nonempty_mulEquiv_dihedralGroup_five_or_card_twenty hX2 hS hS1 hSi with hD | hc
      · exact hDS (Or.inl hD)
      · have : Finite ↥(CFSG.Open.Sz 0) := Nat.finite_of_card_ne_zero (by rw [hSz]; norm_num)
        obtain ⟨e⟩ := nonempty_mulEquiv_of_card_twenty hX2
          (fun N hN hp => le_bot_iff.mp (hSzO2 ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)) hc hSz
        exact hDS (Or.inr ⟨e⟩)
    exact hnot ((sixModels_iff G).mpr (Or.inr (Or.inr (Or.inr (Or.inl htits)))))

end CFSG.Quasithin
