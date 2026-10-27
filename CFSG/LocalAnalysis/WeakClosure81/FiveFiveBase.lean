module

public import CFSG.LocalAnalysis.WeakClosure81.FiveKer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_or_eq_of_maxOver_eq_singleton {H M A K : Subgroup G} (hM : maxOver H A = {M})
    (hKH : K ≤ H) (hAK : A ≤ K) : K ≤ M ∨ K = H := by
  by_cases hK : K = H
  · exact Or.inr hK
  · left
    have hlt : K < H := lt_of_le_of_ne hKH hK
    obtain ⟨N, hNmax, hKN⟩ := exists_isMaxSubgroupIn hlt
    have hN : N ∈ maxOver H A := ⟨hNmax, hAK.trans hKN⟩
    rw [hM] at hN
    rw [Set.mem_singleton_iff] at hN
    exact hKN.trans_eq hN

theorem exists_mul_of_eq_sup_of_normal {H X A : Subgroup G} (hXH : X ≤ H) (hAH : A ≤ H)
    (hX : (X.subgroupOf H).Normal) (hH : H = X ⊔ A) {g : G} (hg : g ∈ H) :
    ∃ a ∈ A, ∃ x ∈ X, g = a * x := by
  haveI : (X.subgroupOf H).Normal := hX
  have hg' : (⟨g, hg⟩ : ↥H) ∈ X.subgroupOf H ⊔ A.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hXH hAH, Subgroup.mem_subgroupOf]
    exact hH ▸ hg
  have hmem : (⟨g, hg⟩ : ↥H) ∈ A.subgroupOf H ⊔ X.subgroupOf H := by
    rw [sup_comm]
    exact hg'
  rw [Subgroup.mem_sup_of_normal_right] at hmem
  obtain ⟨a, ha, x, hx, hax⟩ := hmem
  refine ⟨(a : G), ha, (x : G), hx, ?_⟩
  have hval := congrArg (Subtype.val) hax
  simpa using hval.symm

theorem pCoreOf_two_eq_bot_of_maxOver_eq_singleton {H M A : Subgroup G} (h : Sec5Hyp H M A)
    (hM : maxOver H A = {M}) (hK : kerMOf M H = ⊥) : pCoreOf 2 H = ⊥ := by
  have hQH : pCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
  have hQnorm : ((pCoreOf 2 H).subgroupOf H).Normal := by
    change (((pCore 2 ↥H).map H.subtype).comap H.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact pCore_normal
  have hA2 : IsPGroup 2 A := h.isElemAbelian.isPGroup
  obtain ⟨T, hTsyl, hAT⟩ := B6.exists_isSylowTwoOf_ge hA2 h.le_group
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hTM : T ≤ M := by
    rcases le_or_eq_of_maxOver_eq_singleton hM hTsyl.1 hAT with hle | heq
    · exact hle
    · exfalso
      have hH2 : IsPGroup 2 ↥H := by
        have hT2 := hTsyl.2.1
        rwa [heq] at hT2
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH2
      have hdiv : M.relIndex H ∣ Nat.card ↥H := Subgroup.relIndex_dvd_card M H
      rw [hn] at hdiv
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
      have hk0 : k = 0 := by
        by_contra hkne
        have hev : Even (M.relIndex H) := by
          rw [hk]
          exact Nat.even_pow.mpr ⟨even_two, hkne⟩
        exact (Nat.not_even_iff_odd.mpr h.odd_relIndex) hev
      have hrel1 : M.relIndex H = 1 := by rw [hk, hk0, pow_zero]
      exact h.not_le ((Subgroup.relIndex_eq_one).1 hrel1)
  have hQM : pCoreOf 2 H ≤ M := hQT.trans hTM
  have hle := le_kerMOf_of_normal hQH hQnorm hQM
  rw [hK] at hle
  exact le_bot_iff.mp hle

theorem le_pCoreOf_of_isPGroup_of_normal {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hp' : IsPGroup p ↥(N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.pCore p ↥H :=
    le_sSup ⟨hN, hp'⟩
  calc N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ (CFSG.pCore p ↥H).map H.subtype := Subgroup.map_mono hle
    _ = pCoreOf p H := rfl

theorem exists_isMinNormalOver {H Y : Subgroup G} (hYH : Y < H) (hY : (Y.subgroupOf H).Normal) :
    ∃ X : Subgroup G, IsMinNormalOver H Y X := by
  let S : Set (Subgroup G) := {Z | Y < Z ∧ Z ≤ H ∧ (Z.subgroupOf H).Normal}
  have hHS : H ∈ S := by
    refine ⟨hYH, le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  obtain ⟨X, hXS, hXmin⟩ := (Set.toFinite S).exists_minimal ⟨H, hHS⟩
  refine ⟨X, hXS.1, hXS.2.1, hXS.2.2, ?_⟩
  intro Z hYZ hZX hZN
  by_cases hZY : Z = Y
  · exact Or.inl hZY
  · exact Or.inr (le_antisymm hZX
      (hXmin ⟨lt_of_le_of_ne hYZ (Ne.symm hZY), hZX.trans hXS.2.1, hZN⟩ hZX))

end CFSG.LocalAnalysis.WeakClosure81
