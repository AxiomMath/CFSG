module

public import CFSG.RankThree.PartOne.K1327.FrameL
public import CFSG.RankThree.PartOne.K1327.Comp

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A L E : Subgroup G} {f : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem claimA_frame (hp : p.Prime) (fr : Row8Frame p A L E f K) {c : G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hZ : Subgroup.center L = ⊥)
    {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) {J V : Subgroup G}
    (hVJ : ∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V) (hVs : Group.IsSolvable ↥V)
    (hcop : ¬ p ∣ Nat.card V) (hK₀J : kZero p E fr.r₀ ≤ J) (hK₀'J : kZero p E fr.r₀' ≤ J)
    (hkz₀ : kZero p E fr.r₀ = fr.lft (slB K 0 1))
    (hkz₀' : kZero p E fr.r₀' = fr.lft (slB K 2 3))
    {e : G} (heJ : e ∈ J) (heA : e ∈ A) (heL : e ∈ L) (hep : e ^ p = 1)
    (heR : ∀ x ∈ fr.lft (Rr K r), e * x = x * e) {u : G} (huV : u ∈ V) (huc : u * c = c * u)
    (huR : ∀ x ∈ fr.lft (Rr K r), u * x = x * u) : Commute u e := by
  have hLmem : L ∈ thetaComponentsAt p c := h.L_mem.2
  obtain ⟨hLY, hLm⟩ := mem_thetaComponentsAt_iff.1 hLmem
  have hcomp : IsComponent (L.subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm
      hF.isQuasisimple_L, hLm.2.1⟩
  have hR1 : fr.lft (Rr K r) ≠ ⊥ := by
    intro h0
    have hcard : Nat.card (fr.lft (Rr K r)) = r := by
      rw [fr.lft_card hZ]
      exact rootsOfUnity_card hr hrq
    rw [h0, Subgroup.card_bot] at hcard
    exact hr.one_lt.ne hcard
  have hK₀q := (KFAt.toLiftAt fr.kf₀)
  have hK₀'q := (KFAt.toLiftAt fr.kf₀')
  have huY : u ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact huc
  refine commute_of_block_data hp hLY hcomp (fr.lft_le _) hR1 hZ hVJ hVs hcop hK₀J hK₀'J
    hK₀q.1 hK₀'q.1 hK₀q.2.1 hK₀'q.2.1 ?_ ?_ heJ heL hep heR ?_ huV huY huR
  · intro n hn hnR k hk
    rw [hkz₀] at hk ⊢
    exact (conj_normalizes fr hr hrq hn hnR).1 k hk
  · intro n hn hnR k hk
    rw [hkz₀'] at hk ⊢
    exact (conj_normalizes fr hr hrq hn hnR).2 k hk
  · intro n hn h1 h2
    rw [hkz₀] at h1
    rw [hkz₀'] at h2
    exact commute_of_centralizes_blocks fr hZ hn h1 h2 e ⟨heA, heL⟩

end CFSG.RankThree.PartOne.K1327
