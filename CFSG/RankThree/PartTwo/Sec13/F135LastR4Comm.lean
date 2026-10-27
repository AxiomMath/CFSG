module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13

theorem r4_comm_comm {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A₀ B₀ : Subgroup G} (hA₀ : IsPGroup 2 A₀) (hB₀ : IsPGroup p B₀)
    (hBA : B₀ ≤ Subgroup.normalizer (A₀ : Set G)) : ⁅⁅A₀, B₀⁆, B₀⁆ = ⁅A₀, B₀⁆ := by
  refine CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hB₀ hBA ?_
  intro hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA₀
  rw [hn] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem r4b_cent_sup {G : Type} [Group G] {u f : G} {Y : Subgroup G}
    (hf : f ∈ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)) :
    f ∈ Subgroup.centralizer (Y : Set G) ∧ f ∈ Subgroup.centralizer ({u} : Set G) := by
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_,
    Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  · exact Subgroup.mem_centralizer_iff.mp hf y ((le_sup_left : Y ≤ Y ⊔ Subgroup.zpowers u) hy)
  · rw [Set.mem_singleton_iff.mp hk]
    exact Subgroup.mem_centralizer_iff.mp hf u
      ((le_sup_right : Subgroup.zpowers u ≤ Y ⊔ Subgroup.zpowers u) (Subgroup.mem_zpowers u))

theorem r4b_B_le_normalizer {G : Type} [Group G] [Finite G] {u : G} {Y D : Subgroup G} :
    D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact r5gl_A_conj hb hn
  · intro hn
    have h := r5gl_A_conj (inv_mem hb) hn
    have e : b⁻¹ * (b * n * b⁻¹) * b⁻¹⁻¹ = n := by group
    rw [e] at h
    exact h

theorem r4_U_comm {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : G} {Y D U : Subgroup G} (hD : IsPGroup p D)
    (hU : U = ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G),
      D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)⁆) :
    ⁅U, D ⊓ cM Y ⊓ Subgroup.centralizer ({u} : Set G)⁆ = U := by
  subst hU
  have hcomm : D ⊓ cM Y ⊓ Subgroup.centralizer ({u} : Set G) =
      D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
    ext f
    constructor
    · intro hf
      exact r5gl_S_le_B hf
    · intro hf
      obtain ⟨hfD, hfC⟩ := Subgroup.mem_inf.mp hf
      obtain ⟨hfY, hfu⟩ := r4b_cent_sup hfC
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hfD, hfY⟩, hfu⟩
  have hA₀ : IsPGroup 2 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓
      Subgroup.centralizer (Y : Set G) : Subgroup G) :=
    (CFSG.RankThree.PartTwo.Sec13.F135Last.isPGroup_pCoreOf 2
      (Subgroup.centralizer ({u} : Set G))).to_inf_left
  have hB₀ : IsPGroup p (D ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) :
      Subgroup G) :=
    hD.to_le inf_le_left
  rw [hcomm]
  exact r4_comm_comm hp hp2 hA₀ hB₀ r4b_B_le_normalizer

theorem r4_map_comm {G : Type*} [Group G] (M : Subgroup G) (R : Subgroup M) [R.Normal]
    {U B : Subgroup G} (hUM : U ≤ M) (hBM : B ≤ M) (h : ⁅U, B⁆ = U) :
    (U.subgroupOf M).map (QuotientGroup.mk' R) =
      ⁅(U.subgroupOf M).map (QuotientGroup.mk' R), (B.subgroupOf M).map (QuotientGroup.mk' R)⁆ := by
  have hcomm : ⁅U.subgroupOf M, B.subgroupOf M⁆ = U.subgroupOf M := by
    refine Subgroup.map_injective M.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUM,
      Subgroup.map_subgroupOf_eq_of_le hBM, h]
  calc (U.subgroupOf M).map (QuotientGroup.mk' R)
      = (⁅U.subgroupOf M, B.subgroupOf M⁆).map (QuotientGroup.mk' R) := by rw [hcomm]
    _ = ⁅(U.subgroupOf M).map (QuotientGroup.mk' R), (B.subgroupOf M).map (QuotientGroup.mk' R)⁆ :=
      Subgroup.map_commutator (U.subgroupOf M) (B.subgroupOf M) (QuotientGroup.mk' R)

end CFSG.RankThree.PartTwo.Sec13.F135Last
