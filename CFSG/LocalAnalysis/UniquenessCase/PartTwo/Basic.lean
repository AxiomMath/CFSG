module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp125 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp123 D.M D.T V₀ V ∧
    ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M, CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀

theorem normalizer_eq_of_inCalV (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) :
    normalizer (V : Set G) = D.M := by
  obtain ⟨hVne, -, hMV, hE⟩ := hV
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by simpa using hE.2 (g : G) g.2)⟩
  exact CFSG.LocalAnalysis.RankThreeUC.normalizer_eq_of_isMaxTwoLocal D.maxLocal hVne hV2 hMV

theorem centralizer_le_of_inCalV (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) :
    centralizer (V : Set G) ≤ D.M := by
  rw [← normalizer_eq_of_inCalV D hV]
  exact Subgroup.centralizer_le_normalizer (V : Set G)

private theorem exists_isMaxTwoLocal_ge {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) :
    ∃ N : Subgroup G, CFSG.Open.rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  set S : Set (Subgroup G) := {N | CFSG.Open.IsTwoLocal N ∧ H ≤ N} with hS
  obtain ⟨N, ⟨hN, hHN⟩, hmax⟩ :=
    Set.exists_max_image S (fun N => Nat.card N) (Set.toFinite S) ⟨H, hH, le_rfl⟩
  refine ⟨N, ⟨hN, fun K hK hNK => ?_⟩, hHN⟩
  have hKS : K ∈ S := ⟨hK, hHN.trans hNK⟩
  exact (Subgroup.eq_of_le_of_card_ge hNK (hmax K hKS)).symm

theorem le_of_noncyclic_of_isTwoLocal (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X H : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X)
    (hH : CFSG.Open.IsTwoLocal H) (hXH : X ≤ H) : H ≤ D.M := by
  obtain ⟨N, hN, hHN⟩ := exists_isMaxTwoLocal_ge hH
  have hNmem : N ∈ calMOf X := ⟨hN, hXH.trans hHN⟩
  rw [h61 p hp X hXM hXp hXc] at hNmem
  have hNM : N = D.M := Set.mem_singleton_iff.mp hNmem
  exact hHN.trans (le_of_eq hNM)

theorem centralizer_le_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X) {x : G}
    (hx : x ≠ 1) (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1) (hXx : X ≤ centralizer ({x} : Set G)) :
    centralizer ({x} : Set G) ≤ D.M := by
  have hQne : Subgroup.zpowers x ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hx
  obtain ⟨n, hn⟩ := hx2
  have hQ2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hn)
  have hcent_eq : centralizer ({x} : Set G) = centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure x, Subgroup.centralizer_closure]
  have hcent_le : centralizer ({x} : Set G) ≤ normalizer (Subgroup.zpowers x : Set G) :=
    (le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)
  exact hcent_le.trans
    (le_of_noncyclic_of_isTwoLocal D h61 hp hXM hXp hXc
      ⟨Subgroup.zpowers x, hQne, hQ2, rfl⟩ (hXx.trans hcent_le))

theorem normalizer_le_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X Q : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X) (hQ : Q ≠ ⊥)
    (hQ2 : IsPGroup 2 Q) (hXQ : X ≤ normalizer (Q : Set G)) :
    normalizer (Q : Set G) ≤ D.M :=
  le_of_noncyclic_of_isTwoLocal D h61 hp hXM hXp hXc ⟨Q, hQ, hQ2, rfl⟩ hXQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
