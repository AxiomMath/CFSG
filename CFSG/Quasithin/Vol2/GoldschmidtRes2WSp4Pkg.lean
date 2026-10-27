module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CK
public import CFSG.Quasithin.Vol2.Ch3E213MP6D2
public import CFSG.Quasithin.Vol2.Ch3E213MP6EJ
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WPkgDefs
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WPair

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M
open CFSG.Quasithin.SteinbergBS (rootLong)

@[expose] def Sp4MemberE215W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (g : G) (F₀ : Type) [Field F₀]
    [Finite F₀] [CharP F₀ 2], Sp4Member H T M V g F₀ → E215ConclW H T M V

@[expose] def PkgSp4C2215W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) →
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ), 2 ≤ n → Nat.card k = 2 ^ n →
    ∀ D : Sp4Data H T M V K k, coordIn D.θ V ⊓ rootLong k = ⊥ →
    (∀ μ : k, μ ≠ 0 → ¬ coordIn D.θ V ≤ zLine 1 μ) → E215ConclW H T M V

theorem pkgSp4215W_of
    (hIrr : IrrStatement)
    (hG41 : FactSp4TransvW) (hE : Sp4MemberE215W) (h4 : PkgSp4C2215W) : PkgSp4215W := by
  intro G _ _ H T M V K hS h2 n hn hSp hD hB
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    obtain ⟨g, hg⟩ := member_sp4One hS h2 hSp hD hB
    exact hE G H T M V g (ZMod 2) hg
  · obtain ⟨k, _, _, _, hk, ⟨D⟩⟩ := exists_sp4Data hS h2 hge hSp
    by_cases hdiag : ∃ μ : k, μ ≠ 0 ∧ coordIn D.θ V ≤ zLine 1 μ
    · obtain ⟨μ, hμ, hle⟩ := hdiag
      obtain ⟨T', hT', hP⟩ := P6D.pair_of_sp4Diag hS hk D hμ hle
      exact e215ConclW_of_pair hS hT' hP
    · push Not at hdiag
      by_cases hl : coordIn D.θ V ⊓ rootLong k = ⊥
      · exact h4 G H T M V K hS h2 hD hB k n hge hk D hl hdiag
      · obtain ⟨g, F₀, hg⟩ := exists_sp4Member_of_transv hIrr hG41 hS hB hk D hl
        exact hE G H T M V g ↥F₀ hg

end CFSG.Quasithin.Res2
