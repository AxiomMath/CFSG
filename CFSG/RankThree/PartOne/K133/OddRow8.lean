module

public import CFSG.RankThree.PartOne.K133.Weyl
public import CFSG.RankThree.PartOne.K133.Alpha
public import CFSG.RankThree.PartOne.K133.Basic
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem oddOrderOneOrThree_of_le {X : Type} [Group X] {Γ Δ : Subgroup X} (h : Γ ≤ Δ)
    (hΔ : OddOrderOneOrThree ↥Δ) : OddOrderOneOrThree ↥Γ := by
  intro x hx
  have := hΔ (Subgroup.inclusion h x) (by
    rwa [orderOf_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h) x])
  rwa [orderOf_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h) x] at this

theorem oddOrderOneOrThree_of_rowWeylIso {G : Type} [Group G] {X : Subgroup G}
    {Γ : Subgroup (MulAut X)} {r : ℕ} (hr1 : 1 ≤ r) (hr8 : r ≤ 8) (h : RowWeylIso X Γ r) :
    OddOrderOneOrThree ↥Γ := by
  have hD : ∀ (n a : ℕ) [NeZero n], 2 * n ∣ 2 ^ a * 3 → Nonempty (↥Γ ≃* DihedralGroup n) →
      OddOrderOneOrThree ↥Γ := by
    intro n a _ hdvd ⟨φ⟩
    exact OddOrderOneOrThree.of_mulEquiv φ.symm
      (OddOrderOneOrThree.of_card_dvd (a := a) (by rwa [DihedralGroup.nat_card]))
  interval_cases r
  · obtain ⟨φ⟩ := h
    exact OddOrderOneOrThree.of_mulEquiv φ.symm
      (OddOrderOneOrThree.of_card_dvd (a := 1) (by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]))
  · exact hD 6 2 (by norm_num) h
  · exact hD 6 2 (by norm_num) h
  · exact hD 8 4 (by norm_num) h
  · exact hD 4 3 (by norm_num) h
  · exact hD 4 3 (by norm_num) h
  · exact hD 4 3 (by norm_num) h
  · exact hD 4 3 (by norm_num) h

variable {G : Type} [Group G] [Finite G]

theorem oddOrderOneOrThree_of_zeroStar {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A) {J : Subgroup G}
    (hJ : J ∈ thetaCompZeroStarE p E) : OddOrderOneOrThree ↥(torusImage E J) := by
  obtain ⟨B, c', -, -, -, hH', hF'⟩ := hF13.reinstantiate J hJ
  obtain ⟨-, r, hr1, hr12, -, hW, -, hr9⟩ := hF'.three
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := hr9 (by omega)
    rw [hEA, h.A_card] at h4
    have hp := h.prime
    have h5 := Sec12Three.five_le h
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  exact oddOrderOneOrThree_of_rowWeylIso hr1 hr8 hW

theorem oddOrderOneOrThree_of_split (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) {t : MulAut E} (ht : t ∈ reflectionSet p E) {K : Subgroup G}
    (hK : IsKt p E t K) (hsplit : SplitType p K) (hmov : autMovedInG E t ≤ K) {e : G}
    (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e)
    (hKI : K ≤ I) : OddOrderOneOrThree ↥(torusImage E I) := by
  obtain ⟨J, hJ, hIJ⟩ := exists_zeroStar_of_split hS h hEA ht hK hsplit hmov he he1 hI hKI
  have heE : e ∈ E := (Subgroup.map_subtype_le _) he
  have hEI : E ≤ Subgroup.normalizer (I : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI
  obtain ⟨B, c', -, -, -, hH', hF'⟩ := hF13.reinstantiate J hJ
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) := normalizes_L hH' hF'
  exact oddOrderOneOrThree_of_le
    (torusImage_le_of_sectionTenRel h.prime h.E_elem heE hI hEI hEJ hIJ)
    (oddOrderOneOrThree_of_zeroStar h hF13 hEA hJ)

end CFSG.RankThree.PartOne.K133
