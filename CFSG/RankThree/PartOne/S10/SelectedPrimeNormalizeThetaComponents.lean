module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.GroupTheory.SteinbergBKPrimeElementsFixQuotientComponents
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S10.SelectedPrimeFixCoprimeQuotientComponents
import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank

namespace SelectedPrimeTheta

open CFSG.RankThree.GroupTheory.SteinbergBK in
theorem pElement_normalizes_quotient_component {H : Type} [Group H] [Finite H]
    (he : evenRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {x : H}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) {J : Subgroup (H ⧸ aschbacherSolvableCore p H)}
    (hJ : IsComponent J) :
    (x : H ⧸ aschbacherSolvableCore p H) ∈
      Subgroup.normalizer (J : Set (H ⧸ aschbacherSolvableCore p H)) := by
  have hNcop : ¬ p ∣ Nat.card (aschbacherSolvableCore p H) :=
    (solvable_prime_complement_core_characterization hp).2.2.1
  have hp2 : p ≠ 2 := by omega
  by_cases hdvd : p ∣ Nat.card (J ⧸ Subgroup.center J)
  · have hrank : localRank p H ≤ 3 :=
      (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans he
    exact (selected_prime_elements_fix_prime_divisible_quotient_components
      hp hp3 _ hNcop hrank hJ hdvd).1 x hx
  · exact selected_prime_elements_fix_coprime_quotient_components H he p hp hp3 _ hNcop x hx J hJ
      hdvd

end SelectedPrimeTheta

open SelectedPrimeTheta

theorem selected_prime_elements_normalize_theta_components :
    SelectedPrimeElementsNormalizeThetaComponents := by
  have hpart1 : ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
      ∀ x : H, (∃ k : ℕ, orderOf x = p ^ k) → ∀ L ∈ thetaComponents p H,
        x ∈ Subgroup.normalizer (L : Set H) := by
    intro H _ _ he p hp hp3 x hx L hL
    have hJ := isComponent_map_of_mem_thetaComponents hp hL
    have hxJ := pElement_normalizes_quotient_component he hp hp3 hx hJ
    obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) hp
    obtain ⟨-, hequi⟩ := theta_component_quotient_correspondence_equivariant (H := H) hp
    have hτ : ∀ h : H, (MulAut.conj (x : H ⧸ aschbacherSolvableCore p H))
        (QuotientGroup.mk' (aschbacherSolvableCore p H) h) =
        QuotientGroup.mk' (aschbacherSolvableCore p H) ((MulAut.conj x) h) := fun h => by
      simp [MulAut.conj_apply]
    obtain ⟨hmem, himg⟩ := (hequi (MulAut.conj x) (MulAut.conj (x : H ⧸ aschbacherSolvableCore p H))
      hτ).1 L hL
    have himg' : (L.map (MulAut.conj x).toMonoidHom).map
        (QuotientGroup.mk' (aschbacherSolvableCore p H)) =
        L.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) := by
      rw [himg]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxJ
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hbij.injOn hmem hL himg')
  refine ⟨hpart1, ?_⟩
  intro G _ _ he p hp hp3 A hA L hL
  obtain ⟨a, ⟨haA, ha1⟩, hLa⟩ := Set.mem_iUnion₂.mp hL
  obtain ⟨L₀, hL₀, rfl⟩ := hLa
  have := hA
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : A) ⟨y, hy⟩)
  have hord : ∃ k : ℕ, orderOf (⟨y, hyC⟩ : Subgroup.centralizer ({a} : Set G)) = p ^ k := by
    have hy1 : y ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) y hy
    have hdvd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (pow_one p ▸ hdvd)
    exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩
  have hxn := hpart1 ↥(Subgroup.centralizer ({a} : Set G))
    ((Sec9A.evenRank_subgroup_le (Subgroup.centralizer ({a} : Set G))).trans he) p hp hp3
    ⟨y, hyC⟩ hord L₀ hL₀
  exact Subgroup.le_normalizer_map (Subgroup.centralizer ({a} : Set G)).subtype
    (Subgroup.mem_map_of_mem _ hxn)

end CFSG.RankThree.PartOne
