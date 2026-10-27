module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem Sec12Hyp.A_elem (h : Sec12Hyp G p A c L E) : IsElementaryAbelian p A :=
  h.setup.2.2.2.2.2.2.1

theorem Sec12Hyp.A_card (h : Sec12Hyp G p A c L E) : Nat.card A = p ^ 3 :=
  h.setup.2.2.2.2.2.2.2.1

theorem Sec12Hyp.prime (h : Sec12Hyp G p A c L E) : p.Prime :=
  sectionTenSetup_prime h.setup

theorem Sec12Hyp.three_lt (h : Sec12Hyp G p A c L E) : 3 < p :=
  sectionTenSetup_three_lt h.setup

theorem Sec12Hyp.evenRank_eq (h : Sec12Hyp G p A c L E) : evenRank G = 3 :=
  sectionTenSetup_evenRank_eq h.setup

theorem Sec12Hyp.A_le_E (h : Sec12Hyp G p A c L E) : A ≤ E := by
  have hA := h.A_elem
  have hE := h.E_elem
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun a ha b hb =>
    congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hAE : A ≤ Subgroup.centralizer (E : Set G) := fun a ha e he =>
    (Subgroup.mem_centralizer_iff.mp (h.E_le he) a ha).symm
  have hF : IsElementaryAbelian p ↥(E ⊔ A) := IsElementaryAbelian.sup_of_le_centralizer hAE
  have heq := h.E_max (E ⊔ A) hF (sup_le h.E_le hAC) le_sup_left
  exact heq ▸ le_sup_right

theorem Sec12Hyp.E_max_global (h : Sec12Hyp G p A c L E) (F : Subgroup G)
    (hF : IsElementaryAbelian p F) (hEF : E ≤ F) : F = E := by
  refine h.E_max F hF (fun x hx a ha => ?_) hEF
  exact congrArg Subtype.val (hF.is_comm.comm ⟨a, hEF (h.A_le_E ha)⟩ ⟨x, hx⟩)

theorem Sec12Hyp.pow_three_dvd_card_E (h : Sec12Hyp G p A c L E) : p ^ 3 ∣ Nat.card E := by
  rw [← h.A_card]
  exact Subgroup.card_dvd_of_le h.A_le_E

theorem Sec12Hyp.E_normalizes_thetaComponentsAt (h : Sec12Hyp G p A c L E)
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents) {e : G} (he : e ∈ E)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p e) : E ≤ Subgroup.normalizer (Y : Set G) := by
  have hEel := h.E_elem
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsAt_iff.mp hY
  have hecomm : ∀ x ∈ E, x ∈ Subgroup.centralizer ({e} : Set G) := fun x hx y hy => by
    rw [Set.mem_singleton_iff.mp hy]
    exact congrArg Subtype.val (hEel.is_comm.comm ⟨e, he⟩ ⟨x, hx⟩)
  have hH : evenRank (Subgroup.centralizer ({e} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  intro x hx
  have hxp : (⟨x, hecomm x hx⟩ : Subgroup.centralizer ({e} : Set G)) ^ p = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hord : ∃ k : ℕ, orderOf (⟨x, hecomm x hx⟩ : Subgroup.centralizer ({e} : Set G)) = p ^ k := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow h.prime).mp
      (show orderOf (⟨x, hecomm x hx⟩ : Subgroup.centralizer ({e} : Set G)) ∣ p ^ 1 from by
        rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hxp)
    exact ⟨k, hk⟩
  have hmem := hnorm.1 (Subgroup.centralizer ({e} : Set G)) hH p h.prime h.three_lt _ hord _ hY'
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ Subgroup.centralizer ({e} : Set G)
  · have := Subgroup.mem_normalizer_iff.mp hmem ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY
      exact absurd (hYC hgY) hg
    · intro hxgY
      have h1 : x * g * x⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := hYC hxgY
      have hxC := hecomm x hx
      refine absurd ?_ hg
      have h2 := mul_mem (mul_mem (inv_mem hxC) h1) hxC
      simpa [mul_assoc] using h2

theorem Sec12Hyp.reinstantiate (h : Sec12Hyp G p A c L E) {B : Subgroup G}
    (hB : B ∈ admissibleTriples p E) {c' : G} (hc'B : c' ∈ B) (hc' : c' ≠ 1)
    {L' : Subgroup G}
    (hL' : L' ∈ sectionTenAt p (sectionTenZeroStar p B ∩ sectionTenOne p B) c') :
    Sec12Hyp G p B c' L' E := by
  obtain ⟨hBE, hBel, hBcard, S, hS1, hS2, hBS⟩ := hB
  obtain ⟨hsimple, hnonab, hK, hchar, he, hQ, -, -, -, hpref⟩ := h.setup
  refine ⟨⟨hsimple, hnonab, hK, hchar, he, hQ, hBel, hBcard, ⟨S, hS1, hS2, hBS⟩, hpref⟩, hc'B,
    hc', hL', h.E_elem, fun x hx b hb => ?_, fun F hF _ hEF => h.E_max_global F hF hEF⟩
  exact congrArg Subtype.val (h.E_elem.is_comm.comm ⟨b, hBE hb⟩ ⟨x, hx⟩)

end CFSG.RankThree.PartOne
