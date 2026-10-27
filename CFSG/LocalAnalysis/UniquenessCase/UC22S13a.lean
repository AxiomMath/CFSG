module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847Four (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q →
    ∀ p ∈ D.sig, F08.Thin8 Y → normalizer (X : Set G) ≤ D.M

theorem r847Four_of_r847 (D : Data G) (h847 : F08.R847 D) (he : 3 < evenRank G) :
    R847Four D := by
  intro Y hY X hXY q hq hq2 hXq p hp hthin
  rcases h847 Y hY X hXY q hq hq2 hXq p hp (Or.inl hthin) with h1 | h2 | h3
  · exact h1
  · obtain ⟨_, _, _, _, _, he3, _⟩ := h2
    omega
  · obtain ⟨_, _, _, _, _, he3, _⟩ := h3
    omega

private theorem uc22s13a_map_conj_self {M : Subgroup G} {m : G} (hm : m ∈ M) :
    M.map (MulAut.conj m).toMonoidHom = M := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hm hy) (M.inv_mem hm)
  · intro hx
    exact ⟨m⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm, by group⟩

private theorem uc22s13a_map_conj_map_conj (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

private theorem uc22s13a_conj_mem_uniqueSet {M X : Subgroup G} (hX : X ∈ uniqueSet M) {m : G}
    (hm : m ∈ M) : X.map (MulAut.conj m).toMonoidHom ∈ uniqueSet M := by
  have hmM := uc22s13a_map_conj_self hm
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← hmM]
    exact Subgroup.map_mono hX.1
  · have hXle : X ≤ M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
      have h1 := Subgroup.map_mono (f := (MulAut.conj m⁻¹).toMonoidHom) hg
      rw [uc22s13a_map_conj_map_conj, uc22s13a_map_conj_map_conj, inv_mul_cancel] at h1
      have h2 : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
        ext x
        simp
      rwa [h2] at h1
    have h3 := hX.2 (m⁻¹ * g) hXle
    rw [show g = m * (m⁻¹ * g) by group, ← uc22s13a_map_conj_map_conj, h3, hmM]

private theorem uc22s13a_ne_two {s r : ℕ} (hs : Odd s) (hrs : r ∣ 2 ^ s - 1) : r ≠ 2 := by
  rintro rfl
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact (by decide : ¬ Odd 0) hs
  have h2 : 2 ∣ 2 ^ s := dvd_pow_self 2 hs0
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  omega

theorem uc22s13a_thin8_of_isL2_or_isSz {L : Subgroup G} {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : F08.Thin8 L := by
  intro p hp hp2
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact pRank_le_one_of_isL2_or_isSz hshape hp hp2

theorem uc22s13a_exists_torus {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hLn : (L.subgroupOf D.M).Normal) {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s : ℕ} (hs : Odd s) (hsn : s ∣ n) {r : ℕ}
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ X₀ : Subgroup G, X₀ ≤ L ∧ Nat.card X₀ = r ∧ X₀ ≤ normalizer (D.T : Set G) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hMN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hT : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hMN
  have hS : IsSylowOf 2 (D.T ⊓ L) L := D.sylowM.inf_of_le_normalizer hLM hMN
  obtain ⟨x, hxL, hxo, hxN⟩ : ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (D.T : Set G) := by
    rcases hshape with hL2 | hSz
    · exact uc22ine229_exists_mem_normalizer_of_isL2 hT hTL hS hL2 hs hsn hr hrs
    · exact uc22ine229_exists_mem_normalizer_of_isSz hT hTL hS hSz hs hsn hr hrs
  exact ⟨zpowers x, (zpowers_le).2 hxL, by rw [Nat.card_zpowers, hxo], (zpowers_le).2 hxN⟩

theorem uc22s13a_not_mem_uniqueSet {D : Data G}
    {Ch : Choice2011 G} (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hLn : (L.subgroupOf D.M).Normal) {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s : ℕ} (hs : Odd s) (hsn : s ∣ n) {r : ℕ}
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {X : Subgroup G} (hXL : X ≤ L) (hXr : Nat.card X = r) :
    X ∉ uniqueSet D.M := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hr2 : r ≠ 2 := uc22s13a_ne_two hs hrs
  obtain ⟨X₀, hX₀L, hX₀r, hX₀N⟩ := uc22s13a_exists_torus hL hLn hshape hs hsn hr hrs
  have hX₀U : X₀ ∉ uniqueSet D.M :=
    not_mem_uniqueSet_of_le_normalizer D Ch h211 h1930 c (by rwa [hX₀r])
      (by rw [hX₀r]; exact hr.odd_of_ne_two hr2) (hX₀L.trans hLM) hX₀N
  haveI : Fact r.Prime := ⟨hr⟩
  have hrank : CFSG.Open.pRank r L ≤ 1 := uc22s13a_thin8_of_isL2_or_isSz hshape r hr hr2
  obtain ⟨h, hhL, hh⟩ := exists_mem_map_conj_eq_of_card_eq_prime hrank hXL hX₀L hXr hX₀r
  intro hXU
  exact hX₀U (hh ▸ uc22s13a_conj_mem_uniqueSet hXU (hLM hhL))

theorem uc22s13a_hyp131_3 {D : Data G} {Ch : Choice2011 G}
    (h847 : R847Four D) (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hsig : D.sig.Nonempty) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hLn : (L.subgroupOf D.M).Normal) {n : ℕ} (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {s : ℕ} (hs : Odd s) (hsn : s ∣ n) {r : ℕ} (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    {X : Subgroup G} (hXL : X ≤ L) (hXr : Nat.card X = r) :
    normalizer (X : Set G) ≤ D.M ∧ X ∉ uniqueSet D.M := by
  obtain ⟨p, hp⟩ := hsig
  exact ⟨h847 L hL X hXL r hr (uc22s13a_ne_two hs hrs) hXr p hp
      (uc22s13a_thin8_of_isL2_or_isSz hshape),
    uc22s13a_not_mem_uniqueSet h211 h1930 c hL hLn hshape hs hsn hr hrs hXL hXr⟩

theorem uc22s13a_hyp131_uniq {D : Data G} {Ch : Choice2011 G}
    (h847 : R847Four D) (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hsig : D.sig.Nonempty) (hnormal : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) :
    ∀ L ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
      ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
        ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
          normalizer (X : Set G) ≤ D.M ∧ X ∉ uniqueSet D.M :=
  fun L hL _ hshape _ hs hsn _ hr hrs _ hXL hXr =>
    uc22s13a_hyp131_3 h847 h211 h1930 c hsig hL (hnormal L hL) hshape hs hsn hr hrs hXL hXr

end CFSG.LocalAnalysis.UniquenessCase.UC22
