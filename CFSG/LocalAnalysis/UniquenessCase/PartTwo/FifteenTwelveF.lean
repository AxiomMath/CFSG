module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_Twelve_conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup _ _ _

private theorem s15_Twelve_conj_mem_wConj {D : Data G} {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) {r : G}
    (hr : r ∈ D.M) : conjSubgroup X r ∈ wConj D.M V₀ V hV L := by
  obtain ⟨m, hm, rfl⟩ := hX
  exact ⟨m * r, D.M.mul_mem hm hr, by rw [conjSubgroup_conjSubgroup]⟩

theorem s15_Twelve_exists_inner (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn : n ≤ 2) (hγ : gamma15 D.M V₀ V hV L = n + 1)
    (hs : s15 D.M V₀ V hV L = 3) :
    ∃ Z ∈ wConj D.M V₀ V hV L, conjSubgroup (fSub15 D.M V₀ V hV L Z) k⁻¹ ≤ D.M := by
  have hP2 : IsPGroup 2 (conjSubgroup V k⁻¹ ⊓ D.M : Subgroup G) :=
    (E3.isPGroup_conjSubgroup hV.isPGroup k⁻¹).to_le inf_le_left
  have hPM : conjSubgroup V k⁻¹ ⊓ D.M ≤ D.M := inf_le_right
  have hPexists : ∃ X ∈ wConj D.M V₀ V hV L,
      conjSubgroup V k⁻¹ ⊓ D.M ≤ normalizer (X : Set G) := by
    by_contra hno
    have h' : ∀ X ∈ wConj D.M V₀ V hV L,
        ¬ conjSubgroup V k⁻¹ ⊓ D.M ≤ normalizer (X : Set G) :=
      fun X hX hle => hno ⟨X, hX, hle⟩
    have heven := s15_Glue3_even_of_no_fixed D h.hyp151 hV hP2 hPM h'
    rw [hs] at heven
    obtain ⟨m, hm⟩ := heven
    omega
  obtain ⟨X₀, hX₀, hPX₀⟩ := hPexists
  have hPV₁ : conjSubgroup V k⁻¹ ⊓ D.M ≤
      normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    hPM.trans (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)
  have hPX₀F : conjSubgroup V k⁻¹ ⊓ D.M ≤
      normalizer (fSub15 D.M V₀ V hV L X₀ : Set G) :=
    (le_inf hPX₀ hPV₁).trans (inf_normalizer_le_normalizer_sup X₀ (v1Sub D.M V₀ V hV L))
  have hc_le : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X₀ k : Set G)) ≤ n :=
    (s15_Twelve_rank_bound D h hV hk hX₀).2 (Or.inr hPX₀F)
  have hnγ : n < gamma15 D.M V₀ V hV L := by omega
  have hcγ : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X₀ k : Set G)) <
      gamma15 D.M V₀ V hV L := by omega
  have hcard := s15_Twelve_card_le D h1217 h hV hL hk hnγ hX₀ hcγ
  have hex : ∃ Z ∈ wConj D.M V₀ V hV L, fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k := by
    by_contra hno
    have hall : {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
        ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k} = wConj D.M V₀ V hV L := by
      ext Z
      constructor
      · rintro ⟨hZ, -⟩
        exact hZ
      · intro hZ
        exact ⟨hZ, fun hle => hno ⟨Z, hZ, hle⟩⟩
    rw [hall, ncard_wConj D h.hyp151 hV] at hcard
    rw [hs] at hcard
    omega
  obtain ⟨Z, hZ, hZle⟩ := hex
  refine ⟨Z, hZ, ?_⟩
  have h1 := E3.conjSubgroup_mono_left k⁻¹ hZle
  rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h1

theorem s15_Twelve_normalizes_all (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn : n ≤ 2) (hγ : gamma15 D.M V₀ V hV L = n + 1)
    (hs : s15 D.M V₀ V hV L = 3) {Z₁ : Subgroup G} (hZ₁ : Z₁ ∈ wConj D.M V₀ V hV L)
    (hin : conjSubgroup (fSub15 D.M V₀ V hV L Z₁) k⁻¹ ≤ D.M)
    (hR : ¬ conjSubgroup V k ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L Z₁ : Set G)) :
    (∀ X ∈ wConj D.M V₀ V hV L,
      conjSubgroup V k⁻¹ ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L X : Set G)) ∧
    ∃ X₃ ∈ wConj D.M V₀ V hV L,
      conjSubgroup V k ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L X₃ : Set G) := by
  have hR'2 : IsPGroup 2 (conjSubgroup V k ⊓ D.M : Subgroup G) :=
    (E3.isPGroup_conjSubgroup hV.isPGroup k).to_le inf_le_left
  have hR'M : conjSubgroup V k ⊓ D.M ≤ D.M := inf_le_right
  have hR'V₁ : conjSubgroup V k ⊓ D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    hR'M.trans (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)
  have hnotN : ¬ conjSubgroup V k ⊓ D.M ≤ normalizer (Z₁ : Set G) := by
    intro hN
    exact hR ((le_inf hN hR'V₁).trans
      (inf_normalizer_le_normalizer_sup Z₁ (v1Sub D.M V₀ V hV L)))
  have hexr : ∃ r ∈ conjSubgroup V k ⊓ D.M, conjSubgroup Z₁ r ≠ Z₁ := by
    by_contra hno
    apply hnotN
    intro r hr
    by_contra hne
    exact hno ⟨r, hr, fun heq => hne (conjSubgroup_eq_iff_mem_normalizer.mp heq)⟩
  obtain ⟨r, hr, hrne⟩ := hexr
  have hrM : r ∈ D.M := hr.2
  have hrV : r ∈ conjSubgroup V k := hr.1
  set Z₂ : Subgroup G := conjSubgroup Z₁ r with hZ₂def
  have hZ₂ne : Z₂ ≠ Z₁ := by rw [hZ₂def]; exact hrne
  have hZ₂mem : Z₂ ∈ wConj D.M V₀ V hV L := s15_Twelve_conj_mem_wConj hV hZ₁ hrM
  have hWexists : ∃ W ∈ wConj D.M V₀ V hV L,
      conjSubgroup V k ⊓ D.M ≤ normalizer (W : Set G) := by
    by_contra hno
    have h' : ∀ X ∈ wConj D.M V₀ V hV L,
        ¬ conjSubgroup V k ⊓ D.M ≤ normalizer (X : Set G) :=
      fun X hX hle => hno ⟨X, hX, hle⟩
    have heven := s15_Glue3_even_of_no_fixed D h.hyp151 hV hR'2 hR'M h'
    rw [hs] at heven
    obtain ⟨m, hm⟩ := heven
    omega
  obtain ⟨W, hWmem, hWN⟩ := hWexists
  have hWne₁ : W ≠ Z₁ := fun heq => hnotN (heq ▸ hWN)
  have hWne₂ : W ≠ Z₂ := by
    intro heq
    have hrinv : r⁻¹ ∈ conjSubgroup V k ⊓ D.M :=
      ⟨(conjSubgroup V k).inv_mem hrV, D.M.inv_mem hrM⟩
    have hfix : conjSubgroup Z₂ r⁻¹ = Z₂ := by
      rw [← heq]
      exact conjSubgroup_eq_iff_mem_normalizer.mpr (hWN hrinv)
    have h1 : conjSubgroup Z₂ r⁻¹ = Z₁ := by
      rw [hZ₂def, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [h1] at hfix
    exact hZ₂ne hfix.symm
  have hFZ₂ : fSub15 D.M V₀ V hV L Z₂ =
      conjSubgroup (fSub15 D.M V₀ V hV L Z₁) r := by
    rw [hZ₂def]
    simp only [fSub15]
    rw [s15_Twelve_conjSubgroup_sup, s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV hrM]
  have hZ₂in : conjSubgroup (fSub15 D.M V₀ V hV L Z₂) k⁻¹ ≤ D.M := by
    have hvV : k * r * k⁻¹ ∈ V := mem_conjSubgroup_iff.mp hrV
    have hvM : k * r * k⁻¹ ∈ D.M := h.hyp151.hyp125.pairFacts.le_M hvV
    have heq : conjSubgroup (fSub15 D.M V₀ V hV L Z₂) k⁻¹ =
        conjSubgroup (conjSubgroup (fSub15 D.M V₀ V hV L Z₁) k⁻¹) (k * r * k⁻¹) := by
      rw [hFZ₂]
      simp only [conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [heq]
    exact (E3.conjSubgroup_mono_left (k * r * k⁻¹) hin).trans
      (le_of_eq (s15_Tools_conjSubgroup_M D hvM))
  have hs3 : s15 D.M V₀ V hV L ≤ 3 := by omega
  have hE₁ : ∀ X ∈ wConj D.M V₀ V hV L,
      conjSubgroup (fSub15 D.M V₀ V hV L Z₁) k⁻¹ ≤
        normalizer (fSub15 D.M V₀ V hV L X : Set G) := by
    intro X hX
    have h1 := s15_Twelve_inner_fixes D h1217 h hV hL hk hs3 hZ₁ hin hX
    have h2 : conjSubgroup (fSub15 D.M V₀ V hV L Z₁) k⁻¹ ≤
        normalizer (v1Sub D.M V₀ V hV L : Set G) :=
      hin.trans (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)
    exact (le_inf h1 h2).trans (inf_normalizer_le_normalizer_sup X (v1Sub D.M V₀ V hV L))
  have hE₂ : ∀ X ∈ wConj D.M V₀ V hV L,
      conjSubgroup (fSub15 D.M V₀ V hV L Z₂) k⁻¹ ≤
        normalizer (fSub15 D.M V₀ V hV L X : Set G) := by
    intro X hX
    have h1 := s15_Twelve_inner_fixes D h1217 h hV hL hk hs3 hZ₂mem hZ₂in hX
    have h2 : conjSubgroup (fSub15 D.M V₀ V hV L Z₂) k⁻¹ ≤
        normalizer (v1Sub D.M V₀ V hV L : Set G) :=
      hZ₂in.trans (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV)
    exact (le_inf h1 h2).trans (inf_normalizer_le_normalizer_sup X (v1Sub D.M V₀ V hV L))
  have hFixW : ∀ X ∈ wConj D.M V₀ V hV L,
      ySub15 D.M V₀ V hV L W k⁻¹ ≤ normalizer (fSub15 D.M V₀ V hV L X : Set G) := by
    intro X hX
    have hk' : Cond1512 n D.M V k⁻¹ := cond1512_inv hk
    have hWN' : conjSubgroup V (k⁻¹)⁻¹ ⊓ D.M ≤
        normalizer (fSub15 D.M V₀ V hV L W : Set G) := by
      rw [inv_inv]
      exact (le_inf hWN hR'V₁).trans
        (inf_normalizer_le_normalizer_sup W (v1Sub D.M V₀ V hV L))
    have hc := (s15_Twelve_rank_bound D h hV hk' hWmem).2 (Or.inr hWN')
    have hc' : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L W k⁻¹ : Set G)) <
        gamma15 D.M V₀ V hV L := by omega
    exact (s15_Twelve_fixes D h1217 h.hyp151 hV hL inf_le_right hc' hX).1
  have hmod := s15_Twelve_modular D h1217 h.hyp151 hV hL hs hZ₁ hZ₂mem hWmem
    hZ₂ne.symm hWne₁.symm hWne₂.symm k⁻¹ hin hZ₂in
  refine ⟨?_, ?_⟩
  · intro X hX
    refine hmod.trans (sup_le (sup_le (hE₁ X hX) (hE₂ X hX)) ?_)
    exact hFixW X hX
  · exact ⟨W, hWmem, (le_inf hWN hR'V₁).trans
      (inf_normalizer_le_normalizer_sup W (v1Sub D.M V₀ V hV L))⟩

theorem s15_Twelve_final_contra (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn : n ≤ 2) (hγ : gamma15 D.M V₀ V hV L = n + 1)
    (hs : s15 D.M V₀ V hV L = 3)
    (hRk : ∀ X ∈ wConj D.M V₀ V hV L,
      conjSubgroup V k⁻¹ ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L X : Set G))
    (hX₃ : ∃ X₃ ∈ wConj D.M V₀ V hV L,
      conjSubgroup V k ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L X₃ : Set G)) : False := by
  have hnγ : n < gamma15 D.M V₀ V hV L := by omega
  have hnotk : ∀ X ∈ wConj D.M V₀ V hV L,
      ¬ conjSubgroup (fSub15 D.M V₀ V hV L X) k ≤ D.M := by
    intro X hX hle
    have hc := (s15_Twelve_rank_bound D h hV hk hX).2 (Or.inr (hRk X hX))
    exact s15_Twelve_whole D h1217 h hV hL hk hX hle (by omega)
  have hnot : ∀ Z ∈ wConj D.M V₀ V hV L,
      ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k⁻¹ := by
    intro Z hZ hle
    apply hnotk Z hZ
    have h1 := E3.conjSubgroup_mono_left k hle
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
  obtain ⟨X₃, hX₃mem, hX₃N⟩ := hX₃
  have hk' : Cond1512 n D.M V k⁻¹ := cond1512_inv hk
  have hc := (s15_Twelve_rank_bound D h hV hk' hX₃mem).2 (Or.inr (by rwa [inv_inv]))
  have hc' : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X₃ k⁻¹ : Set G)) <
      gamma15 D.M V₀ V hV L := by omega
  have hcard := s15_Twelve_card_le D h1217 h hV hL hk' hnγ hX₃mem hc'
  have hall : {Z : Subgroup G | Z ∈ wConj D.M V₀ V hV L ∧
      ¬ fSub15 D.M V₀ V hV L Z ≤ conjSubgroup D.M k⁻¹} = wConj D.M V₀ V hV L := by
    ext Z
    constructor
    · rintro ⟨hZ, -⟩
      exact hZ
    · intro hZ
      exact ⟨hZ, hnot Z hZ⟩
  rw [hall, ncard_wConj D h.hyp151 hV, hs] at hcard
  omega

theorem s15_Twelve_exc (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) (hn : n ≤ 2) (hγ : gamma15 D.M V₀ V hV L = n + 1)
    (hs : s15 D.M V₀ V hV L = 3) : False := by
  obtain ⟨Z₁, hZ₁, hin⟩ := s15_Twelve_exists_inner D h1217 h hV hL hk hn hγ hs
  by_cases hR : conjSubgroup V k ⊓ D.M ≤ normalizer (fSub15 D.M V₀ V hV L Z₁ : Set G)
  · have hk' := cond1512_inv hk
    have h2 := (s15_Twelve_rank_bound D h hV hk' hZ₁).2
      (Or.inr (by rwa [inv_inv]))
    exact s15_Twelve_whole D h1217 h hV hL hk' hZ₁ hin (by omega)
  · obtain ⟨hRk, hX₃⟩ := s15_Twelve_normalizes_all D h1217 h hV hL hk hn hγ hs hZ₁ hin hR
    exact s15_Twelve_final_contra D h1217 h hV hL hk hn hγ hs hRk hX₃

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
