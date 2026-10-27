module

public import CFSG.LocalAnalysis.WeakClosure81.TwelvePermMod
public import CFSG.LocalAnalysis.WeakClosure81.W15SixC
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveDefs
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

private theorem w16_y_kerIn_top_eq_normalCore {Γ : Type*} [Group Γ] (K : Subgroup Γ) :
    CFSG.Quasithin.kerIn K ⊤ = K.normalCore := by
  ext x
  simp only [CFSG.Quasithin.kerIn, Subgroup.mem_mk, Subgroup.mem_top, forall_true_left,
    Subgroup.normalCore, Set.mem_setOf_eq]

theorem Hyp167.inf_kerMOf_eq (hB : Asc80ThmB) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T)
    (hA : 2 < (conjSubgroup V g ⊓ kerMOf M X).relIndex (conjSubgroup V g))
    {D Y : Subgroup G} (hDA : D ≤ conjSubgroup V g) (hDY : D ≤ Y) (hYX : Y ≤ X)
    (hYM : ¬ Y ≤ M) : D ⊓ kerMOf M Y = D ⊓ kerMOf M X := by
  have hpair : IsPairAt M X (conjSubgroup V g) := hX.mem.2.2
  have hAe : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hXcent : X ≤ Subgroup.centralizer (U : Set G) := hX.mem.1.trans hX.min.1.2.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    hXcent.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hKX : CFSG.Open.IsKGroup ↥X :=
    (hS.localsK (Subgroup.normalizer (U : Set G))
      ⟨U, hX.cex.ne_bot, hX.cex.hyp.isPGroup.to_le hX.cex.le, rfl⟩).of_le hXU
  obtain ⟨⟨n, hdisj⟩, hBorel⟩ := five_nine_borel hB hpair hAe hKX hA
  have hYK : Y ⊓ kerMOf M X ≤ kerMOf M Y := by
    refine le_kerMOf_of_normal inf_le_left ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro a b ha hb
      obtain ⟨haY, haK⟩ := Subgroup.mem_inf.1 ha
      exact Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.mul_mem hb haY) (Y.inv_mem hb),
        conj_mem_kerMOf (hYX hb) haK⟩
    · exact inf_le_right.trans (kerMOf_le_left M X)
  refine le_antisymm ?_ ?_
  · intro a ha
    obtain ⟨haD, haKer⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨haD, ?_⟩
    by_contra haK
    have haY : a ∈ Y := kerMOf_le_group M Y haKer
    have haX : a ∈ X := hYX haY
    have haA : a ∈ conjSubgroup V g := hDA haD
    obtain ⟨y, hyY, hyM⟩ := SetLike.not_le_iff_exists.1 hYM
    have hyX : y ∈ X := hYX hyY
    have hconj : y⁻¹ * a * y ∈ kerMOf M Y := by
      simpa using conj_mem_kerMOf (Y.inv_mem hyY) haKer
    have hconjX : y⁻¹ * a * y ∈ X := hYX (kerMOf_le_group M Y hconj)
    have hconjM : y⁻¹ * a * y ∈ M := kerMOf_le_left M Y hconj
    have hgq : kerQuotMk M X ⟨y, hyX⟩ ∉ kerQuotImg M X M := by
      intro hmem
      have h1 : (⟨y, hyX⟩ : ↥X) ∈ (kerQuotImg M X M).comap (kerQuotMk M X) := hmem
      rw [b5_FiveNineQuot_comap_kerQuotImg_self] at h1
      exact hyM (Subgroup.mem_subgroupOf.1 h1)
    have haq : kerQuotMk M X ⟨a, haX⟩ ∈ kerQuotImg M X (conjSubgroup V g) := by
      have h : a ∈ kerQuotLift M X (kerQuotImg M X (conjSubgroup V g)) := by
        rw [kerQuotLift_kerQuotImg hpair.A_le]
        exact Subgroup.mem_sup_left haA
      obtain ⟨hx, hq⟩ := mem_kerQuotLift_iff.1 h
      have he : (⟨a, hx⟩ : ↥X) = ⟨a, haX⟩ := Subtype.ext rfl
      rwa [he] at hq
    have hgaq : (kerQuotMk M X ⟨y, hyX⟩)⁻¹ * kerQuotMk M X ⟨a, haX⟩
        * kerQuotMk M X ⟨y, hyX⟩ ∈ kerQuotImg M X M := by
      have hmem : y⁻¹ * a * y ∈ kerQuotLift M X (kerQuotImg M X M) := by
        rw [kerQuotLift_kerQuotImg_left]
        exact Subgroup.mem_inf.2 ⟨hconjM, hconjX⟩
      obtain ⟨hx, hq⟩ := mem_kerQuotLift_iff.1 hmem
      have himg : kerQuotMk M X ⟨y⁻¹ * a * y, hconjX⟩ ∈ kerQuotImg M X M := by
        have he : (⟨y⁻¹ * a * y, hx⟩ : ↥X) = ⟨y⁻¹ * a * y, hconjX⟩ := Subtype.ext rfl
        rwa [he] at hq
      have heq : (kerQuotMk M X ⟨y, hyX⟩)⁻¹ * kerQuotMk M X ⟨a, haX⟩
          * kerQuotMk M X ⟨y, hyX⟩ = kerQuotMk M X ⟨y⁻¹ * a * y, hconjX⟩ := by
        have hsub : (⟨y⁻¹ * a * y, hconjX⟩ : ↥X)
            = (⟨y, hyX⟩ : ↥X)⁻¹ * (⟨a, haX⟩ : ↥X) * (⟨y, hyX⟩ : ↥X) := by
          ext
          simp [mul_assoc]
        rw [hsub, map_mul, map_mul, map_inv]
      rw [heq]
      exact himg
    have h1 : kerQuotMk M X ⟨a, haX⟩ = 1 :=
      rankOne_free_off_borel hdisj hBorel (kerQuotImg_mono hpair.A_le_M)
        (isElemAbelian_kerQuotImg hAe) hgq haq hgaq
    have hker : (⟨a, haX⟩ : ↥X) ∈ (kerQuotMk M X).ker := by
      rw [MonoidHom.mem_ker]
      exact h1
    rw [ker_kerQuotMk] at hker
    exact haK (Subgroup.mem_subgroupOf.1 hker)
  · intro a ha
    obtain ⟨haD, haK⟩ := Subgroup.mem_inf.1 ha
    exact Subgroup.mem_inf.2 ⟨haD, hYK (Subgroup.mem_inf.2 ⟨hDY haD, haK⟩)⟩

theorem Hyp167.setting12Two_of_min (hB : Asc80ThmB) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) {D Y : Subgroup G} (hD : IsElemAbelian 2 D)
    (hDA : D ≤ conjSubgroup V g) (hD2 : 2 < (D ⊓ kerMOf M X).relIndex D)
    (hY : IsMinimalNotLE M D Y) (hYX : Y ≤ X) :
    IsPairAt M Y D ∧ ∃ k : ℕ, E3.mQuot D (D ⊓ kerMOf M X) ≤ k ∧
      Setting12Two (D.subgroupOf Y) (M.subgroupOf Y) k := by
  have hDM : D ≤ M := hDA.trans hX.mem.2.2.A_le_M
  have hA : 2 < (conjSubgroup V g ⊓ kerMOf M X).relIndex (conjSubgroup V g) := by
    have hEq : (D ⊓ kerMOf M X).relIndex D
        = (conjSubgroup V g ⊓ kerMOf M X).relIndex D := by
      rw [← Subgroup.inf_relIndex_left D (conjSubgroup V g ⊓ kerMOf M X)]
      congr 1
      rw [← inf_assoc, inf_of_le_left hDA]
    have hle : (conjSubgroup V g ⊓ kerMOf M X).relIndex D
        ≤ (conjSubgroup V g ⊓ kerMOf M X).relIndex (conjSubgroup V g) :=
      Subgroup.relIndex_le_of_le_right hDA (E3.relIndex_ne_zero' (conjSubgroup V g)
        (conjSubgroup V g ⊓ kerMOf M X))
    exact lt_of_lt_of_le (hEq ▸ hD2) hle
  have hInK : D ⊓ kerMOf M Y = D ⊓ kerMOf M X :=
    Hyp167.inf_kerMOf_eq hB hS hX hA hDA hY.1 hYX hY.2.1
  have hpair : IsPairAt M Y D :=
    { A_le := hY.1
      A_le_M := hDM
      not_le_ker := by
        intro hDle
        have hDK : D ⊓ kerMOf M X = D := by rw [← hInK, inf_of_le_left hDle]
        have hlt : (D ⊓ kerMOf M X).relIndex D = 1 := by rw [hDK, Subgroup.relIndex_self]
        omega
      maxOver_eq := by
        refine Set.Subset.antisymm ?_ ?_
        · intro N hN
          have hNmax : IsMaxSubgroupIn Y N := hN.1
          have hNsup : D ⊔ kerMOf M Y ≤ N := hN.2
          have hNY : N ≤ Y := hNmax.1.le
          have hDN : D ≤ N := le_sup_left.trans hNsup
          have hNM : N ≤ M := by
            by_contra hNM
            exact hNmax.1.ne (hY.2.2 N hDN hNY hNM)
          have hMYne : M ⊓ Y ≠ Y := fun h => hY.2.1 (by rw [← h]; exact inf_le_left)
          have hle : N ≤ M ⊓ Y := le_inf hNM hNY
          rw [Set.mem_singleton_iff]
          by_contra hne
          exact absurd (hNmax.2 (M ⊓ Y) (lt_of_le_of_ne hle hne) inf_le_right) hMYne
        · intro N hN
          rw [Set.mem_singleton_iff] at hN
          rw [hN]
          refine ⟨⟨lt_of_le_of_ne inf_le_right ?_, ?_⟩, ?_⟩
          · intro h
            exact hY.2.1 (by rw [← h]; exact inf_le_left)
          · intro K hltK hKY
            have hDK : D ≤ K := (le_inf hDM hY.1).trans hltK.1
            by_cases hKM : K ≤ M
            · exact absurd (le_inf hKM hKY) hltK.2
            · exact hY.2.2 K hDK hKY hKM
          · exact sup_le (le_inf hDM hY.1)
              (le_inf (kerMOf_le_left M Y) (kerMOf_le_group M Y)) }
  have hYcent : Y ≤ Subgroup.centralizer (U : Set G) :=
    (hYX.trans hX.mem.1).trans hX.min.1.2.1
  have hKY : CFSG.Open.IsKGroup ↥Y :=
    (hS.localsK (Subgroup.normalizer (U : Set G))
      ⟨U, hX.cex.ne_bot, hX.cex.hyp.isPGroup.to_le hX.cex.le, rfl⟩).of_le
      (hYcent.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
  have hbigY : 2 < (D ⊓ kerMOf M Y).relIndex D := by rw [hInK]; exact hD2
  obtain ⟨⟨k, htype⟩, -⟩ := five_nine_borel hB hpair hD hKY hbigY
  have hmQuot : E3.mQuot D (D ⊓ kerMOf M X) ≤ k := by
    obtain ⟨S, hSyl⟩ := (isElemAbelian_kerQuotImg hD).isPGroup.exists_le_sylow
    have hcard : Nat.card ↥(kerQuotImg M Y D) = (D ⊓ kerMOf M X).relIndex D := by
      rw [card_kerQuotImg hY.1, hInK]
    have hpow : (D ⊓ kerMOf M X).relIndex D = 2 ^ E3.mQuot D (D ⊓ kerMOf M X) :=
      E3.relIndex_eq_two_pow hD.isPGroup (D ⊓ kerMOf M X)
    have hle := (rankOne_card_elemAbelian_le htype hSyl (isElemAbelian_kerQuotImg hD)).1
    rw [hcard, hpow] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  refine ⟨hpair, k, hmQuot, ?_⟩
  exact
    { A_two := hD.isPGroup.comap_subtype
      A_le_M := fun x hx => Subgroup.mem_subgroupOf.2 (hDM (Subgroup.mem_subgroupOf.1 hx))
      M_ne := fun htop => hY.2.1 (Subgroup.subgroupOf_eq_top.1 htop)
      unique_max := by
        intro N hDN hNtop
        have hNY : N.map Y.subtype ≤ Y := Subgroup.map_subtype_le N
        have hDN' : D ≤ N.map Y.subtype := by
          intro d hd
          exact ⟨⟨d, hY.1 hd⟩, hDN (Subgroup.mem_subgroupOf.2 hd), rfl⟩
        have hNne : N.map Y.subtype ≠ Y := by
          intro heq
          apply hNtop
          rw [eq_top_iff]
          intro y _
          have hy : (y : G) ∈ N.map Y.subtype := by rw [heq]; exact y.2
          obtain ⟨n, hn, hny⟩ := hy
          exact Subtype.ext hny ▸ hn
        have hNM : N.map Y.subtype ≤ M := by
          by_contra hNM
          exact hNne (hY.2.2 (N.map Y.subtype) hDN' hNY hNM)
        intro x hx
        exact Subgroup.mem_subgroupOf.2 (hNM (Subgroup.mem_map_of_mem Y.subtype hx))
      type := by
        have e : (↥Y ⧸ (M.subgroupOf Y).normalCore) ≃* (↥Y ⧸ kerIn (M.subgroupOf Y) ⊤) :=
          QuotientGroup.quotientMulEquivOfEq
            (w16_y_kerIn_top_eq_normalCore (M.subgroupOf Y)).symm
        rcases htype with ht | ht
        · exact Or.inl (isPSL_congr e ht)
        · exact Or.inr (isSz_congr e ht)
      one_lt_n := one_lt_of_isPSL_or_isSz htype }

end CFSG.LocalAnalysis.WeakClosure81

end
