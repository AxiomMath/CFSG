module

public import CFSG.Quasithin.Vol2.Ch10SecB6Odd
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Quasithin.Vol2.Ch10SecB6Pair

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fittingSubgroup_le_pCore_sup_oddCore' (X : Type) [Group X] [Finite X] :
    CFSG.fittingSubgroup X ≤ CFSG.pCore 2 X ⊔ CFSG.oddCore X :=
  CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore

theorem isQuasisimple_of_not_charTwo {H K : Subgroup G} (hKc : K ∈ cComp H)
    (hO : A37.oddCoreOf K = ⊥) (hnc : ¬ CharTwo K) : CFSG.IsQuasisimple ↥K := by
  have hO' : CFSG.oddCore ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hO
  have hE : CFSG.layer ↥K ≠ ⊥ := by
    intro hE
    apply hnc
    have hF : CFSG.generalizedFitting ↥K ≤ CFSG.pCore 2 ↥K := by
      rw [CFSG.generalizedFitting, hE, sup_bot_eq]
      refine (fittingSubgroup_le_pCore_sup_oddCore' ↥K).trans ?_
      rw [hO', sup_bot_eq]
    intro x hx
    obtain ⟨hxK, hxC⟩ := hx
    have h1 : (⟨x, hxK⟩ : ↥K) ∈
        Subgroup.centralizer (CFSG.generalizedFitting ↥K : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (y : G) ∈ pCoreOf 2 K := ⟨y, by exact hF hy, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hy')
    have h2 := hF (CFSG.centralizer_generalizedFitting_le ↥K h1)
    exact ⟨_, by exact h2, rfl⟩
  obtain ⟨J, hJ, hJ1⟩ : ∃ J : Subgroup ↥K, CFSG.IsComponent J ∧ J ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hE (sSup_eq_bot.mpr fun J hJ => hcon J hJ)
  have hJc := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hJ)
  rw [cComp_self_eq_singleton hKc, Set.mem_singleton_iff] at hJc
  have hJtop : J = ⊤ := by
    have h := congrArg (fun X : Subgroup G => X.subgroupOf K) hJc
    simp only [Subgroup.subgroupOf_self] at h
    rw [← h]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective J).symm
  have hq := hJ.1
  rw [hJtop] at hq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hq

theorem inf_pCoreOf_le_center {H K : Subgroup G} (hKc : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple ↥K) {x : G} (hxH : x ∈ pCoreOf 2 H) (hxK : x ∈ K) :
    ∀ y ∈ K, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hn : ((pCoreOf 2 H ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk)) h
    have h2 : h ∈ K ↔ k * h * k⁻¹ ∈ K := by
      constructor
      · intro hh
        exact K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)
      · intro hh
        have := K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk
        simpa [mul_assoc] using this
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with h | h
  · exfalso
    apply not_isSolvable_of_mem_cComp hKc
    have hK2 : IsPGroup 2 K := by
      refine (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le ?_
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (pCoreOf 2 H ⊓ K).subgroupOf K := by rw [h]; trivial
      exact this.1
    have := hK2.isNilpotent
    infer_instance
  · intro y hy
    have hmem := h (show (⟨x, hxK⟩ : ↥K) ∈ (pCoreOf 2 H ⊓ K).subgroupOf K from ⟨hxH, hxK⟩)
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩).symm)

theorem pCore_modO2Image_ne_bot (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    {X H K : Subgroup G} (hX : X = L ∨ X = CFSG.conjugate L t) (hKc : K ∈ cComp H)
    (hXK : X ≤ K) (hq : CFSG.IsQuasisimple ↥K) :
    CFSG.pCore 2 ↥(modO2Image H X) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨-, hXN, -, -⟩ := li_data h37 h38 hyp ht hX
  have hMN := SecA.fsuM_le_normalizer_fsuVM T L I
  have hXM : X ≤ fsuM T L := by
    rcases hX with rfl | rfl
    · exact (SecA.le_fsuL0 T X).trans (SecA.fsuL0_le_fsuM T X)
    · exact (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)
  have hVX : ⁅fsuVM T L I, X⁆ ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
      (SecA.le_normalizer_commutator (hXM.trans hMN) Subgroup.le_normalizer)
      ((SecA.isPGroup_fsuVM hyp).to_le
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hXM.trans hMN)))
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((fsuVM_le_T1 h37 h38 hyp).trans hXN)
  have hXO : pCoreOf 2 X ≤ pCoreOf 2 H := by
    intro x hx
    have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H)
        (⟨x, hKH (hXK (CFSG.LieType.BorelTits.pCoreOf_le 2 X hx))⟩ : ↥H) ∈
        pCoreOf 2 (modO2Image H X) :=
      modO2Image_pCoreOf_le (Subgroup.mem_map_of_mem _ (show (⟨x, _⟩ : ↥H) ∈
        (pCoreOf 2 X).subgroupOf H from hx))
    have hx2 : pCoreOf 2 (modO2Image H X) = ⊥ := by
      rw [pCoreOf, hbot, Subgroup.map_bot]
    rw [hx2, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact ⟨_, hx1, rfl⟩
  have h1 : ⁅⁅fsuVM T L I, X⁆, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hvX : v ∈ pCoreOf 2 X := hVX hv
    exact (inf_pCoreOf_le_center hKc hq (hXO hvX)
      (hXK (CFSG.LieType.BorelTits.pCoreOf_le 2 X hvX)) x (hXK hx)).symm
  have h2 : ⁅⁅X, fsuVM T L I⁆, X⁆ = ⊥ := by rw [Subgroup.commutator_comm X]; exact h1
  have hperf : ⁅X, X⁆ = X := by
    rcases hX with rfl | rfl
    · exact SecA.perfect_L hyp.fsu.maximal.1
    · rw [SecA.conjugate_eq_map, ← Subgroup.map_commutator, SecA.perfect_L hyp.fsu.maximal.1]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hperf, Subgroup.commutator_comm] at h3
  rcases hX with rfl | rfl
  · exact SecA.commutator_fsuVM_ne_bot hyp.fsu h3
  · apply SecA.commutator_fsuVM_ne_bot hyp.fsu
    rw [← SecA.conjugate_commutator_fsuVM (le_fsuM T L ht), SecA.conjugate_eq_map] at h3
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj t⁻¹).injective).mp h3

end CFSG.Quasithin.Vol2.Ch10.SecB
