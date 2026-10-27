module

public import CFSG.Quasithin.Vol2.Ch11SecB24One
public import CFSG.Quasithin.Vol2.Ch11SecBFacts36

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSubgroup_zpowers (x g : G) :
    conjSubgroup (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  rw [conjSubgroup, MonoidHom.map_zpowers]
  simp

theorem exists_sym_gen {T W : Subgroup G}
    (hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (W : Set G)))
    (hW2 : IsPGroup 2 ↥W) {g : G} (hAT : conjSubgroup W g ≤ T)
    (hnc : ⁅W, conjSubgroup W g⁆ ≠ ⊥)
    (hVN : W ≤ Subgroup.normalizer (conjSubgroup W g : Set G)) :
    ∃ k : G, conjSubgroup W k ≤ T ∧ ⁅W, conjSubgroup W k⁆ ≠ ⊥ ∧
      W ≤ Subgroup.normalizer (conjSubgroup W k : Set G) ∧
      conjSubgroup W k⁻¹ = conjSubgroup W g := by
  set A := conjSubgroup W g with hAdef
  have hAV : conjSubgroup A g⁻¹ = W := E3.conjSubgroup_conj_inv W g
  have hAN : A ≤ Subgroup.normalizer (W : Set G) := hAT.trans hTS.1
  have hBN : conjSubgroup W g⁻¹ ≤ Subgroup.normalizer (W : Set G) := by
    have := E3.conjSubgroup_mono_left g⁻¹ hVN
    rwa [E3.conjSubgroup_normalizer, hAV] at this
  have hB2 : IsPGroup 2 ↥(conjSubgroup W g⁻¹) := E3.isPGroup_conjSubgroup hW2 g⁻¹
  obtain ⟨x, hx, hxB⟩ := exists_conj_le_of_isSylowTwoOf hTS hBN hB2
  have hVx : conjSubgroup W x⁻¹ = W :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hx)
  have hVx' : conjSubgroup W x = W := conjSubgroup_eq_iff_mem_normalizer.mpr hx
  have hk : conjSubgroup W (g⁻¹ * x⁻¹) = conjSubgroup (conjSubgroup W g⁻¹) x⁻¹ :=
    (conjSubgroup_conjSubgroup _ _ _).symm
  have hcj : cjSub x (conjSubgroup W g⁻¹) = conjSubgroup (conjSubgroup W g⁻¹) x⁻¹ := by
    ext y
    simp only [mem_cjSub, mem_conjSubgroup_iff, inv_inv]
  refine ⟨g⁻¹ * x⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hk, ← hcj]
    exact hxB
  · rw [hk]
    have e1 : ⁅W, conjSubgroup (conjSubgroup W g⁻¹) x⁻¹⁆ =
        conjSubgroup (conjSubgroup ⁅A, W⁆ g⁻¹) x⁻¹ := by
      rw [E3.conjSubgroup_commutator, E3.conjSubgroup_commutator, hAV, hVx]
    rw [e1]
    intro h0
    apply hnc
    rw [Subgroup.commutator_comm]
    exact conjSubgroup_eq_bot_iff.mp (conjSubgroup_eq_bot_iff.mp h0)
  · rw [hk, ← E3.conjSubgroup_normalizer]
    have h1 : W ≤ Subgroup.normalizer (conjSubgroup W g⁻¹ : Set G) := by
      rw [← E3.conjSubgroup_le_conjSubgroup_iff g, E3.conjSubgroup_normalizer,
        E3.conjSubgroup_inv_conj]
      exact hAN
    calc W = conjSubgroup W x⁻¹ := hVx.symm
      _ ≤ _ := E3.conjSubgroup_mono_left x⁻¹ h1
  · rw [mul_inv_rev, inv_inv, inv_inv, ← conjSubgroup_conjSubgroup, hVx']

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem aSet_VM {V₁ V₂ : Subgroup G}
    (hfl : Flag36 L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n) (hs : E3.sParam hfl.elemW = 2 * n)
    {g : G} (hgT : conjSubgroup (VM T L I) g ≤ T)
    (hgc : ⁅VM T L I, conjSubgroup (VM T L I) g⁆ ≠ ⊥) :
    autI hfl.elemW (conjSubgroup (VM T L I) g) ∈ E3.aSet (2 * n) (autI hfl.elemW ⊤) := by
  have hn := hfl.two_le
  have hAN : conjSubgroup (VM T L I) g ≤ Subgroup.normalizer (VM T L I : Set G) :=
    hgT.trans hfl.T_le_W
  have hAC : ¬ conjSubgroup (VM T L I) g ≤ Subgroup.centralizer (VM T L I : Set G) := by
    intro hC
    apply hgc
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hC
  have := autI_mem_aSet_of_le hfl.elemW le_rfl hAN hAC (by rw [E3.mQuot_self, hs]; omega)
  rwa [E3.mQuot_self, hs, Nat.sub_zero] at this

end CFSG.Quasithin.Vol2.Ch11.SecB
