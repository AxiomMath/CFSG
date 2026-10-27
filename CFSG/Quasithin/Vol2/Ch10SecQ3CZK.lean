module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZJ
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK
public import CFSG.Quasithin.Vol2.Ch10SecQ3CN
public import CFSG.Quasithin.Vol2.Ch10SecQ3CR

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

namespace Ctx

variable (c : Ctx T L I H K n k b hel I' K₀)
include c

theorem orderOf_b : orderOf b = 2 ^ n - 1 := by
  have hp := c.pow_eq_one (oTwoUpper_le _ c.hbB0).1 (oTwoUpper_le _ c.hbB0).2 c.hbo
  have hk := c.hbk
  rw [c.s7.1] at hk
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hp) hk

theorem isSylowTwoOf_baum_L0 :
    IsSylowTwoOf (baum T) (fsuL0 T L ⊔ baum T) := by
  obtain ⟨hKJ, I'', hcard, hJeq, hcomm, hind, htrans, htype, -, -, h2, -⟩ := c.e23Concl_L0T
  have hL2 := SecE.isL2Natural_of_case1 c.h37 c.h38 c.h322 c.hyp c.h1 hKJ hcard hJeq hcomm hind
    htrans htype
  have h := (h2 hL2).2.2.1
  rwa [SecE.twoResidual_fsuL0_sup c.h37 c.h38 c.hyp] at h

theorem isSylowTwoOf_baum_H : IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T) := by
  have h := (c.hD.two c.all_natural).2.2.1
  rwa [SecE.twoResidual_eq_oTwoUpper] at h

theorem B0_le_normalizer_K (hB0K : Obl10_2_3B0K) : B0 T L ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨m, hm⟩ : ∃ m, ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := ⟨k, c.hKF⟩
  exact hB0K G T L I c.hyp n c.h1 H c.hH c.hn1 c.hZH K m c.hKc
    (oTwoUpper_eq_conjClosure_T c.hKc c.hyp.fsu.sylow.1 c.hHK) hm

theorem baum_le_T1 (h1012 : Stmt10_1_2) : baum T ≤ T1 T L :=
  ((h1012 G T L I c.hyp).2.2.2.2.2.2.2.2 (Or.inl ⟨n, c.h1⟩)).2 c.not_thompsonJ_le

theorem baum_le_normalizer_conjugate (h1012 : Stmt10_1_2) {t : G} (ht : t ∈ T) :
    baum T ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
  (c.baum_le_T1 h1012).trans (SecB.T1_le_normalizer_conjugate c.h37 c.h38 c.hyp ht)

theorem autI_K_perfect_ne_bot :
    ⁅autI hel K, autI hel K⁆ = autI hel K ∧ autI hel K ≠ ⊥ := by
  have hKN : K ≤ Subgroup.normalizer (VZ T H : Set G) :=
    (le_of_mem_cComp c.hKc).trans (le_normalizer_conjClosure _ H)
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp c.hKc
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKperf]
  refine ⟨?_, fun h => c.hZH (commutator_eq_bot_of_le_centralizer c.hHK
    ((autI_eq_bot_iff hel hKN).mp h))⟩
  rw [← range_convK hel hKN, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hKtop]

theorem baum_le_normalizer_K :
    baum T ≤ Subgroup.normalizer (K : Set G) := by
  have := c.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat c.hyp.fsu.nonabelian c.hyp.fsu.qtke).1
  have hHN : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
  obtain ⟨-, -, hO⟩ := SecF.C10P4F.vz_facts c.h331 c.hyp c.hH
  obtain ⟨hperf, hne⟩ := c.autI_K_perfect_ne_bot
  obtain ⟨hbaum, hsyl, -, -⟩ := c.hD.two c.all_natural
  have hJN : autI hel (thompsonJ H) ≤ Subgroup.normalizer (autI hel K : Set _) := by
    rw [c.hD.jeq, c.hKA]
    refine iSup₂_le fun L' hL' => le_trans ?_ (SecF.C10P4F.le_normalizer_oTwoUpper K₀)
    by_cases h : L' = K₀
    · rw [h]
      exact Subgroup.le_normalizer
    · exact SecE.le_normalizer_of_commute fun x hx y hy => c.hD.comm L' hL' K₀ c.hK₀ h x hx y hy
  intro s hs
  have hsH : s ∈ H := c.T_le_H hs.1
  have hsN : s ∈ Subgroup.normalizer (VZ T H : Set G) := hHN hsH
  have hσ : convI hel ⟨s, hsN⟩ ∈ Subgroup.normalizer (autI hel K : Set _) :=
    hJN (hsyl.1 (hbaum ▸ convI_mem_autI hel hs hsN))
  rw [← A38.map_conj_eq_iff]
  by_contra hne'
  set K' := K.map (MulAut.conj s).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H := H13.LocDbl.map_conj_mem_cComp c.hKc (Subgroup.le_normalizer hsH)
  have hA' : autI hel K' = autI hel K := by
    rw [hK', autI_map_conj hel hsN]
    exact A38.map_conj_eq_iff.mpr hσ
  have hc := Vol2Native.lemma_1_2_1_two hloc c.h37 c.hH.1.2 c.hKc hK'c (Ne.symm hne')
  have hKK' : autI hel ⁅K, K'⁆ = ⊥ := autI_eq_bot_of_le_centralizer hel ((hc.1.trans hc.2).trans hO)
  have hle : ⁅autI hel K, autI hel K'⁆ ≤ autI hel ⁅K, K'⁆ := by
    rw [Subgroup.commutator_le]
    intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hel).mp hφ
    obtain ⟨g', hg', rfl⟩ := (mem_autI hel).mp hψ
    rw [← map_commutatorElement]
    exact convI_mem_autI hel (Subgroup.commutator_mem_commutator hg hg') _
  rw [hKK', hA', hperf, le_bot_iff] at hle
  exact hne hle

end Ctx

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
