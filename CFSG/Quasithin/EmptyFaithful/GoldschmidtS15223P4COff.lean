module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CFacts
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.EmptyFaithful.S152He12E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem T_le_normalizer_kS : T ≤ Subgroup.normalizer (kS T Mc M B₀ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (d.T_le_normalizer_kI hg)
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (T_le_normalizer_S152 d.c.inputs hg)
  rw [Subgroup.map_sup, h1, h2]

theorem kS_le_sup : kS T Mc M B₀ ≤ X ⊔ sOf152 T Mc M B₀ :=
  sup_le (d.kI_le_X.trans le_sup_left) le_sup_right

theorem pCoreOf_sup_le : pCoreOf 2 (X ⊔ sOf152 T Mc M B₀) ≤ pCoreOf 2 (kS T Mc M B₀) :=
  le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le_of_isSylowTwoOf d.sylow_sup).trans le_sup_right)
    (d.kS_le_sup.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem zS_le_pCoreOf_kS : zSOf T Mc M B₀ ≤ pCoreOf 2 (kS T Mc M B₀) :=
  le_pCoreOf_of_le_normalizer 2 (d.zS_le_S.trans le_sup_right)
    (d.kS_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
    (B2F.isPGroup_of_isElemAbelian (card_zS152 d.c.b0 d.c.inputs).2)

theorem baum_ne_bot : baum (pCoreOf 2 (kS T Mc M B₀)) ≠ ⊥ := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 (kS T Mc M B₀)) := pCoreOf_isPGroup 2 _
  have hQ1 : pCoreOf 2 (kS T Mc M B₀) ≠ ⊥ := by
    intro h
    have h1 : zSOf T Mc M B₀ = ⊥ := le_bot_iff.mp (h ▸ d.zS_le_pCoreOf_kS)
    have h4 := (card_zS152 d.c.b0 d.c.inputs).1
    rw [h1, Subgroup.card_bot] at h4
    omega
  intro h
  exact S1414.thompsonJ_ne_bot hQ2 hQ1 (le_bot_iff.mp (h ▸ S1414.thompsonJ_le_baum _))

theorem not_baum_eq (h12 : He12.StageLemma15212W) (hF : ¬ X ≤ Mc) :
    baum (pCoreOf 2 (kS T Mc M B₀)) ≠ baum (pCoreOf 2 (X ⊔ sOf152 T Mc M B₀)) := by
  intro hbaum
  apply hF
  have hQ2 : IsPGroup 2 (pCoreOf 2 (kS T Mc M B₀)) := pCoreOf_isPGroup 2 _
  have h1 : X ≤ Subgroup.normalizer (baum (pCoreOf 2 (kS T Mc M B₀)) : Set G) := by
    rw [hbaum]
    exact (le_sup_left.trans (le_normalizer_pCoreOf 2 (X ⊔ sOf152 T Mc M B₀))).trans
      (normalizer_le_normalizer_baum _)
  have h2 : T ≤ Subgroup.normalizer (baum (pCoreOf 2 (kS T Mc M B₀)) : Set G) :=
    (d.T_le_normalizer_kS.trans (normalizer_le_normalizer_pCoreOf 2 _)).trans
      (normalizer_le_normalizer_baum _)
  have hHle : H ≤ Subgroup.normalizer (baum (pCoreOf 2 (kS T Mc M B₀)) : Set G) := by
    rw [H_eq152 d.c.setting d.c.hstar]
    exact sup_le (d.f.K_le.trans h1) h2
  have hbN : baum (pCoreOf 2 (kS T Mc M B₀)) ≤
      pCoreOf 2 (Subgroup.normalizer (baum (pCoreOf 2 (kS T Mc M B₀)) : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (hQ2.to_le (inf_le_left : baum (pCoreOf 2 (kS T Mc M B₀)) ≤ _))
  have hp : pCoreOf 2 (Subgroup.normalizer (baum (pCoreOf 2 (kS T Mc M B₀)) : Set G)) ≠ ⊥ :=
    fun h => d.baum_ne_bot (le_bot_iff.mp (h ▸ hbN))
  obtain ⟨B, hB⟩ := d.c.inputs.hN.sigmaPrime_nonempty
  have hU := (h12 G T Mc M d.c.setting H d.c.hstar B hB).unique
  intro x hx
  exact le_of_isUniqueM hU ⟨hHle, hp⟩ (h1 hx)

theorem q1Offender (h12 : He12.StageLemma15212W) (hF : ¬ X ≤ Mc) :
    Q1Offender15128 T (kS T Mc M B₀) (zSOf T Mc M B₀) (zSOf T Mc M B₀) X := by
  obtain ⟨hU, hred⟩ := d.isTwoReduced_W
  have hSN := d.S_le_normalizer_X
  have hQS : pCoreOf 2 (kS T Mc M B₀) ≤ sOf152 T Mc M B₀ :=
    pCoreOf_le_of_isSylowTwoOf d.sylow_kS
  have hQX : pCoreOf 2 (kS T Mc M B₀) ≤ X ⊔ sOf152 T Mc M B₀ :=
    (pCoreOf_le 2 _).trans d.kS_le_sup
  have hYL : X ⊔ sOf152 T Mc M B₀ ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hSN
  have hLT : ∀ x ∈ X ⊔ sOf152 T Mc M B₀, ∃ l ∈ X, ∃ t ∈ sOf152 T Mc M B₀, x = l * t := by
    intro x hx
    have : x ∈ (X : Set G) * (sOf152 T Mc M B₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X _ hSN]
      exact hx
    obtain ⟨l, hl, t, ht, h⟩ := this
    exact ⟨l, hl, t, ht, h.symm⟩
  have hVL : ⁅uOf1527 (zSOf T Mc M B₀) X, X⁆ ≠ ⊥ := by
    intro h
    apply d.not_le_centralizer_W hF
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h
  obtain ⟨-, -, -, halt⟩ := C124.B2_10_2 hU hred d.pCoreOf_sup_le hQS d.sylow_sup le_sup_left hYL
    hLT hVL (Or.inl d.c.quasi)
  rcases halt with hbaum | ⟨hstab, -, -⟩
  · exact absurd hbaum (d.not_baum_eq h12 hF)
  · obtain ⟨B, hBmem⟩ := hstab.1
    have hYN := hred.2.1
    obtain ⟨g, hg, B', hB', -⟩ := (C124.mem_offenderImagesConjIn_iff hU hYN hQX).1 hBmem
    obtain ⟨A₀, hA₀, rfl⟩ := hB'
    have hne : autI hU A₀ ≠ ⊥ := fun h =>
      hA₀.2 ((autI_eq_bot_iff hU (hA₀.1.1.trans (hQX.trans hYN))).1 h)
    have hP : autI hU A₀ ∈ C124.offenderImagesConjIn hU (X ⊔ sOf152 T Mc M B₀)
        (pCoreOf 2 (kS T Mc M B₀)) := by
      refine ⟨hne, A₀, rfl, 1, (X ⊔ sOf152 T Mc M B₀).one_mem, ?_⟩
      have h1 : cjSub (1 : G)⁻¹ A₀ = A₀ := by
        ext x
        simp [mem_cjSub]
      rw [h1]
      exact hA₀.1
    refine ⟨hU, autI hU A₀, ?_, hstab.2.1 _ hP⟩
    rw [d.q1_eq]
    exact autI_mono hU hA₀.1.1

end CData

end C

end S15223P4

end CFSG.Quasithin
