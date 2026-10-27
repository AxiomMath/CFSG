module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.KFunctor

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem nonempty_mulEquiv_thetaOf
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {L : Subgroup G} (hL : L ∈ lcal (θ a)) :
    Nonempty (↥(thetaOf θ A) ≃* ↥L) := by
  have hdp := isDirectProduct_lcal h hS ha ha1
  have hAH : A ≤ Subgroup.normalizer (θ a : Set G) := h.isFunctor.normalized a ha ha1
  have hper : ∀ c ∈ A, ∀ J ∈ lcal (θ a), J.map (MulAut.conj c).toMonoidHom ∈ lcal (θ a) :=
    fun c hc J hJ => map_conj_mem_lcal hJ (hAH hc)
  have hsm : smear L A = θ a ⊓ Subgroup.centralizer (A : Set G) :=
    smear_eq_centralizer_of_transitive hdp hper hL fun K hK => exists_conj_eq h ha ha1 hL hK
  have hD : smear L A = thetaOf θ A := hsm.trans (h.isFunctor.inf_centralizer_self ha ha1)
  have hN : A ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    rw [inf_normalizer_eq_zpowers h hS ha ha1 hL]
    exact (inf_centralizer_eq_zpowers h hS ha ha1 hL).ge.trans inf_le_right
  obtain ⟨e⟩ := T613.nonempty_mulEquiv_smear_of_le_centralizer hAH hL hN
  exact ⟨(MulEquiv.subgroupCongr hD).symm.trans e⟩

theorem simple_thetaOf
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) :
    IsSimpleGroup (thetaOf θ A) ∧ ¬ IsMulCommutative (thetaOf θ A) := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  obtain ⟨L, hL⟩ := lcal_nonempty h ha ha1
  obtain ⟨e⟩ := nonempty_mulEquiv_thetaOf h hS ha ha1 hL
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hL
  exact ⟨e.isSimpleGroup, fun hc => hnc ((isMulCommutative_congr e).mp hc)⟩

theorem isWreath_apply
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {L : Subgroup G} (hL : L ∈ lcal (θ a)) :
    IsWreath (θ a ⊔ A) L A (Subgroup.zpowers a) (Subgroup.zpowers a) := by
  have hdp := isDirectProduct_lcal h hS ha ha1
  have hAH : A ≤ Subgroup.normalizer (θ a : Set G) := h.isFunctor.normalized a ha ha1
  have hW : θ a ⊔ A ≤ Subgroup.normalizer (θ a : Set G) := sup_le Subgroup.le_normalizer hAH
  have hset : conjOrbit (θ a ⊔ A) L = lcal (θ a) := by
    ext K
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact map_conj_mem_lcal hL (hW hg)
    · intro hK
      obtain ⟨c, hc, rfl⟩ := exists_conj_eq h ha ha1 hL hK
      exact ⟨c, Subgroup.mem_sup_right hc, rfl⟩
  refine ⟨h.elemAbelian.1, le_sup_right, (lcal_le hL).trans le_sup_left, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le_sup_right (lcal_le hL) A) (sup_le ?_ le_sup_right)
    rw [← hdp.sSup_eq]
    refine sSup_le fun J hJ => ?_
    obtain ⟨c, hc, rfl⟩ := exists_conj_eq h ha ha1 hL hJ
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx))
      (inv_mem (Subgroup.mem_sup_right hc))
  · have h1 : orbitClosure L (θ a ⊔ A) = sSup (conjOrbit (θ a ⊔ A) L) := orbitClosure_eq_sSup _ _
    rw [hset, hdp.sSup_eq] at h1
    show IsDirectProduct (conjOrbit (θ a ⊔ A) L) (orbitClosure L (θ a ⊔ A))
    rw [hset, h1]
    exact hdp
  · exact (inf_normalizer_eq_zpowers h hS ha ha1 hL).symm
  · exact (inf_centralizer_eq_zpowers h hS ha ha1 hL).symm

theorem wreath
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : ∃ K : Subgroup G,
      IsWreath (thetaOf θ F ⊔ A) K A F F ∧ Nonempty (↥K ≃* ↥(thetaOf θ A)) := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  obtain ⟨L, hL⟩ := lcal_nonempty h ha ha1
  obtain ⟨e⟩ := nonempty_mulEquiv_thetaOf h hS ha ha1 hL
  refine ⟨L, ?_, ⟨e.symm⟩⟩
  rw [h.isFunctor.thetaOf_zpowers ha ha1]
  exact isWreath_apply h hS ha ha1 hL

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613
