module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreTransport

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def m12Pairs : Subgroup (Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) :=
  Subgroup.closure {(m12gA, m12gA), (m12gB, m12bp)}

theorem blockHom_injective : Function.Injective blockHom :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Equiv.Perm.sumCongrHom_injective

theorem m12D_eq_closure : m12D.originalSubgroup = Subgroup.closure {g | g ∈ [m12A1, m12B1]} :=
  certificate_originalSubgroup _ _ _ _ _

theorem m12D_originalSubgroup : m12D.originalSubgroup = m12Pairs.map blockHom := by
  rw [m12D_eq_closure, m12Pairs, MonoidHom.map_closure, Set.image_pair]
  congr 1
  ext g
  simp [m12A1, m12B1]

theorem m12_gens_memD : ∀ g ∈ [m12A1, m12B1], g ∈ m12D.originalSubgroup := fun g hg => by
  rw [m12D_eq_closure]
  exact Subgroup.subset_closure hg

theorem m12Pairs_card : Nat.card m12Pairs = 95040 := by
  rw [← Subgroup.card_map_of_injective blockHom_injective, ← m12D_originalSubgroup,
    ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]

theorem m12Pairs_fst : m12Pairs.map (MonoidHom.fst _ _) = NativeSporadic.M12 := by
  rw [m12Pairs, MonoidHom.map_closure, m12_eq, Set.image_pair]
  rfl

@[expose] noncomputable def m12Proj : m12Pairs →* NativeSporadic.M12 :=
  ((MonoidHom.fst _ _).comp m12Pairs.subtype).codRestrict NativeSporadic.M12 fun d => by
    rw [← m12Pairs_fst]
    exact ⟨d, d.2, rfl⟩

theorem m12Proj_bijective :
    Function.Bijective m12Proj := by
  have hsurj : Function.Surjective m12Proj := by
    intro g
    have hg : (g : Equiv.Perm (Fin 12)) ∈ m12Pairs.map (MonoidHom.fst _ _) := by
      rw [m12Pairs_fst]
      exact g.2
    obtain ⟨d, hd, hdg⟩ := hg
    exact ⟨⟨d, hd⟩, Subtype.ext hdg⟩
  exact hsurj.bijective_of_nat_card_le (by rw [m12Pairs_card, m12_card])

@[expose] noncomputable def m12EquivD :
    NativeSporadic.M12 ≃* m12D.originalSubgroup :=
  (MulEquiv.ofBijective m12Proj m12Proj_bijective).symm.trans
    ((m12Pairs.equivMapOfInjective blockHom blockHom_injective).trans
      (MulEquiv.subgroupCongr m12D_originalSubgroup.symm))

theorem m12D_sigma_normalizes :
    ∀ h ∈ m12D.originalSubgroup, m12Sigma * h * m12Sigma⁻¹ ∈ m12D.originalSubgroup := by
  obtain ⟨-, hsa, hsb, -⟩ := m12_sigma_check
  have hsift := (m12D.schreier_chain_order m12D_check.1).2.2.2.1
  refine conj_mem_of_closure m12D_eq_closure ?_
  intro s hs
  rcases List.mem_pair.1 hs with rfl | rfl
  · exact (hsift _).1 hsa
  · exact (hsift _).1 hsb

theorem m12D_sigma_sq :
    m12Sigma * m12Sigma ∈ m12D.originalSubgroup := by
  rw [m12_sigma_check.1]
  exact one_mem _

theorem m12D_center :
    Subgroup.center m12D.originalSubgroup = ⊥ := by
  rw [← center_map_equiv m12EquivD, m12_center_eq_bot', Subgroup.map_bot]

theorem m12D_mulAut_card :
    Nat.card (MulAut m12D.originalSubgroup) ≤ 2 * Nat.card m12D.originalSubgroup :=
  mulAut_card_of_equiv m12EquivD.symm m12_mulAut_card

theorem m12D_sigma_outer : ∀ g ∈ m12D.originalSubgroup,
    ¬∀ h ∈ m12D.originalSubgroup, m12Sigma * g * h = h * (m12Sigma * g) :=
  not_centralizes_of_count (by norm_num) m12D m12D_check.1 (m12_gens_memD _ (by simp))
    (m12_gens_memD _ (by simp)) m12_sigma_check.2.2.2

theorem m12D_outer_witness :
    ∀ u, m12Sigma⁻¹ * u ∈ m12D.originalSubgroup → orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn m12D.originalSubgroup u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn m12D.originalSubgroup u) mu := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, hsz, hord⟩ := m12_sigma_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m12_sigma_cent
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hK : m12SigmaCentQ.originalSubgroup ≤ centralizerIn m12D.originalSubgroup m12Sigma := by
    rw [m12SigmaCentQ, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_memD w) hcomm
  have hKc : Nat.card m12SigmaCentQ.originalSubgroup = 120 := by
    rw [← m12SigmaCentQ.orderCertificate_eq_card hc, ho]
  refine centralizer_witness_of_reps hn m12D m12D_check.1 (pairTables_spec hn hA hB) m12Sigma
    (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq)
    [(m12Sigma, m12SigmaCentQ.originalSubgroup, 15, 3)] ?_ 1000 hok ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨by simp, ?_⟩
    exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hK, ?_, by rw [hKc]; norm_num, oddWitness_of_oddWitnessOK hn _ hc hw⟩
    rw [hsz, hKc, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]

theorem m12D_outer_oddCore
    (α : MulAut m12D.originalSubgroup) (hα2 : α * α = 1)
    (hα : α ∉ inner m12D.originalSubgroup) : CFSG.oddCore (fixSub α) = ⊥ :=
  outer_oddCore_eq_bot _ m12Sigma m12D_sigma_normalizes m12D_sigma_sq m12D_center
    m12D_sigma_outer m12D_mulAut_card m12D_outer_witness α hα2 hα

theorem m12_outer_oddCore
    (α : MulAut NativeSporadic.M12) (hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M12) : CFSG.oddCore (fixSub α) = ⊥ :=
  outer_of_equiv m12EquivD m12D_outer_oddCore α hα2 hα

end CFSG.Sporadic.Schreier
