module

public import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockUnitary
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux4
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux6
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux7
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeNbr
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem isBlockOn_permMatrix {d : ℕ} {K : Type} [Field K] {P : Finset (Fin d)}
    {τ : Equiv.Perm (Fin d)} (hτ : ∀ i ∉ P, τ i = i) :
    TableBUE.IsBlockOn P (τ.permMatrix K) := by
  classical
  intro i j hij
  have hiff : τ i = j ↔ i = j := by
    rcases hij with hi | hj
    · rw [hτ i hi]
    · constructor
      · intro h
        exact τ.injective (h.trans (hτ j hj).symm)
      · rintro rfl
        exact hτ i hj
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, hiff]

section Unitary


theorem ggF4Ends_exists_order_three_unitary (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p f : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J ks) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f + 1) (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    ∃ a ∈ ggAutomizer L Bs ⊓ ggAutomizer K Bs, orderOf a = 3 := by
  classical
  obtain ⟨F, hFfield, hFfin, hFchar, hK, ψ, P, h', hd, hrange, hP3, hJ⟩ :=
    ggF4JB_unitary_block hRig hcfg hf hpf hLlab
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hP3
  let σ : Equiv.Perm (Fin 4) := Equiv.swap a b * Equiv.swap a c
  have hσ3 : orderOf σ = 3 := (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf
  have hσfix : ∀ i ∉ ({a, b, c} : Finset (Fin 4)), σ⁻¹ i = i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨hia, hib, hic⟩ := hi
    rw [Equiv.Perm.inv_eq_iff_eq]
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hia hic, Equiv.swap_apply_of_ne_of_ne hia hib]
  have hN := ggNSPosPA_permSU_mem_normalizer h' hd σ⁻¹
  have hgJ : ψ (ggPermSU (K := F) (f := f) σ⁻¹) ∈ J := by
    rw [hJ]
    refine ⟨CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.suEquivUnitarySU F 2 f hK 4
      (ggPermSU (K := F) (f := f) σ⁻¹), ?_, ?_⟩
    · show TableBUE.IsBlockOn {a, b, c} ((σ⁻¹).permMatrix F)
      exact isBlockOn_permMatrix hσfix
    · simp [nsJA2Cover]
  have hJL : J ≤ L := by
    rw [hJ, ← hrange, ← nsJA2Cover_range hK ψ]
    exact Subgroup.map_le_range _ _
  have hlabJ := (ggF4JB_unitary hRig hcfg hf hpf hLlab).1
  have hp : p.Prime := (GGConfig.tableB_facts hcfg.1.1).1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 := (Nat.dvd_add_right h2).mp hpf
    norm_num at h1
  have hpJ : p ∣ Nat.card J :=
    (prime_dvd_card_of_hasLabel_unitary hp hp2 le_rfl hpf hlabJ).trans
      (Subgroup.card_quotient_dvd_card _)
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1.1.1 hcfg.1.1.2.2 hpJ hnbr
  have hmem : ggConjAut Bs hN ∈ ggAutomizer J Bs := ggConjAut_mem_ggAutomizer hgJ hN
  refine ⟨ggConjAut Bs hN, ⟨ggAutomizer_mono Bs hJL hmem, ggAutomizer_mono Bs hJK hmem⟩, ?_⟩
  have hφ : ggConjAut Bs hN =
      ((ggNSPosPA_permAutHom h' hd σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggNSPosPA_permAutHom_apply, ggConjAut_apply]
  rw [hφ, Subgroup.orderOf_coe,
    orderOf_injective _ (ggNSPosPA_permAutHom_injective h' hd) σ, hσ3]

end Unitary

end CFSG.StandardType

end
