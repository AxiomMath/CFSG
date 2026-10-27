module

public import CFSG.LocalAnalysis.StandardType.GGHalfInnerAssembly
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphNbr
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphData
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylHolds
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private theorem ggHalfCore_card_two_eq_zero_or_one {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  rcases eq_or_ne x 0 with h | h
  · exact Or.inl h
  · right
    obtain ⟨y, hy0, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hcard
    rw [hy x h, hy 1 one_ne_zero]

private theorem ggHalfCore_closure_slE_eq_top :
    Subgroup.closure {g : SpecialLinearGroup (Fin 6) F2 | ∃ c d : Fin 6, c ≠ d ∧ g = slE c d} =
      ⊤ := by
  apply CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
  intro i j hij c
  have hcard : Nat.card F2 = 2 := by simpa using GaloisField.card 2 1 (by omega)
  rcases ggHalfCore_card_two_eq_zero_or_one hcard c with rfl | rfl
  · rw [SpecialLinearGroup.transvection_coeff_zero hij]
    exact Subgroup.one_mem _
  · have hE : slE i j = SpecialLinearGroup.transvection hij (1 : F2) := by
      rw [slE, dif_neg hij]
    rw [← hE]
    exact Subgroup.subset_closure ⟨i, j, hij, rfl⟩

private theorem ggHalfCore_le_range_of_K_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (m : GGHalfE6Model) (φ : GGE6Two →* G)
    (hK : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .K (GGHalfBlk.K.lab c) (GGHalfBlk.K.lab d))) = φ₂ (slE c d)) :
    K ≤ φ.range := by
  rw [← h.coords.range₂, MonoidHom.range_eq_map, ← ggHalfCore_closure_slE_eq_top]
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨c, d, hcd, rfl⟩
  show φ₂ (slE c d) ∈ φ.range
  rw [← hK c d hcd]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

namespace GGHalfCtx

theorem secFive_of_core
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (hKG : GGHalfNbrCentInput) (hCert : GGHalfE6Cert) :
    GGSecFiveData p B x L D J ∧ GGSecFiveCompat p B x L D J := by
  by_cases hα : GGHalfAlphaInner φ₁ φ₂
  · exact ⟨secFiveData_of_alphaInner h hα hRig hTP hLB hKG,
      secFiveCompat_of_alphaInner h hα hRig hTP hLB hKG⟩
  · have hm3le : 3 ≤ m := by have := h.nbr.2.2.1; omega
    have hm3 : m = 3 := by
      by_contra hne
      exact hα (alphaInner_of_six_le h (by omega))
    subst hm3
    obtain ⟨m₀, hgood, hX1, hXm⟩ := hCert
    obtain ⟨φ, hinj, hrange, hL, hK, hv, hw, hJ⟩ := exists_e6_of_graph h hα m₀ hgood
    have hKrange : K ≤ φ.range := ggHalfCore_le_range_of_K_frame h m₀ φ hK
    have hnbr : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ φ.range :=
      fun y' K' hn => nbr_le_range_of_graph h hRig hTP hLB m₀ hX1 hXm φ hinj hv hw hJ hKrange hn
    exact ⟨secFiveData_of_graph h m₀ hgood φ hinj hrange hL hnbr,
      secFiveCompat_of_graph h m₀ hgood φ hinj hrange hL hnbr⟩

end GGHalfCtx

private theorem ggHalfCore_secFive_pair
    (hRig : GGLabelRigidInput) (hTP : GGNbrTablePNbrInputOn GGRegimeAm2)
    (hLB : GGLBalanceInput) (hsub : GGNbrSubcomponentInput) (hKG : GGHalfNbrCentInput)
    (hCert : GGHalfE6Cert)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeAHalfNbr p B Bs x L D J (m + 1 + 1) y K) :
    GGSecFiveData p B x L D J ∧ GGSecFiveCompat p B x L D J := by
  obtain ⟨φ₁, φ₂, hcoords⟩ :=
    (ggTypeAHalfCoordInput_of_subcomponent hsub) G p B Bs x L D J m y K hcfg hInn hN
  exact GGHalfCtx.secFive_of_core ⟨hcfg, hInn, hNoTr, hN, hcoords⟩ hRig hTP hLB hKG hCert

theorem ggTypeAHalfLargeAutInput_of_core
    (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (hsub : GGNbrSubcomponentInput) (hKG : GGHalfNbrCentInput) (hCert : GGHalfE6Cert) :
    GGTypeAHalfLargeAutInput := by
  intro G _ _ p B Bs x L D J n y K hR hW hnA hN hAut
  obtain ⟨hcfg, -, hInn, hNoTr, -, -⟩ := hR
  have hN' : GGTypeAHalfNbr p B Bs x L D J (n - 2 + 1 + 1) y K := by
    have : n - 2 + 1 + 1 = n := by have := hN.2.2.1; omega
    rw [this]
    exact hN
  exact (ggHalfCore_secFive_pair (m := n - 2) hRig hTP hLB hsub hKG hCert hcfg hInn hNoTr hN').1

theorem ggSecFiveCompatHalfLargeInput_of_core
    (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (hsub : GGNbrSubcomponentInput) (hKG : GGHalfNbrCentInput) (hCert : GGHalfE6Cert) :
    GGSecFiveCompatHalfLargeInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW t n f ψ hpres m y K hN hAut
  have hN' : GGTypeAHalfNbr p B Bs x L D J (m - 2 + 1 + 1) y K := by
    have : m - 2 + 1 + 1 = m := by have := hN.2.2.1; omega
    rw [this]
    exact hN
  exact (ggHalfCore_secFive_pair (m := m - 2) hRig hTP hLB hsub hKG hCert hcfg hInn hNoTr hN').2

end CFSG.StandardType

end
