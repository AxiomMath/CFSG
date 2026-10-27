module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7S3F
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cj
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7R
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6All

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

theorem quot_equiv_congr {G : Type} [Group G] {A A' : Subgroup G} (h : A = A') {P : Type}
    [Group P] (h1 : Nonempty (↥(Subgroup.normalizer (A : Set G)) ⧸
      A.subgroupOf (Subgroup.normalizer (A : Set G)) ≃* P)) :
    Nonempty (↥(Subgroup.normalizer (A' : Set G)) ⧸
      A'.subgroupOf (Subgroup.normalizer (A' : Set G)) ≃* P) := by
  subst h
  exact h1

theorem conf54_std {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}
    (c : AutCtx G M₁ M₂ z)
    {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R)
    (hC : Conf437 z (c.iso.toG fhB) (c.iso.imgG That) R) :
    Conf54 M₁ M₂ (c.iso.toG fhB) R := by
  have h2 : U42AutSylow := u42AutSylow
  have h4 : NotExtremalStmt := u42AutNotExtremal h2 u42AutFusion
  have h5 : U42AutFusionZ := u42AutFusionZ
  obtain ⟨-, -, hfz, ⟨t, htT, ht2, htcard, htF⟩, -⟩ := hC
  obtain ⟨c0, hc0⟩ := isConj_iff.1 htF
  have ht : c0⁻¹ * c.iso.toG fhB * c0 = t := by rw [← hc0]; group
  have ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB) :=
    t0_conj_F c h5 (g := c0) (by rw [ht]; exact htT) (by rw [ht]; exact ht2)
      (by rw [ht]; exact htcard)
  have hZ : ZStmt c := zStmt c h5 hfz ht0
  have hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤ := h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso)
  refine ⟨centralizer_aOf_M1 c, centralizer_aOf_M2 c, card_aOf_M1 c.iso, card_aOf_M2 c.iso,
    R_equiv c h2 h4 h5 hR hTR, ?_, ?_, ?_⟩
  · rw [aOf_M2]
    exact card_normalizer_A2 c hZ hT₀G
  · exact quot_equiv_congr (aOf_M2 c.iso).symm (normalizer_A2_equiv c hZ hT₀G)
  · exact quot_equiv_congr (aOf_M1 c.iso).symm (normalizer_A1_equiv c hZ hT₀G)

theorem u42AutF54 : U42AutF54 := by
  intro G _ _ M₁ M₂ z c T hT f hfT hf R hR hTR hC
  obtain ⟨g, hgB, -, hTg, hfg⟩ := exists_norm c hT hfT hf
  have hF : (c.conj hgB).iso.toG fhB = f := by
    rw [hfg]
    exact AutIso.toG_conjIso c.iso hgB fhB
  have hT' : (c.conj hgB).iso.imgG That = T := by
    rw [hTg]
    exact AutIso.imgG_conjIso c.iso hgB That
  rw [← hF] at hR hTR hC ⊢
  rw [← hT'] at hTR hC
  exact conf54_std (c.conj hgB) hR hTR hC

end CFSG.Quasithin.H13.F431.U42Aut
