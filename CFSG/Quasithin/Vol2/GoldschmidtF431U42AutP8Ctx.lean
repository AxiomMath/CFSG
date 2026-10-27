module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6All
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7ZC

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

structure F55Ctx (c : AutCtx G M₁ M₂ z) (R : Subgroup G) : Prop where
  hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB))
  hTR : TfG c ≤ R
  hR64 : Nat.card ↥R = 2 ^ 6
  hnc : ¬ IsConj (c.iso.toG fhB) z
  hfz : IsConj (c.iso.toG fhB * z) z
  h5 : U42AutFusionZ
  h6 : FusionTStmt
  ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB)
  hZ : ZStmt c
  hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤
  hD : Nonempty (↥R ≃* DihedralGroup 4 × DihedralGroup 4)

theorem F55Ctx.of_conf (c : AutCtx G M₁ M₂ z) {R : Subgroup G}
    (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R)
    (hC : Conf437 z (c.iso.toG fhB) (c.iso.imgG That) R)
    (h54 : Conf54 M₁ M₂ (c.iso.toG fhB) R) : F55Ctx c R := by
  have h2 : U42AutSylow := u42AutSylow
  have h5 : U42AutFusionZ := u42AutFusionZ
  have h6 : FusionTStmt := u42AutFusionT h2 h5
  obtain ⟨hR64, hnc, hfz, ⟨t, htT, ht2, htcard, htF⟩, -⟩ := hC
  obtain ⟨c0, hc0⟩ := isConj_iff.1 htF
  have ht : c0⁻¹ * c.iso.toG fhB * c0 = t := by rw [← hc0]; group
  have ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB) :=
    t0_conj_F c h5 (g := c0) (by rw [ht]; exact htT) (by rw [ht]; exact ht2)
      (by rw [ht]; exact htcard)
  exact ⟨hR, hTR, hR64, hnc, hfz, h5, h6, ht0, zStmt c h5 hfz ht0,
    h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso), h54.2.2.2.2.1⟩

end CFSG.Quasithin.H13.F431.U42Aut
