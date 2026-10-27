module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6All
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Fz
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Good
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Mov

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

theorem conf437_std {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}
    (c : AutCtx G M₁ M₂ z) (h2 : U42AutSylow) (h4 : NotExtremalStmt) (h5 : U42AutFusionZ)
    (h6 : FusionTStmt) {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R) :
    Conf437 z (c.iso.toG fhB) (c.iso.imgG That) R := by
  have hcard := card_R c h2 h4 h5 hR hTR
  obtain ⟨n, hn, hnz⟩ := exists_moving c hR hTR (Tf_ne c h4 hR)
  have hfz := fz_conj c h5 h6 (Subgroup.mem_inf.1 hn).2 hnz
  obtain ⟨g, ht, ht2, htcard⟩ := exists_t c h2 h5 hR hcard
  have ht0 := t0_conj_F c h5 ht ht2 htcard
  refine ⟨hcard, F_notConj c h5, hfz,
    ⟨g⁻¹ * c.iso.toG fhB * g, ht, ht2, htcard, isConj_iff.2 ⟨g, by group⟩⟩, ?_⟩
  intro u hu2 hu1
  exact all_inv c h2 hfz ht0 hu2 hu1

theorem conjSub_inv_conjSub {G : Type} [Group G] (g : G) (X : Subgroup G) :
    B6.conjSub g⁻¹ (B6.conjSub g X) = X := by
  rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]

theorem conjSub_conjSub_inv {G : Type} [Group G] (g : G) (X : Subgroup G) :
    B6.conjSub g (B6.conjSub g⁻¹ X) = X := by
  rw [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]

theorem u42AutInv :
    U42AutInv := by
  intro h2 h4 h5 G _ _ M₁ M₂ z c T hT f hfT hf R hR hTR
  have h6 : FusionTStmt := u42AutFusionT h2 h5
  obtain ⟨g, -, hgz, hTg, hfg⟩ := exists_norm c hT hfT hf
  have hF : g⁻¹ * f * g⁻¹⁻¹ = c.iso.toG fhB := by
    rw [hfg]
    group
  have hR₀ : IsSylowTwoOf (B6.conjSub g⁻¹ R) (cenOf (c.iso.toG fhB)) := by
    have := B6.isSylowTwoOf_conjSub hR g⁻¹
    rwa [conjSub_cenOf, hF] at this
  have hTR₀ : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ B6.conjSub g⁻¹ R := by
    have h := (B6.conjSub g⁻¹).monotone hTR
    rwa [(B6.conjSub g⁻¹).map_inf, conjSub_cenOf, hF, hTg, conjSub_inv_conjSub] at h
  have h0 := Conf437.of_conj g hgz (conf437_std c h2 h4 h5 h6 hR₀ hTR₀)
  rwa [← hfg, ← hTg, conjSub_conjSub_inv] at h0

end CFSG.Quasithin.H13.F431.U42Aut
