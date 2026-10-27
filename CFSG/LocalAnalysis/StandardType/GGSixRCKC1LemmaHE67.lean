module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1L5
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.StandardType CFSG.Open

private theorem rckHE67_cent_minDatum
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {D : CFSG.LieType.Steinberg.Minuscule.MinData τ} (hV : D.Valid)
    (hA : TauCeti.IsFiniteType τ.cartan) (k : Type) [Field k] (β : Fin τ.rank → ℤ) :
    RCKLemmaHCent ⟨↥(hV.minGroup k), hV.minDatum hA k⟩ β := by
  intro x hx hx1 g hg
  obtain ⟨c₀, rfl⟩ := (hV.mem_rootGroup k).1 hx
  have hc₀ : c₀ ≠ 0 := fun hc => hx1 (by rw [hc, hV.xm_zero])
  have hgx : g * hV.xm k β c₀ = hV.xm k β c₀ * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hcomm : Commute (hV.endo k g) (1 + c₀ • D.rootOp k β) := by
    have h := congrArg (hV.endo k) hgx
    rw [hV.endo_mul, hV.endo_xm] at h
    exact h
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hy
  apply Subtype.ext
  apply Units.ext
  show hV.endo k (hV.xm k β c * g) = hV.endo k (g * hV.xm k β c)
  rw [hV.endo_mul, hV.endo_xm]
  exact (commute_one_add_smul_of_ne_zero hc₀ hcomm c).symm.eq

theorem rck_lemmaHC_E67
    {t' : StatedLieTag} (ht : t' = .E6 ∨ t' = .E7) {m g : ℕ} (hg : 1 ≤ g)
    {β : Fin (ggU t' m g).D.rank → ℤ} (hβ : GGLongRoot (ggU t' m g).D β) :
    RCKLemmaHCent (ggU t' m g) β := by
  rcases ht with rfl | rfl
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact rckHE67_cent_minDatum CFSG.LieType.Steinberg.Minuscule.e6Data_valid
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6 (GaloisField 2 g) β
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact rckHE67_cent_minDatum CFSG.LieType.Steinberg.Minuscule.e7Data_valid
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7 (GaloisField 2 g) β

end CFSG.StandardType.RCKC1
