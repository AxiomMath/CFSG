module

public import CFSG.Quasithin.Background.P3G2Zorn
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem derived_le_cayley (K : Type) [Field K] [CharP K 2] :
    ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K :=
  (Subgroup.commutator_le_self _).trans
    (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le

theorem natural_transport {K K' : Type} [Field K] [Field K'] [CharP K 2] [CharP K' 2]
    (τ : K ≃+* K') {L : Subgroup (GLV V)} (e : ↥L ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (φ : V ≃+ (Ix3 → K))
    (hφ : ∀ (h : ↥L) (v : V),
      φ ((h : GLV V) v) = g2Act ⟨(e h : quasithinZorn K ≃ₗ[K] quasithinZorn K),
        derived_le_cayley K (e h).2⟩ (φ v)) :
    ∃ (e' : ↥L ≃* ↥⁅quasithinG2 K', quasithinG2 K'⁆) (φ' : V ≃+ (Ix3 → K')),
      ∀ (h : ↥L) (v : V),
        φ' ((h : GLV V) v) = g2Act ⟨(e' h : quasithinZorn K' ≃ₗ[K'] quasithinZorn K'),
          derived_le_cayley K' (e' h).2⟩ (φ' v) := by
  have hq : quasithinG2 K = cayleyGroup K := CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup
  have hq' : quasithinG2 K' = cayleyGroup K' := CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup
  have hmap : (⁅quasithinG2 K, quasithinG2 K⁆).map
      (zornConj τ : (quasithinZorn K ≃ₗ[K] quasithinZorn K) →*
        (quasithinZorn K' ≃ₗ[K'] quasithinZorn K')) = ⁅quasithinG2 K', quasithinG2 K'⁆ := by
    rw [hq, hq']
    exact map_cayley_commutator τ
  let ζ : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅quasithinG2 K', quasithinG2 K'⁆ :=
    ((zornConj τ).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  let ρ : (Ix3 → K) ≃+* (Ix3 → K') := RingEquiv.piCongrRight fun _ : Ix3 => τ
  refine ⟨e.trans ζ, φ.trans ρ.toAddEquiv, fun h v => ?_⟩
  have h1 := g2Act_zornConj τ ⟨(e h : quasithinZorn K ≃ₗ[K] quasithinZorn K),
    derived_le_cayley K (e h).2⟩ (φ v)
  change ρ (φ ((h : GLV V) v)) = _
  rw [hφ h v, h1]
  rfl

end CFSG.Quasithin.G11.Harris.G2
