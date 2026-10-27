module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwD4Datum
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwStep
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenLabels

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.Assembly Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem orbitRankOneGroup_three_le_iSup_phiTwoCompIn_d4
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    {T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥(twistedE6RootGroup K σ)}
    (hTinj : Function.Injective T)
    (hT : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {VG W : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p)} (hVW : IsCompl VG W)
    (hdim : Module.finrank (ZMod p) VG = 4)
    (hVG : ∀ t ∈ VG, T (ofAdd t) ∈ ⨆ i, (frameHom σ.toRingHom i).range)
    (hW : ∀ t ∈ W, T (ofAdd t) ∈ (torusG σ.toRingHom).range) :
    orbitRankOneGroup TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ≤
      (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
        phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1).map (twistedE6RootGroup K σ).subtype := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨θ, hYX, hYZ, hYM, hYF, hYC⟩ := exists_d4Datum_twE6 hn hK σ hσ
  have hRadj : twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K := fun g hg =>
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).mp
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hg)).1
  have hσ' : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = 2 ^ n :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two (by omega) hK hσ'
  have hpk : p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) + 1 := by
    rw [hkcard]
    exact hpq
  have hrow := ggTorusRootGenAvoidKG_omegaPlusNs
    (K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) (n := n) (m := 4) hkcard hn
    (by norm_num) hp hp2 hpk 3
  have hker : θ.toMonoidHom.ker ≤ Subgroup.center ↥(d4Group σ.toRingHom) := by
    intro x hx
    have hx1 : x = 1 := θ.injective (by rw [map_one]; exact MonoidHom.mem_ker.mp hx)
    rw [hx1]
    exact Subgroup.one_mem _
  have hstep := range_le_iSup_phiTwoCompIn_of_row (τ := TwistTag.E6.tag) (Or.inl rfl) hp2 hζo hζ
    hg0C hRadj hTinj hT (X := ↥(d4Group σ.toRingHom)) (Ψ := (d4Group σ.toRingHom).subtype)
    Subtype.val_injective hYX
    (fun z hz _ => hYZ z fun x => (Subgroup.mem_center_iff.mp hz x).symm) hrow θ.toMonoidHom
    θ.surjective hker (fun x => ⟨θ x, rfl⟩) hVW
    (fun t ht => by
      rw [Subgroup.range_subtype]
      exact hYF (hVG t ht))
    (fun t ht x hx => by
      rw [Subgroup.range_subtype] at hx
      exact hYC x hx _ (hW t ht))
    (by omega) (by omega)
  rw [Subgroup.range_subtype] at hstep
  exact hYM.trans (Subgroup.map_mono hstep)

end CFSG.StandardType.PhiTwoRootGen

end
