module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwA5Datum
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwStep
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenAsm

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.Assembly Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem orbitRankOneGroup_le_iSup_phiTwoCompIn_a5
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
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
    (hdim : Module.finrank (ZMod p) VG = 5)
    (hVG : ∀ t ∈ VG, T (ofAdd t) ∈
      (frameHom σ.toRingHom 0).range ⊔ (frameHom σ.toRingHom 1).range ⊔
        (frameHom σ.toRingHom 2).range ⊔ (torusG σ.toRingHom).range)
    (hW : ∀ t ∈ W, T (ofAdd t) ∈ (frameHom σ.toRingHom 3).range) :
    ∀ a : Fin TwistTag.E6.foldedTag.rank, a.val ≤ 2 →
      orbitRankOneGroup TwistTag.E6 K σ.toRingHom a ≤
        (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
          phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1).map (twistedE6RootGroup K σ).subtype := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Y, θ, hθs, hθk, hYX, hYZ, hYI, hYM, hYF, hYC⟩ := exists_a5Datum_twE6 hn hK σ hσ hp5
  have hRadj : twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K := fun g hg =>
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).mp
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hg)).1
  have hpd : ¬ p ∣ 6 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    have h56 : p = 5 ∨ p = 6 := by omega
    rcases h56 with h5 | h6
    · rw [h5] at h
      omega
    · exact absurd hp (by rw [h6]; norm_num)
  have hrow := ggTorusRootGenAvoidKG_unitaryCoprime hK hn (by norm_num : 3 ≤ 6) hp hpq hpd 3
  have hstep := range_le_iSup_phiTwoCompIn_of_row (τ := TwistTag.E6.tag) (Or.inl rfl) hp2 hζo hζ
    hg0C hRadj hTinj hT (X := ↥Y) (Ψ := Y.subtype) Subtype.val_injective hYX hYZ hrow θ hθs hθk
    hYI hVW
    (fun t ht => by
      rw [Subgroup.range_subtype]
      exact hYF (hVG t ht))
    (fun t ht x hx => by
      rw [Subgroup.range_subtype] at hx
      exact hYC x hx _ (hW t ht))
    (by omega) (by omega)
  rw [Subgroup.range_subtype] at hstep
  intro a ha
  exact (hYM a ha).trans (Subgroup.map_mono hstep)

end CFSG.StandardType.PhiTwoRootGen

end
