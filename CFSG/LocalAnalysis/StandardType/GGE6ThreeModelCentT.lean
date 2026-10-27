module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTSpec
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCentE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

theorem tFrame_cent (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.Cent := by
  intro r
  constructor
  · intro hr
    let r' : ModGL Tag.E6 Ω :=
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (r : ModGL TwistTag.E6.tag K)
    let s : ModGL Tag.E6 Ω := g⁻¹ * r' * g
    have hR' : r' ∈ adjointGroup Tag.E6 Ω := by
      have hmemC : r' ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
        Subgroup.mem_map.2 ⟨r.1, r.2, rfl⟩
      exact ((TwistedDiag.mem_Rgrp Fr).1
        ((TwistedDiag.cgrp_facts hn K hK σ.toRingHom hσ h3 Ω Fr hFr).2.1 hmemC)).1
    have hsG : s ∈ adjointGroup Tag.E6 Ω :=
      mul_mem (mul_mem (inv_mem hL.1) hR') hL.1
    have hc : ∀ v ∈ NoOffRest.hypE6,
        rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * s * (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹ = s := by
      intro v hv
      obtain ⟨hx, hxeq⟩ := hD.diag_eq v
      let z : ↥(TwistedDiag.Rgrp Ω Fr) :=
        ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹, hx⟩
      have hr_conj : rgrpConjAut hn hK σ hσ Fr hFr z r = r := by
        rw [← hxeq]; exact hr v hv
      have hb := rgrpConjAut_baseChangeGL hn hK σ hσ Fr hFr z r
      have hbase_eq : baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
          (rgrpConjAut hn hK σ hσ Fr hFr z r).1 = r' := by
        rw [show (rgrpConjAut hn hK σ hσ Fr hFr z r).1 = r.1 from congrArg Subtype.val hr_conj]
      have hconj : (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹) * r' *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹)⁻¹ = r' := by
        rw [hbase_eq] at hb
        rw [show baseChangeGL (τ := Tag.E6) (algebraMap K Ω) r.1 = r' from rfl] at hb
        exact hb.symm
      have hconj' := congrArg (fun y : ModGL Tag.E6 Ω => g⁻¹ * y * g) hconj
      have hkey : g⁻¹ * ((g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹) * r' *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹)⁻¹) * g =
          rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * (g⁻¹ * r' * g) *
            (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹ := by group
      rw [hkey] at hconj'
      rw [show s = g⁻¹ * r' * g from rfl]
      exact hconj'
    have hsT : s ∈ torusGroup Tag.E6 Ω :=
      mem_torusGroup_of_commute_zetaVec (k := Ω) hζo hζ hsG hc
    have hr'T : r' ∈ (torusGroup Tag.E6 Ω).map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.2 ⟨s, hsT, ?_⟩
      change (MulAut.conj g) s = r'
      rw [MulAut.conj_apply]
      rw [show s = g⁻¹ * r' * g from rfl]
      group
    exact (hD.tor_eq r).2 hr'T
  · intro hr v hv
    exact (tFrame_torus hn hK σ hσ Fr hFr h3 hL hζ hζo hD).2.2 v r hr

end CFSG.StandardType.E6ThreeModel
