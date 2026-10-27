module

public import CFSG.LocalAnalysis.StandardType.GGTwKGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplitTorus
public import CFSG.LocalAnalysis.StandardType.GGKGTwTheta

public section

namespace CFSG.StandardType.KGL.TwLayer

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.StandardType.TwE6EltSmall

variable {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

section Theta


@[expose] noncomputable def twThetaHom (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K (AlgebraicClosure K)))

theorem twThetaHom_apply (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (x : ModGL TwistTag.E6.tag K) :
    twThetaHom g0 x = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g0 := by
  simp [twThetaHom, MulAut.conj_apply]

theorem twThetaHom_injective (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    Function.Injective (twThetaHom (K := K) g0) :=
  (MulAut.conj g0⁻¹).injective.comp (baseChangeGL_injective _)

end Theta

@[expose] noncomputable def twFrobEquiv (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) : AlgebraicClosure K ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective Fr ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos two_pos n)
    exact ⟨x, by rw [hFr, hx]⟩⟩


@[expose] noncomputable def rawTwLang (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (v : WeylGroup TwistTag.E6.tag)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    TwLangData K σ (2 ^ n) ⊥ where
  v := v
  Fr := Fr
  hFr := hFr
  g0 := g0
  hg0C := hg0C
  hg0 := hg0
  c := 1
  hcI := Subgroup.one_mem _
  hc := by
    intro x hx
    rw [Subgroup.mem_bot] at hx
    subst hx
    simpa using Subgroup.one_mem _

theorem range_twThetaHom_eq_Γ (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (v : WeylGroup TwistTag.E6.tag)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    ((twThetaHom g0).comp (twistedE6RootGroup K σ).subtype).range =
      (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).Γ := by
  rw [Γ_eq_map_twistedE6RootGroup Nat.prime_two hn hK hσ hFr _ rfl, MonoidHom.range_comp,
    Subgroup.range_subtype, twThetaHom, Subgroup.map_map]
  rfl

theorem twThetaHom_mem_model (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (v : WeylGroup TwistTag.E6.tag)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {tc : ModGL TwistTag.E6.tag K} (htc : tc ∈ twistedE6InndiagGL K σ) :
    twThetaHom g0 tc ∈ (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).model := by
  obtain ⟨hadj, hfix⟩ := CFSG.StandardType.TwE6RootKill.baseChangeGL_mem_adjointGroup_twistHom_eq
    hσ hFr htc
  rw [model_eq_map_twistedFixedGroup _ rfl]
  exact ⟨baseChangeGL (algebraMap K (AlgebraicClosure K)) tc,
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hadj, hfix⟩, by
      simp [twThetaHom_apply, MulAut.conj_apply] <;> rfl⟩

theorem map_centralizer_twThetaHom (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (v : WeylGroup TwistTag.E6.tag)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {t : ModGL TwistTag.E6.tag K} {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (hta : rootDiagUnit Tag.E6 a = twThetaHom g0 t) :
    ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ)).map ((twThetaHom g0).comp (twistedE6RootGroup K σ).subtype) =
      (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).Γ ⊓
        Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
  have hrange := range_twThetaHom_eq_Γ hn hK hσ Fr hFr v g0 hg0C hg0
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hcΓ : ((twThetaHom g0).comp (twistedE6RootGroup K σ).subtype) c ∈
        (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0).Γ := by
      rw [← hrange]
      exact ⟨c, rfl⟩
    refine ⟨hcΓ, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have hh' : h = rootDiagUnit Tag.E6 a := hh
    subst hh'
    have hc' : t * (c : ModGL TwistTag.E6.tag K) = (c : ModGL TwistTag.E6.tag K) * t :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hc) t rfl
    have h2 := congrArg (twThetaHom g0) hc'
    rw [map_mul, map_mul, ← hta] at h2
    exact h2
  · rintro ⟨hyΓ, hyC⟩
    rw [← hrange] at hyΓ
    obtain ⟨c, rfl⟩ := hyΓ
    refine ⟨c, Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_), rfl⟩
    have hh' : h = t := hh
    rw [hh']
    have h2 := Subgroup.mem_centralizer_iff.1 hyC (rootDiagUnit Tag.E6 a) rfl
    have h3 : twThetaHom g0 (t * (c : ModGL TwistTag.E6.tag K)) =
        twThetaHom g0 ((c : ModGL TwistTag.E6.tag K) * t) := by
      rw [map_mul, map_mul, ← hta]
      exact h2
    exact twThetaHom_injective g0 h3

end CFSG.StandardType.KGL.TwLayer

end
