module

public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeWeyl
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutFrame
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public noncomputable section

namespace CFSG.StandardType.E6RelativeWeyl

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K] {p : ℕ} (σ : K ≃+* K)
  (hp : p.Prime) {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ)

theorem exists_scalar_weyl_of_map_stdFrame_eq {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp5 : 5 ≤ p) (hζo : orderOf ζ = p)
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ)).range.map α.toMonoidHom =
      (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ)).range) :
    ∃ c : (ZMod p)ˣ, ∃ u : WeylGroup Tag.F4,
      ∀ s : Fin Tag.F4.rank → ZMod p,
        α (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
            (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)) =
          stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
            (hζ := hζ) (hζσ := hζσ)
            (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct Tag.F4 p u s)) := by
  classical
  let C0 := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  let E : Subgroup C0 :=
    (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
      (hζ := hζ) (hζσ := hζσ)).range
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have : Finite C0 := Subtype.finite
  obtain ⟨g, u, δ, hαform⟩ :=
    exists_normalForm_E6 (p := 2) (f := n) (K := K)
      Nat.prime_two hn hK σ hσ α
  obtain ⟨m, hm⟩ := NoTvAut.exists_units_map_eq_pow (p := p) (ζ := ζ) hζo δ.toRingHom
  have hcop : Nat.Coprime m p :=
    NoTvAut.coprime_of_units_map_eq_pow (p := p) hp hζo δ.toRingHom hm
  have hdiag : ∀ s : Fin Tag.F4.rank → ZMod p,
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u
        (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)) =
      stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s) := by
    intro s
    apply Subtype.ext
    rw [coe_compatDiagAutHom]
    change rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ
          (ExcFrames.twE6SplitTheta p s) *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ =
      ExcFrames.frameDiag (τ := TwistTag.E6.tag) ζ hζ (ExcFrames.twE6SplitTheta p s)
    rw [ExcFrames.frameDiag]
    rw [← rootDiagUnit_mul]
    rw [mul_comm (compatDiag TwistTag.E6 σ.toRingHom u)
      (TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s)))]
    rw [rootDiagUnit_mul]
    group
  have hfield : ∀ s : Fin Tag.F4.rank → ZMod p,
      fieldActor σ δ (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)) =
      stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd (m • s)) := by
    intro s
    apply Subtype.ext
    rw [coe_fieldActor]
    have hpow : (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd (m • s)) : C0) =
        (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)) ^ m := by
      rw [← map_pow]
      rw [ofAdd_nsmul]
    rw [hpow, Subgroup.coe_pow]
    have hv : (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s) :
        ModGL TwistTag.E6.tag K) ∈ ExcFrames.splitPow TwistTag.E6.tag K p := by
      refine ⟨?_, ?_⟩
      · have hT := CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup
          (TableBExc.E6Three.zetaVec ζ hζ
            (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s)))
          (by
            change (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
                (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s) :
              ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K
            exact (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans inf_le_left
              (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
                (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)).2)
        change rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ
            (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s))) ∈
          torusGroup TwistTag.E6.tag K
        exact hT
      · have hp1 := ExcFrames.frameDiag_pow (τ := TwistTag.E6.tag) ζ hζ
          (ExcFrames.twE6SplitTheta p s)
        change rootDiagUnit TwistTag.E6.tag
          (TableBExc.E6Three.zetaVec ζ hζ
            (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s))) ^ p = 1
        exact hp1
    exact NoTvAut.units_map_entrywise_eq_pow (τ := TwistTag.E6.tag) (p := p)
      (σ := δ.toRingHom) hm hv
  have hβ : ∀ s : Fin Tag.F4.rank → ZMod p,
      normalActor σ u δ (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)) =
      stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd (m • s)) := by
    intro s
    rw [normalActor, MulAut.mul_apply, hfield s, hdiag (m • s)]
  have hβmap : E.map (normalActor σ u δ).toMonoidHom = E := by
    have hle : E.map (normalActor σ u δ).toMonoidHom ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, rfl⟩ := hx
      exact ⟨Multiplicative.ofAdd (m • s), (hβ s).symm⟩
    have hcard : Nat.card (E.map (normalActor σ u δ).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (normalActor σ u δ).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hβinv_le : E.map ((normalActor σ u δ)⁻¹).toMonoidHom ≤ E := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ E.map (normalActor σ u δ).toMonoidHom := by
      rw [hβmap]
      exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    rw [← hzy]
    have hzz : ((normalActor σ u δ)⁻¹) ((normalActor σ u δ) z) = z :=
      MulAut.inv_apply_self _ (normalActor σ u δ) z
    change ((normalActor σ u δ)⁻¹) ((normalActor σ u δ) z) ∈ E
    rw [hzz]
    exact hz
  have hconj_le : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    have hxβ : ((normalActor σ u δ)⁻¹) x ∈ E :=
      hβinv_le ⟨x, hx, rfl⟩
    have hαx : α (((normalActor σ u δ)⁻¹) x) ∈ E := by
      have hx' : α (((normalActor σ u δ)⁻¹) x) ∈ E.map α.toMonoidHom :=
        ⟨_, hxβ, rfl⟩
      rwa [hα] at hx'
    have h1 : MulAut.conj g = α * (normalActor σ u δ)⁻¹ := by
      rw [hαform]
      group
    change MulAut.conj g x ∈ E
    rw [h1, MulAut.mul_apply]
    exact hαx
  have hconjmap : E.map (MulAut.conj g).toMonoidHom = E := by
    have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact Subgroup.eq_of_le_of_card_ge hconj_le (le_of_eq hcard.symm)
  have hg : g ∈ Subgroup.normalizer (E : Set C0) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjmap
  obtain ⟨w, hw⟩ := normalizer_action (K := K) (σ := σ.toRingHom) (p := p)
    (hp := hp) (hp5 := hp5) (hζo := hζo) (hζ := hζ) (hζσ := hζσ) g hg
  refine ⟨ZMod.unitOfCoprime m hcop, w, fun s => ?_⟩
  have hlin : TableBExc.torusAct Tag.F4 p w (m • s) =
      m • TableBExc.torusAct Tag.F4 p w s := by
    rw [← NoTvAut.torusActHom_apply w (m • s),
      ← NoTvAut.torusActHom_apply w s]
    exact map_nsmul _ m _
  calc
    α (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
        (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s)) =
        MulAut.conj g (normalActor σ u δ
          (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
            (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd s))) := by
      rw [hαform]
      rfl
    _ = MulAut.conj g (stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ) (Multiplicative.ofAdd (m • s))) := by
      rw [hβ s]
    _ = stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ)
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p w (m • s))) := by
      rw [MulAut.conj_apply]
      exact hw (m • s)
    _ = stdFrame (K := K) (σ := σ.toRingHom) (p := p) (hp := hp)
          (hζ := hζ) (hζσ := hζσ)
          (Multiplicative.ofAdd ((ZMod.unitOfCoprime m hcop : ZMod p) •
            TableBExc.torusAct Tag.F4 p w s)) := by
      congr 1
      rw [ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul, ← hlin]

end CFSG.StandardType.E6RelativeWeyl
