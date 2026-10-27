module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover
open CFSG.Yardstones.Md0ec50421ce4

private theorem kg7innd_pquot_le_center {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple ↥L)
    (hmark : CFSG.Assembly.LargeEvenMarking (PQuot 3 L) (fun _ _ _ _ _ _ => True)) :
    CFSG.Open.GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L := by
  rcases CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.normal_le_center_or_eq_top
      (⟨hL.1⟩ : Group.IsPerfect ↥L) hL.2 (CFSG.Open.GLAPPrimeCore 3 ↥L) with hle | htop
  · exact hle
  · exfalso
    obtain ⟨-, lab, hlab, hraw⟩ := hmark
    obtain ⟨S, _, I, F, _hs, hna, θ, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    haveI : Subsingleton (PQuot 3 L) := by
      change Subsingleton (↥L ⧸ CFSG.Open.GLAPPrimeCore 3 ↥L)
      rw [QuotientGroup.subsingleton_iff]
      exact htop
    obtain ⟨a, b, hab⟩ := hna
    have hab' : a = b := θ.symm.injective (Subsingleton.elim (θ.symm a) (θ.symm b))
    exact hab (by rw [hab'])

private theorem kg7innd_largeEvenMarking_centerQuot {X Y : Type*} [Group X] [Group Y]
    (e : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) (hX : commutator X = ⊤)
    {P : LargeEvenMarkProp X} {P' : LargeEvenMarkProp Y}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R),
      P' lab R I F θ → P lab R I F (e.trans θ))
    (h : CFSG.Assembly.LargeEvenMarking Y P') :
    CFSG.Assembly.LargeEvenMarking X P := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, e.trans θ, hPP' lab R I F θ hθ⟩

private theorem kg7innd_mulAut_conj_conj {X : Type*} [Group X] (α : MulAut X) (x : X) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  refine MulEquiv.ext fun y => ?_
  simp [MulAut.mul_apply, MulAut.conj_apply]

private theorem kg7innd_centerQuot_equiv {G H : Type*} [Group G] [Group H]
    (hG : commutator G = ⊤) (ψ : G →* H) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) :
    ∃ e : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H,
      ∀ g : G, e (QuotientGroup.mk g) = QuotientGroup.mk (ψ g) := by
  let χ : G →* H ⧸ Subgroup.center H :=
    (QuotientGroup.mk' (Subgroup.center H)).comp ψ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ
  have hkerχ : χ.ker = Subgroup.center G := by
    have h1 : χ.ker = (Subgroup.center H).comap ψ := by
      change ((QuotientGroup.mk' (Subgroup.center H)).comp ψ).ker = _
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact CFSG.LocalCores.comap_center_eq_of_perfect ⟨hG⟩ ψ hψ hker
  refine ⟨QuotientGroup.liftEquiv (N := Subgroup.center G) hχ hkerχ.symm, ?_⟩
  intro g
  exact QuotientGroup.liftEquiv_mk (N := Subgroup.center G) hχ hkerχ.symm g

theorem marking_induces_of_innDiagOn_conj {R : Type} [Group R]
    (hR : Subgroup.center R = ⊥) {H Kc : Subgroup R} (hKc : IsComponentOf Kc H) {φ : MulAut R}
    (h : CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 3 (Subgroup.zpowers φ)
      (Kc.map (MulAut.conj : R →* MulAut R))) :
    CFSG.Assembly.LargeEvenMarking ↥Kc fun _ _ _ I _ θ =>
      ∃ ψ ∈ I, LargeEvenInduces θ (fun l l' : ↥Kc => (l' : R) = φ l) ψ := by
  classical
  let L : Subgroup (MulAut R) := Kc.map (MulAut.conj : R →* MulAut R)
  have hKcq : CFSG.Assembly.IsQuasisimple ↥Kc := hKc.2.2
  have hKcperf : commutator ↥Kc = ⊤ := hKcq.1
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.StandardType.TableBF4TwoInputs.conj_injective_of_center_eq_bot hR
  let eJ : ↥Kc ≃* ↥L := Kc.equivMapOfInjective (MulAut.conj : R →* MulAut R) hinj
  have heJ : ∀ x : ↥Kc, ((eJ x : ↥L) : MulAut R) = MulAut.conj (x : R) := fun _ => rfl
  have hLq : CFSG.Assembly.IsQuasisimple ↥L :=
    (CFSG.Assembly.IsQuasisimple.congr eJ).mp hKcq
  let O : Subgroup ↥L := CFSG.Open.GLAPPrimeCore 3 ↥L
  have hO : O ≤ Subgroup.center ↥L := kg7innd_pquot_le_center (L := L) hLq
    (CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) h.2)
  let κ : ↥Kc →* PQuot 3 L := (QuotientGroup.mk' O).comp (eJ : ↥Kc →* ↥L)
  have hκsurj : Function.Surjective κ :=
    (QuotientGroup.mk'_surjective O).comp eJ.surjective
  have hκker : κ.ker ≤ Subgroup.center ↥Kc := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxO : eJ x ∈ O := by
      have hx'' : QuotientGroup.mk' O (eJ x) = 1 := hx
      exact (QuotientGroup.eq_one_iff (eJ x)).1
        ((QuotientGroup.mk'_apply (N := O) (eJ x)) ▸ hx'')
    have hxZ : eJ x ∈ Subgroup.center ↥L := hO hxO
    have hmapZ : (Subgroup.center ↥Kc).map (eJ : ↥Kc →* ↥L) = Subgroup.center ↥L :=
      Subgroup.map_center_eq eJ
    have hxZ' : eJ x ∈ (Subgroup.center ↥Kc).map (eJ : ↥Kc →* ↥L) := by
      rwa [hmapZ]
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxZ'
    have hzx' : z = x := eJ.injective hzx
    rw [hzx'] at hz
    exact hz
  obtain ⟨e, he⟩ := kg7innd_centerQuot_equiv hKcperf κ hκsurj hκker
  refine kg7innd_largeEvenMarking_centerQuot e hKcperf ?_ h.2
  intro lab S _ I F θ hQ
  obtain ⟨ψ, hψI, hψ⟩ := hQ (φ⁻¹) (Subgroup.inv_mem _ (Subgroup.mem_zpowers φ))
  refine ⟨ψ, hψI, ?_⟩
  intro x y hxy
  change ψ (θ (e (QuotientGroup.mk x))) = θ (e (QuotientGroup.mk y))
  rw [he x, he y]
  exact hψ (κ x) (κ y) (by
    refine ⟨eJ x, eJ y, rfl, rfl, ?_⟩
    show ((eJ y : ↥L) : MulAut R) = (φ⁻¹)⁻¹ * ((eJ x : ↥L) : MulAut R) * φ⁻¹
    rw [inv_inv, heJ x, heJ y, hxy]
    exact (kg7innd_mulAut_conj_conj φ (x : R)).symm)

end CFSG.StandardType.TwE6KG7

end
