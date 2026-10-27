module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveConjSix
public import CFSG.LocalAnalysis.StandardType.GGOrdPToralF4Holds
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Sylow
public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane
public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GH74.Statements
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.CTP.SeitzFineU5
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.SeitzGeneration.ExcHighThree

namespace OrdPInnerExc

theorem ggOrdPToralMax_twistedE6RootGroup_five
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h5 : 5 ∣ ℓ ^ f + 1) :
    GGOrdPToralMax (twistedE6RootGroup K σ) 5 := by
  obtain ⟨V, hV, -, -, hconj⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_elemAbelian_conj_le_six
      hℓ K hK σ hσ h5
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  exact ggOrdPToralMax_of_conj_le hV hconj

theorem ggOrdPToralMax_twistedE6RootGroup_three
    {f : ℕ} (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (h3 : 3 ∣ 2 ^ f - 1) :
    GGOrdPToralMax (twistedE6RootGroup K σ) 3 := by
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst hf0
    have hcard : Nat.card K = 1 := by simpa using hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hKpow : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hring : ringChar K = 2 :=
    CFSG.RankThree.Chevalley.ringChar_eq_of_card Nat.prime_two (by omega) hKpow
  haveI : CharP K 2 := hring ▸ ringChar.charP K
  let k := RingHom.eqLocusField σ.toRingHom (RingHom.id K)
  have hkcard : Nat.card k = 2 ^ f := by
    exact CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK hσ
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    have hc : σ ((c : K)) = (c : K) := c.2
    exact hc
  haveI : CharP k 2 :=
    (RingHom.charP_iff (Subfield.subtype k) (Subfield.subtype_injective k) 2).mpr ‹CharP K 2›
  haveI : Finite k := Finite.of_injective (fun x : k => (x : K)) Subtype.val_injective
  have hσ' : ∀ c : K, σ c = c ^ Nat.card k := by
    intro c; rw [hkcard]; exact hσ c
  have hK' : Nat.card K = (Nat.card k) ^ 2 := by rw [hkcard]; exact hK
  have h3k : 3 ∣ Nat.card k - 1 := by rw [hkcard]; exact h3
  have hq : Nat.card k % 3 = 1 := by
    obtain ⟨m, hm⟩ := h3
    have hfpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hpow : 2 ^ f = 3 * m + 1 := by omega
    rw [hkcard, hpow]
    omega
  have hq2 : 2 ≤ Nat.card k := by
    rw [hkcard]
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hf
  let φ : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom
  have hφ : Function.Injective φ := (phiG_injective σ hfix).comp (MulEquiv.injective _)
  intro u hu
  obtain ⟨g, hg⟩ :=
    threeSubgroup_conj_into_F4 (k := k) (K := K) σ hσ' hK' hfix hq hq2
      (Subgroup.zpowers u) (isElemAbelian_zpowers hu).2
  have hurel : (MulAut.conj g).toMonoidHom u ∈ φ.range :=
    hg ⟨u, Subgroup.mem_zpowers u, rfl⟩
  obtain ⟨v, hv⟩ := hurel
  have hgu : (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hconjpow : (g * u * g⁻¹) ^ 3 = 1 := by
    have h := congrArg (MulAut.conj g) hu
    simpa only [MulAut.conj_apply, map_pow, map_one] using h
  have hv3 : v ^ 3 = 1 := by
    apply hφ
    rw [map_pow, hv, hgu, map_one]
    exact hconjpow
  obtain ⟨E, hEel, hvE, hEmax⟩ := ggOrdPToralMax_adjointF4_three k h3k v hv3
  let W : Subgroup (twistedE6RootGroup K σ) :=
    (E.map φ).map (MulAut.conj g⁻¹).toMonoidHom
  have hWel : IsElemAbelian 3 W :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map hEel φ) _
  have huW : u ∈ W := by
    refine ⟨φ v, ⟨v, hvE, rfl⟩, ?_⟩
    rw [hv, hgu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  refine ⟨W, hWel, huW, ?_⟩
  intro A hA
  obtain ⟨h, hh⟩ :=
    threeSubgroup_conj_into_F4 (k := k) (K := K) σ hσ' hK' hfix hq hq2 A hA.2
  let B : Subgroup (twistedE6RootGroup K σ) := A.map (MulAut.conj h).toMonoidHom
  have hBle : B ≤ φ.range := hh
  have hBcard : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hCel : IsElemAbelian 3 (B.comap φ) :=
    CFSG.Open.IsElemAbelian.comap (CFSG.Open.IsElemAbelian.map hA _) hφ
  have hmax := hEmax (B.comap φ) hCel
  have hCcard : Nat.card (B.comap φ) = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hBle]
  have hWcard : Nat.card W = Nat.card E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective hφ]
  rw [hWcard]
  calc Nat.card A = Nat.card B := hBcard.symm
    _ = Nat.card (B.comap φ) := hCcard.symm
    _ ≤ Nat.card E := hmax

private theorem ggOrdPToralMax_graphFixedRootGroup_of_eq
    {K : Type} [Field K] {σ : K ≃+* K} {θ : K →+* K} (hθ : σ.toRingHom = θ) {p : ℕ}
    (h : GGOrdPToralMax (twistedE6RootGroup K σ) p) :
    GGOrdPToralMax ↥(graphFixedRootGroup TwistTag.E6 K θ) p := by
  subst hθ
  exact h

theorem ggOrdPToralMax_twistedE6Group_five
    {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) :
    GGOrdPToralMax (twistedE6Group 2 f) 5 := by
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst hf0
    norm_num at h5
  obtain ⟨π, hπ, hkerπ, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  have hcop : Nat.Coprime (Nat.card π.ker) 5 := by
    rw [hkerπ]
    exact OrdPInnerExc.coprime_card_center_twistedE6 ggTwE6CenterTrivialInput_holds hf
      Nat.prime_five (by omega)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  have hroot := ggOrdPToralMax_twistedE6RootGroup_five Nat.prime_two
    (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ h5
  have hgraph := ggOrdPToralMax_graphFixedRootGroup_of_eq hσθ hroot
  exact OrdPInnerExc.ggOrdPToralMax_of_surjective Nat.prime_five hπ hkerπ.le hcop hgraph

theorem ggOrdPToralMax_twistedE6Group_three
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) :
    GGOrdPToralMax (twistedE6Group 2 f) 3 := by
  obtain ⟨π, hπ, hkerπ, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  have hcop : Nat.Coprime (Nat.card π.ker) 3 := by
    rw [hkerπ]
    refine OrdPInnerExc.coprime_card_center_twistedE6 ggTwE6CenterTrivialInput_holds hf
      Nat.prime_three ?_
    rintro ⟨-, hd⟩
    have h2 : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hd h3
    have h2' : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
      have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    rw [h2'] at h2
    norm_num at h2
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  have hroot := ggOrdPToralMax_twistedE6RootGroup_three
    (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ h3
  have hgraph := ggOrdPToralMax_graphFixedRootGroup_of_eq hσθ hroot
  exact OrdPInnerExc.ggOrdPToralMax_of_surjective Nat.prime_three hπ hkerπ.le hcop hgraph

end OrdPInnerExc

theorem ggOrdPToralTwE6RestHard_holds :
    GGOrdPToralTwE6RestHard := by
  intro f p hf hp hcase _
  rcases hcase with ⟨rfl, h3⟩ | ⟨rfl, h5⟩
  · exact OrdPInnerExc.ggOrdPToralMax_twistedE6Group_three hf h3
  · exact OrdPInnerExc.ggOrdPToralMax_twistedE6Group_five h5

end CFSG.StandardType
