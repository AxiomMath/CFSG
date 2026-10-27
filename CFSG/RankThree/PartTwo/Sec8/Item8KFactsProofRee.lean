module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartOne.KEXC.ReeModel
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixedEmbed
public import CFSG.RankThree.PartOne.KEXC.TorusParam
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC
open Item8KFactsProof


namespace Item8KFactsProof

theorem reeGamma_exists_e9 (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ u v : ReeTag.F4.reeGamma K a, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  classical
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Φ, hΦinj, -, -, hΦF⟩ := (torusParam_phi2 D.isFrob).param
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) wPhi2 with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K) :=
    canonicalRep_mem_adjointGroup _ (AlgebraicClosure K) wPhi2
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag (AlgebraicClosure K) :=
    (h : ModGL ReeTag.F4.tag (AlgebraicClosure K)) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K) := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag (AlgebraicClosure K)) = h := rfl
    rw [this, hFh]
    rfl
  have hΦrange : Φ.range ≤ twistedFixed D.F n := by
    rintro _ ⟨z, rfl⟩
    exact hΦF z
  obtain ⟨T, -, hTsurj, -⟩ := exists_twisted_embedding D hg₀adj hFg₀ Φ.range hΦrange
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 :
      Polynomial (AlgebraicClosure K)) (by
    have : (Polynomial.X ^ 2 + Polynomial.X + 1 :
        Polynomial (AlgebraicClosure K)).degree = 2 := by
      compute_degree!
    rw [this]
    decide)
  have hω2 : ω ^ 2 + ω + 1 = 0 := by simpa using hω
  have h2 : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero _ 2
  have hω3 : ω ^ 3 = 1 := by
    have : ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by ring
    rw [hω2, mul_zero, sub_eq_zero] at this
    exact this
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have : (1 : AlgebraicClosure K) + 1 + 1 = 0 := by simpa using hω2
    have h3 : (1 : AlgebraicClosure K) + 1 + 1 = 1 := by
      rw [one_add_one_eq_two, h2, zero_add]
    rw [h3] at this
    exact one_ne_zero this
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  set u : (AlgebraicClosure K)ˣ := Units.mk0 ω hω0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [hu, hω3])
  have hm : 3 ∣ mPhi2 a := by
    rw [mPhi2]
    have : (2 : ℕ) ^ (2 * a + 1) % 3 = 2 := two_pow_mod_three_of_odd (odd_two_mul_add_one a)
    omega
  have hum : u ^ mPhi2 a = 1 := by
    obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, hu3, one_pow]
  set ζ : rootsOfUnity (mPhi2 a) (AlgebraicClosure K) := ⟨u, (mem_rootsOfUnity _ _).mpr hum⟩
    with hζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hω1
    have := congrArg (fun z : rootsOfUnity (mPhi2 a) (AlgebraicClosure K) =>
      ((z : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) h
    simpa [hζ, hu] using this
  have hζ3 : ζ ^ 3 = 1 := Subtype.ext (by simp [hζ, hu3])
  obtain ⟨γ₁, -, hγ₁⟩ := hTsurj (Φ (ζ, 1)) ⟨_, rfl⟩
  obtain ⟨γ₂, -, hγ₂⟩ := hTsurj (Φ (1, ζ)) ⟨_, rfl⟩
  set ψ := (MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma (K := K) (AlgebraicClosure K) a)
    with hψ
  have hψapp : ∀ γ, ψ γ = g₀⁻¹ * thetaGamma (K := K) (AlgebraicClosure K) a γ * g₀ := by
    intro γ
    simp [hψ]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g₀⁻¹).injective.comp (thetaGamma_injective (K := K) (AlgebraicClosure K))
  refine ⟨γ₁, γ₂, e9Pair_of_map_eq ψ hψinj Φ hΦinj (c := (ζ, 1)) (d := (1, ζ))
    (by rw [hψapp, hγ₁]) (by rw [hψapp, hγ₂]) (fun h => hζ1 (congrArg Prod.fst h))
    (Prod.ext (by simp [hζ3]) (by simp)) (Prod.ext (by simp) (by simp [hζ3]))
    (Prod.ext (by simp) (by simp)) ?_⟩
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have h2 := congrArg Prod.snd hk
  simp at h2
  exact hζ1 h2.symm

theorem exists_fixedPoints_reeGammaFieldAut {k : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * k + 1)) (β : K ≃+* K)
    (hβ : orderOf β = 3) :
    ∃ (b : ℕ) (_ : CharP (fixSubfield β) ReeTag.F4.prime),
      Nat.card (fixSubfield β) = 2 ^ (2 * b + 1) ∧ 3 * (2 * b + 1) = 2 * k + 1 ∧
      ∃ ι : ReeTag.F4.reeGamma (fixSubfield β) b →* ReeTag.F4.reeGamma K k,
        Function.Injective ι ∧
        ∀ z, z ∈ ι.range ↔ ReeTag.F4.reeGammaFieldAut K k β z = z := by
  obtain ⟨b, hchar, hk', hbp, ι, hιinj, hιrange⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_fixedPoints_reeGammaFieldAut_odd hK
      Nat.prime_three (by norm_num) β hβ
  exact ⟨b, hchar, hk', by omega, ι, hιinj, hιrange⟩

theorem exists_pair_autFix_ree {k : ℕ} (hk1 : 1 ≤ k) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * k + 1))
    {α : MulAut (ReeTag.F4.reeGamma K k)} (hα3 : α ^ 3 = 1) (hαin : ¬ KFacts.IsInnerAut α) :
    ∃ u v : Sec4.autFix α, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  obtain ⟨β, hβ, hcoset⟩ := KFacts.largeRee_order_three_inFieldCoset hk1 hK hα3 hαin
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj k K hK β hβ α hα3
    hcoset
  obtain ⟨b, _, hcard, -, ι, hιinj, hιrange⟩ := exists_fixedPoints_reeGammaFieldAut hK β hβ
  have hfix : ∀ y, α (MulAut.conj x (ι y)) = MulAut.conj x (ι y) := by
    intro y
    rw [hx]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [(hιrange (ι y)).mp ⟨y, rfl⟩]
  set f : ReeTag.F4.reeGamma (fixSubfield β) b →* Sec4.autFix α :=
    ((MulAut.conj x : ReeTag.F4.reeGamma K k ≃* ReeTag.F4.reeGamma K k).toMonoidHom.comp
      ι).codRestrict _ hfix with hf
  have hfinj : Function.Injective f := by
    intro y y' h
    have h' := congrArg Subtype.val h
    exact hιinj ((MulAut.conj x).injective h')
  have : Finite (fixSubfield β) := Subtype.finite
  exact exists_pair_of_injective f hfinj (reeGamma_exists_e9 b (fixSubfield β) hcard)

end Item8KFactsProof

open Item8KFactsProof

theorem kF82E9ReeF4_holds : KF82E9ReeF4 := by
  intro X _ n _ hX α hα3 hαin
  obtain ⟨-, k, hk1, -, K, _, _, _, hK, ⟨E⟩⟩ := Sec4.exists_mulEquiv_reeGamma hX
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite X := Finite.of_equiv _ E.symm.toEquiv
  set α' := MulAut.congr E α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα3, map_one]
  have hα'in : ¬ KFacts.IsInnerAut α' := fun h => hαin ((KFacts.isInnerAut_congr E α).mp h)
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := exists_pair_autFix_ree hk1 hK hα'3 hα'in
  obtain ⟨u', v', hu1', hu3', hv3', huv', hvu'⟩ := exists_pair_of_injective
    (Sec4.autFixCongrEquiv E α).toMonoidHom (Sec4.autFixCongrEquiv E α).injective
    ⟨u, v, hu1, hu3, hv3, huv, hvu⟩
  exact e9Closed_of_commuting hu1' hu3' hv3' huv' hvu'

theorem isoReeF4_autFix_reeGammaFieldAut {a n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (han : 2 * a + 1 = 3 * n) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (hβ : orderOf β = 3) :
    IsoReeF4 (Sec4.autFix (ReeTag.F4.reeGammaFieldAut K a β)) n := by
  obtain ⟨b, hchar, hcard, hb3, ι, hιinj, hιrange⟩ := exists_fixedPoints_reeGammaFieldAut hK β hβ
  have hbn : 2 * b + 1 = n := by omega
  have hrange : ι.range = Sec4.autFix (ReeTag.F4.reeGammaFieldAut K a β) := by
    ext z
    rw [hιrange]
    rfl
  have : Finite (fixSubfield β) := Subtype.finite
  exact ⟨b, fixSubfield β, inferInstance, inferInstance, hchar, hbn, by rw [hcard, hbn],
    ⟨(MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hιinj).symm⟩⟩

@[expose] def KF83ReeCentThree : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → ∀ y : ReeTag.F4.reeGamma K a, orderOf y = 3 →
      IsoSUThree (inSubgroup perfectResidual
        (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)))) (2 ^ (2 * a + 1))

theorem kF83ReeF4_of (hC : KF83ReeCentThree) : Item83Proof.KF83ReeF4 := by
  intro a K _ _ _ n ha han hK β hβ
  refine ⟨isoReeF4_autFix_reeGammaFieldAut han hK β hβ, ?_⟩
  obtain ⟨b, _, hcard, -, ι, hιinj, hιrange⟩ := exists_fixedPoints_reeGammaFieldAut hK β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := reeGamma_exists_e9 b (fixSubfield β) hcard
  have hy₁o : orderOf (ι u) = 3 := orderOf_eq_prime (by rw [← map_pow, hu3, map_one])
    (fun h => hu1 (hιinj (h.trans (map_one ι).symm)))
  refine ⟨ι u, ι v, (hιrange _).mp ⟨u, rfl⟩, (hιrange _).mp ⟨v, rfl⟩, by rw [← map_pow, hu3,
    map_one], by rw [← map_pow, hv3, map_one], by rw [← map_mul, huv, map_mul],
    fun h => hu1 (hιinj (h.trans (map_one ι).symm)), fun h => hvu ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, hιinj (by rw [map_zpow, hj])⟩
  · have := hC a K ha hK (ι u) hy₁o
    rwa [han] at this

end CFSG.RankThree.PartTwo.Sec8
