module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernel
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCoreDefs
public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCBExponentFourLayer
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Steinberg.Adjoint.Pairs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6EndInner

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TwE6RootKill

theorem endNodeInner_core (hRK : RootKill) (hDat : TwE6FieldCore.SubfieldLangDatumFive)
    (hCore : TwE6RootAs.TwE6CorootCore) {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (h2 : ringChar K = 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ q + 1) {A : Subgroup (twistedE6RootGroup K σ)}
    (hA : IsElemAbelian p A) (h5 : p ^ 5 ≤ Nat.card A)
    (hU : TwNormTwo K σ (A.map (twistedE6RootGroup K σ).subtype)) :
    ∃ t ∈ A, t ≠ 1 ∧
      IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ))))
        (Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ))) ∧
      ∀ s ∈ A, (∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ))),
        s * j = j * s) → s ∈ Subgroup.zpowers t := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  set A₁ : Subgroup (ModGL TwistTag.E6.tag K) := A.map (twistedE6RootGroup K σ).subtype with hA₁
  have hC₀I : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ := le_sup_left
  have hA₁I : A₁ ≤ twistedE6InndiagGL K σ := (Subgroup.map_subtype_le A).trans hC₀I
  have hA₁e : IsElemAbelian p A₁ := hA.map _
  have h5' : p ^ 5 ≤ Nat.card A₁ := by
    rw [hA₁, Subgroup.card_map_of_injective (twistedE6RootGroup K σ).subtype_injective]
    exact h5
  obtain ⟨D, hc1, hv⟩ := hDat K σ q hK hσ p hp hp5 hpq A₁ hA₁I hA₁e
    ((Nat.pow_le_pow_right hp.pos (by norm_num : 4 ≤ 5)).trans h5')
  obtain ⟨β, hβ, -, -, hcor⟩ := rootKernel_of_rootKill hRK hK hσ h2 hp hpq hA₁I hA₁e h5' hU D
  obtain ⟨γ, hγ, hγβ⟩ := exists_root_iform_eq_zero hβ
  haveI : NeZero ((p : ℕ) : K) := ⟨fun h => by
    have h' := (ringChar.spec K p).1 h
    rw [h2] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h').symm⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ p :=
    ⟨_, IsPrimitiveRoot.isUnit_unit hp.ne_zero hζ0⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  obtain ⟨x, hx, ht⟩ := hcor γ hγβ ζ hζ.pow_eq_one
  obtain ⟨t, htA, rfl⟩ := Subgroup.mem_map.1 hx
  simp only [hc1, one_mul, inv_one, mul_one] at ht
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, map_one, map_one, mul_one, inv_mul_cancel] at ht
    have hco := CFSG.LieType.Chevalley.rootDiagUnit_injective
      (ht.trans CFSG.LieType.Chevalley.rootDiagUnit_one.symm)
    obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hγ
    have hγγ : iform γ γ = 2 := by
      rw [hj, show TwistTag.E6.tag.symmetrizer = 1 from rfl, Matrix.one_apply_eq, mul_one]
    have h3 := rootChar_corootTuple γ γ ζ
    rw [hco, hγγ] at h3
    have h4 : rootChar (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) γ = 1 := by
      simp [rootChar]
    have hz2 : ζ ^ 2 = 1 := by
      rw [pow_two, ← zpow_two, ← h3, h4]
    have := Nat.le_of_dvd (by norm_num) ((hζ.pow_eq_one_iff_dvd 2).1 hz2)
    omega
  obtain ⟨X, D', hXD, hXc, hXodd, hXD', hDq, -, -, -, hmem⟩ := hCore K σ q hK hσ h2 p hp hpq
    D.Fr D.hFr D.v hv D.g0 D.hg0C D.hg0 _ (hC₀I t.2) γ hγ ζ hζ.pow_eq_one hζ1 ht.symm
  have hC : Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ)) = X ⊔ D' := by
    rw [← hXD]
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨hlay, hcomp⟩ := TwE6D3.layer_sup_eq hXc hXD'
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hDq)
  have hX : ∀ s ∈ A, (∀ d ∈ D', s * d = d * s) → s ∈ X := by
    intro s hs hsD
    obtain ⟨y, hy, hys⟩ := hmem s.1 (hC₀I s.2) (congrArg Subtype.val (hA.comm hs htA))
      fun d hd => congrArg Subtype.val (hsD d hd)
    exact (Subtype.ext hys : y = s) ▸ hy
  have htX : t ∈ X := hX t htA fun d hd => by
    have hd' : d ∈ Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ)) := by
      rw [hC]
      exact (le_sup_right : D' ≤ X ⊔ D') hd
    exact (Subgroup.mem_centralizer_singleton_iff.1 hd').symm
  refine ⟨t, htA, ht1, by rw [hC]; exact hcomp, fun s hs hsL => ?_⟩
  rw [hC, hlay] at hsL
  haveI : Finite X := Nat.finite_of_card_ne_zero hXodd.pos.ne'
  exact CFSG.LocalAnalysis.GorensteinLyons.mem_of_pow_eq_one_of_isCyclic hXc
    (Subgroup.zpowers_le.2 htX) hp.pos
    (by rw [Nat.card_zpowers]; exact orderOf_eq_prime (hA.2 t htA) ht1) (hX s hs hsL)
    (hA.2 s hs)

end CFSG.StandardType.TwE6EndInner

end
