module

public import CFSG.RankThree.PartTwo.Sec11.Item1116KFact
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

@[expose] def CentBound119For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c t : G),
    (∃ (X : Type) (_ : Group X), F X ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X)) →
    c ∈ Subgroup.normalizer (Y : Set G) → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    t ∈ Subgroup.normalizer (Y : Set G) → (∃ k : ℕ, t ^ 3 ^ k = 1) → t * c = c * t →
    (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) →
      t ^ (3 ^ (Nat.card K).factorization 3) ∈ Sec4.thetaQuotCentralizer Y

@[expose] def CentBound119G2 : Prop :=
  CentBound119For fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def CentBound119D4 : Prop :=
  CentBound119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def CentBound119L3 : Prop :=
  CentBound119For fun X _ => ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
    ((p ^ e % 3 = 1 ∧ Nonempty (X ≃* projSL 3 (GaloisField p e))) ∨
      (p ^ e % 3 = 2 ∧ Nonempty (X ≃* projSU 3 p e)))

@[expose] def CentBound119PGL : Prop :=
  CentBound119For fun X _ => ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K),
    Sec4.PiField π p f K ∧ Sec4.ModThree π (p ^ f) ∧
      Nonempty (X ≃* projImage (Sec4.glPi π 3 (p ^ f) K))

@[expose] def CentBound119Spor : Prop :=
  CentBound119For fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)

namespace Item1118StepsProof

theorem nonempty_commutator_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') :
    Nonempty (_root_.commutator X ≃* _root_.commutator X') := by
  have h : (_root_.commutator X).map e.toMonoidHom = _root_.commutator X' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  exact ⟨((_root_.commutator X).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)⟩

end Item1118StepsProof

theorem centBound119PGL_of (hL3 : CentBound119L3) : CentBound119PGL := by
  intro G _ _ Y K c t hY hcN hc3 hKc hKt htN ht3 htc htK
  obtain ⟨X, _, ⟨π, p, f, k, _, hK, hq, ⟨e⟩⟩, ⟨φ⟩⟩ := hY
  have hp := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hq2 : 2 < p ^ f
  · have hSP : projImage (Sec4.slPi π 3 (p ^ f) k) ≤ projImage (Sec4.glPi π 3 (p ^ f) k) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi fun h => by subst h; exact hK.unitary)
    have hperf : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) k)) :=
      Sec13.isPerfect_projImage_slPi hK hq2
    obtain ⟨e₁⟩ := Item1118StepsProof.nonempty_commutator_mulEquiv e
    have e₂ : _root_.commutator (projImage (Sec4.glPi π 3 (p ^ f) k)) ≃*
        projImage (Sec4.slPi π 3 (p ^ f) k) :=
      (MulEquiv.subgroupCongr (Sec13.commutator_projImage_glPi hK hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP)
    have e₃ : projImage (Sec4.slPi π 3 (p ^ f) k) ≃*
        _root_.commutator (projImage (Sec4.slPi π 3 (p ^ f) k)) :=
      ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv).symm
    exact hL3 G Y K c t ⟨_, inferInstance, Sec13.isLThreePi_projImage_slPi hK hq,
      ⟨φ.trans (e₁.trans (e₂.trans e₃))⟩⟩ hcN hc3 hKc hKt htN ht3 htc htK
  · exfalso
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f :=
        le_trans hp.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
      omega
    cases π
    · have hsP : Group.IsSolvable (projImage (Sec4.glPi false 3 (p ^ f) k)) :=
        Sec13.isSolvable_projImage_glPi_two hK h2
      have hsX : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have hsYb : Group.IsSolvable (Y ⧸ aschbacherSolvableCore 3 Y) :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have hsθ : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
        (solvable_prime_complement_core_characterization Nat.prime_three).1
      have hsY : Group.IsSolvable Y :=
        Group.isSolvable_of_ker_le_range (aschbacherSolvableCore 3 Y).subtype
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
          (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
      obtain ⟨K₀, ⟨-, -, hqs⟩, rfl⟩ := hKc
      have hle : Y ⊓ Subgroup.centralizer ({c} : Set G) ≤ Y := inf_le_left
      have hinj : Function.Injective ((Subgroup.inclusion hle).comp K₀.subtype) :=
        (Subgroup.inclusion_injective hle).comp K₀.subtype_injective
      have hsK₀ : Group.IsSolvable K₀ := Group.isSolvable_of_isSolvable_injective hinj
      obtain ⟨-, hsimple, u, v, huv⟩ := hqs
      have : Group.IsSolvable ((K₀ ⧸ aschbacherSolvableCore 3 K₀) ⧸
          Subgroup.center (K₀ ⧸ aschbacherSolvableCore 3 K₀)) := inferInstance
      exact huv ((IsSimpleGroup.comm_iff_isSolvable).mpr this u v)
    · change p ^ f % 3 = 1 at hq
      omega

theorem centBound119_of (hG2 : CentBound119G2) (hD4 : CentBound119D4) (hL3 : CentBound119L3)
    (hPGL : CentBound119PGL) (hSp : CentBound119Spor) : CentBound119 := by
  intro G _ _ Y K c t ⟨X, _, hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK
  rcases hX with hX | hX | hX | hX | hX | hX
  · exact hG2 G Y K c t ⟨X, inferInstance, hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK
  · exact hD4 G Y K c t ⟨X, inferInstance, hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK
  · exact hL3 G Y K c t ⟨X, inferInstance, hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK
  · exact hPGL G Y K c t ⟨X, inferInstance, hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK
  · exact hSp G Y K c t ⟨X, inferInstance, Or.inl hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK
  · exact hSp G Y K c t ⟨X, inferInstance, Or.inr hX, hY⟩ hcN hc3 hK hKt htN ht3 htc htK

theorem centBound119_of_four (hG2 : CentBound119G2) (hD4 : CentBound119D4)
    (hL3 : CentBound119L3) (hSp : CentBound119Spor) : CentBound119 :=
  centBound119_of hG2 hD4 hL3 (centBound119PGL_of hL3) hSp

end CFSG.RankThree.PartTwo.Sec11
