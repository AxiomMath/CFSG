module

public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.CTTwisted
public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)
open scoped Matrix Polynomial

theorem lang_conjugator_twisted_gen (K : Type) [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL TwistTag.E6.tag L) (hn : n ∈ adjointGroup TwistTag.E6.tag L) :
    ∃ g0 : ModGL TwistTag.E6.tag L, g0 ∈ adjointGroup TwistTag.E6.tag L ∧
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g0 = g0 * n := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).2
    TwistTag.E6 1
  obtain ⟨g, hg⟩ := hLang ⟨n, hn⟩
  refine ⟨(g : ModGL TwistTag.E6.tag L), g.2, ?_⟩
  have h1 : S g = g * ⟨n, hn⟩ := by
    rw [hg, mul_inv_cancel_left]
  have h2 := hS g
  rw [h1, zpow_one] at h2
  exact h2.symm.trans (by rfl)

theorem twistedTorus_E6_eq_map_of_weylImage {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    (v : WeylGroup TwistTag.E6.tag) (hv0 : weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ = v)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) :
    twistedTorusOf n (twistHom TwistTag.E6 L Fr) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom TwistTag.E6.tag L) := by
  rw [twistedTorusOf_eq_of_weylImage hn v hv0 _ fun b =>
    ⟨_, twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := Fr) b⟩]
  exact twistedTorus_E6_eq_map Fr v M hv

theorem a1_twisted_data {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (hordW : ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag))
    (n : ModGL TwistTag.E6.tag L) (hnC : n ∈ adjointGroup TwistTag.E6.tag L)
    {θ : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    (hZcyc : IsCyclic (subtorusA1 n (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) θ))
    {N : ℕ} (hN : N ≠ 0)
    (hZcard : Nat.card (subtorusA1 n (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) θ) = N)
    (hord : p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p =
      p ^ N.factorization p)
    (hkerZ : ∀ a : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag a ∈
        subtorusA1 n (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) θ →
      orderOf (rootDiagUnit TwistTag.E6.tag a) = p → rootCharKernel a ⊆ {θ, -θ}) :
    (∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → IsCyclic Q) ∧
      ∀ (S : Subgroup (SL2 L)) [Finite S],
        (∀ B : SL2 L, n * twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)
            (rootSL2 TwistTag.E6.tag L θ B) * n⁻¹ = rootSL2 TwistTag.E6.tag L θ B ↔ B ∈ S) →
        CFSG.IsQuasisimple S →
        Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
          Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
            (Matrix.GeneralLinearGroup.scalar (Fin 2)).range →
        ∀ x : twistedE6RootGroup K σ, orderOf x = p →
          ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
            Group.IsSolvable V → IsCyclic V := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted_gen K (ℓ := ℓ) (f := f) hf L n hnC
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hyΓ : ∀ y : twistedE6RootGroup K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    fun y => graphFixedRootGroup_le _ _ _ y.2
  have hιC : ∀ y, ι y ∈ adjointGroup TwistTag.E6.tag L := fun y =>
    baseChangeGL_mem_adjointGroup _ ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ y)).1
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (σ c) = Fr (algebraMap K L c)
      rw [hσ, hFr, map_pow]
  have hιΦ : ∀ y, twistHom TwistTag.E6 L Fr (ι y) = ι y := fun y => by
    change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L) (y : ModGL _ K)) =
      baseChangeGL (algebraMap K L) (y : ModGL _ K)
    rw [twistHom_baseChangeGL (algebraMap K L) hcomm,
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hyΓ y)).2]
  have hrat3 : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ι.range.relIndex X ∣ 3 ^ k ∧
        (∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P → P ≤ ι.range) ∧
        ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → ⁅P, P⁆ = P → P ≤ ι.range := by
    intro X _ hXC hXF
    have hXR : X ≤ R := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    refine ⟨relIndex_dvd_of_le_of_index_dvd hXR (hk ▸ dvd_rfl), fun p' hp' hp'3 P hPX hP => ?_,
      fun P hPX hPP => ?_⟩
    · have : Finite P :=
        Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
      exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp' Nat.prime_three (by omega) hk hP
    · have hPR : P ≤ R := hPX.trans hXR
      calc P = ⁅P, P⁆ := hPP.symm
        _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hPR hPR
        _ = C' := hder
  have hrat2 : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ι.range.relIndex X ∣ 3 ^ k ∧
        ∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P → P ≤ ι.range := fun X _ hXC hXF => by
    have h := hrat3 X hXC hXF
    exact ⟨h.1, h.2.1⟩
  have hordC : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ N.factorization p := by
    have h1 := hpp p hp (by omega)
    have h2 : Nat.card C' = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h2, hRcard] at h1
    rw [h1]
    exact hord
  have hZle : subtorusA1 n (twistHom TwistTag.E6 L Fr) θ ≤
      twistedTorusOf n (twistHom TwistTag.E6 L Fr) := subtorusA1_le_twistedTorusOf _ _ _
  obtain ⟨-, -, -, -, hpcyc, hconj⟩ := sylow_conjugacy_of_subtorus (3 ^ k) ι hι
    (twistHom TwistTag.E6 L Fr) n g0 hg0C hg0 hp (by omega) hN hrat2 _ hZle hZcyc hZcard hordC
  refine ⟨hpcyc, fun S _ hS1 hS2 hS3 => ?_⟩
  exact a1_solvable_normal_cyclic ι hι hιC (twistHom TwistTag.E6 L Fr) hιΦ n g0 hg0C hg0
    (fun P hP hPC hPF hPp => (hrat3 P hPC hPF).2.2 P le_rfl hPp) hp hordW hθ (hZ := hZcyc) hconj
    hkerZ S hS1 hS2 hS3

end CFSG.RankThree.PartOne.KE
