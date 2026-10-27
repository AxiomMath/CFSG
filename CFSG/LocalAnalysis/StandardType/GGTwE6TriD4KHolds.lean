module

public import CFSG.LocalAnalysis.StandardType.GGResTriD4TwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDescent
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KToralSetup
import CFSG.LocalAnalysis.StandardType.GGTwE6TriD4KClass
import CFSG.LocalAnalysis.StandardType.GGTwE6TriD4KTorusCount

public section

namespace CFSG.StandardType.TwE6TriD4K

open CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.RankThree.PartOne.KE (d4Nodes)
open scoped MatrixGroups
open CFSG.StandardType.TwE6TwA2K

theorem card_le_of_component_triD4
    (K : Type) [Field K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (h3n : 3 ∣ 2 ^ n + 1)
    (h : ↥(twistedE6InndiagGL K σ)) (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1)
    (J : Subgroup ↥(twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)))
    (hlab : GGHasLabel (⟨.triD4, 0, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (A : Subgroup ↥(twistedE6InndiagGL K σ)) (hA : IsElemAbelian 3 A) (hhA : h ∈ A) :
    Nat.card A ≤ 3 ^ 4 := by
  by_contra hle
  rw [not_le] at hle
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    positivity
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro hzero
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) 2] at hzero
    norm_num at hzero
  obtain ⟨k, hk⟩ := (hA.isPGroup).exists_card_eq
  have hbig : 3 ^ 5 ≤ Nat.card A := by
    rw [hk] at hle ⊢
    have hk5 : 5 ≤ k := by
      have := (Nat.pow_lt_pow_iff_right (show 1 < 3 by norm_num)).1 hle
      omega
    exact Nat.pow_le_pow_right (show 0 < 3 by norm_num) hk5
  obtain ⟨S, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj, hAT⟩ :=
    exists_langSetup_of_big_elemAbelian hn hK σ hσ A hA hbig h hhA hh1
  obtain ⟨v, u, π, hu, hπ, hθ⟩ :=
    exists_theta_of_component_triD4 hn hK h3n S hSq hΦ ι hinj hrange h hconj hT hap h1 J hJ hlab
  let F : ↥(twistedE6InndiagGL K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (twistedE6InndiagGL K σ).subtype)
  have hFinj : Function.Injective F :=
    (MulAut.conj S.D.g0⁻¹).injective.comp
      ((baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K))).comp
        (Subgroup.subtype_injective (twistedE6InndiagGL K σ)))
  let X : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)) := A.map F
  have hX : X ≤ S.D.torus := by
    rintro y ⟨x, hx, rfl⟩
    show MulAut.conj S.D.g0⁻¹
      (baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K)) ∈ S.D.torus
    rw [MulAut.conj_apply, inv_inv]
    exact hAT x hx
  have hX3 : ∀ y ∈ X, y ^ 3 = 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [← map_pow, hA.2 x hx, map_one]
  have hXcard : Nat.card X = Nat.card A := Subgroup.card_map_of_injective hFinj
  have h81 := card_le_of_le_torus_of_theta S h3 (by rw [hSq]; exact h3n) v u hu hπ hθ X hX hX3
  rw [hXcard] at h81
  exact absurd h81 (not_le.2 hle)

theorem modelAtLab_triD4_holds
    (K : Type) [Field K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (h3n : 3 ∣ 2 ^ n + 1) :
    ModelAtLab ⟨.triD4, 0, n⟩ True K σ n := by
  intro h hh3 hh1 J hJ hlab
  exact ⟨trivial, fun A hA hhA =>
    card_le_of_component_triD4 K σ hn hK hσ h3n h hh3 hh1 J hJ hlab A hA hhA⟩

theorem ggTwE6TriD4RankKnown_holds
    : GGTwE6TriD4RankKnown := by
  unfold GGTwE6TriD4RankKnown
  intro m hΛ h3m
  refine TwE6Delta.labelAll (lab := ⟨.twE6, 0, m⟩) rfl fun K _ _ hK => ?_
  have hm : 1 ≤ m := (show 1 ≤ m ∧ (0 : ℕ) = 0 from hΛ).1
  have hR : ModelRLab ⟨.triD4, 0, m⟩ True K m :=
    modelRLab_of_modelAtLab (lab := ⟨.triD4, 0, m⟩)
      (by
        show 1 ≤ m ∧ (0 : ℕ) = 0
        exact ⟨hm, rfl⟩) (by simp) hm hK fun σ hσ =>
      modelAtLab_triD4_holds K σ hm hK hσ h3m
  intro L' _ _ ψ hψ hker hperf e he3 hind J hJ hlab
  exact (lift_of_modelRLab hR L' ψ hψ hker hperf e he3 hind J hJ hlab).2

end CFSG.StandardType.TwE6TriD4K

end
