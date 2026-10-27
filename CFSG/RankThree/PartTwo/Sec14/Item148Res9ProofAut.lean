module

public import CFSG.RankThree.PartTwo.Sec8.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofQuot
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag

variable {Γ : Type} [Group Γ] {K N : Subgroup Γ} {X : Type} [Group X]

omit [Group X] in
theorem map_ker_normalizerMonoidHom [Group X] (ψ : K →* X)
    (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {a : Γ}
    (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ)) :
    ψ.ker.map ((K.normalizerMonoidHom ⟨a, haK⟩ : MulAut K) : K →* K) = ψ.ker := by
  have key : ∀ x : K, K.normalizerMonoidHom ⟨a, haK⟩ x ∈ ψ.ker ↔ x ∈ ψ.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hker]
    exact (Subgroup.mem_normalizer_iff.mp haN x).symm
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).mpr hx
  · intro hy
    set c := K.normalizerMonoidHom ⟨a, haK⟩ with hc
    refine ⟨c.symm y, (key (c.symm y)).mp ?_, c.apply_symm_apply y⟩
    rw [MulEquiv.apply_symm_apply]
    exact hy

@[expose] noncomputable def sectionAut (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {a : Γ}
    (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ)) :
    MulAut X :=
  (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.congr ψ.ker ψ.ker (K.normalizerMonoidHom ⟨a, haK⟩)
      (map_ker_normalizerMonoidHom ψ hker haK haN)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

theorem sectionAut_apply (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {a : Γ}
    (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (x : K) :
    sectionAut ψ hψ hker haK haN (ψ x) = ψ (K.normalizerMonoidHom ⟨a, haK⟩ x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ x) =
      (x : K ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [sectionAut, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
  rfl

theorem sectionAut_apply' (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {a : Γ}
    (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    {x y : K} (hxy : (y : Γ) = a * x * a⁻¹) :
    sectionAut ψ hψ hker haK haN (ψ x) = ψ y := by
  rw [sectionAut_apply]
  congr 1
  exact Subtype.ext hxy.symm

theorem sectionAut_pow_three (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {a : Γ}
    (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (ha3 : a ^ 3 = 1) : sectionAut ψ hψ hker haK haN ^ 3 = 1 := by
  ext w
  obtain ⟨x, rfl⟩ := hψ w
  rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, sectionAut_apply, sectionAut_apply,
    sectionAut_apply, MulAut.one_apply, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul,
    ← map_mul]
  congr 1
  have h1 : (⟨a, haK⟩ * ⟨a, haK⟩ * ⟨a, haK⟩ : Subgroup.normalizer (K : Set Γ)) = 1 :=
    Subtype.ext (by
      change a * a * a = 1
      rw [← pow_three']
      exact ha3)
  rw [h1, map_one, MulAut.one_apply]

theorem exists_mem_of_isInnerAut_sectionAut (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {a : Γ}
    (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (haN : a ∈ Subgroup.normalizer (N : Set Γ))
    (hin : IsInnerAut (sectionAut ψ hψ hker haK haN)) :
    ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ * (k * x * k⁻¹)⁻¹ ∈ N := by
  obtain ⟨w, hw⟩ := hin
  obtain ⟨k, rfl⟩ := hψ w
  refine ⟨k, k.2, fun x hx => ?_⟩
  have hax : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haK x).mp hx
  have h1 := sectionAut_apply' ψ hψ hker haK haN (x := ⟨x, hx⟩) (y := ⟨_, hax⟩) rfl
  rw [← hw, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h1
  have h2 : ψ (⟨a * x * a⁻¹, hax⟩ * (k * ⟨x, hx⟩ * k⁻¹)⁻¹) = 1 := by
    rw [map_mul, ← h1, map_inv, mul_inv_cancel]
  rw [hker] at h2
  simpa using h2

theorem isSimpleGroup_of_isoLThreeMinusPi {p f : ℕ} [hp : Fact p.Prime] (hf : 1 ≤ f)
    (hX : Sec8.IsoLThreeMinusPi X p f) : IsSimpleGroup X := by
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have h : UnitaryFieldData p f (GaloisField p (2 * f)) :=
      ⟨hp.out, hf, GaloisField.card p (2 * f) (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    have := h.finite
    have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
      intro h3
      have h2 : p ^ f = 2 := (Prod.mk.inj h3).2
      rw [h2] at hq
      norm_num at hq
    have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) (GaloisField p (2 * f)))) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU _ p f h.card_eq_sq 3
        le_rfl hnq
    have : IsSimpleGroup (unitaryPSU h 3) := (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
    exact (e.trans φ.symm).isSimpleGroup
  · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p f)
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p f)) :=
      (CFSG.LinearGroups.linear_projective_simple (K := GaloisField p f) (n := 3) (by omega)
        (Or.inl le_rfl)).2.1
    exact ((e.trans φ).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField p f)).symm).isSimpleGroup

theorem mem_of_mem_thetaIn [Finite Γ] {L : Subgroup Γ} (hKL : K ≤ L) [Group.IsPerfect K]
    {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hX : Sec8.IsoLThreeMinusPi X p f) (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ∀ x : K, ψ x = 1 ↔ (x : Γ) ∈ N) {x : K}
    (hx : (x : Γ) ∈ thetaIn L) : (x : Γ) ∈ N := by
  have := isSimpleGroup_of_isoLThreeMinusPi hf hX
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hψ
  set W := (thetaIn L).subgroupOf K with hW
  have hWn : W.Normal := ⟨fun n hn k => by
    rw [hW, Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_thetaIn (Subgroup.le_normalizer (hKL k.2)) hn⟩
  have hθs : Group.IsSolvable (thetaIn L) := by
    have : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).1
    exact Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)
  have hWs : Group.IsSolvable W := by
    have hinj : Function.Injective (Subgroup.inclusion (show W.map K.subtype ≤ thetaIn L by
        rintro _ ⟨y, hy, rfl⟩
        exact hy) |>.comp (K.subtype.subgroupMap W)) := by
      intro y z hyz
      have := congrArg (fun t : thetaIn L => (t : Γ)) hyz
      exact Subtype.ext (Subtype.ext this)
    exact Group.isSolvable_of_isSolvable_injective hinj
  set H := W.map ψ with hH
  have hHn : H.Normal := hWn.map ψ hψ
  have hHs : Group.IsSolvable H := Group.isSolvable_of_surjective (ψ.subgroupMap_surjective W)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hbot | htop
  · have h1 : ψ x ∈ H := Subgroup.mem_map_of_mem _ (by rw [hW, Subgroup.mem_subgroupOf]; exact hx)
    rw [hbot, Subgroup.mem_bot, hker] at h1
    exact h1
  · exfalso
    have : Group.IsSolvable X := by
      have : Group.IsSolvable (⊤ : Subgroup X) := htop ▸ hHs
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype)
        (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
    exact Group.IsPerfect.not_isSolvable X this

end CFSG.RankThree.PartTwo.Sec14.Item148Res9
