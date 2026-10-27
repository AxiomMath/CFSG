module

public import CFSG.RankThree.GF2n.Stroth80.Sec83CommSect
public import CFSG.RankThree.GF2n.Stroth80.Sec78EichlerRange
public import CFSG.RankThree.GF2n.Stroth80.Sec7CardBeta
public import CFSG.RankThree.GF2n.Stroth80.Sec78UBound


public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.CGT.Timmesfeld75
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem exists_isSecMod_of_sectionAct {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] {R V Z : Subgroup G} (φ : ↥R →* GL ι K)
    (h : SectionAct K R V Z φ (fun g => (g : Matrix ι ι K))) :
    ∃ (iA : DistribMulAction ↥R (ι → K)),
      (∀ (r : ↥R) (x : ι → K), r • x = (φ r : Matrix ι ι K) *ᵥ x) ∧
      ∃ κ : ↥V →* Multiplicative (ι → K), IsSecMod R V Z (ι → K) κ := by
  obtain ⟨-, hN, ψ, hψ⟩ := h
  let iA : DistribMulAction ↥R (ι → K) :=
    { smul := fun r x => (φ r : Matrix ι ι K) *ᵥ x
      one_smul := fun x => by
        show (φ 1 : Matrix ι ι K) *ᵥ x = x
        simp
      mul_smul := fun r s x => by
        show (φ (r * s) : Matrix ι ι K) *ᵥ x =
          (φ r : Matrix ι ι K) *ᵥ ((φ s : Matrix ι ι K) *ᵥ x)
        simp [Matrix.mulVec_mulVec]
      smul_zero := fun r => Matrix.mulVec_zero _
      smul_add := fun r x y => Matrix.mulVec_add _ _ _ }
  refine ⟨iA, fun r x => rfl, ?_⟩
  let κ : ↥V →* Multiplicative (ι → K) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf V))
  refine ⟨κ, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (ψ.symm a)
    exact ⟨q, by simp [κ, hq]⟩
  · intro x
    show ψ (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff _ ψ.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro r x y hxy
    exact hψ r x y hxy
  · intro a
    funext i
    exact CharTwo.add_self_eq_zero (a i)


theorem card_commutator_sup_natural {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] [Finite G] {Q₀ : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q₀ X) (hQ : (polarBilin Q₀).Nondegenerate) {R V Z : Subgroup G}
    (φ : ↥R →* GL ι K) (hsec : SectionAct K R V Z φ (fun g => (g : Matrix ι ι K)))
    (hZV : Z ≤ V) {u : ι → K} (hu : Q₀ u = 0) (hu0 : u ≠ 0) {β : ↥R}
    (hβ : φ β ∈ E.LomGL u) (hβ1 : φ β ≠ 1) :
    Nat.card ↥(⁅V, Subgroup.zpowers (β : G)⁆ ⊔ Z) = Nat.card Z * Nat.card K ^ 2 := by
  classical
  obtain ⟨iA, hsmul, κ, hκ⟩ := exists_isSecMod_of_sectionAct φ hsec
  have hP : ∀ r ∈ R, ∀ x ∈ V, r * x * r⁻¹ ∈ V := conj_mem_of_le_normalizer hsec.1
  have h1 := natCard_commutator_sup hκ hP hZV β
  unfold ElemMatrixIso.LomGL at hβ
  obtain ⟨hA, hmem⟩ := mem_matrixOf_iff.1 hβ
  obtain ⟨w, hw, hxw⟩ := mem_rootGroup.mp hmem
  have happ : ∀ v : ι → K, (φ β : Matrix ι ι K) *ᵥ v = eichler Q₀ u w v := by
    intro v
    rw [← E.app ⟨φ β, hA⟩ v]
    exact (congrArg (fun f : _ ≃ₗ[K] _ => f v) hxw).symm
  have hne : eichler Q₀ u w ≠ 1 := by
    intro h
    apply hβ1
    have h2 : E.equiv ⟨φ β, hA⟩ = 1 := Subtype.ext (hxw.symm.trans h)
    have h3 : (⟨φ β, hA⟩ : X) = 1 := by
      have := congrArg E.equiv.symm h2
      rwa [MulEquiv.symm_apply_apply, map_one] at this
    exact congrArg Subtype.val h3
  have hli : LinearIndependent K ![u, w] := eichler_pair_linearIndependent hu0 hu hne
  have hset : ∀ x : ι → K, x ∈ (comm (ι → K) β).range ↔
      ∃ v : ι → K, x = (eichlerG Q₀ u w).app v - v := by
    intro x
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      rw [comm_apply, hsmul]
      show _ = eichler Q₀ u w v - v
      rw [happ]
    · rintro ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      rw [comm_apply, hsmul]
      rw [happ]
      rfl
  have hcard : Nat.card ↥(comm (ι → K) β).range = Nat.card K ^ 2 := by
    rw [← eichlerRangeCard_holds K (ι → K) Q₀ hQ u w hu hw hli]
    exact Nat.card_congr (Equiv.subtypeEquivRight hset)
  rw [h1, hcard]


theorem step78_core {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    {Q₀ : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q₀ X)
    (hQ : (polarBilin Q₀).Nondegenerate) (h4 : 4 ≤ Fintype.card ι) [Finite G]
    {R N V W Z L₁ L₂ A₁ A₂ : Subgroup G} (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R) (hsec : SectionAct K R V Z φ (fun g => (g : Matrix ι ι K)))
    (hZV : Z ≤ V) (hd : IsOppDecomp W V L₁ L₂ A₁ A₂)
    (hWn : ∀ r ∈ R, ∀ x ∈ W, r * x * r⁻¹ ∈ W) (hVn : ∀ r ∈ R, ∀ x ∈ V, r * x * r⁻¹ ∈ V)
    (hNW : ∀ n ∈ N, ∀ y ∈ W, ⁅n, y⁆ ∈ V) (h₁ : L₁ ≤ R) (h₂ : L₂ ≤ R)
    {u u' : ι → K} (hu : Q₀ u = 0) (hu' : Q₀ u' = 0) (hu0 : u ≠ 0) (huu' : polar Q₀ u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u')
    {β : ↥R} (hβ : (β : G) ∈ L₁) (hβN : (β : G) ∉ N)
    (hbig : 6 ≤ Fintype.card ι ∨ ∃ v, polar Q₀ v ((φ β : Matrix ι ι K) *ᵥ v) ≠ 0) :
    ∃ c Y : ℕ, Nat.card ↥(⁅W, Subgroup.zpowers (β : G)⁆ ⊔ V) = Nat.card V * c ∧
      Nat.card ↥(⁅V, Subgroup.zpowers (β : G)⁆ ⊔ Z) = Nat.card Z * Nat.card K ^ 2 ∧
      Nat.card W = Nat.card V * Y ∧ Y ≤ c ^ 4 := by
  classical
  have hVW : V ≤ W := hd.1.trans hd.2.1
  have hsecWV : SecHyp R W V := SecHyp.of_isOppDecomp hd hWn hVn
  obtain ⟨Y, iY, iD, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsecWV hNW
  haveI : Finite Y := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hWn hκ hd h₁ h₂
  have hβL : β ∈ L₁.subgroupOf R := Subgroup.mem_subgroupOf.mpr hβ
  have hβ1 : φ β ≠ 1 := by
    intro h
    apply hβN
    have : β ∈ φ.ker := MonoidHom.mem_ker.mpr h
    rw [hNφ] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hβE : φ β ∈ E.LomGL u := by
    rw [← hL₁]
    exact Subgroup.mem_map_of_mem φ hβL
  have hc1 := natCard_commutator_sup hκ hWn hVW β
  have hW := natCard_eq_of_isSecMod hVW hκ
  have hE := card_commutator_sup_natural E hQ φ hsec hZV hu hu0 hβE hβ1
  refine ⟨Nat.card ↥(comm Y β).range, Nat.card Y, hc1, hE, hW, ?_⟩
  rcases hbig with h6 | hn
  · exact uBound E hQ h6 φ hφ hκ.two hker hu hu' huu' hL₁ hL₂ hdec hβL hβ1
  · have huu'' : polar Q₀ u' u ≠ 0 := by rwa [polar_comm]
    obtain ⟨hr, hcard⟩ := uBound_of_c2 E hQ h4 φ hφ hκ.two hker hu hu' huu' hL₁ hL₂ hdec hβL hn
    have hc0 : 0 < Nat.card ↥(comm Y β).range := Nat.card_pos
    rw [hcard, ← hr]
    calc Nat.card ↥(comm Y β).range ^ 2 ≤ Nat.card ↥(comm Y β).range ^ 4 :=
          Nat.pow_le_pow_right hc0 (by norm_num)

end CFSG.RankThree.GF2n.Stroth80
