module

public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Residual

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_inSubgroup_perfectResidual {P U : Subgroup Y} (hP : ⁅P, P⁆ = P) (hPU : P ≤ U) :
    P ≤ inSubgroup perfectResidual U := by
  have key : ∀ n : ℕ, P ≤ (derivedSeries U n).map U.subtype := by
    intro n
    induction n with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hPU
    | succ n ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, ← hP]
      exact Subgroup.commutator_mono ih ih
  rw [inSubgroup, perfectResidual, Subgroup.map_iInf _ U.subtype_injective]
  exact le_iInf key

theorem commutator_inSubgroup_perfectResidual (U : Subgroup Y) :
    ⁅inSubgroup perfectResidual U, inSubgroup perfectResidual U⁆ =
      inSubgroup perfectResidual U := by
  have hp : Group.IsPerfect (perfectResidual U) :=
    (CFSG.perfect_residual_characterization (G := U)).2.2.1
  rw [Subgroup.isPerfect_iff] at hp
  rw [inSubgroup, ← Subgroup.map_commutator, hp]

theorem inSubgroup_perfectResidual_mono {U U₁ : Subgroup Y} (h : U ≤ U₁) :
    inSubgroup perfectResidual U ≤ inSubgroup perfectResidual U₁ :=
  le_inSubgroup_perfectResidual (commutator_inSubgroup_perfectResidual U)
    ((Subgroup.map_subtype_le _).trans h)

theorem inSubgroup_perfectResidual_le_of_isSolvable {N U : Subgroup Y} (hNU : N ≤ U)
    [hn : (N.subgroupOf U).Normal] (hs : Group.IsSolvable (U ⧸ N.subgroupOf U)) :
    inSubgroup perfectResidual U ≤ N := by
  have h := ((CFSG.perfect_residual_characterization (G := U)).2.2.2.2.1 (N.subgroupOf U)).mp hs
  rw [inSubgroup, ← Subgroup.map_subgroupOf_eq_of_le hNU]
  exact Subgroup.map_mono h

theorem perfectResidual_eq_of_isSubnormal {K R : Subgroup Y} [hRn : R.Normal]
    (hRs : Group.IsSolvable R) (hK : K.IsSubnormal) (hKp : ⁅K, K⁆ = K) (hKR : K ⊔ R = ⊤) :
    inSubgroup perfectResidual (⊤ : Subgroup Y) = K := by
  have hmul : ∀ y : Y, ∃ k ∈ K, ∃ r ∈ R, y = k * r := by
    intro y
    have hy : y ∈ ((K ⊔ R : Subgroup Y) : Set Y) := by rw [hKR]; trivial
    rw [Subgroup.mul_normal] at hy
    obtain ⟨k, hk, r, hr, rfl⟩ := hy
    exact ⟨k, hk, r, hr, rfl⟩
  have claim : ∀ U : Subgroup Y, U.IsSubnormal → K ≤ U →
      inSubgroup perfectResidual U = inSubgroup perfectResidual (⊤ : Subgroup Y) := by
    intro U hU
    induction hU with
    | top => intro _; rfl
    | step U U₁ hUU₁ hU₁ hn ih =>
      intro hKU
      rw [← ih (hKU.trans hUU₁)]
      refine le_antisymm (inSubgroup_perfectResidual_mono hUU₁) ?_
      have hs : Group.IsSolvable (U₁ ⧸ U.subgroupOf U₁) := by
        have hRs' : Group.IsSolvable ((U₁ ⊓ R).subgroupOf U₁) :=
          Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.inclusion (inf_le_right : U₁ ⊓ R ≤ R)).comp
              (Subgroup.subgroupOfEquivOfLe (inf_le_left : U₁ ⊓ R ≤ U₁)).toMonoidHom)
            ((Subgroup.inclusion_injective (inf_le_right : U₁ ⊓ R ≤ R)).comp
              (MulEquiv.injective _))
        refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (U.subgroupOf U₁)).comp
          ((U₁ ⊓ R).subgroupOf U₁).subtype) ?_
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
        obtain ⟨k, hk, r, hr, hx⟩ := hmul x
        have hrU₁ : r ∈ U₁ := by
          have : r = k⁻¹ * x := by rw [hx]; group
          rw [this]
          exact U₁.mul_mem (U₁.inv_mem (hUU₁ (hKU hk))) x.2
        refine ⟨⟨⟨r, hrU₁⟩, Subgroup.mem_subgroupOf.mpr ⟨hrU₁, hr⟩⟩, ?_⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
        have hxkr : x = ⟨k, hUU₁ (hKU hk)⟩ * ⟨r, hrU₁⟩ := Subtype.ext hx
        have hk1 : QuotientGroup.mk' (U.subgroupOf U₁) (⟨k, hUU₁ (hKU hk)⟩ : U₁) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hKU hk))
        rw [hxkr, map_mul, hk1, one_mul]
      have h1 := inSubgroup_perfectResidual_le_of_isSolvable hUU₁ hs
      exact le_inSubgroup_perfectResidual (commutator_inSubgroup_perfectResidual U₁) h1
  rw [← claim K hK le_rfl]
  refine le_antisymm (Subgroup.map_subtype_le _) (le_inSubgroup_perfectResidual hKp le_rfl)

end Residual

section Ambient

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_le {K X Y : Subgroup G} (hsn : (K.subgroupOf X).IsSubnormal)
    (hYX : Y ≤ X) : (K.subgroupOf Y).IsSubnormal := by
  have h := hsn.comap (Subgroup.inclusion hYX)
  convert h using 1
  ext y
  simp [Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem commutator_subgroupOf_eq {K Y : Subgroup G} (hKY : K ≤ Y) (hK : ⁅K, K⁆ = K) :
    ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
  have hp : Group.IsPerfect K := (Subgroup.isPerfect_iff).mpr hK
  have hp' : Group.IsPerfect (K.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKY).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact (Subgroup.isPerfect_iff).mp hp'

theorem inSubgroup_perfectResidual_eq_of_isSubnormal {K R Y : Subgroup G} (hKY : K ≤ Y)
    (hRY : R ≤ Y) (hYR : Y ≤ Subgroup.normalizer (R : Set G)) (hRs : Group.IsSolvable R)
    (hsn : (K.subgroupOf Y).IsSubnormal) (hK : ⁅K, K⁆ = K) (hKR : K ⊔ R = Y) :
    inSubgroup perfectResidual Y = K := by
  have hRn : (R.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mpr hYR
  have hRs' : Group.IsSolvable (R.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRY).toMonoidHom) (MulEquiv.injective _)
  have hsup : K.subgroupOf Y ⊔ R.subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKY hRY, hKR, Subgroup.subgroupOf_self]
  have h := perfectResidual_eq_of_isSubnormal hRs' hsn (commutator_subgroupOf_eq hKY hK) hsup
  have h2 := congrArg (Subgroup.map Y.subtype) h
  rwa [← inSubgroup_perfectResidual_map Y.subtype Y.subtype_injective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hKY] at h2

omit [Finite G] in
theorem commutator_eq_of_mem_oTwoComponentsIn {X K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn X) : ⁅K, K⁆ = K :=
  (Subgroup.isPerfect_iff).mp (isPerfect_of_mem_oTwoComponentsIn hK)

theorem inSubgroup_perfectResidual_sup_pCoreOf {X K : Subgroup G} (hK : K ∈ oTwoComponentsIn X) :
    inSubgroup perfectResidual (K ⊔ CFSG.Open.pCoreOf 2 X) = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKX, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  have hQX : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hYX : K ⊔ CFSG.Open.pCoreOf 2 X ≤ X := sup_le hKX hQX
  have hQs : Group.IsSolvable (CFSG.Open.pCoreOf 2 X) := by
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).isNilpotent
    infer_instance
  exact inSubgroup_perfectResidual_eq_of_isSubnormal le_sup_left le_sup_right
    (hYX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)) hQs
    (isSubnormal_subgroupOf_of_le hsn hYX) (commutator_eq_of_mem_oTwoComponentsIn hK) rfl

theorem eq_of_sup_pCoreOf_eq {X K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ oTwoComponentsIn X)
    (h₂ : K₂ ∈ oTwoComponentsIn X)
    (h : K₁ ⊔ CFSG.Open.pCoreOf 2 X = K₂ ⊔ CFSG.Open.pCoreOf 2 X) : K₁ = K₂ := by
  rw [← inSubgroup_perfectResidual_sup_pCoreOf h₁, h, inSubgroup_perfectResidual_sup_pCoreOf h₂]

theorem pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn {X K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn X) : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', ⟨-, hsn, -⟩, rfl⟩ := hK
  have h1 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hsn
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  rwa [← pCoreOf_map X.subtype X.subtype_injective] at h2

omit [Finite G] in
theorem map_conj_mem_oTwoComponentsIn {X K : Subgroup G} (hK : K ∈ oTwoComponentsIn X) {g : G}
    (hg : g ∈ X) : K.map (MulAut.conj g).toMonoidHom ∈ oTwoComponentsIn X := by
  have h := map_mem_oTwoComponentsIn (MulAut.conj g) hK
  have hX : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  rwa [hX] at h

theorem mem_normalizer_of_eq_sup {X K L : Subgroup G} (hK : K ∈ oTwoComponentsIn X)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) {g : G} (hg : g ∈ X)
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) : g ∈ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  have hKQ : CFSG.Open.pCoreOf 2 K ≤ Q := pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
  have hQg : Q.map (MulAut.conj g).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hg)
  have hLg : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgL
  have hsup : K ⊔ Q = L ⊔ Q := by
    apply le_antisymm
    · rw [hKL]
      exact sup_le (sup_le le_sup_left (hKQ.trans le_sup_right)) le_sup_right
    · rw [hKL]
      exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have heq : K.map (MulAut.conj g).toMonoidHom = K := by
    refine eq_of_sup_pCoreOf_eq (map_conj_mem_oTwoComponentsIn hK hg) hK ?_
    calc K.map (MulAut.conj g).toMonoidHom ⊔ Q
        = (K ⊔ Q).map (MulAut.conj g).toMonoidHom := by rw [Subgroup.map_sup, hQg]
      _ = (L ⊔ Q).map (MulAut.conj g).toMonoidHom := by rw [hsup]
      _ = L ⊔ Q := by rw [Subgroup.map_sup, hLg, hQg]
      _ = K ⊔ Q := hsup.symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

end Ambient

end CFSG.RankThree.PartTwo.Sec18
