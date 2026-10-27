module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bF

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Fields

variable {G : Type} [Group G] [Finite G] {T M H K : Subgroup G} (c : Case2a.Setting T M H K)

@[expose] def K1 (P1 : Subgroup (E2.StarQuot (H ⊓ M) H)) : Subgroup G :=
  perfectCore (Khat (H ⊓ M) c.le_H P1)

variable {c}

omit [Finite G] in
theorem K1_le (P1 : Subgroup (E2.StarQuot (H ⊓ M) H)) : K1 c P1 ≤ K :=
  (perfectCore_le _).trans Khat_le

omit [Finite G] in
theorem inf_le_Khat {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)}
    (hUP : E2.star (H ⊓ M) H (T ⊓ K) ≤ P1) : T ⊓ K ≤ Khat (H ⊓ M) c.le_H P1 := fun t ht =>
  mem_Khat.mpr ⟨ht.2, hUP (GoldS146R.mem_imgJ.mpr ⟨⟨t, c.le_H' ht.1⟩, ht, rfl⟩)⟩

omit [Finite G] in
theorem inf_le_normalizer_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)}
    (hUP : E2.star (H ⊓ M) H (T ⊓ K) ≤ P1) :
    T ⊓ K ≤ Subgroup.normalizer (K1 c P1 : Set G) := by
  rintro t ⟨htT, htK⟩
  have htH : t ∈ H := c.le_H htK
  refine mem_normalizer_perfectCore_Khat htH (Subgroup.le_normalizer htK) ?_
  exact Subgroup.le_normalizer (hUP (GoldS146R.mem_imgJ.mpr ⟨⟨t, htH⟩, ⟨htT, htK⟩, rfl⟩))

theorem pCore_le_normalizer_K1 (P1 : Subgroup (E2.StarQuot (H ⊓ M) H)) :
    pCoreOf 2 H ≤ Subgroup.normalizer (K1 c P1 : Set G) := by
  intro q hq
  have hqH : q ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hq
  refine mem_normalizer_perfectCore_Khat hqH (c.pCore_le_normalizer hq) ?_
  have h1 : ((⟨q, hqH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (c.pCore_le_kerIn hq))
  rw [h1]
  exact one_mem _

theorem sylow_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)}
    (hUP : E2.star (H ⊓ M) H (T ⊓ K) ≤ P1) : IsSylowTwoOf (T ⊓ K1 c P1) (K1 c P1) := by
  have h1 : IsSylowTwoOf (T ⊓ K) (Khat (H ⊓ M) c.le_H P1) :=
    B6.isSylowTwoOf_mono c.sylow_inf (inf_le_Khat (c := c) hUP) Khat_le
  have hn : Khat (H ⊓ M) c.le_H P1 ≤ Subgroup.normalizer (K1 c P1 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le _)).mp (perfectCore_normal _)
  have h2 := A4.isSylowTwoOf_inf_normal h1 (perfectCore_le _) hn
  have e : (T ⊓ K) ⊓ K1 c P1 = T ⊓ K1 c P1 := by
    rw [inf_assoc, inf_eq_right.mpr (K1_le P1)]
  rw [← e]
  exact h2

theorem star_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)} (hP : P1 ≤ E2.star (H ⊓ M) H K) :
    E2.star (H ⊓ M) H (K1 c P1) = perfectCore P1 :=
  star_perfectCore_Khat hP

omit [Finite G] in
theorem inf_pCore_le_pCoreOf {X : Subgroup G} (hXH : X ≤ H) [Finite G] :
    pCoreOf 2 H ⊓ X ≤ pCoreOf 2 X := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hk), Subgroup.le_normalizer hk⟩

section Levi

variable {F : Type} [Field F] [Finite F] {m : ℕ}

theorem isL2Quot_K1 {P1 : Subgroup (E2.StarQuot (H ⊓ M) H)} (hP1 : P1 ≤ E2.star (H ⊓ M) H K)
    (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) (g : ↥(perfectCore P1) →* SL(2, F))
    (hg : Function.Surjective g) (hk : IsPGroup 2 g.ker) :
    ∃ ψ : ↥(K1 c P1) →* SL(2, F), Function.Surjective ψ ∧ Group.IsSolvable ψ.ker ∧
      IsL2Quot m (OTwoQuot (K1 c P1)) := by
  classical
  have hYH : K1 c P1 ≤ H := (K1_le P1).trans c.le_H
  let κ : ↥(K1 c P1) →* E2.StarQuot (H ⊓ M) H :=
    (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)).comp (Subgroup.inclusion hYH)
  have hκmem : ∀ x : ↥(K1 c P1), κ x ∈ perfectCore P1 := fun x => by
    rw [← star_K1 (c := c) hP1]
    exact GoldS146R.mem_imgJ.mpr ⟨Subgroup.inclusion hYH x, x.2, rfl⟩
  let κ' : ↥(K1 c P1) →* ↥(perfectCore P1) := κ.codRestrict _ hκmem
  have hκ' : Function.Surjective κ' := fun y => by
    have hy : (y : E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H (K1 c P1) := by
      rw [star_K1 (c := c) hP1]
      exact y.2
    obtain ⟨h, hh, hhy⟩ := Case2a.exists_of_mem_star hy
    exact ⟨⟨h, hh⟩, Subtype.ext hhy⟩
  have hRN : ∀ x ∈ (g.comp κ').ker, ∃ k : ℕ, x ^ 2 ^ k ∈ κ'.ker := by
    intro x hx
    obtain ⟨k, hk'⟩ := hk ⟨κ' x, hx⟩
    refine ⟨k, ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val hk'
  have hN : ∀ n ∈ κ'.ker, ∀ y : ↥(K1 c P1), ⁅n, y⁆ ∈ CFSG.Open.pCore 2 ↥(K1 c P1) := by
    intro n hn y
    have hn1 : κ n = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    have hnJ : (n : G) ∈ kerIn (H ⊓ M) H := by
      have h2 : ((Subgroup.inclusion hYH n : ↥H) : E2.StarQuot (H ⊓ M) H) = 1 := hn1
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (Subgroup.inclusion hYH n)).mp h2)
    have h1 := ((c.ker n).mp hnJ).2 (y : G) (Subgroup.mem_sup_left (K1_le P1 y.2))
    apply Case2a.mem_pCore_of_mem_pCoreOf
    refine inf_pCore_le_pCoreOf hYH ⟨h1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ n.2 y.2)
      (Subgroup.inv_mem _ n.2)) (Subgroup.inv_mem _ y.2)
  have hperf : Group.IsPerfect ↥(K1 c P1) := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  obtain ⟨hL2, hsolv⟩ := isL2Quot_of_levi_cover hm hF hperf (g.comp κ') (hg.comp hκ') κ'.ker
    hRN hN
  exact ⟨g.comp κ', hg.comp hκ', hsolv, hL2⟩

end Levi

end Fields

end CFSG.Quasithin.F146Field.Case2b
