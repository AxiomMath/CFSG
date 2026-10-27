module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseTwoCoreKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The Sylow 3-counting in the Suzuki recognition step

Suzuki §8 shows the first-case group has `n₃ = 70` Sylow 3-subgroups, each
elementary abelian of order nine.  This module derives that count from the
first-case local data (not from a generic order-`2520` classification):

* `[G : Ĥ] = 35` (`FirstCaseCountData`) and `N_G(U) = Ĥ` (Theorem 2.6) make
  the conjugacy class of `U` a 35-element set `UConjugates c`;
* every Sylow 3-subgroup `P` acts on `UConjugates c`; the fixed points are
  exactly the conjugates of `U` contained in `P`;
* `|P| = 9` and `|U| = 3`, so `P` has at most four subgroups of order three,
  while the fixed-point congruence forces the number of fixed points to be
  `2 mod 3`; hence `P ≃ C₃ × C₃` and `P` contains exactly two conjugates of
  `U`.

The remaining double count (each `U`-conjugate lies in four Sylow 3-subgroups,
so `35 · 4 = 70 · 2`) is the input to the index-seven recognition step.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The conjugacy class of `U = O(H)` under conjugation by `G`. -/
@[reducible, expose]
public def UConjugates {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Type u :=
  {V : Subgroup G // ∃ g : G, V = conjugateSubgroup c.U g}

namespace UConjugates

section

variable {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G)

private lemma conjugateSubgroup_mul {G : Type u} [Group G] (H : Subgroup G) (g h : G) :
    conjugateSubgroup (conjugateSubgroup H h) g = conjugateSubgroup H (g * h) := by
  ext x
  simp [conjugateSubgroup, Subgroup.map_map]

private lemma conjugateSubgroup_one {G : Type u} [Group G] (H : Subgroup G) :
    conjugateSubgroup H (1 : G) = H := by
  ext x
  constructor
  · rintro ⟨u, hu, hx⟩
    rw [← hx]
    simpa using hu
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp

/-- The base point `U` of the conjugacy class. -/
@[expose]
public def base : UConjugates c :=
  ⟨c.U, ⟨1, by
    ext x
    simp [conjugateSubgroup]⟩⟩

/-- The underlying subgroup of the base point is `U`. -/
public theorem base_val (c : CentralizerSetup G) : (UConjugates.base c).1 = c.U :=
  rfl

/-- Conjugation action of `G` on the conjugates of `U`. -/
public instance instMulAction :
    MulAction G {V : Subgroup G // ∃ g : G, V = conjugateSubgroup c.U g} where
  smul g V := ⟨conjugateSubgroup V.1 g, by
    rcases V with ⟨W, hW⟩
    rcases hW with ⟨h, rfl⟩
    exact ⟨g * h, conjugateSubgroup_mul c.U g h⟩⟩
  one_smul V := by
    apply Subtype.ext
    change conjugateSubgroup V.1 1 = V.1
    exact conjugateSubgroup_one V.1
  mul_smul g h V := by
    apply Subtype.ext
    change conjugateSubgroup V.1 (g * h) = conjugateSubgroup (conjugateSubgroup V.1 h) g
    exact (conjugateSubgroup_mul V.1 g h).symm

public theorem smul_def (g : G) (V : UConjugates c) :
    g • V = ⟨conjugateSubgroup V.1 g, by
      rcases V with ⟨W, hW⟩
      rcases hW with ⟨h, rfl⟩
      exact ⟨g * h, conjugateSubgroup_mul c.U g h⟩⟩ := by
  apply Subtype.ext
  change conjugateSubgroup V.1 g = conjugateSubgroup V.1 g
  rfl

/-- The stabilizer of `U` in the conjugation action is its normalizer. -/
theorem stabilizer_eq_normalizer :
    MulAction.stabilizer G (base c) = Subgroup.normalizer (c.U : Set G) := by
  ext g
  constructor
  · intro hg
    rw [MulAction.mem_stabilizer_iff] at hg
    rw [smul_def] at hg
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr (by
      simpa [base, conjugateSubgroup] using (congrArg Subtype.val hg))
  · intro hg
    rw [MulAction.mem_stabilizer_iff]
    rw [smul_def]
    apply Subtype.ext
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp hg

theorem base_orbit_eq_top :
    MulAction.orbit G (base c) = ⊤ := by
  ext V
  constructor
  · intro _
    trivial
  · intro _
    rcases V.2 with ⟨g, hV⟩
    refine ⟨g, ?_⟩
    change g • base c = V
    rw [smul_def]
    apply Subtype.ext
    change conjugateSubgroup c.U g = V.1
    rw [hV]

theorem base_orbit_card :
    Nat.card (MulAction.orbit G (base c)) = Nat.card (UConjugates c) := by
  rw [base_orbit_eq_top]
  simp [Nat.card_congr (Equiv.Set.univ (UConjugates c))]

/-- Orbit-stabilizer for the conjugacy class of `U`. -/
public theorem card_eq_index_normalizer :
    Nat.card (UConjugates c) = (Subgroup.normalizer (c.U : Set G)).index := by
  classical
  calc
    Nat.card (UConjugates c) = Nat.card (MulAction.orbit G (base c)) :=
      (base_orbit_card c).symm
    _ = Nat.card (G ⧸ MulAction.stabilizer G (base c)) :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G (base c))
    _ = (MulAction.stabilizer G (base c)).index :=
      (MulAction.stabilizer G (base c)).index_eq_card.symm
    _ = (Subgroup.normalizer (c.U : Set G)).index := by rw [stabilizer_eq_normalizer]

end

end UConjugates

/-- In the first case, `U` has exactly 35 conjugates: the index of its
normalizer `Ĥ`. -/
public theorem firstCase_UConjugates_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Nat.card (UConjugates c) = 35 := by
  classical
  have hklein : IsKleinFour (pCore 2 c.Hhat) := firstCase_twoCore_isKleinFour hmin c hfirst
  have hVK : IsKleinFour (twoCoreOf c.Hhat) := firstCase_klein_V_klein c hklein
  have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    have hfour : Nat.card (twoCoreOf c.Hhat) = 4 := hVK.card_four
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hO2 hUne
  rcases firstCase_index_card_of_countData c d with ⟨hHidx, _⟩
  have hNidx : (Subgroup.normalizer (c.U : Set G)).index = 35 := by
    rw [hNorm, hHidx]
  simpa [hNidx] using (UConjugates.card_eq_index_normalizer c)

/-- In the first case, `U = O(H)` has order three: the Klein branch gives
`Ĥ / O₂(Ĥ)U ≅ D₆`, `|Ĥ| = 72` and `|O₂(Ĥ)| = 4`, so `|U| = 72 / (6 · 4)`. -/
public theorem firstCase_U_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Nat.card c.U = 3 := by
  classical
  have hklein : IsKleinFour (pCore 2 c.Hhat) := firstCase_twoCore_isKleinFour hmin c hfirst
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := c.Hhat
  let N : Subgroup H := pCore 2 H
  let O : Subgroup H := pPrimeCore 2 H
  let K : Subgroup H := N ⊔ O
  have : N.Normal := by
    dsimp [N, H]
    infer_instance
  have : O.Normal := by
    dsimp [O, H]
    infer_instance
  have : K.Normal := by
    dsimp [K, N, O, H]
    infer_instance
  have hNcard : Nat.card N = 4 := hklein.card_four
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := H)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hNp : IsPGroup 2 N := by
    simpa [N] using (pCore_isPGroup (G := H) (p := 2))
  have hNdisjO : Disjoint N O := by
    rcases (IsPGroup.iff_card (p := 2) (G := N)).mp hNp with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card N) (Nat.card O) := by
      rw [hn]
      exact hOcop.pow_left n
    exact Subgroup.disjoint_of_coprime_natCard hcop
  have hOleN : O ≤ Subgroup.normalizer (N : Set H) := by
    have : N.Normal := by infer_instance
    simp [Subgroup.normalizer_eq_top]
  have hKcard : Nat.card (↥K) = Nat.card N * Nat.card O := by
    exact card_sup_eq_mul_of_disjoint_of_le_normalizer N O hOleN hNdisjO
  have hq : Nonempty ((H ⧸ K) ≃* DihedralGroup 3) := by
    simpa [H, N, O, K] using firstCase_klein_quotient_d6 hmin c hfirst hklein
  obtain ⟨eq⟩ := hq
  have hQcard : Nat.card (H ⧸ K) = 6 := by
    calc
      Nat.card (H ⧸ K) = Nat.card (DihedralGroup 3) := Nat.card_congr eq.toEquiv
      _ = 2 * 3 := DihedralGroup.nat_card
      _ = 6 := by norm_num
  have hHcard : Nat.card H = 72 := by
    rcases firstCase_index_card_of_countData c d with ⟨hHidx, hGcard⟩
    have hm := H.index_mul_card
    rw [hHidx, hGcard] at hm
    omega
  have hKindex : K.index = 6 := by
    rw [Subgroup.index_eq_card]
    exact hQcard
  have hmul := K.card_mul_index
  change Nat.card (↥K) * K.index = Nat.card H at hmul
  rw [hKcard, hNcard, hKindex, hHcard] at hmul
  have hOcard : Nat.card O = 3 := by omega
  have h26 := theorem_2_6 hmin c
  have hUmap : c.U = O.map H.subtype := by
    simpa [H, O, oddCoreOf] using h26.1
  have hUcardO : Nat.card c.U = Nat.card O := by
    rw [hUmap]
    exact Subgroup.card_map_of_injective (K := O) (f := H.subtype) H.subtype_injective
  omega

/-- Every Sylow 3-subgroup of the first-case group has order nine. -/
public theorem firstCase_sylow3_card_nine
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    ∀ P : Sylow 3 G, Nat.card P = 9 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro P
  rcases firstCase_index_card_of_countData c d with ⟨_, hGcard⟩
  have hP := P.card_eq_multiplicity
  rw [hGcard] at hP
  have hfac : (2 ^ 3 * 3 ^ 2 * 5 * 7 : ℕ).factorization 3 = 2 := by
    rw [show (2 ^ 3 * 3 ^ 2 * 5 * 7 : ℕ) = 3 ^ 2 * (2 ^ 3 * 5 * 7) by ring]
    rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [Nat.factorization_pow]
    simp [Nat.prime_three.factorization_self]
    exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (2 ^ 3 * 5 * 7 : ℕ))
  rw [hfac] at hP
  norm_num at hP
  exact hP

private lemma order3_subgroup_zpowers_eq {G : Type u} [Group G] [Finite G]
    {X : Subgroup G} (hX : Nat.card X = 3) {x : G} (hx : x ∈ X) (hxne : x ≠ 1) :
    Subgroup.zpowers x = X := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    exact X.zpow_mem hx n
  · have hord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        have hd := Subgroup.orderOf_dvd_natCard X hx
        rwa [hX] at hd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exfalso
        apply hxne
        exact orderOf_eq_one_iff.mp h1
      · exact h3
    rw [Nat.card_zpowers, hord, hX]

private lemma order3_subgroups_eq_of_common_nonidentity {G : Type u} [Group G] [Finite G]
    {X Y : Subgroup G} (hX : Nat.card X = 3) (hY : Nat.card Y = 3)
    {x : G} (hxX : x ∈ X) (hxY : x ∈ Y) (hxne : x ≠ 1) :
    X = Y := by
  exact (order3_subgroup_zpowers_eq hX hxX hxne).symm.trans
    (order3_subgroup_zpowers_eq hY hxY hxne)

/-- A group of order nine has at most four subgroups of order three. -/
private lemma card_order3_subgroups_le_four {G : Type u} [Group G] [Finite G]
    (hG9 : Nat.card G = 9) :
    Nat.card {X : Subgroup G // Nat.card X = 3} ≤ 4 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let S : Type u := {X : Subgroup G // Nat.card X = 3}
  let : Fintype S := Fintype.ofFinite S
  let part : S → Finset G := fun X =>
    {x : G | x ∈ (X.1 : Set G) ∧ x ≠ 1}.toFinset
  have hpartcard : ∀ X : S, (part X).card = 2 := by
    intro X
    have hXset : ({x : G | x ∈ (X.1 : Set G) ∧ x ≠ 1} : Set G) =
        (X.1 : Set G) \ {1} := by
      ext x
      simp [Set.mem_sdiff]
    have hc2' : ({x : G | x ∈ (X.1 : Set G) ∧ x ≠ 1} : Set G).ncard = 2 := by
      rw [hXset]
      rw [Set.ncard_sdiff_singleton_of_mem (s := (X.1 : Set G)) (a := (1 : G))
        X.1.one_mem]
      have hX3 : (X.1 : Set G).ncard = 3 := by
        rw [← Nat.card_coe_set_eq (X.1 : Set G)]
        exact X.2
      rw [hX3]
    rw [← Set.ncard_eq_toFinset_card'
      ({x : G | x ∈ (X.1 : Set G) ∧ x ≠ 1} : Set G)]
    exact hc2'
  have hdisj : ((Finset.univ : Finset S) : Set S).PairwiseDisjoint part := by
    intro X hX Y hY hXY
    change Disjoint (part X) (part Y)
    rw [Finset.disjoint_left]
    intro x hxX hxY
    apply hXY
    have hxX' : x ∈ X.1 ∧ x ≠ 1 := by simpa [part] using hxX
    have hxY' : x ∈ Y.1 ∧ x ≠ 1 := by simpa [part] using hxY
    exact Subtype.ext (order3_subgroups_eq_of_common_nonidentity X.2 Y.2
      hxX'.1 hxY'.1 hxX'.2)
  have hbunion := Finset.card_biUnion (s := (Finset.univ : Finset S)) (t := part) hdisj
  have htotal : (Finset.univ.biUnion part).card = 2 * Fintype.card S := by
    rw [hbunion]
    simp [hpartcard, mul_comm]
  have hsubset : (Finset.univ.biUnion part) ⊆ {x : G | x ≠ 1}.toFinset := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨X, hX, hxpart⟩
    have hxpart' : x ∈ X.1 ∧ x ≠ 1 := by simpa [part] using hxpart
    simpa using hxpart'.2
  have hone : ({x : G | x ≠ 1} : Set G).ncard = 8 := by
    have hset : ({x : G | x ≠ 1} : Set G) = (Set.univ : Set G) \ {1} := by
      ext x
      simp
    rw [hset]
    rw [Set.ncard_sdiff_singleton_of_mem (s := (Set.univ : Set G)) (a := (1 : G)) (by simp)]
    rw [Set.ncard_univ, hG9]
  have hle : (Finset.univ.biUnion part).card ≤ 8 := by
    calc
      (Finset.univ.biUnion part).card ≤ ({x : G | x ≠ 1} : Set G).toFinset.card :=
        Finset.card_le_card hsubset
      _ = 8 := by
        rw [← Set.ncard_eq_toFinset_card'
          ({x : G | x ≠ 1} : Set G)]
        exact hone
  have hcardS : 2 * Nat.card S ≤ 8 := by
    rw [Nat.card_eq_fintype_card]
    omega
  have hSle : Nat.card S ≤ 4 := by omega
  simpa [S] using hSle

/-- A conjugate `V` of `U` is fixed by the Sylow 3-subgroup `P` exactly when
`V ≤ P`: normalization forces containment by Sylow maximality, and
containment forces normalization because a group of order nine is
commutative. -/
private lemma le_subgroup_iff_normalizer {G : Type u} [Group G] [Finite G]
    {P : Sylow 3 G} (hP9 : Nat.card P = 9)
    {V : Subgroup G} (hV3 : Nat.card V = 3) :
    V ≤ (P : Subgroup G) ↔ (P : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := by
  classical
  constructor
  · intro hVleP
    have hP9' : Nat.card P = 3 ^ 2 := by simpa using hP9
    have : IsMulCommutative P :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9'
    have hcomm : ∀ p : P, ∀ v : G, v ∈ V → (p : G) * v = v * (p : G) := by
      intro p v hv
      exact congrArg Subtype.val
        (((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9').is_comm).comm
          p ⟨v, hVleP hv⟩)
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (p : G) * v * (p : G)⁻¹ = v := by
        rw [hcomm ⟨p, hp⟩ v hv]
        group
      simpa [MulAut.conj_apply, hv']
    · intro hx
      refine ⟨x, hx, ?_⟩
      simp [MulAut.conj_apply, hcomm ⟨p, hp⟩ x hx]
  · intro hPV
    have hVp : IsPGroup 3 V := by
      refine IsPGroup.of_card (n := 1) ?_
      simpa using hV3
    have hsupP : IsPGroup 3 ((P : Subgroup G) ⊔ V : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' P.2 hVp hPV
    have hsup : (P : Subgroup G) ⊔ V = (P : Subgroup G) :=
      P.is_maximal' (Q := ((P : Subgroup G) ⊔ V : Subgroup G)) hsupP le_sup_left
    simpa [hsup] using (le_sup_right : V ≤ (P : Subgroup G) ⊔ V)

private lemma fixedPoint_iff_le {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {P : Sylow 3 G} (hP9 : Nat.card P = 9)
    {V : UConjugates c} (hV3 : Nat.card V.1 = 3) :
    V ∈ MulAction.fixedPoints P (UConjugates c) ↔ V.1 ≤ (P : Subgroup G) := by
  classical
  rw [le_subgroup_iff_normalizer hP9 hV3]
  constructor
  · intro hfix p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hfixp : (⟨p, hp⟩ : P) • V = V := (MulAction.mem_fixedPoints.mp hfix) ⟨p, hp⟩
    have hfixp' : (p : G) • V = V := by
      rw [Subgroup.smul_def] at hfixp
      exact hfixp
    rw [UConjugates.smul_def] at hfixp'
    exact congrArg Subtype.val hfixp'
  · intro hPV
    rw [MulAction.mem_fixedPoints]
    intro p
    change (p : G) • V = V
    rw [UConjugates.smul_def]
    apply Subtype.ext
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPV p.2))

/-- Every Sylow 3-subgroup of the first-case group has exactly two conjugates
of `U` inside it: the fixed-point congruence `≡ 35 ≡ 2 [MOD 3]` and the bound
`≤ 4` (a group of order nine has at most four order-three subgroups). -/
private lemma uConjugates_card_three {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (V : UConjugates c) : Nat.card V.1 = 3 := by
  rcases V with ⟨W, hW⟩
  rcases hW with ⟨g, rfl⟩
  have hcard : Nat.card (conjugateSubgroup c.U g) = Nat.card c.U := by
    exact (Nat.card_congr (Subgroup.equivMapOfInjective c.U
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm
  rw [hcard]
  exact firstCase_U_card_three hmin c hfirst d

private lemma sylow3_fixedPoints_card_eq_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) :
    Nat.card (MulAction.fixedPoints P (UConjugates c)) = 2 := by
  classical
  let Ω := UConjugates c
  have hP9 : Nat.card P = 9 := firstCase_sylow3_card_nine c d P
  have hU3 : ∀ V : UConjugates c, Nat.card V.1 = 3 := by
    exact uConjugates_card_three hmin c hfirst d
  have hfix_iff : ∀ V : Ω, V ∈ MulAction.fixedPoints P Ω ↔ V.1 ≤ (P : Subgroup G) := by
    intro V
    simpa [Ω] using fixedPoint_iff_le c hP9 (hU3 V)
  let f : MulAction.fixedPoints P Ω → {X : Subgroup P // Nat.card X = 3} := fun V =>
    ⟨V.1.1.subgroupOf (P : Subgroup G), by
      have hVle : V.1.1 ≤ (P : Subgroup G) := (hfix_iff V.1).mp V.2
      have hcard : Nat.card (V.1.1.subgroupOf (P : Subgroup G)) = Nat.card V.1.1 := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv
      rw [hcard]
      exact hU3 V.1⟩
  have hf_inj : Function.Injective f := by
    intro V W h
    apply Subtype.ext
    apply Subtype.ext
    have hVle : V.1.1 ≤ (P : Subgroup G) := (hfix_iff V.1).mp V.2
    have hWle : W.1.1 ≤ (P : Subgroup G) := (hfix_iff W.1).mp W.2
    have hsub := congrArg Subtype.val h
    have hinf : V.1.1 ⊓ (P : Subgroup G) = W.1.1 ⊓ (P : Subgroup G) :=
      Subgroup.subgroupOf_inj.mp hsub
    have hVinf : V.1.1 ⊓ (P : Subgroup G) = V.1.1 := inf_eq_left.mpr hVle
    have hWinf : W.1.1 ⊓ (P : Subgroup G) = W.1.1 := inf_eq_left.mpr hWle
    exact hVinf.symm.trans (hinf.trans hWinf)
  have hle1 : Nat.card (MulAction.fixedPoints P Ω) ≤
      Nat.card {X : Subgroup P // Nat.card X = 3} :=
    Nat.card_le_card_of_injective f hf_inj
  have hle2 : Nat.card {X : Subgroup P // Nat.card X = 3} ≤ 4 :=
    card_order3_subgroups_le_four (G := P) hP9
  have hmod0 : Nat.card Ω ≡ Nat.card (MulAction.fixedPoints P Ω) [MOD 3] :=
    P.2.card_modEq_card_fixedPoints Ω
  have hcardU : Nat.card Ω = 35 := by simpa [Ω] using firstCase_UConjugates_card hmin c hfirst d
  have hmod : Nat.card (MulAction.fixedPoints P Ω) % 3 = 2 := by
    change Nat.card Ω % 3 = Nat.card (MulAction.fixedPoints P Ω) % 3 at hmod0
    rw [hcardU] at hmod0
    norm_num at hmod0
    exact hmod0.symm
  have hle : Nat.card (MulAction.fixedPoints P Ω) ≤ 4 := le_trans hle1 hle2
  have hfix : Nat.card (MulAction.fixedPoints P Ω) = 2 := by omega
  simpa [Ω] using hfix

/-- In the first case every Sylow 3-subgroup contains exactly two conjugates
of `U`. -/
theorem firstCase_sylow3_inside_card_eq_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) :
    Nat.card {V : UConjugates c // V.1 ≤ (P : Subgroup G)} = 2 := by
  classical
  have hP9 : Nat.card P = 9 := firstCase_sylow3_card_nine c d P
  let e : {V : UConjugates c // V.1 ≤ (P : Subgroup G)} ≃
      MulAction.fixedPoints P (UConjugates c) :=
    { toFun := fun V => ⟨V.1,
        (fixedPoint_iff_le (V := V.1) c hP9 (uConjugates_card_three hmin c hfirst d V.1)).mpr V.2⟩
      invFun := fun V => ⟨V.1,
        (fixedPoint_iff_le (V := V.1) c hP9 (uConjugates_card_three hmin c hfirst d V.1)).mp V.2⟩
      left_inv := by
        intro V
        apply Subtype.ext
        rfl
      right_inv := by
        intro V
        apply Subtype.ext
        rfl }
  have hfix := sylow3_fixedPoints_card_eq_two hmin c hfirst d P
  have hcard := Nat.card_congr e
  rwa [hfix] at hcard

/-- In the first case every Sylow 3-subgroup contains two distinct conjugates
of `U`.  Public wrapper over plain subgroup statements (the private count
above cannot be exported because it mentions the locally defined
`UConjugates` type). -/
public theorem firstCase_sylow3_two_UConjugates_inside
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) :
    ∃ U1 U2 : Subgroup G,
      U1 ≠ U2 ∧ U1 ≤ (P : Subgroup G) ∧ U2 ≤ (P : Subgroup G) ∧
        (∃ g : G, U1 = conjugateSubgroup c.U g) ∧
        (∃ g : G, U2 = conjugateSubgroup c.U g) := by
  classical
  have hIn : Nat.card {V : UConjugates c // V.1 ≤ (P : Subgroup G)} = 2 :=
    firstCase_sylow3_inside_card_eq_two hmin c hfirst d P
  let α := {V : UConjugates c // V.1 ≤ (P : Subgroup G)}
  have hpair : ∃ a b : α, a ≠ b := by
    have hgt : 1 < Nat.card α := by
      change 1 < Nat.card {V : UConjugates c // V.1 ≤ (P : Subgroup G)}
      rw [hIn]
      norm_num
    have hnt : Nontrivial α := (Finite.one_lt_card_iff_nontrivial).mp hgt
    exact exists_pair_ne α
  rcases hpair with ⟨V1, V2, hVne⟩
  refine ⟨V1.1.1, V2.1.1, ?_, V1.2, V2.2, V1.1.2, V2.1.2⟩
  intro h
  apply hVne
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- In the first case every Sylow 3-subgroup contains exactly two conjugates
of `U`.  Public wrapper over plain subgroup statements: the two subgroups
`U₁, U₂` are the unique conjugates of `U` inside `P`. -/
public theorem firstCase_sylow3_UConjugates_inside_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) :
    ∃ U1 U2 : Subgroup G,
      U1 ≠ U2 ∧ U1 ≤ (P : Subgroup G) ∧ U2 ≤ (P : Subgroup G) ∧
        (∃ g : G, U1 = conjugateSubgroup c.U g) ∧
        (∃ g : G, U2 = conjugateSubgroup c.U g) ∧
        ∀ V : Subgroup G, (∃ g : G, V = conjugateSubgroup c.U g) →
          V ≤ (P : Subgroup G) → V = U1 ∨ V = U2 := by
  classical
  have hIn : Nat.card {V : UConjugates c // V.1 ≤ (P : Subgroup G)} = 2 :=
    firstCase_sylow3_inside_card_eq_two hmin c hfirst d P
  let α := {V : UConjugates c // V.1 ≤ (P : Subgroup G)}
  rcases (Nat.card_eq_two_iff.mp (by simpa [α] using hIn)) with ⟨x, y, hxy, huniv⟩
  refine ⟨x.1.1, y.1.1, ?_, x.2, y.2, x.1.2, y.1.2, ?_⟩
  · intro h
    apply hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro V hVconj hVle
    let v : α := ⟨⟨V, hVconj⟩, hVle⟩
    have hv_univ : v ∈ ({x, y} : Set α) := by
      rw [huniv]
      trivial
    rcases hv_univ with hvx | hvy
    · left
      simpa [v] using (congrArg (fun z : α => z.1.1) hvx)
    · right
      simpa [v] using (congrArg (fun z : α => z.1.1) hvy)

private lemma le_conjSubgroup_iff {G : Type u} [Group G]
    (A : Subgroup G) (g : G) (B : Subgroup G) :
    conjugateSubgroup A g ≤ B ↔ A ≤ conjugateSubgroup B g⁻¹ := by
  constructor
  · intro h a ha
    refine ⟨g * a * g⁻¹, ?_, ?_⟩
    · exact h (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    · change (MulAut.conj g⁻¹) (g * a * g⁻¹) = a
      rw [MulAut.conj_apply]
      group
  · intro h a ha
    rcases ha with ⟨u, hu, rfl⟩
    rcases h hu with ⟨b, hb, hba⟩
    have hb' : g * u * g⁻¹ = b := by
      calc
        g * u * g⁻¹ = g * (g⁻¹ * b * g) * g⁻¹ := by
          congr 1
          have hba' : g⁻¹ * b * g = u := by simpa [MulAut.conj_apply] using hba
          exact congrArg (fun x : G => g * x) hba'.symm
        _ = b := by group
    simpa [hb'] using hb

private lemma firstCase_normalizer_U_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Nat.card (Subgroup.normalizer (c.U : Set G)) = 72 := by
  classical
  have hklein : IsKleinFour (pCore 2 c.Hhat) := firstCase_twoCore_isKleinFour hmin c hfirst
  have hVK : IsKleinFour (twoCoreOf c.Hhat) := firstCase_klein_V_klein c hklein
  have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    have hfour : Nat.card (twoCoreOf c.Hhat) = 4 := hVK.card_four
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hO2 hUne
  rw [hNorm]
  rcases firstCase_index_card_of_countData c d with ⟨hHidx, hGcard⟩
  have hm := c.Hhat.index_mul_card
  rw [hHidx, hGcard] at hm
  omega

private lemma factorization_three_of_countData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    (Nat.card G).factorization 3 = 2 := by
  rcases firstCase_index_card_of_countData c d with ⟨_, hGcard⟩
  rw [hGcard]
  rw [show (2 ^ 3 * 3 ^ 2 * 5 * 7 : ℕ) = 3 ^ 2 * (2 ^ 3 * 5 * 7) by ring]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_three.factorization_self]
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (2 ^ 3 * 5 * 7 : ℕ))

/-- A Sylow 3-subgroup of the first-case group contains at most eight
conjugates of `U`-type subgroups of order three: each such `P` lies in
`N_G(V)` (so the fiber injects into the Sylow 3-subgroups of `N_G(V)`), and
`N_G(V)` has order 72, so it has at most `72 / 9 = 8` Sylow 3-subgroups. -/
private lemma sylow3_containing_card_le_eight
    {G : Type u} [Group G] [Finite G]
    {V : Subgroup G} (hV3 : Nat.card V = 3)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 72)
    (hP9 : ∀ P : Sylow 3 G, Nat.card P = 9) :
    Nat.card {P : Sylow 3 G // V ≤ (P : Subgroup G)} ≤ 8 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hVleN : V ≤ N := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv w hw
    exact V.mul_mem (V.mul_mem hv hw) (V.inv_mem hv)
  let f : {P : Sylow 3 G // V ≤ (P : Subgroup G)} → Sylow 3 (↥N) := fun P =>
    P.1.subtype (by
      exact (le_subgroup_iff_normalizer (hP9 P.1) hV3).mp P.2)
  have hf_inj : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    have hsub : (f P : Subgroup (↥N)) = (f Q : Subgroup (↥N)) :=
      congrArg (fun S : Sylow 3 (↥N) => (S : Subgroup (↥N))) h
    exact Sylow.subtype_injective (P := P.1) (Q := Q.1) (N := N)
      (Sylow.ext hsub)
  have hle1 : Nat.card {P : Sylow 3 G // V ≤ (P : Subgroup G)} ≤
      Nat.card (Sylow 3 (↥N)) :=
    Nat.card_le_card_of_injective f hf_inj
  have hNfac : (Nat.card (↥N)).factorization 3 = 2 := by
    rw [hNcard]
    rw [show (72 : ℕ) = 3 ^ 2 * 8 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [Nat.factorization_pow]
    simp [Nat.prime_three.factorization_self]
    exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (8 : ℕ))
  obtain ⟨Q⟩ := (Sylow.nonempty (p := 3) (G := ↥N))
  have hQcard : Nat.card Q = 9 := by
    rw [Q.card_eq_multiplicity, hNfac]
    norm_num
  have hQindex : Q.index = 8 := by
    have hm := Q.index_mul_card
    rw [hQcard, hNcard] at hm
    omega
  have hdvd : Nat.card (Sylow 3 (↥N)) ∣ 8 := by
    simpa [hQindex] using Q.card_dvd_index
  have hle2 : Nat.card (Sylow 3 (↥N)) ≤ 8 :=
    Nat.le_of_dvd (by norm_num) hdvd
  exact le_trans hle1 hle2

private lemma fiberV_card_eq_of_conjugate
    {G : Type u} [Group G] [Finite G]
    (hGfac : (Nat.card G).factorization 3 = 2)
    (hP9 : ∀ P : Sylow 3 G, Nat.card P = 9)
    (c : CentralizerSetup G) (g : G) :
    Nat.card {P : Sylow 3 G // conjugateSubgroup c.U g ≤ (P : Subgroup G)} =
      Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)} := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : {P : Sylow 3 G // conjugateSubgroup c.U g ≤ (P : Subgroup G)} ≃
      {P : Sylow 3 G // c.U ≤ (P : Subgroup G)} :=
    { toFun := fun P => ⟨Sylow.ofCard (conjugateSubgroup (P.1 : Subgroup G) g⁻¹) (by
          have hcardP : Nat.card (conjugateSubgroup (P.1 : Subgroup G) g⁻¹) = 9 := by
            have h := Subgroup.card_map_of_injective (K := (P.1 : Subgroup G))
              (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
            rw [conjugateSubgroup, h, hP9 P.1]
          rw [hcardP, hGfac]
          norm_num), by
        have hle : c.U ≤ conjugateSubgroup (P.1 : Subgroup G) g⁻¹ :=
          (le_conjSubgroup_iff c.U g (P.1 : Subgroup G)).mp P.2
        simpa [conjugateSubgroup] using hle⟩
      invFun := fun P => ⟨Sylow.ofCard (conjugateSubgroup (P.1 : Subgroup G) g) (by
          have hcardP : Nat.card (conjugateSubgroup (P.1 : Subgroup G) g) = 9 := by
            have h := Subgroup.card_map_of_injective (K := (P.1 : Subgroup G))
              (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
            rw [conjugateSubgroup, h, hP9 P.1]
          rw [hcardP, hGfac]
          norm_num), by
        have hle : conjugateSubgroup c.U g ≤ conjugateSubgroup (P.1 : Subgroup G) g := by
          intro x hx
          rcases hx with ⟨u, hu, rfl⟩
          refine ⟨u, P.2 hu, rfl⟩
        simpa [conjugateSubgroup] using hle⟩
      left_inv := by
        intro P
        apply Subtype.ext
        apply Sylow.ext
        simp only [Sylow.coe_ofCard]
        have h := UConjugates.conjugateSubgroup_mul (P.1 : Subgroup G) g g⁻¹
        rw [h, mul_inv_cancel]
        exact UConjugates.conjugateSubgroup_one (P.1 : Subgroup G)
      right_inv := by
        intro P
        apply Subtype.ext
        apply Sylow.ext
        simp only [Sylow.coe_ofCard]
        have h := UConjugates.conjugateSubgroup_mul (P.1 : Subgroup G) g⁻¹ g
        rw [h, inv_mul_cancel]
        exact UConjugates.conjugateSubgroup_one (P.1 : Subgroup G) }
  exact Nat.card_congr e

private lemma sylow3_count
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Nat.card (Sylow 3 G) = 70 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype (Sylow 3 G) := Fintype.ofFinite _
  let : Fintype (UConjugates c) := Fintype.ofFinite _
  let n3 := Nat.card (Sylow 3 G)
  let fiberP : Sylow 3 G → Type u := fun P => {V : UConjugates c // V.1 ≤ (P : Subgroup G)}
  let fiberV : UConjugates c → Type u := fun V => {P : Sylow 3 G // V.1 ≤ (P : Subgroup G)}
  let PairsP : Type u := {p : (Sylow 3 G) × UConjugates c // p.2.1 ≤ (p.1 : Subgroup G)}
  let PairsV : Type u := {p : UConjugates c × (Sylow 3 G) // p.1.1 ≤ (p.2 : Subgroup G)}
  have hfib2 : ∀ P : Sylow 3 G, Nat.card (fiberP P) = 2 := by
    intro P
    simpa [fiberP] using firstCase_sylow3_inside_card_eq_two hmin c hfirst d P
  have hP9 : ∀ P : Sylow 3 G, Nat.card P = 9 := firstCase_sylow3_card_nine c d
  have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
  have hGfac : (Nat.card G).factorization 3 = 2 := factorization_three_of_countData c d
  have hNcard : Nat.card (Subgroup.normalizer (c.U : Set G)) = 72 :=
    firstCase_normalizer_U_card hmin c hfirst d
  have hUcard : Nat.card (UConjugates c) = 35 := firstCase_UConjugates_card hmin c hfirst d
  let k : ℕ := Nat.card (fiberV (UConjugates.base c))
  have hfibV_const : ∀ V : UConjugates c, Nat.card (fiberV V) = k := by
    intro V
    rcases V with ⟨W, hW⟩
    rcases hW with ⟨g, rfl⟩
    have hcard := fiberV_card_eq_of_conjugate hGfac hP9 c g
    change Nat.card {P : Sylow 3 G // conjugateSubgroup c.U g ≤ (P : Subgroup G)} =
      Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)}
    exact hcard
  have hk_le : k ≤ 8 := by
    have hle := sylow3_containing_card_le_eight hU3 hNcard hP9
    change Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)} ≤ 8
    exact hle
  have hk_ne : k ≠ 0 := by
    have hUp : IsPGroup 3 c.U := by
      refine IsPGroup.of_card (n := 1) ?_
      simpa using hU3
    rcases IsPGroup.exists_le_sylow (p := 3) hUp with ⟨P, hPle⟩
    have hnon : Nonempty (fiberV (UConjugates.base c)) := ⟨⟨P, hPle⟩⟩
    have hpos : 0 < Nat.card (fiberV (UConjugates.base c)) := Finite.card_pos_iff.mpr hnon
    change Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)} ≠ 0
    exact hpos.ne'
  have hPairsP : Nat.card PairsP = 2 * n3 := by
    have e : PairsP ≃ (Σ P : Sylow 3 G, fiberP P) :=
      Equiv.subtypeProdEquivSigmaSubtype
        (fun (P : Sylow 3 G) (V : UConjugates c) => V.1 ≤ (P : Subgroup G))
    have hcard := Nat.card_congr e
    have hsum : Nat.card (Σ P : Sylow 3 G, fiberP P) = 2 * n3 := by
      rw [Nat.card_sigma]
      simp only [fiberP, hfib2, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card]
      simp [n3, mul_comm]
    simpa [PairsP] using hcard.trans hsum
  have hPairsV : Nat.card PairsV = 35 * k := by
    have e : PairsV ≃ (Σ V : UConjugates c, fiberV V) :=
      Equiv.subtypeProdEquivSigmaSubtype
        (fun (V : UConjugates c) (P : Sylow 3 G) => V.1 ≤ (P : Subgroup G))
    have hcard := Nat.card_congr e
    have hsum : Nat.card (Σ V : UConjugates c, fiberV V) = 35 * k := by
      rw [Nat.card_sigma]
      simp only [fiberV, hfibV_const, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, hUcard]
      simp [k]
    simpa [PairsV] using hcard.trans hsum
  have ePair : PairsP ≃ PairsV :=
    { toFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
      invFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        rfl
      right_inv := by
        intro p
        apply Subtype.ext
        rfl }
  have heq : 2 * n3 = 35 * k := by
    calc
      2 * n3 = Nat.card PairsP := hPairsP.symm
      _ = Nat.card PairsV := Nat.card_congr ePair
      _ = 35 * k := hPairsV
  have hmod : n3 % 3 = 1 := by
    have hm := (card_sylow_modEq_one 3 G : Nat.card (Sylow 3 G) ≡ 1 [MOD 3])
    change Nat.card (Sylow 3 G) % 3 = 1 % 3 at hm
    norm_num at hm
    simpa [n3] using hm
  have hk_even : 2 ∣ k := by
    have hdvd : 2 ∣ 35 * k := by
      rw [← heq]
      exact dvd_mul_right 2 n3
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h35 | hk
    · exfalso
      norm_num at h35
    · exact hk
  have hres : n3 = 70 := by
    obtain ⟨m, hm⟩ := hk_even
    have hm_le : m ≤ 4 := by omega
    interval_cases m <;> omega
  simpa [n3] using hres

/-- In the first case the number of Sylow 3-subgroups is 70. -/
public theorem firstCase_sylow3_count
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Nat.card (Sylow 3 G) = 70 := by
  exact sylow3_count hmin c hfirst d

/-- In the first case, each conjugate of `U` lies in exactly four Sylow
3-subgroups.  This is the fiber cardinal `k = 4` of the double count that
gave `n₃ = 70`: the pair count `35 · k = 2 · 70`, the bound `k ≤ 8`, and
`k ≠ 0` force `k = 4`. -/
public theorem firstCase_UConjugates_fiber_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (g : G) :
    Nat.card {P : Sylow 3 G // conjugateSubgroup c.U g ≤ (P : Subgroup G)} = 4 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype (Sylow 3 G) := Fintype.ofFinite _
  let : Fintype (UConjugates c) := Fintype.ofFinite _
  let fiberV : UConjugates c → Type u := fun V => {P : Sylow 3 G // V.1 ≤ (P : Subgroup G)}
  let PairsV : Type u := {p : UConjugates c × (Sylow 3 G) // p.1.1 ≤ (p.2 : Subgroup G)}
  let PairsP : Type u := {p : (Sylow 3 G) × UConjugates c // p.2.1 ≤ (p.1 : Subgroup G)}
  have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
  have hP9 : ∀ P : Sylow 3 G, Nat.card P = 9 := firstCase_sylow3_card_nine c d
  have hGfac : (Nat.card G).factorization 3 = 2 := factorization_three_of_countData c d
  have hNcard : Nat.card (Subgroup.normalizer (c.U : Set G)) = 72 :=
    firstCase_normalizer_U_card hmin c hfirst d
  have hUcard : Nat.card (UConjugates c) = 35 := firstCase_UConjugates_card hmin c hfirst d
  let k : ℕ := Nat.card (fiberV (UConjugates.base c))
  have hfibV_const : ∀ V : UConjugates c, Nat.card (fiberV V) = k := by
    intro V
    rcases V with ⟨W, hW⟩
    rcases hW with ⟨g, rfl⟩
    have hcard := fiberV_card_eq_of_conjugate hGfac hP9 c g
    change Nat.card {P : Sylow 3 G // conjugateSubgroup c.U g ≤ (P : Subgroup G)} = k
    exact hcard.trans (by
      change k = Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)}
      rfl)
  have hk_le : k ≤ 8 := by
    change Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)} ≤ 8
    exact sylow3_containing_card_le_eight hU3 hNcard hP9
  have hk_ne : k ≠ 0 := by
    have hUp : IsPGroup 3 c.U := by
      refine IsPGroup.of_card (n := 1) ?_
      simpa using hU3
    rcases IsPGroup.exists_le_sylow (p := 3) hUp with ⟨P, hPle⟩
    have hnon : Nonempty (fiberV (UConjugates.base c)) := ⟨⟨P, hPle⟩⟩
    change Nat.card {P : Sylow 3 G // c.U ≤ (P : Subgroup G)} ≠ 0
    exact (Finite.card_pos_iff.mpr hnon).ne'
  have hPairsV : Nat.card PairsV = 35 * k := by
    have e : PairsV ≃ (Σ V : UConjugates c, fiberV V) :=
      Equiv.subtypeProdEquivSigmaSubtype
        (fun (V : UConjugates c) (P : Sylow 3 G) => V.1 ≤ (P : Subgroup G))
    have hcard := Nat.card_congr e
    have hsum : Nat.card (Σ V : UConjugates c, fiberV V) = 35 * k := by
      rw [Nat.card_sigma]
      simp only [fiberV, hfibV_const, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, hUcard]
      simp [k]
    simpa [PairsV] using hcard.trans hsum
  have hPairsP : Nat.card PairsP = 2 * 70 := by
    have e : PairsP ≃ (Σ P : Sylow 3 G, {V : UConjugates c // V.1 ≤ (P : Subgroup G)}) :=
      Equiv.subtypeProdEquivSigmaSubtype
        (fun (P : Sylow 3 G) (V : UConjugates c) => V.1 ≤ (P : Subgroup G))
    have hcard := Nat.card_congr e
    have hsum : Nat.card (Σ P : Sylow 3 G, {V : UConjugates c // V.1 ≤ (P : Subgroup G)}) =
        2 * 70 := by
      rw [Nat.card_sigma]
      simp only [firstCase_sylow3_inside_card_eq_two hmin c hfirst d,
        Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, firstCase_sylow3_count hmin c hfirst d]
      norm_num [mul_comm]
    simpa [PairsP] using hcard.trans hsum
  have heq : 35 * k = 2 * 70 := by
    calc
      35 * k = Nat.card PairsV := hPairsV.symm
      _ = Nat.card PairsP := by
        apply Nat.card_congr
        exact {
          toFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
          invFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
          left_inv := by
            intro p
            apply Subtype.ext
            rfl
          right_inv := by
            intro p
            apply Subtype.ext
            rfl }
      _ = 2 * 70 := hPairsP
  have hk_even : 2 ∣ k := by
    have hdvd : 2 ∣ 35 * k := by
      rw [heq]
      exact dvd_mul_right 2 70
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h35 | hk
    · exfalso
      norm_num at h35
    · exact hk
  have hk4 : k = 4 := by
    rcases hk_even with ⟨m, hm⟩
    have hEq' : 35 * (2 * m) = 140 := by
      simpa [hm] using heq
    omega
  have hcard := fiberV_card_eq_of_conjugate hGfac hP9 c g
  change Nat.card {P : Sylow 3 G // conjugateSubgroup c.U g ≤ (P : Subgroup G)} = k at hcard
  exact hcard.trans hk4

end CFSG.GorensteinWalter
