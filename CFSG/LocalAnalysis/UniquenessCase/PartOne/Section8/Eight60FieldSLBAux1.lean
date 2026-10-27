module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldMatrix
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
import CFSG.CGT.Stroth77.L4Sylow.Sylow
import CFSG.Adapters.StatedClassicalOrders
import CFSG.ClassicalInvolution.Asc77.AscSCH20

public section

open Matrix

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.Open (StatedSL)

open scoped MatrixGroups

private noncomputable def reindexGL {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (K : Type) [Field K] (e : m ≃ n) : GL m K →* GL n K :=
  Units.map (Matrix.reindexRingEquiv K e).toMonoidHom

private theorem coe_reindexGL {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {K : Type} [Field K] (e : m ≃ n) (A : GL m K) :
    ((reindexGL K e A : GL n K) : Matrix n n K) = Matrix.reindex e e (A : Matrix m m K) :=
  rfl

private theorem map_reindexGL {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {K : Type} [Field K] (e : m ≃ n) (φ : K →+* K)
    (A : GL m K) :
    Matrix.GeneralLinearGroup.map φ (reindexGL K e A) =
      reindexGL K e (Matrix.GeneralLinearGroup.map φ A) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [coe_reindexGL, Matrix.reindex_apply, Matrix.GeneralLinearGroup.map_apply]

private theorem map_blockDiagHom {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {K : Type} [Field K] (φ : K →+* K)
    (g : GL m K × GL n K) :
    Matrix.GeneralLinearGroup.map φ
        (blockDiagHom (MonoidHom.fst (GL m K) (GL n K))
          (MonoidHom.snd (GL m K) (GL n K)) g) =
      blockDiagHom (MonoidHom.fst (GL m K) (GL n K))
        (MonoidHom.snd (GL m K) (GL n K))
        (Matrix.GeneralLinearGroup.map φ g.1, Matrix.GeneralLinearGroup.map φ g.2) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [coe_blockDiagHom, Matrix.GeneralLinearGroup.map_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd]

private noncomputable def blockGL4 (K : Type) [Field K] :
    GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 4) K :=
  (reindexGL K (finSumFinEquiv (m := 2) (n := 2))).comp
    (blockDiagHom (MonoidHom.fst (GL (Fin 2) K) (GL (Fin 2) K))
      (MonoidHom.snd (GL (Fin 2) K) (GL (Fin 2) K)))

private theorem map_blockGL4 {K : Type} [Field K] (φ : K →+* K)
    (g : GL (Fin 2) K × GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map φ (blockGL4 K g) =
      blockGL4 K (Matrix.GeneralLinearGroup.map φ g.1, Matrix.GeneralLinearGroup.map φ g.2) := by
  rw [blockGL4, MonoidHom.comp_apply, MonoidHom.comp_apply, map_reindexGL, map_blockDiagHom]

private theorem det_blockGL4 {K : Type} [Field K] (g : GL (Fin 2) K × GL (Fin 2) K) :
    ((blockGL4 K g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      ((g.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        ((g.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
  have hcoe : (blockGL4 K g : Matrix (Fin 4) (Fin 4) K) =
      Matrix.reindex (finSumFinEquiv (m := 2) (n := 2))
        (finSumFinEquiv (m := 2) (n := 2))
        (Matrix.fromBlocks ((g.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
          ((g.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    rw [blockGL4, MonoidHom.comp_apply, coe_reindexGL, coe_blockDiagHom, MonoidHom.coe_fst,
      MonoidHom.coe_snd]
  rw [hcoe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

private theorem blockGL4_injective {K : Type} [Field K] :
    Function.Injective (blockGL4 K) := by
  intro g h hgh
  have h1 : (blockGL4 K g : Matrix (Fin 4) (Fin 4) K) =
      (blockGL4 K h : Matrix (Fin 4) (Fin 4) K) := by rw [hgh]
  simp only [blockGL4, MonoidHom.comp_apply, coe_reindexGL, coe_blockDiagHom,
    MonoidHom.coe_fst, MonoidHom.coe_snd] at h1
  have h2 := (Matrix.reindexRingEquiv K (finSumFinEquiv (m := 2) (n := 2))).injective h1
  obtain ⟨h11, -, -, h22⟩ := Matrix.fromBlocks_inj.mp h2
  exact Prod.ext (Units.ext h11) (Units.ext h22)

private theorem blockGL4_mem_statedSL {K : Type} [Field K]
    {g : GL (Fin 2) K × GL (Fin 2) K}
    (h1 : g.1 ∈ StatedSL 2 K) (h2 : g.2 ∈ StatedSL 2 K) :
    blockGL4 K g ∈ StatedSL 4 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  rw [det_blockGL4]
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at h1 h2
  rw [h1, h2, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedSL StatedProj StatedScalars)

private theorem exists_abelian_sylow_power_map_of_data {n : ℕ} {K : Type} [Field K] [Finite K]
    (φ : RingAut K) (T : Subgroup (StatedSL n K)) (s : ℕ)
    (hTcard : Nat.card T = 3 ^ (Nat.card (StatedSL n K)).factorization 3)
    (hTcomm : ∀ a b : T, a * b = b * a)
    (hs : s % 3 = 1)
    (hTmap : ∀ t : T, Matrix.GeneralLinearGroup.map (φ : K →+* K)
        (((t : StatedSL n K) : GL (Fin n) K)) =
        ((((t : StatedSL n K) : GL (Fin n) K)) ^ s)) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSL n K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSL n K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSL n K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSL n K)), IsFieldMapQuot (StatedSL n K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSL n K))), τ x = x ^ s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := StatedSL n K
  let N : Subgroup H := (StatedScalars (Fin n) K).subgroupOf H
  obtain ⟨Q, hQ⟩ := CFSG.CGT.Stroth77.L4Sylow.exists_sylow_quotient_eq_range (p := 3) N
    (Subgroup.subtype T) Subtype.coe_injective hTcard
  refine ⟨Q, s, ?_, hs, ?_⟩
  · intro x hx y hy
    rw [hQ] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    let g : T →* (StatedSL n K ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.subtype T)
    change g a * g b = g b * g a
    rw [← map_mul g a b, ← map_mul g b a, hTcomm a b]
  · intro τ hτ x hx
    rw [hQ] at hx
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨h, hh, hτh⟩ := hτ (T.subtype t)
    have hht : h = T.subtype t ^ s := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hh]
      simpa using hTmap t
    have key : τ ((QuotientGroup.mk' N) (T.subtype t)) = (QuotientGroup.mk' N) h := hτh
    rw [MonoidHom.comp_apply, key, hht, map_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedSL StatedProj StatedScalars)
open CFSG.ABGLocalTools (IsSylowOf)

private theorem exists_abelian_sylow_power_map_of_block {n : ℕ} {K : Type} [Field K] [Finite K]
    (φ : RingAut K) (C : Subgroup (GL (Fin 2) K)) (s : ℕ)
    (hCsyl : IsSylowOf 3 C (StatedSL 2 K)) (hCcyc : IsCyclic C) (hs : s % 3 = 1)
    (hCmap : ∀ g ∈ C, Matrix.GeneralLinearGroup.map (φ : K →+* K) g = g ^ s)
    (β : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin n) K) (hβinj : Function.Injective β)
    (hβmap : ∀ g : GL (Fin 2) K × GL (Fin 2) K,
      Matrix.GeneralLinearGroup.map (φ : K →+* K) (β g) =
        β (Matrix.GeneralLinearGroup.map (φ : K →+* K) g.1,
          Matrix.GeneralLinearGroup.map (φ : K →+* K) g.2))
    (hβdet : ∀ g : GL (Fin 2) K × GL (Fin 2) K, g.1 ∈ StatedSL 2 K → g.2 ∈ StatedSL 2 K →
      β g ∈ StatedSL n K)
    (hcard : (Nat.card (StatedSL n K)).factorization 3 ≤
      2 * (Nat.card (StatedSL 2 K)).factorization 3) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSL n K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSL n K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSL n K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSL n K)), IsFieldMapQuot (StatedSL n K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSL n K))), τ x = x ^ s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic C := hCcyc
  have hCle : C ≤ StatedSL 2 K := hCsyl.le
  set b := (Nat.card (StatedSL 2 K)).factorization 3 with hb
  have hCcard : Nat.card C = 3 ^ b := by
    rw [hb]
    exact hCsyl.card_eq
  let incl : C × C →* GL (Fin 2) K × GL (Fin 2) K :=
    MonoidHom.prodMap (Subgroup.subtype C) (Subgroup.subtype C)
  have hincl_inj : Function.Injective incl := by
    intro x y h
    have h1 : (incl x).1 = (incl y).1 := congrArg Prod.fst h
    have h2 : (incl x).2 = (incl y).2 := congrArg Prod.snd h
    simp only [incl, MonoidHom.coe_prodMap, Prod.map_fst, Prod.map_snd] at h1 h2
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  let βc : C × C →* StatedSL n K :=
    MonoidHom.codRestrict (β.comp incl) (StatedSL n K)
      (fun x => hβdet (incl x) (hCle x.1.2) (hCle x.2.2))
  have hcomp_inj : Function.Injective (β.comp incl) := fun x y h => hincl_inj (hβinj h)
  have hβc_inj : Function.Injective βc := by
    intro x y h
    apply hcomp_inj
    have h2 : (βc x : GL (Fin n) K) = (βc y : GL (Fin n) K) := congrArg Subtype.val h
    simpa [βc, MonoidHom.codRestrict] using h2
  let T : Subgroup (StatedSL n K) := βc.range
  have hTcard_prod : Nat.card T = Nat.card (C × C) := by
    have hmap : T = (⊤ : Subgroup (C × C)).map βc := (Subgroup.map_top βc).symm
    rw [hmap, Subgroup.card_map_of_injective hβc_inj]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have hTcardC : Nat.card T = 3 ^ (2 * b) := by
    rw [hTcard_prod, Nat.card_prod, hCcard, ← pow_add]
    ring_nf
  have hle : (Nat.card (StatedSL n K)).factorization 3 ≤ 2 * b := by
    rw [hb]
    exact hcard
  have hge : 2 * b ≤ (Nat.card (StatedSL n K)).factorization 3 := by
    have hdvd : 3 ^ (2 * b) ∣ Nat.card (StatedSL n K) := by
      rw [← hTcardC]
      exact T.card_subgroup_dvd_card
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos (α := StatedSL n K)).ne').mp hdvd
  have hTcard : Nat.card T = 3 ^ (Nat.card (StatedSL n K)).factorization 3 := by
    rw [hTcardC, le_antisymm hle hge]
  refine exists_abelian_sylow_power_map_of_data φ T s hTcard (fun a b => ?_) hs (fun t => ?_)
  · exact mul_comm' a b
  · obtain ⟨g, hg⟩ := t.2
    rw [← hg]
    change Matrix.GeneralLinearGroup.map (φ : K →+* K) (β (incl g)) = (β (incl g)) ^ s
    rw [hβmap (incl g)]
    have h1 : (incl g).1 = (g.1 : GL (Fin 2) K) := rfl
    have h2 : (incl g).2 = (g.2 : GL (Fin 2) K) := rfl
    rw [h1, h2, hCmap g.1 g.1.2, hCmap g.2 g.2.2,
      show incl g = ((g.1 : GL (Fin 2) K), (g.2 : GL (Fin 2) K)) from Prod.ext h1 h2,
      ← map_pow, ← Prod.pow_mk]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedSL)

private theorem card_statedSL_two_eq {K : Type} [Field K] [Finite K] :
    Nat.card (StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← Nat.card_congr
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv]
  exact CFSG.ClassicalInvolution.Asc77.SCH.card_sl2 K

private theorem card_factor_three_four {K : Type} [Field K] [Finite K]
    (hK3 : Nat.card K % 3 = 2) :
    (Nat.card (StatedSL 4 K)).factorization 3 ≤
      2 * (Nat.card (StatedSL 2 K)).factorization 3 := by
  rw [CFSG.ClassicalInvolution.Asc77.SCH.card_statedSL_four, card_statedSL_two_eq]
  exact CFSG.ClassicalInvolution.Asc77.SCH.factorization_sl4_le_two hK3 Finite.one_lt_card

private theorem card_factor_three_five {K : Type} [Field K] [Finite K]
    (hK3 : Nat.card K % 3 = 2) :
    (Nat.card (StatedSL 5 K)).factorization 3 ≤
      2 * (Nat.card (StatedSL 2 K)).factorization 3 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq3 : ¬ 3 ∣ Nat.card K := by omega
  have hq4 : ¬ 3 ∣ Nat.card K ^ 4 :=
    fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hq5 : ¬ 3 ∣ Nat.card K ^ 5 - 1 := by
    intro h
    have h1 : (Nat.card K ^ 5 - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    have h2 : Nat.card K ^ 5 % 3 = 2 := by
      rw [Nat.pow_mod, hK3]
    have h3 : 1 ≤ Nat.card K ^ 5 := Nat.one_le_pow _ _ (by omega)
    omega
  have hcard5 : Nat.card (StatedSL 5 K) =
      Nat.card K ^ 10 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) *
        (Nat.card K ^ 4 - 1) * (Nat.card K ^ 5 - 1)) := by
    rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 5) (by norm_num)]
    congr 1
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
    simp
  have hpow_ge : ∀ j : ℕ, 1 ≤ j → 2 ≤ Nat.card K ^ j := by
    intro j hj
    exact le_trans hq2 (le_self_pow (by omega : 1 ≤ Nat.card K) (by omega : j ≠ 0))
  have hA0 : Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) *
      (Nat.card K ^ 4 - 1) ≠ 0 := by
    have h2 : Nat.card K ^ 2 - 1 ≠ 0 := by have := hpow_ge 2 (by norm_num); omega
    have h3 : Nat.card K ^ 3 - 1 ≠ 0 := by have := hpow_ge 3 (by norm_num); omega
    have h4 : Nat.card K ^ 4 - 1 ≠ 0 := by have := hpow_ge 4 (by norm_num); omega
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) h2) h3) h4
  have hB0 : Nat.card K ^ 4 * (Nat.card K ^ 5 - 1) ≠ 0 := by
    have h5 : Nat.card K ^ 5 - 1 ≠ 0 := by have := hpow_ge 5 (by norm_num); omega
    exact mul_ne_zero (pow_ne_zero _ (by omega)) h5
  have hB : (Nat.card K ^ 4 * (Nat.card K ^ 5 - 1)).factorization 3 = 0 := by
    have h5 : Nat.card K ^ 5 - 1 ≠ 0 := by have := hpow_ge 5 (by norm_num); omega
    rw [Nat.factorization_mul (pow_ne_zero _ (by omega)) h5, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hq4,
      Nat.factorization_eq_zero_of_not_dvd hq5, add_zero]
  calc (Nat.card (StatedSL 5 K)).factorization 3
      = (Nat.card (StatedSL 4 K)).factorization 3 := by
        rw [hcard5, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSL_four]
        have hsplit : Nat.card K ^ 10 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) *
              (Nat.card K ^ 4 - 1) * (Nat.card K ^ 5 - 1)) =
            (Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) *
              (Nat.card K ^ 4 - 1)) * (Nat.card K ^ 4 * (Nat.card K ^ 5 - 1)) := by
          ring
        rw [hsplit, Nat.factorization_mul hA0 hB0, Finsupp.add_apply, hB, add_zero]
    _ ≤ 2 * (Nat.card (StatedSL 2 K)).factorization 3 := card_factor_three_four hK3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open CFSG.Open (StatedSL)

open scoped MatrixGroups

private theorem map_blockDiagHom_comp {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {K : Type} [Field K] (φ : K →+* K)
    {G : Type*} [Group G] (α : G →* GL m K) (β : G →* GL n K) (g : G) :
    Matrix.GeneralLinearGroup.map φ (blockDiagHom α β g) =
      blockDiagHom ((Matrix.GeneralLinearGroup.map φ).comp α)
        ((Matrix.GeneralLinearGroup.map φ).comp β) g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [coe_blockDiagHom, Matrix.GeneralLinearGroup.map_apply]

private noncomputable def blockGL5 (K : Type) [Field K] :
    GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 5) K :=
  (reindexGL K (finSumFinEquiv (m := 4) (n := 1))).comp
    (blockDiagHom (blockGL4 K)
      (1 : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 1) K))

private theorem map_blockGL5 {K : Type} [Field K] (φ : K →+* K)
    (g : GL (Fin 2) K × GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map φ (blockGL5 K g) =
      blockGL5 K (Matrix.GeneralLinearGroup.map φ g.1, Matrix.GeneralLinearGroup.map φ g.2) := by
  have hcomp : (Matrix.GeneralLinearGroup.map φ).comp (blockGL4 K) =
      (blockGL4 K).comp (MonoidHom.prodMap (Matrix.GeneralLinearGroup.map φ)
        (Matrix.GeneralLinearGroup.map φ)) :=
    MonoidHom.ext (fun g => map_blockGL4 φ g)
  have hone : (Matrix.GeneralLinearGroup.map φ).comp
      (1 : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 1) K) =
      (1 : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 1) K).comp
        (MonoidHom.prodMap (Matrix.GeneralLinearGroup.map φ)
          (Matrix.GeneralLinearGroup.map φ)) := by
    ext g
    simp
  rw [blockGL5, MonoidHom.comp_apply, MonoidHom.comp_apply, map_reindexGL,
    map_blockDiagHom_comp, hcomp, hone]
  rfl

private theorem det_blockGL5 {K : Type} [Field K] (g : GL (Fin 2) K × GL (Fin 2) K) :
    ((blockGL5 K g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det =
      ((g.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        ((g.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
  have hcoe : (blockGL5 K g : Matrix (Fin 5) (Fin 5) K) =
      Matrix.reindex (finSumFinEquiv (m := 4) (n := 1))
        (finSumFinEquiv (m := 4) (n := 1))
        (Matrix.fromBlocks ((blockGL4 K g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0
          (1 : Matrix (Fin 1) (Fin 1) K)) := by
    simp only [blockGL5, MonoidHom.comp_apply, coe_reindexGL, coe_blockDiagHom,
      MonoidHom.one_apply, Units.val_one]
  rw [hcoe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    det_blockGL4]

private theorem blockGL5_injective {K : Type} [Field K] :
    Function.Injective (blockGL5 K) := by
  intro g h hgh
  have h1 : (blockGL5 K g : Matrix (Fin 5) (Fin 5) K) =
      (blockGL5 K h : Matrix (Fin 5) (Fin 5) K) := by rw [hgh]
  simp only [blockGL5, MonoidHom.comp_apply, coe_reindexGL, coe_blockDiagHom,
    MonoidHom.one_apply] at h1
  have h2 := (Matrix.reindexRingEquiv K (finSumFinEquiv (m := 4) (n := 1))).injective h1
  obtain ⟨h11, -, -, -⟩ := Matrix.fromBlocks_inj.mp h2
  exact blockGL4_injective (Units.ext h11)

private theorem blockGL5_mem_statedSL {K : Type} [Field K]
    {g : GL (Fin 2) K × GL (Fin 2) K}
    (h1 : g.1 ∈ StatedSL 2 K) (h2 : g.2 ∈ StatedSL 2 K) :
    blockGL5 K g ∈ StatedSL 5 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  rw [det_blockGL5]
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at h1 h2
  rw [h1, h2, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedSL StatedProj StatedScalars)
open CFSG.ABGLocalTools (IsSylowOf)

theorem exists_abelian_sylow_power_map_statedSL_four {p f : ℕ}
    (hq : p ^ f % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (C : Subgroup (GL (Fin 2) K)) (s : ℕ)
    (hCsyl : IsSylowOf 3 C (StatedSL 2 K)) (hCcyc : IsCyclic C) (hs : s % 3 = 1)
    (hCmap : ∀ g ∈ C, Matrix.GeneralLinearGroup.map (φ : K →+* K) g = g ^ s) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSL 4 K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSL 4 K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSL 4 K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSL 4 K)), IsFieldMapQuot (StatedSL 4 K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSL 4 K))), τ x = x ^ s := by
  have hK3 : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  exact exists_abelian_sylow_power_map_of_block φ C s hCsyl hCcyc hs hCmap (blockGL4 K)
    blockGL4_injective (map_blockGL4 (φ : K →+* K)) (fun g h1 h2 => blockGL4_mem_statedSL h1 h2)
    (card_factor_three_four hK3)

theorem exists_abelian_sylow_power_map_statedSL_five {p f : ℕ}
    (hq : p ^ f % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (φ : RingAut K)
    (C : Subgroup (GL (Fin 2) K)) (s : ℕ)
    (hCsyl : IsSylowOf 3 C (StatedSL 2 K)) (hCcyc : IsCyclic C) (hs : s % 3 = 1)
    (hCmap : ∀ g ∈ C, Matrix.GeneralLinearGroup.map (φ : K →+* K) g = g ^ s) :
    ∃ (Q : Sylow 3 (StatedProj (StatedSL 5 K))) (s : ℕ),
      (∀ x ∈ (Q : Subgroup (StatedProj (StatedSL 5 K))),
        ∀ y ∈ (Q : Subgroup (StatedProj (StatedSL 5 K))), x * y = y * x) ∧
      s % 3 = 1 ∧
      ∀ τ : MulAut (StatedProj (StatedSL 5 K)), IsFieldMapQuot (StatedSL 5 K) φ τ →
        ∀ x ∈ (Q : Subgroup (StatedProj (StatedSL 5 K))), τ x = x ^ s := by
  have hK3 : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  exact exists_abelian_sylow_power_map_of_block φ C s hCsyl hCcyc hs hCmap (blockGL5 K)
    blockGL5_injective (map_blockGL5 (φ : K →+* K)) (fun g h1 h2 => blockGL5_mem_statedSL h1 h2)
    (card_factor_three_five hK3)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

