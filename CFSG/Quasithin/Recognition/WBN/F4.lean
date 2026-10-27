module

public import CFSG.Quasithin.Recognition.WBN.Weyl
public import CFSG.LieType.Ree.LocalBlockSylowAction

import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Yam
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.LieType.Ree.LargeReeSylowOpposition

public section

namespace CFSG.Quasithin.WBN

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.ReeF4
  CFSG.QuasithinUnique

open scoped Pointwise

private noncomputable def f4WeylRep (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (a : ℕ)
    (j : Fin ReeTag.F4.fixedOrbitCount) : ↥(ReeTag.F4.reeGamma K a) :=
  ⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K (ReeTag.F4.fixedOrbitElement j),
    (canonicalRep_mem_reeFixedMonomial ReeTag.F4 K a
      (ReeTag.F4.fixedOrbitElement_mem j)).2⟩

private lemma f4_parabolic_inf
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((ReeTag.F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (ReeTag.F4.reeGamma K a)) ⊓
        ((ReeTag.F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf
          (ReeTag.F4.reeGamma K a)) =
      (ReeTag.F4.reeFixedBorel K a).subgroupOf (ReeTag.F4.reeGamma K a) := by
  let Γ := ReeTag.F4.reeGamma K a
  let P₀ := (ReeTag.F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf Γ
  let P₁ := (ReeTag.F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf Γ
  obtain ⟨-, hcov, -, hn₁, hsup, -, -⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK
  change P₀ ⊓ P₁ = (ReeTag.F4.reeFixedBorel K a).subgroupOf Γ
  have hsup' : P₀ ⊔ P₁ = ⊤ := hsup
  have hne : P₀ ≠ P₁ := by
    intro h
    rw [h, sup_idem] at hsup'
    exact hn₁ hsup'
  exact (inf_eq_of_covers ((hcov P₀).2 (Or.inl rfl)) ((hcov P₁).2 (Or.inr rfl)) hne).trans
    (normalizer_reeFixedPosUnipotent_subgroupOf (K := K) (a := a))

private lemma f4_sup_eq_borel
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ} :
    (ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf (ReeTag.F4.reeGamma K a) ⊔
        (ReeTag.F4.reeFixedTorus K a).subgroupOf (ReeTag.F4.reeGamma K a) =
      (ReeTag.F4.reeFixedBorel K a).subgroupOf (ReeTag.F4.reeGamma K a) := by
  let Γ := ReeTag.F4.reeGamma K a
  have hU₀Γ : (ReeTag.F4.reeFixedPosUnipotent K a) ≤ Γ :=
    reeFixedPosUnipotent_le_reeGamma
  have hH₀Γ : (ReeTag.F4.reeFixedTorus K a) ≤ Γ :=
    reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma
  change (ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf Γ ⊔
      (ReeTag.F4.reeFixedTorus K a).subgroupOf Γ =
    (ReeTag.F4.reeFixedBorel K a).subgroupOf Γ
  rw [← Subgroup.subgroupOf_sup hU₀Γ hH₀Γ]
  rw [show (ReeTag.F4.reeFixedPosUnipotent K a) ⊔ (ReeTag.F4.reeFixedTorus K a) =
      ReeTag.F4.reeFixedBorel K a by rw [sup_comm, ← ReeTag.reeFixedBorel_eq_sup]]

private lemma f4_unipotent_normal
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    {P₀ P₁ : Subgroup ↥(ReeTag.F4.reeGamma K a)}
    (hB : P₀ ⊓ P₁ = (ReeTag.F4.reeFixedBorel K a).subgroupOf (ReeTag.F4.reeGamma K a)) :
    (((ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf (ReeTag.F4.reeGamma K a)).subgroupOf
      (P₀ ⊓ P₁)).Normal := by
  let Γ := ReeTag.F4.reeGamma K a
  let B₀ := ReeTag.F4.reeFixedBorel K a
  change (((ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf Γ).subgroupOf (P₀ ⊓ P₁)).Normal
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
  have hNB : B₀ ≤ Subgroup.normalizer ((ReeTag.F4.reeFixedPosUnipotent K a) :
      Set (ModGL ReeTag.F4.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer reeFixedPosUnipotent_le_reeFixedBorel).mp
      reeFixedPosUnipotent_subgroupOf_normal
  have hgB : ((g : ↥Γ) : ModGL ReeTag.F4.tag K) ∈ B₀ :=
    Subgroup.mem_subgroupOf.mp (hB ▸ g.2)
  exact (Subgroup.mem_normalizer_iff.mp (hNB hgB)
    ((n : ↥Γ) : ModGL ReeTag.F4.tag K)).mp hn

private lemma f4_cartan_odd
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Odd (Nat.card ((ReeTag.F4.reeFixedTorus K a).subgroupOf (ReeTag.F4.reeGamma K a))) := by
  let Γ := ReeTag.F4.reeGamma K a
  let H₀ := ReeTag.F4.reeFixedTorus K a
  have hH₀Γ : H₀ ≤ Γ := reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma
  have hoddT : Odd (Nat.card H₀) := by
    refine (?_ : Odd (Nat.card (torusGroup ReeTag.F4.tag K))).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_left : H₀ ≤ torusGroup ReeTag.F4.tag K))
    rw [show Nat.card (torusGroup ReeTag.F4.tag K) = (Nat.card K - 1) ^ 4 from
      CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_F4 (K := K), hK]
    exact (Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Nat.even_pow.2 ⟨even_two, (by positivity : 0 < 2 * a + 1).ne'⟩) odd_one).pow
  rw [show Nat.card ((ReeTag.F4.reeFixedTorus K a).subgroupOf (ReeTag.F4.reeGamma K a)) =
      Nat.card H₀ from card_subgroupOf_reeGamma hH₀Γ]
  exact hoddT

private lemma f4_weyl_rep_mem_parabolic
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (j : Fin ReeTag.F4.fixedOrbitCount) :
    f4WeylRep K a j ∈
        ((ReeTag.F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf
          (ReeTag.F4.reeGamma K a)) ∨
      f4WeylRep K a j ∈
        ((ReeTag.F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf
          (ReeTag.F4.reeGamma K a)) := by
  let Γ := ReeTag.F4.reeGamma K a
  have hmem : (f4WeylRep K a j : ↥Γ) ∈ (ReeTag.F4.reeLocalParabolic K a j).subgroupOf Γ :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨(f4WeylRep K a j).2,
        canonicalRep_mem_parabolicSubgroup
          (ReeTag.F4.fixedOrbitElement_mem_fixedOrbitWeyl j)⟩)
  have hcases : ∀ j : Fin ReeTag.F4.fixedOrbitCount,
      j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by decide
  rcases hcases j with rfl | rfl
  · exact Or.inl hmem
  · exact Or.inr hmem

private lemma f4_monomial_normalizes_torus
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ} :
    (ReeTag.F4.reeFixedMonomial K a).subgroupOf (ReeTag.F4.reeGamma K a) ≤
      Subgroup.normalizer ((ReeTag.F4.reeFixedTorus K a).subgroupOf
        (ReeTag.F4.reeGamma K a) : Set ↥(ReeTag.F4.reeGamma K a)) := by
  let Γ := ReeTag.F4.reeGamma K a
  let H₀ := ReeTag.F4.reeFixedTorus K a
  change (ReeTag.F4.reeFixedMonomial K a).subgroupOf Γ ≤
    Subgroup.normalizer (H₀.subgroupOf Γ : Set ↥Γ)
  have hH₀Γ : H₀ ≤ Γ := reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma
  rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer Γ H₀ hH₀Γ]
  apply Subgroup.subgroupOf_mono
  intro x hx
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2,
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (reeFixedTorus_le_reeFixedMonomial ReeTag.F4 K a)).mp
      (reeFixedTorus_subgroupOf_normal ReeTag.F4 K a) hx⟩

private lemma f4_longest_mem_closure
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    {w₀ : WeylGroup ReeTag.F4.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.F4.tag).length w ≤
      (coxeterSystem ReeTag.F4.tag).length w₀) :
    (⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
        (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩ :
          ↥(ReeTag.F4.reeGamma K a)) ∈
      (ReeTag.F4.reeFixedTorus K a).subgroupOf (ReeTag.F4.reeGamma K a) ⊔
        Subgroup.closure (Set.range (f4WeylRep K a)) := by
  let Γ := ReeTag.F4.reeGamma K a
  let H := (ReeTag.F4.reeFixedTorus K a).subgroupOf Γ
  let C : Subgroup (ModGL ReeTag.F4.tag K) := Subgroup.closure
    (Set.range fun j => canonicalRep (coxeterSystem ReeTag.F4.tag) K
      (ReeTag.F4.fixedOrbitElement j))
  have hH₀Γ : (ReeTag.F4.reeFixedTorus K a) ≤ Γ :=
    reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_reeGamma
  have hCΓ : C ≤ Γ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    exact (canonicalRep_mem_reeFixedMonomial ReeTag.F4 K a
      (ReeTag.F4.fixedOrbitElement_mem j)).2
  have hCsub : C.subgroupOf Γ = Subgroup.closure (Set.range (f4WeylRep K a)) := by
    apply Subgroup.map_injective (f := Γ.subtype) Γ.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCΓ, MonoidHom.map_closure]
    change Subgroup.closure (Set.range fun j => canonicalRep (coxeterSystem ReeTag.F4.tag) K
      (ReeTag.F4.fixedOrbitElement j)) = Subgroup.closure (Γ.subtype '' Set.range (f4WeylRep K a))
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨f4WeylRep K a j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  have hNsup : (ReeTag.F4.reeFixedMonomial K a).subgroupOf Γ =
      H ⊔ Subgroup.closure (Set.range (f4WeylRep K a)) := by
    rw [reeFixedMonomial_eq_sup ReeTag.F4 K a, Subgroup.subgroupOf_sup hH₀Γ hCΓ, hCsub]
  have hwN : (⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
      (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩ : ↥Γ) ∈
      (ReeTag.F4.reeFixedMonomial K a).subgroupOf Γ :=
    Subgroup.mem_subgroupOf.mpr
      (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀)
  change (⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
      (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩ : ↥Γ) ∈
    H ⊔ Subgroup.closure (Set.range (f4WeylRep K a))
  exact hNsup ▸ hwN

private lemma f4_longest_inverts_torus
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    {w₀ : WeylGroup ReeTag.F4.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.F4.tag).length w ≤
      (coxeterSystem ReeTag.F4.tag).length w₀)
    {x : ↥(ReeTag.F4.reeGamma K a)}
    (hx : x ∈ (ReeTag.F4.reeFixedTorus K a).subgroupOf (ReeTag.F4.reeGamma K a)) :
    (⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
        (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩ :
          ↥(ReeTag.F4.reeGamma K a)) * x *
        (⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
          (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩ :
            ↥(ReeTag.F4.reeGamma K a))⁻¹ = x⁻¹ := by
  let Γ := ReeTag.F4.reeGamma K a
  let w : ↥Γ := ⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
    (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩
  change w * x * w⁻¹ = x⁻¹
  apply Subtype.ext
  have hxT : ((x : ↥Γ) : ModGL ReeTag.F4.tag K) ∈ torusGroup ReeTag.F4.tag K :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have h := canonicalRep_longest_conj_torus (t := ReeTag.F4) (K := K) hw₀ hxT
  simpa [w] using h

theorem invertsByWeyl_twistedF4
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) {m : ℕ} (hm : Odd m) :
    InvertsByWeyl
      ((ReeTag.F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (ReeTag.F4.reeGamma K a))
      ((ReeTag.F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (ReeTag.F4.reeGamma K a))
      m := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  let U₀ := ReeTag.F4.reeFixedPosUnipotent K a
  let H₀ := ReeTag.F4.reeFixedTorus K a
  let U := U₀.subgroupOf (ReeTag.F4.reeGamma K a)
  let H := H₀.subgroupOf (ReeTag.F4.reeGamma K a)
  let P₀ := (ReeTag.F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf
    (ReeTag.F4.reeGamma K a)
  let P₁ := (ReeTag.F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf
    (ReeTag.F4.reeGamma K a)
  obtain ⟨hsyl, -, -, -, -, -, -⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK
  have hU : IsPGroup 2 U := hsyl.2.1
  have hB : P₀ ⊓ P₁ = (ReeTag.F4.reeFixedBorel K a).subgroupOf (ReeTag.F4.reeGamma K a) :=
    f4_parabolic_inf hK
  have hUH : U ⊔ H = P₀ ⊓ P₁ := by
    rw [hB]
    exact f4_sup_eq_borel
  have hUn : (U.subgroupOf (P₀ ⊓ P₁)).Normal := f4_unipotent_normal hB
  have hH : Odd (Nat.card H) := f4_cartan_odd hK
  let nz : Fin ReeTag.F4.fixedOrbitCount → ↥(ReeTag.F4.reeGamma K a) := f4WeylRep K a
  let X : Set ↥(ReeTag.F4.reeGamma K a) := (H : Set _) ∪ Set.range nz
  have hHnorm : (ReeTag.F4.reeFixedMonomial K a).subgroupOf (ReeTag.F4.reeGamma K a) ≤
      Subgroup.normalizer (H : Set ↥(ReeTag.F4.reeGamma K a)) :=
    f4_monomial_normalizes_torus
  have hnzP : ∀ j, nz j ∈ P₀ ∨ nz j ∈ P₁ := fun j => f4_weyl_rep_mem_parabolic j
  have hnzN : ∀ j, nz j ∈ Subgroup.normalizer (H : Set ↥(ReeTag.F4.reeGamma K a)) := fun j =>
    hHnorm (Subgroup.mem_subgroupOf.mpr
      (canonicalRep_mem_reeFixedMonomial ReeTag.F4 K a
        (ReeTag.F4.fixedOrbitElement_mem j)))
  have hHle : H ≤ P₀ ⊓ P₁ := (le_sup_right : H ≤ U ⊔ H).trans hUH.le
  have hX : ∀ x ∈ X, (x ∈ P₀ ∨ x ∈ P₁) ∧
      x ∈ Subgroup.normalizer (H : Set ↥(ReeTag.F4.reeGamma K a)) := by
    intro x hx
    rcases hx with hxH | ⟨j, rfl⟩
    · exact ⟨Or.inl (Subgroup.mem_inf.mp (hHle hxH)).1, Subgroup.le_normalizer hxH⟩
    · exact ⟨hnzP j, hnzN j⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.F4.tag).length
  let w : ↥(ReeTag.F4.reeGamma K a) := ⟨canonicalRep (coxeterSystem ReeTag.F4.tag) K w₀,
    (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2⟩
  have hw : w ∈ Subgroup.closure X := by
    have hw' : w ∈ H ⊔ Subgroup.closure (Set.range nz) := f4_longest_mem_closure hw₀
    have hle : H ⊔ Subgroup.closure (Set.range nz) ≤ Subgroup.closure X := by
      refine sup_le ?_ ?_
      · exact fun x hx => Subgroup.subset_closure (Or.inl hx)
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨j, rfl⟩
        exact Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
    exact hle hw'
  have hinv : ∀ x ∈ H, x ^ m = 1 → w * x * w⁻¹ = x⁻¹ := by
    intro x hx _
    exact f4_longest_inverts_torus hw₀ hx
  exact InvertsByWeyl.of_torus_closure (Y := ↥(ReeTag.F4.reeGamma K a))
    (U := U) (H := H) (P₀ := P₀) (P₁ := P₁) hm hU hUn hUH hH hX hw hinv

theorem allInvertsByWeyl_twistedF4
    {a : ℕ} (ha : 1 ≤ a) {m : ℕ} (hm : Odd m) :
    AllInvertsByWeyl (CFSG.Quasithin.IsTwistedF4Over (2 * a + 1)) m := by
  intro Y _ hY T M₁ M₂ hYam
  rcases hY with ⟨h1, -⟩ | ⟨-, -, hLie⟩
  · omega
  · have hX :=
      (CFSG.LieType.Steinberg.CentralExt.GriessNative.reeTits_of_lieModel hLie (by decide)).2
    obtain ⟨a', K, hKF, hKFin, hKcp, ha', hfa, hK, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
    letI : Field K := hKF
    letI : Finite K := hKFin
    letI : CharP K ReeTag.F4.prime := hKcp
    have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hfa]
    haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
    exact InvertsByWeyl.of_yamStd (f4_yamStd ha' hK')
      (invertsByWeyl_twistedF4 hK' hm) e hYam

end CFSG.Quasithin.WBN
