module

public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizers
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.PartOne.K1214.PAct

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.LieType.Steinberg.Adjoint

section Group

variable {G : Type} [Group G]

theorem card_closure_pair {p : ℕ} (hp : p.Prime) {a b : G} (hab : Commute a b)
    (ha : orderOf a = p) (hb : orderOf b = p) (hind : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  have hcb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hca : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hcb]; exact hp⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases h with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hbb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) ∈
          (Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hbb).1
  let φ : Subgroup.zpowers a × Subgroup.zpowers b →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : G) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers b).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : G) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set G) := by
    have h1 : φ.range = (Subgroup.zpowers a).subtype.range ⊔ (Subgroup.zpowers b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype, Set.insert_eq,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hca, hcb,
    sq]

end Group

section Geometry

variable {τ : Tag} {K : Type} [Field K]

theorem levi_conj_mem_radical (J : Set (Fin τ.rank)) {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) {q : ModGL τ K} (hq : q ∈ parabolicRadical τ K J) :
    g * q * g⁻¹ ∈ parabolicRadical τ K J := by
  obtain ⟨hQP, hnorm, -, hMP, -⟩ := parabolic_root_radical_Levi_factors (τ := τ) (K := K) J
  have h := hnorm.conj_mem (⟨q, hQP hq⟩ : ↥(parabolicSubgroup τ K J))
    (Subgroup.mem_subgroupOf.2 hq) ⟨g, hMP hg⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem mem_normalizer_radicalIn (J : Set (Fin τ.rank)) {a : adjointGroup τ K}
    (ha : (a : ModGL τ K) ∈ parabolicLevi τ K J) :
    a ∈ Subgroup.normalizer ((parabolicRadicalIn τ K J : Subgroup (adjointGroup τ K)) :
      Set (adjointGroup τ K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_parabolicRadicalIn, mem_parabolicRadicalIn]
  constructor
  · intro hh
    have := levi_conj_mem_radical J ha hh
    simpa using this
  · intro hh
    have := levi_conj_mem_radical J (inv_mem ha) hh
    simpa [mul_assoc] using this

theorem entrywise_mem_radical (J : Set (Fin τ.rank)) (σ : K ≃+* K) {q : ModGL τ K}
    (hq : q ∈ parabolicRadical τ K J) :
    Units.map (entrywiseHom σ.toRingHom) q ∈ parabolicRadical τ K J := by
  have : (rootSpan τ K (parabolicRadicalRoots τ J)).map (Units.map (entrywiseHom σ.toRingHom)) =
      rootSpan τ K (parabolicRadicalRoots τ J) := by
    rw [rootSpan, Subgroup.map_iSup]
    refine iSup_congr fun α => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun _ => map_entrywise_rootSubgroup σ α
  have hq' : q ∈ rootSpan τ K (parabolicRadicalRoots τ J) := hq
  have h2 := Subgroup.mem_map_of_mem (Units.map (entrywiseHom σ.toRingHom)) hq'
  rw [this] at h2
  exact h2

end Geometry

section SL2

theorem card_SL2' {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

end SL2

end CFSG.RankThree.PartOne.TCX
