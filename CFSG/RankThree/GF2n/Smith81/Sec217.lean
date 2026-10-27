module

public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def commComponent (z : G) : Set G :=
  {y | Relation.ReflTransGen (CommOn (conjClassSet z)) z y}

section Component

theorem mem_commComponent_self {z : G} : z ∈ commComponent z := Relation.ReflTransGen.refl

theorem reflTransGen_commOn_symm {D : Set G} {a b : G}
    (h : Relation.ReflTransGen (CommOn D) a b) : Relation.ReflTransGen (CommOn D) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (commOn_symm hbc) ih

theorem reflTransGen_commOn_conj {z a b : G} (g : G)
    (h : Relation.ReflTransGen (CommOn (conjClassSet z)) a b) :
    Relation.ReflTransGen (CommOn (conjClassSet z)) (g * a * g⁻¹) (g * b * g⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine Relation.ReflTransGen.tail ih ?_
    obtain ⟨hb, hc, hcomm⟩ := hbc
    refine ⟨conjClassSet_conj hb g, conjClassSet_conj hc g, ?_⟩
    show (g * b * g⁻¹) * (g * c * g⁻¹) = (g * c * g⁻¹) * (g * b * g⁻¹)
    calc (g * b * g⁻¹) * (g * c * g⁻¹) = g * (b * c) * g⁻¹ := by group
      _ = g * (c * b) * g⁻¹ := by rw [hcomm.eq]
      _ = (g * c * g⁻¹) * (g * b * g⁻¹) := by group

theorem mem_normalizer_commComponent {z : G} (hzz : z * z = 1) :
    z ∈ Subgroup.normalizer (commComponent z) := by
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hfix : z * z * z⁻¹ = z := by rw [hinv, hzz, one_mul]
  show ∀ n, n ∈ commComponent z ↔ z * n * z⁻¹ ∈ commComponent z
  intro n
  constructor
  · intro hn
    have := reflTransGen_commOn_conj (z := z) z hn
    rwa [hfix] at this
  · intro hn
    have := reflTransGen_commOn_conj (z := z) z hn
    have e : z * (z * n * z⁻¹) * z⁻¹ = n := by
      rw [hinv]
      calc z * (z * n * z) * z = (z * z) * n * (z * z) := by group
        _ = n := by rw [hzz]; simp
    rw [e, hfix] at this
    exact this

end Component

@[expose] def Smith217UniqueBlockStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ¬ (conjClassSet z ⊆ commComponent z) →
      ∀ g : G, g⁻¹ * z * g ∈ Subgroup.normalizer (commComponent z) →
        g ∈ Subgroup.normalizer (commComponent z)

@[expose] def Smith217ExcludeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B →
      ¬ ((∃ M' : Subgroup (FStar G), CFSG.IsStronglyEmbedded M') ∨
        ∃ n : ℕ, Odd n ∧ Nonempty (FStar G ≃* alternatingGroup (Fin n)))

section Reduction

variable [Finite G] {M Q Z : Subgroup G}

theorem subset_commComponent_iff (z : G) :
    conjClassSet z ⊆ commComponent z ↔ ∀ x ∈ conjClassSet z, ∀ y ∈ conjClassSet z,
      Relation.ReflTransGen (CommOn (conjClassSet z)) x y := by
  constructor
  · intro h x hx y hy
    exact (reflTransGen_commOn_symm (h hx)).trans (h hy)
  · intro h y hy
    exact h z (IsConj.refl z) y hy

theorem holt_of_not_connected (hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (H : StrothHyp M Q Z) {z₀ : G} (hz₀Z : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (P : Sylow 2 ↥(generalizedFitting G))
    (hz₀P : z₀ ∈ (P : Subgroup ↥(generalizedFitting G)).map (generalizedFitting G).subtype)
    (hz₀c : ∀ p ∈ (P : Subgroup ↥(generalizedFitting G)).map (generalizedFitting G).subtype,
      p * z₀ = z₀ * p)
    (hUB : ∀ g : G, g⁻¹ * z₀ * g ∈ Subgroup.normalizer (commComponent z₀) →
      g ∈ Subgroup.normalizer (commComponent z₀))
    (hnot : ¬ conjClassSet z₀ ⊆ commComponent z₀) :
    (∃ M' : Subgroup (FStar G), CFSG.IsStronglyEmbedded M') ∨
      ∃ n : ℕ, Odd n ∧ Nonempty (FStar G ≃* alternatingGroup (Fin n)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : fittingSubgroup G = ⊥ := H.toTim81Hyp.fittingSubgroup_eq_bot H.q4
  obtain ⟨K, hK, hFK, hZK⟩ := exists_component_eq_generalizedFitting H
  obtain ⟨hsimple, hnonab⟩ := Tim81.component_isSimple hF hK
  have hFU := (generalizedFitting_eq_normalClosure H hz₀Z hz₀1).1
  subst hFK
  haveI : IsSimpleGroup ↥(generalizedFitting G) := hsimple
  have hnonab' := hnonab
  have hz₀F : z₀ ∈ generalizedFitting G := hZK hz₀Z
  have hz₀2 : z₀ * z₀ = 1 := by rw [← pow_two]; exact Z_sq H hz₀Z
  have hzN₀ : z₀ ∈ Subgroup.normalizer (commComponent z₀) := mem_normalizer_commComponent hz₀2
  let z₀' : ↥(generalizedFitting G) := ⟨z₀, hz₀F⟩
  have hord : orderOf z₀' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz₀2) hz₀1
  have hNF : (Subgroup.normalizer (commComponent z₀)).subgroupOf (generalizedFitting G) ≠ ⊤ := by
    intro htop
    have hFN : generalizedFitting G ≤ Subgroup.normalizer (commComponent z₀) :=
      Subgroup.subgroupOf_eq_top.mp htop
    apply hnot
    intro y hy
    obtain ⟨x, hx, rfl⟩ := isConj_normalClosure H hz₀Z hz₀1 y hy
    have hxF : x ∈ generalizedFitting G := hFU ▸ hx
    have hxN : x ∈ Subgroup.normalizer (commComponent z₀) := hFN hxF
    have := (show ∀ n, n ∈ commComponent z₀ ↔ x * n * x⁻¹ ∈ commComponent z₀ from hxN) z₀
    exact this.mp mem_commComponent_self
  have hSyl : ∃ S : Sylow 2 ↥(generalizedFitting G), z₀' ∈ (S : Subgroup ↥(generalizedFitting G)) ∧
      (S : Subgroup ↥(generalizedFitting G)) ≤
        Subgroup.centralizer ({z₀'} : Set ↥(generalizedFitting G)) := by
    refine ⟨P, (Subgroup.mem_map_iff_mem (generalizedFitting G).subtype_injective).mp hz₀P,
      fun p hp => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hz₀c (p : G) (Subgroup.mem_map_of_mem _ hp))
  have huniq : ∃! q : ↥(generalizedFitting G) ⧸
      (Subgroup.normalizer (commComponent z₀)).subgroupOf (generalizedFitting G), z₀' • q = q := by
    refine ⟨QuotientGroup.mk 1, ?_, ?_⟩
    · show (QuotientGroup.mk (z₀' * 1) : ↥(generalizedFitting G) ⧸
        (Subgroup.normalizer (commComponent z₀)).subgroupOf (generalizedFitting G)) =
          QuotientGroup.mk 1
      rw [QuotientGroup.eq]
      have hz₀'N : z₀' ∈ (Subgroup.normalizer (commComponent z₀)).subgroupOf
          (generalizedFitting G) := Subgroup.mem_subgroupOf.mpr hzN₀
      have e : (z₀' * 1)⁻¹ * 1 = z₀'⁻¹ := by simp
      rw [e]
      exact Subgroup.inv_mem _ hz₀'N
    · intro q hq
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q
      have hq' : (QuotientGroup.mk (z₀' * g') : ↥(generalizedFitting G) ⧸
          (Subgroup.normalizer (commComponent z₀)).subgroupOf (generalizedFitting G)) =
            QuotientGroup.mk g' := hq
      rw [QuotientGroup.eq] at hq'
      have hz₀'inv : z₀'⁻¹ = z₀' := by
        apply Subtype.ext
        exact inv_eq_of_mul_eq_one_right hz₀2
      have h1 : (g' : G)⁻¹ * z₀ * g' ∈ Subgroup.normalizer (commComponent z₀) := by
        have := Subgroup.mem_subgroupOf.mp hq'
        have e : ((z₀' * g')⁻¹ * g' : ↥(generalizedFitting G)) = g'⁻¹ * z₀' * g' := by
          rw [mul_inv_rev, hz₀'inv]
        rw [e] at this
        simpa using this
      have h2 : (g' : G) ∈ Subgroup.normalizer (commComponent z₀) := hUB (g' : G) h1
      rw [QuotientGroup.eq]
      simpa using Subgroup.mem_subgroupOf.mpr h2
  exact hHolt ↥(generalizedFitting G) hnonab' _ hNF z₀' hord hSyl huniq

theorem smith217_of_holt (hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hUB : Smith217UniqueBlockStatement) (hEx : Smith217ExcludeStatement) :
    Smith217Statement := by
  intro G _ _ M Q Z B IH hc z hz hz1 x y hx hy
  classical
  have H := hc.ctx.hyp
  suffices hconn : conjClassSet z ⊆ commComponent z by
    exact (subset_commComponent_iff z).mp hconn x hx y hy
  by_contra hnot
  haveI : (generalizedFitting G).Normal := (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hQF : Q ≤ generalizedFitting G := Q_le_generalizedFitting H
  obtain ⟨P, z₀, hz₀Z, hz₀1, hz₀P, hz₀c⟩ := exists_involution_center_sylow H hQF
  obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hz₀Z hz₀1
  have hzz₀ : conjClassSet z₀ = conjClassSet z := by
    have h : IsConj z z₀ := isConj_iff.mpr ⟨m, hm⟩
    exact Set.ext fun g => ⟨fun hg => IsConj.trans h hg, fun hg => IsConj.trans h.symm hg⟩
  have hnot₀ : ¬ conjClassSet z₀ ⊆ commComponent z₀ := by
    rw [subset_commComponent_iff, hzz₀]
    rwa [subset_commComponent_iff] at hnot
  have hUB₀ := hUB G M Q Z B IH hc z₀ hz₀Z hz₀1 hnot₀
  exact hEx G M Q Z B IH hc (holt_of_not_connected hHolt H hz₀Z hz₀1 P hz₀P hz₀c hUB₀ hnot₀)

end Reduction

end CFSG.RankThree.GF2n.Smith81
