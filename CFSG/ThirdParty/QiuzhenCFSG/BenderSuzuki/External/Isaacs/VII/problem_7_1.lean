module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.FixedPointProduct

namespace CFSG
end CFSG
open CFSG

/-!
# Isaacs Problem 7.1

A source-faithful statement of Isaacs, *Character Theory of Finite Groups*,
Problem 7.1. The hypotheses `NH = G` and `N \cap H = 1` are kept explicit,
and the six conditions are written out directly.
-/

noncomputable section

namespace CFSG.BenderSuzuki
namespace External
namespace Isaacs
namespace VII

private def problem71A {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  ∀ n : N, n ≠ 1 → Subgroup.centralizer ({(n : G)} : Set G) ≤ N

private def problem71B {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ∀ n : N, n ≠ 1 → ∀ h : H,
    (h : G) * (n : G) = (n : G) * (h : G) → h = 1

private def problem71C {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ h : H, h ≠ 1 → Subgroup.centralizer ({(h : G)} : Set G) ≤ H

private def problem71D {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ∀ x : G, x ∉ N → ∃ h : H, ∃ g : G, g * x * g⁻¹ = (h : G)

private def problem71E {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ∀ h : H, h ≠ 1 → ∀ n : N, ∃ g : G,
    g * ((n : G) * (h : G)) * g⁻¹ = (h : G)

private def problem71F {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  IsFrobeniusGroupWithKernelComplement N H

private def problem71ConjPair
    {G : Type*} [Group G]
    (N H : Subgroup G) [N.Normal] (hdisj : Disjoint N H) :
    N × {h : H // h ≠ 1} → {g : G // g ∉ N} :=
  fun xh =>
    ⟨(xh.1 : G) * (xh.2.1 : G) * (xh.1 : G)⁻¹, by
      intro hmemN
      have hhN : (xh.2.1 : G) ∈ N := by
        have hconj := (inferInstance : N.Normal).conj_mem
          ((xh.1 : G) * (xh.2.1 : G) * (xh.1 : G)⁻¹) hmemN (xh.1 : G)⁻¹
        simpa [mul_assoc] using hconj
      have hhbot : (xh.2.1 : G) ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp hdisj) hhN xh.2.1.2
      exact xh.2.2 (Subtype.ext (by simpa using hhbot))⟩

private theorem problem71ConjPair_card_eq
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) (hcomp : N.IsComplement' H) :
    Nat.card (N × {h : H // h ≠ 1}) = Nat.card {g : G // g ∉ N} := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype N := Fintype.ofFinite N
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype {h : H // h ≠ 1} := Fintype.ofFinite _
  letI : Fintype {g : G // g ∉ N} := Fintype.ofFinite _
  rw [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun h : H => h = 1)]
  rw [Fintype.card_subtype_compl (fun g : G => g ∈ N)]
  have hc := hcomp.card_mul
  simp only [Nat.card_eq_fintype_card] at hc
  simp at hc ⊢
  calc
    Fintype.card N * (Fintype.card H - 1) =
        Fintype.card N * Fintype.card H - Fintype.card N * 1 :=
      Nat.mul_sub_left_distrib _ _ _
    _ = Fintype.card N * Fintype.card H - Fintype.card N := by rw [mul_one]
    _ = Fintype.card G - Fintype.card N :=
      congrArg (fun n => n - Fintype.card N) hc

private theorem problem71_isComplement'
    {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
    (hprod : N ⊔ H = ⊤) (hdisj : Disjoint N H) :
    N.IsComplement' H := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
  rw [Set.eq_univ_iff_forall]
  intro x
  have hx : x ∈ N ⊔ H := by rw [hprod]; trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := N) (t := H) (x := x)).1 hx with
    ⟨n, hnN, h, hhH, hnh⟩
  exact ⟨n, hnN, h, hhH, hnh⟩

private theorem problem71_B_iff_F
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hH : H ≠ ⊥) (hcomp : N.IsComplement' H) :
    problem71B N H ↔ problem71F N H := by
  constructor
  · intro hB
    exact (lemma_3_1 N H hN hH (inferInstance : N.Normal) hcomp).2 (by
      intro h hh
      rw [Subgroup.eq_bot_iff_forall]
      intro n hn
      by_contra hn1
      have hnN : n ∈ N := hn.1
      let nN : N := ⟨n, hnN⟩
      have hnN1 : nN ≠ 1 := by
        intro heq
        exact hn1 (congrArg Subtype.val heq)
      have hcomm : (h : G) * n = n * (h : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp hn.2).symm
      exact hh (hB nN hnN1 h hcomm))
  · intro hfrob n hn h hcomm
    by_contra hh
    have hcent :=
      (lemma_3_1 N H hN hH (inferInstance : N.Normal) hcomp).1 hfrob h hh
    have hncent : (n : G) ∈ elementCentralizerIn N (h : G) := by
      exact ⟨n.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hnbot : (n : G) ∈ (⊥ : Subgroup G) := by simpa [hcent] using hncent
    exact hn (Subtype.ext (by simpa using hnbot))

private theorem problem71_F_imp_D
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hH : H ≠ ⊥) :
    problem71F N H → problem71D N H := by
  intro hfrob x hxN
  have hbij := frobeniusConjPair_bijective N H hfrob hN hH
  rcases hbij.2 ⟨x, hxN⟩ with ⟨⟨n, h⟩, heq⟩
  refine ⟨h.1, (n : G)⁻¹, ?_⟩
  have heqG : (n : G) * (h.1 : G) * (n : G)⁻¹ = x :=
    congrArg Subtype.val heq
  rw [← heqG]
  group

private theorem problem71_D_imp_B
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hcomp : N.IsComplement' H) (hdisj : Disjoint N H) :
    problem71D N H → problem71B N H := by
  classical
  intro hD
  have hsurj : Function.Surjective (problem71ConjPair N H hdisj) := by
    intro x
    rcases hD x.1 x.2 with ⟨h, g, hg⟩
    rcases hcomp.2 g⁻¹ with ⟨⟨⟨n, hnN⟩, ⟨r, hrH⟩⟩, hnr⟩
    let s : H := ⟨r * (h : G) * r⁻¹,
      H.mul_mem (H.mul_mem hrH h.2) (H.inv_mem hrH)⟩
    have hs1 : s ≠ 1 := by
      intro hs
      have hsG : r * (h : G) * r⁻¹ = 1 := congrArg Subtype.val hs
      have hhG : (h : G) = 1 := by
        have ht := congrArg (fun t : G => r⁻¹ * t * r) hsG
        simpa [s, mul_assoc] using ht
      have hg1 : g * x.1 * g⁻¹ = 1 := hg.trans hhG
      have hx1 : x.1 = 1 := by
        have ht := congrArg (fun t : G => g⁻¹ * t * g) hg1
        simpa [mul_assoc] using ht
      exact x.2 (by simp [hx1])
    let p : N × {h : H // h ≠ 1} := ⟨⟨n, hnN⟩, ⟨s, hs1⟩⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    change n * (s : G) * n⁻¹ = x.1
    calc
      n * (s : G) * n⁻¹ = (n * r) * (h : G) * (n * r)⁻¹ := by
        dsimp [s]
        group
      _ = g⁻¹ * (h : G) * (g⁻¹)⁻¹ := by
        have hnr' : n * r = g⁻¹ := by simpa using hnr
        rw [hnr']
      _ = x.1 := by
        have ht := congrArg (fun t : G => g⁻¹ * t * g) hg
        simpa [mul_assoc] using ht.symm
  have hbij : Function.Bijective (problem71ConjPair N H hdisj) :=
    (Nat.bijective_iff_surjective_and_card (problem71ConjPair N H hdisj)).2
      ⟨hsurj, problem71ConjPair_card_eq N H hcomp⟩
  intro n hn h hcomm
  by_contra hh
  let hp : {h : H // h ≠ 1} := ⟨h, hh⟩
  have heq : problem71ConjPair N H hdisj (1, hp) = problem71ConjPair N H hdisj (n, hp) := by
    apply Subtype.ext
    dsimp [problem71ConjPair, hp]
    calc
      (1 : G) * (h : G) * (1 : G)⁻¹ = (h : G) := by simp
      _ = (n : G) * (h : G) * (n : G)⁻¹ := by
        have hc := congrArg (fun t : G => t * (n : G)⁻¹) hcomm
        simpa [mul_assoc] using hc
  have hpairs := hbij.1 heq
  have hnsub : (1 : N) = n := congrArg Prod.fst hpairs
  exact hn hnsub.symm

private theorem problem71_F_imp_A
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hH : H ≠ ⊥) (hcomp : N.IsComplement' H) :
    problem71F N H → problem71A N := by
  intro hfrob n hn x hxcent
  by_contra hxN
  rcases problem71_F_imp_D N H hN hH hfrob x hxN with ⟨h, g, hg⟩
  let ng : N := ⟨g * (n : G) * g⁻¹,
    (inferInstance : N.Normal).conj_mem (n : G) n.2 g⟩
  have hng : ng ≠ 1 := by
    intro heq
    apply hn
    apply Subtype.ext
    have heqG : g * (n : G) * g⁻¹ = 1 := congrArg Subtype.val heq
    have ht := congrArg (fun t : G => g⁻¹ * t * g) heqG
    simpa [ng, mul_assoc] using ht
  have hxcomm : x * (n : G) = (n : G) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxcent
  have hcomm : (h : G) * (ng : G) = (ng : G) * (h : G) := by
    change (h : G) * (g * (n : G) * g⁻¹) =
      (g * (n : G) * g⁻¹) * (h : G)
    rw [← hg]
    calc
      (g * x * g⁻¹) * (g * (n : G) * g⁻¹) =
          g * (x * (n : G)) * g⁻¹ := by group
      _ = g * ((n : G) * x) * g⁻¹ := by rw [hxcomm]
      _ = (g * (n : G) * g⁻¹) * (g * x * g⁻¹) := by group
  have hh1 : h = 1 := (problem71_B_iff_F N H hN hH hcomp).mpr hfrob ng hng h hcomm
  have hx1 : x = 1 := by
    have hg1 : g * x * g⁻¹ = 1 := by simpa [hh1] using hg
    have ht := congrArg (fun t : G => g⁻¹ * t * g) hg1
    simpa [mul_assoc] using ht
  exact hxN (by simp [hx1])

private theorem problem71_A_iff_B
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hH : H ≠ ⊥)
    (hcomp : N.IsComplement' H) (hdisj : Disjoint N H) :
    problem71A N ↔ problem71B N H := by
  constructor
  · intro hA n hn h hcomm
    have hhcent : (h : G) ∈ Subgroup.centralizer ({(n : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hhN := hA n hn hhcent
    have hhbot : (h : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdisj) hhN h.2
    exact Subtype.ext (by simpa using hhbot)
  · intro hB
    exact problem71_F_imp_A N H hN hH hcomp
      ((problem71_B_iff_F N H hN hH hcomp).mp hB)

private theorem problem71_F_imp_C
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal] :
    problem71F N H → problem71C H := by
  intro hfrob h hh x hxcent
  by_contra hxH
  have hxcomm : x * (h : G) = (h : G) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxcent
  have hhconj : (h : G) ∈ H.conjBy x := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨(h : G), h.2, ?_⟩
    simpa [MulAut.conj_apply, mul_assoc] using
      congrArg (fun t : G => t * x⁻¹) hxcomm
  have hhbot : (h : G) ∈ (⊥ : Subgroup G) :=
    (Subgroup.disjoint_def.mp (hfrob.disjoint_conjBy x hxH)) h.2 hhconj
  exact hh (Subtype.ext (by simpa using hhbot))

private theorem problem71_C_imp_B
    {G : Type*} [Group G]
    (N H : Subgroup G) (hdisj : Disjoint N H) :
    problem71C H → problem71B N H := by
  intro hC n hn h hcomm
  by_contra hh
  have hncent : (n : G) ∈ Subgroup.centralizer ({(h : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hnH := hC h hh hncent
  have hnbot : (n : G) ∈ (⊥ : Subgroup G) :=
    (Subgroup.disjoint_def.mp hdisj) n.2 hnH
  exact hn (Subtype.ext (by simpa using hnbot))

private theorem problem71_E_imp_D
    {G : Type*} [Group G]
    (N H : Subgroup G) (hcomp : N.IsComplement' H) :
    problem71E N H → problem71D N H := by
  intro hE x hxN
  rcases hcomp.2 x with ⟨⟨n, h⟩, hnh⟩
  have hh : h ≠ 1 := by
    intro hh1
    apply hxN
    have hx : x = (n : G) := by
      calc
        x = (n : G) * (h : G) := hnh.symm
        _ = (n : G) := by simp [hh1]
    simp [hx]
  rcases hE h hh n with ⟨g, hg⟩
  exact ⟨h, g, by { rw [← hnh]; exact hg }⟩

private theorem problem71_F_imp_E
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hH : H ≠ ⊥)
    (hcomp : N.IsComplement' H) (hdisj : Disjoint N H) :
    problem71F N H → problem71E N H := by
  intro hfrob h hh n
  have hxN : (n : G) * (h : G) ∉ N := by
    intro hx
    have hhN : (h : G) ∈ N := by
      have ht := N.mul_mem (N.inv_mem n.2) hx
      simpa [mul_assoc] using ht
    have hhbot : (h : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdisj) hhN h.2
    exact hh (Subtype.ext (by simpa using hhbot))
  have hbij := frobeniusConjPair_bijective N H hfrob hN hH
  rcases hbij.2 ⟨(n : G) * (h : G), hxN⟩ with ⟨⟨k, r⟩, heq⟩
  have heqG : (k : G) * (r.1 : G) * (k : G)⁻¹ = (n : G) * (h : G) :=
    congrArg Subtype.val heq
  let c : N := ⟨(k : G) * (r.1 : G) * (k : G)⁻¹ * (r.1 : G)⁻¹, by
    have hrconj : (r.1 : G) * (k : G)⁻¹ * (r.1 : G)⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem (k : G)⁻¹ (N.inv_mem k.2) (r.1 : G)
    simpa [mul_assoc] using N.mul_mem k.2 hrconj⟩
  have hprodEq : (c : G) * (r.1 : G) = (n : G) * (h : G) := by
    simpa [c, mul_assoc] using heqG
  have hpairs : (c, r.1) = (n, h) := by
    apply hcomp.1
    exact hprodEq
  have hrh : r.1 = h := congrArg Prod.snd hpairs
  refine ⟨(k : G)⁻¹, ?_⟩
  rw [← heqG]
  have hrhG : (r.1 : G) = h := congrArg Subtype.val hrh
  rw [hrhG]
  group

/-- Isaacs, Character Theory of Finite Groups, Problem 7.1. -/
public theorem isaacs_problem_7_1
    {G : Type*} [Group G] [Finite G]
    (N H : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (hH : H ≠ ⊥)
    (hprod : N ⊔ H = ⊤) (hdisj : Disjoint N H) :
    let A : Prop :=
      forall n : N, n ≠ 1 -> Subgroup.centralizer ({(n : G)} : Set G) ≤ N
    let B : Prop :=
      forall n : N, n ≠ 1 -> forall h : H,
        (h : G) * (n : G) = (n : G) * (h : G) -> h = 1
    let C : Prop :=
      forall h : H, h ≠ 1 -> Subgroup.centralizer ({(h : G)} : Set G) ≤ H
    let D : Prop :=
      forall x : G, x ∉ N -> exists h : H, exists g : G,
        g * x * g⁻¹ = (h : G)
    let E : Prop :=
      forall h : H, h ≠ 1 -> forall n : N, exists g : G,
        g * ((n : G) * (h : G)) * g⁻¹ = (h : G)
    let F : Prop := IsFrobeniusGroupWithKernelComplement N H
    (A ↔ B) ∧ (A ↔ C) ∧ (A ↔ D) ∧ (A ↔ E) ∧ (A ↔ F) := by
  change (problem71A N ↔ problem71B N H) ∧
    (problem71A N ↔ problem71C H) ∧
    (problem71A N ↔ problem71D N H) ∧
    (problem71A N ↔ problem71E N H) ∧
    (problem71A N ↔ problem71F N H)
  have hcomp := problem71_isComplement' N H hprod hdisj
  have hAB := problem71_A_iff_B N H hN hH hcomp hdisj
  have hBF := problem71_B_iff_F N H hN hH hcomp
  have hAC : problem71A N ↔ problem71C H := by
    constructor
    · intro hA
      exact problem71_F_imp_C N H (hBF.mp (hAB.mp hA))
    · intro hC
      exact hAB.mpr (problem71_C_imp_B N H hdisj hC)
  have hAD : problem71A N ↔ problem71D N H := by
    constructor
    · intro hA
      exact problem71_F_imp_D N H hN hH (hBF.mp (hAB.mp hA))
    · intro hD
      exact hAB.mpr (problem71_D_imp_B N H hcomp hdisj hD)
  have hAE : problem71A N ↔ problem71E N H := by
    constructor
    · intro hA
      exact problem71_F_imp_E N H hN hH hcomp hdisj (hBF.mp (hAB.mp hA))
    · intro hE
      exact hAD.mpr (problem71_E_imp_D N H hcomp hE)
  exact ⟨hAB, hAC, hAD, hAE, hAB.trans hBF⟩

end VII
end Isaacs
end External
end CFSG.BenderSuzuki




