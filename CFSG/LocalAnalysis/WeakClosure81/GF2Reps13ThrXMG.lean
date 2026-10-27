module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

private def w16g_yv {X : Subgroup (MulAut W)}
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (u₁ u₂ c d : s13IsoComps X)
    (x : ↥X) : Fin 4 → ZMod 3 :=
  ![lam u₁ (Additive.ofMul x), lam u₂ (Additive.ofMul x), lam c (Additive.ofMul x),
    lam d (Additive.ofMul x)]

private def w16g_pos {X : Subgroup (MulAut W)} (u₁ u₂ c d : s13IsoComps X) :
    Fin 4 → s13IsoComps X :=
  ![u₁, u₂, c, d]

private theorem w16g_supp_zpow_coord_iff {X : Subgroup (MulAut W)}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam)
    (z : ↥X) (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers (z : MulAut W)) ↔
      lam U (Additive.ofMul z) ≠ 0 := by
  have h1 : (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers (z : MulAut W)) ↔
      commSub (U : Subgroup W) (Subgroup.zpowers (z : MulAut W)) ≠ ⊥ := by
    simp only [s13Supp, Set.mem_setOf_eq, U.2, true_and]
  rw [h1]
  exact (coord_ne_zero_iff hl z U).symm

omit [Finite W] in
private theorem w16g_finsum_four_distinct {X : Subgroup (MulAut W)}
    (u₁ u₂ c d : s13IsoComps X)
    (h12 : u₁ ≠ u₂) (h1c : u₁ ≠ c) (h1d : u₁ ≠ d)
    (h2c : u₂ ≠ c) (h2d : u₂ ≠ d) (hcd : c ≠ d)
    (f : ↥(s13IsoComps X) → ZMod 3)
    (hf : ∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d → f U = 0) :
    ∑ᶠ U, f U = f u₁ + f u₂ + f c + f d := by
  classical
  have hsupp : Function.support f ⊆
      (↑({u₁, u₂, c, d} : Finset ↥(s13IsoComps X)) : Set ↥(s13IsoComps X)) := by
    intro U hU
    simp only [Function.mem_support] at hU
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hU (hf U hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2)
  rw [finsum_eq_finsetSum_of_support_subset f hsupp]
  have h1 : u₁ ∉ ({u₂, c, d} : Finset ↥(s13IsoComps X)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h1c, h1d⟩
  have h2 : u₂ ∉ ({c, d} : Finset ↥(s13IsoComps X)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h2c, h2d⟩
  have h3 : c ∉ ({d} : Finset ↥(s13IsoComps X)) := by
    simpa using hcd
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton]
  ring

private theorem w16g_ncard_Dset {X : Subgroup (MulAut W)}
    {u₁ u₂ c d : s13IsoComps X}
    (h12 : u₁ ≠ u₂) (h1c : u₁ ≠ c) (h1d : u₁ ≠ d)
    (h2c : u₂ ≠ c) (h2d : u₂ ≠ d) (hcd : c ≠ d) :
    ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
      Set (Subgroup W)).ncard = 4 := by
  have h1 : (u₁ : Subgroup W) ∉ ({(u₂ : Subgroup W), (c : Subgroup W),
      (d : Subgroup W)} : Set (Subgroup W)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h12 (Subtype.ext h), fun h => h1c (Subtype.ext h),
      fun h => h1d (Subtype.ext h)⟩
  have h2 : (u₂ : Subgroup W) ∉ ({(c : Subgroup W), (d : Subgroup W)} :
      Set (Subgroup W)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h2c (Subtype.ext h), fun h => h2d (Subtype.ext h)⟩
  have h3 : (c : Subgroup W) ∉ ({(d : Subgroup W)} : Set (Subgroup W)) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => hcd (Subtype.ext h)
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

private theorem w16g_zpowers_card_three {L : Subgroup (MulAut W)}
    (hL : Nat.card ↥L = 3) : ∃ q : MulAut W, L = Subgroup.zpowers q := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic ↥L := isCyclic_of_prime_card hL
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := ↥L)
  have hqtop : Subgroup.zpowers q = ⊤ := (Subgroup.eq_top_iff' _).mpr hq
  refine ⟨(q : MulAut W), ?_⟩
  have hcard : Nat.card ↥L ≤ Nat.card ↥(Subgroup.zpowers (q : MulAut W)) := by
    have hord : orderOf q = Nat.card ↥L := by
      rw [← Nat.card_zpowers (q : ↥L), hqtop, Subgroup.card_top]
    simpa only [Nat.card_zpowers, Subgroup.orderOf_coe, hord] using le_rfl
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr q.2) hcard).symm

omit [Finite W] in
private theorem w16g_double_conj_map (Q : Subgroup (MulAut W)) (g a : MulAut W) :
    (Q.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Q.map (MulAut.conj (g * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16g_weight_blocks {X : Subgroup (MulAut W)}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} (hl : IsCoord X 3 lam)
    {u₁ u₂ c d : s13IsoComps X}
    (h12 : u₁ ≠ u₂) (h1c : u₁ ≠ c) (h1d : u₁ ≠ d)
    (h2c : u₂ ≠ c) (h2d : u₂ ≠ d) (hcd : c ≠ d)
    (x : ↥X) (hx3 : (s13Supp X (Subgroup.zpowers (x : MulAut W))).ncard = 3)
    (hyt : w16g_yv lam u₁ u₂ c d x = 0 ∨
      Fintype.card {i : Fin 4 // w16g_yv lam u₁ u₂ c d x i ≠ 0} = 3) :
    s13Supp X (Subgroup.zpowers (x : MulAut W)) ⊆
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) ∨
      Disjoint (s13Supp X (Subgroup.zpowers (x : MulAut W)))
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) := by
  classical
  have hinj : Function.Injective (w16g_pos u₁ u₂ c d) := by
    change Function.Injective (Fin.cons u₁ (![u₂, c, d] : Fin 3 → s13IsoComps X))
    rw [Fin.cons_injective_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact h12 hi.symm
      · exact h1c hi.symm
      · exact h1d hi.symm
    · change Function.Injective (Fin.cons u₂ (![c, d] : Fin 2 → s13IsoComps X))
      rw [Fin.cons_injective_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact h2c hi.symm
        · exact h2d hi.symm
      · change Function.Injective (Fin.cons c (![d] : Fin 1 → s13IsoComps X))
        rw [Fin.cons_injective_iff]
        refine ⟨?_, ?_⟩
        · rintro ⟨i, hi⟩
          fin_cases i
          exact hcd hi.symm
        · intro i j _
          fin_cases i
          fin_cases j
          rfl
  have hyvpos : ∀ i : Fin 4,
      w16g_yv lam u₁ u₂ c d x i = lam (w16g_pos u₁ u₂ c d i) (Additive.ofMul x) := by
    intro i
    fin_cases i <;> simp [w16g_pos, w16g_yv]
  have hposD : ∀ i : Fin 4, (w16g_pos u₁ u₂ c d i : Subgroup W) ∈
      ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
        Set (Subgroup W)) := by
    intro i
    fin_cases i <;> simp [w16g_pos]
  rcases hyt with hyv0 | hyv3
  · right
    rw [Set.disjoint_left]
    intro U hUsupp hUD
    have hUX : U ∈ s13IsoComps X := hUsupp.1
    have hcoord : lam ⟨U, hUX⟩ (Additive.ofMul x) ≠ 0 :=
      (w16g_supp_zpow_coord_iff hl x ⟨U, hUX⟩).mp hUsupp
    have hzero_i : ∀ i : Fin 4, lam (w16g_pos u₁ u₂ c d i) (Additive.ofMul x) = 0 := by
      intro i
      have h := congrFun hyv0 i
      rwa [hyvpos i] at h
    have hUis : U = (u₁ : Subgroup W) ∨ U = (u₂ : Subgroup W) ∨
        U = (c : Subgroup W) ∨ U = (d : Subgroup W) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hUD
    have hzero : lam ⟨U, hUX⟩ (Additive.ofMul x) = 0 := by
      rcases hUis with h | h | h | h
      · have hsub : (⟨U, hUX⟩ : s13IsoComps X) = w16g_pos u₁ u₂ c d 0 := by
          apply Subtype.ext
          simpa [w16g_pos] using h
        rw [hsub]; exact hzero_i 0
      · have hsub : (⟨U, hUX⟩ : s13IsoComps X) = w16g_pos u₁ u₂ c d 1 := by
          apply Subtype.ext
          simpa [w16g_pos] using h
        rw [hsub]; exact hzero_i 1
      · have hsub : (⟨U, hUX⟩ : s13IsoComps X) = w16g_pos u₁ u₂ c d 2 := by
          apply Subtype.ext
          simpa [w16g_pos] using h
        rw [hsub]; exact hzero_i 2
      · have hsub : (⟨U, hUX⟩ : s13IsoComps X) = w16g_pos u₁ u₂ c d 3 := by
          apply Subtype.ext
          simpa [w16g_pos] using h
        rw [hsub]; exact hzero_i 3
    exact hcoord hzero
  · left
    have hvalinj : Function.Injective (fun i : Fin 4 => (w16g_pos u₁ u₂ c d i : Subgroup W)) :=
      fun i j hij => hinj (Subtype.ext hij)
    have hSsub : (fun i : Fin 4 => (w16g_pos u₁ u₂ c d i : Subgroup W)) ''
        {i : Fin 4 | w16g_yv lam u₁ u₂ c d x i ≠ 0} ⊆
        s13Supp X (Subgroup.zpowers (x : MulAut W)) ∩
          ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
            Set (Subgroup W)) := by
      rintro U ⟨i, hi, rfl⟩
      refine ⟨?_, hposD i⟩
      rw [w16g_supp_zpow_coord_iff hl x (w16g_pos u₁ u₂ c d i), ← hyvpos i]
      exact hi
    have hScard : ((fun i : Fin 4 => (w16g_pos u₁ u₂ c d i : Subgroup W)) ''
        {i : Fin 4 | w16g_yv lam u₁ u₂ c d x i ≠ 0}).ncard = 3 := by
      rw [Set.ncard_image_of_injective _ hvalinj, ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card]
      exact hyv3
    have hle : 3 ≤ (s13Supp X (Subgroup.zpowers (x : MulAut W)) ∩
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W))).ncard := by
      rw [← hScard]
      exact Set.ncard_le_ncard hSsub
    have hle' : (s13Supp X (Subgroup.zpowers (x : MulAut W)) ∩
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W))).ncard ≤ 3 := by
      calc _ ≤ (s13Supp X (Subgroup.zpowers (x : MulAut W))).ncard :=
            Set.ncard_le_ncard Set.inter_subset_left
        _ = 3 := hx3
    have heq : (s13Supp X (Subgroup.zpowers (x : MulAut W)) ∩
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W))).ncard = 3 := le_antisymm hle' hle
    have hEq : s13Supp X (Subgroup.zpowers (x : MulAut W)) ∩
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) = s13Supp X (Subgroup.zpowers (x : MulAut W)) :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [heq, hx3])
    intro U hU
    have hU' : U ∈ s13Supp X (Subgroup.zpowers (x : MulAut W)) ∩
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) := by rw [hEq]; exact hU
    exact hU'.2

private theorem w16g_blocks_of_supp_three (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d)
    (x : ↥X) (hx3 : (s13Supp X (Subgroup.zpowers (x : MulAut W))).ncard = 3) :
    s13Supp X (Subgroup.zpowers (x : MulAut W)) ⊆
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) ∨
      Disjoint (s13Supp X (Subgroup.zpowers (x : MulAut W)))
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) := by
  have hqQ : (q : MulAut W) ∈ Q := by rw [F.hQq]; exact Subgroup.mem_zpowers _
  have hconj1 : MulAut.conj (1 : MulAut W) = 1 := by ext w; simp
  have hmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
    have h1 : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
      rw [hconj1]
      ext w
      rfl
    rw [h1, Subgroup.map_id]
  have horth_q : ∀ y : ↥X,
      ∑ᶠ U, lam U (Additive.ofMul q) * lam U (Additive.ofMul y) = 0 := fun y =>
    s13_three_orthogonal h hH0 hQ3 he F.hl 1 A.one_mem q (by rw [hmap1]; exact hqQ) y
  have hrQa : (r : MulAut W) ∈ Q.map (MulAut.conj a).toMonoidHom := by
    rw [F.hQr]; exact Subgroup.mem_zpowers _
  have horth_r : ∀ y : ↥X,
      ∑ᶠ U, lam U (Additive.ofMul r) * lam U (Additive.ofMul y) = 0 := fun y =>
    s13_three_orthogonal h hH0 hQ3 he F.hl a F.ha r hrQa y
  let qv : Fin 4 → ZMod 3 := ![lam u₁ (Additive.ofMul q), lam u₂ (Additive.ofMul q),
    lam c (Additive.ofMul q), 0]
  let rv : Fin 4 → ZMod 3 := ![lam u₁ (Additive.ofMul r), lam u₂ (Additive.ofMul r),
    0, lam d (Additive.ofMul r)]
  have hq0 : qv 0 ≠ 0 := (F.hq u₁).mpr (Or.inl rfl)
  have hq1 : qv 1 ≠ 0 := (F.hq u₂).mpr (Or.inr (Or.inl rfl))
  have hq2 : qv 2 ≠ 0 := (F.hq c).mpr (Or.inr (Or.inr rfl))
  have hq3 : qv 3 = 0 := rfl
  have hr0 : rv 0 ≠ 0 := (F.hr u₁).mpr (Or.inl rfl)
  have hr1 : rv 1 ≠ 0 := (F.hr u₂).mpr (Or.inr (Or.inl rfl))
  have hr2 : rv 2 = 0 := rfl
  have hr3 : rv 3 ≠ 0 := (F.hr d).mpr (Or.inr (Or.inr rfl))
  have hq_d : lam d (Additive.ofMul q) = 0 := by
    by_contra hne
    rcases (F.hq d).mp hne with hd | hd | hd
    · exact F.h1d hd.symm
    · exact F.h2d hd.symm
    · exact F.hcd hd.symm
  have hr_c : lam c (Additive.ofMul r) = 0 := by
    by_contra hne
    rcases (F.hr c).mp hne with hc | hc | hc
    · exact F.h1c hc.symm
    · exact F.h2c hc.symm
    · exact F.hcd hc
  have hfour : ∀ (f : ↥(s13IsoComps X) → ZMod 3),
      (∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d → f U = 0) →
      ∑ᶠ U, f U = f u₁ + f u₂ + f c + f d := fun f hf =>
    w16g_finsum_four_distinct u₁ u₂ c d F.h12 F.h1c F.h1d F.h2c F.h2d F.hcd f hf
  have hqrx : ∑ᶠ U, lam U (Additive.ofMul q) * lam U (Additive.ofMul r) =
      lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
      lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) +
      lam c (Additive.ofMul q) * lam c (Additive.ofMul r) +
      lam d (Additive.ofMul q) * lam d (Additive.ofMul r) := by
    refine hfour _ (fun U h1 h2 h3 _ => ?_)
    have hqU : lam U (Additive.ofMul q) = 0 := by
      by_contra hne
      rcases (F.hq U).mp hne with hUU | hUU | hUU
      · exact h1 hUU
      · exact h2 hUU
      · exact h3 hUU
    rw [hqU, zero_mul]
  have horth : qv ⬝ᵥ rv = 0 := by
    have h2term : lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) = 0 := by
      have hsum := horth_q r
      rw [hqrx, hq_d, zero_mul, add_zero, hr_c, mul_zero, add_zero] at hsum
      exact hsum
    have hdot : qv ⬝ᵥ rv = lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) := by
      simp [qv, rv, dotProduct, Fin.sum_univ_four]
    rw [hdot, h2term]
  have hy1 : qv ⬝ᵥ w16g_yv lam u₁ u₂ c d x = 0 := by
    have h4 := hfour (fun U => lam U (Additive.ofMul q) * lam U (Additive.ofMul x))
      (fun U h1 h2 h3 _ => by
        have hqU : lam U (Additive.ofMul q) = 0 := by
          by_contra hne
          rcases (F.hq U).mp hne with hUU | hUU | hUU
          · exact h1 hUU
          · exact h2 hUU
          · exact h3 hUU
        rw [hqU, zero_mul])
    calc qv ⬝ᵥ w16g_yv lam u₁ u₂ c d x =
        ∑ᶠ U, lam U (Additive.ofMul q) * lam U (Additive.ofMul x) := by
          rw [h4]
          simp [qv, w16g_yv, dotProduct, Fin.sum_univ_four, hq_d]
      _ = 0 := horth_q x
  have hy2 : rv ⬝ᵥ w16g_yv lam u₁ u₂ c d x = 0 := by
    have h4 := hfour (fun U => lam U (Additive.ofMul r) * lam U (Additive.ofMul x))
      (fun U h1 h2 _ h4 => by
        have hrU : lam U (Additive.ofMul r) = 0 := by
          by_contra hne
          rcases (F.hr U).mp hne with hUU | hUU | hUU
          · exact h1 hUU
          · exact h2 hUU
          · exact h4 hUU
        rw [hrU, zero_mul])
    calc rv ⬝ᵥ w16g_yv lam u₁ u₂ c d x =
        ∑ᶠ U, lam U (Additive.ofMul r) * lam U (Additive.ofMul x) := by
          rw [h4]
          simp [rv, w16g_yv, dotProduct, Fin.sum_univ_four, hr_c]
      _ = 0 := horth_r x
  have hmem : w16g_yv lam u₁ u₂ c d x ∈
      Submodule.span (ZMod 3) ({qv, rv} : Set (Fin 4 → ZMod 3)) :=
    w16g_core qv rv (w16g_yv lam u₁ u₂ c d x) hq0 hq1 hq2 hq3 hr0 hr1 hr2 hr3
      horth hy1 hy2
  have hqq : qv ⬝ᵥ qv = 0 := by
    have hdec : ∀ p q' s : ZMod 3, p ≠ 0 → q' ≠ 0 → s ≠ 0 →
        (![p, q', s, 0] : Fin 4 → ZMod 3) ⬝ᵥ ![p, q', s, 0] = 0 := by decide
    have hv : qv = ![qv 0, qv 1, qv 2, qv 3] := by funext i; fin_cases i <;> rfl
    rw [hv, hq3]
    exact hdec (qv 0) (qv 1) (qv 2) hq0 hq1 hq2
  have hrr : rv ⬝ᵥ rv = 0 := by
    have hdec : ∀ p q' s : ZMod 3, p ≠ 0 → q' ≠ 0 → s ≠ 0 →
        (![p, q', 0, s] : Fin 4 → ZMod 3) ⬝ᵥ ![p, q', 0, s] = 0 := by decide
    have hv : rv = ![rv 0, rv 1, rv 2, rv 3] := by funext i; fin_cases i <;> rfl
    rw [hv, hr2]
    exact hdec (rv 0) (rv 1) (rv 3) hr0 hr1 hr3
  have hself : w16g_yv lam u₁ u₂ c d x ⬝ᵥ w16g_yv lam u₁ u₂ c d x = 0 := by
    obtain ⟨p, q', hpq⟩ := Submodule.mem_span_pair.mp hmem
    rw [← hpq]
    have hrq : rv ⬝ᵥ qv = 0 := by rw [dotProduct_comm]; exact horth
    have hexp : (p • qv + q' • rv) ⬝ᵥ (p • qv + q' • rv) =
        p ^ 2 * (qv ⬝ᵥ qv) + p * q' * (qv ⬝ᵥ rv) + q' * p * (rv ⬝ᵥ qv) +
          q' ^ 2 * (rv ⬝ᵥ rv) := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      ring
    rw [hexp, hqq, hrr, horth, hrq]
    ring
  have hyt := w16g_isotropic_weight (w16g_yv lam u₁ u₂ c d x) hself
  exact w16g_weight_blocks F.hl F.h12 F.h1c F.h1d F.h2c F.h2d F.hcd x hx3 hyt

private theorem w16g_conj_supp_blocks (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d)
    {b : MulAut W} (hb : b ∈ A) :
    s13Supp X (Q.map (MulAut.conj b).toMonoidHom) ⊆
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) ∨
      Disjoint (s13Supp X (Q.map (MulAut.conj b).toMonoidHom))
        ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
          Set (Subgroup W)) := by
  have hQbX : Q.map (MulAut.conj b).toMonoidHom ≤ X := by
    intro y hy
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hy
    change (MulAut.conj b) q₀ ∈ X
    rw [MulAut.conj_apply]
    exact h.hXA b hb q₀ (h.hQX hq₀)
  have hQb3 : Nat.card ↥(Q.map (MulAut.conj b).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hQ3]
  obtain ⟨qb, hqb⟩ := w16g_zpowers_card_three hQb3
  have hqbX : (qb : MulAut W) ∈ X := hQbX (hqb ▸ Subgroup.mem_zpowers qb)
  have hsupp_eq : s13Supp X (Q.map (MulAut.conj b).toMonoidHom) =
      s13Supp X (Subgroup.zpowers (qb : MulAut W)) := by rw [hqb]
  have hncard : (s13Supp X (Subgroup.zpowers (qb : MulAut W))).ncard = 3 := by
    rw [← hsupp_eq, s13Supp_conj (X := X) (L := Q) (g := b) (h.hXA b hb)
      (by simpa using fun y hy => h.hXA b⁻¹ (A.inv_mem hb) y hy),
      Set.ncard_image_of_injective _ (Subgroup.map_injective b.injective), he]
  have hres := w16g_blocks_of_supp_three h hH0 hQ3 he F ⟨qb, hqbX⟩ hncard
  rwa [← hsupp_eq] at hres

theorem w16g_tetra_blocks (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d) :
    ∀ g ∈ A,
      s13Supp X ((Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)).map
          (MulAut.conj g).toMonoidHom) =
        s13Supp X (Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)) ∨
      Disjoint
        (s13Supp X ((Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)).map
          (MulAut.conj g).toMonoidHom))
        (s13Supp X (Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W))) := by
  classical
  intro g hg
  set Dset : Set (Subgroup W) :=
    {(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} with hDset
  have hg' : ∀ y ∈ X, g⁻¹ * y * g ∈ X := fun y hy => h.hXA g⁻¹ (A.inv_mem hg) y hy
  have hsuppT : s13Supp X
      (Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)) = Dset := by
    rw [w16g_tetra_supp h hH0 hQ3 he F, hDset]
  rw [s13Supp_conj (X := X)
    (L := Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)) (g := g)
    (h.hXA g hg) hg', hsuppT]
  let E1 : Set (Subgroup W) := s13Supp X (Q.map (MulAut.conj g).toMonoidHom)
  let E2 : Set (Subgroup W) := s13Supp X (Q.map (MulAut.conj (g * a)).toMonoidHom)
  have hblocks1 : E1 ⊆ Dset ∨ Disjoint E1 Dset :=
    w16g_conj_supp_blocks h hH0 hQ3 he F hg
  have hblocks2 : E2 ⊆ Dset ∨ Disjoint E2 Dset :=
    w16g_conj_supp_blocks h hH0 hQ3 he F (A.mul_mem hg F.ha)
  have hImQ : (fun U : Subgroup W => U.map g.toMonoidHom) '' (s13Supp X Q) = E1 :=
    (s13Supp_conj (X := X) (L := Q) (g := g) (h.hXA g hg) hg').symm
  have hImQa : (fun U : Subgroup W => U.map g.toMonoidHom) ''
      (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) = E2 := by
    rw [(s13Supp_conj (X := X) (L := Q.map (MulAut.conj a).toMonoidHom) (g := g)
      (h.hXA g hg) hg').symm, w16g_double_conj_map Q g a]
  have hDset_split : Dset = s13Supp X Q ∪
      s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
    rw [hDset, F.hsq, F.hsr]
    ext U
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hDg_eq : (fun U : Subgroup W => U.map g.toMonoidHom) '' Dset = E1 ∪ E2 := by
    rw [hDset_split, Set.image_union, hImQ, hImQa]
  have hu1Q : (u₁ : Subgroup W) ∈ s13Supp X Q := by rw [F.hsq]; simp
  have hu1Qa : (u₁ : Subgroup W) ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
    rw [F.hsr]; simp
  have hE1E2 : (E1 ∩ E2).Nonempty := by
    refine ⟨(u₁ : Subgroup W).map g.toMonoidHom, ?_, ?_⟩
    · rw [← hImQ]; exact Set.mem_image_of_mem _ hu1Q
    · rw [← hImQa]; exact Set.mem_image_of_mem _ hu1Qa
  rcases hblocks1 with hsub1 | hdisj1
  · have hdisj2 : ¬ Disjoint E2 Dset := by
      rintro hd
      rcases hE1E2 with ⟨y, hy1, hy2⟩
      exact (Set.disjoint_left.mp hd hy2) (hsub1 hy1)
    have hsub2 : E2 ⊆ Dset := hblocks2.resolve_right hdisj2
    left
    have hDgsub : (fun U : Subgroup W => U.map g.toMonoidHom) '' Dset ⊆ Dset := by
      rw [hDg_eq]
      exact Set.union_subset hsub1 hsub2
    have hDgcard : ((fun U : Subgroup W => U.map g.toMonoidHom) '' Dset).ncard = 4 := by
      rw [Set.ncard_image_of_injective _ (Subgroup.map_injective g.injective), hDset]
      exact w16g_ncard_Dset F.h12 F.h1c F.h1d F.h2c F.h2d F.hcd
    have hDsetcard : Dset.ncard = 4 := by
      rw [hDset]
      exact w16g_ncard_Dset F.h12 F.h1c F.h1d F.h2c F.h2d F.hcd
    exact Set.eq_of_subset_of_ncard_le hDgsub (by rw [hDgcard, hDsetcard])
  · rcases hblocks2 with hsub2 | hdisj2
    · exfalso
      rcases hE1E2 with ⟨y, hy1, hy2⟩
      exact (Set.disjoint_left.mp hdisj1 hy1) (hsub2 hy2)
    · right
      rw [hDg_eq]
      exact Set.disjoint_union_left.mpr ⟨hdisj1, hdisj2⟩

end CFSG.LocalAnalysis.WeakClosure81
