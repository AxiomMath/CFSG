module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMD
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement IsMulCommutative

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
private theorem w16g_map_zpowers_sup (X : Subgroup (MulAut W)) (q r : ↥X) :
    (Subgroup.zpowers q ⊔ Subgroup.zpowers r).map X.subtype =
      Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

omit [Finite W] in
private theorem w16g_coord_eq_zero_of_mem_sup {X : Subgroup (MulAut W)} {q r x : ↥X}
    {φ : Additive ↥X →+ ZMod 3}
    (hq0 : φ (Additive.ofMul q) = 0) (hr0 : φ (Additive.ofMul r) = 0)
    (hx : (x : MulAut W) ∈ Subgroup.zpowers (q : MulAut W) ⊔
      Subgroup.zpowers (r : MulAut W)) :
    φ (Additive.ofMul x) = 0 := by
  let P : Subgroup ↥X :=
    { carrier := {y | φ (Additive.ofMul y) = 0}
      one_mem' := by simp
      mul_mem' := fun {y z} hy hz => by
        change φ (Additive.ofMul (y * z)) = 0
        rw [ofMul_mul, map_add, hy, hz, add_zero]
      inv_mem' := fun {y} hy => by
        change φ (Additive.ofMul y⁻¹) = 0
        rw [ofMul_inv, map_neg, hy, neg_zero] }
  have hx' : x ∈ (Subgroup.zpowers q ⊔ Subgroup.zpowers r : Subgroup ↥X) := by
    rw [← Subgroup.mem_map_iff_mem X.subtype_injective, w16g_map_zpowers_sup X q r]
    exact hx
  have hle : (Subgroup.zpowers q ⊔ Subgroup.zpowers r : Subgroup ↥X) ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr (show q ∈ P from hq0))
      (Subgroup.zpowers_le.mpr (show r ∈ P from hr0))
  exact hle hx'

private theorem w16g_mem_s13Supp_zpowers_iff {X : Subgroup (MulAut W)} {p : ℕ}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam)
    {z : MulAut W} (hz : z ∈ X) (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers z) ↔
      lam U (Additive.ofMul ⟨z, hz⟩) ≠ 0 := by
  have h1 : (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers z) ↔
      commSub (U : Subgroup W) (Subgroup.zpowers z) ≠ ⊥ := by
    simp only [s13Supp, Set.mem_setOf_eq, U.2, true_and]
  rw [h1]
  exact (coord_ne_zero_iff hl ⟨z, hz⟩ U).symm

omit [Finite W] in
private theorem w16g_finsum_eq_four {X : Subgroup (MulAut W)}
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

private theorem w16g_dot_self_smul_add (u v : Fin 4 → ZMod 3)
    (huu : u ⬝ᵥ u = 0) (hvv : v ⬝ᵥ v = 0) (huv : u ⬝ᵥ v = 0) (a b : ZMod 3) :
    (a • u + b • v) ⬝ᵥ (a • u + b • v) = 0 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    huu, hvv, huv, hvu, smul_zero, add_zero]

private theorem w16g_dot_three_zero (a b c : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (![a, b, c, 0] : Fin 4 → ZMod 3) ⬝ᵥ (![a, b, c, 0] : Fin 4 → ZMod 3) = 0 := by
  revert a b c
  decide +kernel

private theorem w16g_dot_three_zero' (a b c : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (![a, b, 0, c] : Fin 4 → ZMod 3) ⬝ᵥ (![a, b, 0, c] : Fin 4 → ZMod 3) = 0 := by
  revert a b c
  decide +kernel

theorem w16g_tetra_supp (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d) :
    s13Supp X (Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)) =
      {(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} := by
  classical
  have _h := h
  have _hH0 := hH0
  have _hQ3 := hQ3
  have _he := he
  have hTX : Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W) ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr q.2) (Subgroup.zpowers_le.mpr r.2)
  apply Set.Subset.antisymm
  · intro U hU
    by_contra hUnot
    have hUnot' : U ≠ (u₁ : Subgroup W) ∧ U ≠ (u₂ : Subgroup W) ∧ U ≠ (c : Subgroup W) ∧
        U ≠ (d : Subgroup W) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hUnot
    have hUmem : U ∈ s13IsoComps X := hU.1
    let U' : s13IsoComps X := ⟨U, hUmem⟩
    obtain ⟨x, hxT, hxne⟩ := (mem_s13Supp_iff_coord F.hl hTX U').mp hU
    have hn1 : U' ≠ u₁ := fun hh => hUnot'.1 (congrArg Subtype.val hh)
    have hn2 : U' ≠ u₂ := fun hh => hUnot'.2.1 (congrArg Subtype.val hh)
    have hnc : U' ≠ c := fun hh => hUnot'.2.2.1 (congrArg Subtype.val hh)
    have hnd : U' ≠ d := fun hh => hUnot'.2.2.2 (congrArg Subtype.val hh)
    have hq0 : lam U' (Additive.ofMul q) = 0 := by
      by_contra hne
      rcases (F.hq U').mp hne with hh | hh | hh
      · exact hn1 hh
      · exact hn2 hh
      · exact hnc hh
    have hr0 : lam U' (Additive.ofMul r) = 0 := by
      by_contra hne
      rcases (F.hr U').mp hne with hh | hh | hh
      · exact hn1 hh
      · exact hn2 hh
      · exact hnd hh
    exact hxne (w16g_coord_eq_zero_of_mem_sup hq0 hr0 hxT)
  · intro U hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    rcases hU with rfl | rfl | rfl | rfl
    · exact (mem_s13Supp_iff_coord F.hl hTX u₁).mpr
        ⟨q, Subgroup.mem_sup_left (Subgroup.mem_zpowers (q : MulAut W)),
          (F.hq u₁).mpr (Or.inl rfl)⟩
    · exact (mem_s13Supp_iff_coord F.hl hTX u₂).mpr
        ⟨q, Subgroup.mem_sup_left (Subgroup.mem_zpowers (q : MulAut W)),
          (F.hq u₂).mpr (Or.inr (Or.inl rfl))⟩
    · exact (mem_s13Supp_iff_coord F.hl hTX c).mpr
        ⟨q, Subgroup.mem_sup_left (Subgroup.mem_zpowers (q : MulAut W)),
          (F.hq c).mpr (Or.inr (Or.inr rfl))⟩
    · exact (mem_s13Supp_iff_coord F.hl hTX d).mpr
        ⟨r, Subgroup.mem_sup_right (Subgroup.mem_zpowers (r : MulAut W)),
          (F.hr d).mpr (Or.inr (Or.inr rfl))⟩


private theorem w16g_tetra_rank_six (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d) :
    ∀ x ∈ Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W), x ≠ 1 →
      rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6 := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : IsMulCommutative ↥X := h.hXe.1
  set T : Subgroup (MulAut W) :=
    Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W) with hT
  have hTX : T ≤ X := by
    rw [hT]
    exact sup_le (Subgroup.zpowers_le.mpr q.2) (Subgroup.zpowers_le.mpr r.2)
  let qv : Fin 4 → ZMod 3 :=
    ![lam u₁ (Additive.ofMul q), lam u₂ (Additive.ofMul q), lam c (Additive.ofMul q), 0]
  let rv : Fin 4 → ZMod 3 :=
    ![lam u₁ (Additive.ofMul r), lam u₂ (Additive.ofMul r), 0, lam d (Additive.ofMul r)]
  have hq₁ : qv 0 ≠ 0 := by simpa [qv] using (F.hq u₁).mpr (Or.inl rfl)
  have hq₂ : qv 1 ≠ 0 := by simpa [qv] using (F.hq u₂).mpr (Or.inr (Or.inl rfl))
  have hqc : qv 2 ≠ 0 := by simpa [qv] using (F.hq c).mpr (Or.inr (Or.inr rfl))
  have hq3 : qv 3 = 0 := rfl
  have hr₁ : rv 0 ≠ 0 := by simpa [rv] using (F.hr u₁).mpr (Or.inl rfl)
  have hr₂ : rv 1 ≠ 0 := by simpa [rv] using (F.hr u₂).mpr (Or.inr (Or.inl rfl))
  have hr2 : rv 2 = 0 := rfl
  have hrd : rv 3 ≠ 0 := by simpa [rv] using (F.hr d).mpr (Or.inr (Or.inr rfl))
  have hq_d : lam d (Additive.ofMul q) = 0 := by
    by_contra hne
    rcases (F.hq d).mp hne with hh | hh | hh
    · exact F.h1d hh.symm
    · exact F.h2d hh.symm
    · exact F.hcd hh.symm
  have hr_c : lam c (Additive.ofMul r) = 0 := by
    by_contra hne
    rcases (F.hr c).mp hne with hh | hh | hh
    · exact F.h1c hh.symm
    · exact F.h2c hh.symm
    · exact F.hcd hh
  have hqq : qv ⬝ᵥ qv = 0 := by
    have hqv : qv = ![qv 0, qv 1, qv 2, qv 3] := by funext i; fin_cases i <;> rfl
    rw [hqv, hq3]
    exact w16g_dot_three_zero (qv 0) (qv 1) (qv 2) hq₁ hq₂ hqc
  have hrr : rv ⬝ᵥ rv = 0 := by
    have hrv : rv = ![rv 0, rv 1, rv 2, rv 3] := by funext i; fin_cases i <;> rfl
    rw [hrv, hr2]
    exact w16g_dot_three_zero' (rv 0) (rv 1) (rv 3) hr₁ hr₂ hrd
  have hqr : qv ⬝ᵥ rv = 0 := by
    have hqQ : (q : MulAut W) ∈ Q := by rw [F.hQq]; exact Subgroup.mem_zpowers _
    have hmap1 : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
      rw [show MulAut.conj (1 : MulAut W) = 1 from by ext w; simp]
      exact Subgroup.map_id Q
    have hqr_sum : ∑ᶠ U : ↥(s13IsoComps X),
        lam U (Additive.ofMul q) * lam U (Additive.ofMul r) = 0 :=
      s13_three_orthogonal h hH0 hQ3 he F.hl (1 : MulAut W) A.one_mem q
        (by rw [hmap1]; exact hqQ) r
    have hf : ∀ U, U ≠ u₁ → U ≠ u₂ → U ≠ c → U ≠ d →
        lam U (Additive.ofMul q) * lam U (Additive.ofMul r) = 0 := by
      intro U h1 h2 h3 _
      have hqU : lam U (Additive.ofMul q) = 0 := by
        by_contra hne
        rcases (F.hq U).mp hne with hh | hh | hh
        · exact h1 hh
        · exact h2 hh
        · exact h3 hh
      rw [hqU, zero_mul]
    have h4 := w16g_finsum_eq_four u₁ u₂ c d F.h12 F.h1c F.h1d F.h2c F.h2d F.hcd
      (fun U => lam U (Additive.ofMul q) * lam U (Additive.ofMul r)) hf
    have hqr0 : lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) +
        lam c (Additive.ofMul q) * lam c (Additive.ofMul r) +
        lam d (Additive.ofMul q) * lam d (Additive.ofMul r) = 0 := by
      rw [← h4]; exact hqr_sum
    have hqr0' : lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) = 0 := by
      have hh := hqr0
      rw [hr_c, mul_zero, hq_d, zero_mul] at hh
      simpa using hh
    have hdot : qv ⬝ᵥ rv = lam u₁ (Additive.ofMul q) * lam u₁ (Additive.ofMul r) +
        lam u₂ (Additive.ofMul q) * lam u₂ (Additive.ofMul r) := by
      simp [qv, rv, dotProduct, Fin.sum_univ_four]
    rw [hdot, hqr0']
  have hsuppT : s13Supp X T =
      ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
        Set (Subgroup W)) := by
    rw [hT]
    exact w16g_tetra_supp h hH0 hQ3 he F
  intro x hxT hx1
  have hxX : x ∈ X := hTX hxT
  let x' : ↥X := ⟨x, hxX⟩
  have hx'mem : x' ∈ (Subgroup.zpowers q ⊔ Subgroup.zpowers r : Subgroup ↥X) := by
    rw [← Subgroup.mem_map_iff_mem X.subtype_injective, w16g_map_zpowers_sup X q r]
    exact hxT
  obtain ⟨m, n, hmn⟩ : ∃ m n : ℤ, x' = q ^ m * r ^ n := by
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hx'mem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨m, n, by rw [← hyz, ← hm, ← hn]⟩
  let g' : Fin 4 → s13IsoComps X := ![u₁, u₂, c, d]
  have hg'0 : g' 0 = u₁ := rfl
  have hg'1 : g' 1 = u₂ := rfl
  have hg'2 : g' 2 = c := rfl
  have hg'3 : g' 3 = d := rfl
  let v : Fin 4 → ZMod 3 := (m : ZMod 3) • qv + (n : ZMod 3) • rv
  have hzm : ∀ (k : ℤ) (b : ZMod 3), k • b = (k : ZMod 3) * b := by
    intro k b
    rw [← Int.cast_smul_eq_zsmul (R := ZMod 3) k b, smul_eq_mul]
  have hcoord : ∀ i : Fin 4, lam (g' i) (Additive.ofMul x') = v i := by
    intro i
    have h1 : lam (g' i) (Additive.ofMul (q ^ m)) =
        (m : ZMod 3) * lam (g' i) (Additive.ofMul q) := by
      rw [ofMul_zpow, map_zsmul, hzm]
    have h2 : lam (g' i) (Additive.ofMul (r ^ n)) =
        (n : ZMod 3) * lam (g' i) (Additive.ofMul r) := by
      rw [ofMul_zpow, map_zsmul, hzm]
    calc lam (g' i) (Additive.ofMul x')
        = lam (g' i) (Additive.ofMul (q ^ m * r ^ n)) := by rw [hmn]
      _ = lam (g' i) (Additive.ofMul (q ^ m) + Additive.ofMul (r ^ n)) := by rw [ofMul_mul]
      _ = lam (g' i) (Additive.ofMul (q ^ m)) +
          lam (g' i) (Additive.ofMul (r ^ n)) := map_add ..
      _ = (m : ZMod 3) * lam (g' i) (Additive.ofMul q) +
          (n : ZMod 3) * lam (g' i) (Additive.ofMul r) := by rw [h1, h2]
      _ = v i := by fin_cases i <;> simp [v, qv, rv, g', hq_d, hr_c]
  have hvself : v ⬝ᵥ v = 0 := by
    have hh := w16g_dot_self_smul_add qv rv hqq hrr hqr (m : ZMod 3) (n : ZMod 3)
    simpa [v] using hh
  have hvne : v ≠ 0 := by
    intro hv0
    have hx'1 : x' = 1 := by
      refine coord_injective h.hW hp3 hp32 h.hXe F.hl ?_
      intro U
      rw [ofMul_one, map_zero]
      by_cases hUD : U = u₁ ∨ U = u₂ ∨ U = c ∨ U = d
      · rcases hUD with hh | hh | hh | hh
        · rw [hh, ← hg'0, hcoord 0]; exact congrFun hv0 0
        · rw [hh, ← hg'1, hcoord 1]; exact congrFun hv0 1
        · rw [hh, ← hg'2, hcoord 2]; exact congrFun hv0 2
        · rw [hh, ← hg'3, hcoord 3]; exact congrFun hv0 3
      · push Not at hUD
        have hq0 : lam U (Additive.ofMul q) = 0 := by
          by_contra hne
          rcases (F.hq U).mp hne with hh | hh | hh
          · exact hUD.1 hh
          · exact hUD.2.1 hh
          · exact hUD.2.2.1 hh
        have hr0 : lam U (Additive.ofMul r) = 0 := by
          by_contra hne
          rcases (F.hr U).mp hne with hh | hh | hh
          · exact hUD.1 hh
          · exact hUD.2.1 hh
          · exact hUD.2.2.2 hh
        exact w16g_coord_eq_zero_of_mem_sup hq0 hr0 hxT
    exact hx1 (by
      have hh := congrArg (fun z : ↥X => (z : MulAut W)) hx'1
      simpa [x'] using hh)
  have hweight : Fintype.card {i : Fin 4 // v i ≠ 0} = 3 :=
    w16g_weight_of_selfOrthogonal v hvself hvne
  have hg'_inj : Function.Injective g' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [g'] at hij ⊢ <;>
      first
        | rfl
        | exact absurd hij F.h12
        | exact absurd hij.symm F.h12
        | exact absurd hij F.h1c
        | exact absurd hij.symm F.h1c
        | exact absurd hij F.h1d
        | exact absurd hij.symm F.h1d
        | exact absurd hij F.h2c
        | exact absurd hij.symm F.h2c
        | exact absurd hij F.h2d
        | exact absurd hij.symm F.h2d
        | exact absurd hij F.hcd
        | exact absurd hij.symm F.hcd
  have hsubD : s13Supp X (Subgroup.zpowers x) ⊆
      ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
        Set (Subgroup W)) := by
    have hmono : s13Supp X (Subgroup.zpowers x) ⊆ s13Supp X T := by
      intro V hV
      exact ⟨hV.1, fun hbot => hV.2
        (le_bot_iff.mp (hbot ▸ commSub_mono le_rfl (Subgroup.zpowers_le.mpr hxT)))⟩
    rw [hsuppT] at hmono
    exact hmono
  have hncard : (s13Supp X (Subgroup.zpowers x)).ncard = 3 := by
    let S' : Set (s13IsoComps X) :=
      {U | (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers x)}
    have hSeq : s13Supp X (Subgroup.zpowers x) = Subtype.val '' S' := by
      ext U; constructor
      · intro hU
        exact ⟨⟨U, hU.1⟩, hU, rfl⟩
      · rintro ⟨U', hU', rfl⟩
        exact hU'
    have hS'_eq : S' = g' '' {i : Fin 4 | v i ≠ 0} := by
      ext U; constructor
      · intro hU
        have hne : lam U (Additive.ofMul x') ≠ 0 :=
          (w16g_mem_s13Supp_zpowers_iff F.hl hxX U).mp hU
        have hUD : U = u₁ ∨ U = u₂ ∨ U = c ∨ U = d := by
          by_contra hnot
          push Not at hnot
          have hq0 : lam U (Additive.ofMul q) = 0 := by
            by_contra hne'
            rcases (F.hq U).mp hne' with hh | hh | hh
            · exact hnot.1 hh
            · exact hnot.2.1 hh
            · exact hnot.2.2.1 hh
          have hr0 : lam U (Additive.ofMul r) = 0 := by
            by_contra hne'
            rcases (F.hr U).mp hne' with hh | hh | hh
            · exact hnot.1 hh
            · exact hnot.2.1 hh
            · exact hnot.2.2.2 hh
          exact hne (w16g_coord_eq_zero_of_mem_sup hq0 hr0 hxT)
        rcases hUD with hh | hh | hh | hh
        · refine ⟨0, ?_, by rw [hg'0, ← hh]⟩
          change v 0 ≠ 0
          rw [← hcoord 0, hg'0, ← hh]; exact hne
        · refine ⟨1, ?_, by rw [hg'1, ← hh]⟩
          change v 1 ≠ 0
          rw [← hcoord 1, hg'1, ← hh]; exact hne
        · refine ⟨2, ?_, by rw [hg'2, ← hh]⟩
          change v 2 ≠ 0
          rw [← hcoord 2, hg'2, ← hh]; exact hne
        · refine ⟨3, ?_, by rw [hg'3, ← hh]⟩
          change v 3 ≠ 0
          rw [← hcoord 3, hg'3, ← hh]; exact hne
      · rintro ⟨i, hi, rfl⟩
        exact (w16g_mem_s13Supp_zpowers_iff F.hl hxX (g' i)).mpr (by rw [hcoord i]; exact hi)
    have hS'ncard : S'.ncard = 3 := by
      rw [hS'_eq, Set.ncard_image_of_injective _ hg'_inj]
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact hweight
    rw [hSeq, Set.ncard_image_of_injective _ Subtype.coe_injective]
    exact hS'ncard
  rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hXe
    (Subgroup.zpowers_le.mpr hxX)]
  have : Fintype ↥(s13Supp X (Subgroup.zpowers x)) := Fintype.ofFinite _
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  have hsum2 : (∑ U : ↥(s13Supp X (Subgroup.zpowers x)), rk ↥(U.1)) =
      ∑ _ : ↥(s13Supp X (Subgroup.zpowers x)), (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro U _
    have hU := hsubD U.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    rcases hU with hh | hh | hh | hh
    · rw [hh]; exact F.hrk₁
    · rw [hh]; exact F.hrk₂
    · rw [hh]; exact F.hrkc
    · rw [hh]; exact F.hrkd
  rw [hsum2, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hncard]

theorem w16g_tetra_ranks (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    {a : MulAut W} {lam : s13IsoComps X → Additive ↥X →+ ZMod 3} {q r : ↥X}
    {u₁ u₂ c d : s13IsoComps X} (F : TetraFrame A X Q a lam q r u₁ u₂ c d) :
    IsElemAbelianOfRank 3 2
        ↥(Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W)) ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W))) = 8 ∧
      ∀ x ∈ Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W), x ≠ 1 →
        rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6 := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : IsMulCommutative ↥X := h.hXe.1
  set T : Subgroup (MulAut W) :=
    Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W) with hT
  have hTX : T ≤ X := by
    rw [hT]
    exact sup_le (Subgroup.zpowers_le.mpr q.2) (Subgroup.zpowers_le.mpr r.2)
  have hsuppT : s13Supp X T =
      ({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W), (d : Subgroup W)} :
        Set (Subgroup W)) := by
    rw [hT]
    exact w16g_tetra_supp h hH0 hQ3 he F
  have hrk8 : rk ↥(commSub ⊤ T) = 8 := by
    rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hXe hTX, hsuppT]
    have : Fintype ↥({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W),
        (d : Subgroup W)} : Set (Subgroup W)) := Fintype.ofFinite _
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
    have h2 : (∑ U : ↥({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W),
        (d : Subgroup W)} : Set (Subgroup W)), rk ↥(U.1)) =
        ∑ _ : ↥({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W),
        (d : Subgroup W)} : Set (Subgroup W)), (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro U _
      have hU := U.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
      rcases hU with hh | hh | hh | hh
      · rw [hh]; exact F.hrk₁
      · rw [hh]; exact F.hrk₂
      · rw [hh]; exact F.hrkc
      · rw [hh]; exact F.hrkd
    rw [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hcardD : Fintype.card ↥({(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W),
        (d : Subgroup W)} : Set (Subgroup W)) = 4 := by
      have h12' : (u₁ : Subgroup W) ≠ (u₂ : Subgroup W) := fun hh => F.h12 (Subtype.ext hh)
      have h1c' : (u₁ : Subgroup W) ≠ (c : Subgroup W) := fun hh => F.h1c (Subtype.ext hh)
      have h1d' : (u₁ : Subgroup W) ≠ (d : Subgroup W) := fun hh => F.h1d (Subtype.ext hh)
      have h2c' : (u₂ : Subgroup W) ≠ (c : Subgroup W) := fun hh => F.h2c (Subtype.ext hh)
      have h2d' : (u₂ : Subgroup W) ≠ (d : Subgroup W) := fun hh => F.h2d (Subtype.ext hh)
      have hcd' : (c : Subgroup W) ≠ (d : Subgroup W) := fun hh => F.hcd (Subtype.ext hh)
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      rw [Set.ncard_insert_of_notMem (by simp [h12', h1c', h1d']),
        Set.ncard_insert_of_notMem (by simp [h2c', h2d']),
        Set.ncard_insert_of_notMem (by simp [hcd']), Set.ncard_singleton]
    rw [hcardD]
  have hrank : IsElemAbelianOfRank 3 2 ↥T := by
    have hqne0 : (q : MulAut W) ≠ 1 := by
      intro hq1
      exact h.hQ1 (by rw [F.hQq, hq1, Subgroup.zpowers_one_eq_bot])
    have hrne0 : (r : MulAut W) ≠ 1 := by
      intro hr1
      apply h.hQ1
      have hmapbot : Q.map (MulAut.conj a).toMonoidHom = ⊥ := by
        rw [F.hQr, hr1, Subgroup.zpowers_one_eq_bot]
      exact (Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj a).toMonoidHom) Q
        (fun _ _ hh => (MulAut.conj a).injective hh)).mp hmapbot
    have hqne : q ≠ 1 := fun hh => hqne0 (congrArg Subtype.val hh)
    have hrne : r ≠ 1 := fun hh => hrne0 (congrArg Subtype.val hh)
    have hqordc : orderOf q = 3 :=
      orderOf_eq_prime (Subtype.ext (h.hXe.2 (q : MulAut W) q.2)) hqne
    have hrodrc : orderOf r = 3 :=
      orderOf_eq_prime (Subtype.ext (h.hXe.2 (r : MulAut W) r.2)) hrne
    have hqcardc : Nat.card ↥(Subgroup.zpowers q) = 3 := by
      rw [Nat.card_zpowers, hqordc]
    have hrcardc : Nat.card ↥(Subgroup.zpowers r) = 3 := by
      rw [Nat.card_zpowers, hrodrc]
    have hqord0 : orderOf (q : MulAut W) = 3 :=
      orderOf_eq_prime (h.hXe.2 (q : MulAut W) q.2) hqne0
    have hqcard0 : Nat.card ↥(Subgroup.zpowers (q : MulAut W)) = 3 := by
      rw [Nat.card_zpowers, hqord0]
    have hinf : (Subgroup.zpowers q ⊓ Subgroup.zpowers r : Subgroup ↥X) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      by_contra hz1
      have hz0ne : (z : MulAut W) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
      have hz0q : (z : MulAut W) ∈ Subgroup.zpowers (q : MulAut W) := by
        have hh := Subgroup.mem_map_of_mem X.subtype hz.1
        rwa [MonoidHom.map_zpowers] at hh
      have hz0r : (z : MulAut W) ∈ Subgroup.zpowers (r : MulAut W) := by
        have hh := Subgroup.mem_map_of_mem X.subtype hz.2
        rwa [MonoidHom.map_zpowers] at hh
      have hz0X : (z : MulAut W) ∈ X := Subgroup.zpowers_le.mpr q.2 hz0q
      have hz0ord : orderOf (z : MulAut W) = 3 :=
        orderOf_eq_prime (h.hXe.2 (z : MulAut W) hz0X) hz0ne
      have hzcard : Nat.card ↥(Subgroup.zpowers (z : MulAut W)) = 3 := by
        rw [Nat.card_zpowers, hz0ord]
      have hzeq : Subgroup.zpowers (z : MulAut W) = Subgroup.zpowers (q : MulAut W) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz0q)
          (by simp [hqcard0, hzcard])
      have hsuppq : s13Supp X (Subgroup.zpowers (q : MulAut W)) =
          {(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W)} := by
        rw [← F.hQq, F.hsq]
      have hsuppr : s13Supp X (Subgroup.zpowers (r : MulAut W)) =
          {(u₁ : Subgroup W), (u₂ : Subgroup W), (d : Subgroup W)} := by
        rw [← F.hQr, F.hsr]
      have hc_mem : (c : Subgroup W) ∈ s13Supp X (Subgroup.zpowers (z : MulAut W)) := by
        rw [hzeq, hsuppq]; simp
      have hsub : s13Supp X (Subgroup.zpowers (z : MulAut W)) ⊆
          {(u₁ : Subgroup W), (u₂ : Subgroup W), (d : Subgroup W)} := by
        intro V hV
        have hmono : s13Supp X (Subgroup.zpowers (z : MulAut W)) ⊆
            s13Supp X (Subgroup.zpowers (r : MulAut W)) := by
          intro W' hW'
          exact ⟨hW'.1, fun hbot => hW'.2
            (le_bot_iff.mp (hbot ▸ commSub_mono le_rfl (Subgroup.zpowers_le.mpr hz0r)))⟩
        rw [hsuppr] at hmono
        exact hmono hV
      have hthis := hsub hc_mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hthis
      rcases hthis with hh | hh | hh
      · exact F.h1c (Subtype.ext hh.symm)
      · exact F.h2c (Subtype.ext hh.symm)
      · exact F.hcd (Subtype.ext hh)
    have hcardT' : Nat.card ↥(Subgroup.zpowers q ⊔ Subgroup.zpowers r : Subgroup ↥X) = 9 := by
      have hcc := card_sup_mul_card_inf (Subgroup.zpowers q) (Subgroup.zpowers r)
      rw [hinf, Subgroup.card_bot, mul_one, hqcardc, hrcardc] at hcc
      rw [hcc]
    have hmapT : (Subgroup.zpowers q ⊔ Subgroup.zpowers r : Subgroup ↥X).map X.subtype = T := by
      rw [w16g_map_zpowers_sup X q r, hT]
    have hcardT : Nat.card ↥T = 9 := by
      have h1 : Nat.card ↥T =
          Nat.card ↥(Subgroup.zpowers q ⊔ Subgroup.zpowers r : Subgroup ↥X) := by
        rw [← hmapT]
        exact Subgroup.card_map_of_injective X.subtype_injective
      rw [h1, hcardT']
    exact w16g_isElemAbelianOfRank_of_card
      (fun p q' : ↥T => Subtype.ext (congrArg (fun z : ↥X => (z : MulAut W))
        (h.hXe.1.is_comm.comm ⟨p.1, hTX p.2⟩ ⟨q'.1, hTX q'.2⟩)))
      (fun p : ↥T => Subtype.ext (h.hXe.2 p.1 (hTX p.2)))
      hcardT
  have hrk6 : ∀ x ∈ T, x ≠ 1 → rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6 :=
    w16g_tetra_rank_six h hH0 hQ3 he F
  exact ⟨hrank, hrk8, hrk6⟩

end CFSG.LocalAnalysis.WeakClosure81
