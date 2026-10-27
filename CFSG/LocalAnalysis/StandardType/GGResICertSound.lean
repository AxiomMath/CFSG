module

public import CFSG.LocalAnalysis.StandardType.GGResICert

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open GGPoly

section Sound

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem eval_foldr_add' {M : ℕ} (u v : ZMod p) (F : Fin M → GGPoly) :
    eval u v ((List.finRange M).foldr (fun l acc => add (F l) acc) []) =
      ∑ l : Fin M, eval u v (F l) := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  induction (List.finRange M) with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, eval_add, ih, List.map_cons, List.sum_cons]

theorem ggResI_word_mem {N : ℕ} {g : Fin N → (V ≃ₗ[ZMod p] V)} (ws : List (Fin N)) :
    (ws.map g).prod ∈ Subgroup.closure (Set.range g) :=
  (Subgroup.closure (Set.range g)).list_prod_mem fun s hs => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs
    exact Subgroup.subset_closure ⟨i, rfl⟩

theorem ggResI_wstar_sound {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {M : ℕ} (hp2 : p ≠ 2) (hM : (M : ZMod p) ≠ 0) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod p) V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hind : LinearIndependent (ZMod p) h) {E : List GGPoly} (hE : ∀ e ∈ E, eval u v e = 0)
    {typ : GGWTypeI} {ts : List (Fin (n + 1) × List (Fin (n + 1)))} {dd : List GGPoly}
    {lam : List (List GGPoly)} {dz : GGPoly} {cpair : List (List CertV)} {cnz : List CertNV}
    {nz : CertNV} {clam : List (List CertV)}
    (hchk : checkWStarI M (ggStdTableSymI C ib ic e₁ e₂) E typ ts dd lam dz cpair cnz nz clam =
      true) :
    ZS.LinWeyl p (Subgroup.closure (Set.range g)) := by
  have hev : evalT u v (ggStdTableSymI C ib ic e₁ e₂) = ggStdTableI (Int.cast) C ib ic e₁ e₂ u v :=
    ggStdTableI_eval u v C ib ic e₁ e₂
  set Ts := ggStdTableSymI C ib ic e₁ e₂
  set T := ggStdTableI (Int.cast) C ib ic e₁ e₂ u v
  set t : Fin (n + 1) → Fin (n + 1) × List (Fin (n + 1)) := fun i => ts.getD i.val (0, [])
  set d : Fin (n + 1) → ZMod p := fun i => eval u v (dd.getD i.val [])
  set ll : Fin (n + 1) → Fin (n + 1) → ZMod p := fun o i => eval u v ((lam.getD o.val []).getD i.val [])
  simp only [checkWStarI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies]
    at hchk
  obtain ⟨⟨⟨⟨⟨hok, hgen⟩, hdz⟩, hnz⟩, hpair⟩, hlam⟩ := hchk
  have hdz' : eval u v dz ≠ 0 := checkNV_sound u v hM hdz hE
  set w : Fin (n + 1) → (V ≃ₗ[ZMod p] V) := fun i => ((t i).2.map g).prod
  set t' : Fin (n + 1) → (V ≃ₗ[ZMod p] V) := fun i => w i * g (t i).1 * (w i)⁻¹
  set H : Fin (n + 1) → V := fun i => ggFPi (RingHom.id (ZMod p)) h 0 (ggFH T (t i))
  set A : Fin (n + 1) → Module.Dual (ZMod p) V := fun i => ggFFun (RingHom.id (ZMod p)) α (ggFC T (t i))
  have hd : ∀ i, d i ≠ 0 := fun i => checkNV_sound u v hM (hnz i) hE
  have ht' : ∀ i x, t' i x = x - A i x • H i := fun i x => ggF_conj' hT hg h2 (t i) x
  set H' : Fin (n + 1) → V := fun i => d i • H i
  set A' : Fin (n + 1) → Module.Dual (ZMod p) V := fun i => (d i)⁻¹ • A i
  have ht'' : ∀ i x, t' i x = x - A' i x • H' i := by
    intro i x
    rw [ht' i x]
    simp only [A', H', LinearMap.smul_apply, smul_eq_mul, smul_smul]
    rw [show (d i)⁻¹ * (A i) x * d i = (A i) x by
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (hd i), one_mul]]
  obtain ⟨Mx, hW, hC⟩ := ggWCartanI_spec typ (n + 1) hok
  have hP : ∀ i j, A' j (H' i) = (ggWCartanI typ (n + 1) i j : ZMod p) := by
    intro i j
    have h1 := checkV_sound u v hM (hpair i j) hE
    rw [eval_sub, eval_mul, eval_mul, eval_const, eval_frootAt, evalV_fC, evalV_fH, hev] at h1
    have hAH : A j (H i) = ggFRootAt T (ggFC T (t j)) (ggFH T (t i)) :=
      ggFFun_pi hT (ggFC T (t j)) (ggFH T (t i))
    simp only [A', H', LinearMap.smul_apply, map_smul, smul_eq_mul, hAH]
    have hdj := hd j
    field_simp
    linear_combination h1
  have hindH : LinearIndependent (ZMod p) H' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc o
    have hcoord : ∀ l : Fin (n + 1), ∑ i, c i * d i * (ggFH T (t i)).get l.castSucc = 0 := by
      have hsum : ∑ i, c i • H' i =
          ∑ l : Fin (n + 1), (∑ i, c i * d i * (ggFH T (t i)).get l.castSucc) • h l := by
        simp only [H', H, ggFPi_zero, RingHom.id_apply, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
      rw [hsum] at hc
      exact fun l => (Fintype.linearIndependent_iff.mp hind) _ hc l
    have hZl : ∀ i o, ∑ l : Fin (n + 1), (ggFH T (t i)).get l.castSucc * ll l o =
        if i = o then eval u v dz else 0 := by
      intro i o
      have h1 := checkV_sound u v hM (hlam i o) hE
      rw [eval_sub, eval_foldr_add'] at h1
      simp only [eval_mul, eval_fH, hev] at h1
      rw [sub_eq_zero] at h1
      rw [h1]
      split_ifs <;> simp
    have hco : c o * d o * eval u v dz = 0 := by
      calc c o * d o * eval u v dz = ∑ i, c i * d i * (if i = o then eval u v dz else 0) := by
            simp
        _ = ∑ i, c i * d i * ∑ l : Fin (n + 1), (ggFH T (t i)).get l.castSucc * ll l o := by
          simp only [hZl]
        _ = ∑ l : Fin (n + 1), (∑ i, c i * d i * (ggFH T (t i)).get l.castSucc) * ll l o := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
          ring
        _ = 0 := by simp [hcoord]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hco).resolve_right hdz')).resolve_right (hd o)
  have hW' := ggResI_linWeyl_T hp2 hW hC t' H' A' ht'' hP hindH
  have hle : Subgroup.closure (Set.range t') ≤ Subgroup.closure (Set.range g) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ggF_conj_mem (t i).1 (t i).2
  have hge : Subgroup.closure (Set.range g) ≤ Subgroup.closure (Set.range t') := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    simp only [wstarGen, List.all_eq_true, List.mem_finRange, true_implies] at hgen
    have hk := hgen k
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and,
      decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true] at hk
    rcases hk with ⟨m, hm⟩ | ⟨i, hi, hws⟩
    · have hm' : t m = (k, []) := hm
      have : t' m = g k := by
        show w m * g (t m).1 * (w m)⁻¹ = g k
        simp only [w, hm', List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
      rw [← this]
      exact Subgroup.subset_closure ⟨m, rfl⟩
    · have hwi : w i ∈ Subgroup.closure (Set.range t') := by
        refine (Subgroup.closure (Set.range t')).list_prod_mem fun s hs => ?_
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
        obtain ⟨m, hm⟩ := hws l hl
        have hm' : t m = (l, []) := hm
        have : t' m = g l := by
          show w m * g (t m).1 * (w m)⁻¹ = g l
          simp only [w, hm', List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
        rw [← this]
        exact Subgroup.subset_closure ⟨m, rfl⟩
      have hi' : (t i).1 = k := hi
      have hgk : g k = (w i)⁻¹ * t' i * w i := by
        show g k = (w i)⁻¹ * (w i * g (t i).1 * (w i)⁻¹) * w i
        rw [hi']
        group
      rw [hgk]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwi)
        (Subgroup.subset_closure ⟨i, rfl⟩)) hwi
  rwa [le_antisymm hle hge] at hW'

theorem ggStdTableSymI_get_eval {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (u v : ZMod p) (k : Fin (n + 1)) (l : Fin (n + 2)) :
    eval u v ((ggStdTableSymI C ib ic e₁ e₂ k).get l) =
      ((ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) k).get l := by
  rw [← get_evalV]
  exact congrArg (fun T => (T k).get l) (ggStdTableI_eval u v C ib ic e₁ e₂)

theorem ggResI_concl_of_triple {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {e₁ e₂ : ℤ} (hp5 : 5 ≤ p) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    {j j₂ : Fin n} (hj : j ≠ ib) (hj₂ : j₂ ≠ ib) (tws : List (Fin (n + 1)))
    (hbad : GGTriBad p fun i k => (RingHom.id (ZMod p))
      (![![((ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) j.castSucc).get j.castSucc.castSucc,
          ((ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) j.castSucc).get j₂.castSucc.castSucc,
          ggFA (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws) j.castSucc],
        ![((ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) j₂.castSucc).get j.castSucc.castSucc,
          ((ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) j₂.castSucc).get j₂.castSucc.castSucc,
          ggFA (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws) j₂.castSucc],
        ![ggFDualAt (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)
            (ggFC (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)) j.castSucc,
          ggFDualAt (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)
            (ggFC (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)) j₂.castSucc,
          ggFDualAt (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)
            (ggFC (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)) j.castSucc * 0 +
            2]] i k)) :
    GGResIConcl g h α ib x := by
  right; left
  refine ⟨hp5, _, ggResI_word_mem tws, j, j₂, hj, hj₂, ?_⟩
  rw [ggF_triMat_eq hT hg h2 j.castSucc j₂.castSucc tws]
  exact hbad

theorem ggResI_checkTree_sound {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {e₁ e₂ : ℤ} {M : ℕ} (hp5 : 5 ≤ p) (hM : (M : ZMod p) ≠ 0)
    {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod p) h) :
    ∀ (Tr : GGTreeI n) (E : List GGPoly),
      checkTreeI M (ggStdTableSymI C ib ic e₁ e₂) ib E Tr = true →
      (∀ e ∈ E, eval u v e = 0) → GGResIConcl g h α ib x := by
  have hp2 : p ≠ 2 := by omega
  have hev : evalT u v (ggStdTableSymI C ib ic e₁ e₂) = ggStdTableI (Int.cast) C ib ic e₁ e₂ u v :=
    ggStdTableI_eval u v C ib ic e₁ e₂
  intro Tr
  induction Tr with
  | tv t₁ t₂ l₀ z cs n₁ n₂ nY =>
    intro E hchk hE
    simp only [checkTreeI, checkTVI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnY⟩ := hchk
    left
    refine ggF_tvH (φ := RingHom.id (ZMod p)) hp2 hT hg h2 t₁ t₂ l₀ (ggFUnit z) ?_ ?_ ?_ ?_
    · intro l
      have := checkV_sound u v hM (hmin l) hE
      rw [eval_sub, eval_mul, eval_mul, eval_fH, eval_fH, eval_fH, eval_fH, hev] at this
      exact this
    · have := checkNV_sound u v hM hn₁ hE
      rwa [eval_fH, hev] at this
    · have := checkNV_sound u v hM hn₂ hE
      rwa [eval_fH, hev] at this
    · have := checkNV_sound u v hM hnY hE
      rw [eval_sub, eval_mul, eval_mul, eval_fH, eval_fH, eval_frootAt, eval_frootAt, evalV_fC,
        evalV_fC, evalV_funit, hev] at this
      exact this
  | tvk t₁ t₂ o₀ l cs n₁ n₂ nC =>
    intro E hchk hE
    simp only [checkTreeI, checkTVkI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnC⟩ := hchk
    left
    refine ggF_tvkV (φ := RingHom.id (ZMod p)) hp2 hT hg h2 hspan hind t₁ t₂ o₀ l ?_ ?_ ?_ ?_
    · intro o
      have := checkV_sound u v hM (hmin o) hE
      rw [eval_sub, eval_mul, eval_mul, eval_fdualAt, eval_fdualAt, eval_fdualAt, eval_fdualAt,
        evalV_fC, evalV_fC, hev] at this
      exact this
    · have := checkNV_sound u v hM hn₁ hE
      rwa [eval_fdualAt, evalV_fC, hev] at this
    · have := checkNV_sound u v hM hn₂ hE
      rwa [eval_fdualAt, evalV_fC, hev] at this
    · have := checkNV_sound u v hM hnC hE
      rw [eval_sub, eval_mul, eval_mul, eval_fdualAt, eval_fdualAt, evalV_fC, evalV_fC, eval_fH,
        eval_fH, hev] at this
      exact this
  | tri t j' cs =>
    intro E hchk hE
    obtain ⟨tk, tws⟩ := t
    simp only [checkTreeI, checkTRI, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hchk
    obtain ⟨⟨ht, hj'⟩, hcs⟩ := hchk
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    refine ggResI_concl_of_triple hp5 hg h2 hT hj hj₂ tws (ggTriBad_of_pair ?_)
    set P := pairPoly (ggStdTableSymI C ib ic e₁ e₂) (j.castSucc, tws) j₂.castSucc with hPdef
    have hk : ∀ k : ℕ, k < 5 → eval u v P ≠ (k : ZMod p) := by
      intro k hk heq
      have := checkNV_sound u v hM (hcs k hk) hE
      rw [eval_sub, eval_const, heq] at this
      exact this (by push_cast; ring)
    have hPv : eval u v P = ggFA (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)
        j₂.castSucc * ggFDualAt (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)
          (ggFC (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)) j₂.castSucc := by
      rw [hPdef, pairPoly, eval_mul, eval_fA, eval_fdualAt, evalV_fC, hev]
    simp only [RingHom.id_apply, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero]
    rw [← hPv]
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h0 | h0 | h0 | h0 | h0
    · exact hk 0 (by norm_num) (by rw [h0]; norm_num)
    · exact hk 1 (by norm_num) (by rw [h0]; norm_num)
    · exact hk 2 (by norm_num) (by rw [h0]; norm_num)
    · exact hk 3 (by norm_num) (by rw [h0]; norm_num)
    · exact hk 4 (by norm_num) (by rw [h0]; norm_num)
  | triple t j' nt =>
    intro E hchk hE
    obtain ⟨tk, tws⟩ := t
    simp only [checkTreeI, checkTripleI, Bool.and_eq_true] at hchk
    obtain ⟨⟨ht, hj'⟩, hnt⟩ := hchk
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    refine ggResI_concl_of_triple hp5 hg h2 hT hj hj₂ tws (ggTriBad_of_tau ?_)
    have := checkNV_sound u v hM hnt hE
    rw [triTau, eval_sub, eval_mul, eval_mul, eval_mul, eval_mul, eval_fA, eval_fA,
      eval_fdualAt, eval_fdualAt, evalV_fC, ggStdTableSymI_get_eval, ggStdTableSymI_get_eval,
      hev] at this
    simp only [RingHom.id_apply, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero]
    intro heq
    exact this (sub_eq_zero.mpr heq)
  | wstar typ ts dd lam dz cpair cnz nz clam =>
    intro E hchk hE
    right; right; right
    exact ggResI_wstar_sound hp2 hM hg h2 hT hind hE hchk
  | split s₁ s₂ m₁ m₂ cv l r ihl ihr =>
    intro E hchk hE
    simp only [checkTreeI, Bool.and_eq_true] at hchk
    obtain ⟨⟨hcv, hl⟩, hr⟩ := hchk
    have h0 := checkV_sound u v hM hcv hE
    rw [eval_mul, eval_pow, eval_pow] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · refine ihl (E ++ [s₁]) hl fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact hE e he
      · rw [List.mem_singleton.mp he]
        by_contra hs
        exact pow_ne_zero _ hs h1
    · refine ihr (E ++ [s₂]) hr fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact hE e he
      · rw [List.mem_singleton.mp he]
        by_contra hs
        exact pow_ne_zero _ hs h1
  | empty cv =>
    intro E hchk hE
    have h0 := checkV_sound u v hM hchk hE
    rw [eval_const, Int.cast_one] at h0
    exact absurd h0 one_ne_zero
  | triOr t j' c₀ c₁ c₂ c₃ c₄ ih₀ ih₁ ih₂ ih₃ ih₄ =>
    intro E hchk hE
    simp only [checkTreeI, Bool.and_eq_true] at hchk
    obtain ⟨⟨ht, hj'⟩, ⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩⟩ := hchk
    set P := pairPoly (ggStdTableSymI C ib ic e₁ e₂) t j' with hPdef
    have hext : ∀ k : ℕ, eval u v P = (k : ZMod p) →
        ∀ e ∈ E ++ [sub P (const (k : ℤ))], eval u v e = 0 := by
      intro k hk e he
      rcases List.mem_append.mp he with he | he
      · exact hE e he
      · rw [List.mem_singleton.mp he, eval_sub, eval_const, hk]
        push_cast
        ring
    by_cases hP : eval u v P ∈ ({0, 1, 2, 3, 4} : Set (ZMod p))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with h0 | h0 | h0 | h0 | h0
      · exact ih₀ _ h₀ (hext 0 (by rw [h0]; norm_num))
      · exact ih₁ _ h₁ (hext 1 (by rw [h0]; norm_num))
      · exact ih₂ _ h₂ (hext 2 (by rw [h0]; norm_num))
      · exact ih₃ _ h₃ (hext 3 (by rw [h0]; norm_num))
      · exact ih₄ _ h₄ (hext 4 (by rw [h0]; norm_num))
    · obtain ⟨tk, tws⟩ := t
      obtain ⟨j, rfl, hj⟩ := inJ_spec ht
      obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
      refine ggResI_concl_of_triple hp5 hg h2 hT hj hj₂ tws (ggTriBad_of_pair ?_)
      have hPv : eval u v P = ggFA (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)
          j₂.castSucc * ggFDualAt (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)
            (ggFC (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)) j₂.castSucc := by
        rw [hPdef, pairPoly, eval_mul, eval_fA, eval_fdualAt, evalV_fC, hev]
      simp only [RingHom.id_apply, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_zero]
      rw [← hPv]
      exact hP

end Sound

end CFSG.StandardType
