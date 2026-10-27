module

public import CFSG.Walter.Ree.Bombieri.DetSound
public import CFSG.Walter.Ree.Bombieri.Resultant

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P hiding X
open Polynomial

theorem allSome_spec : ∀ {l : List (Option F3P)} {ys : List F3P}, allSome l = some ys →
    ys.length = l.length ∧ ∀ i (hi : i < l.length) (hi' : i < ys.length), l[i] = some ys[i]
  | [], ys, h => by
    simp only [allSome, Option.some.injEq] at h
    subst h; simp
  | none :: _, _, h => by simp [allSome] at h
  | some a :: l, ys, h => by
    simp only [allSome, Option.map_eq_some_iff] at h
    obtain ⟨zs, hzs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := allSome_spec hzs
    refine ⟨by simp [h1], fun i hi hi' => ?_⟩
    rcases i with _ | i
    · simp
    · simp only [List.getElem_cons_succ]
      exact h2 i (by simpa using hi) (by simpa using hi')

section

variable {K : Type*} [Field K] [CharP K 3] {T : Tab} {r : K}
  (hm : PE.IsMul (castThree K) r (mulT T))
include hm

theorem ev_ne_zero_of_unitT {a : F3P} (ha : a.Valid) (h : unitT T a = true) :
    F3P.ev (castThree K) r a ≠ 0 := by
  intro h0
  have h1 := congrArg (F3P.ev (castThree K) r) (beq_iff_eq.mp h)
  rw [(hm _ _ ha (valid_normalize _)).2, h0, zero_mul, ev_one] at h1
  exact zero_ne_one h1

theorem vandProd_spec {pts : List F3P} (hv : AllValid pts)
    (h : unitT T (vandProd T pts) = true) :
    (∀ x ∈ pts, F3P.ev (castThree K) r x ≠ 0) ∧ (pts.map (F3P.ev (castThree K) r)).Nodup := by
  set diffs := pts.zipIdx.flatMap fun (x, i) => (pts.drop (i + 1)).map fun y => sub x y
  have hdv : AllValid diffs := by
    intro a ha
    simp only [diffs, List.mem_flatMap, List.mem_map] at ha
    obtain ⟨⟨x, i⟩, hx, y, hy, rfl⟩ := ha
    have hx' : x ∈ pts := by
      obtain ⟨k, hk, hk'⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_zipIdx] at hk'
      have : pts[k]'(by simpa using hk) = x := (Prod.ext_iff.mp hk').1
      rw [← this]
      exact List.getElem_mem _
    exact valid_sub (hv x hx') (hv y (List.mem_of_mem_drop hy))
  have hall : AllValid (pts ++ diffs) := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hv a h
    · exact hdv a h
  obtain ⟨hpv, hpe⟩ := prodT_spec hm hall
  have hne := ev_ne_zero_of_unitT hm hpv (by rw [← h]; rfl)
  rw [hpe] at hne
  have hmem : ∀ a ∈ pts ++ diffs, F3P.ev (castThree K) r a ≠ 0 := by
    intro a ha h0
    apply hne
    rw [List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨a, ha, h0⟩
  refine ⟨fun x hx => hmem x (List.mem_append_left _ hx), ?_⟩
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at heq
  have hd : sub pts[i] pts[j] ∈ diffs := by
    simp only [diffs, List.mem_flatMap, List.mem_map]
    refine ⟨(pts[i], i), ?_, pts[j], ?_, rfl⟩
    · rw [List.mem_iff_getElem]
      exact ⟨i, by simpa using hi, by simp⟩
    · rw [List.mem_iff_getElem]
      exact ⟨j - (i + 1), by simp; omega, by simp; congr 1; omega⟩
  apply hmem _ (List.mem_append_right _ hd)
  rw [ev_sub (hv _ (List.getElem_mem _)) (hv _ (List.getElem_mem _)), heq, sub_self]

theorem interp_eq {xs ys p : List F3P} {Q : K[X]} (hxv : AllValid xs) (hpv : AllValid p)
    (hnd : (xs.map (F3P.ev (castThree K) r)).Nodup) (hlen : ys.length = xs.length)
    (hQ : ∀ i (hi : i < xs.length) (hi' : i < ys.length),
      Q.eval (F3P.ev (castThree K) r xs[i]) = F3P.ev (castThree K) r ys[i])
    (hp : (List.zip xs ys).all (fun xy => horner T p xy.1 == xy.2) = true)
    (hdeg : Q.natDegree < xs.length) (hplen : p.length ≤ xs.length) :
    Q = toPolyK (castThree K) r p := by
  have hxs : 0 < xs.length := by omega
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q _
    (ι := Fin xs.length) (f := fun i => F3P.ev (castThree K) r xs[i]) ?_ ?_ ?_
  · intro i j hij
    have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
      (hi := by simp) (hj := by simp)).mp (by simpa using hij)
    exact Fin.ext this
  · intro i
    have hiy : (i : ℕ) < ys.length := by omega
    show Q.eval (F3P.ev (castThree K) r xs[(i : ℕ)]) =
      (toPolyK (castThree K) r p).eval (F3P.ev (castThree K) r xs[(i : ℕ)])
    rw [hQ i i.2 hiy]
    rw [List.all_eq_true] at hp
    have hz := hp (xs[(i : ℕ)], ys[(i : ℕ)])
      (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩)
    simp only [beq_iff_eq] at hz
    rw [← (horner_spec hm (hxv _ (List.getElem_mem _)) hpv).2, hz]
  · simp only [Fintype.card_fin]
    refine max_lt hdeg ?_
    have := natDegree_toPolyK_le (ι := castThree K) (r := r) p
    omega

omit hm in
theorem bezout_eq {pts s t : List F3P} {A B Q1 Q2 : K[X]} {g : K}
    (hnd : (pts.map (F3P.ev (castThree K) r)).Nodup)
    (h : ∀ x ∈ pts, ((toPolyK (castThree K) r s).eval (F3P.ev (castThree K) r x)) * A.eval
      (F3P.ev (castThree K) r x) + (toPolyK (castThree K) r t).eval (F3P.ev (castThree K) r x) *
        B.eval (F3P.ev (castThree K) r x) = g)
    (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ 2 * D) (hs : s.length ≤ 2 * D) (ht : t.length ≤ D)
    (hlen : 3 * D + 1 ≤ pts.length) (hQ1 : Q1 = toPolyK (castThree K) r s)
    (hQ2 : Q2 = toPolyK (castThree K) r t) :
    Q1 * A + Q2 * B = C g := by
  subst hQ1 hQ2
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
    (ι := Fin pts.length) (f := fun i => F3P.ev (castThree K) r pts[i]) ?_ ?_ ?_
  · intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
      (hi := by simp) (hj := by simp)).mp (by simpa using hij))
  · intro i
    simp only [eval_add, eval_mul, eval_C]
    exact h _ (List.getElem_mem _)
  · simp only [Fintype.card_fin, natDegree_C]
    refine max_lt ?_ (by omega)
    have h1 := natDegree_toPolyK_le (ι := castThree K) (r := r) s
    have h2 := natDegree_toPolyK_le (ι := castThree K) (r := r) t
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact natDegree_mul_le.trans_lt (by omega)
    · exact natDegree_mul_le.trans_lt (by omega)


end

section

variable {K : Type*} [Field K] [CharP K 3] {T : Tab} {r : K}

theorem ev_ptVarsF (c0 c1 c2 c3 t : F3P) :
    F3P.ev (castThree K) r ∘ ptVarsF c0 c1 c2 c3 t =
      Elim.ptVars (F3P.ev (castThree K) r c0) (F3P.ev (castThree K) r c1)
        (F3P.ev (castThree K) r c2) (F3P.ev (castThree K) r c3) (F3P.ev (castThree K) r t) := by
  funext i
  rcases i with _ | _ | _ | _ | _ | i <;> simp [ptVarsF, Elim.ptVars, ev_zero]

theorem valid_ptVarsF {c0 c1 c2 c3 t : F3P} (h0 : c0.Valid) (h1 : c1.Valid) (h2 : c2.Valid)
    (h3 : c3.Valid) (ht : t.Valid) : ∀ i, (ptVarsF c0 c1 c2 c3 t i).Valid := by
  intro i
  rcases i with _ | _ | _ | _ | _ | i <;> simp [ptVarsF, valid_zero, *]

theorem allValid_codePts (n : ℕ) : AllValid (codePts n) := by
  intro a ha
  simp only [codePts, List.mem_map] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact valid_normalize _

theorem specCheck_sound (hT : tabCheck T = true) (hf : T.f.Valid)
    (hr : F3P.ev (castThree K) r T.f = 0) {c0 c1 c2 c3 c4 : F3P}
    (h : specCheck T c0 c1 c2 c3 c4 = true) :
    Elim.evA5 ![F3P.ev (castThree K) r (normalize c0), F3P.ev (castThree K) r (normalize c1),
      F3P.ev (castThree K) r (normalize c2), F3P.ev (castThree K) r (normalize c3),
      F3P.ev (castThree K) r (normalize c4)] Elim.H0 ≠ 0 := by
  have hm := F3P.isMul_mulT hT hf hr
  simp only [specCheck] at h
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i ys ys' hys hys'
  set ev := F3P.ev (castThree K) r with hev
  set n0 := normalize c0
  set n1 := normalize c1
  set n2 := normalize c2
  set n3 := normalize c3
  set n4 := normalize c4
  have v0 : n0.Valid := valid_normalize _
  have v1 : n1.Valid := valid_normalize _
  have v2 : n2.Valid := valid_normalize _
  have v3 : n3.Valid := valid_normalize _
  have v4 : n4.Valid := valid_normalize _
  set zs : Fin 5 → K := ![ev n0, ev n1, ev n2, ev n3, ev n4] with hzs
  set φ := Elim.evA5 zs with hφ
  set xs := codePts (D + 1) with hxs
  have hxv : AllValid xs := allValid_codePts _
  have hxlen : xs.length = D + 1 := by simp [xs, codePts]
  obtain ⟨hyl, hyv⟩ := allSome_spec hys
  obtain ⟨hyl', hyv'⟩ := allSome_spec hys'
  simp only [List.length_map] at hyl hyl'
  have hval : ∀ i (hi : i < xs.length) (hi' : i < ys.length),
      ys[i].Valid ∧ (Elim.P.map φ).eval (ev xs[i]) = ev ys[i] := by
    intro i hi hi'
    have := hyv i (by simpa using hi) hi'
    simp only [List.getElem_map] at this
    obtain ⟨hv, he⟩ := detAt_spec hm (valid_ptVarsF v0 v1 v2 v3 (hxv _ (List.getElem_mem _)))
      this
    rw [← hev] at he
    refine ⟨hv, ?_⟩
    rw [eval_map, Elim.eval_P, ← he, hev, ev_ptVarsF]
    rfl
  have hval' : ∀ i (hi : i < xs.length) (hi' : i < ys'.length),
      ys'[i].Valid ∧ (Elim.P'.map φ).eval (ev xs[i]) = ev ys'[i] := by
    intro i hi hi'
    have := hyv' i (by simpa using hi) hi'
    simp only [List.getElem_map] at this
    obtain ⟨hv, he⟩ := detAt_spec hm (valid_ptVarsF v1 v2 v3 v4 (hxv _ (List.getElem_mem _)))
      this
    rw [← hev] at he
    refine ⟨hv, ?_⟩
    rw [eval_map, Elim.eval_P', ← he, hev, ev_ptVarsF]
    rfl
  simp only [specCore, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpl, hp'l⟩, hsl⟩, htl⟩, hint⟩, hint'⟩, hlc⟩, hvx⟩, hvb⟩, hg⟩, hbez⟩ := h
  set p := List.map F3P.normalize (interp T xs ys) with hp
  set p' := List.map F3P.normalize (interp T xs ys') with hp'
  set ζ := zetaF T n0 n1 with hζ
  set bpts := codePts (3 * D + 1) with hbpts
  set p1 := (List.range (2 * D + 1)).map fun n =>
    if n % 2 = 0 then mulT T (p'.getD (D - n / 2) zero) (PE.powM (mulT T) ζ (D - n / 2))
    else zero with hp1
  set gst := pxgcd T p p1 with hgst
  set s := List.map F3P.normalize (ptrim gst.2.1) with hs
  set t := List.map F3P.normalize (ptrim gst.2.2) with ht
  set g := F3P.normalize (gst.1.headD zero) with hg'
  have hpv : AllValid p := allValid_map_normalize _
  have hp'v : AllValid p' := allValid_map_normalize _
  have hsv : AllValid s := allValid_map_normalize _
  have htv : AllValid t := allValid_map_normalize _
  have hgv : g.Valid := valid_normalize _
  obtain ⟨-, hnd⟩ := vandProd_spec hm hxv hvx
  have hdegP : (Elim.P.map φ).natDegree ≤ D :=
    (natDegree_map_le).trans Elim.natDegree_P
  have hdegP' : (Elim.P'.map φ).natDegree ≤ D :=
    (natDegree_map_le).trans Elim.natDegree_P'
  have hA : Elim.P.map φ = toPolyK (castThree K) r p :=
    interp_eq hm hxv hpv hnd hyl (fun i hi hi' => (hval i hi hi').2) hint (by omega) (by omega)
  have hA' : Elim.P'.map φ = toPolyK (castThree K) r p' :=
    interp_eq hm hxv hp'v hnd hyl' (fun i hi hi' => (hval' i hi hi').2) hint' (by omega)
      (by omega)
  have hlc' : (Elim.P.map φ).coeff D ≠ 0 := by
    rw [hA, coeff_toPolyK]
    have hD : D < p.length := by omega
    have hget : p.getD D zero = p[D] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hD, Option.getD_some]
    exact ev_ne_zero_of_unitT hm (hpv _ (by rw [hget]; exact List.getElem_mem _)) hlc
  have hnatA : (Elim.P.map φ).natDegree = D :=
    le_antisymm hdegP (le_natDegree_of_ne_zero hlc')
  obtain ⟨hbne, hbnd⟩ := vandProd_spec hm (allValid_codePts _) hvb
  have hbv : AllValid bpts := allValid_codePts _
  have hζv : ζ.Valid := by
    simp only [ζ, zetaF]
    exact valid_add valid_one (hm _ _ v1 (hm _ _ v0 v0).1).1
  have hζe : φ Elim.ζA = F3P.ev (castThree K) r ζ := by
    rw [hφ, Elim.evA5_ζA, hζ, zetaF, ev_add valid_one (hm _ _ v1 (hm _ _ v0 v0).1).1, ev_one,
      (hm _ _ v1 (hm _ _ v0 v0).1).2, (hm _ _ v0 v0).2]
    simp [zs, hev, pow_two]
  have hB : ∀ x ∈ bpts, (toPolyK (castThree K) r s).eval (F3P.ev (castThree K) r x) *
      (Elim.P.map φ).eval (F3P.ev (castThree K) r x) +
      (toPolyK (castThree K) r t).eval (F3P.ev (castThree K) r x) *
        (Elim.P1.map φ).eval (F3P.ev (castThree K) r x) = F3P.ev (castThree K) r g := by
    intro x hx
    rw [List.all_eq_true] at hbez
    have hb := hbez x hx
    simp only [bezoutAt, Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨hxi, hb⟩ := hb
    have hxv' := hbv x hx
    set xi := F3P.normalize (invT T x)
    have hxiv : xi.Valid := valid_normalize _
    have hxx : F3P.ev (castThree K) r x * F3P.ev (castThree K) r xi = 1 := by
      rw [← (hm _ _ hxv' hxiv).2, hxi, ev_one]
    have hx0 : F3P.ev (castThree K) r x ≠ 0 := hbne x hx
    have hxi2 : (mulT T xi xi).Valid := (hm _ _ hxiv hxiv).1
    have hζx : (mulT T ζ (mulT T xi xi)).Valid := (hm _ _ hζv hxi2).1
    obtain ⟨hs1, hs2⟩ := horner_spec hm hxv' hsv
    obtain ⟨hp1v, hp2⟩ := horner_spec hm hxv' hpv
    obtain ⟨ht1, ht2⟩ := horner_spec hm hxv' htv
    obtain ⟨hq1, hq2⟩ := horner_spec hm hζx hp'v
    obtain ⟨hw1, hw2⟩ := PE.powM_spec hm hxv' (2 * D)
    have hy1 : φ Elim.ζA = (F3P.ev (castThree K) r ζ * F3P.ev (castThree K) r xi ^ 2) *
        F3P.ev (castThree K) r x ^ 2 := by
      rw [hζe, mul_assoc, ← mul_pow, mul_comm (F3P.ev (castThree K) r xi), hxx, one_pow,
        mul_one]
    have h1 := congrArg (F3P.ev (castThree K) r) hb
    simp only [p1At] at h1
    rw [ev_add (hm _ _ hs1 hp1v).1 (hm _ _ ht1 (hm _ _ hw1 hq1).1).1,
      (hm _ _ hs1 hp1v).2, (hm _ _ ht1 (hm _ _ hw1 hq1).1).2, (hm _ _ hw1 hq1).2,
      hs2, hp2, ht2, hq2, hw2, (hm _ _ hζv hxi2).2, (hm _ _ hxiv hxiv).2] at h1
    have he' : Polynomial.eval₂ φ
        (F3P.ev (castThree K) r ζ * F3P.ev (castThree K) r xi ^ 2) Elim.P' =
        (toPolyK (castThree K) r p').eval
          (F3P.ev (castThree K) r ζ * F3P.ev (castThree K) r xi ^ 2) := by
      rw [← hA', eval_map]
    have hP1e : (Elim.P1.map φ).eval (F3P.ev (castThree K) r x) =
        F3P.ev (castThree K) r x ^ (2 * D) * (toPolyK (castThree K) r p').eval
          (F3P.ev (castThree K) r ζ * F3P.ev (castThree K) r xi ^ 2) := by
      rw [eval_map, hφ, Elim.eval_P1 _ zs (hφ ▸ hy1), ← hφ, he']
    rw [← h1, hA, hP1e, pow_two]
  have hbl : bpts.length = 3 * D + 1 := by simp [bpts, codePts]
  have hbez' := bezout_eq (A := Elim.P.map φ) (B := Elim.P1.map φ) hbnd hB hdegP
    (natDegree_map_le.trans Elim.natDegree_P1) (by simpa using hsl) (by simpa using htl)
    (le_of_eq (by simp [codePts])) rfl rfl
  have hg0 : F3P.ev (castThree K) r g ≠ 0 := ev_ne_zero_of_unitT hm hgv hg
  have hcop : IsCoprime (Elim.P.map φ) (Elim.P1.map φ) := by
    refine ⟨C (F3P.ev (castThree K) r g)⁻¹ * toPolyK (castThree K) r s,
      C (F3P.ev (castThree K) r g)⁻¹ * toPolyK (castThree K) r t, ?_⟩
    calc C (F3P.ev (castThree K) r g)⁻¹ * toPolyK (castThree K) r s * Elim.P.map φ +
          C (F3P.ev (castThree K) r g)⁻¹ * toPolyK (castThree K) r t * Elim.P1.map φ =
        C (F3P.ev (castThree K) r g)⁻¹ * (toPolyK (castThree K) r s * Elim.P.map φ +
          toPolyK (castThree K) r t * Elim.P1.map φ) := by ring
      _ = 1 := by rw [hbez', ← C_mul, inv_mul_cancel₀ hg0, C_1]
  rw [Elim.H0_eq, ← resultant_map_map]
  have hk : 2 * Elim.D = (Elim.P1.map φ).natDegree + (2 * Elim.D - (Elim.P1.map φ).natDegree) :=
    by have := (natDegree_map_le (f := φ) (p := Elim.P1)).trans Elim.natDegree_P1; omega
  rw [hk, resultant_add_right_deg _ _ _ _ _ le_rfl]
  refine mul_ne_zero (pow_ne_zero _ hlc') ?_
  have : Elim.D = (Elim.P.map φ).natDegree := hnatA.symm
  rw [this]
  exact resultant_ne_zero _ _ hcop
end

end Spec

end CFSG.Walter.Ree.Bombieri
