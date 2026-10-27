module

public import CFSG.LocalAnalysis.StandardType.GGTWLowEnum
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma l05nL6_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

lemma l05nL6_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nL6_form_apply a (v - w), map_sub, l05nL6_form_apply a v, l05nL6_form_apply a w]

lemma l05nL6_dot_smul {p N : ℕ} (a : GGDepAE p N) (k : ZMod p) (v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nL6_form_apply a (k • v), map_smul, l05nL6_form_apply a v]
  simp

lemma l05nL6_refl_invol {p N : ℕ} (c f : GGDepAE p N) (h : ggDepAdot f c = 2) :
    ggDepARefl c f * ggDepARefl c f = 1 := by
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nPT_refl_apply, Pi.sub_apply, Pi.smul_apply,
    l05nL6_dot_sub, l05nL6_dot_smul, h]
  rw [hone]
  ring

lemma l05nL6_dot_of_valid {q : GGDepANPair} (h : GGTWNValid 3 6 q) :
    ggTWdot (ggTWNToZ 3 6 q.2) (ggTWNToZ 3 6 q.1) = 2 := by
  change ggDepAdot (N := 5) (ggDepANToZ 3 5 q.2) (ggDepANToZ 3 5 q.1) = 2
  have hcast := ggDepANDot_cast (p := 3) (N := 5) q.2 q.1
    (by simpa using h.2.1) (by simpa using h.1)
  rw [h.2.2, ZMod.natCast_mod] at hcast
  norm_num at hcast
  exact hcast.symm

lemma l05nL6_toZ_refl {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = 5) (hq2 : q.2.length = 5) (hv : v.length = 5) :
    ggTWNToZ 3 6 (ggTWNRefl 3 q v) =
      ggTWRefl (ggTWNToZ 3 6 q.1) (ggTWNToZ 3 6 q.2) (ggTWNToZ 3 6 v) := by
  have hlen : (ggDepANSmul 3 (ggDepANDot 3 q.2 v) q.1).length = 5 := l05nNC_smul_length hq1
  change ggDepANToZ 3 5 (ggDepANSub 3 v (ggDepANSmul 3 (ggDepANDot 3 q.2 v) q.1)) =
    ggDepARefl (ggDepANToZ 3 5 q.1) (ggDepANToZ 3 5 q.2) (ggDepANToZ 3 5 v)
  rw [l05nNC_toZ_sub (N := 5) hv hlen, l05nNC_toZ_smul (N := 5) hq1,
    ggDepANDot_cast (p := 3) (N := 5) q.2 v hq2 hv, l05nPT_refl_apply]

lemma l05nL6_dot_alpha_x (i : Fin 5) :
    ggDepAdot (N := 5) (ggTWα 3 6 i) (ggTWx 3 6) = 0 := by
  rw [ggDepAdot]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val + 2 = 6
  · rw [show ggTWα 3 6 i j = 0 by simp [ggTWα, hj], zero_mul]
  · rw [show ggTWx 3 6 j = 0 by simp [ggTWx, hj], mul_zero]

lemma l05nL6_frame_gen_fixes (i : Fin 5) :
    ggTWRefl (ggTWh 3 6 i) (ggTWα 3 6 i) (ggTWx 3 6) = ggTWx 3 6 := by
  rw [l05nPT_refl_apply, l05nL6_dot_alpha_x i, zero_smul, sub_zero]

lemma l05nL6_e6M (i j : Fin 6) :
    ggTWLE6M i.val j.val = CoxeterMatrix.E₆.M i j := by
  fin_cases i <;> fin_cases j <;> decide

@[expose] def l05nL6_endFold (news : List GGDepANPair) (ot : List (Nat × Nat)) :
    List (Module.End (ZMod 3) (GGTWE 3 6)) :=
  ot.foldl (fun L e => L ++ [ggTWNRflOf 3 6 (ggTWNGen 3 6 news e.2) * L.getD e.1 1]) [1]

@[expose] def l05nL6_sim (news : List GGDepANPair) (P : List (List ℕ))
    (E : List (Module.End (ZMod 3) (GGTWE 3 6))) : Prop :=
  E.length = P.length ∧
  (∀ k < P.length, (P.getD k []).length = 5) ∧
  (∀ k < P.length, (E.getD k 1) (ggTWx 3 6) = ggTWNToZ 3 6 (P.getD k [])) ∧
  (∀ k < E.length, (E.getD k 1) ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)))

lemma l05nL6_sim_step {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid 3 6 q)
    {P : List (List ℕ)} {E : List (Module.End (ZMod 3) (GGTWE 3 6))}
    (h : l05nL6_sim news P E) {e : Nat × Nat} (he : e.1 < P.length)
    (he2 : e.2 < 6 - 1 + news.length) :
    l05nL6_sim news (P ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (P.getD e.1 [])])
      (E ++ [ggTWNRflOf 3 6 (ggTWNGen 3 6 news e.2) * E.getD e.1 1]) := by
  obtain ⟨hlen, hPlen, happly, hmem⟩ := h
  have hgv : GGTWNValid 3 6 (ggTWNGen 3 6 news e.2) :=
    ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews (by simpa using he2)
  have hg1 : (ggTWNGen 3 6 news e.2).1.length = 5 := by simpa using hgv.1
  have hg2 : (ggTWNGen 3 6 news e.2).2.length = 5 := by simpa using hgv.2.1
  have hPv : (P.getD e.1 []).length = 5 := hPlen e.1 he
  have hplen : (ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (P.getD e.1 [])).length = 5 := by
    show (ggDepANSub 3 (P.getD e.1 [])
      (ggDepANSmul 3 (ggDepANDot 3 (ggTWNGen 3 6 news e.2).2 (P.getD e.1 []))
        (ggTWNGen 3 6 news e.2).1)).length = 5
    exact l05nNC_sub_length hPv (l05nNC_smul_length hg1)
  have hmemg : ggTWNRflOf 3 6 (ggTWNGen 3 6 news e.2) ∈
      Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) :=
    ggTWNGen_mem (p := 3) (N := 6) (by norm_num) (by norm_num) (by simpa using he2)
  have hmemE : E.getD e.1 1 ∈ Submonoid.closure (ggTWGens 3 6 (ggTWNNews 3 6 news)) :=
    hmem e.1 (by rw [hlen]; exact he)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.length_append, hlen]
  · intro k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hklt | rfl
    · rw [List.getD_append _ _ _ k hklt]
      exact hPlen k hklt
    · rw [List.getD_append_right P _ [] P.length le_rfl, Nat.sub_self, List.getD_cons_zero]
      exact hplen
  · intro k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hklt | rfl
    · rw [List.getD_append _ _ _ k (by rw [hlen]; exact hklt), List.getD_append _ _ _ k hklt]
      exact happly k hklt
    · rw [List.getD_append_right E _ _ _ (by rw [hlen]),
        List.getD_append_right P _ [] P.length le_rfl, hlen, Nat.sub_self,
        List.getD_cons_zero]
      rw [Module.End.mul_apply, happly e.1 he]
      show ggTWRefl (ggTWNToZ 3 6 (ggTWNGen 3 6 news e.2).1)
          (ggTWNToZ 3 6 (ggTWNGen 3 6 news e.2).2) (ggTWNToZ 3 6 (P.getD e.1 [])) =
        ggTWNToZ 3 6 (ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (P.getD e.1 []))
      exact (l05nL6_toZ_refl hg1 hg2 hPv).symm
  · intro k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hklt | rfl
    · rw [List.getD_append _ _ _ k hklt]
      exact hmem k hklt
    · rw [List.getD_append_right E _ _ _ (by rw [hlen]), Nat.sub_self, List.getD_cons_zero]
      exact Submonoid.mul_mem _ hmemg hmemE

lemma l05nL6_sim_fold {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid 3 6 q)
    (l : List (Nat × Nat)) (P₀ : List (List ℕ))
    (E₀ : List (Module.End (ZMod 3) (GGTWE 3 6))) (h0 : l05nL6_sim news P₀ E₀)
    (hpar : ∀ j < l.length, (l.getD j (0, 0)).1 < P₀.length + j)
    (hgen : ∀ j < l.length, (l.getD j (0, 0)).2 < 6 - 1 + news.length) :
    l05nL6_sim news
      (l.foldl (fun L e => L ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (L.getD e.1 [])]) P₀)
      (l.foldl (fun L e => L ++ [ggTWNRflOf 3 6 (ggTWNGen 3 6 news e.2) * L.getD e.1 1]) E₀) := by
  induction l generalizing P₀ E₀ with
  | nil => simpa using h0
  | cons e l ih =>
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (P₀ := P₀ ++ [ggTWNRefl 3 (ggTWNGen 3 6 news e.2) (P₀.getD e.1 [])])
        (E₀ := E₀ ++ [ggTWNRflOf 3 6 (ggTWNGen 3 6 news e.2) * E₀.getD e.1 1])
        (l05nL6_sim_step hnews h0 (hpar 0 (by simp)) (hgen 0 (by simp))) ?_ ?_
      · intro j hj
        have h1 := hpar (j + 1) (by simpa using hj)
        rw [List.getD_cons_succ] at h1
        simp only [List.length_append, List.length_singleton]
        omega
      · intro j hj
        have h1 := hgen (j + 1) (by simpa using hj)
        rw [List.getD_cons_succ] at h1
        exact h1

lemma l05nL6_sim_orbit {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid 3 6 q) (ot : List (Nat × Nat))
    (hpar : ∀ j < ot.length, (ot.getD j (0, 0)).1 < j + 1)
    (hgen : ∀ j < ot.length, (ot.getD j (0, 0)).2 < 6 - 1 + news.length) :
    l05nL6_sim news (ggTWLOrbitPts 3 6 news ot) (l05nL6_endFold news ot) := by
  apply l05nL6_sim_fold hnews ot [ggTWNX 6] [1]
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      simpa [ggTWNX_length]
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      simp [ggTWNX_toZ]
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      exact Submonoid.one_mem _
  · intro j hj
    have h := hpar j hj
    simp only [List.length_singleton]
    omega
  · exact hgen

lemma l05nL6_Ts_getD {w : GGTWLE6} {j : ℕ} (hj : j < w.s.length) :
    (List.map (ggTWLMatOfPair 3 5) w.s).getD j [] = ggTWLMatOfPair 3 5 (w.s.getD j ([], [])) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
    List.getD_eq_getElem _ _ hj, List.getElem_map]

lemma l05nL6_Tg_getD {news : List GGDepANPair} {g : ℕ} (hg : g < 5 + news.length) :
    (ggTWLGenMats 3 6 news).getD g [] = ggTWLMatOfPair 3 5 (ggTWNGen 3 6 news g) := by
  rw [ggTWLGenMats, List.getD_eq_getElem _ _
      (by rw [List.length_map, List.length_map, List.length_range]; simpa using hg),
    List.getElem_map, List.getElem_map, List.getElem_range]

lemma l05nL6_word_mem {M : Submonoid (Module.End (ZMod 3) (GGTWE 3 6))}
    {T : List (List (List ℕ))} {w : List ℕ} (hT : ∀ t ∈ T, ggTWLMatWF 5 t)
    (hgen : ∀ t ∈ T, ggTWLMatLin 3 5 t ∈ M) (hw : ∀ k ∈ w, k < T.length) :
    ggTWLMatLin 3 5 (ggTWLWordMat 3 5 T w) ∈ M := by
  obtain ⟨-, heq⟩ := ggTWLWordMat_lin (p := 3) (d := 5) hT hw
  rw [heq]
  refine Submonoid.list_prod_mem M ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact hgen _ (by
    rw [List.getD_eq_getElem _ _ (hw k hk)]
    exact List.getElem_mem _)

lemma l05nL6_S_invol {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid 3 6 q) :
    ∀ r ∈ ggTWGens 3 6 (ggTWNNews 3 6 news), r * r = 1 := by
  intro r hr
  rw [ggTWGens] at hr
  rcases hr with hr | hr
  · obtain ⟨i, rfl⟩ := hr
    have hiv : i.val + 1 < 6 := by have := i.isLt; omega
    obtain ⟨h1, h2, h3⟩ :=
      ggTWNGen_valid (p := 3) (N := 6) (by norm_num) (by norm_num) hnews
        (g := i.val) (by have := i.isLt; simp only [Nat.reduceSub]; omega)
    have hgen : ggTWNGen 3 6 news i.val = (ggTWNH 3 6 i.val, ggTWNA 3 6 i.val) := by
      simp only [ggTWNGen, if_pos hiv]
    have hdot : ggTWdot (ggTWα 3 6 i) (ggTWh 3 6 i) = 2 := by
      have h := l05nL6_dot_of_valid (q := ggTWNGen 3 6 news i.val) ⟨h1, h2, h3⟩
      simp only [hgen, Prod.fst, Prod.snd, ggTWNH_toZ, ggTWNA_toZ] at h
      exact h
    exact l05nL6_refl_invol (ggTWh 3 6 i) (ggTWα 3 6 i) hdot
  · obtain ⟨t, ht, rfl⟩ := hr
    obtain ⟨q, hq, rfl⟩ := ht
    exact l05nL6_refl_invol (ggTWNToZ 3 6 q.1) (ggTWNToZ 3 6 q.2)
      (l05nL6_dot_of_valid (hnews q hq))

lemma l05nL6_closure_inv {S : Set (Module.End (ZMod 3) (GGTWE 3 6))}
    (hS : ∀ r ∈ S, r * r = 1) :
    ∀ g ∈ Submonoid.closure S, ∃ h ∈ Submonoid.closure S, h * g = 1 := by
  intro g hg
  induction hg using Submonoid.closure_induction with
  | mem x hx => exact ⟨x, Submonoid.subset_closure hx, hS x hx⟩
  | one => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx'mem, hx'x⟩ := ihx
      obtain ⟨y', hy'mem, hy'y⟩ := ihy
      refine ⟨y' * x', Submonoid.mul_mem _ hy'mem hx'mem, ?_⟩
      calc (y' * x') * (x * y) = y' * (x' * (x * y)) := mul_assoc _ _ _
        _ = y' * ((x' * x) * y) := by rw [mul_assoc]
        _ = y' * (1 * y) := by rw [hx'x]
        _ = y' * y := by rw [one_mul]
        _ = 1 := hy'y

lemma l05nL6_veceq_of_toZ {u v : List ℕ} (hu : u.length = 5) (hv : v.length = 5)
    (h : ggTWNToZ 3 6 u = ggTWNToZ 3 6 v) : ggTWLVecEq 3 u v = true := by
  have hmod : ∀ j : Fin 5, u.getD j.val 0 % 3 = v.getD j.val 0 % 3 := by
    intro j
    have hc := congrFun h j
    simp only [ggTWNToZ, ggDepANToZ] at hc
    exact (ZMod.natCast_eq_natCast_iff' _ _ 3).mp hc
  unfold ggTWLVecEq
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by rw [hu, hv], ?_⟩
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  rw [List.getElem_zipWith, id_eq, beq_iff_eq]
  have hiu : i < u.length := by
    have hlt := hi; rw [List.length_zipWith] at hlt
    exact lt_of_lt_of_le hlt (Nat.min_le_left _ _)
  have hiv : i < v.length := by
    have hlt := hi; rw [List.length_zipWith] at hlt
    exact lt_of_lt_of_le hlt (Nat.min_le_right _ _)
  rw [← List.getD_eq_getElem u 0 hiu, ← List.getD_eq_getElem v 0 hiv]
  exact hmod ⟨i, by rw [← hu]; exact hiu⟩

lemma l05nL6_nodup_getD {L : List (List (List ℕ))}
    (h : ggTWLNodup 3 L = true) :
    ∀ i j, i < j → j < L.length → ggTWLMatEq 3 (L.getD i []) (L.getD j []) = false := by
  induction L with
  | nil => intro i j _ hj; exact absurd hj (by simp)
  | cons a l ih =>
      intro i j hij hj
      rw [List.length_cons] at hj
      rcases i with _ | i
      · rw [List.getD_cons_zero]
        have h1 : ∀ b ∈ l, ggTWLMatEq 3 a b = false := by
          intro b hb
          have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 b hb
          simpa using this
        rcases j with _ | j
        · omega
        · rw [List.getD_cons_succ]
          exact h1 _ (by
            rw [List.getD_eq_getElem _ _ (by omega)]
            exact List.getElem_mem _)
      · rcases j with _ | j
        · omega
        · rw [List.getD_cons_succ, List.getD_cons_succ]
          exact ih (Bool.and_eq_true_iff.mp h).2 i j (by omega) (by omega)

end CFSG.StandardType

end
