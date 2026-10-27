module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallWord
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosFacts

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pff_foldl_add_zeros (n : ℕ) :
    (List.replicate n 0).foldl (fun x y => x + y) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl_cons]; simpa using ih

private lemma pff_dot_add (P : Pt) (f x y : P.V) :
    P.dot f (x + y) = P.dot f x + P.dot f y := by
  simp only [Pt.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma pff_dot_sub (P : Pt) (f x y : P.V) :
    P.dot f (x - y) = P.dot f x - P.dot f y := by
  simp only [Pt.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma pff_dot_smul (P : Pt) (f x : P.V) (a : ZMod P.p) :
    P.dot f (a • x) = a * P.dot f x := by
  simp only [Pt.dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private noncomputable def pff_reflLM (P : Pt) [Fact P.p.Prime] (r : Refl) :
    P.V →ₗ[ZMod P.p] P.V where
  toFun w := w - P.dot (P.vec r.f) w • P.vec r.h
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pff_dot_add]
    ring
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply, pff_dot_smul]
    ring

private lemma pff_reflLM_involutive (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) :
    Function.Involutive (pff_reflLM P r) := by
  intro w
  have hd : P.dot (P.vec r.f) (P.vec r.h) = 2 := hwf r hr
  have h2 : P.dot (P.vec r.f) (w - P.dot (P.vec r.f) w • P.vec r.h)
      = -(P.dot (P.vec r.f) w) := by
    rw [pff_dot_sub, pff_dot_smul, hd]
    ring
  show (w - P.dot (P.vec r.f) w • P.vec r.h)
      - P.dot (P.vec r.f) (w - P.dot (P.vec r.f) w • P.vec r.h) • P.vec r.h = w
  rw [h2, neg_smul, sub_neg_eq_add, sub_add_cancel]

private noncomputable def pff_reflLE (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) : P.V ≃ₗ[ZMod P.p] P.V :=
  LinearEquiv.ofInvolutive (pff_reflLM P r) (pff_reflLM_involutive P hwf r hr)

private lemma pff_reflLE_apply (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) (v : P.V) :
    pff_reflLE P hwf r hr v = v - P.dot (P.vec r.f) v • P.vec r.h := rfl

private lemma pff_lin_ext_unit (P : Pt) [Fact P.p.Prime] {W : Type*} [AddCommMonoid W]
    [Module (ZMod P.p) W] {f g : P.V →ₗ[ZMod P.p] W}
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = g (P.vec (P.unit j))) : f = g := by
  apply LinearMap.ext
  intro z
  have hz : z = ∑ j : Fin P.D, z j • Pi.single j (1 : ZMod P.p) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]; ring
    · intro k _ hk
      rw [Pi.single_apply, if_neg (Ne.symm hk), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hz]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Pt.vec_unit P j]
  exact congrArg (fun w => z j • w) (h j)

private lemma pff_le_ext_unit (P : Pt) [Fact P.p.Prime] {f g : P.V ≃ₗ[ZMod P.p] P.V}
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = g (P.vec (P.unit j))) : f = g := by
  have hlm : (f : P.V →ₗ[ZMod P.p] P.V) = (g : P.V →ₗ[ZMod P.p] P.V) := by
    apply pff_lin_ext_unit P
    exact h
  apply LinearEquiv.ext
  intro z
  exact congrFun (congrArg (fun m : P.V →ₗ[ZMod P.p] P.V => (m : P.V → P.V)) hlm) z

private lemma pff_le_eq_one_of_unit (P : Pt) [Fact P.p.Prime] (f : P.V ≃ₗ[ZMod P.p] P.V)
    (h : ∀ j : Fin P.D, f (P.vec (P.unit j)) = P.vec (P.unit j)) : f = 1 := by
  apply pff_le_ext_unit P
  intro j
  rw [h j]
  rfl

private lemma pff_applyWord_append (P : Pt) (x y : Word) (v : Vec) :
    P.applyWord (x ++ y) v = P.applyWord x (P.applyWord y v) := by
  simp only [Pt.applyWord, List.foldr_append]

private lemma pff_applyWord_singleton (P : Pt) (k : Nat) (v : Vec) (hk : k < P.gens.length) :
    P.applyWord [k] v = P.applyRefl (P.gens[k]'hk) v := by
  simp only [Pt.applyWord, List.foldr_cons, List.foldr_nil, List.getElem?_eq_getElem hk]

private lemma pff_wordOK_reverse (P : Pt) (w : Word) (hw : P.wordOK w = true) :
    P.wordOK w.reverse = true := by
  simpa only [Pt.wordOK, List.all_reverse] using hw

private lemma pff_vec_applyRefl_eq (P : Pt) [Fact P.p.Prime] (r : Refl) (a b : Vec)
    (h : P.vec a = P.vec b) : P.vec (P.applyRefl r a) = P.vec (P.applyRefl r b) := by
  rw [Pt.vec_applyRefl, Pt.vec_applyRefl, h]

private lemma pff_applyRefl_invol (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) (v : Vec) :
    P.vec (P.applyRefl r (P.applyRefl r v)) = P.vec v := by
  rw [Pt.vec_applyRefl P r (P.applyRefl r v), Pt.vec_applyRefl P r v]
  have hd : P.dot (P.vec r.f) (P.vec v - P.dot (P.vec r.f) (P.vec v) • P.vec r.h)
      = -(P.dot (P.vec r.f) (P.vec v)) := by
    rw [pff_dot_sub, pff_dot_smul, hwf r hr]; ring
  rw [hd, neg_smul, sub_neg_eq_add, sub_add_cancel]

private lemma pff_applyWord_reverse_inv (P : Pt) [Fact P.p.Prime] (hwf : P.WF) :
    ∀ (w : Word), P.wordOK w = true →
      ∀ v : Vec, P.vec (P.applyWord w (P.applyWord w.reverse v)) = P.vec v := by
  intro w
  induction w with
  | nil =>
      intro _ v
      simp only [Pt.applyWord, List.reverse_nil, List.foldr_nil]
  | cons i w ih =>
      intro hw v
      have hw' : ∀ x ∈ i :: w, decide (x < P.gens.length) = true :=
        List.all_eq_true.mp (by simpa only [Pt.wordOK] using hw)
      have hir : i < P.gens.length := by simpa using hw' i (by simp)
      have hwt : P.wordOK w = true := by
        apply List.all_eq_true.mpr
        intro x hx
        exact hw' x (List.mem_cons_of_mem i hx)
      have hword : P.applyWord (i :: w) (P.applyWord (i :: w).reverse v)
          = P.applyRefl (P.gens[i]'hir)
              (P.applyWord w (P.applyWord w.reverse (P.applyRefl (P.gens[i]'hir) v))) := by
        rw [List.reverse_cons, pff_applyWord_append]
        simp only [Pt.applyWord, List.foldr_cons, List.foldr_nil, List.getElem?_eq_getElem hir]
      rw [hword, pff_vec_applyRefl_eq P (P.gens[i]'hir) _ _
          (ih hwt (P.applyRefl (P.gens[i]'hir) v)),
        pff_applyRefl_invol P hwf _ (List.getElem_mem hir) v]

private lemma pff_range_map_getD_lt {D p : ℕ} (F : ℕ → ℕ) (hF : ∀ i, i < D → F i < p)
    (hp : 0 < p) (k : ℕ) : (((List.range D).map F).getD k 0) < p := by
  by_cases hk : k < D
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]
    exact hF k hk
  · have hlen : ((List.range D).map F).length ≤ k := by
      simp only [List.length_map, List.length_range]; omega
    rw [List.getD_eq_default _ _ hlen]
    exact hp

private lemma pff_applyRefl_lt (P : Pt) (r : Refl) (v : Vec) (hp : 0 < P.p) (k : Nat) :
    (P.applyRefl r v).getD k 0 < P.p := by
  unfold Pt.applyRefl
  exact pff_range_map_getD_lt (fun i => (v.getD i 0 + (P.p - (P.dotv r.f v * r.h.getD i 0) % P.p)) % P.p)
    (fun i _ => Nat.mod_lt _ hp) hp k

private lemma pff_unit_getD (P : Pt) (i k : Nat) (hk : k < P.D) :
    (P.unit i).getD k 0 = if k = i then 1 else 0 := by
  unfold Pt.unit
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range (j := k) (by simpa using hk)]

private lemma pff_applyWord_unit_length (P : Pt) (w : Word) (i : Nat) :
    (P.applyWord w (P.unit i)).length = P.D := by
  induction w with
  | nil => simp [Pt.applyWord, Pt.unit]
  | cons k w ih =>
      simp only [Pt.applyWord, List.foldr_cons]
      split
      · simp [Pt.applyRefl]
      · exact ih

private lemma pff_applyWord_unit_lt (P : Pt) (w : Word) (i : Nat) (hp : 1 < P.p) :
    ∀ k, k < P.D → (P.applyWord w (P.unit i)).getD k 0 < P.p := by
  induction w with
  | nil =>
      intro k hk
      simp only [Pt.applyWord, List.foldr_nil]
      rw [pff_unit_getD P i k hk]
      split <;> omega
  | cons k w ih =>
      intro j hj
      simp only [Pt.applyWord, List.foldr_cons]
      split
      · exact pff_applyRefl_lt P _ _ (by omega) j
      · exact ih j hj

private lemma pff_vec_ext (P : Pt) (hp : 0 < P.p) {a b : Vec}
    (ha : a.length = P.D) (hb : b.length = P.D)
    (halt : ∀ k, k < P.D → a.getD k 0 < P.p)
    (hblt : ∀ k, k < P.D → b.getD k 0 < P.p)
    (h : P.vec a = P.vec b) : a = b := by
  apply List.ext_getElem
  · rw [ha, hb]
  · intro k h1 h2
    have hk : k < P.D := by rwa [ha] at h1
    have hv : ((a.getD k 0 : ℕ) : ZMod P.p) = ((b.getD k 0 : ℕ) : ZMod P.p) := by
      have := congrFun h ⟨k, hk⟩
      simpa only [Pt.vec] using this
    have hm : (a.getD k 0) % P.p = (b.getD k 0) % P.p :=
      (ZMod.natCast_eq_natCast_iff (a.getD k 0) (b.getD k 0) P.p).mp hv
    rw [Nat.mod_eq_of_lt (halt k hk), Nat.mod_eq_of_lt (hblt k hk)] at hm
    rw [← List.getD_eq_getElem a 0 h1, ← List.getD_eq_getElem b 0 h2]
    exact hm

theorem verifyC_sound {Q : SPt} [Fact Q.pt.p.Prime] (hwf : Q.pt.WF) {c : CWit} (h : verifyC Q c = true) :
    Q.pt.CycleAt Q.s := by
  rcases Q with ⟨P, s⟩
  unfold verifyC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hp5, hpsi⟩, hsj⟩, hjn⟩, hsj'⟩, hj'n⟩, hne⟩, hprod⟩, hany⟩
  obtain ⟨i, hi, hunit⟩ := List.any_eq_true.mp hany
  have hiD : i < P.D := List.mem_range.mp hi
  have hp0 : 0 < P.p := by omega
  have hp1 : 1 < P.p := by omega
  have hunit_ne : P.applyWord ((c.psi ++ [c.j] ++ c.psi.reverse) ++ [c.j']) (P.unit i) ≠
      P.applyWord ([c.j'] ++ (c.psi ++ [c.j] ++ c.psi.reverse)) (P.unit i) := by
    simpa using hunit
  have hj : c.j < P.gens.length := by
    by_contra hcon
    have hge : P.gens.length ≤ c.j := Nat.le_of_not_lt hcon
    have hdef : P.gens.getD c.j ⟨[], []⟩ = ⟨[], []⟩ := List.getD_eq_default _ _ hge
    have ha1 : P.alphaK c.j (P.hK c.j') = 0 := by
      unfold Pt.alphaK Pt.hK
      rw [hdef]
      simp [Pt.dotv, pff_foldl_add_zeros]
    have hb1 : P.alphaK c.j' (P.hK c.j) = 0 := by
      unfold Pt.alphaK Pt.hK
      rw [hdef]
      simp [Pt.dotv, pff_foldl_add_zeros]
    have hL : (P.alphaK c.j (P.hK c.j') * P.alphaK c.j' (P.applyWord c.psi (P.hK c.j)) *
        P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j))) % P.p = 0 := by
      rw [ha1]; simp
    have hR : (P.alphaK c.j' (P.hK c.j) * P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j')) *
        P.alphaK c.j (P.applyWord c.psi (P.hK c.j))) % P.p = 0 := by
      rw [hb1]; simp
    exact hprod (by rw [hL, hR])
  have hj' : c.j' < P.gens.length := by
    by_contra hcon
    have hge : P.gens.length ≤ c.j' := Nat.le_of_not_lt hcon
    have hdef : P.gens.getD c.j' ⟨[], []⟩ = ⟨[], []⟩ := List.getD_eq_default _ _ hge
    have ha2 : P.alphaK c.j' (P.applyWord c.psi (P.hK c.j)) = 0 := by
      unfold Pt.alphaK
      rw [hdef]
      simp [Pt.dotv, pff_foldl_add_zeros]
    have hb1 : P.alphaK c.j' (P.hK c.j) = 0 := by
      unfold Pt.alphaK
      rw [hdef]
      simp [Pt.dotv, pff_foldl_add_zeros]
    have hL : (P.alphaK c.j (P.hK c.j') * P.alphaK c.j' (P.applyWord c.psi (P.hK c.j)) *
        P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j))) % P.p = 0 := by
      rw [ha2]; simp
    have hR : (P.alphaK c.j' (P.hK c.j) * P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j')) *
        P.alphaK c.j (P.applyWord c.psi (P.hK c.j))) % P.p = 0 := by
      rw [hb1]; simp
    exact hprod (by rw [hL, hR])
  obtain ⟨ψ, hψmem, hψ⟩ := Pt.applyWord_spec P hwf c.psi hpsi
  obtain ⟨δ, hδmem, hδ⟩ := Pt.applyWord_spec P hwf c.psi.reverse (pff_wordOK_reverse P c.psi hpsi)
  have hψδ : ψ * δ = 1 := by
    apply pff_le_eq_one_of_unit P
    intro j
    rw [LinearEquiv.mul_apply, hδ, hψ]
    exact pff_applyWord_reverse_inv P hwf c.psi hpsi (P.unit j)
  have hψinv : ψ⁻¹ = δ := by
    calc ψ⁻¹ = ψ⁻¹ * 1 := by rw [mul_one]
      _ = ψ⁻¹ * (ψ * δ) := by rw [hψδ]
      _ = (ψ⁻¹ * ψ) * δ := by rw [mul_assoc]
      _ = 1 * δ := by rw [inv_mul_cancel]
      _ = δ := by rw [one_mul]
  let rjC : Refl := P.gens[c.j]'hj
  let rjC' : Refl := P.gens[c.j']'hj'
  let rj : P.V ≃ₗ[ZMod P.p] P.V := pff_reflLE P hwf rjC (List.getElem_mem hj)
  let rj' : P.V ≃ₗ[ZMod P.p] P.V := pff_reflLE P hwf rjC' (List.getElem_mem hj')
  have hrj : ∀ w, rj w = w - P.dot (P.vec rjC.f) w • P.vec rjC.h :=
    fun w => pff_reflLE_apply P hwf rjC (List.getElem_mem hj) w
  have hrj' : ∀ w, rj' w = w - P.dot (P.vec rjC'.f) w • P.vec rjC'.h :=
    fun w => pff_reflLE_apply P hwf rjC' (List.getElem_mem hj') w
  let ht : P.V := ψ (P.vec rjC.h)
  let αt : Module.Dual (ZMod P.p) P.V :=
    { toFun := fun w => P.dot (P.vec rjC.f) (δ w)
      map_add' := by intro x y; rw [map_add, pff_dot_add]
      map_smul' := by
        intro a x
        rw [map_smul]
        simpa [smul_eq_mul] using pff_dot_smul P (P.vec rjC.f) (δ x) a }
  have hconj : ∀ w, (ψ * rj * ψ⁻¹) w = w - αt w • ht := by
    intro w
    rw [hψinv]
    show ψ (rj (δ w)) = w - αt w • ht
    rw [hrj, map_sub, map_smul]
    have h1 : ψ (δ w) = w := by
      rw [← LinearEquiv.mul_apply, hψδ]
      rfl
    rw [h1]
    rfl
  have hαt_ht : αt ht = 2 := by
    show P.dot (P.vec rjC.f) (δ ht) = 2
    have hδψ : δ ht = P.vec rjC.h := by
      show δ (ψ (P.vec rjC.h)) = P.vec rjC.h
      rw [← hψinv]
      simp
    rw [hδψ]
    exact hwf rjC (List.getElem_mem hj)
  have hs1 : rj' (P.vec (P.unit i)) = P.vec (P.applyWord [c.j'] (P.unit i)) := by
    rw [hrj', pff_applyWord_singleton P c.j' (P.unit i) hj']
    exact (Pt.vec_applyRefl P rjC' (P.unit i)).symm
  have hs2 : δ (rj' (P.vec (P.unit i)))
      = P.vec (P.applyWord c.psi.reverse (P.applyWord [c.j'] (P.unit i))) := by
    rw [hs1, hδ]
  have hs3 : rj (δ (rj' (P.vec (P.unit i))))
      = P.vec (P.applyWord [c.j] (P.applyWord c.psi.reverse (P.applyWord [c.j'] (P.unit i)))) := by
    rw [hs2, hrj, pff_applyWord_singleton P c.j _ hj]
    exact (Pt.vec_applyRefl P rjC _).symm
  have hs4 : ψ (rj (δ (rj' (P.vec (P.unit i)))))
      = P.vec (P.applyWord c.psi
          (P.applyWord [c.j] (P.applyWord c.psi.reverse (P.applyWord [c.j'] (P.unit i))))) := by
    rw [hs3, hψ]
  have hact1 : (ψ * rj * ψ⁻¹ * rj') (P.vec (P.unit i))
      = P.vec (P.applyWord ((c.psi ++ [c.j] ++ c.psi.reverse) ++ [c.j']) (P.unit i)) := by
    rw [hψinv]
    show ψ (rj (δ (rj' (P.vec (P.unit i))))) = _
    rw [hs4]
    congr 1
    rw [pff_applyWord_append, pff_applyWord_append, pff_applyWord_append]
  have ht1 : δ (P.vec (P.unit i)) = P.vec (P.applyWord c.psi.reverse (P.unit i)) := by
    rw [hδ]
  have ht2 : rj (δ (P.vec (P.unit i)))
      = P.vec (P.applyWord [c.j] (P.applyWord c.psi.reverse (P.unit i))) := by
    rw [ht1, hrj, pff_applyWord_singleton P c.j _ hj]
    exact (Pt.vec_applyRefl P rjC _).symm
  have ht3 : ψ (rj (δ (P.vec (P.unit i))))
      = P.vec (P.applyWord c.psi (P.applyWord [c.j] (P.applyWord c.psi.reverse (P.unit i)))) := by
    rw [ht2, hψ]
  have ht4 : rj' (ψ (rj (δ (P.vec (P.unit i)))))
      = P.vec (P.applyWord [c.j']
          (P.applyWord c.psi (P.applyWord [c.j] (P.applyWord c.psi.reverse (P.unit i))))) := by
    rw [ht3, hrj', pff_applyWord_singleton P c.j' _ hj']
    exact (Pt.vec_applyRefl P rjC' _).symm
  have hact2 : (rj' * (ψ * rj * ψ⁻¹)) (P.vec (P.unit i))
      = P.vec (P.applyWord ([c.j'] ++ (c.psi ++ [c.j] ++ c.psi.reverse)) (P.unit i)) := by
    rw [hψinv]
    show rj' (ψ (rj (δ (P.vec (P.unit i))))) = _
    rw [ht4]
    congr 1
    rw [pff_applyWord_append, pff_applyWord_append, pff_applyWord_append]
  have hcomm : ψ * rj * ψ⁻¹ * rj' ≠ rj' * (ψ * rj * ψ⁻¹) := by
    intro heq
    have hvec : P.vec (P.applyWord ((c.psi ++ [c.j] ++ c.psi.reverse) ++ [c.j']) (P.unit i))
        = P.vec (P.applyWord ([c.j'] ++ (c.psi ++ [c.j] ++ c.psi.reverse)) (P.unit i)) := by
      rw [← hact1, ← hact2, heq]
    have hlen1 : (P.applyWord ((c.psi ++ [c.j] ++ c.psi.reverse) ++ [c.j']) (P.unit i)).length = P.D :=
      pff_applyWord_unit_length P _ i
    have hlen2 : (P.applyWord ([c.j'] ++ (c.psi ++ [c.j] ++ c.psi.reverse)) (P.unit i)).length = P.D :=
      pff_applyWord_unit_length P _ i
    have hlt1 : ∀ k, k < P.D →
        (P.applyWord ((c.psi ++ [c.j] ++ c.psi.reverse) ++ [c.j']) (P.unit i)).getD k 0 < P.p :=
      pff_applyWord_unit_lt P _ i hp1
    have hlt2 : ∀ k, k < P.D →
        (P.applyWord ([c.j'] ++ (c.psi ++ [c.j] ++ c.psi.reverse)) (P.unit i)).getD k 0 < P.p :=
      pff_applyWord_unit_lt P _ i hp1
    exact hunit_ne (pff_vec_ext P hp0 hlen1 hlen2 hlt1 hlt2 hvec)
  have hdotA1 : P.dot (P.vec rjC.f) (P.vec rjC'.h) = (P.alphaK c.j (P.hK c.j') : ZMod P.p) := by
    unfold Pt.alphaK Pt.hK
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
    exact (Pt.dotv_spec P _ _).symm
  have hdotB1 : P.dot (P.vec rjC'.f) (P.vec rjC.h) = (P.alphaK c.j' (P.hK c.j) : ZMod P.p) := by
    unfold Pt.alphaK Pt.hK
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
    exact (Pt.dotv_spec P _ _).symm
  have hdotA2 : P.dot (P.vec rjC'.f) ht = (P.alphaK c.j' (P.applyWord c.psi (P.hK c.j)) : ZMod P.p) := by
    show P.dot (P.vec rjC'.f) (ψ (P.vec rjC.h)) = _
    have hh : rjC.h = P.hK c.j := by
      unfold Pt.hK
      rw [List.getD_eq_getElem _ _ hj]
    rw [hh, hψ]
    unfold Pt.alphaK
    rw [List.getD_eq_getElem _ _ hj']
    exact (Pt.dotv_spec P _ _).symm
  have hdotB3 : P.dot (P.vec rjC.f) ht = (P.alphaK c.j (P.applyWord c.psi (P.hK c.j)) : ZMod P.p) := by
    show P.dot (P.vec rjC.f) (ψ (P.vec rjC.h)) = _
    have hh : rjC.h = P.hK c.j := by
      unfold Pt.hK
      rw [List.getD_eq_getElem _ _ hj]
    rw [hh, hψ]
    unfold Pt.alphaK
    rw [List.getD_eq_getElem _ _ hj]
    exact (Pt.dotv_spec P _ _).symm
  have hdotA3 : αt (P.vec rjC.h) = (P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j)) : ZMod P.p) := by
    show P.dot (P.vec rjC.f) (δ (P.vec rjC.h)) = _
    rw [hδ]
    have hh : rjC.h = P.hK c.j := by
      unfold Pt.hK
      rw [List.getD_eq_getElem _ _ hj]
    rw [hh]
    unfold Pt.alphaK
    rw [List.getD_eq_getElem _ _ hj]
    exact (Pt.dotv_spec P _ _).symm
  have hdotB2 : αt (P.vec rjC'.h) = (P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j')) : ZMod P.p) := by
    show P.dot (P.vec rjC.f) (δ (P.vec rjC'.h)) = _
    rw [hδ]
    have hh : rjC'.h = P.hK c.j' := by
      unfold Pt.hK
      rw [List.getD_eq_getElem _ _ hj']
    rw [hh]
    unfold Pt.alphaK
    rw [List.getD_eq_getElem _ _ hj]
    exact (Pt.dotv_spec P _ _).symm
  have hprod_goal : P.dot (P.vec rjC.f) (P.vec rjC'.h) * P.dot (P.vec rjC'.f) ht * αt (P.vec rjC.h) ≠
      P.dot (P.vec rjC'.f) (P.vec rjC.h) * αt (P.vec rjC'.h) * P.dot (P.vec rjC.f) ht := by
    rw [hdotA1, hdotA2, hdotA3, hdotB1, hdotB2, hdotB3]
    intro hG
    exact hprod (by
      have hcast : ((P.alphaK c.j (P.hK c.j') * P.alphaK c.j' (P.applyWord c.psi (P.hK c.j)) *
          P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j)) : ℕ) : ZMod P.p) =
          ((P.alphaK c.j' (P.hK c.j) * P.alphaK c.j (P.applyWord c.psi.reverse (P.hK c.j')) *
          P.alphaK c.j (P.applyWord c.psi (P.hK c.j)) : ℕ) : ZMod P.p) := by
        push_cast
        exact hG
      exact (ZMod.natCast_eq_natCast_iff _ _ P.p).mp hcast)
  refine ⟨hp5, ψ, rj, rj', c.j, c.j', hψmem, hsj, hjn, hsj', hj'n, hne, ?_, ?_, ht, αt, hconj, hαt_ht,
    hcomm, ?_⟩
  · intro w
    rw [List.getD_eq_getElem _ _ hj]
    exact hrj w
  · intro w
    rw [List.getD_eq_getElem _ _ hj']
    exact hrj' w
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
    exact hprod_goal

end CFSG.TwoNodeSmall
