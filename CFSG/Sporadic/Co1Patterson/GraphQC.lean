module

public import CFSG.Sporadic.Co1Patterson.GraphPoints
public import CFSG.Sporadic.Co1Patterson.GraphRonan

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

section Transport

variable {V : Type*} {G : SimpleGraph V}

theorem PentNull.map (f : G →g G) {v₀ v₁ v₂ v₃ v₄ : V} (h : PentNull G v₀ v₁ v₂ v₃ v₄) :
    PentNull G (f v₀) (f v₁) (f v₂) (f v₃) (f v₄) := by
  induction h with
  | chord h => exact .chord (h.imp (congrArg f) f.map_adj)
  | centre h₀ h₂ h₃ => exact .centre (f.map_adj h₀) (f.map_adj h₂) (f.map_adj h₃)
  | split h₀ h₂ _ ih => exact .split (f.map_adj h₀) (f.map_adj h₂) ih
  | rot _ ih => exact .rot ih

theorem Q2Good.map (f : G →g G) {a b g : V} (h : Q2Good G a b g) :
    Q2Good G (f a) (f b) (f g) := by
  induction h with
  | pent hac hcb hbg hgc' hc'a hP =>
    exact .pent (f.map_adj hac) (f.map_adj hcb) (f.map_adj hbg) (f.map_adj hgc')
      (f.map_adj hc'a) (hP.map f)
  | prop hbg _ _ ih₁ ih₂ => exact .prop (f.map_adj hbg) ih₁ ih₂

theorem PentNull.of_rot (v : ℕ → V) (hv : ∀ i, v (i % 5) = v i) (r : ℕ)
    (h : PentNull G (v r) (v (r + 1)) (v (r + 2)) (v (r + 3)) (v (r + 4))) :
    PentNull G (v 0) (v 1) (v 2) (v 3) (v 4) := by
  have hr : ∀ i, v (r + i) = v ((r % 5) + i) := fun i => by
    rw [← hv (r + i), ← hv (r % 5 + i)]
    congr 1
    omega
  rw [show r = r + 0 from rfl, hr 0, hr 1, hr 2, hr 3, hr 4] at h
  have h5 : r % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have e : ∀ i, v (i + 5) = v i := fun i => by rw [← hv (i + 5), Nat.add_mod_right, hv]
  interval_cases r % 5
  · exact h
  · exact .rot (by simpa [e] using h)
  · exact .rot (.rot (by simpa [e] using h))
  · exact .rot (.rot (.rot (by simpa [e] using h)))
  · exact .rot (.rot (.rot (.rot (by simpa [e] using h))))

end Transport

@[expose] def CRep (p : Native.Rows × Native.Rows) (x : NativeSporadic.Co1) : Prop :=
  NRep p.1 x ∧ NRep p.2 x⁻¹ ∧ CFSG.Sporadic.Co1.InvNative.validRows p.1 = true ∧
    CFSG.Sporadic.Co1.InvNative.validRows p.2 = true

theorem crep_one : CRep (Native.one, Native.one) 1 :=
  ⟨NRep.one', by rw [inv_one]; exact NRep.one', validRows_one, validRows_one⟩

theorem crep_xE {k : ℕ} (hk : k < orbE.c.pts.size) : CRep (xeK orbE k, xeiK orbE k) (xE k) :=
  ⟨nrep_xE hk, nrep_xEinv hk, valid_xeK hk, valid_xeiK hk⟩

theorem crep_nbrX {p : Native.Rows × Native.Rows} {x : NativeSporadic.Co1} (h : CRep p x)
    {k : ℕ} (hk : k < orbE.c.pts.size) : CRep (nbrX orbE p k) (x * xE k) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have := nrep_nbrX h1 h2 hk
  have hv := valid_nbrX h3 h4 hk
  exact ⟨this.1, this.2, hv.1, hv.2⟩

theorem crep_rep {j : ℕ} (hj : j < 10) : CRep (repP j) (gElt (repJ j)) :=
  ⟨nrep_repX dagOK_true j, nrep_repXi dagOK_true hj,
    ((dagOK_parts dagOK_true).2 _ (repJ_mem hj).1 (repJ_mem hj).2).1,
    ((dagOK_parts dagOK_true).2 _ (repJ_mem hj).1 (repJ_mem hj).2).2.1⟩

theorem adj_of_adjC {p q : Native.Rows × Native.Rows} {x y : NativeSporadic.Co1} (hp : CRep p x)
    (hq : CRep q y) (h : adjC (ptSet orbE) p.1 p.2 (vtxR q.1 q.2) = true) :
    (a2Graph aNC).Adj (x • vA) (y • vA) :=
  (adj_iff_adjC hp.1 hp.2.1 (nrep_vtxR hq.1 hq.2.1) hp.2.2.1 hp.2.2.2
    (valid_vtxR hq.2.2.1 hq.2.2.2)).2 h

theorem eq_of_vtxR {p q : Native.Rows × Native.Rows} {x y : NativeSporadic.Co1} (hp : CRep p x)
    (hq : CRep q y) (h : vtxR p.1 p.2 = vtxR q.1 q.2) : x • vA = y • vA :=
  Subtype.ext (NRep.unique (nrep_vtxR hp.1 hp.2.1) (h ▸ nrep_vtxR hq.1 hq.2.1))

@[expose] def PRep (vs : Array (Native.Rows × Native.Rows)) (xs : ℕ → NativeSporadic.Co1) : Prop :=
  ∀ i, CRep (pv vs i) (xs i)

theorem pv_mod (vs : Array (Native.Rows × Native.Rows)) (i : ℕ) : pv vs (i % 5) = pv vs i := by
  unfold pv
  rw [Nat.mod_mod]

theorem PRep.periodic {vs : Array (Native.Rows × Native.Rows)} {xs : ℕ → NativeSporadic.Co1}
    (h : PRep vs xs) (i : ℕ) : xs (i % 5) • vA = xs i • vA := by
  have h1 := h (i % 5)
  rw [pv_mod] at h1
  exact congrArg (· • vA) (NRep.unique h1.1 (h i).1)

theorem pcOK_sound : ∀ (P : PC) (vs : Array (Native.Rows × Native.Rows))
    (xs : ℕ → NativeSporadic.Co1), PRep vs xs → pcOK orbE (ptSet orbE) vs P = true →
    PentNull (a2Graph aNC) (xs 0 • vA) (xs 1 • vA) (xs 2 • vA) (xs 3 • vA) (xs 4 • vA)
  | .chord r, vs, xs, hvs, h => by
    unfold pcOK at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    refine PentNull.of_rot (fun i => xs i • vA) hvs.periodic r (.chord ?_)
    rcases h with h | h
    · exact Or.inl (eq_of_vtxR (hvs r) (hvs (r + 2)) h)
    · exact Or.inr (adj_of_adjC (hvs r) (hvs (r + 2)) h)
  | .centre r k, vs, xs, hvs, h => by
    unfold pcOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, h2⟩, h3⟩ := h
    have hz := crep_nbrX (hvs r) hk
    refine PentNull.of_rot (fun i => xs i • vA) hvs.periodic r (.centre (z := (xs r * xE k) • vA)
      ?_ (adj_of_adjC hz (hvs (r + 2)) h2) (adj_of_adjC hz (hvs (r + 3)) h3))
    exact (adj_nbrV (xs r) hk).symm
  | .split r k P, vs, xs, hvs, h => by
    unfold pcOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, h2⟩, hP⟩ := h
    have hz := crep_nbrX (hvs r) hk
    let xs' : ℕ → NativeSporadic.Co1 := fun i =>
      [xs r, xs r * xE k, xs (r + 2), xs (r + 3), xs (r + 4)].getD (i % 5) 1
    have hvs' : PRep #[pv vs r, nbrX orbE (pv vs r) k, pv vs (r + 2), pv vs (r + 3),
        pv vs (r + 4)] xs' := by
      intro i
      have hi : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
      unfold pv
      simp only [xs']
      interval_cases i % 5
      · exact hvs r
      · exact hz
      · exact hvs (r + 2)
      · exact hvs (r + 3)
      · exact hvs (r + 4)
    have ih : PentNull (a2Graph aNC) (xs r • vA) ((xs r * xE k) • vA) (xs (r + 2) • vA)
        (xs (r + 3) • vA) (xs (r + 4) • vA) := pcOK_sound P _ xs' hvs' hP
    exact PentNull.of_rot (fun i => xs i • vA) hvs.periodic r
      (.split (z := (xs r * xE k) • vA) (adj_nbrV (xs r) hk).symm
        (adj_of_adjC hz (hvs (r + 2)) h2) ih)

theorem qcOK_sound : ∀ (C : QC) (b g : Native.Rows × Native.Rows) (xb xg : NativeSporadic.Co1),
    CRep b xb → CRep g xg → (a2Graph aNC).Adj (xb • vA) (xg • vA) →
    qcOK orbE (ptSet orbE) b g C = true → Q2Good (a2Graph aNC) vA (xb • vA) (xg • vA)
  | .pent c c' P, b, g, xb, xg, hb, hg, hbg, h => by
    unfold qcOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hc, hc'⟩, hcb⟩, hgc'⟩, hP⟩ := h
    have pc := crep_xE hc
    have pc' := crep_xE hc'
    let xs : ℕ → NativeSporadic.Co1 := fun i => [1, xE c, xb, xg, xE c'].getD (i % 5) 1
    have hvs : PRep #[(Native.one, Native.one), (xeK orbE c, xeiK orbE c), b, g,
        (xeK orbE c', xeiK orbE c')] xs := by
      intro i
      have hi : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
      unfold pv
      simp only [xs]
      interval_cases i % 5
      · exact crep_one
      · exact pc
      · exact hb
      · exact hg
      · exact pc'
    have hpent : PentNull (a2Graph aNC) ((1 : NativeSporadic.Co1) • vA) (xE c • vA) (xb • vA)
        (xg • vA) (xE c' • vA) := pcOK_sound P _ xs hvs hP
    rw [one_smul] at hpent
    exact .pent (adj_vA_cV hc) (adj_of_adjC pc hb hcb) hbg (adj_of_adjC hg pc' hgc')
      (adj_vA_cV hc').symm hpent
  | .prop k C₁ C₂, b, g, xb, xg, hb, hg, hbg, h => by
    unfold qcOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hk, hxg⟩, h₁⟩, h₂⟩ := h
    have hx := crep_nbrX hb hk
    have hbx : (a2Graph aNC).Adj (xb • vA) ((xb * xE k) • vA) := adj_nbrV xb hk
    have hxg' := adj_of_adjC hx hg hxg
    exact .prop hbg (qcOK_sound C₁ b _ xb _ hb hx hbx h₁) (qcOK_sound C₂ _ g _ xg hx hg hxg' h₂)

end CFSG.Sporadic.Co1Patterson
