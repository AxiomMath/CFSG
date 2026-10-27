module

public import CFSG.Monster.AxisCount.DenseTau
public import CFSG.Monster.Generated.Data
public import CFSG.Monster.AxisCount.DenseLetters

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Rep4371 Matrix

theorem bvec_mem_C_of (w : ℕ) (h : Model.wordN (Model.coeffN w) = w) : bvec 24 w ∈ C := by
  have : bvec 24 w = ((toC (Model.coeffN w) : C) : Fin 24 → ZMod 2) := by rw [coe_toC, h]
  rw [this]
  exact (toC _).2

theorem permValid_spec {arr : Array ℕ} (h : Native.permValid arr = true) :
    ∃ p : AutPerm, RepPerm (p : Equiv.Perm (Fin 24)) arr := by
  simp only [Native.permValid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hlt : ∀ i : Fin 24, arr[(i : ℕ)]! < 24 := fun i => by
    have := List.all_eq_true.1 h1 i (List.mem_range.2 i.2)
    simpa using this
  have hlt' : ∀ j : Fin 24, (Native.permInv arr)[(j : ℕ)]! < 24 := fun j => by
    have := List.all_eq_true.1 h2 j (List.mem_range.2 j.2)
    simpa using this
  have hr : ∀ j : Fin 24, arr[(Native.permInv arr)[(j : ℕ)]!]! = j := fun j => by
    have := List.all_eq_true.1 h3 j (List.mem_range.2 j.2)
    simpa using this
  have hl : ∀ i : Fin 24, (Native.permInv arr)[arr[(i : ℕ)]!]! = i := fun i => by
    have := List.all_eq_true.1 h4 i (List.mem_range.2 i.2)
    simpa using this
  let σ : Equiv.Perm (Fin 24) :=
    { toFun := fun i => ⟨arr[(i : ℕ)]!, hlt i⟩
      invFun := fun j => ⟨(Native.permInv arr)[(j : ℕ)]!, hlt' j⟩
      left_inv := fun i => Fin.ext (hl i)
      right_inv := fun j => Fin.ext (hr j) }
  have hσ : RepPerm σ arr := fun i => rfl
  have hσ' : RepPerm σ⁻¹ (Native.permInv arr) := fun j => rfl
  have hB : ∀ i : Fin 12, B i = bvec 24 (Model.bmaskN i) := B_eq_bvec_bmaskN
  have hi : ∀ i : Fin 12,
      Native.wordN (Native.coeffN (Native.permWordN arr (Native.bmaskN i))) =
        Native.permWordN arr (Native.bmaskN i) ∧
      Native.wordN (Native.coeffN (Native.permWordN (Native.permInv arr) (Native.bmaskN i))) =
        Native.permWordN (Native.permInv arr) (Native.bmaskN i) := fun i => by
    have := List.all_eq_true.1 h5 i (List.mem_range.2 (by omega : (i : ℕ) < 12))
    simpa [Bool.and_eq_true] using this
  have hmem : σ ∈ AutPerm := by
    refine mem_AutPerm_of_basis (fun i => ?_) (fun i => ?_)
    · have e : B i ∘ ⇑σ = permWord σ⁻¹ (B i) := by
        funext k
        simp [permWord]
      rw [e, hB i, permWord_bvec hσ']
      apply bvec_mem_C_of
      have := (hi i).2
      simp only [native_wordN, native_coeffN, native_permWordN, native_bmaskN] at this
      exact this
    · have e : B i ∘ ⇑σ⁻¹ = permWord σ (B i) := rfl
      rw [e, hB i, permWord_bvec hσ]
      apply bvec_mem_C_of
      have := (hi i).1
      simp only [native_wordN, native_coeffN, native_permWordN, native_bmaskN] at this
      exact this
  exact ⟨⟨σ, hmem⟩, hσ⟩

@[expose] noncomputable def permOf (arr : Array ℕ) : AutPerm :=
  open Classical in
  if h : ∃ p : AutPerm, RepPerm (p : Equiv.Perm (Fin 24)) arr then h.choose else 1

theorem permOf_spec_of_exists {arr : Array ℕ}
    (hex : ∃ p : AutPerm, RepPerm (p : Equiv.Perm (Fin 24)) arr) :
    RepPerm (permOf arr : Equiv.Perm (Fin 24)) arr := by
  unfold permOf
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem permOf_spec {arr : Array ℕ} (h : Native.permValid arr = true) :
    RepPerm (permOf arr : Equiv.Perm (Fin 24)) arr :=
  permOf_spec_of_exists (permValid_spec h)

theorem permOf_eq {arr : Array ℕ} (p : AutPerm) (hp : RepPerm (p : Equiv.Perm (Fin 24)) arr) :
    permOf arr = p := by
  have h1 := permOf_spec_of_exists ⟨p, hp⟩
  refine Subtype.ext (Equiv.ext fun i => Fin.ext ?_)
  rw [h1 i, hp i]

@[expose] noncomputable def Native.Gen.pair : Native.Gen → Pvis
  | .rho q => rhoPair (pauliQ q)
  | .perm arr => permPairOf (permOf arr)
  | .sign a => signPair a
  | .xi => xiPair
  | .tau => 1

@[expose] noncomputable def Native.Gen.toLin : Native.Gen → (SpaceB ≃ₗ[ℚ] SpaceB)
  | .tau => tauB
  | g => thetaEquiv g.pair

theorem Native.Gen.toLin_rho (q : Model.Pauli) : (Native.Gen.rho q).toLin = rhoEquiv (pauliQ q) := rfl

theorem Native.Gen.toLin_perm (arr : Array ℕ) :
    (Native.Gen.perm arr).toLin = thetaEquiv (permPairOf (permOf arr)) := rfl

theorem Native.Gen.toLin_perm_of (arr : Array ℕ) (p : AutPerm)
    (hp : RepPerm (p : Equiv.Perm (Fin 24)) arr) :
    (Native.Gen.perm arr).toLin = thetaEquiv (permPairOf p) := by
  rw [Native.Gen.toLin_perm, permOf_eq p hp]

theorem Native.Gen.toLin_sign (a : ℕ) : (Native.Gen.sign a).toLin = thetaEquiv (signPair a) := rfl

theorem Native.Gen.toLin_xi : Native.Gen.xi.toLin = thetaEquiv xiPair := rfl

theorem Native.Gen.toLin_tau : Native.Gen.tau.toLin = tauB := rfl

theorem Native.Gen.toLin_mem_Gvis (g : Native.Gen) (hg : ¬ g = .tau) : g.toLin ∈ Gvis := by
  cases g
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact absurd rfl hg

theorem Native.Gen.toLin_mem_Gmat (g : Native.Gen) : g.toLin ∈ Gmat := by
  cases g
  · exact Hmat_le_Gmat (⟨_, rfl⟩ : _ ∈ Gvis)
  · exact Hmat_le_Gmat (⟨_, rfl⟩ : _ ∈ Gvis)
  · exact Hmat_le_Gmat (⟨_, rfl⟩ : _ ∈ Gvis)
  · exact Hmat_le_Gmat (⟨_, rfl⟩ : _ ∈ Gvis)
  · exact tauB_mem_Gmat

theorem applyGen_sound
    (g : Native.Gen) (hg : g.validB = true) (v : Native.DVec) :
    interp (Native.applyGen (Native.mkCtx ()) g v) = g.toLin (interp v) := by
  cases g with
  | rho q => exact applyGD_sound _ _ (gdSpec_rho q) v
  | perm arr =>
    exact applyGD_sound _ _ (gdSpec_perm arr (permOf arr) (permOf_spec hg)) v
  | sign a => exact applyGD_sound _ _ (gdSpec_sign a) v
  | xi => exact applyGD_sound _ _ gdSpec_xi v
  | tau => exact interp_applyTau v

theorem interp_eq_of_cf
    {v w : Native.DVec} (h : ∀ k, cf v k = cf w k) : interp v = interp w := by
  have : cf v = cf w := funext h
  rw [interp_eq_sum v, interp_eq_sum w, this]

theorem scale_getD_all (f : ℕ) (A : Array ℤ) (k : ℕ) :
    (Native.scale f A).getD k 0 = A.getD k 0 * 2 ^ f := by
  by_cases hk : k < A.size
  · exact Native.scale_getD f A k hk
  · have h0 : A.getD k 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have h1 : (Native.scale f A).getD k 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp [Native.scale]; omega)]
      rfl
    rw [h0, h1, zero_mul]

theorem eqv_sound
    {v w : Native.DVec} (h : v.eqv w = true) : interp v = interp w := by
  refine interp_eq_of_cf fun k => ?_
  unfold Native.DVec.eqv at h
  rw [beq_iff_eq] at h
  have hk := congrArg (fun A => A.getD k 0) h
  simp only [scale_getD_all] at hk
  have hq : (v.D.getD k 0 : ℚ) * 2 ^ (max v.e w.e - v.e) =
      (w.D.getD k 0 : ℚ) * 2 ^ (max v.e w.e - w.e) := by exact_mod_cast hk
  have h1 : (2 : ℚ) ^ (max v.e w.e) = 2 ^ v.e * 2 ^ (max v.e w.e - v.e) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_left _ _)]
  have h2 : (2 : ℚ) ^ (max v.e w.e) = 2 ^ w.e * 2 ^ (max v.e w.e - w.e) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_right _ _)]
  unfold cf
  have e1 : (v.D.getD k 0 : ℚ) / 2 ^ v.e =
      ((v.D.getD k 0 : ℚ) * 2 ^ (max v.e w.e - v.e)) / 2 ^ (max v.e w.e) := by
    rw [h1]
    field_simp
  have e2 : (w.D.getD k 0 : ℚ) / 2 ^ w.e =
      ((w.D.getD k 0 : ℚ) * 2 ^ (max v.e w.e - w.e)) / 2 ^ (max v.e w.e) := by
    rw [h2]
    field_simp
  rw [e1, e2, hq]

theorem getD_map_div2 (D : Array ℤ) (k : ℕ) : (D.map (· / 2)).getD k 0 = D.getD k 0 / 2 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases h : D[k]? with _ | x <;> simp

theorem cf_reduceN : ∀ (n : ℕ) (v : Native.DVec), cf (Native.reduceN n v) = cf v
  | 0, v => rfl
  | n + 1, v => by
    unfold Native.reduceN
    by_cases hc : (v.e > 0 && v.D.all (fun x => x % 2 == 0)) = true
    · rw [ite_eq_left hc]
      rw [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨he, hall⟩ := hc
      rw [cf_reduceN n]
      funext k
      have hev : v.D.getD k 0 % 2 = 0 := by
        by_cases hk : k < v.D.size
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
          have := (Array.all_eq_true.1 hall) k hk
          simpa using this
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
          rfl
      unfold cf
      show ((((v.D.map (· / 2)).getD k 0 : ℤ) : ℚ)) / 2 ^ (v.e - 1) = _
      rw [getD_map_div2]
      have hdv : ((v.D.getD k 0 / 2 : ℤ) : ℚ) * 2 = (v.D.getD k 0 : ℚ) := by
        have := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hev)
        exact_mod_cast this
      have hpw : (2 : ℚ) ^ v.e = 2 ^ (v.e - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel he]
      rw [hpw, ← hdv]
      field_simp
    · rw [ite_eq_right hc]

theorem interp_reduce
    (v : Native.DVec) : interp v.reduce = interp v :=
  interp_eq_of_cf fun k => by rw [Native.DVec.reduce, cf_reduceN]

@[expose] noncomputable def wordLin : List Native.Gen → (SpaceB ≃ₗ[ℚ] SpaceB)
  | [] => 1
  | g :: w => wordLin w * g.toLin

theorem wordLin_nil : wordLin [] = 1 := rfl

theorem wordLin_cons (g : Native.Gen) (w : List Native.Gen) :
    wordLin (g :: w) = wordLin w * g.toLin := rfl

theorem wordLin_apply_cons (g : Native.Gen) (w : List Native.Gen) (x : SpaceB) :
    wordLin (g :: w) x = wordLin w (g.toLin x) := rfl

theorem wordLin_append (w₁ w₂ : List Native.Gen) :
    wordLin (w₁ ++ w₂) = wordLin w₂ * wordLin w₁ := by
  induction w₁ with
  | nil => simp [wordLin_nil]
  | cons g w ih => rw [List.cons_append, wordLin_cons, ih, wordLin_cons, mul_assoc]

theorem wordLin_mem_Gmat (w : List Native.Gen) : wordLin w ∈ Gmat := by
  induction w with
  | nil => exact one_mem _
  | cons g w ih => exact mul_mem ih (Native.Gen.toLin_mem_Gmat g)

theorem wordLin_mem_Gvis (w : List Native.Gen) (hw : ∀ g ∈ w, ¬ g = .tau) : wordLin w ∈ Gvis := by
  induction w with
  | nil => exact one_mem _
  | cons g w ih =>
    exact mul_mem (ih fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
      (Native.Gen.toLin_mem_Gvis g (hw g List.mem_cons_self))

theorem wordLin_tauPow (e : ℕ) : wordLin (Native.Gen.tauPow e) = tauB ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [Native.Gen.tauPow, List.replicate_succ', wordLin_append, ← Native.Gen.tauPow, ih]
    rw [pow_succ']
    rfl

theorem wordLin_xiPow (e : ℕ) : wordLin (Native.Gen.xiPow e) = thetaEquiv xiPair ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [Native.Gen.xiPow, List.replicate_succ', wordLin_append, ← Native.Gen.xiPow, ih]
    rw [pow_succ']
    rfl

theorem wordLin_tauPow_two : wordLin (Native.Gen.tauPow 2) = tauB⁻¹ := by
  rw [wordLin_tauPow]
  have h3 := tauB_pow_three
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  exact h3

theorem evalWordC_cons (c : Native.Ctx) (g : Native.Gen) (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWordC c (g :: w) v = Native.evalWordC c w (Native.applyGen c g v).reduce := rfl

theorem evalWordC_sound :
    ∀ (w : List Native.Gen), (∀ g ∈ w, g.validB = true) →
    ∀ v : Native.DVec, interp (Native.evalWordC (Native.mkCtx ()) w v) = wordLin w (interp v)
  | [], _, v => rfl
  | g :: w, hw, v => by
    rw [evalWordC_cons, evalWordC_sound w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')),
      interp_reduce, applyGen_sound g (hw g List.mem_cons_self), wordLin_apply_cons]

theorem evalWord_sound
    (w : List Native.Gen) (hw : ∀ g ∈ w, g.validB = true) (v : Native.DVec) :
    interp (Native.evalWord w v) = wordLin w (interp v) := evalWordC_sound w hw v

theorem checkWordC_sound {w : List Native.Gen} {v v' : Native.DVec}
    (h : Native.checkWordC (Native.mkCtx ()) w v v' = true) :
    wordLin w (interp v) = interp v' := by
  unfold Native.checkWordC at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hv, he⟩ := h
  have hw : ∀ g ∈ w, g.validB = true := fun g hg => List.all_eq_true.1 hv g hg
  rw [← evalWordC_sound w hw v]
  exact eqv_sound he

theorem checkWord_sound {w : List Native.Gen} {v v' : Native.DVec}
    (h : Native.checkWord w v v' = true) : wordLin w (interp v) = interp v' :=
  checkWordC_sound h

theorem checkWordsC_sound
    {ws : List (List Native.Gen × Native.DVec × Native.DVec)}
    (h : Native.checkWordsC (Native.mkCtx ()) ws = true) :
    ∀ x ∈ ws, wordLin x.1 (interp x.2.1) = interp x.2.2 := fun x hx =>
  checkWordC_sound (List.all_eq_true.1 h x hx)

theorem checkWords_sound
    {ws : List (List Native.Gen × Native.DVec × Native.DVec)}
    (h : Native.checkWords ws = true) :
    ∀ x ∈ ws, wordLin x.1 (interp x.2.1) = interp x.2.2 := checkWordsC_sound h

theorem checkEqsC_sound
    {vs : Array Native.DVec} {items : List (List Native.Gen × ℕ × ℕ)}
    (h : Native.checkEqsC (Native.mkCtx ()) vs items = true) :
    ∀ x ∈ items, wordLin x.1 (interp vs[x.2.1]!) = interp vs[x.2.2]! := fun x hx =>
  checkWordC_sound (List.all_eq_true.1 h x hx)

theorem checkEqs_sound
    {vs : Array Native.DVec} {items : List (List Native.Gen × ℕ × ℕ)}
    (h : Native.checkEqs vs items = true) :
    ∀ x ∈ items, wordLin x.1 (interp vs[x.2.1]!) = interp vs[x.2.2]! := checkEqsC_sound h

end CFSG.Monster.AxisCount
