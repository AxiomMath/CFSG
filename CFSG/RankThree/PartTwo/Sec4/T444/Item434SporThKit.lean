module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporThMat
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Table2
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)

@[expose] def encV (v : V4) : Array ℕ := #[v.w0.toNat, v.w1.toNat, v.w2.toNat, v.w3.toNat]

@[expose] def decV (a : Array ℕ) : V4 :=
  ⟨UInt64.ofNat a[0]!, UInt64.ofNat a[1]!, UInt64.ofNat a[2]!, UInt64.ofNat a[3]!⟩

@[expose] def validV (a : Array ℕ) : Bool :=
  a.size == 4 && decide (a[0]! < 2 ^ 64) && decide (a[1]! < 2 ^ 64) && decide (a[2]! < 2 ^ 64) &&
    decide (a[3]! < 2 ^ 56)

@[expose] def keyV (a : Array ℕ) : ℕ := a[0]! + 2 ^ 64 * a[1]! + 2 ^ 128 * a[2]! + 2 ^ 192 * a[3]!

theorem encV_size (v : V4) : (encV v).size = 4 := rfl

theorem encV_get0 (v : V4) : (encV v)[0]! = v.w0.toNat := rfl

theorem encV_get1 (v : V4) : (encV v)[1]! = v.w1.toNat := rfl

theorem encV_get2 (v : V4) : (encV v)[2]! = v.w2.toNat := rfl

theorem encV_get3 (v : V4) : (encV v)[3]! = v.w3.toNat := rfl

theorem decV_encV (v : V4) : decV (encV v) = v := by
  obtain ⟨w0, w1, w2, w3⟩ := v
  simp only [decV, encV_get0, encV_get1, encV_get2, encV_get3, UInt64.ofNat_toNat]

theorem validV_spec {a : Array ℕ} (h : validV a = true) :
    a.size = 4 ∧ a[0]! < 2 ^ 64 ∧ a[1]! < 2 ^ 64 ∧ a[2]! < 2 ^ 64 ∧ a[3]! < 2 ^ 56 := by
  simp only [validV, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem eq_four {a : Array ℕ} (hs : a.size = 4) : a = #[a[0]!, a[1]!, a[2]!, a[3]!] := by
  apply Array.ext (by simp [hs])
  intro i hi _
  have hi4 : i < 4 := by omega
  interval_cases i
  · exact (getElem!_pos a 0 (by omega)).symm
  · exact (getElem!_pos a 1 (by omega)).symm
  · exact (getElem!_pos a 2 (by omega)).symm
  · exact (getElem!_pos a 3 (by omega)).symm

theorem encV_decV {a : Array ℕ} (h : validV a = true) : encV (decV a) = a := by
  obtain ⟨hs, h0, h1, h2, h3⟩ := validV_spec h
  have h3' : a[3]! < 2 ^ 64 := lt_trans h3 (by norm_num)
  conv_rhs => rw [eq_four hs]
  simp only [encV, decV, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3']

theorem wf_decV {a : Array ℕ} (h : validV a = true) : (decV a).wf = true := by
  obtain ⟨hs, h0, h1, h2, h3⟩ := validV_spec h
  rw [V4.wf_iff_w3]
  show (UInt64.ofNat a[3]!).toNat < 2 ^ 56
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans h3 (by norm_num))]
  exact h3

theorem validV_encV {v : V4} (h : v.wf = true) : validV (encV v) = true := by
  rw [V4.wf_iff_w3] at h
  have h0 : v.w0.toNat < 2 ^ 64 := v.w0.toNat_lt
  have h1 : v.w1.toNat < 2 ^ 64 := v.w1.toNat_lt
  have h2 : v.w2.toNat < 2 ^ 64 := v.w2.toNat_lt
  unfold validV
  rw [encV_size, encV_get0, encV_get1, encV_get2, encV_get3]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨trivial, decide_eq_true h0⟩, decide_eq_true h1⟩, decide_eq_true h2⟩, decide_eq_true h⟩

theorem eq_of_toVec_eq {a b : Array ℕ} (ha : validV a = true) (hb : validV b = true)
    (h : (decV a).toVec = (decV b).toVec) : a = b := by
  have := V4.eq_of_toVec_eq (wf_decV ha) (wf_decV hb) h
  rw [← encV_decV ha, ← encV_decV hb, this]

@[expose, reducible] def vecAction :
    MulAction (GL (Fin 248) (ZMod 2)) (Fin 248 → ZMod 2) where
  smul g v := Matrix.mulVec (g : Matrix (Fin 248) (Fin 248) (ZMod 2)) v
  one_smul v := by
    show Matrix.mulVec ((1 : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show Matrix.mulVec ((g * h : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) v =
      Matrix.mulVec (g : Matrix (Fin 248) (Fin 248) (ZMod 2))
        (Matrix.mulVec (h : Matrix (Fin 248) (Fin 248) (ZMod 2)) v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

@[expose] def tabsOf (P : Array Mat) : Array (Array V4) :=
  P.map fun M => frTable (transposeRows M)

@[expose] def actV (tabs : Array (Array V4)) (k : ℕ) (a : Array ℕ) : Array ℕ :=
  encV (frApply tabs[k]! (decV a))

@[expose] def orbCert (tabs : Array (Array V4)) (v : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (actV tabs) tabs.size keyV v fuel

@[expose] def arrCertOK' (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (valid : Array ℕ → Bool)
    (key : Array ℕ → ℕ) (root : Array ℕ) (c : ArrCert) : Bool :=
  decide (0 < c.pts.size) && c.pts[0]! == root &&
    (List.range c.pts.size).all (arrPointOK act ngen valid c) &&
    isStrictAsc ((c.pts.toList.map key).mergeSort (fun a b => decide (a ≤ b)))

theorem arrCertOK_of' {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ} {valid : Array ℕ → Bool}
    {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}
    (h : arrCertOK' act ngen valid key root c = true) :
    arrCertOK act ngen valid key root c = true := by
  simp only [arrCertOK', arrCertOK, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨⟨h1, h2⟩, h3⟩, decide_eq_true (pairwise_of_isStrictAsc _ h4)⟩

@[expose] def orbitOK (tabs : Array (Array V4)) (v : Array ℕ) (c : ArrCert) (N : ℕ) : Bool :=
  validV v && arrCertOK' (actV tabs) tabs.size validV keyV v c && (c.pts.size == N)

theorem getElem!_map_of_lt {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {k : ℕ} (hk : k < A.size) : (A.map f)[k]! = f A[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos A k hk]

theorem orbit_table {n N : ℕ} {P : Array Mat} {v : Array ℕ} {c : ArrCert}
    {g : ℕ → GL (Fin 248) (ZMod 2)} (hPn : P.size = n) (hg : ∀ l < n, Rp P[l]! (g l))
    (hQ : Nat.card (Subgroup.closure (g '' {k | k < n})) ≤ N)
    (h : orbitOK (tabsOf P) v c N = true) :
    (∃ gi : ℕ → GL (Fin 248) (ZMod 2), IsTable g n N gi c.edges c.par c.lab) ∧
      Nat.card (Subgroup.closure (g '' {k | k < n})) = N := by
  let _ : MulAction (GL (Fin 248) (ZMod 2)) (Fin 248 → ZMod 2) := vecAction
  have htsize : (tabsOf P).size = n := by simp [tabsOf, hPn]
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hv, hcert'⟩, hN⟩ := h
  have hcert := arrCertOK_of' hcert'
  rw [htsize] at hcert
  set Q := Subgroup.closure (g '' {k | k < n}) with hQdef
  have hact : ∀ k < n, ∀ a, validV a = true →
      (decV (actV (tabsOf P) k a)).toVec = g k • (decV a).toVec := by
    intro k hk a _
    show (decV (actV (tabsOf P) k a)).toVec =
      Matrix.mulVec ((g k : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))
        (decV a).toVec
    have hk' : rowsMatrix P[k]! =
        ((g k : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) := hg k hk
    have htab : (tabsOf P)[k]! = frTable (transposeRows P[k]!) :=
      getElem!_map_of_lt P _ (by omega)
    rw [actV, decV_encV, htab, frApply_transposeRows_toVec, hk']
  have hkey : ∀ a b, validV a = true → validV b = true →
      (decV a).toVec = (decV b).toVec → keyV a = keyV b := fun a b ha hb e => by
    rw [eq_of_toVec_eq ha hb e]
  have horb := orbit_of_arrCertOK (dec := fun a => (decV a).toVec) hcert hact
  have hncard := ncard_orbit_of_arrCertOK (dec := fun a => (decV a).toVec) hcert hact hkey
  set v' := (decV v).toVec with hv'
  have hfin : Finite Q := inferInstance
  have hsurj : Function.Surjective
      (fun q : Q => (⟨q • v', MulAction.mem_orbit v' q⟩ : MulAction.orbit Q v')) := by
    rintro ⟨_, q, rfl⟩
    exact ⟨q, rfl⟩
  have hcardorb : Nat.card (MulAction.orbit Q v') = N := by
    rw [Nat.card_coe_set_eq, hncard, hN]
  have hbij := hsurj.bijective_of_nat_card_le (by rw [hcardorb]; exact hQ)
  have hqinj : ∀ q q' : Q, q • v' = q' • v' → q = q' := fun q q' e =>
    hbij.1 (Subtype.ext e)
  have hQN : Nat.card Q = N := by
    rw [← hcardorb]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  refine ⟨?_, hQN⟩
  have hex : ∀ i : ℕ, i < N →
      ∃ q : Q, (q : GL (Fin 248) (ZMod 2)) • v' = (decV c.pts[i]!).toVec := by
    intro i hi
    have : (decV c.pts[i]!).toVec ∈ MulAction.orbit Q v' := by
      rw [horb]
      exact ⟨i, by show i < c.pts.size; omega, rfl⟩
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  choose! gq hgq using hex
  have huniq : ∀ i < N, ∀ x ∈ Q, x • v' = (decV c.pts[i]!).toVec →
      x = (gq i : GL (Fin 248) (ZMod 2)) := by
    intro i hi x hx e
    have := hqinj ⟨x, hx⟩ (gq i) (e.trans (hgq i hi).symm)
    exact congrArg Subtype.val this
  have hgenQ : ∀ k < n, g k ∈ Q := fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hNpts : c.pts.size = N := hN
  refine ⟨fun i => (gq i : GL (Fin 248) (ZMod 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hNpts]
    exact arrCertOK_pos hcert
  · have h0 : 0 < N := by rw [← hNpts]; exact arrCertOK_pos hcert
    refine (huniq 0 h0 1 (Subgroup.one_mem _) ?_).symm
    rw [arrCertOK_root hcert]
    exact one_smul _ _
  · intro i hi k hk
    obtain ⟨h1, h2⟩ := arrCertOK_edge hcert (by rw [hNpts]; exact hi) hk
    refine ⟨by rw [← hNpts]; exact h1, ?_⟩
    have hvalid := arrCertOK_valid hcert (by rw [hNpts]; exact hi : i < c.pts.size)
    refine (huniq _ (by rw [← hNpts]; exact h1) _
      (Subgroup.mul_mem _ (hgenQ k hk) (gq i).2) ?_).symm
    rw [h2, hact k hk _ hvalid, ← hgq i hi, mul_smul]
  · intro i hi hi0
    obtain ⟨h1, h2, h3⟩ := arrCertOK_tree hcert hi0 (by rw [hNpts]; exact hi)
    refine ⟨h1, h2, ?_⟩
    have hp : c.par[i]! < N := lt_trans h1 hi
    have hvalid := arrCertOK_valid hcert (by rw [hNpts]; exact hp : c.par[i]! < c.pts.size)
    refine (huniq i hi _ (Subgroup.mul_mem _ (hgenQ _ h2) (gq _).2) ?_).symm
    rw [h3, hact _ h2 _ hvalid, ← hgq _ hp, mul_smul]
  · intro i hi j hj e
    have := arrCertOK_dec_inj hcert hkey (by rw [hNpts]; exact hi) (by rw [hNpts]; exact hj)
      (by rw [← hgq i hi, ← hgq j hj, e])
    exact this
  · intro x hx
    have : x • v' ∈ MulAction.orbit Q v' := MulAction.mem_orbit_iff.2 ⟨⟨x, hx⟩, rfl⟩
    rw [horb] at this
    obtain ⟨i, hi, hix⟩ := this
    have hiN : i < N := by rw [← hNpts]; exact hi
    exact ⟨i, hiN, (huniq i hiN x hx hix.symm).symm⟩

structure ThE81Data where
  w61 : List (ℕ × ℕ)
  w62 : List (ℕ × ℕ)
  pW : Array (List (ℕ × ℕ))
  cubeW : Array (List (ℕ × ℕ))
  commW : Array (Array (List (ℕ × ℕ)))
  v : Array ℕ
  fuel : ℕ
  idZ : ℕ
  sets : List (List ℕ)

@[expose] def thE81Check (X : ThE81Data) (A B : Mat) : Bool :=
  let gs : Array Mat := #[evalWord #[A, B] X.w61, evalWord #[A, B] X.w62]
  let P : Array Mat := X.pW.map (evalWord gs)
  let tabs := tabsOf P
  let c := orbCert tabs X.v X.fuel
  X.w61.all (fun x => decide (x.1 < 2)) && X.w62.all (fun x => decide (x.1 < 2)) &&
    X.pW.toList.all (fun w => w.all fun x => decide (x.1 < 2)) &&
    pcCheck 10 P X.cubeW X.commW && orbitOK tabs X.v c 59049 &&
    tabCheck2 10 59049 c.edges c.par c.lab X.idZ X.sets

theorem thE81_sound (X : ThE81Data) {A B : Mat} {a b : GL (Fin 248) (ZMod 2)} (hA : Rp A a)
    (hB : Rp B b) {J : Subgroup (GL (Fin 248) (ZMod 2))} [Finite J] (ha : a ∈ J) (hb : b ∈ J)
    (hJ : (Nat.card J).factorization 3 = 10) (h : thE81Check X A B = true) :
    ∃ (Q : Subgroup (GL (Fin 248) (ZMod 2))) (z : GL (Fin 248) (ZMod 2)), Q ≤ J ∧
      Nat.card Q = 3 ^ (Nat.card J).factorization 3 ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧
      (∀ q ∈ Q, q * z = z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup (GL (Fin 248) (ZMod 2)), E ≤ J ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
          s ∈ E ∧ z ∈ E := by
  simp only [thE81Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl1, hl2⟩, hl3⟩, hpc⟩, horb⟩, htab⟩ := h
  obtain ⟨gs, hgsdef⟩ : ∃ gs : Array Mat,
      gs = #[evalWord #[A, B] X.w61, evalWord #[A, B] X.w62] := ⟨_, rfl⟩
  rw [← hgsdef] at hpc horb htab
  obtain ⟨P, hPdef⟩ : ∃ P : Array Mat, P = X.pW.map (evalWord gs) := ⟨_, rfl⟩
  rw [← hPdef] at hpc horb htab
  obtain ⟨c, hcdef⟩ : ∃ c : ArrCert, c = orbCert (tabsOf P) X.v X.fuel := ⟨_, rfl⟩
  rw [← hcdef] at horb htab
  let cd0 : ℕ → GL (Fin 248) (ZMod 2) := fun l => if l = 0 then a else b
  have hcd0J : ∀ l, cd0 l ∈ J := fun l => by
    by_cases hl : l = 0
    · simp only [cd0, hl, ite_true]
      exact ha
    · simp only [cd0, hl, ite_false]
      exact hb
  have hAB : ∀ l < 2, Rp (#[A, B] : Array Mat)[l]! (cd0 l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hA
    · exact hB
  have hletters1 : ∀ x ∈ X.w61, x.1 < 2 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 hl1 x hx)
  have hletters2 : ∀ x ∈ X.w62, x.1 < 2 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 hl2 x hx)
  have hx61 : Rp (evalWord #[A, B] X.w61) (wordG cd0 X.w61) :=
    rowsMatrix_evalWord_eq fun x hx => hAB x.1 (hletters1 x hx)
  have hx62 : Rp (evalWord #[A, B] X.w62) (wordG cd0 X.w62) :=
    rowsMatrix_evalWord_eq fun x hx => hAB x.1 (hletters2 x hx)
  have hx61J : wordG cd0 X.w61 ∈ J := wordG_mem fun x _ => hcd0J x.1
  have hx62J : wordG cd0 X.w62 ∈ J := wordG_mem fun x _ => hcd0J x.1
  let cd1 : ℕ → GL (Fin 248) (ZMod 2) := fun l =>
    if l = 0 then wordG cd0 X.w61 else wordG cd0 X.w62
  have hcd1J : ∀ l, cd1 l ∈ J := fun l => by
    by_cases hl : l = 0
    · simp only [cd1, hl, ite_true]
      exact hx61J
    · simp only [cd1, hl, ite_false]
      exact hx62J
  have hgs1 : ∀ l < 2, Rp gs[l]! (cd1 l) := by
    intro l hl
    rw [hgsdef]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hx61
    · exact hx62
  have hsize : P.size = 10 := pcCheck_size hpc
  have hpWsize : X.pW.size = 10 := by rw [hPdef, Array.size_map] at hsize; exact hsize
  have hletters : ∀ k < 10, ∀ x ∈ X.pW[k]!, x.1 < 2 := by
    intro k hk x hx
    have := List.all_eq_true.1 hl3 (X.pW[k]!) (by
      rw [getElem!_pos X.pW k (by omega)]
      exact Array.getElem_mem_toList (by omega))
    exact of_decide_eq_true (List.all_eq_true.1 this x hx)
  let g : ℕ → GL (Fin 248) (ZMod 2) := fun k => wordG cd1 (X.pW[k]!)
  have hg : ∀ l < 10, Rp P[l]! (g l) := by
    intro l hl
    have hP : P[l]! = evalWord gs X.pW[l]! := by
      rw [hPdef, getElem!_map_of_lt X.pW (evalWord gs) (by omega)]
    rw [hP]
    exact rowsMatrix_evalWord_eq fun x hx => hgs1 x.1 (hletters l hl x hx)
  have hgJ : ∀ k, g k ∈ J := fun k => wordG_mem fun x _ => hcd1J x.1
  obtain ⟨hcube, hconj⟩ := pc_sound hg hpc
  have hQp : IsPGroup 3 (tailGroup g 10 0) := isPGroup_tailGroup g 10 hcube hconj 0
  have hQeq : tailGroup g 10 0 = Subgroup.closure (g '' {k | k < 10}) := by
    have hs : ({l | 0 ≤ l ∧ l < 10} : Set ℕ) = {k | k < 10} := by
      ext l
      simp
    unfold tailGroup
    rw [hs]
  rw [hQeq] at hQp
  have hQJ : Subgroup.closure (g '' {k | k < 10}) ≤ J := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact hgJ k
  have hle : Nat.card (Subgroup.closure (g '' {k | k < 10})) ≤ 59049 := by
    have := card_le_of_isPGroup hQJ hQp
    rw [hJ] at this
    simpa using this
  obtain ⟨⟨gi, hT⟩, hQN⟩ := orbit_table hsize hg hle horb
  obtain ⟨z, hzQ, hz3, hz1, hzc, hgood⟩ := tab_sound2 hT (fun k _ => hgJ k) htab
  refine ⟨Subgroup.closure (g '' {k | k < 10}), z, hQJ, ?_, hz3, hz1, hzQ, hzc, hgood⟩
  rw [hQN, hJ]
  norm_num

theorem exists_e81_of_thE81Check (X : ThE81Data) {A B : Mat} {a b : GL (Fin 248) (ZMod 2)}
    (hA : Rp A a) (hB : Rp B b) {J : Subgroup (GL (Fin 248) (ZMod 2))} [Finite J] (ha : a ∈ J)
    (hb : b ∈ J) (hJ : (Nat.card J).factorization 3 = 10) (h : thE81Check X A B = true)
    {P : Subgroup J} (hP : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B' E : Subgroup J, B' ≤ P ∧ 9 ≤ Nat.card B' ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      ∀ b ∈ B', ∀ d ∈ E, b * d = d * b := by
  obtain ⟨Q, z, hQJ, hQ, hz3, hz1, hzQ, hzc, hgood⟩ := thE81_sound X hA hB ha hb hJ h
  exact exists_e81_of_e27_ambient hQJ hQ hz3 hz1 hzQ hzc le_rfl (by omega) hgood hP hP27

end CFSG.RankThree.PartTwo.Sec4.Item434SporTh
