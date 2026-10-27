module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyMat
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Table
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporLy

open CFSG.Sporadic.He.Native CFSG.Monster.B.Fischer CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Assembly (IsElemAbelian)

@[expose, reducible] def vecAction :
    MulAction (GL (Fin 111) (ZMod 5)) (Fin 111 → ZMod 5) where
  smul g v := Matrix.mulVec (g : Matrix (Fin 111) (Fin 111) (ZMod 5)) v
  one_smul v := by
    show Matrix.mulVec ((1 : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show Matrix.mulVec ((g * h : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) v =
      Matrix.mulVec (g : Matrix (Fin 111) (Fin 111) (ZMod 5))
        (Matrix.mulVec (h : Matrix (Fin 111) (Fin 111) (ZMod 5)) v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

@[expose] def actV (P : Array Mat) (k : ℕ) (a : Array ℕ) : Array ℕ := mulVec 5 111 P[k]! a

@[expose] def keyV (a : Array ℕ) : ℕ := a.foldl (fun acc x => acc * 5 + x) 0

@[expose] def orbCert (P : Array Mat) (v : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (actV P) P.size keyV v fuel

@[expose] def orbitOK (P : Array Mat) (v : Array ℕ) (c : ArrCert) (N : ℕ) : Bool :=
  canonV 5 111 v && arrCertOK (actV P) P.size (canonV 5 111) keyV v c && (c.pts.size == N)

theorem orbit_table {n N : ℕ} {P : Array Mat} {v : Array ℕ} {c : ArrCert}
    {g : ℕ → GL (Fin 111) (ZMod 5)} (hPn : P.size = n) (hg : ∀ l < n, Rp P[l]! (g l))
    (hQ : Nat.card (Subgroup.closure (g '' {k | k < n})) ≤ N)
    (h : orbitOK P v c N = true) :
    (∃ gi : ℕ → GL (Fin 111) (ZMod 5), IsTable g n N gi c.edges c.par c.lab) ∧
      Nat.card (Subgroup.closure (g '' {k | k < n})) = N := by
  subst hPn
  let _ : MulAction (GL (Fin 111) (ZMod 5)) (Fin 111 → ZMod 5) := vecAction
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hv, hcert⟩, hN⟩ := h
  set Q := Subgroup.closure (g '' {k | k < P.size}) with hQdef
  have hact : ∀ k < P.size, ∀ a, canonV 5 111 a = true →
      toVec 5 111 (actV P k a) = g k • toVec 5 111 a := by
    intro k hk a _
    show toVec 5 111 (mulVec 5 111 P[k]! a) =
      Matrix.mulVec ((g k : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5))
        (toVec 5 111 a)
    have hk' : toMat 5 111 P[k]! =
        ((g k : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) := hg k hk
    rw [toVec_mulVec, hk']
  have hkey : ∀ a b, canonV 5 111 a = true → canonV 5 111 b = true →
      toVec 5 111 a = toVec 5 111 b → keyV a = keyV b := fun a b ha hb e => by
    rw [eq_of_toVec_eq ha hb e]
  have horb := orbit_of_arrCertOK (dec := toVec 5 111) hcert hact
  have hncard := ncard_orbit_of_arrCertOK (dec := toVec 5 111) hcert hact hkey
  set v' := toVec 5 111 v with hv'
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
      ∃ q : Q, (q : GL (Fin 111) (ZMod 5)) • v' = toVec 5 111 c.pts[i]! := by
    intro i hi
    have : toVec 5 111 c.pts[i]! ∈ MulAction.orbit Q v' := by
      rw [horb]
      exact ⟨i, by show i < c.pts.size; omega, rfl⟩
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  choose! gq hgq using hex
  have huniq : ∀ i < N, ∀ x ∈ Q, x • v' = toVec 5 111 c.pts[i]! →
      x = (gq i : GL (Fin 111) (ZMod 5)) := by
    intro i hi x hx e
    have := hqinj ⟨x, hx⟩ (gq i) (e.trans (hgq i hi).symm)
    exact congrArg Subtype.val this
  have hgenQ : ∀ k < P.size, g k ∈ Q := fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hNpts : c.pts.size = N := hN
  refine ⟨fun i => (gq i : GL (Fin 111) (ZMod 5)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hNpts]
    exact arrCertOK_pos hcert
  ·
    have h0 : 0 < N := by rw [← hNpts]; exact arrCertOK_pos hcert
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

structure LyE81Data where
  pW : Array (List (ℕ × ℕ))
  cubeW : Array (List (ℕ × ℕ))
  commW : Array (Array (List (ℕ × ℕ)))
  v : Array ℕ
  fuel : ℕ
  idZ : ℕ
  sets : List (List ℕ)

@[expose] def lyE81Check (X : LyE81Data) (A B : Mat) : Bool :=
  let r := slpM A B
  let P : Array Mat := X.pW.map (evalWord #[r.1, r.2.1])
  let c := orbCert P X.v X.fuel
  r.2.2 && X.pW.toList.all (fun w => w.all fun x => decide (x.1 < 2)) &&
    pcCheck 7 P X.cubeW X.commW && orbitOK P X.v c 2187 &&
    tabCheck 7 2187 c.edges c.par c.lab X.idZ X.sets

theorem lyE81_sound (X : LyE81Data) {A B : Mat} {a b : GL (Fin 111) (ZMod 5)} (hA : Rp A a)
    (hB : Rp B b) {J : Subgroup (GL (Fin 111) (ZMod 5))} [Finite J] (ha : a ∈ J) (hb : b ∈ J)
    (hJ : (Nat.card J).factorization 3 = 7) (h : lyE81Check X A B = true) :
    ∃ (Q : Subgroup (GL (Fin 111) (ZMod 5))) (z : GL (Fin 111) (ZMod 5)), Q ≤ J ∧
      Nat.card Q = 3 ^ (Nat.card J).factorization 3 ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ Q ∧
      (∀ q ∈ Q, q * z = z * q) ∧
      ∀ s ∈ Q, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup (GL (Fin 111) (ZMod 5)), E ≤ J ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
          s ∈ E ∧ z ∈ E := by
  simp only [lyE81Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hslp, hlet⟩, hpc⟩, horb⟩, htab⟩ := h
  obtain ⟨P, hPdef⟩ : ∃ P : Array Mat,
      P = X.pW.map (evalWord #[(slpM A B).1, (slpM A B).2.1]) := ⟨_, rfl⟩
  rw [← hPdef] at hpc horb htab
  obtain ⟨c, hcdef⟩ : ∃ c : ArrCert, c = orbCert P X.v X.fuel := ⟨_, rfl⟩
  rw [← hcdef] at horb htab
  obtain ⟨hc, hd⟩ := slpM_rep hA hB hslp
  have hslpJ := slpG_mem ha hb
  let cd : ℕ → GL (Fin 111) (ZMod 5) := fun l => if l = 0 then (slpG a b).1 else (slpG a b).2
  have hcdJ : ∀ l, cd l ∈ J := fun l => by
    by_cases hl : l = 0
    · simp only [cd, hl, ite_true]
      exact hslpJ.1
    · simp only [cd, hl, ite_false]
      exact hslpJ.2
  have hgs : ∀ l < 2, toMat 5 111 (#[(slpM A B).1, (slpM A B).2.1] : Array Mat)[l]! =
      ((cd l : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hc
    · exact hd
  have hsize : P.size = 7 := pcCheck_size hpc
  have hpWsize : X.pW.size = 7 := by rw [hPdef, Array.size_map] at hsize; exact hsize
  have hletters : ∀ k < 7, ∀ x ∈ X.pW[k]!, x.1 < 2 := by
    intro k hk x hx
    have := List.all_eq_true.1 hlet (X.pW[k]!) (by
      rw [getElem!_pos X.pW k (by omega)]
      exact Array.getElem_mem_toList (by omega))
    simpa using List.all_eq_true.1 this x hx
  let g : ℕ → GL (Fin 111) (ZMod 5) := fun k => wordG cd (X.pW[k]!)
  have hg : ∀ l < 7, Rp P[l]! (g l) := by
    intro l hl
    have hP : P[l]! = evalWord #[(slpM A B).1, (slpM A B).2.1] X.pW[l]! := by
      rw [hPdef, getElem!_pos _ l (by simpa using hpWsize ▸ hl), Array.getElem_map,
        getElem!_pos X.pW l (by omega)]
    rw [hP]
    exact toMat_evalWord_eq fun x hx => hgs x.1 (hletters l hl x hx)
  have hgJ : ∀ k, g k ∈ J := fun k => wordG_mem fun x _ => hcdJ x.1
  obtain ⟨hcube, hconj⟩ := pc_sound hg hpc
  have hQp : IsPGroup 3 (tailGroup g 7 0) := isPGroup_tailGroup g 7 hcube hconj 0
  have hQeq : tailGroup g 7 0 = Subgroup.closure (g '' {k | k < 7}) := by
    have hs : ({l | 0 ≤ l ∧ l < 7} : Set ℕ) = {k | k < 7} := by
      ext l
      simp
    unfold tailGroup
    rw [hs]
  rw [hQeq] at hQp
  have hQJ : Subgroup.closure (g '' {k | k < 7}) ≤ J := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact hgJ k
  have hle : Nat.card (Subgroup.closure (g '' {k | k < 7})) ≤ 2187 := by
    have := card_le_of_isPGroup hQJ hQp
    rw [hJ] at this
    simpa using this
  obtain ⟨⟨gi, hT⟩, hQN⟩ := orbit_table hsize hg hle horb
  obtain ⟨z, hzQ, hz3, hz1, hzc, hgood⟩ := tab_sound hT (fun k _ => hgJ k) htab
  refine ⟨Subgroup.closure (g '' {k | k < 7}), z, hQJ, ?_, hz3, hz1, hzQ, hzc, hgood⟩
  rw [hQN, hJ]
  norm_num

theorem exists_e81_of_lyE81Check (X : LyE81Data) {A B : Mat} {a b : GL (Fin 111) (ZMod 5)}
    (hA : Rp A a) (hB : Rp B b) {J : Subgroup (GL (Fin 111) (ZMod 5))} [Finite J] (ha : a ∈ J)
    (hb : b ∈ J) (hJ : (Nat.card J).factorization 3 = 7) (h : lyE81Check X A B = true)
    {P : Subgroup J} (hP : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B' E : Subgroup J, B' ≤ P ∧ 9 ≤ Nat.card B' ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      ∀ b ∈ B', ∀ d ∈ E, b * d = d * b := by
  obtain ⟨Q, z, hQJ, hQ, hz3, hz1, hzQ, hzc, hgood⟩ := lyE81_sound X hA hB ha hb hJ h
  exact exists_e81_of_e27_ambient hQJ hQ hz3 hz1 hzQ hzc le_rfl (by omega) hgood hP hP27

end CFSG.RankThree.PartTwo.Sec4.Item434SporLy
