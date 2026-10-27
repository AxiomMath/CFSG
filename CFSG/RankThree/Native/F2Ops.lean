module

public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {d : ℕ}

theorem mmul_assoc (A B C : ℕ) : mmul d (mmul d A B) C = mmul d A (mmul d B C) := by
  apply mat_ext (mmul_lt _ _) (mmul_lt _ _)
  intro k hk
  rw [row_mmul _ _ hk, row_mmul _ _ hk, row_mmul _ _ hk, vmul_mmul]

theorem mmul_congr_right {A X Y : ℕ} (h : ∀ k < d, row d X k = row d Y k) :
    mmul d A X = mmul d A Y := by
  have hv : ∀ v, vmul d v X = vmul d v Y := by
    intro v
    unfold vmul
    have : ∀ L : List ℕ, (∀ k ∈ L, k < d) →
        L.foldr (fun k acc => if v.testBit k then row d X k ^^^ acc else acc) 0 =
          L.foldr (fun k acc => if v.testBit k then row d Y k ^^^ acc else acc) 0 := by
      intro L hL
      induction L with
      | nil => rfl
      | cons k l ih =>
        rw [List.foldr_cons, List.foldr_cons, ih fun j hj => hL j (List.mem_cons_of_mem _ hj),
          h k (hL k List.mem_cons_self)]
    exact this _ fun k hk => List.mem_range.1 hk
  unfold mmul
  simp only [hv]

theorem row_idM_mmul (hd : 0 < d) (X : ℕ) {k : ℕ} (hk : k < d) :
    row d (mmul d (idM d) X) k = row d X k := by
  rw [row_mmul _ _ hk, row_idM hd hk, vmul_unit _ hk]

theorem idM_lt : idM d < 2 ^ (d * d) :=
  bs_lt (fun _ => Nat.mod_lt _ (Nat.two_pow_pos d)) d

theorem mmul_idM_idM (hd : 0 < d) : mmul d (idM d) (idM d) = idM d :=
  mat_ext (mmul_lt _ _) idM_lt fun _ hk => row_idM_mmul hd _ hk

variable {V : Array ℕ}

theorem Inv.symm {A A' : ℕ} (h : Inv d V A A') : Inv d V A' A :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem inv_idM (hd : 0 < d) (hVd : ∀ v ∈ V, v < 2 ^ d) : Inv d V (idM d) (idM d) :=
  ⟨fun v hv => by rwa [vmul_idM hd (hVd v hv)], fun v hv => by rwa [vmul_idM hd (hVd v hv)],
    mmul_idM_idM hd, mmul_idM_idM hd⟩

theorem maps_mmul {A B : ℕ} (hA : ∀ v ∈ V, vmul d v A ∈ V) (hB : ∀ v ∈ V, vmul d v B ∈ V) :
    ∀ v ∈ V, vmul d v (mmul d A B) ∈ V := fun v hv => by
  rw [vmul_mmul]
  exact hB _ (hA v hv)

theorem mmul_inv_cancel (hd : 0 < d) {A A' B B' : ℕ} (hA : mmul d A A' = idM d)
    (hB : mmul d B B' = idM d) : mmul d (mmul d A B) (mmul d B' A') = idM d := by
  rw [mmul_assoc, ← mmul_assoc B, hB,
    mmul_congr_right (fun k hk => row_idM_mmul hd A' hk), hA]

theorem Inv.mul (hd : 0 < d) {A A' B B' : ℕ} (hA : Inv d V A A') (hB : Inv d V B B') :
    Inv d V (mmul d A B) (mmul d B' A') :=
  ⟨maps_mmul hA.1 hB.1, maps_mmul hB.2.1 hA.2.1, mmul_inv_cancel hd hA.2.2.1 hB.2.2.1,
    mmul_inv_cancel hd hB.2.2.2 hA.2.2.2⟩

theorem compA_permOfMat {A B : ℕ} (hB : ∀ v ∈ V, vmul d v B ∈ V) :
    compA V.size (permOfMat d V A) (permOfMat d V B) = permOfMat d V (mmul d B A) :=
  (permOfMat_mmul hB).symm

theorem invCand_size (n : ℕ) (t : Array ℕ) : (invCand n t).size = n := by
  rw [invCand_eq_foldl]
  have : ∀ (l : List ℕ) (r : Array ℕ), (l.foldl (fun r i => r.set! t[i]! i) r).size = r.size := by
    intro l
    induction l with
    | nil => intro r; rfl
    | cons x l ih => intro r; rw [List.foldl_cons, ih, Array.size_set!]
  rw [this, Array.size_replicate]

theorem invCand_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {A A' : ℕ} (h : Inv d V A A') : invCand V.size (permOfMat d V A) = permOfMat d V A' := by
  have hr := rep_invCand (rep_permOfMat hd hV hVd h)
  apply eq_permOfMat hV (invCand_size _ _)
  intro i hi
  have hj := hr.lt hi
  refine ⟨hj, ?_⟩
  set j := (invCand V.size (permOfMat d V A))[i]!
  have hAj : (permOfMat d V A)[j]! = i := by
    have e : (⟨j, hj⟩ : Fin V.size) = (sigma d V A)⁻¹ ⟨i, hi⟩ := Fin.ext (hr.apply hi)
    rw [(rep_permOfMat hd hV hVd h).apply hj, e]
    simp
  have hvi : V[i]! = vmul d V[j]! A := by
    rw [← hAj, permOfMat_get hj]
    exact (getElem_vidx (h.1 _ (mem_of_lt hj))).2
  rw [hvi, ← vmul_mmul, h.2.2.1, vmul_idM hd (hVd _ (mem_of_lt hj))]

variable (d) in
@[expose] def mpow (A : ℕ) : ℕ → ℕ
  | 0 => idM d
  | e + 1 => mmul d (mpow A e) A

theorem maps_mpow (hd : 0 < d) (hVd : ∀ v ∈ V, v < 2 ^ d) {A : ℕ}
    (hA : ∀ v ∈ V, vmul d v A ∈ V) : ∀ e, ∀ v ∈ V, vmul d v (mpow d A e) ∈ V
  | 0 => fun v hv => by rwa [mpow, vmul_idM hd (hVd v hv)]
  | e + 1 => maps_mmul (maps_mpow hd hVd hA e) hA

theorem powArr_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d) {A : ℕ}
    (hA : ∀ v ∈ V, vmul d v A ∈ V) :
    ∀ e, CFSG.Monster.B.Mathieu.powArr V.size (permOfMat d V A) e = permOfMat d V (mpow d A e)
  | 0 => (permOfMat_idM hd hV hVd).symm
  | e + 1 => by
    rw [CFSG.Monster.B.Mathieu.powArr, powArr_permOfMat hd hV hVd hA e,
      compA_permOfMat (maps_mpow hd hVd hA e), mpow]

theorem conjA_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {G G' Y : ℕ} (hG : Inv d V G G') (hY : ∀ v ∈ V, vmul d v Y ∈ V) :
    conjA V.size (permOfMat d V G) (permOfMat d V Y) =
      permOfMat d V (mmul d (mmul d G' Y) G) := by
  rw [conjA, invCand_permOfMat hd hV hVd hG, compA_permOfMat hG.2.1,
    compA_permOfMat (maps_mmul hG.2.1 hY)]

theorem commutatorA_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {G G' H H' : ℕ} (hG : Inv d V G G') (hH : Inv d V H H') :
    commutatorA V.size (permOfMat d V G) (permOfMat d V H) =
      permOfMat d V (mmul d (mmul d H' G') (mmul d H G)) := by
  rw [commutatorA, invCand_permOfMat hd hV hVd hG, invCand_permOfMat hd hV hVd hH,
    compA_permOfMat hH.1, compA_permOfMat hH.2.1, compA_permOfMat (maps_mmul hH.2.1 hG.2.1)]

theorem commA_permOfMat {l : ℕ → List ℕ} (hs : Spans d V l) {P X : ℕ}
    (hP : ∀ v ∈ V, vmul d v P ∈ V) (hX : ∀ v ∈ V, vmul d v X ∈ V) :
    commA V.size (permOfMat d V P) (permOfMat d V X) = Nat.beq (mmul d X P) (mmul d P X) := by
  rw [commA, compA_permOfMat hX, compA_permOfMat hP]
  exact eqA_permOfMat hs (maps_mmul hX hP) (maps_mmul hP hX) (mmul_lt _ _) (mmul_lt _ _)

theorem beq_permOfMat {l : ℕ → List ℕ} (hs : Spans d V l) {A B : ℕ}
    (hA : ∀ v ∈ V, vmul d v A ∈ V) (hB : ∀ v ∈ V, vmul d v B ∈ V) (hAl : A < 2 ^ (d * d))
    (hBl : B < 2 ^ (d * d)) : (permOfMat d V A == permOfMat d V B) = Nat.beq A B := by
  rw [← eqA_permOfMat hs hA hB hAl hBl, Bool.eq_iff_iff, beq_iff_eq, eqA, allLt_iff]
  constructor
  · rintro h i -
    rw [h, beq_self_eq_true]
  · intro h
    apply Array.ext (by rw [permOfMat_size, permOfMat_size])
    intro i h1 h2
    have hi : i < V.size := by rwa [permOfMat_size] at h1
    have := h i hi
    rw [beq_iff_eq, getElem!_pos _ i h1, getElem!_pos _ i h2] at this
    exact this

end CFSG.RankThree.Native.F2

end
