module

public import CFSG.Monster.VisQuot.SignLiftInv
public import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Model

@[expose] def octPairs : List (ℕ × ℕ) :=
  [(296, 2109), (304, 1093), (410, 695), (495, 643), (619, 943), (2048, 2919)]

@[expose] def octBasis : List (List (ℕ × ℕ)) := [
  [(63, 0), (279, 0), (2050, 0), (0, 5), (0, 17), (0, 40), (0, 64), (0, 128), (0, 265),
    (0, 512), (0, 1024), (0, 2051)],
  [(63, 0), (271, 0), (1093, 0), (0, 5), (0, 10), (0, 48), (0, 67), (0, 128), (0, 274),
    (0, 512), (0, 1027), (0, 2048)],
  [(63, 0), (410, 0), (648, 0), (0, 5), (0, 18), (0, 33), (0, 64), (0, 137), (0, 259),
    (0, 522), (0, 1024), (0, 2048)],
  [(63, 0), (464, 0), (643, 0), (0, 3), (0, 12), (0, 36), (0, 84), (0, 145), (0, 276),
    (0, 517), (0, 1024), (0, 2048)],
  [(63, 0), (452, 0), (596, 0), (0, 3), (0, 9), (0, 33), (0, 69), (0, 148), (0, 276), (0, 529),
    (0, 1024), (0, 2048)],
  [(63, 0), (856, 0), (2048, 0), (0, 3), (0, 5), (0, 24), (0, 33), (0, 73), (0, 128), (0, 265),
    (0, 521), (0, 1024)]]

@[expose] def octAnn : List (List (ℕ × ℕ)) := [
  [(5, 0), (17, 0), (40, 0), (64, 0), (128, 0), (265, 0), (512, 0), (1024, 0), (2051, 0),
    (0, 63), (0, 279), (0, 2050)],
  [(5, 0), (10, 0), (48, 0), (67, 0), (128, 0), (274, 0), (512, 0), (1027, 0), (2048, 0),
    (0, 63), (0, 271), (0, 1093)],
  [(5, 0), (18, 0), (33, 0), (64, 0), (137, 0), (259, 0), (522, 0), (1024, 0), (2048, 0),
    (0, 63), (0, 410), (0, 648)],
  [(3, 0), (12, 0), (36, 0), (84, 0), (145, 0), (276, 0), (517, 0), (1024, 0), (2048, 0),
    (0, 63), (0, 464), (0, 643)],
  [(3, 0), (9, 0), (33, 0), (69, 0), (148, 0), (276, 0), (529, 0), (1024, 0), (2048, 0),
    (0, 63), (0, 452), (0, 596)],
  [(3, 0), (5, 0), (24, 0), (33, 0), (73, 0), (128, 0), (265, 0), (521, 0), (1024, 0), (0, 63),
    (0, 856), (0, 2048)]]

@[expose] def octDual : List (List (ℕ × ℕ)) := [
  [(32, 0), (256, 0), (2048, 0), (0, 4), (0, 16), (0, 32), (0, 64), (0, 128), (0, 256),
    (0, 512), (0, 1024), (0, 2048)],
  [(32, 0), (256, 0), (1024, 0), (0, 4), (0, 8), (0, 32), (0, 64), (0, 128), (0, 256),
    (0, 512), (0, 1024), (0, 2048)],
  [(32, 0), (256, 0), (512, 0), (0, 4), (0, 16), (0, 32), (0, 64), (0, 128), (0, 256),
    (0, 512), (0, 1024), (0, 2048)],
  [(32, 0), (256, 0), (512, 0), (0, 2), (0, 8), (0, 32), (0, 64), (0, 128), (0, 256), (0, 512),
    (0, 1024), (0, 2048)],
  [(32, 0), (256, 0), (512, 0), (0, 2), (0, 8), (0, 32), (0, 64), (0, 128), (0, 256), (0, 512),
    (0, 1024), (0, 2048)],
  [(32, 0), (512, 0), (2048, 0), (0, 2), (0, 4), (0, 16), (0, 32), (0, 64), (0, 128), (0, 256),
    (0, 512), (0, 1024)]]

@[expose] def octCert : List ((ℕ × ℕ) × List (ℕ × ℕ)) := [
  ((64, 0), [(0, 3)]),
  ((128, 0), [(0, 4)]),
  ((256, 0), [(0, 1), (0, 2), (0, 5), (1, 2)]),
  ((512, 0), [(0, 6)]),
  ((1024, 0), [(0, 7)]),
  ((2048, 0), [(0, 1), (0, 2), (0, 8), (1, 1), (1, 2)]),
  ((3, 0), [(0, 1), (0, 2), (1, 1), (1, 2)]),
  ((5, 0), [(0, 0)]),
  ((9, 0), [(0, 1), (0, 2), (1, 2)]),
  ((17, 0), [(0, 1)]),
  ((33, 0), [(0, 1), (1, 2)]),
  ((0, 1), [(0, 11), (1, 10), (2, 11), (3, 10), (4, 11), (5, 11)]),
  ((0, 2), [(0, 11), (5, 11)]),
  ((0, 4), [(0, 10), (3, 11), (4, 10), (4, 11)]),
  ((0, 8), [(1, 10), (3, 10), (3, 11), (4, 11)]),
  ((0, 16), [(0, 10), (3, 10), (3, 11), (4, 11)]),
  ((0, 32), [(0, 9), (2, 11), (3, 10), (3, 11), (4, 10)]),
  ((0, 64), [(0, 11), (1, 10), (2, 10), (3, 11), (4, 11), (5, 11)]),
  ((0, 128), [(0, 11), (2, 10), (2, 11), (4, 10), (4, 11), (5, 11)]),
  ((0, 256), [(0, 10), (1, 10), (2, 11), (4, 10), (4, 11)]),
  ((0, 512), [(0, 11), (1, 10), (2, 10), (3, 10), (3, 11), (4, 10), (5, 11)]),
  ((0, 1024), [(0, 10), (1, 11), (2, 10), (2, 11), (3, 10), (4, 10), (4, 11)]),
  ((0, 2048), [(5, 11)])]

@[expose] def basisAt (j k : ℕ) : ℕ × ℕ := (octBasis.getD j []).getD k (0, 0)

@[expose] def annAt (j k : ℕ) : ℕ × ℕ := (octAnn.getD j []).getD k (0, 0)

theorem annAt_def (j k : ℕ) : annAt j k = (octAnn.getD j []).getD k (0, 0) := rfl

@[expose] def dualAt (j k : ℕ) : ℕ × ℕ := (octDual.getD j []).getD k (0, 0)

@[expose] def maskFun (mn : ℕ × ℕ) (x : SpinCoord) : ZMod 2 :=
  pair x.a (toD mn.1) + pair (toC mn.2) x.δ

@[expose] def liftW (w : ℕ × ℕ) : CFSG.Monster.B.Model.Pauli := (false, w.1, w.2)

@[expose] def octE (ws : List (ℕ × ℕ)) : Subgroup Q :=
  Subgroup.closure (insert zQ {r | ∃ w ∈ ws, r = pauliQ (liftW w)})

@[expose] def octA (a b : ℕ) (ws : List (ℕ × ℕ)) : Subgroup Gvis :=
  Subgroup.closure ({hS a, hS b} ∪ {g | ∃ r ∈ octE ws, g = rhoGvis r})

@[expose] def octMember (j : Fin 6) : Subgroup Gvis :=
  octA (octPairs.getD j (0, 0)).1 (octPairs.getD j (0, 0)).2 (octBasis.getD j [])

@[expose] def octTriple (a b : ℕ) : List ℕ := [a % 2 ^ 12, b % 2 ^ 12, (a ^^^ b) % 2 ^ 12]

@[expose] def octQuad (a b : ℕ) : List ℕ := 0 :: octTriple a b

@[expose] def maskXor (m n : ℕ × ℕ) : ℕ × ℕ := (m.1 ^^^ n.1, m.2 ^^^ n.2)

@[expose] def maskFold : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | m :: l => maskXor m (maskFold l)

theorem octPairs_fst_sq : octPairs.all (fun p => !thetaBit (pi0N p.1) p.1) = true := by
  decide +kernel

theorem octPairs_snd_sq : octPairs.all (fun p => !thetaBit (pi0N p.2) p.2) = true := by
  decide +kernel

theorem octPairs_comm :
    octPairs.all (fun p => thetaBit (pi0N p.1) p.2 == thetaBit (pi0N p.2) p.1) = true := by
  decide +kernel

theorem octBasis_conj_fst : (List.finRange 6).all (fun j =>
    (octBasis.getD (j : ℕ) []).all (fun w =>
      conjYN (octPairs.getD (j : ℕ) (0, 0)).1 (liftW w) == liftW w)) = true := by
  decide +kernel

theorem octBasis_conj_snd : (List.finRange 6).all (fun j =>
    (octBasis.getD (j : ℕ) []).all (fun w =>
      conjYN (octPairs.getD (j : ℕ) (0, 0)).2 (liftW w) == liftW w)) = true := by
  decide +kernel

theorem octBasis_sq : (List.finRange 6).all (fun j =>
    (octBasis.getD (j : ℕ) []).all (fun w => !pairN w.1 w.2)) = true := by
  decide +kernel

theorem octBasis_comm : (List.finRange 6).all (fun j =>
    (octBasis.getD (j : ℕ) []).all (fun w =>
      (octBasis.getD (j : ℕ) []).all (fun w' => pairN w'.1 w.2 == pairN w.1 w'.2))) = true := by
  decide +kernel

theorem octAnn_vanishes : (List.finRange 6).all (fun j =>
    (octBasis.getD (j : ℕ) []).all (fun w =>
      (octAnn.getD (j : ℕ) []).all (fun m =>
        !(pairN w.1 m.1 ^^ pairN m.2 w.2)))) = true := by
  decide +kernel

theorem octDual_apply : (List.finRange 6).all (fun j =>
    (List.finRange 12).all (fun i => (List.finRange 12).all (fun k =>
      (pairN (basisAt (j : ℕ) (k : ℕ)).1 (dualAt (j : ℕ) (i : ℕ)).1 ^^
        pairN (dualAt (j : ℕ) (i : ℕ)).2 (basisAt (j : ℕ) (k : ℕ)).2) ==
        decide (i = k)))) = true := by
  decide +kernel

theorem octCert_check : octCert.all (fun p =>
    (maskFold (p.2.map (fun jk => annAt jk.1 jk.2)) == p.1)) = true := by
  decide +kernel

theorem octTriple_nonzero : (List.finRange 6).all (fun j =>
    (octTriple (octPairs.getD (j : ℕ) (0, 0)).1 (octPairs.getD (j : ℕ) (0, 0)).2).all
      (fun x => !(x == 0) && !(x == 63))) = true := by
  decide +kernel

theorem octQuad_distinct : (List.finRange 6).all (fun j =>
    let t := octQuad (octPairs.getD (j : ℕ) (0, 0)).1 (octPairs.getD (j : ℕ) (0, 0)).2
    t.all (fun x => t.all (fun y => (x == y) || !(x ^^^ y == 63)))) = true := by
  decide +kernel

theorem octTriple_cross :
    (octTriple (octPairs.getD 0 (0, 0)).1 (octPairs.getD 0 (0, 0)).2).all (fun x =>
      (octTriple (octPairs.getD 1 (0, 0)).1 (octPairs.getD 1 (0, 0)).2).all (fun y =>
        !(x == y) && !(x ^^^ y == 63))) = true := by
  decide +kernel

theorem boolZ_add_eq_zero {a b : Bool} (h : (a ^^ b) = false) : boolZ a + boolZ b = 0 := by
  rw [← boolZ_xor, h, boolZ_false]

theorem maskFun_mul (m : ℕ × ℕ) (x y : SpinCoord) :
    maskFun m (x * y) = maskFun m x + maskFun m y := by
  rw [maskFun, maskFun, maskFun, SpinCoord.mul_a, SpinCoord.mul_δ, pair_add_right,
    pair_add_left]
  abel

theorem maskFun_one (m : ℕ × ℕ) : maskFun m (1 : SpinCoord) = 0 := by
  rw [maskFun, SpinCoord.one_a, SpinCoord.one_δ, pair_zero_left, pair_zero_right, add_zero]

theorem maskFun_inv (m : ℕ × ℕ) (x : SpinCoord) : maskFun m x⁻¹ = maskFun m x := by
  rw [maskFun, maskFun, SpinCoord.inv_a, SpinCoord.inv_δ]

@[expose] def maskKer (anns : List (ℕ × ℕ)) : Subgroup Q where
  carrier := {r | ∀ m ∈ anns, maskFun m (spinEquiv.symm r) = 0}
  mul_mem' := by
    intro r s hr hs m hm
    rw [map_mul, maskFun_mul, hr m hm, hs m hm, add_zero]
  one_mem' := by
    intro m _
    rw [map_one, maskFun_one]
  inv_mem' := by
    intro r hr m hm
    rw [map_inv, maskFun_inv]
    exact hr m hm

theorem octE_le_maskKer {ws anns : List (ℕ × ℕ)}
    (h : ∀ w ∈ ws, ∀ m ∈ anns, (pairN w.1 m.1 ^^ pairN m.2 w.2) = false) :
    octE ws ≤ maskKer anns := by
  rw [octE, Subgroup.closure_le]
  rintro r (rfl | ⟨w, hw, rfl⟩)
  · intro m _
    show maskFun m (spinEquiv.symm (spinEquiv SpinCoord.z)) = 0
    rw [MulEquiv.symm_apply_apply]
    show pair SpinCoord.z.a (toD m.1) + pair (toC m.2) SpinCoord.z.δ = 0
    simp [SpinCoord.z]
  · intro m hm
    have e : spinEquiv.symm (pauliQ (liftW w)) = toSC (liftW w) := by
      show spinEquiv.symm (spinEquiv (toSC (liftW w))) = toSC (liftW w)
      rw [MulEquiv.symm_apply_apply]
    rw [e]
    show pair (toSC (liftW w)).a (toD m.1) + pair (toC m.2) (toSC (liftW w)).δ = 0
    rw [show (toSC (liftW w)).a = toC w.1 from rfl,
      show (toSC (liftW w)).δ = toD w.2 from rfl, pair_toC_toD, pair_toC_toD]
    exact boolZ_add_eq_zero (h w hw m hm)

theorem thetaBit_zero (a : ℕ) : thetaBit 0 a = false := by
  show pairN a (thetaN 0) = false
  rw [show thetaN 0 = 0 from rfl, pairN_zero_right]

theorem thetaBit_zero_right (a : ℕ) : thetaBit a 0 = false := by
  show pairN 0 (thetaN a) = false
  rw [pairN_zero_left]

theorem acodeN_zero (a : ℕ) : acodeN a 0 = 0 := by
  show dualN (wordN a &&& wordN 0) = 0
  rw [show wordN 0 = 0 from rfl, Nat.and_zero]
  rfl

theorem conjTN_zero (a : ℕ) : conjTN a 0 = (false, 0, 0) := by
  show (thetaBit 0 a, (0 : ℕ) ^^^ (if thetaBit a 0 then 63 else 0), acodeN a 0) =
    (false, 0, 0)
  rw [thetaBit_zero, thetaBit_zero_right, acodeN_zero]
  simp

theorem conjDN_zero (a : ℕ) : conjDN a 0 = (false, 0, 0) := by
  show (!pairN 63 0 && pairN a 0,
    (if pairN 63 0 then a else 0) ^^^ (if (pairN 63 0 && pN a) ^^ pairN a 0 then 63 else 0),
    (if pairN 63 0 then thetaN a else 0) ^^^ 0) = (false, 0, 0)
  rw [pairN_zero_right, pairN_zero_right]
  simp

theorem conjYN_z (a : ℕ) : conjYN a (true, 0, 0) = (true, 0, 0) := by
  show Pauli.mul (Pauli.mul ((true : Bool), 0, 0) (conjTN a 0)) (conjDN a 0) = (true, 0, 0)
  rw [conjTN_zero, conjDN_zero]
  rfl

theorem pauliQ_liftW_mul_self {w : ℕ × ℕ} (h : pairN w.1 w.2 = false) :
    pauliQ (liftW w) * pauliQ (liftW w) = 1 := by
  rw [← pauliQ_mul]
  have hm : (liftW w).mul (liftW w) = (pairN w.1 w.2, 0, 0) := by
    simp [liftW, Pauli.mul]
  rw [hm, h]
  exact pauliQ_false_zero

theorem pauliQ_liftW_comm {w w' : ℕ × ℕ} (h : pairN w'.1 w.2 = pairN w.1 w'.2) :
    pauliQ (liftW w) * pauliQ (liftW w') = pauliQ (liftW w') * pauliQ (liftW w) := by
  rw [← pauliQ_mul, ← pauliQ_mul]
  congr 1
  simp only [liftW, Pauli.mul]
  rw [h, Nat.xor_comm w'.1 w.1, Nat.xor_comm w'.2 w.2]

theorem zQ_mul_self : zQ * zQ = 1 := by
  show spinEquiv SpinCoord.z * spinEquiv SpinCoord.z = 1
  rw [← map_mul, show SpinCoord.z * SpinCoord.z = 1 from by
    rw [← pow_two]; exact SpinCoord.z_sq, map_one]

theorem zQ_mem_center : zQ ∈ Subgroup.center Q := by
  rw [center_Q]
  exact Subgroup.mem_zpowers zQ

theorem zQ_comm (r : Q) : zQ * r = r * zQ :=
  (Subgroup.mem_center_iff.1 zQ_mem_center r).symm

theorem hS_rhoGvis_zQ_comm (a : ℕ) : hS a * rhoGvis zQ = rhoGvis zQ * hS a := by
  have h := hS_mul_rhoGvis (a := a) (y := (true, 0, 0)) (conjYN_z a)
  rwa [pauliQ_z] at h

theorem commute_hS_rhoGvis_octE {a : ℕ} {ws : List (ℕ × ℕ)}
    (h : ∀ w ∈ ws, conjYN a (liftW w) = liftW w) :
    ∀ r ∈ octE ws, Commute (hS a) (rhoGvis r) := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    rcases hr with rfl | ⟨w, hw, rfl⟩
    · exact hS_rhoGvis_zQ_comm a
    · exact hS_mul_rhoGvis (h w hw)
  | one => rw [rhoGvis_one]; exact Commute.one_right (hS a)
  | mul x y _ _ ihx ihy =>
    rw [rhoGvis_mul]
    exact ihy.mul_right ihx
  | inv x _ ih =>
    rw [rhoGvis_inv]
    exact ih.inv_right

theorem octE_isElemAbelian {ws : List (ℕ × ℕ)}
    (hsq : ∀ w ∈ ws, pairN w.1 w.2 = false)
    (hcomm : ∀ w ∈ ws, ∀ w' ∈ ws, pairN w'.1 w.2 = pairN w.1 w'.2) :
    CFSG.Open.IsElemAbelian 2 (octE ws) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro r (rfl | ⟨w, hw, rfl⟩) s (rfl | ⟨w', hw', rfl⟩)
    · rfl
    · exact zQ_comm _
    · exact (zQ_comm _).symm
    · exact pauliQ_liftW_comm (hcomm w hw w' hw')
  · rintro r (rfl | ⟨w, hw, rfl⟩)
    · rw [pow_two]; exact zQ_mul_self
    · rw [pow_two]; exact pauliQ_liftW_mul_self (hsq w hw)

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def octVec (w : ℕ × ℕ) : C × Cocode := (toC w.1, toD w.2)

@[expose] def octB (ws : List (ℕ × ℕ)) (k : Fin 12) : C × Cocode :=
  octVec (ws.getD (k : ℕ) (0, 0))

@[expose] def octV (ws : List (ℕ × ℕ)) : Submodule (ZMod 2) (C × Cocode) :=
  Submodule.span (ZMod 2) (Set.range (octB ws))

@[expose] def maskLM (mn : ℕ × ℕ) : (C × Cocode) →ₗ[ZMod 2] ZMod 2 :=
  (pairing.flip (toD mn.1)).comp (LinearMap.fst (ZMod 2) C Cocode) +
    (pair (toC mn.2)).comp (LinearMap.snd (ZMod 2) C Cocode)

theorem maskLM_apply (mn : ℕ × ℕ) (x : C × Cocode) :
    maskLM mn x = pair x.1 (toD mn.1) + pair (toC mn.2) x.2 := rfl

theorem maskFun_xor (m n : ℕ × ℕ) (x : SpinCoord) :
    maskFun (maskXor m n) x = maskFun m x + maskFun n x := by
  rw [maskFun, maskFun, maskFun, maskXor, toD_xor, toC_xor, pair_add_right, pair_add_left]
  abel

theorem maskFun_maskFold_zero : ∀ (l : List (ℕ × ℕ)) (x : SpinCoord),
    (∀ m ∈ l, maskFun m x = 0) → maskFun (maskFold l) x = 0
  | [], x, _ => by simp [maskFold, maskFun, toD_zero, toC_zero]
  | a :: l, x, h => by
    show maskFun (maskXor a (maskFold l)) x = 0
    rw [maskFun_xor, h a (by simp),
      maskFun_maskFold_zero l x (fun m hm => h m (by simp [hm])), add_zero]

@[expose] def octCoord (ds : List (ℕ × ℕ)) : (C × Cocode) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  LinearMap.pi fun i => maskLM (ds.getD (i : ℕ) (0, 0))

theorem octCoord_apply (ds : List (ℕ × ℕ)) (x : C × Cocode) (i : Fin 12) :
    octCoord ds x i = maskLM (ds.getD (i : ℕ) (0, 0)) x := rfl

theorem octCoord_octB {ws ds : List (ℕ × ℕ)}
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k))
    (i k : Fin 12) :
    octCoord ds (octB ws k) i = (Pi.single k (1 : ZMod 2) : Fin 12 → ZMod 2) i := by
  rw [octCoord_apply, octB, octVec, maskLM_apply, pair_toC_toD, pair_toC_toD, ← boolZ_xor,
    hdual i k]
  by_cases hik : i = k
  · subst hik
    simp
  · rw [show decide (i = k) = false from by simp [hik], boolZ_false, Pi.single_apply,
      if_neg hik]

theorem octV_eq_sum {ws ds : List (ℕ × ℕ)}
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k))
    {x : C × Cocode} (hx : x ∈ octV ws) :
    x = ∑ k, octCoord ds x k • octB ws k := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    rw [Finset.sum_eq_single k]
    · rw [octCoord_octB hdual k k, Pi.single_eq_same, one_smul]
    · intro i _ hik
      rw [octCoord_octB hdual i k, Pi.single_apply, if_neg hik, zero_smul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  | zero => rw [map_zero]; simp
  | add x y _ _ ihx ihy =>
    conv_lhs => rw [ihx, ihy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, map_add]
    rfl
  | smul c x _ ih =>
    conv_lhs => rw [ih]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, map_smul, Pi.smul_apply, smul_eq_mul]

theorem octCoord_sum {ws ds : List (ℕ × ℕ)}
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k))
    (c : Fin 12 → ZMod 2) :
    octCoord ds (∑ k, c k • octB ws k) = c := by
  have h1 : octCoord ds (∑ k, c k • octB ws k) =
      ∑ k, c k • octCoord ds (octB ws k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  rw [h1]
  ext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [Pi.smul_apply, octCoord_octB hdual i i, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro k _ hki
    rw [Pi.smul_apply, octCoord_octB hdual i k, Pi.single_apply, if_neg (Ne.symm hki),
      smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

@[expose] noncomputable def octVEquiv {ws ds : List (ℕ × ℕ)}
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k)) :
    ↥(octV ws) ≃ (Fin 12 → ZMod 2) :=
  { toFun := fun x => octCoord ds x.1
    invFun := fun c => ⟨∑ k, c k • octB ws k,
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)⟩
    left_inv := fun x => Subtype.ext (octV_eq_sum hdual x.2).symm
    right_inv := fun c => octCoord_sum hdual c }

theorem natCard_fun12 : Nat.card (Fin 12 → ZMod 2) = 2 ^ 12 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem natCard_octV {ws ds : List (ℕ × ℕ)}
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k)) :
    Nat.card (octV ws) = 2 ^ 12 := by
  rw [Nat.card_congr (octVEquiv hdual), natCard_fun12]

@[expose] def spinPre (ws : List (ℕ × ℕ)) : Subgroup SpinCoord where
  carrier := {x : SpinCoord | (x.a, x.δ) ∈ octV ws}
  mul_mem' := by
    intro x y hx hy
    change ((x * y).a, (x * y).δ) ∈ octV ws
    rw [SpinCoord.mul_a, SpinCoord.mul_δ]
    exact (octV ws).add_mem hx hy
  one_mem' := by
    change ((1 : SpinCoord).a, (1 : SpinCoord).δ) ∈ octV ws
    rw [SpinCoord.one_a, SpinCoord.one_δ]
    exact (octV ws).zero_mem
  inv_mem' := by
    intro x hx
    change (x⁻¹.a, x⁻¹.δ) ∈ octV ws
    rwa [SpinCoord.inv_a, SpinCoord.inv_δ]

@[expose] noncomputable def spinPreEquiv (ws : List (ℕ × ℕ)) :
    ↥(spinPre ws) ≃ ↥(octV ws) × ZMod 2 where
  toFun x := (⟨(x.1.a, x.1.δ), x.2⟩, x.1.s)
  invFun p := ⟨⟨p.2, (p.1 : C × Cocode).1, (p.1 : C × Cocode).2⟩, p.1.2⟩
  left_inv x := Subtype.ext (SpinCoord.ext rfl rfl rfl)
  right_inv p := by
    obtain ⟨⟨v, hv⟩, s⟩ := p
    rfl

theorem natCard_spinPre {ws ds : List (ℕ × ℕ)}
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k)) :
    Nat.card (spinPre ws) = 2 ^ 13 := by
  rw [Nat.card_congr (spinPreEquiv ws), Nat.card_prod, natCard_octV hdual, Nat.card_zmod]
  norm_num

instance finiteSpinCoord : Finite SpinCoord :=
  Finite.of_injective SpinCoord.equivProd SpinCoord.equivProd.injective

instance finiteQ : Finite Q :=
  Finite.of_injective (spinEquiv.symm : Q → SpinCoord) spinEquiv.symm.injective

@[expose] def sc (s : ZMod 2) (v : C × Cocode) : SpinCoord := ⟨s, v.1, v.2⟩

theorem sc_mul (s t : ZMod 2) (v w : C × Cocode) :
    sc s v * sc t w = sc (s + t + pair w.1 v.2) (v + w) := rfl

theorem sc_zero_mul (s : ZMod 2) (v : C × Cocode) :
    sc s v = sc 0 v * sc s (0 : C × Cocode) := by
  rw [sc_mul]
  congr 1
  · simp
  · simp

theorem add_self_zmod2 (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem sc_add_mul (s : ZMod 2) (v w : C × Cocode) :
    sc s (v + w) = sc (s + pair w.1 v.2) v * sc 0 w := by
  rw [sc_mul, add_zero, add_assoc, add_self_zmod2, add_zero]

theorem spinEquiv_sc_zero {ws : List (ℕ × ℕ)} (s : ZMod 2) :
    spinEquiv (sc s (0 : C × Cocode)) ∈ octE ws := by
  rcases zmod2_cases s with rfl | rfl
  · have e : sc 0 (0 : C × Cocode) = 1 := rfl
    rw [e, map_one]
    exact (octE ws).one_mem
  · have e : sc 1 (0 : C × Cocode) = SpinCoord.z := rfl
    rw [e]
    exact Subgroup.subset_closure (Or.inl rfl)

theorem octB_mem {ws : List (ℕ × ℕ)} (hlen : 12 ≤ ws.length) (k : Fin 12) :
    ws.getD (k : ℕ) (0, 0) ∈ ws := by
  have hk : (k : ℕ) < ws.length := lt_of_lt_of_le k.2 hlen
  have h : ws.getD (k : ℕ) (0, 0) = ws[(k : ℕ)] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [h]
  exact List.getElem_mem hk

theorem spinEquiv_octB_self {ws : List (ℕ × ℕ)} (hlen : 12 ≤ ws.length) (k : Fin 12) :
    spinEquiv (sc 0 (octB ws k)) ∈ octE ws := by
  have hw := octB_mem hlen k
  have e : sc 0 (octB ws k) = toSC (liftW (ws.getD (k : ℕ) (0, 0))) := rfl
  rw [e]
  exact Subgroup.subset_closure (Or.inr ⟨_, hw, rfl⟩)

theorem spinPre_le_octE {ws ds : List (ℕ × ℕ)} (hlen : 12 ≤ ws.length)
    (_hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k)) :
    spinPre ws ≤ (octE ws).comap spinEquiv := by
  have key : ∀ v : C × Cocode, v ∈ octV ws → ∀ s : ZMod 2, spinEquiv (sc s v) ∈ octE ws := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      intro s
      rw [sc_zero_mul, map_mul]
      exact (octE ws).mul_mem (spinEquiv_octB_self hlen k) (spinEquiv_sc_zero s)
    | zero =>
      intro s
      exact spinEquiv_sc_zero s
    | add v w hv hw ihv ihw =>
      intro s
      rw [sc_add_mul, map_mul]
      exact (octE ws).mul_mem (ihv (s + pair w.1 v.2)) (ihw 0)
    | smul c v hv ih =>
      intro s
      rcases zmod2_cases c with rfl | rfl
      · rw [zero_smul]
        exact spinEquiv_sc_zero s
      · rw [one_smul]
        exact ih s
  intro x hx
  exact key (x.a, x.δ) hx x.s

theorem natCard_spinPre_le_octE {ws ds : List (ℕ × ℕ)} (hlen : 12 ≤ ws.length)
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k)) :
    Nat.card (spinPre ws) ≤ Nat.card (octE ws) := by
  refine Nat.card_le_card_of_injective
    (fun x : ↥(spinPre ws) => (⟨spinEquiv x.1, spinPre_le_octE hlen hdual x.2⟩ : ↥(octE ws))) ?_
  intro x y hxy
  have h : spinEquiv x.1 = spinEquiv y.1 := congrArg (fun z : ↥(octE ws) => (z : Q)) hxy
  exact Subtype.ext (spinEquiv.injective h)

theorem two_pow_le_card_octE {ws ds : List (ℕ × ℕ)} (hlen : 12 ≤ ws.length)
    (hdual : ∀ i k : Fin 12,
      (pairN (ws.getD (k : ℕ) (0, 0)).1 (ds.getD (i : ℕ) (0, 0)).1 ^^
        pairN (ds.getD (i : ℕ) (0, 0)).2 (ws.getD (k : ℕ) (0, 0)).2) = decide (i = k)) :
    2 ^ 13 ≤ Nat.card (octE ws) := by
  rw [← natCard_spinPre hdual]
  exact natCard_spinPre_le_octE hlen hdual

theorem ΩC_eq_toC_vis : (ΩC : C) = toC 63 := by
  apply Subtype.ext
  rw [show (ΩC : Fin 24 → ZMod 2) = Ω from rfl, coe_toC]
  decide

theorem toC_eq_iff {a b : ℕ} : toC a = toC b ↔ a % 2 ^ 12 = b % 2 ^ 12 := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rcases lt_or_ge j 12 with hj | hj
    · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and,
        Bool.true_and]
      have h' := congrArg (fun x : C => basisC.repr x ⟨j, hj⟩) h
      rw [repr_toC_apply, repr_toC_apply] at h'
      exact boolZ_injective h'
    · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
        show decide (j < 12) = false from by simp [hj], Bool.false_and, Bool.false_and]
  · intro h
    refine toC_ext fun j => ?_
    have h' := congrArg (fun x => x.testBit (j : ℕ)) h
    rwa [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and,
      Bool.true_and] at h'

theorem toC_eq_zero_iff {a : ℕ} : toC a = 0 ↔ a % 2 ^ 12 = 0 := by
  rw [show (0 : C) = toC 0 from toC_zero.symm, toC_eq_iff, Nat.zero_mod]

theorem neg_eq_self_C (v : C) : -v = v := by
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [← neg_one_smul (ZMod 2) v, h, one_smul]

theorem mk_toC_eq_zero_iff {a : ℕ} :
    (Submodule.Quotient.mk (toC a) : C ⧸ ΩLine) = 0 ↔
      a % 2 ^ 12 = 0 ∨ a % 2 ^ 12 = 63 := by
  rw [Submodule.Quotient.mk_eq_zero, mem_ΩLine_iff, toC_eq_zero_iff, ΩC_eq_toC_vis,
    toC_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by
        rw [show (63 : ℕ) = 63 % 2 ^ 12 from (Nat.mod_eq_of_lt (by norm_num)).symm]
        exact h)

theorem mk_toC_eq_mk_toC_iff {x y : ℕ} :
    (Submodule.Quotient.mk (toC x) : C ⧸ ΩLine) = Submodule.Quotient.mk (toC y) ↔
      toC x = toC y ∨ toC x + toC y = ΩC := by
  rw [Submodule.Quotient.eq, mem_ΩLine_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (by rw [sub_eq_add_neg, neg_eq_self_C] at h; exact h)
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.2 h)
    · exact Or.inr (by rw [sub_eq_add_neg, neg_eq_self_C]; exact h)

@[expose] def gpow (x : ZMod 2) (g : Gvis) : Gvis := if x = 0 then 1 else g

theorem gpow_add {g : Gvis} (hg : g * g = 1) (x y : ZMod 2) :
    gpow (x + y) g = gpow x g * gpow y g := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [gpow, hg, add_self_zmod2]

theorem gpow_mul_comm {g h : Gvis} (_hg : g * g = 1) (_hh : h * h = 1) (hgh : g * h = h * g)
    (x y : ZMod 2) : gpow x h * gpow y g = gpow y g * gpow x h := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [gpow, hgh]

@[expose] def octU (a b : ℕ) (i : ZMod 2 × ZMod 2) : Gvis :=
  gpow i.1 (hS a) * gpow i.2 (hS b)

@[expose] def octVal (a b : ℕ) (i : ZMod 2 × ZMod 2) : ℕ :=
  ((if i.1 = 0 then 0 else a) ^^^ (if i.2 = 0 then 0 else b)) % 2 ^ 12

theorem octU_zero (a b : ℕ) : octU a b 0 = 1 := by
  simp [octU, gpow]

theorem octU_add {a b : ℕ} (ha : hS a * hS a = 1) (hb : hS b * hS b = 1)
    (hab : hS a * hS b = hS b * hS a) (i j : ZMod 2 × ZMod 2) :
    octU a b (i + j) = octU a b i * octU a b j := by
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  show gpow (i1 + j1) (hS a) * gpow (i2 + j2) (hS b) =
    (gpow i1 (hS a) * gpow i2 (hS b)) * (gpow j1 (hS a) * gpow j2 (hS b))
  rw [gpow_add ha, gpow_add hb]
  calc (gpow i1 (hS a) * gpow j1 (hS a)) * (gpow i2 (hS b) * gpow j2 (hS b))
      = gpow i1 (hS a) * (gpow j1 (hS a) * gpow i2 (hS b)) * gpow j2 (hS b) := by group
    _ = gpow i1 (hS a) * (gpow i2 (hS b) * gpow j1 (hS a)) * gpow j2 (hS b) := by
        rw [gpow_mul_comm hb ha hab.symm j1 i2]
    _ = (gpow i1 (hS a) * gpow i2 (hS b)) * (gpow j1 (hS a) * gpow j2 (hS b)) := by group

theorem zmod2_add_self' (i : ZMod 2 × ZMod 2) : i + i = 0 := by
  obtain ⟨x, y⟩ := i
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp [add_self_zmod2]

theorem octU_mul_self {a b : ℕ} (ha : hS a * hS a = 1) (hb : hS b * hS b = 1)
    (hab : hS a * hS b = hS b * hS a) (i : ZMod 2 × ZMod 2) :
    octU a b i * octU a b i = 1 := by
  rw [← octU_add ha hb hab, zmod2_add_self', octU_zero]

theorem octU_mul_rhoGvis {a b : ℕ} {ws : List (ℕ × ℕ)}
    (hA : ∀ w ∈ ws, conjYN a (liftW w) = liftW w)
    (hB : ∀ w ∈ ws, conjYN b (liftW w) = liftW w)
    (i : ZMod 2 × ZMod 2) {s : Q} (hs : s ∈ octE ws) :
    octU a b i * rhoGvis s = rhoGvis s * octU a b i := by
  have hx : ∀ x : ZMod 2, gpow x (hS a) * rhoGvis s = rhoGvis s * gpow x (hS a) := by
    intro x
    rcases zmod2_cases x with h | h
    · rw [gpow, if_pos h, one_mul, mul_one]
    · rw [gpow, if_neg (by rw [h]; exact one_ne_zero)]
      exact (commute_hS_rhoGvis_octE hA s hs).eq
  have hy : ∀ x : ZMod 2, gpow x (hS b) * rhoGvis s = rhoGvis s * gpow x (hS b) := by
    intro x
    rcases zmod2_cases x with h | h
    · rw [gpow, if_pos h, one_mul, mul_one]
    · rw [gpow, if_neg (by rw [h]; exact one_ne_zero)]
      exact (commute_hS_rhoGvis_octE hB s hs).eq
  show gpow i.1 (hS a) * gpow i.2 (hS b) * rhoGvis s =
    rhoGvis s * (gpow i.1 (hS a) * gpow i.2 (hS b))
  rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

theorem octU_mem {a b : ℕ} {ws : List (ℕ × ℕ)} (i : ZMod 2 × ZMod 2) :
    octU a b i ∈ octA a b ws := by
  show gpow i.1 (hS a) * gpow i.2 (hS b) ∈ octA a b ws
  refine (octA a b ws).mul_mem ?_ ?_
  · rcases zmod2_cases i.1 with h | h
    · rw [gpow, if_pos h]; exact (octA a b ws).one_mem
    · rw [gpow, if_neg (by rw [h]; exact one_ne_zero)]
      exact Subgroup.subset_closure (Or.inl (by simp))
  · rcases zmod2_cases i.2 with h | h
    · rw [gpow, if_pos h]; exact (octA a b ws).one_mem
    · rw [gpow, if_neg (by rw [h]; exact one_ne_zero)]
      exact Subgroup.subset_closure (Or.inl (by simp))

theorem PhiV_octU (a b : ℕ) (i : ZMod 2 × ZMod 2) :
    CFSG.Monster.Schur.PhiV (octU a b i) = monoHom (SemidirectProduct.inl
      (Multiplicative.ofAdd (Submodule.Quotient.mk (toC (octVal a b i))))) := by
  obtain ⟨i1, i2⟩ := i
  rcases zmod2_cases i1 with rfl | rfl <;> rcases zmod2_cases i2 with rfl | rfl
  · rw [show octU a b (0, 0) = 1 from by simp [octU, gpow],
      show octVal a b (0, 0) = 0 from by simp [octVal], toC_zero]
    simp
  · rw [show octU a b (0, 1) = hS b from by simp [octU, gpow], PhiV_hS,
      show octVal a b (0, 1) = b % 2 ^ 12 from by simp [octVal],
      show toC (b % 2 ^ 12) = toC b from by rw [toC_eq_iff, Nat.mod_mod]]
  · rw [show octU a b (1, 0) = hS a from by simp [octU, gpow], PhiV_hS,
      show octVal a b (1, 0) = a % 2 ^ 12 from by simp [octVal],
      show toC (a % 2 ^ 12) = toC a from by rw [toC_eq_iff, Nat.mod_mod]]
  · have hval : toC (octVal a b (1, 1)) = toC a + toC b := by
      rw [show octVal a b (1, 1) = (a ^^^ b) % 2 ^ 12 from by simp [octVal],
        show toC ((a ^^^ b) % 2 ^ 12) = toC (a ^^^ b) from by rw [toC_eq_iff, Nat.mod_mod],
        toC_xor]
    have hmk : (Submodule.Quotient.mk (toC a) + Submodule.Quotient.mk (toC b) : C ⧸ ΩLine) =
        Submodule.Quotient.mk (toC a + toC b) := by
      rw [← Submodule.Quotient.mk_add]
    rw [show octU a b (1, 1) = hS a * hS b from by simp [octU, gpow], map_mul, PhiV_hS,
      PhiV_hS, hval, ← map_mul, ← map_mul, ← ofAdd_add, hmk]

@[expose] def octRepSet (a b : ℕ) (ws : List (ℕ × ℕ)) : Set Gvis :=
  {g | ∃ r ∈ octE ws, ∃ i : ZMod 2 × ZMod 2, g = rhoGvis r * octU a b i}

theorem octRepSet_mul {a b : ℕ} {ws : List (ℕ × ℕ)}
    (ha : hS a * hS a = 1) (hb : hS b * hS b = 1) (hab : hS a * hS b = hS b * hS a)
    (hcommE : ∀ r ∈ octE ws, ∀ s ∈ octE ws, r * s = s * r)
    (hA : ∀ w ∈ ws, conjYN a (liftW w) = liftW w)
    (hB : ∀ w ∈ ws, conjYN b (liftW w) = liftW w) {g h : Gvis}
    (hg : g ∈ octRepSet a b ws) (hh : h ∈ octRepSet a b ws) :
    g * h ∈ octRepSet a b ws := by
  obtain ⟨r, hr, i, rfl⟩ := hg
  obtain ⟨s, hs, j, rfl⟩ := hh
  refine ⟨r * s, (octE ws).mul_mem hr hs, i + j, ?_⟩
  rw [octU_add ha hb hab]
  have h1 : octU a b i * rhoGvis s = rhoGvis s * octU a b i := octU_mul_rhoGvis hA hB i hs
  calc (rhoGvis r * octU a b i) * (rhoGvis s * octU a b j)
      = rhoGvis r * (octU a b i * rhoGvis s) * octU a b j := by group
    _ = rhoGvis r * (rhoGvis s * octU a b i) * octU a b j := by rw [h1]
    _ = (rhoGvis r * rhoGvis s) * (octU a b i * octU a b j) := by group
    _ = rhoGvis (s * r) * (octU a b i * octU a b j) := by rw [rhoGvis_mul]
    _ = rhoGvis (r * s) * (octU a b i * octU a b j) := by rw [hcommE r hr s hs]

theorem octRepSet_inv {a b : ℕ} {ws : List (ℕ × ℕ)}
    (ha : hS a * hS a = 1) (hb : hS b * hS b = 1) (hab : hS a * hS b = hS b * hS a)
    (hA : ∀ w ∈ ws, conjYN a (liftW w) = liftW w)
    (hB : ∀ w ∈ ws, conjYN b (liftW w) = liftW w) {g : Gvis}
    (hg : g ∈ octRepSet a b ws) : g⁻¹ ∈ octRepSet a b ws := by
  obtain ⟨r, hr, i, rfl⟩ := hg
  refine ⟨r⁻¹, (octE ws).inv_mem hr, i, ?_⟩
  have hi : (octU a b i)⁻¹ = octU a b i :=
    inv_eq_of_mul_eq_one_left (octU_mul_self ha hb hab i)
  rw [mul_inv_rev, hi, show (rhoGvis r)⁻¹ = rhoGvis r⁻¹ from rhoGvis_inv r]
  exact octU_mul_rhoGvis hA hB i ((octE ws).inv_mem hr)

def octRepSubgroup (a b : ℕ) (ws : List (ℕ × ℕ))
    (ha : hS a * hS a = 1) (hb : hS b * hS b = 1) (hab : hS a * hS b = hS b * hS a)
    (hcommE : ∀ r ∈ octE ws, ∀ s ∈ octE ws, r * s = s * r)
    (hA : ∀ w ∈ ws, conjYN a (liftW w) = liftW w)
    (hB : ∀ w ∈ ws, conjYN b (liftW w) = liftW w) : Subgroup Gvis where
  carrier := octRepSet a b ws
  one_mem' := ⟨1, (octE ws).one_mem, 0, by
    rw [rhoGvis_one, one_mul, octU_zero]⟩
  mul_mem' := octRepSet_mul ha hb hab hcommE hA hB
  inv_mem' := octRepSet_inv ha hb hab hA hB

theorem octA_exists_rep {a b : ℕ} {ws : List (ℕ × ℕ)}
    (ha : hS a * hS a = 1) (hb : hS b * hS b = 1) (hab : hS a * hS b = hS b * hS a)
    (hcommE : ∀ r ∈ octE ws, ∀ s ∈ octE ws, r * s = s * r)
    (hA : ∀ w ∈ ws, conjYN a (liftW w) = liftW w)
    (hB : ∀ w ∈ ws, conjYN b (liftW w) = liftW w) :
    ∀ g ∈ octA a b ws, ∃ r ∈ octE ws, ∃ i : ZMod 2 × ZMod 2, g = rhoGvis r * octU a b i := by
  have hle : octA a b ws ≤ octRepSubgroup a b ws ha hb hab hcommE hA hB := by
    change Subgroup.closure ({hS a, hS b} ∪ {g | ∃ r ∈ octE ws, g = rhoGvis r}) ≤
      octRepSubgroup a b ws ha hb hab hcommE hA hB
    refine (Subgroup.closure_le (octRepSubgroup a b ws ha hb hab hcommE hA hB)).2 ?_
    rintro g (hg | ⟨r, hr, rfl⟩)
    · rcases hg with rfl | rfl
      · exact ⟨1, (octE ws).one_mem, (1, 0), by
          rw [rhoGvis_one, one_mul]
          show hS a = gpow (1 : ZMod 2) (hS a) * gpow (0 : ZMod 2) (hS b)
          rw [gpow, gpow, if_neg one_ne_zero, if_pos rfl, mul_one]⟩
      · exact ⟨1, (octE ws).one_mem, (0, 1), by
          rw [rhoGvis_one, one_mul]
          show hS b = gpow (0 : ZMod 2) (hS a) * gpow (1 : ZMod 2) (hS b)
          rw [gpow, gpow, if_neg one_ne_zero, if_pos rfl, one_mul]⟩
    · exact ⟨r, hr, 0, by rw [octU_zero, mul_one]⟩
  exact hle

theorem octA_isElemAbelian {a b : ℕ} {ws : List (ℕ × ℕ)}
    (ha : thetaBit (pi0N a) a = false) (hb : thetaBit (pi0N b) b = false)
    (hab : thetaBit (pi0N a) b = thetaBit (pi0N b) a)
    (hsq : ∀ w ∈ ws, pairN w.1 w.2 = false)
    (hcomm : ∀ w ∈ ws, ∀ w' ∈ ws, pairN w'.1 w.2 = pairN w.1 w'.2)
    (hA : ∀ w ∈ ws, conjYN a (liftW w) = liftW w)
    (hB : ∀ w ∈ ws, conjYN b (liftW w) = liftW w) :
    CFSG.Open.IsElemAbelian 2 (octA a b ws) := by
  have ha' : hS a * hS a = 1 := hS_mul_self ha
  have hb' : hS b * hS b = 1 := hS_mul_self hb
  have hab' : hS a * hS b = hS b * hS a := hS_mul_comm hab
  have hE := octE_isElemAbelian hsq hcomm
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro r hr s hs
    rcases hr with hr | ⟨r, hr, rfl⟩
    · rcases hs with hs | ⟨s, hs, rfl⟩
      · rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        · rfl
        · exact hab'
        · exact hab'.symm
        · rfl
      · rcases hr with rfl | rfl
        · exact (commute_hS_rhoGvis_octE hA s hs).eq
        · exact (commute_hS_rhoGvis_octE hB s hs).eq
    · rcases hs with hs | ⟨s, hs, rfl⟩
      · rcases hs with rfl | rfl
        · exact ((commute_hS_rhoGvis_octE hA r hr).eq).symm
        · exact ((commute_hS_rhoGvis_octE hB r hr).eq).symm
      · rw [← rhoGvis_mul, ← rhoGvis_mul, hE.comm hr hs]
  · rintro r (hr | ⟨r, hr, rfl⟩)
    · rcases hr with rfl | rfl
      · rw [pow_two]; exact ha'
      · rw [pow_two]; exact hb'
    · have h1 : r * r = 1 := by
        have := hE.2 r hr
        rwa [pow_two] at this
      rw [pow_two, ← rhoGvis_mul, h1, rhoGvis_one]

@[expose] def oa (j : Fin 6) : ℕ := (octPairs.getD (j : ℕ) (0, 0)).1

@[expose] def ob (j : Fin 6) : ℕ := (octPairs.getD (j : ℕ) (0, 0)).2

@[expose] def ow (j : Fin 6) : List (ℕ × ℕ) := octBasis.getD (j : ℕ) []

@[expose] def on (j : Fin 6) : List (ℕ × ℕ) := octAnn.getD (j : ℕ) []

theorem fin_all {p : Fin 6 → Bool} (h : (List.finRange 6).all p = true) (j : Fin 6) :
    p j = true := (List.all_eq_true.1 h) j (List.mem_finRange j)

theorem octPairs_mem (j : Fin 6) : octPairs.getD (j : ℕ) (0, 0) ∈ octPairs := by
  have h : octPairs.getD (j : ℕ) (0, 0) = octPairs[(j : ℕ)] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Fin.is_lt j)]
    rfl
  rw [h]
  exact List.getElem_mem (Fin.is_lt j)

theorem octPairs_fst_sq' (j : Fin 6) : thetaBit (pi0N (oa j)) (oa j) = false := by
  have h := (List.all_eq_true.1 octPairs_fst_sq) _ (octPairs_mem j)
  simpa [oa] using h

theorem octPairs_snd_sq' (j : Fin 6) : thetaBit (pi0N (ob j)) (ob j) = false := by
  have h := (List.all_eq_true.1 octPairs_snd_sq) _ (octPairs_mem j)
  simpa [ob] using h

theorem octPairs_comm' (j : Fin 6) :
    thetaBit (pi0N (oa j)) (ob j) = thetaBit (pi0N (ob j)) (oa j) := by
  have h := (List.all_eq_true.1 octPairs_comm) _ (octPairs_mem j)
  simpa [oa, ob, beq_iff_eq] using h

theorem octBasis_conj_fst' (j : Fin 6) :
    ∀ w ∈ ow j, conjYN (oa j) (liftW w) = liftW w := by
  have h := (List.all_eq_true.1 (fin_all octBasis_conj_fst j))
  intro w hw
  have h' := h w (by simpa [ow] using hw)
  simpa [oa, ow, beq_iff_eq] using h'

theorem octBasis_conj_snd' (j : Fin 6) :
    ∀ w ∈ ow j, conjYN (ob j) (liftW w) = liftW w := by
  have h := (List.all_eq_true.1 (fin_all octBasis_conj_snd j))
  intro w hw
  have h' := h w (by simpa [ow] using hw)
  simpa [ob, ow, beq_iff_eq] using h'

theorem octBasis_sq' (j : Fin 6) : ∀ w ∈ ow j, pairN w.1 w.2 = false := by
  have h := (List.all_eq_true.1 (fin_all octBasis_sq j))
  intro w hw
  have h' := h w (by simpa [ow] using hw)
  simpa [ow] using h'

theorem octBasis_comm' (j : Fin 6) :
    ∀ w ∈ ow j, ∀ w' ∈ ow j, pairN w'.1 w.2 = pairN w.1 w'.2 := by
  have h := (List.all_eq_true.1 (fin_all octBasis_comm j))
  intro w hw w' hw'
  have h' := h w (by simpa [ow] using hw)
  have h'' := (List.all_eq_true.1 h') w' (by simpa [ow] using hw')
  simpa [ow, beq_iff_eq] using h''

theorem octAnn_vanishes' (j : Fin 6) :
    ∀ w ∈ ow j, ∀ m ∈ on j, (pairN w.1 m.1 ^^ pairN m.2 w.2) = false := by
  have h := (List.all_eq_true.1 (fin_all octAnn_vanishes j))
  intro w hw m hm
  have h' := h w (by simpa [ow] using hw)
  have h'' := (List.all_eq_true.1 h') m (by simpa [on] using hm)
  simpa [ow, on] using h''

theorem octDual_apply' (j : Fin 6) :
    ∀ i k : Fin 12,
      (pairN (basisAt (j : ℕ) (k : ℕ)).1 (dualAt (j : ℕ) (i : ℕ)).1 ^^
        pairN (dualAt (j : ℕ) (i : ℕ)).2 (basisAt (j : ℕ) (k : ℕ)).2) = decide (i = k) := by
  have h := (List.all_eq_true.1 (fin_all octDual_apply j))
  intro i k
  have h1 := h i (List.mem_finRange i)
  have h2 := (List.all_eq_true.1 h1) k (List.mem_finRange k)
  simpa [basisAt, dualAt, beq_iff_eq] using h2

theorem octBasis_length' (j : Fin 6) : 12 ≤ (ow j).length := by
  have h : octBasis.all (fun l => 12 ≤ l.length) = true := by decide +kernel
  have hmem : octBasis.getD (j : ℕ) [] ∈ octBasis := by
    have h1 : octBasis.getD (j : ℕ) [] = octBasis[(j : ℕ)] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Fin.is_lt j)]
      rfl
    rw [h1]
    exact List.getElem_mem (Fin.is_lt j)
  have h' := (List.all_eq_true.1 h) _ hmem
  simpa [ow] using h'

theorem octMember_isElemAbelian (j : Fin 6) :
    CFSG.Open.IsElemAbelian 2 (octMember j) :=
  octA_isElemAbelian (octPairs_fst_sq' j) (octPairs_snd_sq' j) (octPairs_comm' j)
    (octBasis_sq' j) (octBasis_comm' j) (octBasis_conj_fst' j) (octBasis_conj_snd' j)

theorem octMember_exists_rep (j : Fin 6) :
    ∀ g ∈ octMember j, ∃ r ∈ octE (ow j), ∃ i : ZMod 2 × ZMod 2,
      g = rhoGvis r * octU (oa j) (ob j) i :=
  octA_exists_rep (hS_mul_self (octPairs_fst_sq' j)) (hS_mul_self (octPairs_snd_sq' j))
    (hS_mul_comm (octPairs_comm' j))
    (fun _ hr _ hs => (octE_isElemAbelian (octBasis_sq' j) (octBasis_comm' j)).comm hr hs)
    (octBasis_conj_fst' j) (octBasis_conj_snd' j)

theorem exists_PhiV_eq_inl {j : Fin 6} {g : Gvis} (hg : g ∈ octMember j) :
    ∃ n : Multiplicative (C ⧸ ΩLine),
      CFSG.Monster.Schur.PhiV g = monoHom (SemidirectProduct.inl n) := by
  obtain ⟨r, _, i, hg'⟩ := octMember_exists_rep j g hg
  refine ⟨Multiplicative.ofAdd (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) i))), ?_⟩
  rw [hg', map_mul, PhiV_rhoGvis, one_mul, PhiV_octU]

theorem octVal_lt (a b : ℕ) (i : ZMod 2 × ZMod 2) : octVal a b i < 2 ^ 12 :=
  Nat.mod_lt _ (by norm_num)

theorem octVal_zero (a b : ℕ) : octVal a b 0 = 0 := by
  simp [octVal]

theorem octVal_inj' (j : Fin 6) : Function.Injective (octVal (oa j) (ob j)) := by
  have h : (List.finRange 6).all (fun j =>
      decide (Function.Injective (octVal (oa j) (ob j)))) = true := by
    decide +kernel
  have h' := (List.all_eq_true.1 h) j (List.mem_finRange j)
  simpa using h'

theorem octVal_mem' (j : Fin 6) (i : ZMod 2 × ZMod 2) :
    octVal (oa j) (ob j) i ∈ octQuad (oa j) (ob j) := by
  have h : (List.finRange 6).all (fun j =>
      decide (∀ i : ZMod 2 × ZMod 2,
        octVal (oa j) (ob j) i ∈ octQuad (oa j) (ob j))) = true := by
    decide +kernel
  have h' : ∀ i : ZMod 2 × ZMod 2,
      octVal (oa j) (ob j) i ∈ octQuad (oa j) (ob j) :=
    of_decide_eq_true ((List.all_eq_true.1 h) j (List.mem_finRange j))
  exact h' i

theorem octQuad_63_eq' (j : Fin 6) :
    ∀ x ∈ octQuad (oa j) (ob j), ∀ y ∈ octQuad (oa j) (ob j), x ^^^ y = 63 → x = y := by
  intro x hx y hy hxy
  have h1 := (List.all_eq_true.1 octQuad_distinct) j (List.mem_finRange j)
  have h2 := (List.all_eq_true.1 h1) x (by simpa [oa, ob] using hx)
  have h3 := (List.all_eq_true.1 h2) y (by simpa [oa, ob] using hy)
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · simpa [beq_iff_eq] using h3
  · simp [hxy] at h3

theorem octVal_class_injective (j : Fin 6) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 =>
      (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) i)) : C ⧸ ΩLine)) := by
  intro i i' h
  rw [mk_toC_eq_mk_toC_iff] at h
  rcases h with h | h
  · rw [toC_eq_iff, Nat.mod_eq_of_lt (octVal_lt _ _ i),
      Nat.mod_eq_of_lt (octVal_lt _ _ i')] at h
    exact octVal_inj' j h
  · have h' : octVal (oa j) (ob j) i ^^^ octVal (oa j) (ob j) i' = 63 := by
      have h2 : toC (octVal (oa j) (ob j) i ^^^ octVal (oa j) (ob j) i') = ΩC := by
        rw [toC_xor, h]
      rw [ΩC_eq_toC_vis, toC_eq_iff, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow
        (octVal_lt _ _ i) (octVal_lt _ _ i')),
        Nat.mod_eq_of_lt (by norm_num : 63 < 2 ^ 12)] at h2
      exact h2
    exact octVal_inj' j (octQuad_63_eq' j _ (octVal_mem' j i) _ (octVal_mem' j i') h')

theorem octU_PhiV_injective (j : Fin 6) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 =>
      CFSG.Monster.Schur.PhiV (octU (oa j) (ob j) i)) := by
  intro i i' h
  change CFSG.Monster.Schur.PhiV (octU (oa j) (ob j) i) =
    CFSG.Monster.Schur.PhiV (octU (oa j) (ob j) i') at h
  rw [PhiV_octU, PhiV_octU] at h
  have h1 := monoHom_injective h
  have h2 := SemidirectProduct.inl_injective h1
  have h3 : (Submodule.Quotient.mk (toC (octVal (oa j) (ob j) i)) : C ⧸ ΩLine) =
      Submodule.Quotient.mk (toC (octVal (oa j) (ob j) i')) :=
    congrArg (fun z : Multiplicative (C ⧸ ΩLine) => z.toAdd) h2
  exact octVal_class_injective j h3

theorem two_pow_le_card_octMember (j : Fin 6) : 2 ^ 15 ≤ Nat.card (octMember j) := by
  have hrep := octA_exists_rep (hS_mul_self (octPairs_fst_sq' j))
    (hS_mul_self (octPairs_snd_sq' j)) (hS_mul_comm (octPairs_comm' j))
    (fun r hr s hs => (octE_isElemAbelian (octBasis_sq' j) (octBasis_comm' j)).comm hr hs)
    (octBasis_conj_fst' j) (octBasis_conj_snd' j)
  let f : ↥(octE (ow j)) × (ZMod 2 × ZMod 2) → ↥(octMember j) := fun p =>
    ⟨rhoGvis p.1 * octU (oa j) (ob j) p.2,
      (octA (oa j) (ob j) (ow j)).mul_mem
        (Subgroup.subset_closure (Or.inr ⟨p.1, p.1.2, rfl⟩)) (octU_mem p.2)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨r, hr, i, rfl⟩ := hrep g hg
    exact ⟨(⟨r, hr⟩, i), rfl⟩
  have : Finite ↥(octMember j) := Finite.of_surjective f hsurj
  have hinj : Function.Injective f := by
    rintro ⟨r, i⟩ ⟨s, i'⟩ hpq
    have heq : rhoGvis r * octU (oa j) (ob j) i = rhoGvis s * octU (oa j) (ob j) i' :=
      congrArg Subtype.val hpq
    have h2 : i = i' := octU_PhiV_injective j (by
      have h1 := congrArg CFSG.Monster.Schur.PhiV heq
      rwa [map_mul, map_mul, PhiV_rhoGvis, PhiV_rhoGvis, one_mul, one_mul] at h1)
    subst h2
    have h3 : rhoGvis r = rhoGvis s := by
      have h1 := congrArg (fun z => z * (octU (oa j) (ob j) i)⁻¹) heq
      simpa [mul_assoc] using h1
    have h4 : r = s := Subtype.ext (rhoGvis_injective h3)
    subst h4
    rfl
  have hcard := @Nat.card_le_card_of_injective _ _ this f hinj
  have hZ : Nat.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Nat.card_prod, Nat.card_zmod]
  rw [Nat.card_prod, hZ] at hcard
  have hE := two_pow_le_card_octE (octBasis_length' j) (octDual_apply' j)
  calc 2 ^ 15 = 2 ^ 13 * 4 := by norm_num
    _ ≤ Nat.card ↥(octE (ow j)) * 4 := Nat.mul_le_mul_right 4 hE
    _ ≤ Nat.card ↥(octMember j) := hcard

