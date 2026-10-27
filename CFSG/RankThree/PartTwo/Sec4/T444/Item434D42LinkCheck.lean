module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoArr
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Quasithin
  CFSG.AGLEmbedding.D4Two
open scoped LinearAlgebra.Projectivization

@[expose] def vecOf (v : Array ℕ) : Fin 8 → GF8 := fun i => GF8.ofNat' v[i.val]!

@[expose] def lead (w : Fin 8 → GF8) : GF8 :=
  match (List.finRange 8).find? (fun i => decide (w i ≠ 0)) with
  | some i => w i
  | none => 1

@[expose] def normV (w : Fin 8 → GF8) : Fin 8 → GF8 := (lead w)⁻¹ • w

@[expose] def leadCode (w : Array ℕ) : ℕ :=
  match (List.finRange 8).find? (fun i => decide (w[i.val]! ≠ 0)) with
  | some i => w[i.val]!
  | none => 1

@[expose] def ginv (c : ℕ) : ℕ :=
  GF8.mulNat (GF8.mulNat c c) (GF8.mulNat (GF8.mulNat c c) (GF8.mulNat c c))

@[expose] def normCode (w : Array ℕ) : Array ℕ := w.map (GF8.mulNat (ginv (leadCode w)))

@[expose] def matCode (M : Matrix (Fin 8) (Fin 8) GF8) : Array ℕ :=
  Array.ofFn (n := 64) fun t => (M ⟨t.val / 8, by omega⟩ ⟨t.val % 8, by omega⟩).toNat

@[expose] def genCodes : Array (Array ℕ) := Array.ofFn (n := 18) fun k => matCode (letterMat k.val)

@[expose] def dotCode (M v : Array ℕ) (i : ℕ) : ℕ :=
  GF8.mulNat M[8 * i]! v[0]! ^^^ GF8.mulNat M[8 * i + 1]! v[1]! ^^^
    GF8.mulNat M[8 * i + 2]! v[2]! ^^^ GF8.mulNat M[8 * i + 3]! v[3]! ^^^
    GF8.mulNat M[8 * i + 4]! v[4]! ^^^ GF8.mulNat M[8 * i + 5]! v[5]! ^^^
    GF8.mulNat M[8 * i + 6]! v[6]! ^^^ GF8.mulNat M[8 * i + 7]! v[7]!

@[expose] def mulVecCode (M v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun i => dotCode M v i.val

@[expose] def projAct (k : ℕ) (v : Array ℕ) : Array ℕ :=
  normCode (mulVecCode (genCodes.getD k #[]) v)

@[expose] def validV (v : Array ℕ) : Bool :=
  v.size == 8 && v.all (· < 8) && v.any (· != 0) && leadCode v == 1

@[expose] def keyV (v : Array ℕ) : ℕ := v.foldl (fun a x => a * 8 + x) 0

@[expose] def rootV : Array ℕ := #[1, 0, 0, 0, 0, 0, 0, 0]

@[expose] def lineCert : ArrCert := arrBfs projAct 18 keyV rootV 2500

@[expose] def piArr (c : ArrCert) (k : ℕ) : Array ℕ :=
  Array.ofFn (n := 2457) fun i => (c.edges[i.val]!)[k]!

theorem ofNat'_toNat (a : GF8) : GF8.ofNat' a.toNat = a := by
  obtain ⟨⟨v, hv⟩⟩ := a
  simp only [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hv]

theorem toNat_lt (a : GF8) : a.toNat < 8 := a.val.isLt

theorem lead_ne_zero {w : Fin 8 → GF8} (hw : w ≠ 0) : lead w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  unfold lead
  cases hf : (List.finRange 8).find? (fun i => decide (w i ≠ 0)) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf i (List.mem_finRange i)
    simp_all
  | some j =>
    have := List.find?_some hf
    simpa using this

theorem lead_smul {c : GF8} (hc : c ≠ 0) {w : Fin 8 → GF8} (hw : w ≠ 0) :
    lead (c • w) = c * lead w := by
  have hpred : (fun i => decide ((c • w) i ≠ 0)) = fun i => decide (w i ≠ 0) := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, hc]
  unfold lead
  rw [hpred]
  cases hf : (List.finRange 8).find? (fun i => decide (w i ≠ 0)) with
  | none =>
    exfalso
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have := List.find?_eq_none.mp hf i (List.mem_finRange i)
    simp_all
  | some j => simp [Pi.smul_apply, smul_eq_mul]

theorem normV_ne_zero {w : Fin 8 → GF8} (hw : w ≠ 0) : normV w ≠ 0 :=
  smul_ne_zero (inv_ne_zero (lead_ne_zero hw)) hw

theorem lead_normV {w : Fin 8 → GF8} (hw : w ≠ 0) : lead (normV w) = 1 := by
  unfold normV
  rw [lead_smul (inv_ne_zero (lead_ne_zero hw)) hw]
  exact inv_mul_cancel₀ (lead_ne_zero hw)

theorem ofNat'_mulNat {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (GF8.mulNat a b) = GF8.ofNat' a * GF8.ofNat' b := by
  show _ = GF8.ofNat' (GF8.mulNat (GF8.ofNat' a).toNat (GF8.ofNat' b).toNat)
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem mulNat_lt {a b : ℕ} (ha : a < 8) (hb : b < 8) : GF8.mulNat a b < 8 := by
  have h : ∀ a : Fin 8, ∀ b : Fin 8, GF8.mulNat a b < 8 := by decide
  exact h ⟨a, ha⟩ ⟨b, hb⟩

theorem xor_lt8 {a b : ℕ} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 :=
  Nat.xor_lt_two_pow (n := 3) ha hb

theorem ofNat'_xor {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (a ^^^ b) = GF8.ofNat' a + GF8.ofNat' b := by
  show _ = GF8.ofNat' ((GF8.ofNat' a).toNat ^^^ (GF8.ofNat' b).toNat)
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat'_xor8 {t0 t1 t2 t3 t4 t5 t6 t7 : ℕ} (h0 : t0 < 8) (h1 : t1 < 8) (h2 : t2 < 8)
    (h3 : t3 < 8) (h4 : t4 < 8) (h5 : t5 < 8) (h6 : t6 < 8) (h7 : t7 < 8) :
    GF8.ofNat' (t0 ^^^ t1 ^^^ t2 ^^^ t3 ^^^ t4 ^^^ t5 ^^^ t6 ^^^ t7) =
      GF8.ofNat' t0 + GF8.ofNat' t1 + GF8.ofNat' t2 + GF8.ofNat' t3 + GF8.ofNat' t4 +
        GF8.ofNat' t5 + GF8.ofNat' t6 + GF8.ofNat' t7 := by
  have h01 := xor_lt8 h0 h1
  have h012 := xor_lt8 h01 h2
  have h0123 := xor_lt8 h012 h3
  have h01234 := xor_lt8 h0123 h4
  have h012345 := xor_lt8 h01234 h5
  have h0123456 := xor_lt8 h012345 h6
  rw [ofNat'_xor h0123456 h7, ofNat'_xor h012345 h6, ofNat'_xor h01234 h5, ofNat'_xor h0123 h4,
    ofNat'_xor h012 h3, ofNat'_xor h01 h2, ofNat'_xor h0 h1]

theorem getElem!_matCode (M : Matrix (Fin 8) (Fin 8) GF8) (i j : Fin 8) :
    (matCode M)[8 * i.val + j.val]! = (M i j).toNat := by
  have h : 8 * i.val + j.val < 64 := by omega
  rw [matCode, getElem!_ofFn_nat _ h]
  have e1 : (⟨(8 * i.val + j.val) / 8, by omega⟩ : Fin 8) = i :=
    Fin.ext (by show (8 * i.val + j.val) / 8 = i.val; omega)
  have e2 : (⟨(8 * i.val + j.val) % 8, by omega⟩ : Fin 8) = j :=
    Fin.ext (by show (8 * i.val + j.val) % 8 = j.val; omega)
  simp only [e1, e2]

theorem vecOf_mulVecCode (M : Matrix (Fin 8) (Fin 8) GF8) {v : Array ℕ} (hv1 : v.size = 8)
    (hv2 : ∀ x ∈ v, x < 8) : vecOf (mulVecCode (matCode M) v) = M.mulVec (vecOf v) := by
  have hvj : ∀ j : ℕ, j < 8 → v[j]! < 8 := fun j hj =>
    hv2 _ (by rw [getElem!_pos v j (by omega)]; exact Array.getElem_mem (by omega))
  funext i
  simp only [vecOf, mulVecCode]
  rw [getElem!_ofFn_nat _ i.2]
  simp only [dotCode]
  have hM : ∀ j : Fin 8, (matCode M)[8 * i.val + j.val]! = (M i j).toNat :=
    fun j => getElem!_matCode M i j
  have m0 : (matCode M)[8 * i.val]! = (M i 0).toNat := hM 0
  have m1 : (matCode M)[8 * i.val + 1]! = (M i 1).toNat := hM 1
  have m2 : (matCode M)[8 * i.val + 2]! = (M i 2).toNat := hM 2
  have m3 : (matCode M)[8 * i.val + 3]! = (M i 3).toNat := hM 3
  have m4 : (matCode M)[8 * i.val + 4]! = (M i 4).toNat := hM 4
  have m5 : (matCode M)[8 * i.val + 5]! = (M i 5).toNat := hM 5
  have m6 : (matCode M)[8 * i.val + 6]! = (M i 6).toNat := hM 6
  have m7 : (matCode M)[8 * i.val + 7]! = (M i 7).toNat := hM 7
  rw [m0, m1, m2, m3, m4, m5, m6, m7]
  rw [ofNat'_xor8 (mulNat_lt (toNat_lt _) (hvj 0 (by norm_num)))
    (mulNat_lt (toNat_lt _) (hvj 1 (by norm_num))) (mulNat_lt (toNat_lt _) (hvj 2 (by norm_num)))
    (mulNat_lt (toNat_lt _) (hvj 3 (by norm_num))) (mulNat_lt (toNat_lt _) (hvj 4 (by norm_num)))
    (mulNat_lt (toNat_lt _) (hvj 5 (by norm_num))) (mulNat_lt (toNat_lt _) (hvj 6 (by norm_num)))
    (mulNat_lt (toNat_lt _) (hvj 7 (by norm_num)))]
  rw [ofNat'_mulNat (toNat_lt _) (hvj 0 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 1 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 2 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 3 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 4 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 5 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 6 (by norm_num)),
    ofNat'_mulNat (toNat_lt _) (hvj 7 (by norm_num))]
  simp only [ofNat'_toNat, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
  rfl


theorem ofNat'_eq_zero_iff {x : ℕ} (hx : x < 8) : GF8.ofNat' x = 0 ↔ x = 0 := by
  show GF8.ofNat' x = GF8.ofNat' 0 ↔ x = 0
  simp [GF8.ofNat', Nat.mod_eq_of_lt hx]

theorem matCode_lt (M : Matrix (Fin 8) (Fin 8) GF8) (t : ℕ) : (matCode M)[t]! < 8 := by
  by_cases ht : t < 64
  · rw [matCode, getElem!_ofFn_nat _ ht]
    exact toNat_lt _
  · rw [getElem!_neg _ _ (by simp [matCode]; omega)]
    decide

theorem lt_of_mem_mulVecCode (M : Matrix (Fin 8) (Fin 8) GF8) {v : Array ℕ}
    (hv : ∀ j : ℕ, j < 8 → v[j]! < 8) : ∀ x ∈ mulVecCode (matCode M) v, x < 8 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  simp only [mulVecCode, Array.getElem_ofFn, dotCode]
  have l : ∀ j : ℕ, j < 8 → ∀ t : ℕ, GF8.mulNat (matCode M)[t]! v[j]! < 8 := fun j hj t =>
    mulNat_lt (matCode_lt M t) (hv j hj)
  exact xor_lt8 (xor_lt8 (xor_lt8 (xor_lt8 (xor_lt8 (xor_lt8 (xor_lt8 (l 0 (by norm_num) _)
    (l 1 (by norm_num) _)) (l 2 (by norm_num) _)) (l 3 (by norm_num) _)) (l 4 (by norm_num) _))
    (l 5 (by norm_num) _)) (l 6 (by norm_num) _)) (l 7 (by norm_num) _)

theorem leadCode_lt {w : Array ℕ} (hw : ∀ j : ℕ, j < 8 → w[j]! < 8) : leadCode w < 8 := by
  unfold leadCode
  cases hf : (List.finRange 8).find? (fun i => decide (w[i.val]! ≠ 0)) with
  | none => norm_num
  | some j => exact hw j.val j.2

theorem ginv_lt {c : ℕ} (hc : c < 8) : ginv c < 8 :=
  mulNat_lt (mulNat_lt hc hc) (mulNat_lt (mulNat_lt hc hc) (mulNat_lt hc hc))

theorem lead_vecOf {w : Array ℕ} (hw : ∀ j : ℕ, j < 8 → w[j]! < 8) :
    lead (vecOf w) = GF8.ofNat' (leadCode w) := by
  have hpred : (fun i : Fin 8 => decide (vecOf w i ≠ 0)) = fun i => decide (w[i.val]! ≠ 0) := by
    funext i
    simp only [vecOf]
    exact decide_eq_decide.mpr (not_congr (ofNat'_eq_zero_iff (hw i.val i.2)))
  unfold lead leadCode
  rw [hpred]
  cases hf : (List.finRange 8).find? (fun i => decide (w[i.val]! ≠ 0)) <;> rfl

theorem vecOf_normCode {w : Array ℕ} (hw1 : w.size = 8) (hw : ∀ j : ℕ, j < 8 → w[j]! < 8) :
    vecOf (normCode w) = normV (vecOf w) := by
  have hl := leadCode_lt hw
  have hinv : GF8.ofNat' (ginv (leadCode w)) = (GF8.ofNat' (leadCode w))⁻¹ := by
    have h1 : (GF8.ofNat' (leadCode w))⁻¹ =
        GF8.ofNat' (ginv (GF8.ofNat' (leadCode w)).toNat) := rfl
    rw [h1]
    simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hl]
  funext i
  simp only [vecOf, normCode, normV, Pi.smul_apply, smul_eq_mul]
  rw [lead_vecOf hw, ← hinv]
  have hmap : (w.map (GF8.mulNat (ginv (leadCode w))))[i.val]! =
      GF8.mulNat (ginv (leadCode w)) w[i.val]! := by
    rw [getElem!_pos _ i.val (by simp [hw1]), Array.getElem_map, getElem!_pos w i.val (by omega)]
  rw [hmap, ofNat'_mulNat (ginv_lt hl) (hw i.val i.2)]

theorem vecOf_projAct {k : ℕ} (hk : k < 18) {v : Array ℕ} (hv1 : v.size = 8)
    (hv2 : ∀ x ∈ v, x < 8) :
    vecOf (projAct k v) = normV ((letterMat k).mulVec (vecOf v)) := by
  have hM : genCodes.getD k #[] = matCode (letterMat k) := by
    simp [genCodes, Array.getD_eq_getD_getElem?, hk]
  have hvj : ∀ j : ℕ, j < 8 → v[j]! < 8 := fun j hj =>
    hv2 _ (by rw [getElem!_pos v j (by omega)]; exact Array.getElem_mem (by omega))
  have hsz : (mulVecCode (matCode (letterMat k)) v).size = 8 := by simp [mulVecCode]
  have hlt := lt_of_mem_mulVecCode (letterMat k) hvj
  have hwj : ∀ j : ℕ, j < 8 → (mulVecCode (matCode (letterMat k)) v)[j]! < 8 := fun j hj =>
    hlt _ (by rw [getElem!_pos _ j (by omega)]; exact Array.getElem_mem (by omega))
  unfold projAct
  rw [hM, vecOf_normCode hsz hwj, vecOf_mulVecCode _ hv1 hv2]

@[expose] noncomputable def decL (v : Array ℕ) : ℙ GF8 (Fin 8 → GF8) :=
  if h : vecOf v ≠ 0 then Projectivization.mk GF8 (vecOf v) h
  else Projectivization.mk GF8 (Pi.single 0 1) (by simp [Pi.single_eq_zero_iff])

theorem validV_spec {v : Array ℕ} (h : validV v = true) :
    v.size = 8 ∧ (∀ x ∈ v, x < 8) ∧ vecOf v ≠ 0 ∧ lead (vecOf v) = 1 := by
  simp only [validV, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq,
    Array.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, ⟨i, hi, h3⟩⟩, h4⟩ := h
  have hall : ∀ x ∈ v, x < 8 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
    simpa using h2 i hi
  have hvj : ∀ j : ℕ, j < 8 → v[j]! < 8 := fun j hj =>
    hall _ (by rw [getElem!_pos v j (by omega)]; exact Array.getElem_mem (by omega))
  refine ⟨h1, hall, ?_, ?_⟩
  · intro h0
    have hi8 : i < 8 := by omega
    have := congrFun h0 ⟨i, hi8⟩
    simp only [vecOf, Pi.zero_apply] at this
    rw [ofNat'_eq_zero_iff (hvj i hi8), getElem!_pos v i hi] at this
    exact h3 this
  · rw [lead_vecOf hvj, h4]
    rfl

theorem eq_of_vecOf_eq {a b : Array ℕ} (ha : validV a = true) (hb : validV b = true)
    (h : vecOf a = vecOf b) : a = b := by
  obtain ⟨ha1, ha2, -, -⟩ := validV_spec ha
  obtain ⟨hb1, hb2, -, -⟩ := validV_spec hb
  have key : ∀ (t : Array ℕ), t.size = 8 → (∀ x ∈ t, x < 8) → ∀ i : Fin 8,
      t[i.val]! = (vecOf t i).toNat := by
    intro t ht1 ht2 i
    have hi : i.val < t.size := by rw [ht1]; exact i.2
    have hlt : t[i.val]! < 8 := ht2 _ (by rw [getElem!_pos t i.val hi]; exact Array.getElem_mem hi)
    simp only [vecOf, GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hlt]
  apply Array.ext (ha1.trans hb1.symm)
  intro i hia hib
  have hi8 : i < 8 := by rw [← ha1]; exact hia
  have e := congrFun h ⟨i, hi8⟩
  have k1 := key a ha1 ha2 ⟨i, hi8⟩
  have k2 := key b hb1 hb2 ⟨i, hi8⟩
  rw [e, getElem!_pos a i hia] at k1
  rw [getElem!_pos b i hib] at k2
  exact k1.trans k2.symm

theorem decL_inj {a b : Array ℕ} (ha : validV a = true) (hb : validV b = true)
    (h : decL a = decL b) : a = b := by
  obtain ⟨-, -, hna, hla⟩ := validV_spec ha
  obtain ⟨-, -, hnb, hlb⟩ := validV_spec hb
  unfold decL at h
  rw [dite_eq_left hna, dite_eq_left hnb, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hna (by rw [← hc]; simp)
  have hlead : lead (c • vecOf b) = c * lead (vecOf b) := lead_smul hc0 hnb
  rw [hc, hla, hlb, mul_one] at hlead
  rw [← hlead, one_smul] at hc
  exact eq_of_vecOf_eq ha hb hc.symm

theorem decL_projAct {k : ℕ} (hk : k < 18) {v : Array ℕ} (hv : validV v = true) :
    decL (projAct k v) = letterGL k • decL v := by
  obtain ⟨hv1, hv2, hne, -⟩ := validV_spec hv
  have hMw : (letterMat k).mulVec (vecOf v) ≠ 0 := by
    intro h
    apply hne
    have := congrArg (letterMat k).mulVec h
    rwa [Matrix.mulVec_mulVec, letterMat_mul_self, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have hn := normV_ne_zero hMw
  have hvec := vecOf_projAct hk hv1 hv2
  have hne' : vecOf (projAct k v) ≠ 0 := by rw [hvec]; exact hn
  have hsmul : (letterGL k) • (vecOf v) = (letterMat k).mulVec (vecOf v) := rfl
  unfold decL
  rw [dite_eq_left hne', dite_eq_left hne, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨(lead ((letterMat k).mulVec (vecOf v)))⁻¹, ?_⟩
  rw [hsmul, hvec]
  rfl

theorem keyV_eq_of_decL_eq {a b : Array ℕ} (ha : validV a = true) (hb : validV b = true)
    (h : decL a = decL b) : keyV a = keyV b := by
  rw [decL_inj ha hb h]


@[expose] def lineGroup : Subgroup (GL (Fin 8) GF8) :=
  Subgroup.closure (letterGL '' {k | k < 18})

@[expose] noncomputable def ptL (c : ArrCert) (i : ℕ) : ℙ GF8 (Fin 8 → GF8) := decL c.pts[i]!

section Action

variable {c : ArrCert}

theorem hact18 : ∀ k < 18, ∀ a, validV a = true → decL (projAct k a) = letterGL k • decL a :=
  fun _ hk _ ha => decL_projAct hk ha

theorem orbit_ptL (hc : arrCertOK projAct 18 validV keyV rootV c = true) :
    MulAction.orbit lineGroup (decL rootV) = (fun i => ptL c i) '' {i | i < c.pts.size} :=
  orbit_of_arrCertOK (gens := letterGL) hc hact18

theorem ptL_inj (hc : arrCertOK projAct 18 validV keyV rootV c = true) {i j : ℕ}
    (hi : i < c.pts.size) (hj : j < c.pts.size) (h : ptL c i = ptL c j) : i = j :=
  arrCertOK_dec_inj hc (fun _ _ ha hb hab => keyV_eq_of_decL_eq ha hb hab) hi hj h

theorem exists_ptL_smul (hc : arrCertOK projAct 18 validV keyV rootV c = true) (g : lineGroup)
    {i : ℕ} (hi : i < c.pts.size) : ∃ j < c.pts.size, ptL c j = (g : GL (Fin 8) GF8) • ptL c i := by
  have hmem : ptL c i ∈ MulAction.orbit lineGroup (decL rootV) := by
    rw [orbit_ptL hc]
    exact ⟨i, hi, rfl⟩
  have hmem' : (g : lineGroup) • ptL c i ∈ MulAction.orbit lineGroup (decL rootV) := by
    obtain ⟨h, hh⟩ := hmem
    refine ⟨g * h, ?_⟩
    have hh' : h • decL rootV = ptL c i := hh
    show (g * h) • decL rootV = g • ptL c i
    rw [mul_smul, hh']
  rw [orbit_ptL hc] at hmem'
  obtain ⟨j, hj, hjg⟩ := hmem'
  exact ⟨j, hj, hjg⟩

variable (hc : arrCertOK projAct 18 validV keyV rootV c = true) (hsize : c.pts.size = 2457)
include hc hsize

theorem exists_fin_smul (g : lineGroup) (i : Fin 2457) :
    ∃ j : Fin 2457, ptL c j = (g : GL (Fin 8) GF8) • ptL c i := by
  obtain ⟨j, hj, hjg⟩ := exists_ptL_smul hc g (i := i.val) (by rw [hsize]; exact i.2)
  exact ⟨⟨j, by rw [← hsize]; exact hj⟩, hjg⟩

theorem ptL_inj_fin {i j : Fin 2457} (h : ptL c i = ptL c j) : i = j :=
  Fin.ext (ptL_inj hc (by rw [hsize]; exact i.2) (by rw [hsize]; exact j.2) h)

noncomputable def rhoFun (g : lineGroup) (i : Fin 2457) : Fin 2457 :=
  (exists_fin_smul hc hsize g i).choose

theorem rhoFun_spec (g : lineGroup) (i : Fin 2457) :
    ptL c (rhoFun hc hsize g i) = (g : GL (Fin 8) GF8) • ptL c i :=
  (exists_fin_smul hc hsize g i).choose_spec

theorem rhoFun_bijective (g : lineGroup) : Function.Bijective (rhoFun hc hsize g) := by
  have hinj : Function.Injective (rhoFun hc hsize g) := by
    intro i j hij
    apply ptL_inj_fin hc hsize
    apply smul_left_cancel (g : GL (Fin 8) GF8)
    rw [← rhoFun_spec hc hsize, ← rhoFun_spec hc hsize, hij]
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

noncomputable def rho : lineGroup →* Equiv.Perm (Fin 2457) :=
  MonoidHom.mk' (fun g => Equiv.ofBijective (rhoFun hc hsize g) (rhoFun_bijective hc hsize g))
    (fun g h => by
      apply Equiv.ext
      intro i
      apply ptL_inj_fin hc hsize
      show ptL c (rhoFun hc hsize (g * h) i) = ptL c (rhoFun hc hsize g (rhoFun hc hsize h i))
      rw [rhoFun_spec hc hsize, rhoFun_spec hc hsize, rhoFun_spec hc hsize]
      exact mul_smul _ _ _)

theorem ptL_rho (g : lineGroup) (i : Fin 2457) :
    ptL c (rho hc hsize g i) = (g : GL (Fin 8) GF8) • ptL c i :=
  rhoFun_spec hc hsize g i

@[expose] def letterX (k : ℕ) : lineGroup :=
  if h : k < 18 then ⟨letterGL k, Subgroup.subset_closure ⟨k, h, rfl⟩⟩ else 1

theorem rep_piArr {k : ℕ} (hk : k < 18) : Rep 2457 (piArr c k) (rho hc hsize (letterX k)) := by
  intro x
  have hx : x.val < c.pts.size := by rw [hsize]; exact x.2
  obtain ⟨hj, hedge⟩ := arrCertOK_edge hc hx hk
  have hvalid := arrCertOK_valid hc hx
  have hpt : ptL c ((c.edges[x.val]!)[k]!) = (letterGL k) • ptL c x.val := by
    show decL c.pts[(c.edges[x.val]!)[k]!]! = _
    rw [hedge, hact18 k hk _ hvalid]
    rfl
  have hx' : ptL c (rho hc hsize (letterX k) x) = (letterGL k) • ptL c x.val := by
    rw [ptL_rho]
    simp [letterX, hk]
  have := ptL_inj hc hj (by rw [hsize]; exact (rho hc hsize (letterX k) x).2) (hpt.trans hx'.symm)
  simp only [piArr]
  rw [getElem!_ofFn_nat _ x.2]
  exact this

@[expose] def wordX : List ℕ → lineGroup
  | [] => 1
  | l :: w => letterX l * wordX w

@[expose] def compWord (c : ArrCert) (w : List ℕ) : Array ℕ :=
  w.foldr (fun l acc => compA 2457 (piArr c l) acc) (idA 2457)

omit hc hsize in
theorem compWord_nil : compWord c [] = idA 2457 := by simp [compWord]

omit hc hsize in
theorem compWord_cons (l : ℕ) (w : List ℕ) :
    compWord c (l :: w) = compA 2457 (piArr c l) (compWord c w) := by simp [compWord]

theorem rep_compWord {w : List ℕ} (hw : ∀ l ∈ w, l < 18) :
    Rep 2457 (compWord c w) (rho hc hsize (wordX w)) := by
  induction w with
  | nil =>
    rw [compWord_nil, wordX, map_one]
    exact rep_idA
  | cons l w ih =>
    have h1 := rep_piArr hc hsize (hw l List.mem_cons_self)
    have h2 := ih (fun m hm => hw m (List.mem_cons_of_mem l hm))
    rw [compWord_cons, wordX, map_mul]
    exact rep_compA h1 h2

end Action

theorem coe_wordX {w : List ℕ} (hw : ∀ l ∈ w, l < 18) :
    ((wordX w : lineGroup) : GL (Fin 8) GF8) = wordGL w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have hl := hw l List.mem_cons_self
    rw [wordX, Subgroup.coe_mul, ih (fun m hm => hw m (List.mem_cons_of_mem l hm))]
    simp [letterX, hl, wordGL]

theorem lineGroup_eq : lineGroup = trialityGroup8 := by
  apply le_antisymm
  · rw [lineGroup, Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact letterGL_mem k
  · rw [trialityGroup8, Subgroup.closure_le]
    intro A hA
    rcases hA with ⟨a, s, hM⟩ | ⟨s, hM⟩
    · have ha : a.toNat < 8 := a.val.isLt
      cases s with
      | true =>
        have hAeq : A = letterGL a.toNat := by
          apply Units.ext
          rw [hM]
          simp only [letterGL, letterMat, ha, ite_true]
          rw [ofNat'_toNat]
        rw [hAeq]
        exact Subgroup.subset_closure ⟨a.toNat, (show a.toNat < 18 by omega), rfl⟩
      | false =>
        have hAeq : A = letterGL (8 + a.toNat) := by
          apply Units.ext
          rw [hM]
          have h1 : ¬ (8 + a.toNat < 8) := by omega
          have h2 : 8 + a.toNat < 16 := by omega
          simp only [letterGL, letterMat, h1, h2, ite_false, ite_true, Nat.add_sub_cancel_left]
          rw [ofNat'_toNat]
        rw [hAeq]
        exact Subgroup.subset_closure ⟨8 + a.toNat, (show 8 + a.toNat < 18 by omega), rfl⟩
    · cases s with
      | true =>
        have hAeq : A = letterGL 16 := by
          apply Units.ext
          rw [hM]
          simp [letterGL, letterMat]
        rw [hAeq]
        exact Subgroup.subset_closure ⟨16, (by norm_num), rfl⟩
      | false =>
        have hAeq : A = letterGL 17 := by
          apply Units.ext
          rw [hM]
          simp [letterGL, letterMat]
        rw [hAeq]
        exact Subgroup.subset_closure ⟨17, (by norm_num), rfl⟩

end CFSG.RankThree.PartTwo.Sec4.Item434D42
