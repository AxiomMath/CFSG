module

public import CFSG.Quasithin.H13.L32AC50aPack
public import CFSG.Permutation.FinPackInv

public section

namespace CFSG.Quasithin.H13.A6.L19aPack

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack

theorem h5 : (5 : ℕ) ≤ 16 := by norm_num

@[expose] def e5 : ℕ := 274960

theorem enc_one5 : enc (1 : Perm (Fin 5)) = e5 := by decide +kernel

@[expose] def invC5 : List ℕ := [
    213280, 136240, 74560, 213505, 271105, 144385, 213010, 266290, 77890, 132115, 262435, 66115,
    8980, 12580, 4660]

@[expose] def c3eC : List ℕ := [
    274960, 148240, 205840, 267040, 78880, 270640, 82480, 143680, 201280, 274465, 262705, 12865,
    274690, 262930, 13330, 266755, 270355, 16915, 78340, 143380, 197140]

@[expose] def twoC : List ℕ := [
    274960, 213520, 271120, 144400, 274720, 213280, 82720, 201760, 147760, 266800, 136240, 74800,
    205120, 78400, 136000, 74560, 274945, 213505, 271105, 144385, 262945, 13345, 270385, 16945,
    143425, 197185, 267010, 78850, 274450, 213010, 17170, 197650, 266290, 262450, 77890, 12610,
    270595, 82435, 147475, 262675, 132115, 9235, 266275, 262435, 66115, 4675, 143620, 201220,
    204820, 12820, 131860, 8980, 77860, 12580, 66100, 4660]

theorem w1_ok : walkK 5 (fun c => !Nat.beq (mulK 5 c c) e5 || Nat.beq c e5 || !evenK 5 c ||
    memK c invC5) 5 0 0 0 = true := by decide +kernel

theorem w2_ok : walkK 5 (fun c => !Nat.beq (mulK 5 (mulK 5 c c) c) e5 || memK c c3eC) 5 0 0 0 =
    true := by decide +kernel

theorem w3_ok : walkK 5 (fun c => !Nat.beq (powK 5 e5 c 8) e5 || memK c twoC) 5 0 0 0 = true := by
  decide +kernel

theorem beq_one_false {s : Perm (Fin 5)} (h : s ≠ 1) : Nat.beq (enc s) e5 = false := by
  rw [← enc_one5]
  exact beq_enc_false h5 h

theorem beq_mul_iff {σ τ ρ : Perm (Fin 5)} :
    Nat.beq (mulK 5 (enc σ) (enc τ)) (enc ρ) = true ↔ σ * τ = ρ := by
  rw [← enc_mul h5, beq_enc_iff h5]

theorem mem_invC5 {a : Perm (Fin 5)} (h1 : a * a = 1) (h2 : a ≠ 1) (h3 : Perm.sign a = 1) :
    memK (enc a) invC5 = true := by
  have h := walkK_sound w1_ok a
  rw [← enc_one5, beq_mul_iff.2 h1, beq_enc_false h5 h2, (sign_eq_one_iff_evenK h5 a).1 h3] at h
  simpa using h

theorem mem_c3eC {s : Perm (Fin 5)} (h1 : s * s * s = 1) : memK (enc s) c3eC = true := by
  have h := walkK_sound w2_ok s
  rw [← enc_one5, ← enc_mul h5, beq_mul_iff.2 h1] at h
  simpa using h

theorem mem_twoC {g : Perm (Fin 5)} (h1 : g ^ 8 = 1) : memK (enc g) twoC = true := by
  have h := walkK_sound w3_ok g
  rw [← enc_one5, ← enc_pow h5, h1, Nat.beq_refl] at h
  simpa using h

@[expose] noncomputable def klK (ca cb : ℕ) : List ℕ := [e5, ca, cb, mulK 5 ca cb]

theorem map_enc_kl (a b : Perm (Fin 5)) : [1, a, b, a * b].map enc = klK (enc a) (enc b) := by
  rw [klK, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil, enc_one5,
    enc_mul h5]

theorem mem_kl_iff (a b g : Perm (Fin 5)) :
    g ∈ [1, a, b, a * b] ↔ memK (enc g) (klK (enc a) (enc b)) = true := by
  rw [mem_iff_enc h5, map_enc_kl, memK_iff]

@[expose] noncomputable def conjK5 (cg cx : ℕ) : ℕ := mulK 5 (mulK 5 cg cx) (invCK 5 cg)

theorem enc_conj (g x : Perm (Fin 5)) : enc (g * x * g⁻¹) = conjK5 (enc g) (enc x) := by
  rw [conjK5, enc_mul h5, enc_mul h5, enc_inv_invCK h5]

@[expose] noncomputable def normK5 (ca cb cg : ℕ) : Bool :=
  memK (conjK5 cg ca) (klK ca cb) && memK (conjK5 cg cb) (klK ca cb)

theorem normK5_iff (a b g : Perm (Fin 5)) :
    (g * a * g⁻¹ ∈ [1, a, b, a * b] ∧ g * b * g⁻¹ ∈ [1, a, b, a * b]) ↔
      normK5 (enc a) (enc b) (enc g) = true := by
  rw [mem_kl_iff, mem_kl_iff, enc_conj, enc_conj, normK5, Bool.and_eq_true]

@[expose] noncomputable def isKlK (ca cb : ℕ) : Bool :=
  Nat.beq (mulK 5 ca cb) (mulK 5 cb ca) && !Nat.beq ca cb

theorem forall_kl {F : ℕ → ℕ → Bool}
    (hF : allK (fun ca => allK (fun cb => !isKlK ca cb || F ca cb) invC5) invC5 = true)
    {a b : Perm (Fin 5)} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) (hsa : Perm.sign a = 1) (hsb : Perm.sign b = 1) :
    F (enc a) (enc b) = true := by
  have h := allK_iff.1 (allK_iff.1 hF _ (memK_iff.1 (mem_invC5 ha ha1 hsa))) _
    (memK_iff.1 (mem_invC5 hb hb1 hsb))
  have hk : isKlK (enc a) (enc b) = true := by
    rw [isKlK, ← enc_mul h5, ← enc_mul h5, hab, Nat.beq_refl, beq_enc_false h5 hne]
    all_goals rfl
  rw [hk] at h
  simpa using h

@[expose] noncomputable def flK (ca cb cs : ℕ) : List ℕ :=
  [e5, mulK 5 cs e5, mulK 5 (mulK 5 cs cs) e5, ca, mulK 5 cs ca, mulK 5 (mulK 5 cs cs) ca,
    cb, mulK 5 cs cb, mulK 5 (mulK 5 cs cs) cb, mulK 5 ca cb, mulK 5 cs (mulK 5 ca cb),
    mulK 5 (mulK 5 cs cs) (mulK 5 ca cb)]

theorem map_enc_fl (a b s : Perm (Fin 5)) :
    ([1, a, b, a * b].flatMap fun w => [w, s * w, s * s * w]).map enc =
      flK (enc a) (enc b) (enc s) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.append_nil, List.map_cons, List.map_nil, enc_mul h5, enc_one5, flK]

@[expose] noncomputable def cosK (ca cb cs : ℕ) : Bool :=
  allK (fun cv => memK (conjK5 cv cs) (flK ca cb cs)) (klK ca cb)

theorem cosK_of (a b s : Perm (Fin 5))
    (h : ∀ v ∈ [1, a, b, a * b], v * s * v⁻¹ ∈ [1, a, b, a * b].flatMap
      fun w => [w, s * w, s * s * w]) : cosK (enc a) (enc b) (enc s) = true := by
  rw [cosK, allK_iff]
  intro cv hcv
  rw [← map_enc_kl] at hcv
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hcv
  have h1 := List.mem_map_of_mem (f := enc) (h v hv)
  rw [map_enc_fl, enc_conj] at h1
  exact memK_iff.2 h1

@[expose] noncomputable def t3K (c : ℕ) : Bool :=
  Nat.beq (mulK 5 (mulK 5 c c) c) e5 && !Nat.beq c e5

theorem t1_ok : allK (fun ca => allK (fun cb => !isKlK ca cb || allK (fun cg =>
    !normK5 ca cb cg || !evenK 5 cg || memK cg (klK ca cb)) twoC) invC5) invC5 = true := by
  decide +kernel

theorem t2_ok : allK (fun ca => allK (fun cb => !isKlK ca cb || allK (fun cs =>
    !cosK ca cb cs || normK5 ca cb cs) c3eC) invC5) invC5 = true := by
  decide +kernel

theorem t3_ok : allK (fun ca => allK (fun cb => !isKlK ca cb || allK (fun cs =>
    Nat.beq cs e5 || !normK5 ca cb cs || allK (fun cg => !normK5 ca cb cg ||
      !memK (mulK 5 (conjK5 cg cs) (invCK 5 cs)) (klK ca cb) || memK cg (klK ca cb)) twoC)
    c3eC) invC5) invC5 = true := by
  decide +kernel

theorem t4_ok : allK (fun ca => allK (fun cb => !isKlK ca cb ||
    !walkK 5 (fun c => !(t3K c && normK5 ca cb c)) 5 0 0 0) invC5) invC5 = true := by
  decide +kernel

theorem t5_ok : allK (fun c => !evenK 5 c || Nat.beq (mulK 5 c c) e5) twoC = true := by
  decide +kernel

end CFSG.Quasithin.H13.A6.L19aPack
