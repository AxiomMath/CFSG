module

public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.RankThree.Asc83Table.J3Defs
public import CFSG.RankThree.Asc83Table.OrbitBound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Sporadic.J3
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.Asc83Table.J3

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.Sporadic.J3 CFSG.SectionRank.LocalWitness Subgroup MulAction
open scoped Matrix

abbrev D : CFSG.Sporadic.J3.Native.Data := CFSG.Sporadic.J3.Native.j3Data

private theorem seedA_eq' : D.seedA = NativeSporadic.J3Seed1 := rfl

private theorem seedB_eq' : D.seedB = NativeSporadic.J3Seed2 := rfl

theorem seedMonoid_eq :
    NativeSporadic.seedMonoid 2 80 1 NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 =
      NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB := by
  rw [seedA_eq', seedB_eq']

@[expose] noncomputable def unitsEquiv :
    NativeSporadic.J3 ≃* (NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB)ˣ :=
  Units.mapEquiv (MulEquiv.submonoidCongr seedMonoid_eq)

@[expose] noncomputable def groupEquiv :
    (NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB)ˣ ≃* J D :=
  (NativeSporadic.matrixSeedEquiv 2 80 (by norm_num) (mA D) (mB D) (det_mA_ne_zero j3Facts.powA)
    (det_mB_ne_zero j3Facts.powB)).trans (MulEquiv.subgroupCongr (by
      show _ = Subgroup.closure {gA D, gB D}
      rw [gA_eq j3Facts.powA, gB_eq j3Facts.powB]))

@[expose] noncomputable def φ : NativeSporadic.J3 ≃* J D := unitsEquiv.trans groupEquiv

theorem coe_groupEquiv (g : (NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB)ˣ) :
    (((groupEquiv g : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      g.val.val := rfl

private theorem coe_unitsEquiv (g : NativeSporadic.J3) : (unitsEquiv g).val.val = g.val.val :=
  rfl

theorem coe_φ (g : NativeSporadic.J3) :
    (((φ g : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) = g.val.val := by
  rw [φ, MulEquiv.trans_apply, coe_groupEquiv, coe_unitsEquiv]

theorem toVecD_eq (d v : ℕ) : CFSG.Sporadic.J3.toVecD d v = CFSG.Sporadic.SmallF2.toVecD d v :=
  rfl

theorem smul_P_eq {g : J D} {Y : Array ℕ}
    (hg : ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      CFSG.Sporadic.SmallF2.rowsMatrix 80 Y) (i : ℕ) :
    g • P D i = CFSG.Sporadic.SmallF2.toVecD 80 (colAct Y D.pts[i]!) := by
  rw [smul_vec, hg, P, toVecD_eq, CFSG.Sporadic.SmallF2.rowsMatrix_mulVec]
  rfl

variable {cert : J3Cert}
  (hJ : j3Check NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 D.pts D.n cert = true)

include hJ in
theorem mcert_ok :
    mcertCheck (ops2fr 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 cert.mcert = true := by
  unfold j3Check at hJ
  simp only [Bool.and_eq_true] at hJ
  exact hJ.1

local notation "Rg" => certRegs (ops2fr 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 cert.mcert

include hJ in
theorem extra_ok : j3Extra Rg D.pts D.n cert = true := by
  unfold j3Check at hJ
  simp only [Bool.and_eq_true] at hJ
  exact hJ.2

@[expose] noncomputable def X (r : ℕ) : J D := φ (regUnit (spec2fr 80) (mcert_ok hJ) r)

@[expose] noncomputable def XW (w : Native.Word) : J D :=
  φ (wordUnit (spec2fr 80) (mcert_ok hJ) w)

theorem matrix_X {r e : ℕ} (hf : MFact.ord r e ∈ cert.facts) :
    (((X hJ r : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      CFSG.Sporadic.SmallF2.rowsMatrix 80 Rg[r]! := by
  rw [X, coe_φ]
  exact val_regUnit (spec2fr 80) (mcert_ok hJ) (C := cert.mcert) hf

theorem matrix_XW {w : Native.Word} (hw : HasOrd cert.mcert w) :
    (((XW hJ w : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      CFSG.Sporadic.SmallF2.rowsMatrix 80 (evalW (ops2fr 80) Rg w) := by
  rw [XW, coe_φ]
  exact val_wordUnit_eq (spec2fr 80) (mcert_ok hJ) hw

include hJ in
theorem wf_evalW {w : Native.Word} (hw : HasOrd cert.mcert w) :
    (spec2fr 80).WF (evalW (ops2fr 80) Rg w) :=
  (evalW_ok (spec2fr 80) (mcert_ok hJ) (wordLt_of_hasOrd (spec2fr 80) (mcert_ok hJ) hw)).1

include hJ in
theorem wf_reg {r e : ℕ} (hf : MFact.ord r e ∈ cert.facts) : (spec2fr 80).WF Rg[r]! :=
  (reg_ok (spec2fr 80) (mcert_ok hJ) (reg_pow (spec2fr 80) (mcert_ok hJ) (C := cert.mcert) hf).1).1

theorem XW_cons (r e : ℕ) (w : Native.Word) : XW hJ ((r, e) :: w) = X hJ r ^ e * XW hJ w := by
  rw [XW, wordUnit_cons, map_mul, map_pow]
  rfl

theorem XW_nil : XW hJ [] = 1 := by
  rw [XW, wordUnit_nil, map_one]

theorem XW_append (w₁ w₂ : Native.Word) : XW hJ (w₁ ++ w₂) = XW hJ w₁ * XW hJ w₂ := by
  rw [XW, wordUnit_append, map_mul]
  rfl

theorem ne_of_matNe {Y Z : Array ℕ} (hY : (spec2fr 80).WF Y) (hZ : (spec2fr 80).WF Z)
    (h : matNe Y Z = true) : (spec2fr 80).toMat Y ≠ (spec2fr 80).toMat Z := by
  intro he
  obtain ⟨t, -, ht⟩ := List.any_eq_true.1 h
  apply (spec2fr 80).toVec_ne ht
  rw [(spec2fr 80).toVec_vmul ((spec2fr 80).unit_wf t) hY,
    (spec2fr 80).toVec_vmul ((spec2fr 80).unit_wf t) hZ, he]

@[expose] def rbF (cert : J3Cert) : Fin 3 → ℕ := ![cert.rb.1, cert.rb.2.1, cert.rb.2.2]

@[expose] def rhF (cert : J3Cert) : Fin 3 → ℕ := ![cert.rh.1, cert.rh.2.1, cert.rh.2.2]

@[expose] noncomputable def xb (i : Fin 3) : J D := X hJ (rbF cert i)

@[expose] noncomputable def hb (k : Fin 3) : J D := X hJ (rhF cert k)

@[expose] def code (a : Fin 3 → ZMod 3) : ℕ := (a 0).val + 3 * (a 1).val + 9 * (a 2).val

theorem code_lt (a : Fin 3 → ZMod 3) : code a < 27 := by
  have h0 := (a 0).val_lt
  have h1 := (a 1).val_lt
  have h2 := (a 2).val_lt
  unfold code
  omega

theorem code_eq_zero {a : Fin 3 → ZMod 3} (h : code a = 0) : a = 0 := by
  unfold code at h
  funext i
  have h0 : (a 0).val = 0 := by omega
  have h1 : (a 1).val = 0 := by omega
  have h2 : (a 2).val = 0 := by omega
  fin_cases i
  · exact (ZMod.val_eq_zero _).1 h0
  · exact (ZMod.val_eq_zero _).1 h1
  · exact (ZMod.val_eq_zero _).1 h2

theorem basisW_code (a : Fin 3 → ZMod 3) :
    basisW cert.rb (code a) =
      [(cert.rb.1, (a 0).val), (cert.rb.2.1, (a 1).val), (cert.rb.2.2, (a 2).val)] := by
  have h0 := (a 0).val_lt
  have h1 := (a 1).val_lt
  have h2 := (a 2).val_lt
  have e0 : code a % 3 = (a 0).val := by unfold code; omega
  have e1 : code a / 3 % 3 = (a 1).val := by unfold code; omega
  have e2 : code a / 9 % 3 = (a 2).val := by unfold code; omega
  rw [basisW, e0, e1, e2]

theorem basisProd_eq (a : Fin 3 → ZMod 3) :
    basisProd (xb hJ) a = XW hJ (basisW cert.rb (code a)) := by
  rw [basisW_code, XW_cons, XW_cons, XW_cons, XW_nil, mul_one]
  simp [basisProd, List.ofFn_succ, xb, rbF]

include hJ in
theorem extra_parts :
    movedOK D.pts D.n cert.xs ((List.range 26).map fun k =>
        CFSG.Sporadic.SmallF2.Native.transposeRows 80
          (evalW (ops2fr 80) Rg (basisW cert.rb (k + 1)))) = true ∧
      colAct Rg[cert.rb.1]! D.pts[0]! = D.pts[0]! ∧
      (∀ k < 24, (ops2fr 80).vne (colAct (evalW (ops2fr 80) Rg (basisW cert.rb (k + 3))) D.pts[0]!)
        D.pts[0]! = true) ∧
      (∀ k < 26, matNe (evalW (ops2fr 80) Rg (basisW cert.rb (k + 1))) (ops2fr 80).one = true) ∧
      (∀ s ∈ cert.ss, colAct Rg[s.1]! D.pts[0]! = D.pts[0]!) ∧
      conjOK (cert.cs.map fun c => Rg[c]!).toArray
        ((cert.cs.map fun c => Rg[c]!).toArray.map fun Y => (ops2fr 80).pow Y 2) = true ∧
      (∀ k < 27, ∀ m < 8, matNe ((ops2fr 80).pow (evalW (ops2fr 80) Rg
        (basisW cert.rb k ++ hW cert.rh (m + 1))) 3) (ops2fr 80).one = true) ∧
      cert.ss.length = cert.cs.length := by
  have h := extra_ok hJ
  simp only [j3Extra, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun k hk m hm => h7 k hk m hm, h8⟩

variable (hrb : ∀ i, MFact.ord (rbF cert i) 3 ∈ cert.facts)
include hrb

theorem hasOrd_basisW (k : ℕ) : HasOrd cert.mcert (basisW cert.rb k) := by
  intro q hq
  simp only [basisW, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨3, hrb 0⟩
  · exact ⟨3, hrb 1⟩
  · exact ⟨3, hrb 2⟩

theorem matrix_basisProd (a : Fin 3 → ZMod 3) :
    (((basisProd (xb hJ) a : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      CFSG.Sporadic.SmallF2.rowsMatrix 80 (evalW (ops2fr 80) Rg (basisW cert.rb (code a))) := by
  rw [basisProd_eq]
  exact matrix_XW hJ (hasOrd_basisW hrb _)

theorem xb_pow (i : Fin 3) : xb hJ i ^ 3 = 1 := by
  rw [xb, X, ← map_pow, regUnit_pow (spec2fr 80) (mcert_ok hJ) (C := cert.mcert) (hrb i), map_one]

theorem basisProd_ne_one {a : Fin 3 → ZMod 3} (ha : a ≠ 0) : basisProd (xb hJ) a ≠ 1 := by
  intro h1
  have hk : 0 < code a := Nat.pos_of_ne_zero fun h => ha (code_eq_zero h)
  have hcheck := (extra_parts hJ).2.2.2.1 (code a - 1) (by have := code_lt a; omega)
  rw [show code a - 1 + 1 = code a by omega] at hcheck
  have hm := congrArg (fun g : J D => ((g : GL (Fin 80) (ZMod 2)) :
    Matrix (Fin 80) (Fin 80) (ZMod 2))) h1
  rw [matrix_basisProd hJ hrb, Subgroup.coe_one, Units.val_one] at hm
  apply ne_of_matNe (wf_evalW hJ (hasOrd_basisW hrb _)) (spec2fr 80).one_wf hcheck
  rw [(spec2fr 80).toMat_one]
  exact hm

theorem basisProd_smul_ne {a : Fin 3 → ZMod 3} (ha : a ≠ 0) {i : ℕ} (hi : i < D.n)
    (hxs : i ∉ cert.xs) : basisProd (xb hJ) a • P D i ≠ P D i := by
  have hk : 0 < code a := Nat.pos_of_ne_zero fun h => ha (code_eq_zero h)
  have h1 := (extra_parts hJ).1
  simp only [movedOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.mem_map] at h1
  rcases h1 i hi with h | h
  · exact absurd (by simpa using h) hxs
  · have hT := h _ ⟨code a - 1, by have := code_lt a; omega, rfl⟩
    rw [show code a - 1 + 1 = code a by omega] at hT
    rw [smul_P_eq (matrix_basisProd hJ hrb a), P, toVecD_eq]
    exact (spec2fr 80).toVec_ne hT

theorem xb_smul_root : xb hJ 0 • P D 0 = P D 0 := by
  have h0 : MFact.ord cert.rb.1 3 ∈ cert.facts := hrb 0
  have e := smul_P_eq (matrix_X hJ h0) 0
  rw [(extra_parts hJ).2.1] at e
  exact e

theorem basisProd_smul_root {a : Fin 3 → ZMod 3} (h : basisProd (xb hJ) a • P D 0 = P D 0) :
    a 1 = 0 ∧ a 2 = 0 := by
  by_contra hne
  have h3 : 3 ≤ code a := by
    unfold code
    have : (a 1).val ≠ 0 ∨ (a 2).val ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hne ⟨(ZMod.val_eq_zero _).1 h'.1, (ZMod.val_eq_zero _).1 h'.2⟩
    omega
  have hc := (extra_parts hJ).2.2.1 (code a - 3) (by have := code_lt a; omega)
  rw [show code a - 3 + 3 = code a by omega] at hc
  apply (spec2fr 80).toVec_ne hc
  have := h
  rw [smul_P_eq (matrix_basisProd hJ hrb a), P, toVecD_eq] at this
  exact this

theorem omega_ne (a : Fin 3 → ZMod 3) (i j : ℕ) (hi : i < 3) (hj : j < 3) (hij : i ≠ 0 ∨ j ≠ 0)
    (hrh : MFact.ord (rhF cert 0) 9 ∈ cert.facts ∧ MFact.ord (rhF cert 1) 9 ∈ cert.facts) :
    (basisProd (xb hJ) a * hb hJ 0 ^ i * hb hJ 1 ^ j) ^ 3 ≠ 1 := by
  have hm : i + 3 * j - 1 < 8 := by omega
  have hc := (extra_parts hJ).2.2.2.2.2.2.1 (code a) (code_lt a) _ hm
  rw [show i + 3 * j - 1 + 1 = i + 3 * j by omega] at hc
  have hw : hW cert.rh (i + 3 * j) = [(cert.rh.1, i), (cert.rh.2.1, j)] := by
    rw [hW, show (i + 3 * j) % 3 = i by omega, show (i + 3 * j) / 3 = j by omega]
  rw [hw] at hc
  have hord :
      HasOrd cert.mcert (basisW cert.rb (code a) ++ [(cert.rh.1, i), (cert.rh.2.1, j)]) := by
    refine hasOrd_append (hasOrd_basisW hrb _) ?_
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨9, hrh.1⟩
    · exact ⟨9, hrh.2⟩
  have heq : basisProd (xb hJ) a * hb hJ 0 ^ i * hb hJ 1 ^ j =
      XW hJ (basisW cert.rb (code a) ++ [(cert.rh.1, i), (cert.rh.2.1, j)]) := by
    rw [XW_append, XW_cons, XW_cons, XW_nil, basisProd_eq, mul_one, mul_assoc]
    rfl
  rw [heq]
  intro h1
  have hmat := congrArg (fun g : J D => ((g : GL (Fin 80) (ZMod 2)) :
    Matrix (Fin 80) (Fin 80) (ZMod 2))) h1
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one] at hmat
  rw [matrix_XW hJ hord] at hmat
  have hwf := wf_evalW hJ hord
  obtain ⟨hpw, hpm⟩ := (spec2fr 80).pow_spec hwf 3
  apply ne_of_matNe hpw (spec2fr 80).one_wf hc
  rw [hpm, (spec2fr 80).toMat_one]
  exact hmat

omit hrb in
theorem X_comm {r s e₁ e₂ : ℕ} (hr : MFact.ord r e₁ ∈ cert.facts) (hs : MFact.ord s e₂ ∈ cert.facts)
    (hf : MFact.eq [(r, 1), (s, 1)] [(s, 1), (r, 1)] ∈ cert.facts) : Commute (X hJ r) (X hJ s) := by
  have hw : ∀ q ∈ [(r, 1), (s, 1)], ∃ e, MFact.ord q.1 e ∈ cert.mcert.facts := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨e₁, hr⟩
    · exact ⟨e₂, hs⟩
  have hw' : ∀ q ∈ [(s, 1), (r, 1)], ∃ e, MFact.ord q.1 e ∈ cert.mcert.facts := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨e₂, hs⟩
    · exact ⟨e₁, hr⟩
  have h := regUnit_comm' (spec2fr 80) (mcert_ok hJ) (C := cert.mcert) hf hw hw'
  exact h.map φ

theorem X_conj {r e : ℕ} (hr : MFact.ord r e ∈ cert.facts) (j : Fin 3) (c : Fin 3 → ZMod 3)
    (hf : MFact.conj r [(rbF cert j, 1)]
      [(cert.rb.1, (c 0).val), (cert.rb.2.1, (c 1).val), (cert.rb.2.2, (c 2).val)] ∈ cert.facts) :
    X hJ r * xb hJ j * (X hJ r)⁻¹ = basisProd (xb hJ) c := by
  have h := regUnit_conj (spec2fr 80) (mcert_ok hJ) (C := cert.mcert) hf hr
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact ⟨3, hrb j⟩)
    (by
      have hw := hasOrd_basisW (cert := cert) hrb (code c)
      rw [basisW_code] at hw
      exact hw)
  rw [wordUnit_one] at h
  have := congrArg φ h
  rw [map_mul, map_mul, map_inv] at this
  rw [basisProd_eq, basisW_code]
  exact this

theorem basisProd_injective (hc : ∀ i j, Commute (xb hJ i) (xb hJ j)) :
    Function.Injective (basisProd (xb hJ)) := by
  have hx := xb_pow hJ hrb
  intro a b hab
  have h1 : basisHom hx hc (Multiplicative.ofAdd a) = basisHom hx hc (Multiplicative.ofAdd b) :=
    Subtype.ext (by rw [coe_basisHom, coe_basisHom]; exact hab)
  have h2 : basisHom hx hc (Multiplicative.ofAdd (a - b)) = 1 := by
    rw [ofAdd_sub, map_div, h1, div_self']
  have h3 : basisProd (xb hJ) (a - b) = 1 := by
    have := congrArg Subtype.val h2
    rwa [coe_basisHom, toAdd_ofAdd] at this
  by_contra hne
  exact basisProd_ne_one hJ hrb (sub_ne_zero.2 hne) h3

omit hrb in
theorem stabFacts_mem {k : ℕ} (hk : k < cert.ss.length) (hkc : k < cert.cs.length) :
    MFact.ord cert.ss[k].1 cert.ss[k].2 ∈ cert.facts ∧ MFact.ord cert.cs[k] 3 ∈ cert.facts ∧
      MFact.conj cert.ss[k].1 [(cert.rb.1, 1)] [(cert.cs[k], 1)] ∈ cert.facts := by
  have hz : (cert.ss[k], cert.cs[k]) ∈ cert.ss.zip cert.cs := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp [hk, hkc], by simp⟩
  have hsub : ∀ f ∈ stabFacts cert.rb.1 cert.ss[k] cert.cs[k], f ∈ cert.facts := fun f hf =>
    List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hz, hf⟩)
  exact ⟨hsub _ (by simp [stabFacts]), hsub _ (by simp [stabFacts]), hsub _ (by simp [stabFacts])⟩

omit hrb in
@[expose] noncomputable def sE (k : Fin cert.ss.length) : J D := X hJ cert.ss[k].1

omit hrb in
@[expose] noncomputable def cE (hlen : cert.ss.length = cert.cs.length) (k : Fin cert.ss.length) :
    J D :=
  X hJ (cert.cs.get ⟨k.val, hlen ▸ k.isLt⟩)

omit hrb in
theorem sE_smul_root (k : Fin cert.ss.length) (hlen : cert.ss.length = cert.cs.length) :
    sE hJ k • P D 0 = P D 0 := by
  have hf := (stabFacts_mem (cert := cert) k.isLt (hlen ▸ k.isLt)).1
  have e := smul_P_eq (matrix_X hJ hf) 0
  rw [(extra_parts hJ).2.2.2.2.1 _ (List.getElem_mem k.isLt)] at e
  exact e

theorem sE_conj (hlen : cert.ss.length = cert.cs.length) (k : Fin cert.ss.length) :
    sE hJ k * xb hJ 0 * (sE hJ k)⁻¹ = cE hJ hlen k := by
  obtain ⟨hs, hc, hconj⟩ := stabFacts_mem (cert := cert) k.isLt (hlen ▸ k.isLt)
  have h := regUnit_conj (spec2fr 80) (mcert_ok hJ) (C := cert.mcert) hconj hs
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact ⟨3, hrb 0⟩)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact ⟨3, hc⟩)
  rw [wordUnit_one, wordUnit_one] at h
  have := congrArg φ h
  rw [map_mul, map_mul, map_inv] at this
  exact this

omit hrb in
theorem cE_ne (hlen : cert.ss.length = cert.cs.length) {k l : Fin cert.ss.length} (hkl : k ≠ l) :
    cE hJ hlen k ≠ cE hJ hlen l ∧ cE hJ hlen k ≠ cE hJ hlen l ^ 2 := by
  have h6 := (extra_parts hJ).2.2.2.2.2.1
  simp only [conjOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, List.size_toArray, List.length_map] at h6
  have hk : k.val < cert.cs.length := hlen ▸ k.isLt
  have hl : l.val < cert.cs.length := hlen ▸ l.isLt
  rcases h6 k hk l hl with h | ⟨h1, h2⟩
  · exact absurd (Fin.ext h) hkl
  have e1 : ((cert.cs.map fun c => Rg[c]!).toArray)[k.val]! = Rg[cert.cs[k.val]]! := by
    rw [getElem!_pos _ _ (by simp [hk])]; simp
  have e2 : ((cert.cs.map fun c => Rg[c]!).toArray)[l.val]! = Rg[cert.cs[l.val]]! := by
    rw [getElem!_pos _ _ (by simp [hl])]; simp
  have e3 : (((cert.cs.map fun c => Rg[c]!).toArray).map fun Y => (ops2fr 80).pow Y 2)[l.val]! =
      (ops2fr 80).pow Rg[cert.cs[l.val]]! 2 := by
    rw [getElem!_pos _ _ (by simp [hl])]; simp
  rw [e1, e2] at h1
  rw [e1, e3] at h2
  obtain ⟨-, hck, -⟩ := stabFacts_mem (cert := cert) k.isLt hk
  obtain ⟨-, hcl, -⟩ := stabFacts_mem (cert := cert) l.isLt hl
  have hwk := wf_reg hJ hck
  have hwl := wf_reg hJ hcl
  constructor
  · intro he
    have hm := congrArg (fun g : J D => ((g : GL (Fin 80) (ZMod 2)) :
      Matrix (Fin 80) (Fin 80) (ZMod 2))) he
    simp only [cE, List.get_eq_getElem] at hm
    rw [matrix_X hJ hck, matrix_X hJ hcl] at hm
    exact ne_of_matNe hwk hwl h1 hm
  · intro he
    have hm := congrArg (fun g : J D => ((g : GL (Fin 80) (ZMod 2)) :
      Matrix (Fin 80) (Fin 80) (ZMod 2))) he
    simp only [cE, List.get_eq_getElem, Subgroup.coe_pow, Units.val_pow_eq_pow_val] at hm
    rw [matrix_X hJ hck, matrix_X hJ hcl] at hm
    obtain ⟨hpw, hpm⟩ := (spec2fr 80).pow_spec hwl 2
    apply ne_of_matNe hwk hpw h2
    rw [hpm]
    exact hm

end CFSG.RankThree.Asc83Table.J3
