module

public import CFSG.Sporadic.Schreier.J4SLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def φ : J →* Matrix (Fin 112) (Fin 112) (ZMod 2) := (Units.coeHom _).comp J.subtype

theorem φ_apply (g : J) :
    φ g = ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  rfl

theorem φ_injective : Function.Injective φ := fun _ _ e => Subtype.ext (Units.ext e)

abbrev O : Ops (Array ℕ) ℕ := ops2fr 112

abbrev Sp : OpsSpec O 2 112 := spec2fr 112

abbrev Pair : Type := Array ℕ × Array ℕ

@[expose] def mulP (P Q : Pair) : Pair := (O.mul P.1 Q.1, O.mul Q.2 P.2)

@[expose] def invP (P : Pair) : Pair := (P.2, P.1)

@[expose] def powP (P : Pair) (e : ℕ) : Pair := (O.pow P.1 e, O.pow P.2 e)

@[expose] def oneP : Pair := (O.one, O.one)

@[expose] def letterP (P Q : Pair) (l : ℤ) : Pair :=
  if l = 1 then P else if l = -1 then invP P else if l = 2 then Q else if l = -2 then invP Q
  else oneP

@[expose] def wordP (P Q : Pair) : List ℤ → Pair
  | [] => oneP
  | l :: w => mulP (letterP P Q l) (wordP P Q w)

@[expose] def prodP : List Pair → Pair
  | [] => oneP
  | P :: L => mulP P (prodP L)

section Rep

variable {g h : J} {P Q : Pair}

theorem rep_mulP (hg : Rep Sp φ g P) (hh : Rep Sp φ h Q) : Rep Sp φ (g * h) (mulP P Q) :=
  hg.mul hh

theorem rep_invP (hg : Rep Sp φ g P) : Rep Sp φ g⁻¹ (invP P) := hg.inv

theorem rep_powP (hg : Rep Sp φ g P) (e : ℕ) : Rep Sp φ (g ^ e) (powP P e) := hg.pow e

theorem rep_oneP : Rep Sp φ 1 oneP := Rep.one

theorem rep_letterP (hg : Rep Sp φ g P) (hh : Rep Sp φ h Q) (l : ℤ) :
    Rep Sp φ (letter g h l) (letterP P Q l) := by
  unfold letter letterP
  split_ifs
  · exact hg
  · exact rep_invP hg
  · exact hh
  · exact rep_invP hh
  · exact rep_oneP

theorem rep_wordP (hg : Rep Sp φ g P) (hh : Rep Sp φ h Q) :
    ∀ w : List ℤ, Rep Sp φ (signedWord g h w) (wordP P Q w)
  | [] => by
    rw [signedWord, List.map_nil, List.prod_nil]
    exact rep_oneP
  | l :: w => by
    rw [signedWord, List.map_cons, List.prod_cons]
    exact rep_mulP (rep_letterP hg hh l) (rep_wordP hg hh w)

theorem rep_prodP : ∀ {L : List J} {M : List Pair}, List.Forall₂ (Rep Sp φ) L M →
    Rep Sp φ L.prod (prodP M)
  | [], [], _ => by rw [List.prod_nil]; exact rep_oneP
  | _ :: _, _ :: _, List.Forall₂.cons h hL => by
    rw [List.prod_cons]
    exact rep_mulP h (rep_prodP hL)

end Rep

abbrev An : Pair :=
  (O.decode Blueprint.NativeSporadic.J4Seed1, O.decode Blueprint.NativeSporadic.J4Seed1)

abbrev Bn : Pair :=
  (O.decode Blueprint.NativeSporadic.J4Seed2, O.pow (O.decode Blueprint.NativeSporadic.J4Seed2) 3)

@[expose] def regsN : Array Pair := runProgN O (initRegsN O 9 An Bn) typeIIProg

@[expose] def Xn : Pair := regsN[1]!

@[expose] def Yn : Pair := regsN[2]!

@[expose] def Tn : Pair := regsN[3]!

@[expose] def Dn : Pair := mulP (mulP (powP (mulP Yn Xn) 4) (invP Yn)) Xn

@[expose] def Zn : Pair := powP (mulP (mulP (mulP Yn (invP Dn)) Tn) Dn) 3

@[expose] def Cn (j : Fin 11) : Pair := wordP Xn Yn (normalConjugators j)

@[expose] def Un (j : Fin 11) : Pair := mulP (mulP (invP (Cn j)) Zn) (Cn j)

@[expose] def etaP (i : ℕ) : Pair :=
  prodP (List.ofFn fun j : Fin 11 => if i.testBit j then Un j else oneP)

section Facts

variable (hM : MatFacts)
include hM

theorem a_mul_self' : (a : J) * a = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, a_coe, gA_val hM, ← pow_two, matA_sq hM]
  rfl

theorem b_pow_four' : (b : J) ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, b_coe, gB_val hM, matB_pow_four hM]
  rfl

theorem a_inv' : (a : J)⁻¹ = a := inv_eq_of_mul_eq_one_right (a_mul_self' hM)

theorem b_inv' : (b : J)⁻¹ = b ^ 3 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', b_pow_four' hM])

theorem toMat_seedA : Sp.toMat (O.decode Blueprint.NativeSporadic.J4Seed1) = φ a := by
  rw [Sp.toMat_decode, φ_apply, a_coe, gA_val hM]

theorem toMat_seedA_inv : Sp.toMat (O.decode Blueprint.NativeSporadic.J4Seed1) = φ a⁻¹ := by
  rw [a_inv' hM]
  exact toMat_seedA hM

theorem toMat_seedB : Sp.toMat (O.decode Blueprint.NativeSporadic.J4Seed2) = φ b := by
  rw [Sp.toMat_decode, φ_apply, b_coe, gB_val hM]

theorem toMat_seedB_inv :
    Sp.toMat (O.pow (O.decode Blueprint.NativeSporadic.J4Seed2) 3) = φ b⁻¹ := by
  rw [(Sp.pow_spec (Sp.decode_wf Blueprint.NativeSporadic.J4Seed2) 3).2, toMat_seedB hM,
    b_inv' hM, map_pow]

theorem rep_a : Rep Sp φ a An :=
  ⟨Sp.decode_wf Blueprint.NativeSporadic.J4Seed1, Sp.decode_wf Blueprint.NativeSporadic.J4Seed1,
    toMat_seedA hM, toMat_seedA_inv hM⟩

theorem rep_b : Rep Sp φ b Bn :=
  ⟨Sp.decode_wf Blueprint.NativeSporadic.J4Seed2,
    (Sp.pow_spec (Sp.decode_wf Blueprint.NativeSporadic.J4Seed2) 3).1, toMat_seedB hM,
    toMat_seedB_inv hM⟩

omit hM in
theorem typeIIProg_lt : typeIIProg.all (Instr.lt 9) = true := by decide

theorem regsRep : RegsRep Sp φ 9 regs regsN :=
  regsRep_runProg typeIIProg typeIIProg_lt (regsRep_initRegs (rep_a hM) (rep_b hM))

theorem rep_x : Rep Sp φ x Xn := (regsRep hM).2 1 (by norm_num)

theorem rep_y : Rep Sp φ y Yn := (regsRep hM).2 2 (by norm_num)

theorem rep_t : Rep Sp φ t Tn := (regsRep hM).2 3 (by norm_num)

theorem rep_d : Rep Sp φ d Dn :=
  rep_mulP (rep_mulP (rep_powP (rep_mulP (rep_y hM) (rep_x hM)) 4) (rep_invP (rep_y hM)))
    (rep_x hM)

theorem rep_z : Rep Sp φ z Zn :=
  rep_powP (rep_mulP (rep_mulP (rep_mulP (rep_y hM) (rep_invP (rep_d hM))) (rep_t hM))
    (rep_d hM)) 3

theorem rep_c (j : Fin 11) : Rep Sp φ (c j) (Cn j) := rep_wordP (rep_x hM) (rep_y hM) _

theorem rep_u (j : Fin 11) : Rep Sp φ (u j) (Un j) :=
  rep_mulP (rep_mulP (rep_invP (rep_c hM j)) (rep_z hM)) (rep_c hM j)

theorem rep_etaP (i : ℕ) : Rep Sp φ (η i) (etaP i) := by
  refine rep_prodP ?_
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun k h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  split_ifs
  · exact rep_u hM _
  · exact rep_oneP

omit hM in
theorem eq_of_rep {g h : J} {P Q : Pair} (hg : Rep Sp φ g P) (hh : Rep Sp φ h Q)
    (e : O.eq P.1 Q.1 = true) : g = h :=
  φ_injective (by rw [← hg.2.2.1, ← hh.2.2.1]; exact Sp.toMat_eq hg.1 hh.1 e)

end Facts

@[expose] def rootCheck : Bool :=
  O.vmul rootBits Xn.1 == rootBits && O.vmul rootBits Yn.1 == rootBits &&
    O.vmul rootBits Zn.1 == rootBits

@[expose] def colsCheck : Bool :=
  (List.finRange 11).all fun j =>
    O.eq (mulP (mulP Xn (Un j)) (invP Xn)).1 (etaP xColumns[j]!).1 &&
      O.eq (mulP (mulP Yn (Un j)) (invP Yn)).1 (etaP yColumns[j]!).1

@[expose] def elemCheck : Bool := elem2OK O (List.ofFn fun j => (Un j).1) [0]

end CFSG.Sporadic.J4Schreier
