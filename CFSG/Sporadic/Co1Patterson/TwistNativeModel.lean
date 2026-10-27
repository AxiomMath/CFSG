module

public import CFSG.Sporadic.Co1Patterson.TwistNativeTw
public import CFSG.Sporadic.Co1Patterson.TwistNativeCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

@[expose] def cword (c : ℕ) : List ℕ :=
  (List.range 6).flatMap fun i => if c.testBit i then uWords.getD i [] else []

theorem cword_lt (c : ℕ) : ∀ j ∈ cword c, j < 8 := by
  intro j hj
  obtain ⟨i, hi, hj⟩ := List.mem_flatMap.1 hj
  by_cases hb : c.testBit i
  · rw [ite_eq_left hb] at hj
    exact uWords_lt i (List.mem_range.1 hi) j hj
  · rw [ite_eq_right hb] at hj
    exact absurd hj List.not_mem_nil

theorem eichWord_append (l l' : List ℕ) : eichWord (l ++ l') = eichWord l * eichWord l' := by
  unfold eichWord
  rw [List.foldl_append]
  generalize l.foldl (fun acc j => acc * eichL j) 1 = a
  induction l' generalizing a with
  | nil => simp
  | cons j l' ih =>
    simp only [List.foldl_cons, one_mul]
    rw [ih, ih (eichL j), mul_assoc]

theorem eichWord_flatMap (l : List ℕ) (f : ℕ → List ℕ) (a : L₀) :
    a * eichWord (l.flatMap f) = l.foldl (fun acc i => acc * eichWord (f i)) a := by
  induction l generalizing a with
  | nil => simp [eichWord]
  | cons i l ih => rw [List.flatMap_cons, eichWord_append, ← mul_assoc, ih, List.foldl_cons]

theorem liftRoots_eq (k c : ℕ) :
    liftRoots k c = (cword c).flatMap fun j => omWords.getD (liftLetter k j) [] := by
  rw [liftRoots, cword, List.flatMap_assoc]
  congr 1
  funext i
  split_ifs <;> simp

theorem phi_hcH_eq_eichWord (c : ℕ) : typeSystemC.φ (hcH c) = eichWord (cword c) := by
  rw [phi_hcH, ← one_mul (eichWord (cword c)), cword, eichWord_flatMap]
  refine List.foldl_ext _ _ _ fun b i _ => ?_
  by_cases hb : c.testBit i
  · rw [ite_eq_left hb, ite_eq_left hb]
  · rw [ite_eq_right hb, ite_eq_right hb]
    simp [eichWord]

theorem vec_z_ne_vec_yH : typeSystemC.vec typeSystemC.z ≠ typeSystemC.vec (yH 0) := by
  rw [typeSystemC.vec_z, vec_yH_zero]
  intro h
  exact absurd (bv_inj (by norm_num) (by norm_num) (h.symm.trans bv_zero.symm)) (by norm_num)

theorem vec_one_ne_vec_yH :
    typeSystemC.vec (1 : centralizer ({aNC} : Set NativeSporadic.Co1)) ≠
      typeSystemC.vec (yH 0) := by
  rw [ExtraspecialTypeSystem.vec_one, vec_yH_zero]
  intro h
  exact absurd (bv_inj (by norm_num) (by norm_num) (h.symm.trans bv_zero.symm)) (by norm_num)

theorem yH_zero_sq : yH 0 * yH 0 = 1 := by
  apply centEmb_injective
  rw [map_mul, centEmb_yH, map_one, ← yprodG_two_pow (show 0 < 8 by norm_num), pow_zero]
  exact (yprodG_sq_eq_one_iff (by norm_num)).2 rfl

section WPlus

theorem zPlus_comm (e : wPlus) : zPlus * e = e * zPlus :=
  (mem_center_iff.1 zPlus_mem_center e).symm

theorem zPlus_mul_self :
    zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self

variable (k : Fin 3)

noncomputable abbrev TM : Type := twistModel typeSystemC iotaC k

noncomputable abbrev FP : Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1) × wPlus) :=
  fibreProd typeSystemC.φ (wPlusMap iotaC k)

noncomputable abbrev tw (g : FP k) : TM k := QuotientGroup.mk g

theorem tw_eq_tw_iff {g g' : FP k} : tw k g = tw k g' ↔ g' = g ∨
    g' = g * zζ typeSystemC (wPlusMap iotaC k) zPlus (wPlusMap_zPlus iotaC k) :=
  mk_eq_mk_iff_twist typeSystemC (wPlusMap_zPlus iotaC k) zPlus_comm zPlus_mul_self

@[expose] noncomputable def eHat (c : ℕ) : wPlus := liftWord k (cword c)

theorem πk_eHat (c : ℕ) : wPlusMap iotaC k (eHat k c) = typeSystemC.φ (hcH c) := by
  rw [eHat, wPlusMap_liftWord k _ (cword_lt c), phi_hcH_eq_eichWord]

@[expose] noncomputable def Ψ (c : ℕ) (p : ℕ × ℕ) : TM k :=
  tw k ⟨(hcH c * aElt p, eHat k c), by
    rw [mem_fibreProd, map_mul, phi_aElt, mul_one, πk_eHat]⟩

@[expose] noncomputable def zT : TM k := twZ typeSystemC (wPlusMap_zPlus iotaC k)

@[expose] noncomputable def wFib : FP k :=
  ⟨(yH 0, 1), by rw [mem_fibreProd, phi_yH_zero, map_one]⟩

@[expose] noncomputable def wT : TM k := tw k (wFib k)

theorem zT_mem_center : zT k ∈ center (TM k) := twZ_mem_center _ _

theorem zT_ne_one : zT k ≠ 1 :=
  twZ_ne_one _ _ zPlus_comm zPlus_mul_self zPlus_ne_one

theorem wT_mem_ker : wT k ∈ (twPhi typeSystemC (wPlusMap_zPlus iotaC k)).ker := by
  rw [MonoidHom.mem_ker, wT, twPhi_mk]
  exact phi_yH_zero

theorem isPGroup_ker_twPhiT :
    IsPGroup 2 (twPhi typeSystemC (wPlusMap_zPlus iotaC k)).ker :=
  isPGroup_ker_twPhi _ _ (fun _ he => (wPlusMap_eq_one_iff iotaC k).1 he) zPlus_mul_self

theorem fst_z1Fib : (z1Fib typeSystemC : FP k).val.1 = typeSystemC.z := rfl

theorem snd_z1Fib : (z1Fib typeSystemC : FP k).val.2 = 1 := rfl

theorem fst_wFib : (wFib k : FP k).val.1 = yH 0 := rfl

theorem snd_wFib : (wFib k : FP k).val.2 = 1 := rfl

theorem snd_zζ : (zζ typeSystemC (wPlusMap iotaC k) zPlus (wPlusMap_zPlus iotaC k) :
    FP k).val.2 = zPlus := rfl

theorem wT_ne_zT : wT k ≠ zT k := by
  intro h
  rw [wT, zT, twZ, tw_eq_tw_iff] at h
  rcases h with h | h
  · have h1 : (z1Fib typeSystemC : FP k).val.1 = (wFib k : FP k).val.1 := by rw [h]
    rw [fst_z1Fib, fst_wFib] at h1
    exact vec_z_ne_vec_yH (congrArg typeSystemC.vec h1)
  · have h1 : (z1Fib typeSystemC : FP k).val.2 = (wFib k * zζ typeSystemC
        (wPlusMap iotaC k) zPlus (wPlusMap_zPlus iotaC k) : FP k).val.2 := by rw [h]
    rw [Subgroup.coe_mul, Prod.snd_mul, snd_z1Fib, snd_wFib, snd_zζ, one_mul] at h1
    exact zPlus_ne_one h1.symm

theorem orderOf_wT : orderOf (wT k) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · have hsq : wFib k * wFib k = 1 := Subtype.ext (Prod.ext yH_zero_sq (one_mul _))
    rw [wT, sq, ← QuotientGroup.mk_mul, hsq, QuotientGroup.mk_one]
  · rw [wT, ← QuotientGroup.mk_one, tw_eq_tw_iff] at h
    rcases h with h | h
    · have h1 : (1 : FP k).val.1 = (wFib k : FP k).val.1 := by rw [h]
      rw [fst_wFib] at h1
      exact vec_one_ne_vec_yH (congrArg typeSystemC.vec h1)
    · have h1 : (1 : FP k).val.2 = (wFib k * zζ typeSystemC
          (wPlusMap iotaC k) zPlus (wPlusMap_zPlus iotaC k) : FP k).val.2 := by rw [h]
      rw [Subgroup.coe_mul, Prod.snd_mul, snd_wFib, snd_zζ, one_mul] at h1
      exact zPlus_ne_one h1.symm

end WPlus

end CFSG.Sporadic.Co1Patterson.TwistNative
