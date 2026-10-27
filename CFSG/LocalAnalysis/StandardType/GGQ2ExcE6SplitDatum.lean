module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
open Polynomial

noncomputable section

def MInt : Matrix (Fin 6) (Fin 4) ℤ :=
  !![2, 2, 0, 0;
     0, 2, 2, 2;
     2, 0, 2, 1;
     0, 0, 2, 2;
     2, 0, 2, 1;
     2, 2, 0, 0]

def AinvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 1, 0, 2;
     0, 2, 0, 1;
     2, 1, 1, 0;
     1, 2, 2, 2]

def M : Matrix (Fin 6) (Fin 4) (ZMod 3) := MInt.map (Int.cast)

def Ainv : Matrix (Fin 4) (Fin 4) (ZMod 3) := AinvInt.map (Int.cast)

def proj4 : (Fin 6 → ZMod 3) → (Fin 4 → ZMod 3) := fun y i => y (Fin.castLE (by decide) i)

def MA : Matrix (Fin 6) (Fin 4) (ZMod 3) := M * Ainv

theorem MA_apply (i : Fin 6) (j : Fin 4) :
    MA i j = if i = 0 then (if j = 0 then 1 else 0)
             else if i = 1 then (if j = 1 then 1 else 0)
             else if i = 2 then (if j = 2 then 1 else 0)
             else if i = 3 then (if j = 3 then 1 else 0)
             else if i = 4 then (if j = 2 then 1 else 0)
             else if j = 0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem Ainv_mulVec_M : ∀ v : ExcRaw.V 1, Ainv.mulVec (proj4 (M.mulVec v)) = v := by
  intro v
  ext i
  fin_cases i <;>
    simp [M, Ainv, MInt, AinvInt, proj4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    ring_nf <;>
    revert v <;>
    decide +kernel

theorem M_mulVec_Ainv (y : Fin 6 → ZMod 3)
    (hy : ∀ j : Fin 6, y j = y (TwistTag.E6.perm j)) :
    M.mulVec (Ainv.mulVec (proj4 y)) = y := by
  rw [Matrix.mulVec_mulVec]
  change MA.mulVec (proj4 y) = y
  ext j
  fin_cases j <;>
    simp only [Matrix.mulVec, MA_apply] <;>
    ring_nf <;>
    revert hy y <;>
    decide +kernel

theorem M_mulVec_sigma_invariant (v : ExcRaw.V 1) :
    ∀ j : Fin 6, (M.mulVec v) j = (M.mulVec v) (TwistTag.E6.perm j) := by
  intro j
  fin_cases j <;>
    simp [M, MInt, Matrix.mulVec, dotProduct, TwistTag.perm] <;>
    ring_nf <;>
    revert v <;>
    decide +kernel

theorem exists_root_sq_add_self_add_one (L : Type) [Field L] [IsAlgClosed L] :
    ∃ z : L, z ^ 2 + z + 1 = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L)
    (by
      have h : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).natDegree = 2 := by
        compute_degree!
      intro h0
      rw [Polynomial.degree_eq_natDegree (fun h1 => by simp [h1] at h), h] at h0
      exact absurd h0 (by decide))
  exact ⟨z, by simpa [Polynomial.IsRoot] using hz⟩

noncomputable def zeta (L : Type) [Field L] [IsAlgClosed L] (_h2 : (2 : L) = 0) : L :=
  (exists_root_sq_add_self_add_one L).choose

theorem zeta_spec (L : Type) [Field L] [IsAlgClosed L] (h2 : (2 : L) = 0) :
    (zeta L h2) ^ 2 + zeta L h2 + 1 = 0 :=
  (exists_root_sq_add_self_add_one L).choose_spec

noncomputable def zetaUnit (L : Type) [Field L] [IsAlgClosed L] (h2 : (2 : L) = 0) : Lˣ :=
  Units.mk0 (zeta L h2) (by
    have hz := zeta_spec L h2
    intro hz0
    rw [hz0] at hz
    simp at hz)

theorem zetaUnit_pow_three (L : Type) [Field L] [IsAlgClosed L] (h2 : (2 : L) = 0) :
    (zetaUnit L h2) ^ 3 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  have hz := zeta_spec L h2
  have h1 : ((zeta L h2) - 1) * ((zeta L h2) ^ 2 + zeta L h2 + 1) = (zeta L h2) ^ 3 - 1 := by ring
  rw [hz, mul_zero] at h1
  exact sub_eq_zero.mp h1.symm

theorem zetaUnit_ne_one (L : Type) [Field L] [IsAlgClosed L] (h2 : (2 : L) = 0) :
    (zetaUnit L h2) ≠ 1 := by
  intro h
  have hval : (zeta L h2 : L) = 1 := by
    have := congrArg Units.val h
    simpa [zetaUnit] using this
  have hz := zeta_spec L h2
  rw [hval] at hz
  have h3 : (3 : L) = 0 := by
    norm_num at hz
    exact hz
  have h31 : (3 : L) = 1 := by
    calc (3 : L) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [h2]
      _ = 1 := by simp
  rw [h31] at h3
  exact one_ne_zero h3

theorem M_spec (i : ExcRaw.Root 1) (k : Fin 4) :
    ∑ j : Fin 6, (e6SplitRoot i j : ZMod 3) * M j k = (ExcRaw.F 1 i k : ZMod 3) := by
  revert i k
  decide +kernel

theorem coroot_M_spec (i : ExcRaw.Root 1) (j : Fin 6) :
    (M.mulVec (ExcRaw.coroot 1 i)) j =
    (e6RelCorootPair (e6SplitRoot i) (Pi.single j 1) : ZMod 3) := by
  revert i j
  decide +kernel

def Mrank : Matrix (Fin Tag.E6.rank) (Fin 4) (ZMod 3) := M

private def corootVec (i : ExcRaw.Root 1) : Fin 4 → ZMod 3 := ExcRaw.coroot 1 i

private def e6perm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

private def Msigma (v : Fin 4 → ZMod 3) : Fin TwistTag.E6.tag.rank → ZMod 3 := Mrank.mulVec v

private def rootFin (i : ExcRaw.Root 1) (v : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ k, (ExcRaw.F 1 i k : ZMod 3) * v k

private theorem Msigma_sigma_invariant (v : Fin 4 → ZMod 3) :
    ∀ j : Fin TwistTag.E6.tag.rank, Msigma v j = Msigma v (TwistTag.E6.perm j) :=
  M_mulVec_sigma_invariant v

private theorem Mrank_spec (i : ExcRaw.Root 1) (k : Fin 4) :
    ∑ j : Fin Tag.E6.rank, (e6SplitRoot i j : ZMod 3) * Mrank j k = (ExcRaw.F 1 i k : ZMod 3) :=
  M_spec i k

private theorem Mrank_coroot_spec (i : ExcRaw.Root 1) (j : Fin Tag.E6.rank) :
    (Mrank.mulVec (corootVec i)) j =
      (e6RelCorootPair (e6SplitRoot i) (Pi.single j 1) : ZMod 3) :=
  coroot_M_spec i j

noncomputable def tMap {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (v : Fin 4 → ZMod 3) : ModGL .E6 L :=
  rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec v))

private theorem tMap_add {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (v w : Fin 4 → ZMod 3) : tMap (L := L) hζ (v + w) = tMap hζ v * tMap hζ w := by
  show rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ
      (Mrank.mulVec (v + w))) =
    rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec v)) *
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec w))
  rw [Matrix.mulVec_add, ExcFrames.zetaVec_add (τ := .E6) (p := 3), rootDiagUnit_mul]

private theorem tMap_zero {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    tMap (L := L) hζ (0 : Fin 4 → ZMod 3) = 1 := by
  show rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ
    (Mrank.mulVec (0 : Fin 4 → ZMod 3))) = 1
  rw [Matrix.mulVec_zero]
  have h : TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ
      (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
    funext i
    show ζ ^ ((0 : Fin Tag.E6.rank → ZMod 3) i).val = 1
    rw [Pi.zero_apply]
    simp
  rw [h, rootDiagUnit_one]

private theorem tMap_coroot {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (i : ExcRaw.Root 1) :
    (fun j : Fin Tag.E6.rank => ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) =
      TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec (corootVec i)) := by
  funext j
  show ζ ^ e6RelCorootPair (e6SplitRoot i) (Pi.single j 1) =
    ζ ^ ((Mrank.mulVec (corootVec i)) j).val
  rw [Mrank_coroot_spec i j]
  have h1 : CFSG.RankThree.CentralCover.zmodPowHom (p := 3) ζ hζ
      (Multiplicative.ofAdd (1 : ZMod 3)) = ζ := by
    rw [CFSG.RankThree.CentralCover.zmodPowHom_apply]
    have hone : ((1 : ZMod 3)).val = 1 := by decide
    rw [hone, pow_one]
  have hz := TableBExc.E6Three.zmodPowHom_zpow (p := 3) ζ hζ
    (e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) (1 : ZMod 3)
  rw [h1, mul_one, CFSG.RankThree.CentralCover.zmodPowHom_apply] at hz
  exact hz

theorem tMap_mem_fullThreeTorus {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (hS : E6SplitLangTwo S) {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (v : Fin 4 → ZMod 3) : tMap (L := L) hζ v ∈ fullThreeTorus S := by
  have hσ := Msigma_sigma_invariant v
  refine (rootDiagUnit_mem_fullThreeTorus_iff hS
    (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec v))).2 ⟨?_, ?_⟩
  · funext i
    show TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec v) i ^ 3 = 1
    rw [TableBExc.E6Three.zetaVec_apply (τ := .E6) (p := 3), ← pow_mul, Nat.mul_comm, pow_mul,
      hζ, one_pow]
  · intro j
    show ζ ^ (Msigma v (TwistTag.E6.perm j)).val = ζ ^ (Msigma v j).val
    rw [hσ j]

private theorem tMap_injective {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) : Function.Injective (tMap (L := L) hζ) := by
  intro v w hvw
  have h1 : TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec v) =
      TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ (Mrank.mulVec w) :=
    rootDiagUnit_injective hvw
  have h2 : Mrank.mulVec v = Mrank.mulVec w :=
    TableBExc.E6Three.zetaVec_injective (τ := .E6) (p := 3) hζo hζ h1
  have h3 := congrArg (fun y => Ainv.mulVec (proj4 y)) h2
  rw [show Ainv.mulVec (proj4 (Mrank.mulVec v)) = v from Ainv_mulVec_M v,
    show Ainv.mulVec (proj4 (Mrank.mulVec w)) = w from Ainv_mulVec_M w] at h3
  exact h3

private theorem tMap_surjective {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup .E6 L p) (hS : E6SplitLangTwo S) {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {t : ModGL .E6 L} (ht : t ∈ fullThreeTorus S) :
    ∃ v : Fin 4 → ZMod 3, tMap hζ v = t := by
  have htorus : t ∈ torusGroup .E6 L :=
    (inf_le_left : S.D.torus ≤ torusGroup .E6 L) ht.1
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htorus
  obtain ⟨hb3, hbσ⟩ := (rootDiagUnit_mem_fullThreeTorus_iff hS b).1 ht
  obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq (τ := .E6) (p := 3) hζo hζ hb3
  have hxσ : ∀ j : Fin Tag.E6.rank, x j = x (e6perm j) := by
    have hbσ' : ∀ j : Fin Tag.E6.rank, b (e6perm j) = b j := hbσ
    intro j
    have hy : TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ x =
        TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ
          (fun k : Fin Tag.E6.rank => x (e6perm k)) := by
      funext k
      have h : b (e6perm k) = b k := hbσ' k
      rw [← hx, TableBExc.E6Three.zetaVec_apply (τ := .E6) (p := 3),
        TableBExc.E6Three.zetaVec_apply (τ := .E6) (p := 3)] at h
      exact h.symm
    exact congrFun (TableBExc.E6Three.zetaVec_injective (τ := .E6) (p := 3) hζo hζ hy) j
  refine ⟨Ainv.mulVec (proj4 x), ?_⟩
  show rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) ζ hζ
    (Mrank.mulVec (Ainv.mulVec (proj4 x)))) = rootDiagUnit .E6 b
  rw [show Mrank.mulVec (Ainv.mulVec (proj4 x)) = x from M_mulVec_Ainv x hxσ, hx]

theorem e6SplitCoreDatum_holds : E6SplitCoreDatum := by
  intro L _ _ p S hS
  have h2 : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hS.1] at h
    simpa using h
  have hζ : zetaUnit L h2 ^ 3 = 1 := zetaUnit_pow_three L h2
  have hζo : orderOf (zetaUnit L h2) = 3 := orderOf_eq_prime hζ (zetaUnit_ne_one L h2)
  let F : (Fin 4 → ZMod 3) → Additive ↥(fullThreeTorus S) :=
    fun v => Additive.ofMul (⟨tMap hζ v, tMap_mem_fullThreeTorus S hS hζ v⟩ :
      ↥(fullThreeTorus S))
  have F_zero : F 0 = 0 := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    show tMap hζ (0 : Fin 4 → ZMod 3) = 1
    rw [tMap_zero]
  have F_add : ∀ v w : Fin 4 → ZMod 3, F (v + w) = F v + F w := by
    intro v w
    apply Additive.ofMul.injective
    apply Subtype.ext
    show tMap hζ (v + w) = tMap hζ v * tMap hζ w
    rw [tMap_add]
  let f : (Fin 4 → ZMod 3) →+ Additive ↥(fullThreeTorus S) :=
    { toFun := F, map_zero' := F_zero, map_add' := F_add }
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      have h1 : (⟨tMap hζ v, tMap_mem_fullThreeTorus S hS hζ v⟩ : ↥(fullThreeTorus S)) =
          ⟨tMap hζ w, tMap_mem_fullThreeTorus S hS hζ w⟩ := by
        apply Additive.ofMul.injective
        exact hvw
      exact tMap_injective hζo hζ (congrArg Subtype.val h1)
    · intro t
      obtain ⟨v, hv⟩ := tMap_surjective S hS hζo hζ (t := ((Additive.toMul t :
        ↥(fullThreeTorus S)) : ModGL .E6 L)) (Additive.toMul t).2
      refine ⟨v, ?_⟩
      apply Additive.ofMul.injective
      apply Subtype.ext
      show tMap hζ v = ((Additive.toMul t : ↥(fullThreeTorus S)) : ModGL .E6 L)
      rw [hv]
  let e : (Fin 4 → ZMod 3) ≃+ Additive ↥(fullThreeTorus S) := AddEquiv.ofBijective f hf
  have hcorootMem : ∀ i : ExcRaw.Root 1,
      rootDiagUnit .E6 (fun j : Fin Tag.E6.rank => zetaUnit L h2 ^
        e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)) ∈ fullThreeTorus S := by
    intro i
    rw [tMap_coroot hζ i]
    exact tMap_mem_fullThreeTorus S hS hζ (corootVec i)
  refine ⟨{ ζ := zetaUnit L h2
            coord := e.symm
            le_fullThreeTorus := le_rfl
            ζ_pow_three := hζ
            ζ_ne_one := zetaUnit_ne_one L h2
            rootChar_eq := ?_
            coroot_mem := hcorootMem
            coord_coroot := ?_ }⟩
  · intro t b hb i
    set v : Fin 4 → ZMod 3 := e.symm (Additive.ofMul t) with hv
    have hev : e v = Additive.ofMul t := e.apply_symm_apply _
    have h1 : (⟨tMap hζ v, tMap_mem_fullThreeTorus S hS hζ v⟩ : ↥(fullThreeTorus S)) = t := by
      apply Additive.ofMul.injective
      exact hev
    have htv : tMap hζ v = (t : ModGL .E6 L) := congrArg Subtype.val h1
    have hb' : TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) (zetaUnit L h2) hζ
        (Mrank.mulVec v) = b := by
      apply rootDiagUnit_injective
      change tMap hζ v = rootDiagUnit .E6 b
      rw [htv, hb]
    rw [← hb']
    show rootChar (TableBExc.E6Three.zetaVec (τ := .E6) (p := 3) (zetaUnit L h2) hζ
        (Mrank.mulVec v)) (e6SplitRoot i) = (zetaUnit L h2) ^ (rootFin i v).val
    rw [NoOffE8Five.rootChar_zetaVec (τ := .E6) (p := 3)]
    rw [CFSG.RankThree.CentralCover.zmodPowHom_apply]
    have hsum : (∑ j : Fin Tag.E6.rank, ((e6SplitRoot i) j : ZMod 3) * (Mrank.mulVec v) j) =
        rootFin i v := by
      calc (∑ j : Fin Tag.E6.rank, ((e6SplitRoot i) j : ZMod 3) * (Mrank.mulVec v) j)
          = ∑ j : Fin Tag.E6.rank, ∑ k : Fin 4,
              ((e6SplitRoot i) j : ZMod 3) * (Mrank j k * v k) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        _ = ∑ k : Fin 4, ∑ j : Fin Tag.E6.rank,
              ((e6SplitRoot i) j : ZMod 3) * (Mrank j k * v k) := Finset.sum_comm
        _ = rootFin i v := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show (∑ j : Fin Tag.E6.rank, ((e6SplitRoot i) j : ZMod 3) * (Mrank j k * v k)) =
                (∑ j : Fin Tag.E6.rank, ((e6SplitRoot i) j : ZMod 3) * Mrank j k) * v k from by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring]
            rw [Mrank_spec i k]
    rw [hsum]
  · intro i
    have h1 : e (corootVec i) = Additive.ofMul (⟨rootDiagUnit .E6
        (fun j : Fin Tag.E6.rank => zetaUnit L h2 ^
          e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)), hcorootMem i⟩ :
          ↥(fullThreeTorus S)) := by
      have h2 : (⟨tMap hζ (corootVec i),
          tMap_mem_fullThreeTorus S hS hζ (corootVec i)⟩ : ↥(fullThreeTorus S)) =
          ⟨rootDiagUnit .E6 (fun j : Fin Tag.E6.rank => zetaUnit L h2 ^
            e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)), hcorootMem i⟩ := by
        apply Subtype.ext
        change tMap hζ (corootVec i) = rootDiagUnit .E6
          (fun j : Fin Tag.E6.rank => zetaUnit L h2 ^
            e6RelCorootPair (e6SplitRoot i) (Pi.single j 1))
        rw [tMap_coroot hζ i]
        rfl
      rw [show e (corootVec i) = Additive.ofMul (⟨tMap hζ (corootVec i),
        tMap_mem_fullThreeTorus S hS hζ (corootVec i)⟩ : ↥(fullThreeTorus S)) from rfl, h2]
    calc e.symm (Additive.ofMul (⟨rootDiagUnit .E6
          (fun j : Fin Tag.E6.rank => zetaUnit L h2 ^
            e6RelCorootPair (e6SplitRoot i) (Pi.single j 1)), hcorootMem i⟩ :
          ↥(fullThreeTorus S)))
        = e.symm (e (corootVec i)) := by rw [h1]
      _ = corootVec i := e.symm_apply_apply _

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
