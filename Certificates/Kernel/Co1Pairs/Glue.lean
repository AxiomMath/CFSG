module

public import Certificates.Kernel.Co1Pairs.Elts
public import Certificates.Kernel.Co1Pairs.Orb1
public import Certificates.Kernel.Co1Pairs.Orb2
public import Certificates.Kernel.Co1Pairs.Orb3
public import Certificates.Kernel.Co1Pairs.Three
public import Certificates.Kernel.Co1ThreeK.GlueMoore
public import CFSG.Certificates.Kernel.F2Set24Sound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Three
public import CFSG.Sporadic.Co1.Module.InvSpec
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pairs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.KS.SporSch.M24
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.KC.Co1Pairs CFSG.KD.Co1Pairs CertificateChecks.KernelCo1ThreeK
open CFSG.Sporadic.SmallF2 (toVecD)
open CFSG.Sporadic.SmallF2.Native (transposeRows)
open CertificateChecks.KernelSporSch.Co1Elem (AF aRows_eq)

theorem bAnd_eq {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem validRows_unpack24 (X : Nat) :
    CFSG.Sporadic.Co1.InvNative.validRows (unpack 24 24 X) = true := by
  rw [← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR X

theorem ne_one_of_neK {X : Nat} {g : GL24} (hX : MRep (unpack 24 24 X) g) (h : neK X = true) :
    g ≠ 1 := by
  rintro rfl
  have e : unpack 24 24 X = unpack 24 24 CFSG.KC.Co1B.oneK :=
    CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid (validRows_unpack24 X)
      (validRows_unpack24 _) (hX.trans (by rw [← one_unpack]; exact MRep.one.symm))
  have h2 := beq_unpackW X CFSG.KC.Co1B.oneK
  rw [e, beq_self_eq_true] at h2
  unfold neK at h
  rw [← h2] at h
  exact Bool.false_ne_true h

theorem order_of {X q : Nat} {g : ↥GA} (hq : q.Prime) (hX : MRep (unpack 24 24 X) (g : GL24))
    (hp : unpack 24 24 (CFSG.KC.Co1B.powWK X q) = one ()) (hn : neK X = true) : orderOf g = q := by
  have h1 : g ^ q = 1 := by
    have e := hX.pow q
    rw [pow_unpackW, hp] at e
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact e.eq MRep.one
  have h2 : g ≠ 1 := fun e => ne_one_of_neK hX hn (by rw [e]; rfl)
  haveI : Fact q.Prime := ⟨hq⟩
  exact orderOf_eq_prime h1 h2

section Facts

theorem elt_facts {w : List Nat} {X R q : Nat} {x : ↥GA} (hq : q.Prime)
    (hR : MRep (unpack 24 24 R) (x : GL24)) (h : eltOK L.M L.MI w X R q = true)
    (hn : neK X = true) :
    MRep (unpack 24 24 X) (Co1T.wG w : GL24) ∧ Co1T.wG w * x = x * Co1T.wG w ∧
      orderOf (Co1T.wG w) = q := by
  unfold eltOK at h
  obtain ⟨hl, h⟩ := bAnd_eq h
  obtain ⟨hw, h⟩ := bAnd_eq h
  obtain ⟨hc, h⟩ := bAnd_eq h
  obtain ⟨hp, -⟩ := bAnd_eq h
  have hrep : MRep (unpack 24 24 X) (Co1T.wG w : GL24) := by
    have e := Co1T.wordL_rep w
    rwa [wordL_eq hl, Nat.eq_of_beq_eq_true hw] at e
  refine ⟨hrep, ?_, order_of hq hrep (by rw [Nat.eq_of_beq_eq_true hp, MatL.unpack_idM]) hn⟩
  have e1 := hrep.mul hR
  have e2 := hR.mul hrep
  rw [mul_unpackW, Nat.eq_of_beq_eq_true hc, ← mul_unpackW] at e1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact e1.eq e2

end Facts

theorem eltR_unpack (gs e : List Nat) :
    _root_.Timmesfeld.Co1Leaf.eltR (gs.map (unpack 24 24)) e =
      unpack 24 24 (eltK gs e) := by
  unfold _root_.Timmesfeld.Co1Leaf.eltR eltK
  rw [List.zip_map_left, List.foldl_map, one_unpack]
  generalize CFSG.KC.Co1B.oneK = a
  induction (gs.zip e) generalizing a with
  | nil => rfl
  | cons ge l ih =>
    simp only [List.foldl_cons, Prod.map_fst, Prod.map_snd, id_eq]
    rw [pow_unpackW, mul_unpackW]
    exact ih _

theorem aGens_eq : Co1T.Native.aGens () = [AF 0, AF 1, AF 2, AF 3, AF 4, AF 5].map (unpack 24 24) := by
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  unfold Co1T.Native.aGens
  rw [aRows_eq, hr]
  simp only [List.map_cons, List.map_nil]

theorem rep_elt
    (e : List Nat) {R : Nat}
    (h : eltK [AF 0, AF 1, AF 2, AF 3, AF 4, AF 5] e = R) :
    MRep (unpack 24 24 R) (Co1T.eltG Co1T.aGA e : GL24) := by
  have r := Co1T.mrep_eltR Co1T.aGens_rep e
  rwa [aGens_eq, eltR_unpack, h] at r

theorem rep_root2 :
    MRep (unpack 24 24 (R.M 2)) (Co1T.root 2 : GL24) := by
  obtain ⟨h1, h2, -⟩ := rootK (j := 2) (by norm_num)
  have e := Co1T.wordL_rep (Co1T.Data.rootWords.getD 2 [])
  rwa [wordL_eq h1, Nat.eq_of_beq_eq_true h2] at e

theorem order_three {X : Nat} {g : ↥GA} (hX : MRep (unpack 24 24 X) (g : GL24))
    (h : threeK X = true) : orderOf g = 3 := by
  unfold threeK at h
  obtain ⟨hp, hn⟩ := bAnd_eq h
  have e := beq_unpackW (CFSG.KC.Co1B.powWK X 3) CFSG.KC.Co1B.oneK
  rw [hp, beq_iff_eq, ← one_unpack] at e
  exact order_of Nat.prime_three hX e hn

open scoped Matrix

theorem ncard_kOrbit_dvd (K : Subgroup GL24) (v : Vec24) : (kOrbit K v).ncard ∣ Nat.card K := by
  letI : MulAction ↥K Vec24 :=
    { smul := fun g v => ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v
      one_smul := fun v => by
        change (((1 : ↥K) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
        simp
      mul_smul := fun a b v => by
        change (((a * b : ↥K) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v =
          ((a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
            (((b : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)
        simp [Matrix.mulVec_mulVec] }
  have heq : kOrbit K v = MulAction.orbit ↥K v := by
    ext w
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  have horbstab : Nat.card (MulAction.orbit ↥K v) * Nat.card (MulAction.stabilizer ↥K v) =
      Nat.card ↥K := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥K v)
  rw [heq, ← Nat.card_coe_set_eq]
  exact Dvd.intro _ horbstab

theorem card_closure_pair (a b : ↥GA) :
    Nat.card (Subgroup.closure ({(a : GL24), (b : GL24)} : Set GL24)) =
      Nat.card (Subgroup.closure ({a, b} : Set ↥GA)) := by
  have e : ({(a : GL24), (b : GL24)} : Set GL24) = GA.subtype '' {a, b} := by
    rw [Set.image_pair]
    rfl
  rw [e, ← MonoidHom.map_closure, Subgroup.card_map_of_injective GA.subtype_injective]

theorem orbit_dvd {a b : ↥GA} {Xa Xb : Nat} {ca cb : List Nat} {oa ob : List (Nat × Nat)}
    {root n steps : Nat} (ra : MRep (unpack 24 24 Xa) (a : GL24))
    (rb : MRep (unpack 24 24 Xb) (b : GL24))
    (hca : ca.toArray = transposeRows 24 (unpack 24 24 Xa))
    (hcb : cb.toArray = transposeRows 24 (unpack 24 24 Xb))
    (h : CFSG.KC.F2Set24.orbOK ca cb oa ob root n steps = true) :
    n ∣ Nat.card (Subgroup.closure ({a, b} : Set ↥GA)) := by
  have hP : ActsBy (a : GL24) ca.toArray := by rw [hca]; exact MRep.actsBy ra
  have hQ : ActsBy (b : GL24) cb.toArray := by rw [hcb]; exact MRep.actsBy rb
  obtain ⟨hn, -⟩ := CFSG.KS.F2Set24.orbit_of_orbOK hP hQ h
  rw [← card_closure_pair, ← hn]
  exact ncard_kOrbit_dvd _ _

theorem c2_eq : c2.toArray = transposeRows 24 (unpack 24 24 K2) := by decide +kernel
theorem c3_eq : c3.toArray = transposeRows 24 (unpack 24 24 K3) := by decide +kernel
theorem c4_eq : c4.toArray = transposeRows 24 (unpack 24 24 K4) := by decide +kernel
theorem c5_eq : c5.toArray = transposeRows 24 (unpack 24 24 K5) := by decide +kernel
theorem c6_eq : c6.toArray = transposeRows 24 (unpack 24 24 K6) := by decide +kernel
theorem c7_eq : c7.toArray = transposeRows 24 (unpack 24 24 K7) := by decide +kernel

theorem prod_order {X Y d : Nat} {a b : ↥GA} (hd : d.Prime) (ra : MRep (unpack 24 24 X) (a : GL24))
    (rb : MRep (unpack 24 24 Y) (b : GL24)) (h : prodOK X Y d = true)
    (hn : neK (CFSG.KC.Co1B.mulWK X Y) = true) : orderOf (a * b) = d := by
  unfold prodOK at h
  rw [CFSG.KS.F2Set24.strict_eq] at h
  obtain ⟨hp, -⟩ := bAnd_eq h
  have r : MRep (unpack 24 24 (CFSG.KC.Co1B.mulWK X Y)) ((a * b : ↥GA) : GL24) := by
    rw [← mul_unpackW, Subgroup.coe_mul]
    exact ra.mul rb
  exact order_of hd r (by rw [Nat.eq_of_beq_eq_true hp, MatL.unpack_idM]) hn

theorem dvd_of_order {a b : ↥GA} {d : Nat} (h : orderOf (a * b) = d) :
    d ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA)) := by
  have hmem : a * b ∈ Subgroup.closure ({a, b} : Set ↥GA) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  rw [← h]
  exact Subgroup.orderOf_dvd_natCard _ hmem

theorem facts214033 :
    (orderOf (Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0]) = 3 ∧ ∃ a b : ↥GA,
      a * Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] * a ∧
      b * Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] * b ∧
      orderOf a = 7 ∧ orderOf b = 7 ∧
      13 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0]) = 3 ∧ ∃ a b : ↥GA,
      a * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] * a ∧
      b * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] * b ∧
      orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0]) = 3 ∧ ∃ a b : ↥GA,
      a * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * a ∧
      b * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * b ∧
      orderOf a = 5 ∧ orderOf b = 5 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.root 2) = 3 ∧ ∃ a b : ↥GA, a * Co1T.root 2 = Co1T.root 2 * a ∧
      b * Co1T.root 2 = Co1T.root 2 * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) := by
  have hr := ch214033r
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨e0, e1⟩, e2⟩ := hr
  have r0 := rep_elt [1, 0, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true e0)
  have r1 := rep_elt [0, 1, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true e1)
  have r2 := rep_elt [1, 1, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true e2)
  have r3 := rep_root2
  have ht := ch214033t
  simp only [Bool.and_eq_true] at ht
  obtain ⟨⟨⟨t0, t1⟩, t2⟩, t3⟩ := ht
  have hk := ch214033k
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, -⟩, -⟩, kp⟩ := hk
  have p7 : Nat.Prime 7 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  obtain ⟨q0, c0, o0⟩ := elt_facts p7 r0 ch214033e0 k0
  obtain ⟨q1, c1, o1⟩ := elt_facts p7 r0 ch214033e1 k1
  obtain ⟨q2, c2', o2⟩ := elt_facts p7 r1 ch214033e2 k2
  obtain ⟨q3, c3', o3⟩ := elt_facts p7 r1 ch214033e3 k3
  obtain ⟨q4, c4', o4⟩ := elt_facts p5 r2 ch214033e4 k4
  obtain ⟨q5, c5', o5⟩ := elt_facts p5 r2 ch214033e5 k5
  obtain ⟨q6, c6', o6⟩ := elt_facts p7 r3 ch214033e6 k6
  obtain ⟨q7, c7', o7⟩ := elt_facts p7 r3 ch214033e7 k7
  refine ⟨⟨order_three r0 t0, _, _, c0, c1, o0, o1,
      dvd_of_order (prod_order (by norm_num) q0 q1 ch214033p kp)⟩,
    ⟨order_three r1 t1, _, _, c2', c3', o2, o3,
      dvd_trans (by norm_num) (orbit_dvd q2 q3 c2_eq c3_eq ch214033o1)⟩,
    ⟨order_three r2 t2, _, _, c4', c5', o4, o5,
      dvd_trans (by norm_num) (orbit_dvd q4 q5 c4_eq c5_eq ch214033o2)⟩,
    ⟨order_three r3 t3, _, _, c6', c7', o6, o7,
      dvd_trans (by norm_num) (orbit_dvd q6 q7 c6_eq c7_eq ch214033o3)⟩⟩

end CertificateChecks.KernelCo1Pairs

end
