module

public import Certificates.Data.Kernel.U43Case
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KC.U43Case

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def commPt (n w a b : Nat) : Bool :=
  allN n fun i => Nat.beq (pg w (mask w) a (pg w (mask w) b i)) (pg w (mask w) b (pg w (mask w) a i))

@[expose] noncomputable def invPt (n w k : Nat) : Bool :=
  allN n fun i => Nat.beq (pg w (mask w) k (pg w (mask w) k i)) i

@[expose] noncomputable def ord3Pt (n w x : Nat) : Bool :=
  andB (allN n fun i => Nat.beq (pg w (mask w) x (pg w (mask w) x (pg w (mask w) x i))) i)
    (notB (allN n fun i => Nat.beq (pg w (mask w) x i) i))

@[expose] noncomputable def candQ (n w t y c : Nat) : Bool :=
  ord3Pt n w c && commPt n w c (cpP n w t c) && commPt n w y (cpP n w t c) &&
    relFreeP n w y c (cpP n w t c)

@[expose] noncomputable def kQ (n w t c k : Nat) : Bool :=
  (invPt n w k && !Nat.beq k (pidn n w)) && commPt n w k (cpP n w t c) &&
    commPt n w k (cpP n w t k) && Nat.beq (pp n w (pp n w (pp n w k c) k) c) (pidn n w)

@[expose] noncomputable def cent5Q (n w t N : Nat) (Y : Nat → Nat) (c k : Nat) : Nat :=
  ((List.range N).filter fun i => commPt n w (Y i) c && commPt n w (Y i) (cpP n w t c) &&
    commPt n w (Y i) k && commPt n w (Y i) (cpP n w t k)).length

theorem allN_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allN n f = allN n g := by
  apply Bool.eq_iff_iff.mpr
  rw [CFSG.KS.PK.allN_iff, CFSG.KS.PK.allN_iff]
  exact ⟨fun H i hi => (h i hi) ▸ H i hi, fun H i hi => (h i hi).symm ▸ H i hi⟩

theorem beq_fields {n w X Y : Nat} (hw : 0 < w) (hX : X >>> (n * w) = 0)
    (hY : Y >>> (n * w) = 0) :
    Nat.beq X Y = allN n fun i => Nat.beq (pg w (mask w) X i) (pg w (mask w) Y i) := by
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq, CFSG.KS.PK.allN_iff]
  constructor
  · rintro rfl i _
    exact Nat.beq_refl _
  · intro h
    exact eq_of_fields hw hX hY fun i hi => Nat.eq_of_beq_eq_true (h i hi)

theorem commP_eq_pt {n w : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (a b : Nat) :
    commP n w a b = commPt n w a b := by
  unfold commP pp commPt
  rw [beq_fields hw (pcomp_shr a b hn hw) (pcomp_shr b a hn hw)]
  exact allN_congr fun i hi => by rw [pg_pcomp hn hi, pg_pcomp hn hi]

theorem inv_eq_pt {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (k : Nat) :
    Nat.beq (pp n w k k) (pidn n w) = invPt n w k := by
  have hn' : n < 2 ^ 32 := by omega
  unfold pp invPt
  rw [beq_fields (w_pos hw) (pcomp_shr k k hn' (w_pos hw)) (pidn_shr hn hw)]
  exact allN_congr fun i hi => by rw [pg_pcomp hn' hi, pg_pidn hn hw hi]

theorem ord3P_eq_pt {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (x : Nat) :
    ord3P n w x = ord3Pt n w x := by
  have hn' : n < 2 ^ 32 := by omega
  have e3 : ppw n w x 3 = pcomp n w (mask w) x (pcomp n w (mask w) x
      (pcomp n w (mask w) x (pidn n w))) := rfl
  have e1 : ppw n w x 1 = pcomp n w (mask w) x (pidn n w) := rfl
  unfold ord3P ord3Pt
  rw [e3, e1, beq_fields (w_pos hw) (pcomp_shr _ _ hn' (w_pos hw)) (pidn_shr hn hw),
    beq_fields (w_pos hw) (pcomp_shr _ _ hn' (w_pos hw)) (pidn_shr hn hw)]
  congr 1
  · exact allN_congr fun i hi => by
      rw [pg_pcomp hn' hi, pg_pcomp hn' hi, pg_pcomp hn' hi, pg_pidn hn hw hi]
  · exact congrArg notB (allN_congr fun i hi => by rw [pg_pcomp hn' hi, pg_pidn hn hw hi])

theorem candQ_eq {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (t y c : Nat) :
    candQ n w t y c = candP n w t y c := by
  unfold candQ candP
  simp only [ord3P_eq_pt hn hw, commP_eq_pt (by omega : n < 2 ^ 32) (w_pos hw)]

theorem kQ_eq {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (t c k : Nat) :
    kQ n w t c k = kP n w t c k := by
  unfold kQ kP
  simp only [inv_eq_pt hn hw, commP_eq_pt (by omega : n < 2 ^ 32) (w_pos hw)]

theorem cent5Q_eq {n w : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (t N : Nat) (Y : Nat → Nat)
    (c k : Nat) : cent5Q n w t N Y c k = cent5P n w t N Y c k := by
  unfold cent5Q cent5P
  simp only [commP_eq_pt hn hw]

end CFSG.KC.U43Case

end
