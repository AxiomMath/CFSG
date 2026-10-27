module

public import CFSG.Sporadic.Co2Smith.RigidLift

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u

namespace SmithConfig

variable (c : SmithConfig.{u})

theorem mA_piM_ι
    (g : S0) (e : c.E) : c.mA g (c.piM e) = c.piM (c.cE (c.ι g) e) :=
  c.mA_piM g e

theorem frame_vh_ι
    (k : ℕ) (hk : k < 9) (a : Fin 8) :
    ∃ σ : ZMod 2, c.cE (c.ι (frS k)) (c.vh a) = nf c.zE c.vh σ fun b => frameMat k b a :=
  c.frame_vh k hk a

theorem cE_cE (g h : S0) (e : c.E) :
    c.cE (c.ι g) (c.cE (c.ι h) e) = c.cE (c.ι (g * h)) e := by
  rw [map_mul, c.cE_mul]

theorem vhv_ι
    (e0 e1 e2 : Bool) : c.vhv e0 e1 e2 = c.cE (c.ι (yw e0 e1 e2)) c.wh := rfl

theorem y1_vhv_false
    (e1 e2 : Bool) :
    c.cE (c.ι (frS 0)) (c.vhv false e1 e2) = c.vhv true e1 e2 := by
  rw [vhv_ι, c.cE_cE, vhv_ι, yw, yw]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [mul_assoc]

theorem y1_vhv_true
    (e1 e2 : Bool) :
    c.cE (c.ι (frS 0)) (c.vhv true e1 e2) = c.vhv true e1 e2 * c.vhv false e1 e2 := by
  set A : S0 := if e1 then frS 2 else 1 with hAdef
  set B : S0 := if e2 then frS 4 else 1 with hBdef
  have hA : frS 0 * A = A * frS 0 := frS0_comm_ite 2 (Or.inl rfl) e1
  have hB : frS 0 * B = B * frS 0 := frS0_comm_ite 4 (Or.inr rfl) e2
  have hyw0 : yw false e1 e2 = A * B := by
    rw [yw]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rfl
  have hyw1 : yw true e1 e2 = frS 0 * (A * B) := by
    rw [yw]
    simp only [↓reduceIte, mul_assoc]
    rfl
  have hcomm : frS 0 * (A * B) = A * B * frS 0 := by
    rw [← mul_assoc, hA, mul_assoc, hB, ← mul_assoc]
  have e1' : frS 0 * (frS 0 * (A * B)) = A * B * frS 0 * frS 0 := by
    rw [hcomm, ← mul_assoc, hcomm]
  have hcy : c.cE (c.ι (frS 0)) (c.cE (c.ι (frS 0)) c.wh) =
      c.cE (c.ι (frS 0)) c.wh * c.wh := by
    have hn := c.norm_wh
    rw [LocalConfig.normY] at hn
    have h1 : c.cE (c.ι (frS 0)) (c.cE (c.ι (frS 0)) c.wh) =
        (c.wh * c.cE (c.ι (frS 0)) c.wh)⁻¹ := eq_inv_of_mul_eq_one_right hn
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right c.wh_sq]
    congr 1
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, c.wh_sq, map_one]
  rw [vhv_ι, vhv_ι, hyw0, hyw1]
  calc c.cE (c.ι (frS 0)) (c.cE (c.ι (frS 0 * (A * B))) c.wh)
      = c.cE (c.ι (A * B)) (c.cE (c.ι (frS 0)) (c.cE (c.ι (frS 0)) c.wh)) := by
        rw [c.cE_cE, c.cE_cE, c.cE_cE, e1']
    _ = c.cE (c.ι (A * B)) (c.cE (c.ι (frS 0)) c.wh * c.wh) := by rw [hcy]
    _ = c.cE (c.ι (frS 0 * (A * B))) c.wh * c.cE (c.ι (A * B)) c.wh := by
        rw [map_mul, c.cE_cE, ← hcomm]

end SmithConfig

end CFSG.Sporadic.Co2Smith
