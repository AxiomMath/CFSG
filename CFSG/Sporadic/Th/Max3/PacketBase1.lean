
module

public import CFSG.Sporadic.Th.Max3.PacketBase
import all CFSG.Sporadic.Th.Max3.PacketBase

public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.PacketInputs
public meta import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.Th.Max3.RelationsBase1

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.Certificates

namespace Packet

@[expose] noncomputable def initRegs :
    ℕ → J := fun i => if i = 1 then a else if i = 2 then b else 1

@[expose] noncomputable def Instr.exec : Instr → (ℕ → J) → (ℕ → J)
  | .mu i j k, R => Function.update R k (R i * R j)
  | .iv i k, R => Function.update R k (R i)⁻¹
  | .pwr e i k, R => Function.update R k (R i ^ e)

@[expose] noncomputable def run (p : List Instr) : ℕ → J :=
  p.foldl (fun R ins => ins.exec R) initRegs

theorem program_x : run program 1 = x := rfl

theorem program_y : run program 2 = y := rfl

@[expose] noncomputable def signedLetter (l : ℤ) : J :=
  if l = 1 then x else if l = -1 then x⁻¹ else if l = 2 then y else if l = -2 then y⁻¹ else 1

end Packet

@[expose] noncomputable def signedWordProd
    (w : List ℤ) : J := (w.map Packet.signedLetter).prod

@[expose] noncomputable def zP : J := signedWordProd Packet.coreZWord

@[expose] noncomputable def qP
    (i : Fin 8) : J := signedWordProd (Packet.coreGeneratorWords i)

namespace Packet

end Packet

namespace Packet

theorem pow_mul_of_comm
    {a b : J} (h : a * b = b * a) : ∀ n : ℕ, a ^ n * b = b * a ^ n
  | 0 => by rw [pow_zero, one_mul, mul_one]
  | n + 1 => by rw [pow_succ, mul_assoc, h, ← mul_assoc, pow_mul_of_comm h n, mul_assoc]

end Packet

namespace Packet

@[expose] noncomputable def E (e : Fin 9 → ZMod 2) : J :=
  zP ^ (e 0).val * (List.ofFn fun i : Fin 8 => qP i ^ (e i.succ).val).prod

end Packet

@[expose] noncomputable def EP
    (k : Fin 512) : J := Packet.E (Packet.bits k)

theorem EP_eq_nf (k : Fin 512) :
    EP k = ExtraspecialNF.nf zP qP (Packet.bits k 0) (fun i => Packet.bits k i.succ) := rfl

namespace Packet

private theorem z_mul_list_prod :
    ∀ l : List J, (∀ b ∈ l, z * b = b * z) →
    z * l.prod = l.prod * z
  | [], _ => by simp
  | b :: l, h => by
    rw [List.prod_cons, ← mul_assoc, h b (List.mem_cons_self ..), mul_assoc,
      z_mul_list_prod l fun b' hb' => h b' (List.mem_cons_of_mem _ hb'), mul_assoc]

end Packet

@[expose] noncomputable def repP (v : Fin 8 → ZMod 2) : J :=
  (List.ofFn fun i => qP i ^ (v i).val).prod

end CFSG.Sporadic.Th.Max3
