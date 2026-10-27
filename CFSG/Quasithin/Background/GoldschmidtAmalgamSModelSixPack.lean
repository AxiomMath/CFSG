module

public import CFSG.Permutation.FinPackInv

public section

namespace CFSG.Quasithin.F6.GoldAmS.Pack

open Equiv Finset CFSG.Permutation.FinPack

theorem h6 : (6 : ℕ) ≤ 16 := by norm_num

@[expose] def oneS : ℕ := 5517840

theorem enc_oneS : enc (1 : Perm (Fin 6)) = oneS := by decide +kernel

@[expose] noncomputable def gK (x c : ℕ) : Bool := Nat.beq (mulK 6 c x) (mulK 6 x c)

theorem cent_iff {g e : Perm (Fin 6)} {x : ℕ} (hx : enc e = x) :
    g * e = e * g ↔ gK x (enc g) = true := by
  rw [gK, ← hx, ← enc_mul h6, ← enc_mul h6, beq_enc_iff h6]

theorem enc_eq_iff {g p : Perm (Fin 6)} : enc g = enc p ↔ g = p :=
  ⟨enc_inj h6, congrArg enc⟩

theorem mem4_iff {g p q r : Perm (Fin 6)} {a b c : ℕ} (ha : enc p = a) (hb : enc q = b)
    (hc : enc r = c) : (g = 1 ∨ g = p ∨ g = q ∨ g = r) ↔ memK (enc g) [oneS, a, b, c] = true := by
  rw [memK_iff, ← ha, ← hb, ← hc, ← enc_oneS]
  simp only [List.mem_cons, List.not_mem_nil, or_false, enc_eq_iff]

@[expose] noncomputable def k1K (c : ℕ) : Bool := gK 4534800 c && evenK 6 c

@[expose] noncomputable def k2K (c : ℕ) : Bool := gK 4530945 c && evenK 6 c

@[expose] noncomputable def tK (c : ℕ) : Bool := gK 4534800 c && gK 4530945 c

@[expose] noncomputable def hK (c : ℕ) : Bool := k1K c && k2K c

@[expose] noncomputable def conjK6 (cg cx : ℕ) : ℕ := mulK 6 (mulK 6 cg cx) (invCK 6 cg)

theorem enc_conj6 (g x : Perm (Fin 6)) : enc (g * x * g⁻¹) = conjK6 (enc g) (enc x) := by
  rw [conjK6, enc_mul h6, enc_mul h6, enc_inv_invCK h6]

theorem n1_mul_ok : allK (fun a => allK (fun b => memK (mulK 6 a b)
    [oneS, 5513985, 5509170, 5505315]) [oneS, 5513985, 5509170, 5505315])
    [oneS, 5513985, 5509170, 5505315] = true := by decide +kernel

theorem n1_inv_ok : allK (fun a => memK (invCK 6 a) [oneS, 5513985, 5509170, 5505315])
    [oneS, 5513985, 5509170, 5505315] = true := by decide +kernel

theorem n2_mul_ok : allK (fun a => allK (fun b => memK (mulK 6 a b)
    [oneS, 5513985, 4530960, 4534785]) [oneS, 5513985, 4530960, 4534785])
    [oneS, 5513985, 4530960, 4534785] = true := by decide +kernel

theorem n2_inv_ok : allK (fun a => memK (invCK 6 a) [oneS, 5513985, 4530960, 4534785])
    [oneS, 5513985, 4530960, 4534785] = true := by decide +kernel

theorem n1_ok : allK (fun c => k1K c && k2K c && Nat.beq (mulK 6 c c) oneS)
    [oneS, 5513985, 5509170, 5505315] = true := by decide +kernel

theorem n2_ok : allK (fun c => k2K c && Nat.beq (mulK 6 c c) oneS)
    [oneS, 5513985, 4530960, 4534785] = true := by decide +kernel

theorem k1_norm_ok : walkK 6 (fun c => !k1K c || allK (fun q => memK (conjK6 c q)
    [oneS, 5513985, 5509170, 5505315]) [oneS, 5513985, 5509170, 5505315]) 6 0 0 0 = true := by
  decide +kernel

theorem k2_norm_ok : walkK 6 (fun c => !k2K c || allK (fun q => memK (conjK6 c q)
    [oneS, 5513985, 4530960, 4534785]) [oneS, 5513985, 4530960, 4534785]) 6 0 0 0 = true := by
  decide +kernel

theorem k1_cent_ok : walkK 6 (fun c => !k1K c || !allK (fun q => gK q c)
    [oneS, 5513985, 5509170, 5505315] || memK c [oneS, 5513985, 5509170, 5505315]) 6 0 0 0 =
    true := by
  decide +kernel

theorem k2_cent_ok : walkK 6 (fun c => !k2K c || !allK (fun q => gK q c)
    [oneS, 5513985, 4530960, 4534785] || memK c [oneS, 5513985, 4530960, 4534785]) 6 0 0 0 =
    true := by
  decide +kernel

theorem split_ok : walkK 6 (fun c => !tK c || hK c || hK (mulK 6 4534800 c)) 6 0 0 0 = true := by
  decide +kernel

theorem split1_ok : walkK 6 (fun c => !gK 4534800 c || k1K c || k1K (mulK 6 4534800 c)) 6 0 0 0 =
    true := by
  decide +kernel

theorem split2_ok : walkK 6 (fun c => !gK 4530945 c || k2K c || k2K (mulK 6 4530945 c)) 6 0 0 0 =
    true := by
  decide +kernel

theorem moved_ok : walkK 6 (fun c => !(tK c && !Nat.beq c oneS) ||
    !walkK 6 (fun d => !(!tK (conjK6 d c))) 6 0 0 0) 6 0 0 0 = true := by
  decide +kernel

end CFSG.Quasithin.F6.GoldAmS.Pack
