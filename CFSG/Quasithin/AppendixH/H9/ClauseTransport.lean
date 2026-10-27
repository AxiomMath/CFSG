module

public import CFSG.Quasithin.AppendixH.H9.H91Clauses
public import CFSG.Quasithin.AppendixH.H9.Transport.Clause3Transport
public import CFSG.Quasithin.AppendixH.H9.Transport.Clause4Transport

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem H91Clause3_conj (n : ℕ) {l : MulAut (PairN n)} (hl : l ∈ Lg n)
    (T : Subgroup (MulAut (PairN n))) (v₁ : PairN n) :
    H91Clause3 n T v₁ ↔ H91Clause3 n (conjAut l T) (l v₁) :=
  Transport.clause3Gen_conj (M := Mg n) (L := Lg n) (V1 := V1n n) (V2 := V2n n)
    (perp := perpN n) (c := 2 ^ (n - 1)) (Q := GL (Fin (n - 1)) (ZMod 2))
    (Γ := natSub (n - 1) (ZMod 2) ⊤) (G := Lg n)
    (fun _ hg => Transport.conjAut_Lg_of_mem hg) (fun _ hg => Transport.conjAut_Mg_of_mem hg)
    Lg_le_stabSub_V1n Lg_le_stabSub_V2n (fun _ hg U => Transport.perpN_map_of_mem_Lg hg U) hl T v₁

theorem H91Clause4_conj (n : ℕ) {l : MulAut (PairN n)} (hl : l ∈ Lg n)
    (T : Subgroup (MulAut (PairN n))) (v₁ v₂ : PairN n) :
    H91Clause4 n T v₁ v₂ ↔ H91Clause4 n (conjAut l T) (l v₁) (l v₂) :=
  Transport.clause4Gen_conj (M := Mg n) (L := Lg n) (V1 := V1n n) (V2 := V2n n)
    (perp := perpN n) (polar := polarN n) (Orb := Oorb n 2)
    (X := MulAut (GL (Fin (n - 1)) (ZMod 2))) (Γ := natSub (n - 1) (ZMod 2) ⊤) (G := Lg n)
    (fun _ hg => Transport.conjAut_Lg_of_mem hg) (fun _ hg => Transport.conjAut_Mg_of_mem hg)
    Lg_le_stabSub_V1n Lg_le_stabSub_V2n (fun _ hg U => Transport.perpN_map_of_mem_Lg hg U)
    (fun _ hg x y => polarN_of_mem_Mg (Lg_le_Mg hg) x y)
    (fun _ hg x => Transport.mem_Oorb_two_iff_of_mem_Lg hg x) hl T v₁ v₂

end CFSG.ASVolI.ChH
