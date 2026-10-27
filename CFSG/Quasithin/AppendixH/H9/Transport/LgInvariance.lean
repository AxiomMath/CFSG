module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.ConjTransport

public section

namespace CFSG.ASVolI.ChH.Transport

open CFSG.Quasithin CFSG.Open

section Generic

variable {V : Type*} [CommGroup V]

theorem map_eq_self_of_mem_stabSub {g : MulAut V} {U : Subgroup V} (hg : g ∈ stabSub U) :
    U.map (g : MulAut V).toMonoidHom = U := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have h := hg (g.symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem inv_apply_apply (g : MulAut V) (v : V) : (g⁻¹ : MulAut V) (g v) = v :=
  g.symm_apply_apply v

theorem conjAut_inv_conjAut (g : MulAut V) (A : Subgroup (MulAut V)) :
    conjAut g⁻¹ (conjAut g A) = A := by
  rw [← conjAut_mul, inv_mul_cancel, conjAut_one]

theorem map_zpowers_sup_zpowers_aut (g : MulAut V) (v₁ v₂ : V) :
    (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂).map (g : MulAut V).toMonoidHom =
      Subgroup.zpowers (g v₁) ⊔ Subgroup.zpowers (g v₂) := by
  rw [map_sup_subgroup, map_zpowers, map_zpowers]

theorem inf_centSub_zpowers_map_eq_conjAut {g : MulAut V} {X : Subgroup (MulAut V)}
    (hX : conjAut g X = X) (x : V) :
    X ⊓ centSub (Subgroup.zpowers (g x)) = conjAut g (X ⊓ centSub (Subgroup.zpowers x)) := by
  rw [conjAut_inf, hX, conjAut_centSub, map_zpowers]

theorem inf_centSub_zpowers_sup_map_eq_conjAut {g : MulAut V} {X : Subgroup (MulAut V)}
    (hX : conjAut g X = X) (v₁ v₂ : V) :
    X ⊓ centSub (Subgroup.zpowers (g v₁) ⊔ Subgroup.zpowers (g v₂)) =
      conjAut g (X ⊓ centSub (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) := by
  rw [conjAut_inf, hX, conjAut_centSub, map_zpowers_sup_zpowers_aut]

theorem commOn_conjAut_of_map_eq {g : MulAut V} {W : Subgroup V}
    (hW : W.map (g : MulAut V).toMonoidHom = W) (A : Subgroup (MulAut V)) :
    commOn W (conjAut g A) = (commOn W A).map (g : MulAut V).toMonoidHom := by
  have h := commOn_conjAut g W A
  rwa [hW] at h

theorem conjAut_inf_stabSub {g : MulAut V} {U : Subgroup V} (hU : g ∈ stabSub U)
    (T : Subgroup (MulAut V)) :
    conjAut g T ⊓ stabSub U = conjAut g (T ⊓ stabSub U) := by
  rw [conjAut_inf, conjAut_stabSub, map_eq_self_of_mem_stabSub hU]

theorem inf_map_eq_of_map_eq_self {g : MulAut V} {U P P' : Subgroup V}
    (hU : U.map (g : MulAut V).toMonoidHom = U)
    (hP : P' = P.map (g : MulAut V).toMonoidHom) :
    U ⊓ P' = (U ⊓ P).map (g : MulAut V).toMonoidHom := by
  rw [hP, map_inf_subgroup, hU]

end Generic

variable {n : ℕ}

theorem conjAut_Lg_of_mem {l : MulAut (PairN n)} (hl : l ∈ Lg n) : conjAut l (Lg n) = Lg n :=
  conjAut_eq_self_of_mem hl

theorem conjAut_Mg_of_mem {l : MulAut (PairN n)} (hl : l ∈ Lg n) : conjAut l (Mg n) = Mg n :=
  conjAut_eq_self_of_mem (Lg_le_Mg hl)

theorem perpN_map_of_mem_Lg {l : MulAut (PairN n)} (hl : l ∈ Lg n) (S : Subgroup (PairN n)) :
    perpN n (S.map (l : MulAut (PairN n)).toMonoidHom) =
      (perpN n S).map (l : MulAut (PairN n)).toMonoidHom :=
  perpN_map_of_mem_Mg (Lg_le_Mg hl) S

theorem mem_Oorb_two_iff_of_mem_Lg {l : MulAut (PairN n)} (hl : l ∈ Lg n) (x : PairN n) :
    l x ∈ Oorb n 2 ↔ x ∈ Oorb n 2 := by
  have h1 : (l x).1 = 1 ↔ x.1 = 1 := by
    rw [← mem_V2n, ← mem_V2n]
    exact Lg_le_stabSub_V2n hl x
  have h2 : (l x).2 = 1 ↔ x.2 = 1 := by
    rw [← mem_V1n, ← mem_V1n]
    exact Lg_le_stabSub_V1n hl x
  have h3 : pairQn n (l x) = pairQn n x := pairQn_of_mem_Mg (Lg_le_Mg hl) x
  show ((l x).1 ≠ 1 ∧ (l x).2 ≠ 1 ∧ pairQn n (l x) = 1) ↔ (x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ pairQn n x = 1)
  rw [h3, ne_eq, ne_eq, ne_eq, ne_eq, h1, h2]

end CFSG.ASVolI.ChH.Transport
