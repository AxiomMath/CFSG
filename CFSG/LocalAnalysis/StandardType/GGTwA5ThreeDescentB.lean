module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGTDModelLiftTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma twd_pow_mod_three {G : Type} [Group G] (c : G) (hc : c ^ 3 = 1) (m : ℕ) :
    c ^ m = c ^ (m % 3) := by
  have h : m = 3 * (m / 3) + m % 3 := by omega
  conv_lhs => rw [h]
  rw [pow_add, pow_mul, hc, one_pow, one_mul]

private lemma twd_ofAdd_one_cube :
    (Multiplicative.ofAdd (1 : ZMod 3) : Multiplicative (ZMod 3)) ^ 3 = 1 := by
  decide

private theorem twd_mu3_cube (θ : Multiplicative (ZMod 3)) : θ ^ 3 = 1 := by
  have hgen : (Multiplicative.ofAdd (1 : ZMod 3) : Multiplicative (ZMod 3)) ^ (θ.toAdd).val =
      θ := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    rfl
  rw [← hgen, ← pow_mul, Nat.mul_comm (θ.toAdd).val 3, pow_mul, twd_ofAdd_one_cube, one_pow]

private def twd_zmodHom {G : Type} [Group G] (c : G) (hc : c ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun z := c ^ (z.toAdd).val
  map_one' := by simp [ZMod.val_zero]
  map_mul' := by
    intro a b
    change c ^ (a.toAdd + b.toAdd).val = c ^ (a.toAdd).val * c ^ (b.toAdd).val
    have hsum : (a.toAdd + b.toAdd).val = (a.toAdd.val + b.toAdd.val) % 3 := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a.toAdd, ← ZMod.natCast_zmod_val b.toAdd,
        ← Nat.cast_add]
      rw [ZMod.val_natCast]
    rw [hsum, ← pow_add]
    exact (twd_pow_mod_three c hc (a.toAdd.val + b.toAdd.val)).symm

private noncomputable def twd_corElt {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) : L' :=
  (Classical.choose (QuotientGroup.mk_surjective
    (w₁.cor k (Multiplicative.ofAdd (1 : ZMod 3))))) ^ (4 ^ Nat.card L')

private theorem twd_corElt_mk {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) :
    ((twd_corElt hker hAle w₁ k : L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
      w₁.cor k (Multiplicative.ofAdd (1 : ZMod 3)) := by
  rw [twd_corElt, QuotientGroup.mk_pow,
    Classical.choose_spec (QuotientGroup.mk_surjective
      (w₁.cor k (Multiplicative.ofAdd (1 : ZMod 3))))]
  rw [← map_pow]
  congr 1
  rw [twd_pow_mod_three _ twd_ofAdd_one_cube (4 ^ Nat.card L'), Nat.pow_mod]
  norm_num

private theorem twd_corElt_cube {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) :
    (twd_corElt hker hAle w₁ k) ^ 3 = 1 := by
  set ĉ : L' := Classical.choose (QuotientGroup.mk_surjective
    (w₁.cor k (Multiplicative.ofAdd (1 : ZMod 3)))) with hĉ
  have hĉmk : (ĉ : L' ⧸ U63TB.twoSub ψ.ker hker) =
      w₁.cor k (Multiplicative.ofAdd (1 : ZMod 3)) :=
    Classical.choose_spec (QuotientGroup.mk_surjective _)
  have hĉ3 : ĉ ^ 3 ∈ U63TB.twoSub ψ.ker hker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hĉmk, ← map_pow,
      twd_ofAdd_one_cube, map_one]
  have hZ2 : ((ĉ ^ 3) ^ (2 ^ Nat.card L')) = 1 :=
    ((U63TB.mem_twoSub hker).mp hĉ3).2
  have he : (4 : ℕ) ^ Nat.card L' = 2 ^ Nat.card L' * 2 ^ Nat.card L' := by
    rw [← mul_pow]; norm_num
  have htw : twd_corElt hker hAle w₁ k = ĉ ^ (4 ^ Nat.card L') := by
    rw [twd_corElt, hĉ]
  rw [htw, ← pow_mul, Nat.mul_comm (4 ^ Nat.card L') 3, pow_mul, he, pow_mul, hZ2, one_pow]

private noncomputable def twd_cor {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) :
    Multiplicative (ZMod 3) →* L' :=
  twd_zmodHom (twd_corElt hker hAle w₁ k) (twd_corElt_cube hker hAle w₁ k)

private theorem twd_cor_mk {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) (ζ : Multiplicative (ZMod 3)) :
    ((twd_cor hker hAle w₁ k ζ : L') : L' ⧸ U63TB.twoSub ψ.ker hker) = w₁.cor k ζ := by
  have hgen : (Multiplicative.ofAdd (1 : ZMod 3) : Multiplicative (ZMod 3)) ^ (ζ.toAdd).val =
      ζ := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    rfl
  change (((twd_corElt hker hAle w₁ k) ^ (ζ.toAdd).val : L') :
    L' ⧸ U63TB.twoSub ψ.ker hker) = w₁.cor k ζ
  rw [QuotientGroup.mk_pow, twd_corElt_mk, ← map_pow, hgen]

private theorem twd_eq_of_mk_eq {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {x y : L'} (h : (x : L' ⧸ U63TB.twoSub ψ.ker hker) =
      (y : L' ⧸ U63TB.twoSub ψ.ker hker)) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) : x = y := by
  have h2 : IsPGroup 2 (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)).ker := by
    rw [QuotientGroup.ker_mk']
    exact U63TB.isPGroup_twoSub hker
  have hc : (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)).ker ≤
      Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    exact U63TB.twoSub_le_center hker
  exact eq_of_map_eq_of_pow_odd hc h2 (m := 3) (by norm_num) h hx hy

end CFSG.StandardType

end
