module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRank
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem card_le_pow_orthPlus_cover {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥)
    (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))),
      ∀ l : L', φ (ψ l) = ψ (a l)) :
    Nat.card A ≤ p ^ m := by
  classical
  haveI := Fact.mk hp
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))
  have hZR : Subgroup.center R = ⊥ := hZ
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hI a a.2
    obtain ⟨t, rfl⟩ := hφI
    exact ⟨t, fun l => by simpa [MulAut.conj_apply] using (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZR, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have heq : ((a : MulAut L') : L' →* L') = MonoidHom.id L' := by
      refine TypeA.eq_of_inv_mul_mem_center (S := L') hperf
        ((a : MulAut L') : L' →* L') (MonoidHom.id L') ?_
      intro l
      apply hker
      rw [MonoidHom.mem_ker]
      change ψ (((a : MulAut L') l)⁻¹ * l) = 1
      have h := hχ a l
      rw [ha, one_mul, inv_one, mul_one] at h
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel (ψ l)
    apply Subtype.ext
    ext l
    simpa using congrArg (fun f : L' →* L' => f l) heq
  have hEA : IsElemAbelian p χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcard : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  calc Nat.card A = Nat.card χ.range := hcard.symm
    _ ≤ p ^ m := OrthRest.card_le_plus hm hp hp2 χ.range hEA

end CFSG.StandardType
