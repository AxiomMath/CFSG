module

public import CFSG.RankThree.PartOne.U5K.Hyp.Lam
public import CFSG.RankThree.PartOne.U5K.Hyp.SLTwo

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

section Hom

variable (hK)

@[expose] def eeHom : Lam hK →* Matrix (Fin 2) (Fin 2) K where
  toFun x := blkEE (x : Gam hK)
  map_one' := by
    ext i j
    simp [blkEE, lmat, Matrix.one_apply]
  map_mul' x y := by
    have hm := lmat_mul_of_right_one (y := (y : Gam hK)) x.2.1
    obtain ⟨-, hA, -, -⟩ := mul_para x.2.2.1 y.2.2.1
    show blkEE ((x : Gam hK) * (y : Gam hK)) = blkEE (x : Gam hK) * blkEE (y : Gam hK)
    calc blkEE ((x : Gam hK) * (y : Gam hK)) = blkA (lmat ((x : Gam hK) * (y : Gam hK))) := rfl
      _ = blkA (lmat (x : Gam hK) * lmat (y : Gam hK)) := by rw [hm]
      _ = blkA (lmat (x : Gam hK)) * blkA (lmat (y : Gam hK)) := hA
      _ = blkEE (x : Gam hK) * blkEE (y : Gam hK) := rfl

@[expose] def ffHom : Lam hK →* Matrix (Fin 2) (Fin 2) K where
  toFun x := blkFF (x : Gam hK)
  map_one' := by
    ext i j
    simp [blkFF, lmat, Matrix.one_apply]
  map_mul' x y := by
    have hm := lmat_mul_of_right_one (y := (y : Gam hK)) x.2.1
    obtain ⟨-, -, -, hD⟩ := mul_para x.2.2.1 y.2.2.1
    show blkFF ((x : Gam hK) * (y : Gam hK)) = blkFF (x : Gam hK) * blkFF (y : Gam hK)
    calc blkFF ((x : Gam hK) * (y : Gam hK)) = blkD (lmat ((x : Gam hK) * (y : Gam hK))) := rfl
      _ = blkD (lmat (x : Gam hK) * lmat (y : Gam hK)) := by rw [hm]
      _ = blkD (lmat (x : Gam hK)) * blkD (lmat (y : Gam hK)) := hD
      _ = blkFF (x : Gam hK) * blkFF (y : Gam hK) := rfl

end Hom

section Gram

theorem ee_ff_gram (x : Gam hK) (hP : IsPara (lmat x)) :
    ∃ μ : K, μ ≠ 0 ∧ hK.bar μ = μ ∧ ∀ i k : Fin 2,
      hK.bar (blkEE x 0 i) * blkFF x 0 k + hK.bar (blkEE x 1 i) * blkFF x 1 k =
        if i = k then μ else 0 := by
  obtain ⟨μ, hμ0, hμ, hgram⟩ := x.2
  refine ⟨μ, hμ0, hμ, fun i k => ?_⟩
  have := congrFun (congrFun hgram (.inl i)) (.inr (.inr k))
  rw [conjTranspose_hypGram_mul_apply] at this
  have h1 := hP.1
  have h2 := hP.2.1
  simp [Fintype.sum_sum_type, Fin.sum_univ_two] at this
  have e1 : lmat x (Sum.inr (Sum.inl 0)) (Sum.inl i) = 0 := h1 i
  have e2 : ∀ j, lmat x (Sum.inr (Sum.inr j)) (Sum.inl i) = 0 := fun j => h2 i j
  unfold lmat at e1 e2
  simp only [e1, e2, map_zero, zero_mul, add_zero] at this
  simpa [blkEE, blkFF, lmat, Matrix.of_apply] using this

end Gram

section Faithful

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem centralizes_of_blocks {x : Gam hK} (hxr : x.1.right = 1) (hE : blkEE x = 1)
    (hF : blkFF x = 1)
    (hρ : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1)))) :
    Phi hK x ∈ Subgroup.centralizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
  have hact : ∀ v ∈ Vsub hK, act hK x v = v := by
    intro v hv
    obtain ⟨-, Y'', hY''⟩ := act_mem_Vsub hZ hρ hv
    obtain ⟨-, Y, hY⟩ := hv
    have h := ef_block (x := x) hY hY''
    rw [hE, hF, Matrix.one_mul, Matrix.mul_one] at h
    have hmap : Y.map x.1.right = Y := by
      ext i j
      simp [hxr]
    rw [hmap] at h
    apply mat_injective
    rw [hY'', hY, h]
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  have h1 := Phi_mul_innM_mul_inv x v
  rw [hact v hv, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem faithful_Sh {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpf : p ∣ 2 ^ f + 1)
    {B : Subgroup (MulAut (hypPSU hK 2 1))}
    (hBN : B ≤ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) ⊓ Dlin hK)
    (hBel : IsElementaryAbelian p B) (hBcard : Nat.card B = p ^ 2) :
    ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have := finite_Gam hK
  have hKfin : Finite K := hK.finite
  have hchar : CharP K 2 := hK.charP
  have hbN : ∀ b ∈ B, b ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) :=
    fun b hb => mem_normalizer_Vh_of_Sh hZ (hBN hb).1
  let g : Lam hK →* MulAut (hypPSU hK 2 1) := (Phi hK).comp (Lam hK).subtype
  set BL : Subgroup (Lam hK) := B.comap g with hBL
  let π : BL →* B := (g.comp BL.subtype).codRestrict B (fun x => x.2)
  have hπinj : Function.Injective π := by
    intro x y h
    have h1 : Phi hK ((x : Lam hK) : Gam hK) = Phi hK ((y : Lam hK) : Gam hK) :=
      congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Phi_injOn_Lam (x : Lam hK).2 (y : Lam hK).2 h1))
  have hπsurj : Function.Surjective π := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hxL, hx⟩ := exists_lam_lift hZ (hBN hb).2 (hbN b hb)
    exact ⟨⟨⟨x, hxL⟩, by rw [hBL, Subgroup.mem_comap]; change Phi hK x ∈ B; rw [hx]; exact hb⟩,
      Subtype.ext hx⟩
  let e : BL ≃* B := MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  have hBc : ∀ a b : B, a * b = b * a := fun a b => hBel.toIsMulCommutative.is_comm.comm a b
  have hBp : ∀ a : B, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B)
  have hcomm : ∀ a b : BL, a * b = b * a := fun a b => e.injective (by rw [map_mul, map_mul, hBc])
  have hexp : ∀ a : BL, a ^ p = 1 := fun a => e.injective (by rw [map_pow, hBp, map_one])
  have hcard : p < Nat.card BL := by
    rw [Nat.card_congr e.toEquiv, hBcard]
    have := hp.two_le
    nlinarith
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hdvdK : p ∣ Nat.card K - 1 := by
    rw [hK.card_eq_sq]
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      obtain ⟨r, hr⟩ : ∃ r, 2 ^ f = r + 1 := ⟨2 ^ f - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hpf _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd hp hdvdK
  let ε : BL →* Matrix (Fin 2) (Fin 2) K := (eeHom hK).comp BL.subtype
  let ε' : BL →* Matrix (Fin 2) (Fin 2) K := (ffHom hK).comp BL.subtype
  obtain ⟨a, ha1, haε⟩ := exists_ne_one_ker hp hp2 hζ hcomm hexp hcard ε (fun a => a.1.2.2.2)
  set x : Gam hK := ((a : Lam hK) : Gam hK) with hx
  have hxL : x ∈ Lam hK := (a : Lam hK).2
  have hxr : x.1.right = 1 := hxL.1
  have hxP : IsPara (lmat x) := hxL.2.1
  have hE : blkEE x = 1 := haε
  have hxB : Phi hK x ∈ B := a.2
  have hxp : x ^ p = 1 := by
    have := congrArg (fun y : BL => (((y : Lam hK)) : Gam hK)) (hexp a)
    simpa using this
  obtain ⟨μ, hμ0, hμF, hμ⟩ := ee_ff_gram x hxP
  have hFμ : blkFF x = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext k l
    have := hμ k l
    rw [hE] at this
    fin_cases k <;> fin_cases l <;>
      simp [Matrix.one_apply, map_one, map_zero] at this ⊢ <;> assumption
  have hμp : μ ^ p = 1 := by
    have h1 : (ε' a) ^ p = 1 := by rw [← map_pow, hexp, map_one]
    have h2 : ε' a = blkFF x := rfl
    rw [h2, hFμ, smul_pow, one_pow] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  have hμq : μ ^ (2 ^ f - 1) = 1 := by
    have h1 : μ ^ 2 ^ f = μ := by rw [← UnitaryFieldData.bar_apply]; exact hμF
    have h2 : μ ^ 2 ^ f = μ ^ (2 ^ f - 1) * μ := by
      rw [← pow_succ, Nat.sub_add_cancel hq1]
    rw [h2] at h1
    exact mul_right_cancel₀ hμ0 (by rw [h1, one_mul])
  have hcop : Nat.Coprime p (2 ^ f - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    have h2 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hpf h
    have h3 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [h3] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hμ1 : μ = 1 := by
    have := pow_gcd_eq_one.2 ⟨hμp, hμq⟩
    rwa [hcop, pow_one] at this
  have hF : blkFF x = 1 := by rw [hFμ, hμ1, one_smul]
  have hxN : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := hbN _ hxB
  refine ⟨Phi hK x, hxB, ?_, centralizes_of_blocks hZ hxr hE hF hxN⟩
  intro h1
  apply ha1
  exact Subtype.ext (Subtype.ext (Phi_injOn_Lam hxL (one_mem _) (h1.trans (map_one (Phi hK)).symm)))

end Faithful

end CFSG.RankThree.PartOne.U5K.Hyp
