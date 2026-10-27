module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdB
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem finite_W (S : OmegaModel W) : Finite W :=
  Finite.of_injective (S.e : W → Multiplicative (OmI → S.K)) S.e.injective

private theorem finite_mulAut (S : OmegaModel W) : Finite (MulAut W) := by
  haveI := finite_W S
  exact Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

theorem card_omega0 (hK : Nat.card S.K = 8) : Nat.card S.omega0 = 254016 := by
  have hSL : Nat.card (SL(2, S.K)) = 504 := by
    have h := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two S.K
    rw [hK] at h
    norm_num at h
    exact h
  have hnum : (504 : ℕ) * 504 = 254016 := by norm_num
  change Nat.card (S.jHom.range) = 254016
  rw [Nat.card_congr (MonoidHom.ofInjective S.jHom_injective).toEquiv.symm, Nat.card_prod,
    hSL, hnum]

theorem omega_eq_omega0 (hK : Nat.card S.K = 8) (hΩ : Nat.card S.omega = 254016) :
    S.omega = S.omega0 := by
  haveI := finite_mulAut S
  have hcard : Nat.card S.omega ≤ Nat.card S.omega0 := by
    simp [hΩ, card_omega0 S hK]
  exact (Subgroup.eq_of_le_of_card_ge (H := S.omega0) (K := S.omega) (omega0_le_omega S)
    hcard).symm

theorem le_omega_of_isPGroup_of_le_isoSub (hK : Nat.card S.K = 8)
    (hΩ : Nat.card S.omega = 254016) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut W)} (hP : IsPGroup p P) (hPI : P ≤ isoSub S) : P ≤ S.omega := by
  intro x hx
  have hcardH : Nat.card (S.omega.subgroupOf (isoSub S)) = 254016 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (omega_le_isoSub S)).toEquiv]
    exact hΩ
  have hcardI : Nat.card (isoSub S) = 508032 := card_isoSub S hK
  have hindex : (S.omega.subgroupOf (isoSub S)).index = 2 := by
    have hmul := Subgroup.card_mul_index (H := S.omega.subgroupOf (isoSub S))
    rw [hcardH, hcardI] at hmul
    omega
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hxpow : x ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  let y : ↥(isoSub S) := ⟨x, hPI hx⟩
  have hy_pow : y ^ (p ^ k) = 1 := by
    apply Subtype.ext
    change x ^ (p ^ k) = 1
    exact hxpow
  have hsq : y ^ 2 ∈ S.omega.subgroupOf (isoSub S) :=
    Subgroup.sq_mem_of_index_two hindex y
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have hpow_eq : y ^ (p ^ k) = y * (y ^ 2) ^ m := by
    rw [hm, pow_succ', pow_mul]
  have hprod : y * (y ^ 2) ^ m = 1 := by
    rw [← hpow_eq, hy_pow]
  have hy_eq : y = ((y ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hy_mem : y ∈ S.omega.subgroupOf (isoSub S) := by
    rw [hy_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq m)
  simpa using (Subgroup.mem_subgroupOf).mp hy_mem

theorem card_le_nine_of_isElemAbelian_le_omega0 (hK : Nat.card S.K = 8)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian 3 X) (hXΩ : X ≤ S.omega0) :
    Nat.card X ≤ 9 := by
  let fstHom : SL(2, S.K) × SL(2, S.K) →* SL(2, S.K) := MonoidHom.fst _ _
  let sndHom : SL(2, S.K) × SL(2, S.K) →* SL(2, S.K) := MonoidHom.snd _ _
  set X' : Subgroup (SL(2, S.K) × SL(2, S.K)) := X.comap S.jHom with hX'def
  have hmap : X'.map S.jHom = X := by
    rw [hX'def]
    exact Subgroup.map_comap_eq_self (f := S.jHom) (H := X) hXΩ
  have hcard : Nat.card X' = Nat.card X := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (K := X') (f := S.jHom) S.jHom_injective).symm
  haveI : IsMulCommutative ↥X := hX.1
  have hX' : IsElemAbelian 3 X' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply S.jHom_injective
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val
        (mul_comm' (⟨S.jHom a.1, a.2⟩ : X) (⟨S.jHom b.1, b.2⟩ : X))
    · apply S.jHom_injective
      rw [map_pow, map_one]
      exact hX.2 (S.jHom x) hx
  have h1 : Nat.card (X'.map fstHom) ≤ 3 :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.card_le_three_of_elemAbelian_sl2
      (IsElemAbelian.map hX' fstHom)
  have h2 : Nat.card (X'.map sndHom) ≤ 3 :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.card_le_three_of_elemAbelian_sl2
      (IsElemAbelian.map hX' sndHom)
  haveI : Finite ↥(X'.map fstHom) := Subtype.finite
  haveI : Finite ↥(X'.map sndHom) := Subtype.finite
  have hinj : Function.Injective (fun e : X' =>
      ((⟨e.1.1, Subgroup.mem_map_of_mem fstHom e.2⟩ : X'.map fstHom),
       (⟨e.1.2, Subgroup.mem_map_of_mem sndHom e.2⟩ : X'.map sndHom))) := by
    intro u v huv
    simp only [Prod.mk.injEq] at huv
    exact Subtype.ext (Prod.ext (congrArg Subtype.val huv.1) (congrArg Subtype.val huv.2))
  calc Nat.card X = Nat.card X' := hcard.symm
    _ ≤ Nat.card (X'.map fstHom × X'.map sndHom) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (X'.map fstHom) * Nat.card (X'.map sndHom) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul h1 h2
    _ = 9 := by norm_num

theorem card_le_nine_of_isElemAbelian_le_normalizer_inf_linSub (hK : Nat.card S.K = 8)
    (hΩ : Nat.card S.omega = 254016) {X : Subgroup (MulAut W)} (hX : IsElemAbelian 3 X)
    (hXN : X ≤ omegaNorm S ⊓ linSub S) : Nat.card X ≤ 9 := by
  have hXp : IsPGroup 3 X := hX.isPGroup
  have hXiso : X ≤ isoSub S :=
    le_isoSub_of_isPGroup_of_le_linSub S hK Nat.prime_three (by norm_num) hXp hXN
  have hXω : X ≤ S.omega :=
    le_omega_of_isPGroup_of_le_isoSub S hK hΩ Nat.prime_three (by norm_num) hXp hXiso
  exact card_le_nine_of_isElemAbelian_le_omega0 S hK hX
    (by rw [← omega_eq_omega0 S hK hΩ]; exact hXω)

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
