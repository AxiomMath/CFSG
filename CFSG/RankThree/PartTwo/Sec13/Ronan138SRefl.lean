module

import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item138

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open Matrix (GeneralLinearGroup ProjGenLinGroup)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits diagTau cycThree slPi glPi PiField ModThree)

section Swap

variable {K : Type} [Field K]

@[expose] def swapTwoThree : GL (Fin 3) K :=
  ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], !![-1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapTwoThree :
    ((swapTwoThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0] :=
  rfl

theorem swapTwoThree_inv : (swapTwoThree : GL (Fin 3) K)⁻¹ = swapTwoThree := rfl

theorem swapTwoThree_mem_slPi {p f : ℕ} {π : Bool} (hπ : π = false → UnitaryFieldData p f K) :
    swapTwoThree ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((swapTwoThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_swapTwoThree, Matrix.det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [Sec4.mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_swapTwoThree]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, map_neg, map_one]
  · rw [Sec4.mem_slPi_true]
    exact hdet

theorem swapTwoThree_conj_diagUnits (a b c : Kˣ) :
    swapTwoThree * diagUnits a b c * swapTwoThree⁻¹ = diagUnits a c b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, swapTwoThree_inv, coe_swapTwoThree, Sec4.coe_diagUnits_eq,
    Sec4.coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem comm_swapTwoThree_conj {g y : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) :
    (g * swapTwoThree * g⁻¹) * y * (g * swapTwoThree * g⁻¹)⁻¹ * y⁻¹ =
      g * diagUnits 1 (t * s⁻¹) (s * t⁻¹) * g⁻¹ := by
  have hy' : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  have hsc : swapTwoThree * GeneralLinearGroup.scalar (Fin 3) l =
      GeneralLinearGroup.scalar (Fin 3) l * swapTwoThree :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l swapTwoThree).eq
  have h1 := swapTwoThree_conj_diagUnits (K := K) 1 s t
  have h2 : diagUnits 1 t s * (diagUnits 1 s t)⁻¹ = diagUnits 1 (t * s⁻¹) (s * t⁻¹) := by
    rw [Sec4.diagUnits_inv, Sec4.diagUnits_mul, inv_one, mul_one]
  rw [hy']
  calc g * swapTwoThree * g⁻¹ * (g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) *
        g⁻¹) * (g * swapTwoThree * g⁻¹)⁻¹ *
        (g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹)⁻¹ =
      g * ((swapTwoThree * GeneralLinearGroup.scalar (Fin 3) l) * diagUnits 1 s t *
        swapTwoThree⁻¹ * (diagUnits 1 s t)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹) * g⁻¹ := by
        group
    _ = g * (GeneralLinearGroup.scalar (Fin 3) l * ((swapTwoThree * diagUnits 1 s t *
        swapTwoThree⁻¹) * (diagUnits 1 s t)⁻¹) * (GeneralLinearGroup.scalar (Fin 3) l)⁻¹) *
        g⁻¹ := by
      rw [hsc]
      group
    _ = g * diagUnits 1 (t * s⁻¹) (s * t⁻¹) * g⁻¹ := by rw [h1, h2, scalar_conj]

theorem mk_swapTwoThree_conj_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ProjGenLinGroup.mk (swapTwoThree * diagTau hτ * swapTwoThree⁻¹) =
      (ProjGenLinGroup.mk (diagTau hτ))⁻¹ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set u := Units.mk0 τ hτ0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hτ,
    Units.val_one])
  rw [Sec4.diagTau_eq_diagUnits hτ hτ0, swapTwoThree_conj_diagUnits, ← hu, ← map_inv,
    Sec4.diagUnits_inv]
  have h1 : diagUnits u 1 (u ^ 2) =
      GeneralLinearGroup.scalar (Fin 3) (u ^ 2) * diagUnits u⁻¹ (u ^ 2)⁻¹ 1⁻¹ := by
    have hs : GeneralLinearGroup.scalar (Fin 3) (u ^ 2) = diagUnits (u ^ 2) (u ^ 2) (u ^ 2) := by
      apply Units.ext
      rw [Sec4.coe_diagUnits_eq, Sec4.coe_scalar_eq_smul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hs, Sec4.diagUnits_mul]
    congr 1
    · rw [show u ^ 2 * u⁻¹ = u by group]
    · rw [mul_inv_cancel]
    · rw [inv_one, mul_one]
  rw [h1, map_mul, Sec13.mk_scalar, one_mul]

end Swap

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_inverting_of_hyp138 {A : Subgroup G} {c : G} {L E : Subgroup G}
    (hH : Hyp138 A c L E) :
    ∃ d t : G, d ∈ E ∧ d ∈ L ∧ d ≠ 1 ∧ t ∈ L ∧ t ∈ Subgroup.normalizer (E : Set G) ∧
      t * d * t⁻¹ = d⁻¹ := by
  obtain ⟨h, -, -, hE3, -, hEN, -, hST, hC⟩ := hH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := by
    rcases hST with hS | hT
    · exact hS.1
    · exact hT.1
  have hEF : E ∈ partTwoF G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ hEE
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hEF.2.1
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3.2 g g.2)⟩
  obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hτD, -⟩ := hC
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨g, hg, hdiag, -⟩ := Sec4.isTypeC_conj_std hK hq hD
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hd₁ : g * diagTau hτ * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (Sec4.diagTau_mem_slPi hπ hq' hτ)
  have hdw : g * swapTwoThree * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    Sec4.conj_mem_slPi hπ hg (swapTwoThree_mem_slPi hπ)
  set P₁ : projImage (slPi π 3 (p ^ f) K) := Sec4.projOf _ ⟨_, hd₁⟩ with hP₁
  set Pw : projImage (slPi π 3 (p ^ f) K) := Sec4.projOf _ ⟨_, hdw⟩ with hPw
  set θ := aschbacherSolvableCore 3 L with hθ
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  set y₁ : L ⧸ θ := e.symm P₁ with hy₁
  set yw : L ⧸ θ := e.symm Pw with hyw
  have he₁ : ((e y₁ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * diagTau hτ * g⁻¹) := by
    rw [hy₁, MulEquiv.apply_symm_apply, hP₁, Sec4.coe_projOf]
  have hew : ((e yw : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g * swapTwoThree * g⁻¹) := by
    rw [hyw, MulEquiv.apply_symm_apply, hPw, Sec4.coe_projOf]
  have hfixDiag : ∀ (z : L ⧸ θ) (a b c' : Kˣ),
      ((e z : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * diagUnits a b c' * g⁻¹) →
      ∀ (x : G) (hx : x ∈ E), Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hEN hx⟩) z = z := by
    intro z a b c' hz x hx
    obtain ⟨y, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hEN hx, hx, rfl⟩)
    obtain ⟨l, s, t, -, -, hl⟩ := hdiag y hyD
    apply e.injective
    apply Subtype.ext
    rw [hyz z, hz, ← map_inv, ← map_mul, ← map_mul, conj_diag_comm hl]
  have hfix₁ := hfixDiag y₁ (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1
    (by rw [he₁, Sec4.diagTau_eq_diagUnits hτ hτ0])
  have hy₁3 : y₁ ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, he₁, ← map_pow, conj_pow,
      Sec4.diagTau_pow_three, mul_one, mul_inv_cancel, map_one]
  have hy₁1 : y₁ ≠ 1 := by
    intro h1
    have h2 : ((e y₁ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) = 1 := by
      rw [h1, map_one, Subgroup.coe_one]
    rw [he₁, map_mul, map_mul, map_inv] at h2
    apply mk_diagTau_ne_one hτ hτ1
    calc ProjGenLinGroup.mk (diagTau hτ) = (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹) *
          ProjGenLinGroup.mk g := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨n, hnE, hny⟩ := exists_mem_of_fixed hEN hE3 hEmax hy₁3 hfix₁
  have hn1 : (n : G) ≠ 1 := by
    intro h1
    apply hy₁1
    rw [← hny, show n = 1 from Subtype.ext h1, QuotientGroup.mk_one]
  obtain ⟨w₂, hw₂⟩ := QuotientGroup.mk_surjective yw
  have hw₂E : ∀ x ∈ E, (w₂ : G) * x * (w₂ : G)⁻¹ ∈ E ⊔ θG := by
    intro x hx
    set σ := L.normalizerMonoidHom ⟨x, hEN hx⟩ with hσ
    set k : L := w₂ * (σ w₂)⁻¹ with hk
    have hkG : (k : G) = (w₂ : G) * (x * (w₂ : G) * x⁻¹)⁻¹ := rfl
    obtain ⟨y, hyD, hyz⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hEN hx, hx, rfl⟩)
    obtain ⟨l, s, t, hs, ht, hl⟩ := hdiag y hyD
    have hs3 : s ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hs
    have ht3 : t ^ 3 = 1 := (mem_rootsOfUnity _ _).mp ht
    have hmk : (k : L ⧸ θ) = yw * (Sec4.thetaQuotMulAut L σ yw)⁻¹ := by
      rw [hk, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← Sec4.thetaQuotMulAut_mk, hw₂]
    have hek : ((e (k : L ⧸ θ) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (g * diagUnits 1 (t * s⁻¹) (s * t⁻¹) * g⁻¹) := by
      rw [hmk, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyz yw, hew,
        ← comm_swapTwoThree_conj hl]
      simp only [map_mul, map_inv]
      group
    have hk3 : (k : L ⧸ θ) ^ 3 = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, hek, ← map_pow, conj_pow,
        diagUnits_pow_three (one_pow 3) (by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul])
          (by rw [mul_pow, inv_pow, hs3, ht3, inv_one, one_mul]),
        mul_one, mul_inv_cancel, map_one]
    obtain ⟨n', hn'E, hn'k⟩ := exists_mem_of_fixed hEN hE3 hEmax hk3 (hfixDiag _ _ _ _ hek)
    have hnk' : (n' : G)⁻¹ * (k : G) ∈ θG := (mk_eq_mk_iff n' k).mp hn'k
    have hθx : x⁻¹ * ((n' : G)⁻¹ * (k : G)) * x⁻¹⁻¹ ∈ θG :=
      conj_mem_theta_of_normalizer (inv_mem (hEN hx)) hnk'
    have heq : (w₂ : G) * x * (w₂ : G)⁻¹ =
        ((n' : G) * x) * (x⁻¹ * ((n' : G)⁻¹ * (k : G)) * x⁻¹⁻¹) := by
      rw [hkG]
      group
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hn'E hx)) (Subgroup.mem_sup_right hθx)
  obtain ⟨t, htL, htN, htw⟩ := exists_mem_normalizer_of_conj_mem hEN hEp w₂.2 hw₂E
  have htw' : ((⟨t, htL⟩ : L) : L ⧸ θ) = yw := by
    rw [← hw₂, mk_eq_mk_iff]
    refine inv_mul_mem_theta_of_mul_inv_mem htL ?_
    have := inv_mem htw
    rwa [mul_inv_rev, inv_inv] at this
  refine ⟨n, t, hnE, n.2, hn1, htL, htN, ?_⟩
  have hinvbar : yw * y₁ * yw⁻¹ = y₁⁻¹ := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, hew, he₁]
    have h1 := mk_swapTwoThree_conj_diagTau (K := K) hτ
    simp only [map_mul, map_inv] at h1 ⊢
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk swapTwoThree * (ProjGenLinGroup.mk g)⁻¹ *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g)⁻¹) *
          (ProjGenLinGroup.mk g * ProjGenLinGroup.mk swapTwoThree * (ProjGenLinGroup.mk g)⁻¹)⁻¹ =
        ProjGenLinGroup.mk g * (ProjGenLinGroup.mk swapTwoThree * ProjGenLinGroup.mk (diagTau hτ) *
          (ProjGenLinGroup.mk swapTwoThree)⁻¹) * (ProjGenLinGroup.mk g)⁻¹ := by group
      _ = (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (diagTau hτ) *
          (ProjGenLinGroup.mk g)⁻¹)⁻¹ := by rw [h1]; group
  have htd : t * (n : G) * t⁻¹ ∈ L := mul_mem (mul_mem htL n.2) (inv_mem htL)
  have hmk : ((⟨t * (n : G) * t⁻¹, htd⟩ : L) : L ⧸ θ) = ((n⁻¹ : L) : L ⧸ θ) := by
    have e1 : (⟨t * (n : G) * t⁻¹, htd⟩ : L) = ⟨t, htL⟩ * n * (⟨t, htL⟩)⁻¹ := rfl
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, htw', hny,
      QuotientGroup.mk_inv, hny, hinvbar]
  have hmem : (t * (n : G) * t⁻¹)⁻¹ * (n : G)⁻¹ ∈ E ⊓ θG := by
    refine Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem ((Subgroup.mem_normalizer_iff.mp htN _).mp hnE)) (inv_mem hnE), ?_⟩
    exact (mk_eq_mk_iff ⟨t * (n : G) * t⁻¹, htd⟩ n⁻¹).mp hmk
  rw [inf_theta_eq_bot hEp L, Subgroup.mem_bot] at hmem
  calc t * (n : G) * t⁻¹ = t * (n : G) * t⁻¹ * ((t * (n : G) * t⁻¹)⁻¹ * (n : G)⁻¹) := by
        rw [hmem, mul_one]
    _ = (n : G)⁻¹ := by group

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
