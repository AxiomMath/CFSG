module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUModel
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

private theorem blockMat_three_zero_eq_blkMat_L3MxU5 {F : Type} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 3 0 M =
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat M 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.Phan.blockMat_apply,
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat]

private theorem blockEmb_mem_sl2Block_L3MxU5 {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ 1) ^ 2)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F)
    (A : CFSG.ClassicalInvolution.Phan.Su F p 1 2) :
    ((CFSG.ClassicalInvolution.Phan.blockEmb F p 1 3 2 0 (show 0 + 2 ≤ 3 by norm_num) A :
        CFSG.ClassicalInvolution.Phan.Su F p 1 3) : GL (Fin 3) F) ∈
      sl2BlockL3 (GU2Stated (p ^ 1) F) := by
  have hA2 : (A : GL (Fin 2) F) ∈ StatedSU 2 (p ^ 1) F := by
    rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 2]
    exact A.2
  have hmem := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h1).mp hA2
  have hdet : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := hmem.1
  rw [sl2BlockL3]
  refine Subgroup.mem_map.mpr ⟨(A : GL (Fin 2) F), ?_, ?_⟩
  · have hGU : (A : GL (Fin 2) F) ∈ GU2Stated (p ^ 1) F :=
      (CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_GU2Stated_iff h1).mpr hmem.2
    have hdetK : (A : GL (Fin 2) F) ∈
        (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker :=
      MonoidHom.mem_ker.mpr (Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact hdet))
    exact Subgroup.mem_inf.mpr ⟨hGU, hdetK⟩
  · apply Units.ext
    rw [CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.coe_blk, hdet, inv_one]
    exact (blockMat_three_zero_eq_blkMat_L3MxU5 _).symm

theorem factB_std_statedSU {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = (p ^ 1) ^ 2) {G : Type} [Group G] (ψ : ↥(StatedSU 3 (p ^ 1) F) →* G)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ 1) F))
    (hN : ψ.range.Normal) (hC : ∀ v : G, (∀ n ∈ ψ.range, v * n = n * v) → v = 1) :
    ∀ v : G, v * v = 1 →
      (∀ A : ↥(StatedSU 3 (p ^ 1) F), (A : GL (Fin 3) F) ∈ sl2BlockL3 (GU2Stated (p ^ 1) F) →
        v * ψ A = ψ A * v) →
      v = 1 ∨ ∃ A : ↥(StatedSU 3 (p ^ 1) F), (A : GL (Fin 3) F) = negDiag3 F ∧ v = ψ A := by
  intro v hv2 hvA
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, by rw [hF]; ring⟩
  haveI : CharP F p := h1.charP
  have hp2 : p ≠ 2 := by omega
  have hq : 5 ≤ p ^ 1 := by rw [pow_one]; exact hp5
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  have h23 : (2 : ℕ) ≤ 3 := by norm_num
  let eU : CFSG.ClassicalInvolution.Phan.Su F p 1 3 ≃* ↥(StatedSU 3 (p ^ 1) F) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3)
  set θ : CFSG.ClassicalInvolution.Phan.Su F p 1 3 →* G := ψ.comp eU.toMonoidHom with hθ
  have hθapply : ∀ s, θ s = ψ (eU s) := fun s => rfl
  have hθrange : θ.range = ψ.range := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨eU s, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨eU.symm a, by rw [hθapply, MulEquiv.apply_symm_apply]⟩
  have hθker : θ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p 1 3) := by
    intro y hy
    have hy' : eU y ∈ ψ.ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy)
    have hc := CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _ (hker hy')
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro z
    apply eU.injective
    rw [map_mul, map_mul]
    exact hc (eU z)
  set R : Subgroup (CFSG.ClassicalInvolution.Phan.Su F p 1 3) :=
    CFSG.ClassicalInvolution.Models.rootSU2 F p 1 h23 with hR
  set x : CFSG.ClassicalInvolution.Phan.Su F p 1 3 :=
    CFSG.ClassicalInvolution.Models.rootInvSU F p 1 h23 with hx
  have hRmem : R ∈ CFSG.ClassicalInvolution.Models.longRootSetU (K := F) (p := p) (f := 1) h23 := by
    rw [hR, CFSG.ClassicalInvolution.Models.mem_longRootSetU_iff]
    refine ⟨1, ?_⟩
    ext y
    simp [Subgroup.mem_map]
  have hxR : x ∈ R := by
    rw [hR, hx]
    exact CFSG.ClassicalInvolution.Models.rootInvSU_mem_rootSU2 (K := F) (p := p) (f := 1) h23
  have hxc : ∀ r ∈ R, x * r = r * x := by
    intro r hr
    rw [hR, CFSG.ClassicalInvolution.Models.rootSU2, MonoidHom.mem_range] at hr
    obtain ⟨A, rfl⟩ := hr
    rw [hx, CFSG.ClassicalInvolution.Models.rootInvSU, ← map_mul, ← map_mul,
      CFSG.ClassicalInvolution.Models.negOneSU_comm]
  have hx1 : x ≠ 1 := by
    intro hxeq
    apply CFSG.ClassicalInvolution.Models.negOneSU_ne_one (K := F) (p := p) (f := 1) h2F
    apply CFSG.ClassicalInvolution.Phan.blockEmb_injective (K := F) (p := p) (f := 1)
      (show 0 + 2 ≤ 3 by norm_num)
    rw [map_one]
    exact hxeq
  have hxx : x * x = 1 := by
    rw [hx, CFSG.ClassicalInvolution.Models.rootInvSU, ← map_mul,
      CFSG.ClassicalInvolution.Models.negOneSU_mul_self, map_one]
  have hmat3 : (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![-1, -1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hex : ((eU x : ↥(StatedSU 3 (p ^ 1) F)) : GL (Fin 3) F) = negDiag3 F := by
    apply Units.ext
    have hx3 := CFSG.ClassicalInvolution.Disconnected.AschTight.S19K.coe_rootInvSU_three
      (K := F) (p := p) (f := 1)
    rw [CFSG.RankThree.SubgroupLists.coe_negDiag3, ← hmat3]
    exact hx3
  have hθN : θ.range.Normal := by rw [hθrange]; exact hN
  have hv : v ∈ Subgroup.normalizer ((θ.range : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hθN]
    exact Subgroup.mem_top v
  have hvR : ∀ r ∈ R, v * θ r = θ r * v := by
    intro r hr
    rw [hR, CFSG.ClassicalInvolution.Models.rootSU2, MonoidHom.mem_range] at hr
    obtain ⟨A, rfl⟩ := hr
    exact hvA (eU (CFSG.ClassicalInvolution.Phan.blockEmb F p 1 3 2 0
      (show 0 + 2 ≤ 3 by norm_num) A)) (blockEmb_mem_sl2Block_L3MxU5 hF h1 A)
  rcases CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU.psu3_involution_fund hF hp2 hq θ hθker
      hRmem hxR hxc hx1 hv hv2 hvR with hall | hall
  · left
    apply hC v
    intro n hn
    rw [← hθrange] at hn
    exact hall n hn
  · right
    have hvx : v * θ x = 1 := by
      apply hC (v * θ x)
      intro n hn
      rw [← hθrange] at hn
      exact hall n hn
    have hθxx : θ x * θ x = 1 := by
      rw [← map_mul, hxx, map_one]
    have hvθ : v = θ x := by
      calc v = v * (θ x * θ x) := by rw [hθxx, mul_one]
        _ = (v * θ x) * θ x := by rw [mul_assoc]
        _ = θ x := by rw [hvx, one_mul]
    exact ⟨eU x, hex, hvθ⟩

end CFSG.Quasithin.H13
