module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B4
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B5a
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.PSL2Table
open CFSG.RankThree.PartOne (torusWeyl torusIrreducible)
open CFSG.RankThree.PartOne.LinAlg (bsub torusWeylGL wActionGL)
open CFSG.Blueprint (LieModel)
open scoped Matrix MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Mz614

variable {G : Type} [Group G] [Finite G]

theorem c623_of_L2 (hK : UCK.K323) (m : Mz614 G) (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S))
    (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620)
    (hL : LieModel ↥m.L .PSL 2 m.r 2) : m.C623 := by
  classical
  by_contra hne
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨F, _, _, e, -, hFq⟩ :=
    CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' m.hr m.d.odd hL
  haveI : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (m.hr.odd_of_ne_two m.d.odd).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hodd
  obtain ⟨P, -, hSP_eq⟩ := exists_l2_sylow m h620 hL
  set S0 : Subgroup ↥m.L := (m.A ⊓ m.L).subgroupOf m.L
  obtain ⟨c, hc⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_psiEquiv_eq e m.hr hFq P
  set ψ := CFSG.GH74.GLS.IVK.L2Borel.psiEquiv e c with hψ
  have hψS : ∀ x : ↥m.L, x ∈ S0 ↔ ψ.symm x ∈ unipotent F := by
    intro x
    rw [hSP_eq, hc, Subgroup.mem_map_equiv]
  have hBmem : ∀ b ∈ m.A ⊓ m.L, ∃ t : F, b = ((ψ (PSL2Table.mk (unip t)) : ↥m.L) : G) := by
    intro b hb
    have h1 : ψ.symm ⟨b, hb.2⟩ ∈ unipotent F := (hψS ⟨b, hb.2⟩).1 hb
    obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists _).1 h1
    refine ⟨t, ?_⟩
    rw [← ht, MulEquiv.apply_symm_apply]
  have hUmem : ∀ t : F, ((ψ (PSL2Table.mk (unip t)) : ↥m.L) : G) ∈ m.A ⊓ m.L := by
    intro t
    have h1 : ψ (PSL2Table.mk (unip t)) ∈ S0 := by
      rw [hψS, MulEquiv.symm_apply_apply]
      exact mk_unip_mem_unipotent t
    exact h1
  have hTconj : ∀ (a : Fˣ) (t : F),
      ((ψ (PSL2Table.mk (diag a)) : ↥m.L) : G) * ((ψ (PSL2Table.mk (unip t)) : ↥m.L) : G) *
          ((ψ (PSL2Table.mk (diag a)) : ↥m.L) : G)⁻¹ = ((ψ (PSL2Table.mk (unip ((a : F) ^ 2 * t))) : ↥m.L) : G) := by
    intro a t
    rw [coe_conj_L, ← map_inv, ← map_mul, ← map_mul, mk_conj, diag_conj_unip]
  have hTB : ∀ a : Fˣ, ∀ b ∈ m.A ⊓ m.L,
      ((ψ (PSL2Table.mk (diag a)) : ↥m.L) : G) * b * ((ψ (PSL2Table.mk (diag a)) : ↥m.L) : G)⁻¹ ∈ m.A ⊓ m.L := by
    intro a b hb
    obtain ⟨t, rfl⟩ := hBmem b hb
    rw [hTconj]
    exact hUmem _
  have hTW : ∀ a : Fˣ, ((ψ (PSL2Table.mk (diag a)) : ↥m.L) : G) ∈ m.W := fun a =>
    mem_W_of_mem_L h620 (ψ (PSL2Table.mk (diag a))).2 (hTB a)
  have h621 : m.C621 := c621_of_L2 m h620 hL
  obtain ⟨a, ha⟩ : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    have hq : Fintype.card F = m.r ^ 2 := by rw [← Nat.card_eq_fintype_card, hFq]
    rw [hq]
    obtain ⟨k, hk⟩ := m.hr.odd_of_ne_two m.d.odd
    rw [hk]
    ring_nf
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha
    exact one_ne_zero (neg_eq_zero.1 ha)
  set a' : Fˣ := Units.mk0 a ha0 with ha'
  have ha2 : (a' : F) ^ 2 = -1 := by rw [ha', Units.val_mk0, sq, ← ha]
  set y : G := ((ψ (PSL2Table.mk (diag a')) : ↥m.L) : G) with hy
  have hyB : ∀ b ∈ m.A ⊓ m.L, y * b * y⁻¹ = b ^ (m.r - 1) := by
    intro b hb
    have hbr : b ^ m.r = 1 := m.isElemAbelian_A.2 b hb.1
    have hinvb : b ^ (m.r - 1) = b⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel m.hr.one_lt.le, hbr]
    rw [hinvb]
    obtain ⟨t, rfl⟩ := hBmem b hb
    rw [hy, hTconj, ha2, neg_one_mul, ← unip_neg, map_inv, map_inv, Subgroup.coe_inv]
  have hs : (m.r - 1) % m.r ≠ 1 := by
    rw [Nat.mod_eq_of_lt (Nat.sub_lt m.hr.pos one_pos)]
    have := m.hr.two_le
    have := m.d.odd
    omega
  have hyLW : y ∈ m.L ⊓ m.W := ⟨(ψ (PSL2Table.mk (diag a'))).2, hTW a'⟩
  have htorus := m.torusIrreducible_A h69 h620 h621 hyLW hs hyB hne
  obtain ⟨f⟩ := m.exists_coords_A
  have hirr := m.irredGL3_torusWeylGL f htorus
  have hcard := m.not_dvd_card_torusWeylGL f h69
  have hZ1 := m.finrank_bsub_Z f
  let τ : splitTorus F →* GL (Fin 3) (ZMod m.r) :=
    { toFun := fun d => wActionGL f ⟨((ψ (d : PSL(2, F)) : ↥m.L) : G), by
        obtain ⟨b, hb⟩ := (mem_splitTorus_iff_exists (d : PSL(2, F))).1 d.2
        rw [hb]
        exact hTW b⟩
      map_one' := by
        rw [← map_one (wActionGL f)]
        congr 1
        apply Subtype.ext
        simp
      map_mul' := fun d₁ d₂ => by
        rw [← map_mul (wActionGL f)]
        congr 1
        apply Subtype.ext
        simp }
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨b, hb⟩ := (mem_splitTorus_iff_exists (d : PSL(2, F))).1 d.2
    have hC := (m.wActionGL_eq_one_iff f _).1 hd
    have hcomm := mem_centralizer_iff.1 hC _ (hUmem 1).1
    have h1 : ((ψ (d : PSL(2, F)) : ↥m.L) : G) * ((ψ (PSL2Table.mk (unip 1)) : ↥m.L) : G) *
        ((ψ (d : PSL(2, F)) : ↥m.L) : G)⁻¹ = ((ψ (PSL2Table.mk (unip 1)) : ↥m.L) : G) := by
      rw [← hcomm]
      group
    rw [hb, hTconj, mul_one] at h1
    have h3 : PSL2Table.mk (unip ((b : F) ^ 2)) = PSL2Table.mk (unip (1 : F)) :=
      ψ.injective (Subtype.ext h1)
    rw [mk_unip_eq_mk_unip_iff h2] at h3
    apply Subtype.ext
    rw [hb, OneMemClass.coe_one, mk_diag_eq_one_iff, h3]
  set X := τ.range with hX
  have hXle : X ≤ torusWeylGL f := by
    rintro _ ⟨d, rfl⟩
    exact m.wActionGL_mem f _
  have hXfix : ∀ x ∈ X, ∀ z ∈ bsub f m.Z, ((x : GL (Fin 3) (ZMod m.r)) :
      Matrix (Fin 3) (Fin 3) (ZMod m.r)).mulVec z = z := by
    rintro _ ⟨d, rfl⟩ z hz
    refine (m.wActionGL_mulVec_eq_iff f _ z).2 ?_
    have hzZ : ((f (Multiplicative.ofAdd z) : ↥m.A) : G) ∈ m.Z := hz
    show ((ψ (d : PSL(2, F)) : ↥m.L) : G) * _ * ((ψ (d : PSL(2, F)) : ↥m.L) : G)⁻¹ = _
    rw [← m.Z_comm_L hzZ (ψ (d : PSL(2, F))).2]
    group
  have hXcyc : IsCyclic X := by
    haveI := splitTorus_isCyclic (F := F)
    exact isCyclic_of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  have hXcard : Nat.card X = (m.r ^ 2 - 1) / 2 := by
    rw [hX, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hτinj, Subgroup.card_top,
      CFSG.GH74.GLS.IVK.L2Borel.card_splitTorus_eq h2, hFq]
  exact hcard (hK m.r m.d.odd (torusWeylGL f) hirr (bsub f m.Z) hZ1 X hXle hXfix hXcyc hXcard)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
