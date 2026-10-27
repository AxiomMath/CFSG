module

public import CFSG.Quasithin.H13.A7BlkAct
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206d
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre mem_ptPre ptCore ptCore_le_ptPre ptHom ptHom_surjective
  ker_ptHom isSimpleGroup_stabilizer)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (four_le_pRank_imp_mem_sigma
  isStronglyPEmbedded_of_clause_one)

variable {G : Type} [Group G]

@[expose] def uc22s206gExt (i : Fin 9) : Equiv.Perm (Fin 8) →* Equiv.Perm (Fin 9) :=
  Equiv.Perm.extendDomainHom (Fin.succAboveEmb i).toEquivRange

theorem uc22s206gExt_apply (i : Fin 9) (σ : Equiv.Perm (Fin 8)) :
    uc22s206gExt i σ = σ.viaFintypeEmbedding (Fin.succAboveEmb i) := rfl

theorem uc22s206gExt_self (i : Fin 9) (σ : Equiv.Perm (Fin 8)) : uc22s206gExt i σ i = i := by
  rw [uc22s206gExt_apply]
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨k, hk⟩
  exact Fin.succAbove_ne i k hk

theorem uc22s206gExt_succAbove (i : Fin 9) (σ : Equiv.Perm (Fin 8)) (k : Fin 8) :
    uc22s206gExt i σ (i.succAbove k) = i.succAbove (σ k) := by
  rw [uc22s206gExt_apply]
  exact Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.succAboveEmb i) k

theorem uc22s206gExt_sign (i : Fin 9) (σ : Equiv.Perm (Fin 8)) :
    Equiv.Perm.sign (uc22s206gExt i σ) = Equiv.Perm.sign σ := by
  rw [uc22s206gExt_apply]
  exact Equiv.Perm.viaFintypeEmbedding_sign σ _

@[expose] def uc22s206gEmb (i : Fin 9) :
    alternatingGroup (Fin 8) →* ↥(MulAction.stabilizer (alternatingGroup (Fin 9)) i) :=
  (((uc22s206gExt i).comp (alternatingGroup (Fin 8)).subtype).codRestrict
      (alternatingGroup (Fin 9)) fun σ => by
        rw [Equiv.Perm.mem_alternatingGroup, MonoidHom.comp_apply, Subgroup.coe_subtype,
          uc22s206gExt_sign]
        exact Equiv.Perm.mem_alternatingGroup.mp σ.2).codRestrict _ fun σ => by
    rw [MulAction.mem_stabilizer_iff]
    exact uc22s206gExt_self i σ

theorem uc22s206gEmb_coe (i : Fin 9) (σ : alternatingGroup (Fin 8)) :
    (((uc22s206gEmb i σ : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9))) =
      uc22s206gExt i σ := rfl

theorem uc22s206gEmb_injective (i : Fin 9) : Function.Injective (uc22s206gEmb i) := by
  intro σ τ h
  have h1 := congrArg (fun z : ↥(MulAction.stabilizer (alternatingGroup (Fin 9)) i) =>
    ((z : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9))) h
  simp only [uc22s206gEmb_coe] at h1
  exact Subtype.ext (Equiv.Perm.extendDomainHom_injective _ h1)

theorem uc22s206gEmb_fix (i : Fin 9) (σ : alternatingGroup (Fin 8)) {k : Fin 8}
    (hk : (σ : Equiv.Perm (Fin 8)) k = k) :
    ((uc22s206gEmb i σ : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) (i.succAbove k) =
      i.succAbove k := by
  rw [uc22s206gEmb_coe, uc22s206gExt_succAbove, hk]

@[expose] def uc22s206gC (i : Fin 9) : alternatingGroup (Fin 9) :=
  ⟨Equiv.swap i (i.succAbove 1) * Equiv.swap i (i.succAbove 0), by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Fin.ne_succAbove i 1), Equiv.Perm.sign_swap (Fin.ne_succAbove i 0)]
    decide⟩

theorem uc22s206gC_apply (i : Fin 9) :
    ((uc22s206gC i : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) i = i.succAbove 0 := by
  show (Equiv.swap i (i.succAbove 1) * Equiv.swap i (i.succAbove 0)) i = i.succAbove 0
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
    (Fin.succAbove_ne i 0) (Fin.succAbove_right_injective.ne (by decide))]

theorem uc22s206g_X0_Y0 : uc22s206dX0 * uc22s206dY0 ≠ uc22s206dY0 * uc22s206dX0 := by
  decide

theorem uc22s206g_lift [Finite G] {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) (i : Fin 9) {Γ : Type*}
    [Group Γ] (ρ : ↥(ptCore α i) →* Γ) (hρ : ρ.ker ≤ CFSG.pCore 2 ↥(ptCore α i)) :
    ∃ x y : ↥(ptCore α i), ptHom α i x = uc22s206gEmb i uc22s206dX0 ∧
      ptHom α i y = uc22s206gEmb i uc22s206dY0 ∧ orderOf x = 3 ∧ orderOf y = 7 ∧
      x * y * x⁻¹ = y ^ 2 ∧ ∃ E : Subgroup Γ, E ≤ ρ.range ∧ CFSG.Open.IsElemAbelian 2 E ∧
        Nat.card E = 8 ∧ ρ y ∈ normalizer (E : Set Γ) ∧
          ∀ e ∈ E, ρ y * e * (ρ y)⁻¹ = e → e = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := ker_ptHom α hα hker (by norm_num) i
  have hinj := uc22s206gEmb_injective i
  refine uc22s206d_lift (ptHom α i) (ptHom_surjective α hα (by norm_num) i)
    (by rw [hk]; exact CFSG.pCore_isPGroup) ρ (by rw [hk]; exact hρ)
    (by rw [orderOf_injective _ hinj, uc22s206d_orderOf_X0])
    (by rw [orderOf_injective _ hinj, uc22s206d_orderOf_Y0])
    (by rw [← map_inv, ← map_mul, ← map_mul, uc22s206d_conj_X0_Y0, map_pow])
    (uc22s206d_isPGroup_E0.map _)
    (le_normalizer_map _ (mem_map_of_mem _ uc22s206d_mem_normalizer_E0)) ?_
  obtain ⟨e, he, hne⟩ := uc22s206d_not_centralizer_E0
  refine ⟨_, mem_map_of_mem _ he, fun h => hne (hinj ?_)⟩
  rw [map_mul, map_mul, map_inv]
  exact h

theorem uc22s206g_not_isSolvable [Finite G] {L M : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α) {i : Fin 9}
    (hLM : L ⊓ M = ptPre α i) : ¬ Group.IsSolvable ↥M := by
  intro hM
  have hKM : ptCore α i ≤ M := by
    refine (ptCore_le_ptPre α i).trans ?_
    rw [← hLM]
    exact inf_le_right
  haveI : Group.IsSolvable ↥(ptCore α i) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKM)
  haveI : Group.IsSolvable ↥(MulAction.stabilizer (alternatingGroup (Fin 9)) i) :=
    Group.isSolvable_of_surjective (ptHom_surjective α hα (by norm_num) i)
  haveI := isSimpleGroup_stabilizer (n := 9) (by norm_num) i
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable
    (G := ↥(MulAction.stabilizer (alternatingGroup (Fin 9)) i))).mpr inferInstance
  apply uc22s206g_X0_Y0
  apply uc22s206gEmb_injective i
  rw [map_mul, map_mul]
  exact hcomm _ _

theorem uc22s206g_not_strongly {L M : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) {i : Fin 9} (hLM : L ⊓ M = ptPre α i)
    {w c : alternatingGroup (Fin 9)} (hwi : (w : Equiv.Perm (Fin 9)) i = i)
    (hwc : (w : Equiv.Perm (Fin 9)) ((c : Equiv.Perm (Fin 9)) i) = (c : Equiv.Perm (Fin 9)) i)
    (hci : (c : Equiv.Perm (Fin 9)) i ≠ i) : ¬ IsStronglyPEmbedded (orderOf w) M := by
  rintro ⟨-, -, hSE⟩
  obtain ⟨g, rfl⟩ := hα c
  obtain ⟨z, rfl⟩ := hα w
  have hmemP : ∀ h : ↥L, (α h : Equiv.Perm (Fin 9)) i = i → (h : G) ∈ M := by
    intro h hh
    have : (h : G) ∈ ptPre α i := (mem_ptPre α).mpr ⟨h.2, hh⟩
    rw [← hLM] at this
    exact this.2
  have hgM : (g : G) ∉ M := by
    intro hg
    have : (g : G) ∈ L ⊓ M := ⟨g.2, hg⟩
    rw [hLM, mem_ptPre] at this
    obtain ⟨_, hgi⟩ := this
    exact hci hgi
  refine hSE g hgM ?_
  have hgz : ((g⁻¹ * z * g : ↥L) : G) ∈ M := by
    apply hmemP
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hwc]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have hmem : (z : G) ∈ M ⊓ M.map (MulAut.conj (g : G)).toMonoidHom := by
    refine ⟨hmemP z hwi, ⟨_, hgz, ?_⟩⟩
    simp [mul_assoc]
  calc orderOf (α z) ∣ orderOf z := orderOf_map_dvd α z
    _ = orderOf (z : G) := (Subgroup.orderOf_coe z).symm
    _ = orderOf (⟨z, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj (g : G)).toMonoidHom)) :=
        (Subgroup.orderOf_mk _ _).symm
    _ ∣ _ := orderOf_dvd_natCard _

theorem uc22s206g_coprime [Finite G] (hU : uniqueFourUnique G) {M L : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) {i : Fin 9} (hLM : L ⊓ M = ptPre α i) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h3 : 3 < CFSG.Open.pRank p M) :
    p ∈ uniqueFourSigma M ∧ IsStronglyPEmbedded p M ∧ p ≠ 3 ∧ p ≠ 7 := by
  have hσ : p ∈ uniqueFourSigma M := four_le_pRank_imp_mem_sigma hU hM hp hp2 h3
  obtain ⟨-, hM0, -, P, -, -, hcl⟩ := (hU M hM ⟨p, hσ⟩).1 p hσ
  have hSE : IsStronglyPEmbedded p M := by
    rcases hcl with ⟨hdvd, hstrong⟩ | ⟨-, hsolv, -⟩
    · exact isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
    · exact absurd hsolv (uc22s206g_not_isSolvable α hα hLM)
  have hinj := uc22s206gEmb_injective i
  have hci : ((uc22s206gC i : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) i ≠ i := by
    rw [uc22s206gC_apply]
    exact Fin.succAbove_ne i 0
  refine ⟨hσ, hSE, ?_, ?_⟩
  · rintro rfl
    have hX : orderOf (uc22s206gEmb i uc22s206dX0 : alternatingGroup (Fin 9)) = 3 := by
      rw [Subgroup.orderOf_coe, orderOf_injective _ hinj, uc22s206d_orderOf_X0]
    refine uc22s206g_not_strongly α hα hLM (w := uc22s206gEmb i uc22s206dX0)
      (uc22s206gExt_self i _) ?_ hci (hX ▸ hSE)
    rw [uc22s206gC_apply]
    exact uc22s206gEmb_fix i _ (by decide)
  · rintro rfl
    have hY : orderOf (uc22s206gEmb i uc22s206dY0 : alternatingGroup (Fin 9)) = 7 := by
      rw [Subgroup.orderOf_coe, orderOf_injective _ hinj, uc22s206d_orderOf_Y0]
    refine uc22s206g_not_strongly α hα hLM (w := uc22s206gEmb i uc22s206dY0)
      (uc22s206gExt_self i _) ?_ hci (hY ▸ hSE)
    rw [uc22s206gC_apply]
    exact uc22s206gEmb_fix i _ (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
