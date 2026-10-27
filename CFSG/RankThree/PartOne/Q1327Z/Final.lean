module

public import CFSG.RankThree.PartOne.Q1327Z.Glue
public import CFSG.RankThree.PartOne.Q1327Z.Refl
public import CFSG.RankThree.PartOne.Q1327T.MFinal
import CFSG.RankThree.PartOne.KF.R9Final
import CFSG.RankThree.PartOne.S12.Sec127

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.Q1327C CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Neg

variable {G : Type} [Group G]

theorem eq_one_of_neg_mem {E : Subgroup G} {Γ : Subgroup (MulAut E)} {Γ₀ : Type*} [Group Γ₀]
    (e : ↥Γ ≃* Γ₀) (hΓ₀ : ∀ σ : Γ₀, (∀ τ : Γ₀, τ * σ = σ * τ) → σ = 1) {φ : MulAut E}
    (hφ : φ ∈ Γ) (hneg : ∀ x : E, φ x = x⁻¹) : φ = 1 := by
  have hcomm : ∀ g : ↥Γ, g * ⟨φ, hφ⟩ = ⟨φ, hφ⟩ * g := by
    intro g
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    show (g : MulAut E) (φ x) = φ ((g : MulAut E) x)
    rw [hneg, hneg, map_inv]
  have h1 : e ⟨φ, hφ⟩ = 1 := by
    apply hΓ₀
    intro τ
    obtain ⟨g, rfl⟩ := e.surjective τ
    rw [← map_mul, ← map_mul, hcomm g]
  have h2 : (⟨φ, hφ⟩ : ↥Γ) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end Neg

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem false_of_neg_one (H : Hyp G p A c L E f r R s s' zs)
    (hneg : ∀ x : E, (1 : MulAut E) x = x⁻¹) : False := by
  have h := H.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := Sec12Three.five_le h; omega
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have h1 := hneg ⟨c, hcE⟩
  rw [MulAut.one_apply] at h1
  have h2 : c = c⁻¹ := congrArg Subtype.val h1
  have hc2 : c ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h2
  exact h.c_ne_one (eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 hc2
    (Sec12Three.pow_eq_one_of_mem_A h h.c_mem))

theorem kf1327M_of_refl
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (hSLB : N143.SectionListBound) (hI613 : N143.Item613ListIdx)
    (hBridge : N143.EvenListBridge) (hLS : KF1327S) (hLP5 : KF1327P5) (hRefl : KF1327Refl) :
    KF1327M := by
  intro G _ _ p A c L E f r R s s' zs Jc H hJ φ hφ
  classical
  by_contra hcon
  push Not at hcon
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  obtain ⟨a, N, A₀, S, ha1, ha2, hN1, hN2, hN3, hN4, hA₀1, hA₀2, hA₀3, hS1, hS2, hS3, hS4, hS5⟩ :=
    hLS G p A c L E f r R s s' zs H
  have d : SDatum p E R s f a N A₀ S :=
    ⟨ha1, ha2, hN1, hN2, hN3, hN4, hA₀1, hA₀2, hA₀3, hS1, hS2, hS3, hS4, hS5⟩
  have hEven := evenLie_Jc hGA hS hRe hTwo hFull hSLB hI613 hBridge hLP5 H hJ d
  have hbase := t123Base_Jc hGA hS hRe hTwo hFull H hJ d.A₀_le d.A₀_elem d.A₀_card d.S_le d.S_ne
    d.S_two d.A₀_norm d.comm
  have hsolv : Group.IsSolvable ↥(torusImage E Jc) :=
    isSolvable_of_le_torusWeyl H (Sec127.torusImage_le_torusWeyl E Jc)
  have hirr := Jc_irreducible hGA H hJ
  have hsT : s ∈ torusImage E Jc := mem_torusImage_Jc H hJ (mem_clsOf_self p E s)
  have hKJ : kZero p E s ≤ Jc := hJ.K_le s (mem_clsOf_self p E s)
  have hKle : kZero p E s ≤ Jc ⊓ Subgroup.centralizer (autFixedInG E s : Set G) :=
    le_inf hKJ (kZero_le_centralizer_fixed p E s)
  have hKθ := kZero_mem_thetaComponents_inf hp (KFAt.toLiftAt H.hKs).1 hKJ
  have hdat : ∃ (t : MulAut ↥E) (K : Subgroup G) (g : ℕ), t ∈ torusImage E Jc ∧
      IsAutReflection p E t ∧ K ≤ Jc ⊓ Subgroup.centralizer (autFixedInG E t : Set G) ∧
      K.subgroupOf (Jc ⊓ Subgroup.centralizer (autFixedInG E t : Set G)) ∈
        thetaComponents p ↥(Jc ⊓ Subgroup.centralizer (autFixedInG E t : Set G)) ∧
      autMovedInG E t ≤ K ∧ StatedClassicalModel ↥K .PSL 2 2 g ∧ 2 ≤ g ∧ p ∣ 2 ^ g + 1 :=
    ⟨s, kZero p E s, f, hsT, H.hs.1, hKle, hKθ, H.hKs.2.2.2.1, H.hKs.2.1, H.hf2, H.hpf⟩
  have h7 : p ≠ 7 := by
    rintro rfl
    exact seven_not_dvd_two_pow_add_one f H.hpf
  have hzs : zs ∈ torusImage E Jc := zs_mem_torusImage hGA H hJ hφ hcon
  have hcmov : c ∈ autMovedInG E zs := by
    rw [H.hmov]
    exact Subgroup.mem_zpowers c
  have hreflFalse : (RowModel p Jc 10 ∨ Sp6Cell p Jc ∨ Om8Cell p Jc) → False := fun ho =>
    hRefl.false_of_commute hbase ho hzs H.hzs.1 hcmov h.c_ne_one
      fun y₁ h₁ y₂ h₂ => conj_c_commute H hJ h₁ h₂
  rcases bClassify hGA CTP.spinRankFour PartTwo.Census.Exceptional.exceptionalRankFour hbase h7
    hEven with h9 | h10 | h12 | hM3
  ·
    obtain ⟨f9, K9, hKf9, ⟨C⟩⟩ := exists_r9ctx (psuFourEvenCenterTrivial_of_multipliers hGA)
      (Q1327C.T123Base.toCore hbase) h9
    have hKfin : Finite K9 := C.hU.finite
    have hζ := C.exists_unit_root
    have hp2 : p ≠ 2 := by have := C.h5; omega
    have S := C.toSymCtx
    have hφ1 : φ = 1 := eq_one_of_neg_mem (S.weylEquiv C.hp hp2 hζ) perm_four_center hφ hcon
    exact false_of_neg_one H (fun x => by rw [← hφ1]; exact hcon x)
  · exact hreflFalse (Or.inl h10)
  ·
    obtain ⟨e⟩ := (rowData_core_twelve (Q1327C.T123Base.toCore hbase) h12).2.2.1
    have hs5 : Group.IsSolvable (Equiv.Perm (Fin 5)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact Equiv.Perm.not_isSolvable_fin_5 hs5
  · rcases hM3 with hm | hm | hm | hm
    · exact false_of_l4_split hbase hdat hm
    · exact hreflFalse (Or.inr (Or.inl hm))
    · exact hreflFalse (Or.inr (Or.inr hm))
    · by_cases hp5' : p = 5
      · subst hp5'
        obtain ⟨f', hf1, -, h25, hcl⟩ := hm
        obtain ⟨t, -, -, htT, htR, -⟩ := hdat
        refine false_of_u5_five hbase hirr ⟨t, htT, htR⟩ ⟨f', hf1, ?_, hcl⟩
        rcases h25 with hne | h25
        · exact absurd rfl hne
        · exact h25
      · exact false_of_u5_ne_five hbase hp5' hm

theorem kf1327Q_of_remR
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (hSLB : N143.SectionListBound) (hI613 : N143.Item613ListIdx)
    (hBridge : N143.EvenListBridge) (hP5 : KF1327P5) (hB : KF1327BM) (hRem : Row8U3Inspection ∧
        KF1327Refl) :
    K1327.KF1327Q :=
  kf1327Q_of_remM hGA hS hRe hTwo hFull hSLB hI613 hBridge hP5 hB
    ⟨hRem.1, kf1327M_of_refl hGA hS hRe hTwo hFull hSLB hI613 hBridge
      (kf1327S_of_inspectionM hGA hS hSLB hRem.1) hP5 hRem.2⟩

end Main

end CFSG.RankThree.PartOne.Q1327Z
