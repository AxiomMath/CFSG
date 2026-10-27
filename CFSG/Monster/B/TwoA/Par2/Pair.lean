
module

public import CFSG.Monster.B.TwoA.Base.PsiV

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

attribute [local instance] restAction

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem hInt_pairVec_01_0j : ∀ j : Fin 24, j ≠ 0 → j ≠ 1 → ∀ b : ZMod 2,
    hInt (pairVec 0 1 0) (pairVec 0 j b) = 2 := by
  decide +kernel

theorem rest_ne_zero (j : Rest) : (0 : Fin 24) ≠ j := fun h => j.2.1 h.symm

theorem rest_ne_one (j : Rest) : (1 : Fin 24) ≠ j := fun h => j.2.2 h.symm

theorem pairCls0_mem
    (j : Rest) (b : ZMod 2) : pairCls 0 j b ∈ vPerpL v0 := by
  change bL v0 (pairCls 0 j b) = 0
  rw [v0_eq_pairCls, pairCls, pairCls, Griess.classOf_eq_cls (pairVec_mem (by decide) 0).1,
    Griess.classOf_eq_cls (pairVec_mem (rest_ne_zero j) b).1, bL_apply]
  change QuadraticMap.polarBilin qL _ _ = 0
  rw [bL_cls, hInt_pairVec_01_0j j j.2.1 j.2.2 b]
  rfl

@[expose] def pW
    (j : Rest) (b : ZMod 2) : Wv v0 :=
  Submodule.Quotient.mk ⟨pairCls 0 j b, pairCls0_mem j b⟩

theorem pairVec_zero_add (j : Fin 24) (b : ZMod 2) :
    pairVec 0 j b + pairVec 0 1 0 = pairVec 1 j b + (2 : ℤ) • pairVec 0 1 0 := by
  funext m
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pairVec_apply, sgnI_zero]
  split_ifs <;> ring

theorem pairCls_zero_add_v0
    (j : Rest) (b : ZMod 2) : pairCls 0 j b + v0 = pairCls 1 j b := by
  rw [v0_eq_pairCls, pairCls, pairCls, pairCls,
    ← Griess.classOf_add_of_mem (pairVec_mem (rest_ne_zero j) b).1
      (pairVec_mem (by decide) 0).1, pairVec_zero_add,
    Griess.classOf_add_two_smul (pairVec_mem (rest_ne_one j) b).1 (pairVec_mem (by decide) 0).1]

theorem pairCls1_mem
    (j : Rest) (b : ZMod 2) : pairCls 1 j b ∈ vPerpL v0 := by
  rw [← pairCls_zero_add_v0]
  exact Submodule.add_mem _ (pairCls0_mem j b) (by
    change bL v0 v0 = 0
    rw [bL_apply, QuadraticMap.polar_self, Griess.qL_classOf_minVecs vMinus_zero_one_mem]
    rfl)

theorem mk_pairCls1
    (j : Rest) (b : ZMod 2) (h : pairCls 1 j b ∈ vPerpL v0) :
    (Submodule.Quotient.mk ⟨pairCls 1 j b, h⟩ : Wv v0) = pW j b := by
  rw [pW, Submodule.Quotient.eq]
  change pairCls 1 j b - pairCls 0 j b ∈ vLineL v0
  rw [mem_vLineL, ← pairCls_zero_add_v0, add_sub_cancel_left]
  exact .inr rfl

theorem pW_add_one
    (j : Rest) (b : ZMod 2) : pW j (b + 1) = pW j b + wFr := by
  rw [pW, pW, wFr, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  change pairCls 0 j (b + 1) = pairCls 0 j b + twoΩCls
  rw [add_comm (pairCls 0 j b), twoΩCls_add_pairCls (rest_ne_zero j)]

theorem pW_one
    (j : Rest) : pW j 1 = pW j 0 + wFr := by
  rw [← pW_add_one, zero_add]

theorem pW_eq_iff
    (j k : Rest) (b c : ZMod 2) : pW j b = pW k c ↔ j = k ∧ b = c := by
  constructor
  · intro he
    rw [pW, pW, Submodule.Quotient.eq] at he
    have he' : pairCls 0 j b - pairCls 0 k c ∈ vLineL v0 := he
    rcases mem_vLineL.1 he' with h0 | h0
    · have h1 := (pairCls_eq_iff (rest_ne_zero j) (rest_ne_zero k) b c).1 (sub_eq_zero.1 h0)
      rcases h1.1 with ⟨-, hjk⟩ | ⟨-, hj0⟩
      · exact ⟨Subtype.ext hjk, h1.2⟩
      · exact absurd hj0 j.2.1
    · exfalso
      have e : pairCls 0 j b = pairCls 1 k c := by
        rw [← pairCls_zero_add_v0, ← h0, add_sub_cancel]
      have h1 := (pairCls_eq_iff (rest_ne_zero j) (rest_ne_one k) b c).1 e
      rcases h1.1 with ⟨h01, -⟩ | ⟨h0k, -⟩
      · exact absurd h01 (by decide)
      · exact rest_ne_zero k h0k
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pW_injective
    (j : Rest) : Function.Injective (pW j) := fun _ _ h =>
  ((pW_eq_iff j j _ _).1 h).2

theorem pW_ne_zero
    (j : Rest) (b : ZMod 2) : pW j b ≠ 0 := by
  rw [pW, Ne, mk_eq_zero_iff]
  rintro (h0 | h0)
  · exact VisCert.zero_notMem_shortSet (h0 ▸ pairCls_mem_shortSet (rest_ne_zero j) b)
  · have := (pairCls_eq_iff (rest_ne_zero j) (by decide : (0 : Fin 24) ≠ 1) b 0).1
      (h0.trans v0_eq_pairCls)
    rcases this.1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact j.2.2 h
    · exact absurd h (by decide)

theorem pW_ne_wFr
    (j : Rest) (b : ZMod 2) : pW j b ≠ wFr := by
  rw [pW, wFr, Ne, Submodule.Quotient.eq]
  intro he
  have he' : pairCls 0 j b - twoΩCls ∈ vLineL v0 := he
  rcases mem_vLineL.1 he' with h0 | h0
  · exact twoΩCls_not_short (sub_eq_zero.1 h0 ▸ pairCls_mem_shortSet (rest_ne_zero j) b)
  · have e : pairCls 0 j b = pairCls 0 1 1 := by
      rw [← twoΩCls_add_v0, ← h0, add_sub_cancel]
    have := (pairCls_eq_iff (rest_ne_zero j) (by decide : (0 : Fin 24) ≠ 1) b 1).1 e
    rcases this.1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact j.2.2 h
    · exact absurd h (by decide)

@[expose] def restImg {p : AutPerm} (hp : p ∈ Ppair) (j : Rest) : Rest :=
  ⟨(p : Equiv.Perm (Fin 24)) j, Ppair_apply_ne hp j.2.1 j.2.2⟩

theorem restImg_eq_smul (p : Ppair) (j : Rest) : restImg p.2 j = p • j := rfl

theorem wAct_monomial_pW
    {a : C} {p : AutPerm} (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈
    Kstab v0) (j : Rest) (b : ZMod 2) :
    wAct v0 ⟨_, hk⟩ (pW j b) = pW (restImg ((mk_mem_Kstab_iff_monomial a p).1 hk).1 j)
      (b + (a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) j) := by
  have hp := ((mk_mem_Kstab_iff_monomial a p).1 hk).1
  rw [pW, wAct_mk]
  have e : kOp (QuotientGroup.mk (gO a * PO p)) (pairCls 0 j b) =
      pairCls ((p : Equiv.Perm (Fin 24)) 0) ((p : Equiv.Perm (Fin 24)) j)
        (b + (a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) j) := by
    rw [kOp_mk, modTwoEnd_gO_mul_PO_pairCls a p (rest_ne_zero j)]
  rcases (mem_Ppair_iff p).1 hp with ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [pW]
    congr 1
    apply Subtype.ext
    change kOp (QuotientGroup.mk (gO a * PO p)) (pairCls 0 j b) = _
    rw [e, h0]
    rfl
  · have e' : (⟨kOp ((⟨_, hk⟩ : Kstab v0) : OLq) ((⟨pairCls 0 j b, pairCls0_mem j b⟩ :
        vPerpL v0) : L2), kOp_mem_vPerpL hk (pairCls0_mem j b)⟩ : vPerpL v0) =
        ⟨pairCls 1 (restImg hp j) (b + (a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) j),
          pairCls1_mem _ _⟩ := by
      apply Subtype.ext
      change kOp (QuotientGroup.mk (gO a * PO p)) (pairCls 0 j b) = _
      rw [e, h0]
      rfl
    rw [e', mk_pairCls1]

theorem psiW_dhat0
    (j : Rest) : psiW (dhatE 0 j) = pW j 0 := by
  have hij : (0 : Fin 24) < j := by
    rcases j with ⟨j, hj0, -⟩
    exact Fin.pos_iff_ne_zero.2 hj0
  have e : dhatE 0 j = ehatEquiv ⟨dbar 0 j, dbar_mem_Ebar 0 j⟩ := rfl
  rw [e, psiW_ehatEquiv]
  have e2 := psiBar_kappa_rho (DQ_mem_centralizer (deltaPair 0 j))
  change wvEquiv hv0 (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv (DQ (deltaPair 0 j)),
    rhoEquiv_mem_Cgen (DQ_mem_centralizer (deltaPair 0 j))⟩,
    kappa_rho_mem_Ebar (DQ_mem_centralizer (deltaPair 0 j))⟩)) = _
  rw [e2, toAdd_ofAdd, wvEquiv_mk, pW]
  congr 1
  apply Subtype.ext
  change phi0 (coordOf (rMinus 0 j)) = pairCls 0 j 0
  rw [phi0_coordOf_rMinus hij, pairCls, pairVec_zero]

theorem exists_Ehat_bV_eq_one
    {S : Submodule (ZMod 2) (Wv v0)} {x : Wv v0} (hx : x ∉ S) :
    ∃ e : Ehat, psiW e ∈ bV.orthogonal S ∧ bV x (psiW e) = 1 := by
  obtain ⟨f, hfx, hS⟩ := Submodule.exists_le_ker_of_notMem hx
  set u := (bV.toDual bV_nondegenerate).symm f with hu
  have hbu : ∀ m, bV u m = f m := fun m => by
    rw [← LinearMap.BilinForm.toDual_def bV_nondegenerate, hu, LinearEquiv.apply_symm_apply]
  obtain ⟨e, he⟩ := psiW_surjective u
  refine ⟨e, ?_, ?_⟩
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro m hm
    rw [he, bV_comm, hbu]
    exact hS hm
  · rw [he, bV_comm, hbu]
    rcases zmod2_cases (f x) with h | h
    · exact absurd h hfx
    · exact h

end CFSG.Monster.B.TwoA.Par2
