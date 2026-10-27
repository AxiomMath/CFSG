module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Frame
public import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomPrincipal
import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomSecRep
import CFSG.Quasithin.Recognition.St84.Gen.SecRepForms
public import CFSG.Quasithin.Background.JonesParshallBasic
import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single conj_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem exists_eElt_mul eElt_add_mul_inv_mem
  conj_eElt_mul_inv_mem eEltQuotEquiv eEltQuotEquiv_ofAdd eElt_mul_inv_mem_of_cols)
open Certificates.A5GL42 (aO bO)
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13.NFa2
open Matrix
open scoped commutatorElement Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

private def cobA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 1, 0, 1, 0; 1, 0, 0, 0; 1, 0, 1, 0]

private def cobB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 1, 1, 0, 0; 1, 1, 0, 0]

private def corA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 1, 0, 1, 0; 0, 0, 0, 0; 0, 0, 1, 0]

private def corB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def splA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 1, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 0]

private def splB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 0; 0, 0, 0, 0]

private def formO : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

private theorem cobA_a : (aO + 1) * cobA = 1 + corA * (1 + aO) := by decide

private theorem cobB_b : (bO + 1) * cobB = 1 + corB * (1 + bO + bO ^ 2) := by decide

private theorem cobB_a : (aO + 1) * cobB = 0 := by decide

private theorem cobA_b : (bO + 1) * cobA = 0 := by decide

private theorem spl_eq : (aO + 1) * splA + (bO + 1) * splB = 1 := by decide

private theorem formO_a : aOᵀ * formO * aO = formO := by decide

private theorem formO_b : bOᵀ * formO * bO = formO := by decide

private theorem formO_mul : formO * formO = 1 := by decide

private theorem formO_transpose : formOᵀ = formO := by decide

private theorem v1Diag_mul (X Y : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    v1Diag (X * Y) = v1Diag X * v1Diag Y := by
  ext i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · simp only [v1Diag_castAdd_castAdd, Matrix.mul_apply]
      rw [Fin.sum_univ_add (a := 4) (b := 4)]
      simp only [v1Diag_castAdd_castAdd, v1Diag_castAdd_natAdd, v1Diag_natAdd_castAdd,
        mul_zero, Finset.sum_const_zero, add_zero]
    · simp only [v1Diag_castAdd_natAdd, Matrix.mul_apply]
      rw [Fin.sum_univ_add (a := 4) (b := 4)]
      simp only [v1Diag_castAdd_castAdd, v1Diag_castAdd_natAdd, v1Diag_natAdd_castAdd,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · simp only [v1Diag_natAdd_castAdd, Matrix.mul_apply]
      rw [Fin.sum_univ_add (a := 4) (b := 4)]
      simp only [v1Diag_castAdd_castAdd, v1Diag_castAdd_natAdd, v1Diag_natAdd_castAdd,
        v1Diag_natAdd_natAdd, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    · simp only [v1Diag_natAdd_natAdd, Matrix.mul_apply]
      rw [Fin.sum_univ_add (a := 4) (b := 4)]
      simp only [v1Diag_castAdd_castAdd, v1Diag_castAdd_natAdd, v1Diag_natAdd_castAdd,
        v1Diag_natAdd_natAdd, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]

private theorem v1Diag_add (X Y : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    v1Diag (X + Y) = v1Diag X + v1Diag Y := by
  ext i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · simp only [Matrix.add_apply, v1Diag_castAdd_castAdd]
    · simp only [Matrix.add_apply, v1Diag_castAdd_natAdd, add_zero]
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · simp only [Matrix.add_apply, v1Diag_natAdd_castAdd, add_zero]
    · simp only [Matrix.add_apply, v1Diag_natAdd_natAdd]

private theorem v1Diag_one : v1Diag (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
  ext i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · simp only [v1Diag_castAdd_castAdd, Matrix.one_apply]
      by_cases h : a = b
      · subst h
        simp
      · rw [if_neg h, if_neg (fun hc => h (Fin.castAdd_inj.mp hc))]
    · rw [v1Diag_castAdd_natAdd, Matrix.one_apply]
      have hne : Fin.castAdd 4 a ≠ Fin.natAdd 4 d := by
        intro h
        have hv := congrArg Fin.val h
        simp [Fin.castAdd, Fin.natAdd] at hv
        omega
      rw [if_neg hne]
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [v1Diag_natAdd_castAdd, Matrix.one_apply]
      have hne : Fin.natAdd 4 c ≠ Fin.castAdd 4 b := by
        intro h
        have hv := congrArg Fin.val h
        simp [Fin.castAdd, Fin.natAdd] at hv
        omega
      rw [if_neg hne]
    · simp only [v1Diag_natAdd_natAdd, Matrix.one_apply]
      by_cases h : c = d
      · subst h
        simp
      · rw [if_neg h]
        symm
        rw [if_neg]
        intro hc
        apply h
        apply Fin.ext
        have hv := congrArg Fin.val hc
        simp only [Fin.val_natAdd] at hv
        omega

private theorem v1Diag_transpose (X : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    (v1Diag X)ᵀ = v1Diag Xᵀ := by
  ext i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [Matrix.transpose_apply, v1Diag_castAdd_castAdd, v1Diag_castAdd_castAdd,
        Matrix.transpose_apply]
    · rw [Matrix.transpose_apply, v1Diag_castAdd_natAdd, v1Diag_natAdd_castAdd]
  · refine Fin.addCases (m := 4) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [Matrix.transpose_apply, v1Diag_natAdd_castAdd, v1Diag_castAdd_natAdd]
    · rw [Matrix.transpose_apply, v1Diag_natAdd_natAdd, v1Diag_natAdd_natAdd,
        Matrix.transpose_apply]

private theorem v1Diag_cobA_a :
    (v1Diag aO + 1) * v1Diag cobA = 1 + v1Diag corA * (1 + v1Diag aO) := by
  rw [← v1Diag_one, ← v1Diag_add, ← v1Diag_mul, cobA_a, v1Diag_add, v1Diag_mul,
    v1Diag_add, v1Diag_one]

private theorem v1Diag_cobB_b :
    (v1Diag bO + 1) * v1Diag cobB = 1 + v1Diag corB * (1 + v1Diag bO + v1Diag bO ^ 2) := by
  rw [← v1Diag_one, ← v1Diag_add, ← v1Diag_mul, cobB_b, v1Diag_add, v1Diag_mul,
    v1Diag_add, v1Diag_add, v1Diag_one]
  rw [show v1Diag bO ^ 2 = v1Diag (bO ^ 2) by rw [pow_two, pow_two, ← v1Diag_mul]]

private theorem v1Diag_zero : v1Diag (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 := by
  ext i j
  simp [v1Diag]

private theorem v1Diag_cobB_a : (v1Diag aO + 1) * v1Diag cobB = 0 := by
  rw [← v1Diag_one, ← v1Diag_add, ← v1Diag_mul, cobB_a, v1Diag_zero]

private theorem v1Diag_cobA_b : (v1Diag bO + 1) * v1Diag cobA = 0 := by
  rw [← v1Diag_one, ← v1Diag_add, ← v1Diag_mul, cobA_b, v1Diag_zero]

private theorem v1Diag_spl_eq :
    (v1Diag aO + 1) * v1Diag splA + (v1Diag bO + 1) * v1Diag splB = 1 := by
  rw [← v1Diag_one, ← v1Diag_add, ← v1Diag_add, ← v1Diag_mul, ← v1Diag_mul,
    ← v1Diag_add, spl_eq]

private theorem v1Diag_formO_a :
    (v1Diag aO)ᵀ * v1Diag formO * v1Diag aO = v1Diag formO := by
  rw [v1Diag_transpose, ← v1Diag_mul, ← v1Diag_mul, formO_a]

private theorem v1Diag_formO_b :
    (v1Diag bO)ᵀ * v1Diag formO * v1Diag bO = v1Diag formO := by
  rw [v1Diag_transpose, ← v1Diag_mul, ← v1Diag_mul, formO_b]

private theorem v1Diag_formO_mul : v1Diag formO * v1Diag formO = 1 := by
  rw [← v1Diag_one, ← v1Diag_mul, formO_mul]

private theorem v1Diag_formO_transpose : (v1Diag formO)ᵀ = v1Diag formO := by
  rw [v1Diag_transpose, formO_transpose]

private abbrev v1N (F : G24Frame1 L1 L2 S) : Subgroup G :=
  Subgroup.closure ({F.a, F.b} : Set G)

private def v1a (F : G24Frame1 L1 L2 S) : ↥(v1N F) :=
  ⟨F.a, Subgroup.subset_closure (by simp)⟩

private def v1b (F : G24Frame1 L1 L2 S) : ↥(v1N F) :=
  ⟨F.b, Subgroup.subset_closure (by simp)⟩

private theorem v1N_le (F : G24Frame1 L1 L2 S) :
    v1N F ≤ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) := by
  rw [v1N, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ⟨Subgroup.mem_sup_left F.a_mem.1, F.a_mem.2⟩
  · exact ⟨Subgroup.mem_sup_left F.b_mem.1, F.b_mem.2⟩

private theorem v1Z_normal (L1 L2 S : Subgroup G) :
    ((centerOf (dsQ L1 L2 S)).subgroupOf (dsQ L1 L2 S)).Normal :=
  Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x =>
      Subtype.ext (G24Vertex1.centerOf_dsQ_comm (z : G) (Subgroup.mem_subgroupOf.mp hz)
        (x : G) x.2).symm

private theorem v1N_normal (F : G24Frame1 L1 L2 S) :
    ∀ r ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G),
      ∀ n ∈ v1N F, r * n * r⁻¹ ∈ v1N F := by
  have hk : F.k ∈ Subgroup.centralizer (v1N F : Set G) := by
    rw [v1N, Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rcases hh with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp F.a_mem.2
    · exact Subgroup.mem_centralizer_singleton_iff.mp F.b_mem.2
  have hR : (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) ≤
      Subgroup.normalizer (v1N F : Set G) := by
    intro r hr
    rw [← F.closure_eq] at hr
    refine (Subgroup.closure_le _).mpr ?_ hr
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.le_normalizer (Subgroup.subset_closure (by simp))
    · exact Subgroup.le_normalizer (Subgroup.subset_closure (by simp))
    · exact Subgroup.centralizer_le_normalizer _ hk
  intro r hr n hn
  exact (Subgroup.mem_normalizer_iff.mp (hR hr) n).mp hn

private theorem v1SecHyp [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) :
    SecHyp (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) where
  le := inf_le_left
  norm₀ := (v1N_le F).trans
    (inf_le_left.trans (P_le_normalizer_centerOf_dsQ_left L1 L2 S))
  norm₁ := (v1N_le F).trans
    (inf_le_left.trans (P_le_normalizer_dsQ_left L1 L2 S))
  normal := (dsQ_le_P_left L1 L2 S).trans (P_le_normalizer_centerOf_dsQ_left L1 L2 S)
  comm := fun a ha b hb => by
    rw [← commutatorElement_def]
    exact G24Vertex1.commutator_mem_centerOf_dsQ hD a ha b hb
  sq := fun a ha => by
    rw [← pow_two]
    exact G24Vertex1.sq_mem_centerOf_dsQ hD a ha

private noncomputable def v1CoordEquiv [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {N : Subgroup G} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep N (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] W := by
  classical
  haveI : ((centerOf (dsQ L1 L2 S)).subgroupOf (dsQ L1 L2 S)).Normal := v1Z_normal L1 L2 S
  obtain ⟨hQ, hC, hSq, hCm, hCard⟩ := F.frame_spec hD
  let qe := CFSG.GroupTheory.eEltQuotEquiv (n := 8) (Q := dsQ L1 L2 S)
    (Z := centerOf (dsQ L1 L2 S)) (f := v1Frame F.k F.e) inf_le_left hQ hC hSq hCm
    F.indep hCard
  let m : Multiplicative (Fin 8 → ZMod 2) ≃* Multiplicative W :=
    qe.trans (SecRep.quotEquiv s)
  let cA : (Fin 8 → ZMod 2) ≃+ W :=
    { toFun := fun u => (m (Multiplicative.ofAdd u)).toAdd
      invFun := fun w => (m.symm (Multiplicative.ofAdd w)).toAdd
      left_inv := fun u => by simp
      right_inv := fun w => by simp
      map_add' := fun u v => by
        show (m (Multiplicative.ofAdd (u + v))).toAdd =
          (m (Multiplicative.ofAdd u)).toAdd + (m (Multiplicative.ofAdd v)).toAdd
        rw [show Multiplicative.ofAdd (u + v) =
          Multiplicative.ofAdd u * Multiplicative.ofAdd v from rfl, map_mul,
          toAdd_mul] }
  exact cA.toLinearEquiv (fun c x => ZMod.map_smul cA c x)

private theorem v1CoordEquiv_apply [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {N : Subgroup G} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep N (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W)
    (u : Fin 8 → ZMod 2) :
    v1CoordEquiv F hD s u =
      s.cl ⟨eElt (v1Frame F.k F.e) u,
        eElt_mem_of_forall_mem (F.frame_spec hD).1 u⟩ := by
  classical
  haveI : ((centerOf (dsQ L1 L2 S)).subgroupOf (dsQ L1 L2 S)).Normal := v1Z_normal L1 L2 S
  obtain ⟨hQ, hC, hSq, hCm, hCard⟩ := F.frame_spec hD
  rw [v1CoordEquiv]
  change Multiplicative.toAdd ((SecRep.quotEquiv s)
    (QuotientGroup.mk ⟨eElt (v1Frame F.k F.e) u,
      eElt_mem_of_forall_mem hQ u⟩)) = _
  rw [SecRep.quotEquiv_mk]

private noncomputable def v1Rep {N : Subgroup G} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep N (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) :
    Representation (ZMod 2) ↥N W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp s.ρ

private theorem v1Rep_apply {N : Subgroup G} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep N (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) (n : ↥N) (w : W) :
    v1Rep s n w = s.ρ n w := rfl

private theorem v1Rep_a [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W)
    (u : Fin 8 → ZMod 2) :
    v1Rep s (v1a F) (v1CoordEquiv F hD s u) =
      v1CoordEquiv F hD s (v1Diag aO *ᵥ u) := by
  classical
  obtain ⟨hQ, hC, hSq, hCm, hCard⟩ := F.frame_spec hD
  haveI : ((centerOf (dsQ L1 L2 S)).subgroupOf (dsQ L1 L2 S)).Normal := v1Z_normal L1 L2 S
  have hxq : eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u) ∈ dsQ L1 L2 S :=
    eElt_mem_of_forall_mem hQ _
  have hmQ : F.a * eElt (v1Frame F.k F.e) u * F.a⁻¹ ∈ dsQ L1 L2 S := by
    have ha : F.a ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
      P_le_normalizer_dsQ_left L1 L2 S (Subgroup.mem_sup_left F.a_mem.1)
    exact (Subgroup.mem_normalizer_iff.mp ha _).mp (eElt_mem_of_forall_mem hQ u)
  let m : ↥(dsQ L1 L2 S) := ⟨F.a * eElt (v1Frame F.k F.e) u * F.a⁻¹, hmQ⟩
  have hact : s.ρ (v1a F) (s.cl ⟨eElt (v1Frame F.k F.e) u,
      eElt_mem_of_forall_mem hQ u⟩) = s.cl m :=
    s.act (v1a F) ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩ m rfl
  have hy : (m : G) * (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹ ∈
      centerOf (dsQ L1 L2 S) := by
    simpa [m] using conj_eElt_mul_inv_mem hC hSq hCm (v1Diag aO) F.act_a u
  have hy' : (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹ * (m : G) ∈
      centerOf (dsQ L1 L2 S) := by
    have hcx := G24Vertex1.centerOf_dsQ_comm
      ((m : G) * (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹) hy
      ((eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹) (Subgroup.inv_mem _ hxq)
    have hm : (m : G) = ((m : G) * (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹) *
        eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u) := by group
    rw [hm, ← mul_assoc, ← hcx]
    have he : (((m : G) * (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹) *
        (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹) *
        eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u) =
        (m : G) * (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹ := by group
    rw [he]
    exact hy
  have hcl : s.cl m = s.cl ⟨eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u), hxq⟩ := by
    rw [s.cl_eq_iff]
    exact hy'
  calc v1Rep s (v1a F) (v1CoordEquiv F hD s u)
      = s.ρ (v1a F) (s.cl ⟨eElt (v1Frame F.k F.e) u,
          eElt_mem_of_forall_mem hQ u⟩) := by rw [v1Rep_apply, v1CoordEquiv_apply]
    _ = s.cl m := hact
    _ = s.cl ⟨eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u), hxq⟩ := hcl
    _ = v1CoordEquiv F hD s (v1Diag aO *ᵥ u) := by rw [v1CoordEquiv_apply]

private theorem v1Rep_b [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W)
    (u : Fin 8 → ZMod 2) :
    v1Rep s (v1b F) (v1CoordEquiv F hD s u) =
      v1CoordEquiv F hD s (v1Diag bO *ᵥ u) := by
  classical
  obtain ⟨hQ, hC, hSq, hCm, hCard⟩ := F.frame_spec hD
  haveI : ((centerOf (dsQ L1 L2 S)).subgroupOf (dsQ L1 L2 S)).Normal := v1Z_normal L1 L2 S
  have hxq : eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u) ∈ dsQ L1 L2 S :=
    eElt_mem_of_forall_mem hQ _
  have hmQ : F.b * eElt (v1Frame F.k F.e) u * F.b⁻¹ ∈ dsQ L1 L2 S := by
    have hb : F.b ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
      P_le_normalizer_dsQ_left L1 L2 S (Subgroup.mem_sup_left F.b_mem.1)
    exact (Subgroup.mem_normalizer_iff.mp hb _).mp (eElt_mem_of_forall_mem hQ u)
  let m : ↥(dsQ L1 L2 S) := ⟨F.b * eElt (v1Frame F.k F.e) u * F.b⁻¹, hmQ⟩
  have hact : s.ρ (v1b F) (s.cl ⟨eElt (v1Frame F.k F.e) u,
      eElt_mem_of_forall_mem hQ u⟩) = s.cl m :=
    s.act (v1b F) ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩ m rfl
  have hy : (m : G) * (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹ ∈
      centerOf (dsQ L1 L2 S) := by
    simpa [m] using conj_eElt_mul_inv_mem hC hSq hCm (v1Diag bO) F.act_b u
  have hy' : (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹ * (m : G) ∈
      centerOf (dsQ L1 L2 S) := by
    have hcx := G24Vertex1.centerOf_dsQ_comm
      ((m : G) * (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹) hy
      ((eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹) (Subgroup.inv_mem _ hxq)
    have hm : (m : G) = ((m : G) * (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹) *
        eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u) := by group
    rw [hm, ← mul_assoc, ← hcx]
    have he : (((m : G) * (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹) *
        (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹) *
        eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u) =
        (m : G) * (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹ := by group
    rw [he]
    exact hy
  have hcl : s.cl m = s.cl ⟨eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u), hxq⟩ := by
    rw [s.cl_eq_iff]
    exact hy'
  calc v1Rep s (v1b F) (v1CoordEquiv F hD s u)
      = s.ρ (v1b F) (s.cl ⟨eElt (v1Frame F.k F.e) u,
          eElt_mem_of_forall_mem hQ u⟩) := by rw [v1Rep_apply, v1CoordEquiv_apply]
    _ = s.cl m := hact
    _ = s.cl ⟨eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u), hxq⟩ := hcl
    _ = v1CoordEquiv F hD s (v1Diag bO *ᵥ u) := by rw [v1CoordEquiv_apply]

private theorem v1Rep_a_symm [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) (x : W) :
    v1Rep s (v1a F) x =
      v1CoordEquiv F hD s (v1Diag aO *ᵥ (v1CoordEquiv F hD s).symm x) := by
  conv_lhs => rw [← (v1CoordEquiv F hD s).apply_symm_apply x]
  rw [v1Rep_a]

private theorem v1Rep_b_symm [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) (x : W) :
    v1Rep s (v1b F) x =
      v1CoordEquiv F hD s (v1Diag bO *ᵥ (v1CoordEquiv F hD s).symm x) := by
  conv_lhs => rw [← (v1CoordEquiv F hD s).apply_symm_apply x]
  rw [v1Rep_b]

private theorem form_pair (A G : Matrix (Fin 8) (Fin 8) (ZMod 2)) (hG : Gᵀ = G)
    (hA : Aᵀ * G * A = G) (x y : Fin 8 → ZMod 2) :
    (A *ᵥ x) ⬝ᵥ (G *ᵥ (A *ᵥ y)) = x ⬝ᵥ (G *ᵥ y) := by
  calc (A *ᵥ x) ⬝ᵥ (G *ᵥ (A *ᵥ y))
      = (A *ᵥ x) ᵥ* G ⬝ᵥ (A *ᵥ y) := by rw [dotProduct_mulVec]
    _ = (Gᵀ *ᵥ (A *ᵥ x)) ⬝ᵥ (A *ᵥ y) := by rw [mulVec_transpose]
    _ = (G *ᵥ (A *ᵥ x)) ⬝ᵥ (A *ᵥ y) := by rw [hG]
    _ = ((G * A) *ᵥ x) ⬝ᵥ (A *ᵥ y) := by rw [mulVec_mulVec]
    _ = (A *ᵥ y) ⬝ᵥ ((G * A) *ᵥ x) := by rw [dotProduct_comm]
    _ = x ⬝ᵥ ((G * A)ᵀ *ᵥ (A *ᵥ y)) := by rw [dotProduct_transpose_mulVec]
    _ = x ⬝ᵥ ((Aᵀ * G) *ᵥ (A *ᵥ y)) := by rw [Matrix.transpose_mul, hG]
    _ = x ⬝ᵥ (((Aᵀ * G) * A) *ᵥ y) := by rw [mulVec_mulVec]
    _ = x ⬝ᵥ (G *ᵥ y) := by rw [hA]

private noncomputable def v1Form [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) :
    W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2 :=
  (Matrix.toLinearMap₂' (ZMod 2) (v1Diag formO)).compl₁₂
    (v1CoordEquiv F hD s).symm.toLinearMap (v1CoordEquiv F hD s).symm.toLinearMap

private theorem v1Form_apply [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) (x y : W) :
    v1Form F hD s x y =
      (v1CoordEquiv F hD s).symm x ⬝ᵥ
        (v1Diag formO *ᵥ (v1CoordEquiv F hD s).symm y) := by
  rw [v1Form, LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply']
  rfl

private theorem v1Form_invariant [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) :
    ∀ n x y, v1Form F hD s (v1Rep s n x) (v1Rep s n y) = v1Form F hD s x y := by
  classical
  intro n
  refine Subgroup.closure_induction (p := fun g hg =>
    ∀ x y, v1Form F hD s (v1Rep s ⟨g, hg⟩ x) (v1Rep s ⟨g, hg⟩ y) =
      v1Form F hD s x y) ?mem ?one ?mul ?inv n.2
  · rintro g (rfl | rfl) x y
    · change v1Form F hD s (v1Rep s (v1a F) x) (v1Rep s (v1a F) y) =
        v1Form F hD s x y
      rw [v1Rep_a_symm, v1Rep_a_symm, v1Form_apply, v1Form_apply,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact form_pair (v1Diag aO) (v1Diag formO) v1Diag_formO_transpose v1Diag_formO_a _ _
    · change v1Form F hD s (v1Rep s (v1b F) x) (v1Rep s (v1b F) y) =
        v1Form F hD s x y
      rw [v1Rep_b_symm, v1Rep_b_symm, v1Form_apply, v1Form_apply,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact form_pair (v1Diag bO) (v1Diag formO) v1Diag_formO_transpose v1Diag_formO_b _ _
  · intro x y
    change v1Form F hD s (v1Rep s (1 : ↥(v1N F)) x) (v1Rep s (1 : ↥(v1N F)) y) =
      v1Form F hD s x y
    rw [map_one]
    rfl
  · intro a b ha hb iha ihb x y
    have h1 : (⟨a * b, Subgroup.mul_mem (v1N F) ha hb⟩ : ↥(v1N F)) =
        ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [h1, map_mul]
    change v1Form F hD s (v1Rep s ⟨a, ha⟩ (v1Rep s ⟨b, hb⟩ x))
      (v1Rep s ⟨a, ha⟩ (v1Rep s ⟨b, hb⟩ y)) = v1Form F hD s x y
    rw [iha, ihb]
  · intro a ha iha x y
    have hxa : v1Rep s ⟨a, ha⟩ (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ x) = x := by
      have h1 : (⟨a, ha⟩ * ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ : ↥(v1N F)) = 1 := by
        ext
        simp
      rw [← Module.End.mul_apply (v1Rep s ⟨a, ha⟩)
        (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩)]
      rw [← map_mul, h1, map_one]
      rfl
    have hya : v1Rep s ⟨a, ha⟩ (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ y) = y := by
      have h1 : (⟨a, ha⟩ * ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ : ↥(v1N F)) = 1 := by
        ext
        simp
      rw [← Module.End.mul_apply (v1Rep s ⟨a, ha⟩)
        (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩)]
      rw [← map_mul, h1, map_one]
      rfl
    calc v1Form F hD s (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ x)
          (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ y)
        = v1Form F hD s (v1Rep s ⟨a, ha⟩ (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ x))
            (v1Rep s ⟨a, ha⟩ (v1Rep s ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ y)) :=
          (iha _ _).symm
      _ = v1Form F hD s x y := by rw [hxa, hya]

private theorem v1Form_nondegenerate [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) :
    ∀ x, (∀ y, v1Form F hD s x y = 0) → x = 0 := by
  classical
  intro x hx
  set x' : Fin 8 → ZMod 2 := (v1CoordEquiv F hD s).symm x with hx'
  have hdot : ∀ y : Fin 8 → ZMod 2, x' ⬝ᵥ (v1Diag formO *ᵥ y) = 0 := by
    intro y
    have h := hx (v1CoordEquiv F hD s y)
    rw [v1Form_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ i, (v1Diag formO *ᵥ x') i = 0 := by
    intro i
    have h := hdot (Pi.single i 1)
    rw [dotProduct_mulVec] at h
    rw [dotProduct_single] at h
    rw [← mulVec_transpose, v1Diag_formO_transpose] at h
    simpa using h
  have hzero : v1Diag formO *ᵥ x' = 0 := by
    ext i
    exact h1 i
  have hx'0 : x' = 0 := by
    calc x' = (v1Diag formO * v1Diag formO) *ᵥ x' := by
          rw [v1Diag_formO_mul, one_mulVec]
      _ = v1Diag formO *ᵥ (v1Diag formO *ᵥ x') := by rw [mulVec_mulVec]
      _ = 0 := by rw [hzero, mulVec_zero]
  calc x = v1CoordEquiv F hD s x' := ((v1CoordEquiv F hD s).apply_symm_apply x).symm
    _ = 0 := by rw [hx'0, map_zero]

private theorem v1Z1_eq_zero_of [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W)
    {ψ : ↥(v1N F) → W} (hψ : ψ ∈ Z1 (v1Rep s))
    (ha : ψ (v1a F) = 0) (hb : ψ (v1b F) = 0) :
    ∀ n, ψ n = 0 := by
  classical
  have hψ1 : ψ 1 = 0 := by
    have h := hψ (1 : ↥(v1N F)) (1 : ↥(v1N F))
    have h1 : ψ 1 + ψ 1 = 0 := ZModModule.add_self (ψ 1)
    have h' : ψ 1 = ψ 1 + ψ 1 := by simpa using h
    exact h'.trans h1
  intro n
  refine Subgroup.closure_induction (p := fun g hg => ψ ⟨g, hg⟩ = 0) ?mem ?one ?mul ?inv n.2
  · rintro g (rfl | rfl)
    · change ψ (v1a F) = 0
      exact ha
    · change ψ (v1b F) = 0
      exact hb
  · change ψ (1 : ↥(v1N F)) = 0
    exact hψ1
  · intro a b ha hb iha ihb
    have h := hψ ⟨a, ha⟩ ⟨b, hb⟩
    rw [show (⟨a * b, Subgroup.mul_mem (v1N F) ha hb⟩ : ↥(v1N F)) =
        ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, h, iha, ihb, map_zero, add_zero]
  · intro a ha iha
    have h := hψ ⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ ⟨a, ha⟩
    rw [show (⟨a⁻¹, Subgroup.inv_mem (v1N F) ha⟩ * ⟨a, ha⟩ : ↥(v1N F)) = 1 from
      Subtype.ext (inv_mul_cancel a), hψ1, iha, map_zero, add_zero] at h
    exact h.symm

private theorem v1H1 [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (v1N F) (centerOf (dsQ L1 L2 S)) (dsQ L1 L2 S) W) :
    ∀ φ : ↥(v1N F) → W, φ ∈ Z1 (v1Rep s) → φ ∈ B1 (v1Rep s) := by
  classical
  intro φ hφ
  have hφ1 : φ 1 = 0 := by
    have h := hφ (1 : ↥(v1N F)) (1 : ↥(v1N F))
    have h1 : φ 1 + φ 1 = 0 := ZModModule.add_self (φ 1)
    have h' : φ 1 = φ 1 + φ 1 := by simpa using h
    exact h'.trans h1
  set x : Fin 8 → ZMod 2 := (v1CoordEquiv F hD s).symm (φ (v1a F)) with hx
  set y : Fin 8 → ZMod 2 := (v1CoordEquiv F hD s).symm (φ (v1b F)) with hy
  have hAa : (v1Diag aO + 1) *ᵥ x = 0 := by
    have hinv : (v1a F) * (v1a F) = 1 := by
      apply Subtype.ext
      show F.a * F.a = 1
      rw [← pow_two, F.a_sq]
    have h := hφ (v1a F) (v1a F)
    rw [hinv, hφ1] at h
    have h2 : v1CoordEquiv F hD s x +
        v1CoordEquiv F hD s (v1Diag aO *ᵥ x) = 0 := by
      rw [← h.symm]
      rw [show v1CoordEquiv F hD s x = φ (v1a F) from
          ((v1CoordEquiv F hD s).apply_symm_apply _),
        show v1Rep s (v1a F) (φ (v1a F)) =
          v1CoordEquiv F hD s (v1Diag aO *ᵥ x) from v1Rep_a_symm F hD s _]
    have h3 : x + v1Diag aO *ᵥ x = 0 := by
      apply (v1CoordEquiv F hD s).injective
      rw [map_add, map_zero]
      exact h2
    calc (v1Diag aO + 1) *ᵥ x = v1Diag aO *ᵥ x + 1 *ᵥ x := by rw [add_mulVec]
      _ = v1Diag aO *ᵥ x + x := by rw [one_mulVec]
      _ = x + v1Diag aO *ᵥ x := by rw [add_comm]
      _ = 0 := h3
  have hBb : (1 + v1Diag bO + v1Diag bO ^ 2) *ᵥ y = 0 := by
    have hcube : ((v1b F) * (v1b F)) * (v1b F) = 1 := by
      apply Subtype.ext
      show (F.b * F.b) * F.b = 1
      rw [← pow_two, ← pow_succ]
      exact F.b_cube
    have hb2 := hφ (v1b F) (v1b F)
    have hb3 := hφ ((v1b F) * (v1b F)) (v1b F)
    rw [hcube, hφ1] at hb3
    rw [hb2] at hb3
    rw [map_mul, Module.End.mul_apply] at hb3
    have h2 : v1CoordEquiv F hD s y +
        v1CoordEquiv F hD s (v1Diag bO *ᵥ y) +
        v1CoordEquiv F hD s (v1Diag bO *ᵥ (v1Diag bO *ᵥ y)) = 0 := by
      rw [← hb3.symm]
      rw [show v1CoordEquiv F hD s y = φ (v1b F) from
          ((v1CoordEquiv F hD s).apply_symm_apply _),
        show v1CoordEquiv F hD s (v1Diag bO *ᵥ y) =
          v1Rep s (v1b F) (φ (v1b F)) from (v1Rep_b_symm F hD s _).symm,
        show v1CoordEquiv F hD s (v1Diag bO *ᵥ (v1Diag bO *ᵥ y)) =
          v1Rep s (v1b F) (v1Rep s (v1b F) (φ (v1b F))) from by
            rw [v1Rep_b_symm F hD s, v1Rep_b_symm F hD s,
              LinearEquiv.symm_apply_apply, ← hy]]
    have h3 : y + v1Diag bO *ᵥ y +
        v1Diag bO *ᵥ (v1Diag bO *ᵥ y) = 0 := by
      apply (v1CoordEquiv F hD s).injective
      rw [map_add, map_add, map_zero]
      exact h2
    calc (1 + v1Diag bO + v1Diag bO ^ 2) *ᵥ y
        = 1 *ᵥ y + v1Diag bO *ᵥ y + v1Diag bO ^ 2 *ᵥ y := by
          rw [add_mulVec, add_mulVec]
      _ = y + v1Diag bO *ᵥ y + v1Diag bO *ᵥ (v1Diag bO *ᵥ y) := by
          rw [one_mulVec, pow_two, mulVec_mulVec]
      _ = 0 := h3
  set w : Fin 8 → ZMod 2 := v1Diag cobA *ᵥ x + v1Diag cobB *ᵥ y with hw
  have hwA : (v1Diag aO + 1) *ᵥ w = x := by
    rw [hw, mulVec_add, mulVec_mulVec, mulVec_mulVec, v1Diag_cobA_a, v1Diag_cobB_a,
      add_mulVec, one_mulVec, zero_mulVec, add_zero]
    rw [← mulVec_mulVec, show (1 + v1Diag aO) *ᵥ x = 0 by rw [add_comm, hAa],
      mulVec_zero, add_zero]
  have hwB : (v1Diag bO + 1) *ᵥ w = y := by
    rw [hw, mulVec_add, mulVec_mulVec, mulVec_mulVec, v1Diag_cobA_b, v1Diag_cobB_b,
      add_mulVec, one_mulVec, zero_mulVec, zero_add]
    rw [← mulVec_mulVec, hBb, mulVec_zero, add_zero]
  let ψ : ↥(v1N F) → W := φ - coboundary (v1Rep s) (v1CoordEquiv F hD s w)
  have hψZ : ψ ∈ Z1 (v1Rep s) :=
    (Z1 (v1Rep s)).sub_mem hφ (B1_le_Z1 (v1Rep s) (LinearMap.mem_range_self _ _))
  have hψa : ψ (v1a F) = 0 := by
    have hcob : coboundary (v1Rep s) (v1CoordEquiv F hD s w) (v1a F) =
        v1CoordEquiv F hD s ((v1Diag aO + 1) *ᵥ w) := by
      calc coboundary (v1Rep s) (v1CoordEquiv F hD s w) (v1a F)
          = v1Rep s (v1a F) (v1CoordEquiv F hD s w) - v1CoordEquiv F hD s w := rfl
        _ = v1CoordEquiv F hD s (v1Diag aO *ᵥ w) - v1CoordEquiv F hD s w := by
              rw [v1Rep_a]
        _ = v1CoordEquiv F hD s (v1Diag aO *ᵥ w) + v1CoordEquiv F hD s w := by
              rw [ZModModule.sub_eq_add]
        _ = v1CoordEquiv F hD s (v1Diag aO *ᵥ w + w) := by simp only [map_add]
        _ = v1CoordEquiv F hD s ((v1Diag aO + 1) *ᵥ w) := by rw [add_mulVec, one_mulVec]
    rw [show ψ (v1a F) = φ (v1a F) - coboundary (v1Rep s)
        (v1CoordEquiv F hD s w) (v1a F) from rfl, hcob, hwA]
    rw [show φ (v1a F) = v1CoordEquiv F hD s x from
      ((v1CoordEquiv F hD s).apply_symm_apply _).symm]
    exact sub_self _
  have hψb : ψ (v1b F) = 0 := by
    have hcob : coboundary (v1Rep s) (v1CoordEquiv F hD s w) (v1b F) =
        v1CoordEquiv F hD s ((v1Diag bO + 1) *ᵥ w) := by
      calc coboundary (v1Rep s) (v1CoordEquiv F hD s w) (v1b F)
          = v1Rep s (v1b F) (v1CoordEquiv F hD s w) - v1CoordEquiv F hD s w := rfl
        _ = v1CoordEquiv F hD s (v1Diag bO *ᵥ w) - v1CoordEquiv F hD s w := by
              rw [v1Rep_b]
        _ = v1CoordEquiv F hD s (v1Diag bO *ᵥ w) + v1CoordEquiv F hD s w := by
              rw [ZModModule.sub_eq_add]
        _ = v1CoordEquiv F hD s (v1Diag bO *ᵥ w + w) := by simp only [map_add]
        _ = v1CoordEquiv F hD s ((v1Diag bO + 1) *ᵥ w) := by rw [add_mulVec, one_mulVec]
    rw [show ψ (v1b F) = φ (v1b F) - coboundary (v1Rep s)
        (v1CoordEquiv F hD s w) (v1b F) from rfl, hcob, hwB]
    rw [show φ (v1b F) = v1CoordEquiv F hD s y from
      ((v1CoordEquiv F hD s).apply_symm_apply _).symm]
    exact sub_self _
  have hψzero : ψ = 0 := by
    funext n
    exact v1Z1_eq_zero_of F hD s hψZ hψa hψb n
  have hφeq : φ = coboundary (v1Rep s) (v1CoordEquiv F hD s w) := by
    funext n
    have h : φ n - coboundary (v1Rep s) (v1CoordEquiv F hD s w) n = 0 :=
      congrFun hψzero n
    exact sub_eq_zero.mp h
  rw [hφeq]
  exact ⟨_, rfl⟩

private theorem v1NZ' [Finite G] (F : G24Frame1 L1 L2 S) {G' : Type} [Group G']
    {Z' R' : Subgroup G'}
    (e : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) ≃* ↥R')
    (ha : ∀ r : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (r : G) = F.a → ∀ z ∈ Z', (e r : G') * z * (e r : G')⁻¹ = z)
    (hb : ∀ r : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (r : G) = F.b → ∀ z ∈ Z', (e r : G') * z * (e r : G')⁻¹ = z) :
    ∀ n : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (n : G) ∈ v1N F → ∀ z ∈ Z', (e n : G') * z * (e n : G')⁻¹ = z := by
  classical
  intro n hn
  refine (Subgroup.closure_induction (p := fun g hg =>
    ∀ hr : g ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G),
      ∀ z ∈ Z', (e ⟨g, hr⟩ : G') * z * (e ⟨g, hr⟩ : G')⁻¹ = z) ?mem ?one ?mul ?inv hn) n.2
  · rintro g (rfl | rfl) hr z hz
    · exact ha ⟨F.a, hr⟩ rfl z hz
    · exact hb ⟨F.b, hr⟩ rfl z hz
  · rintro hr z hz
    have h1 : (⟨1, hr⟩ : ↥((L1 ⊔ bigB L1 L2 S) ⊓
        Subgroup.centralizer ({F.k} : Set G))) = 1 := rfl
    rw [h1, map_one]
    simp
  · intro a b ha hb iha ihb hr z hz
    have hha : a ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) :=
      v1N_le F ha
    have hhb : b ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) :=
      v1N_le F hb
    have he : (⟨a * b, hr⟩ : ↥((L1 ⊔ bigB L1 L2 S) ⊓
        Subgroup.centralizer ({F.k} : Set G))) = ⟨a, hha⟩ * ⟨b, hhb⟩ := rfl
    rw [he, map_mul]
    calc ((e ⟨a, hha⟩ : ↥R') * (e ⟨b, hhb⟩ : ↥R')) * z *
          ((e ⟨a, hha⟩ : ↥R') * (e ⟨b, hhb⟩ : ↥R'))⁻¹
        = (e ⟨a, hha⟩ : G') * ((e ⟨b, hhb⟩ : G') * z * (e ⟨b, hhb⟩ : G')⁻¹) *
            (e ⟨a, hha⟩ : G')⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
      _ = (e ⟨a, hha⟩ : G') * z * (e ⟨a, hha⟩ : G')⁻¹ := by rw [ihb hhb z hz]
      _ = z := iha hha z hz
  · intro a ha iha hr z hz
    have hha : a ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G) :=
      v1N_le F ha
    have h2 : ((e ⟨a⁻¹, hr⟩ : ↥R') : G') = ((e ⟨a, hha⟩ : ↥R') : G')⁻¹ := by
      rw [show (⟨a⁻¹, hr⟩ : ↥((L1 ⊔ bigB L1 L2 S) ⊓
          Subgroup.centralizer ({F.k} : Set G))) = ⟨a, hha⟩⁻¹ from rfl, map_inv]
      rfl
    rw [h2]
    have h := iha hha z hz
    have hgoal : (↑(e ⟨a, hha⟩) : G')⁻¹ * z * ↑(e ⟨a, hha⟩) = z := by
      have h2' := congrArg (fun t => (↑(e ⟨a, hha⟩) : G')⁻¹ * t *
        ↑(e ⟨a, hha⟩)) h
      have h3 : (↑(e ⟨a, hha⟩) : G')⁻¹ * ((↑(e ⟨a, hha⟩) : G') * z *
          ((↑(e ⟨a, hha⟩) : G')⁻¹)) * ↑(e ⟨a, hha⟩) = z := by group
      exact h2'.symm.trans h3
    simpa [inv_inv] using hgoal

private theorem centerOf_le_self (X : Subgroup G) : centerOf X ≤ X := by
  rw [centerOf]
  exact inf_le_left

private theorem v1Fix [Finite G] (F : G24Frame1 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {G' : Type} [Group G'] {Z' R' : Subgroup G'}
    (e : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) ≃* ↥R')
    (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (ha : ∀ r : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (r : G) = F.a → ∀ z ∈ Z', (e r : G') * z * (e r : G')⁻¹ = z)
    (hb : ∀ r : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (r : G) = F.b → ∀ z ∈ Z', (e r : G') * z * (e r : G')⁻¹ = z)
    (φ : ↥(dsQ L1 L2 S) →* ↥Z')
    (hφZ : ∀ v : ↥(dsQ L1 L2 S), (v : G) ∈ centerOf (dsQ L1 L2 S) → φ v = 1)
    (hφN : ∀ n : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (n : G) ∈ v1N F → ∀ (v w : ↥(dsQ L1 L2 S)),
        (w : G) = (n : G) * v * (n : G)⁻¹ →
          (φ w : G') = (e n : G') * (φ v : G') * (e n : G')⁻¹) :
    φ = 1 := by
  classical
  obtain ⟨hQ, hC, hSq, hCm, hCard⟩ := F.frame_spec hD
  let χ : (Fin 8 → ZMod 2) → ↥Z' := fun u =>
    φ ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩
  have hchi_add : ∀ u u', χ (u + u') = χ u * χ u' := by
    intro u u'
    have hmem : eElt (v1Frame F.k F.e) (u + u') *
        (eElt (v1Frame F.k F.e) u * eElt (v1Frame F.k F.e) u')⁻¹ ∈
        centerOf (dsQ L1 L2 S) :=
      eElt_add_mul_inv_mem hC hSq hCm u u'
    let q : ↥(dsQ L1 L2 S) :=
      ⟨eElt (v1Frame F.k F.e) (u + u'), eElt_mem_of_forall_mem hQ _⟩
    let r : ↥(dsQ L1 L2 S) :=
      ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩ *
        ⟨eElt (v1Frame F.k F.e) u', eElt_mem_of_forall_mem hQ u'⟩
    have hmem' : ((q * r⁻¹ : ↥(dsQ L1 L2 S)) : G) ∈ centerOf (dsQ L1 L2 S) := by
      simpa [q, r, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    have hone : φ (q * r⁻¹) = 1 := hφZ _ hmem'
    have hqr : φ q = φ r := by
      have h : φ q * (φ r)⁻¹ = 1 := by
        rw [map_mul, map_inv] at hone
        exact hone
      exact mul_inv_eq_one.mp h
    have hχ : χ (u + u') = χ u * χ u' := by
      change φ q = φ ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩ *
        φ ⟨eElt (v1Frame F.k F.e) u', eElt_mem_of_forall_mem hQ u'⟩
      rw [hqr, show r = (⟨eElt (v1Frame F.k F.e) u,
          eElt_mem_of_forall_mem hQ u⟩ : ↥(dsQ L1 L2 S)) *
          ⟨eElt (v1Frame F.k F.e) u', eElt_mem_of_forall_mem hQ u'⟩ from rfl,
        map_mul]
    exact hχ
  have hchiA : ∀ u, χ (v1Diag aO *ᵥ u) = χ u := by
    intro u
    have hmem : F.a * eElt (v1Frame F.k F.e) u * F.a⁻¹ *
        (eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u))⁻¹ ∈
        centerOf (dsQ L1 L2 S) :=
      conj_eElt_mul_inv_mem hC hSq hCm (v1Diag aO) F.act_a u
    let na : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) :=
      ⟨F.a, v1N_le F (Subgroup.subset_closure (by simp))⟩
    let m : ↥(dsQ L1 L2 S) :=
      ⟨F.a * eElt (v1Frame F.k F.e) u * F.a⁻¹,
        (Subgroup.mem_normalizer_iff.mp
          (P_le_normalizer_dsQ_left L1 L2 S (Subgroup.mem_sup_left F.a_mem.1)) _).mp
          (eElt_mem_of_forall_mem hQ u)⟩
    let v : ↥(dsQ L1 L2 S) :=
      ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩
    let w : ↥(dsQ L1 L2 S) :=
      ⟨eElt (v1Frame F.k F.e) (v1Diag aO *ᵥ u),
        eElt_mem_of_forall_mem hQ _⟩
    have heq : (φ m : G') = (e na : G') * (φ v : G') * (e na : G')⁻¹ :=
      hφN na (Subgroup.subset_closure (by simp [na])) v m rfl
    have hcentral : (e na : G') * (φ v : G') * (e na : G')⁻¹ = φ v :=
      ha na rfl (φ v) (φ v).2
    have hmw : ((m * w⁻¹ : ↥(dsQ L1 L2 S)) : G) ∈ centerOf (dsQ L1 L2 S) := by
      simpa [m, w, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    have hone : φ (m * w⁻¹) = 1 := hφZ _ hmw
    have hφm : φ m = φ w := by
      have h : φ m * (φ w)⁻¹ = 1 := by
        rw [map_mul, map_inv] at hone
        exact hone
      exact mul_inv_eq_one.mp h
    apply Subtype.ext
    change (φ w : G') = (φ v : G')
    rw [show (φ w : G') = (φ m : G') from congrArg Subtype.val hφm.symm, heq]
    exact hcentral
  have hchiB : ∀ u, χ (v1Diag bO *ᵥ u) = χ u := by
    intro u
    have hmem : F.b * eElt (v1Frame F.k F.e) u * F.b⁻¹ *
        (eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u))⁻¹ ∈
        centerOf (dsQ L1 L2 S) :=
      conj_eElt_mul_inv_mem hC hSq hCm (v1Diag bO) F.act_b u
    let nb : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) :=
      ⟨F.b, v1N_le F (Subgroup.subset_closure (by simp))⟩
    let m : ↥(dsQ L1 L2 S) :=
      ⟨F.b * eElt (v1Frame F.k F.e) u * F.b⁻¹,
        (Subgroup.mem_normalizer_iff.mp
          (P_le_normalizer_dsQ_left L1 L2 S (Subgroup.mem_sup_left F.b_mem.1)) _).mp
          (eElt_mem_of_forall_mem hQ u)⟩
    let v : ↥(dsQ L1 L2 S) :=
      ⟨eElt (v1Frame F.k F.e) u, eElt_mem_of_forall_mem hQ u⟩
    let w : ↥(dsQ L1 L2 S) :=
      ⟨eElt (v1Frame F.k F.e) (v1Diag bO *ᵥ u),
        eElt_mem_of_forall_mem hQ _⟩
    have heq : (φ m : G') = (e nb : G') * (φ v : G') * (e nb : G')⁻¹ :=
      hφN nb (Subgroup.subset_closure (by simp [nb])) v m rfl
    have hcentral : (e nb : G') * (φ v : G') * (e nb : G')⁻¹ = φ v :=
      hb nb rfl (φ v) (φ v).2
    have hmw : ((m * w⁻¹ : ↥(dsQ L1 L2 S)) : G) ∈ centerOf (dsQ L1 L2 S) := by
      simpa [m, w, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    have hone : φ (m * w⁻¹) = 1 := hφZ _ hmw
    have hφm : φ m = φ w := by
      have h : φ m * (φ w)⁻¹ = 1 := by
        rw [map_mul, map_inv] at hone
        exact hone
      exact mul_inv_eq_one.mp h
    apply Subtype.ext
    change (φ w : G') = (φ v : G')
    rw [show (φ w : G') = (φ m : G') from congrArg Subtype.val hφm.symm, heq]
    exact hcentral
  have hchi_shiftA : ∀ u, χ ((v1Diag aO + 1) *ᵥ u) = 1 := by
    intro u
    rw [add_mulVec, one_mulVec, hchi_add, hchiA]
    exact Subtype.ext (by simpa [pow_two] using hZ'2 (χ u : G') (χ u).2)
  have hchi_shiftB : ∀ u, χ ((v1Diag bO + 1) *ᵥ u) = 1 := by
    intro u
    rw [add_mulVec, one_mulVec, hchi_add, hchiB]
    exact Subtype.ext (by simpa [pow_two] using hZ'2 (χ u : G') (χ u).2)
  have hsplit : ∀ u, u = (v1Diag aO + 1) *ᵥ (v1Diag splA *ᵥ u) +
      (v1Diag bO + 1) *ᵥ (v1Diag splB *ᵥ u) := by
    intro u
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, v1Diag_spl_eq, one_mulVec]
  have hchi_one : ∀ u, χ u = 1 := by
    intro u
    rw [hsplit u, hchi_add, hchi_shiftA, hchi_shiftB, mul_one]
  refine MonoidHom.ext fun q => ?_
  obtain ⟨u, y, hyZ, hq⟩ := F.exists_eElt_mul hD q q.2
  have hq' : q = (⟨eElt (v1Frame F.k F.e) u,
      eElt_mem_of_forall_mem hQ u⟩ : ↥(dsQ L1 L2 S)) *
      ⟨y, centerOf_le_self _ hyZ⟩ := Subtype.ext hq
  apply Subtype.ext
  rw [hq', map_mul]
  change (φ (⟨eElt (v1Frame F.k F.e) u,
      eElt_mem_of_forall_mem hQ u⟩ : ↥(dsQ L1 L2 S)) : G') *
      (φ ⟨y, centerOf_le_self _ hyZ⟩ : G') = 1
  rw [show (φ (⟨eElt (v1Frame F.k F.e) u,
        eElt_mem_of_forall_mem hQ u⟩ : ↥(dsQ L1 L2 S)) : G') = 1 from
      congrArg Subtype.val (hchi_one u),
    show (φ ⟨y, centerOf_le_self _ hyZ⟩ : G') = 1 from
      congrArg Subtype.val (hφZ ⟨y, centerOf_le_self _ hyZ⟩ hyZ)]
  simp

theorem G24Frame1.crossedHomPrincipal [Finite G] {G' : Type} [Group G'] [Finite G']
    (F : G24Frame1 L1 L2 S) (hD : G24LocalData L1 L2 S) {Z' R' : Subgroup G'}
    (e : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) ≃* ↥R')
    (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a) (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (ha : ∀ r : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (r : G) = F.a → ∀ z ∈ Z', (e r : G') * z * (e r : G')⁻¹ = z)
    (hb : ∀ r : ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)),
      (r : G) = F.b → ∀ z ∈ Z', (e r : G') * z * (e r : G')⁻¹ = z) :
    CrossedHomPrincipal (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S))
      ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({F.k} : Set G)) Z' R' e := by
  classical
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ :=
    exists_secRep (v1SecHyp F hD)
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hN := crossedHomPrincipalOn_of_secRep (Q := dsQ L1 L2 S)
    (Z := centerOf (dsQ L1 L2 S)) (R := (L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({F.k} : Set G)) (N := v1N F) e
    (F.special_data hD).1 (v1N_le F) hZ'c hZ'2 (v1NZ' F e ha hb) s (v1Rep s)
    (fun _ _ => rfl) (v1Form F hD s) (v1Form_invariant F hD s)
    (v1Form_nondegenerate F hD s) (v1H1 F hD s)
  exact crossedHomPrincipal_of_normal e (F.special_data hD).1
    (F.special_data hD).2.2.2.2.2.2.1 hR'Z' hZ'c (v1N_le F) (v1N_normal F) hN
    (v1Fix F hD e hZ'2 ha hb)

end CFSG.Quasithin.F112R.St84

end
