module

public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That
public import CFSG.Fischer.Classification.PartIII.Beta.Data

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open scoped Matrix Pointwise
open CFSG.Fischer.Classification.Beta
open CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.H13.F431.U42 (L0S wordP Xs_eq card_Xs)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 tauFun tauPerm x45 y45 f45)

local notation "AhMat" => Matrix (Fin 6) (Fin 6) (ZMod 3)

@[expose] def pt45 (k : Fin 45) : V6 :=
  ![CFSG.Fischer.Classification.Beta.oPt k 2, CFSG.Fischer.Classification.Beta.oPt k 3,
    CFSG.Fischer.Classification.Beta.oPt k 0, CFSG.Fischer.Classification.Beta.oPt k 1,
    CFSG.Fischer.Classification.Beta.oPt k 4, 0]

@[expose, irreducible] def ahLab (v : V6) : Fin 45 := oIdx ![v 2, v 3, v 0, v 1, v 4]

theorem ahLab_pt45_pm : ∀ k : Fin 45, ahLab (pt45 k) = k ∧ ahLab (-pt45 k) = k := by
  decide +kernel

theorem ah_qV_pt45 : ∀ k : Fin 45, qV (pt45 k) = 1 := by decide +kernel

theorem ahK1 : ∀ k j : Fin 45, -(pt45 j - bil (pt45 j) (pt45 k) • pt45 k) = pt45 (tauFun k j) ∨
    -(pt45 j - bil (pt45 j) (pt45 k) • pt45 k) = -pt45 (tauFun k j) := by decide +kernel

theorem ahLab_vec : ∀ a b c d e : ZMod 3, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 1 →
    pt45 (ahLab ![a, b, c, d, e, 0]) = ![a, b, c, d, e, 0] ∨
    pt45 (ahLab ![a, b, c, d, e, 0]) = -![a, b, c, d, e, 0] := by decide +kernel

theorem ah_pt45_last (k : Fin 45) : pt45 k 5 = 0 := rfl

theorem ahLab_pt45 (k : Fin 45) : ahLab (pt45 k) = k := (ahLab_pt45_pm k).1

theorem ahLab_neg_pt45 (k : Fin 45) : ahLab (-pt45 k) = k := (ahLab_pt45_pm k).2

theorem ahLab_spec {v : V6} (h5 : v 5 = 0) (hq : qV v = 1) :
    v = pt45 (ahLab v) ∨ v = -pt45 (ahLab v) := by
  obtain ⟨a, b, c, d, e, rfl⟩ : ∃ a b c d e : ZMod 3, v = ![a, b, c, d, e, 0] :=
    ⟨v 0, v 1, v 2, v 3, v 4, by
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h5⟩
  have hq' : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 1 := by
    simpa [qV] using hq
  rcases ahLab_vec a b c d e hq' with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem ah_mulVec_last {g : GL6} (hg : g ∈ M0Dot) {v : V6} (hv : v 5 = 0) :
    ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) 5 = 0 := by
  have hB : ∀ j : Fin 5, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) 5 j.castSucc = 0 :=
    (blockDiag_of_mem_OPt (M0Dot_le_OPt hg)).2
  show (∑ j : Fin 6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) 5 j * v j) = 0
  rw [Fin.sum_univ_castSucc]
  simp [hB, hv]

@[expose] def ahAct (g : ↥M0Dot) (k : Fin 45) : Fin 45 := ahLab ((g : GL6) • pt45 k)

theorem ahAct_spec (g : ↥M0Dot) (k : Fin 45) :
    (g : GL6) • pt45 k = pt45 (ahAct g k) ∨ (g : GL6) • pt45 k = -pt45 (ahAct g k) := by
  refine ahLab_spec ?_ ?_
  · exact ah_mulVec_last g.2 (ah_pt45_last k)
  · exact (qV_smul_of_mem_MDot g.2.1 _).trans (ah_qV_pt45 k)

theorem ahAct_eq_iff (g : ↥M0Dot) (k j : Fin 45) :
    ahAct g k = j ↔
      ((g : GL6) • pt45 k = pt45 j ∨ (g : GL6) • pt45 k = -pt45 j) := by
  constructor
  · rintro rfl
    exact ahAct_spec g k
  · intro h
    unfold ahAct
    rcases h with h | h <;> rw [h]
    · exact ahLab_pt45 j
    · exact ahLab_neg_pt45 j

theorem ahAct_one (k : Fin 45) : ahAct 1 k = k :=
  (ahAct_eq_iff 1 k k).2 (Or.inl (one_smul _ _))

theorem ahAct_mul (g h : ↥M0Dot) (k : Fin 45) : ahAct (g * h) k = ahAct g (ahAct h k) := by
  rw [ahAct_eq_iff]
  have e : ((g * h : ↥M0Dot) : GL6) • pt45 k = (g : GL6) • ((h : GL6) • pt45 k) := mul_smul _ _ _
  rw [e]
  rcases ahAct_spec h k with h1 | h1
  · rw [h1]
    exact ahAct_spec g _
  · rw [h1]
    have e2 : (g : GL6) • (-pt45 (ahAct h k)) = -((g : GL6) • pt45 (ahAct h k)) :=
      Matrix.mulVec_neg _ _
    rw [e2]
    rcases ahAct_spec g (ahAct h k) with h2 | h2
    · right
      rw [h2]
    · left
      rw [h2, neg_neg]

theorem ahAct_left_inv (g : ↥M0Dot) (k : Fin 45) : ahAct g⁻¹ (ahAct g k) = k := by
  rw [← ahAct_mul, inv_mul_cancel, ahAct_one]

theorem ahAct_right_inv (g : ↥M0Dot) (k : Fin 45) : ahAct g (ahAct g⁻¹ k) = k := by
  rw [← ahAct_mul, mul_inv_cancel, ahAct_one]

@[expose] def ahPerm (g : ↥M0Dot) : Equiv.Perm (Fin 45) :=
  ⟨ahAct g, ahAct g⁻¹, ahAct_left_inv g, ahAct_right_inv g⟩

theorem ahPerm_apply (g : ↥M0Dot) (k : Fin 45) : ahPerm g k = ahAct g k := rfl

theorem ahPerm_mul (g h : ↥M0Dot) : ahPerm (g * h) = ahPerm g * ahPerm h := by
  refine Equiv.ext fun k => ?_
  rw [Equiv.Perm.mul_apply, ahPerm_apply, ahPerm_apply, ahPerm_apply]
  exact ahAct_mul g h k

@[expose] noncomputable def act45 : ↥M0Dot →* Equiv.Perm (Fin 45) :=
  MonoidHom.mk' ahPerm ahPerm_mul

theorem act45_eq_iff (g : ↥M0Dot) (k j : Fin 45) :
    act45 g k = j ↔
      ((g : GL6) • pt45 k = pt45 j ∨ (g : GL6) • pt45 k = -pt45 j) :=
  ahAct_eq_iff g k j

theorem ah_pt45_basis :
    pt45 20 = xvec 0 ∧ pt45 24 = xvec 1 ∧ pt45 15 = xvec 2 ∧ pt45 16 = xvec 3 ∧
      pt45 0 = xvec 4 := by
  decide +kernel

theorem ah_diag_of_pm {g : GL6}
    (h : ∀ j : Fin 6, (g : AhMat) *ᵥ xvec j = xvec j ∨ (g : AhMat) *ᵥ xvec j = -xvec j) :
    ∃ ε : Fin 6 → ZMod 3, (∀ i, ε i ≠ 0) ∧ (g : AhMat) = Matrix.diagonal ε := by
  have h' : ∀ j : Fin 6, ∃ e : ZMod 3, (e = 1 ∨ e = -1) ∧ (g : AhMat) *ᵥ xvec j = e • xvec j := by
    intro j
    rcases h j with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h1, neg_one_smul]⟩
  choose ε hε1 hε2 using h'
  refine ⟨ε, fun i => ?_, ?_⟩
  · rcases hε1 i with h | h <;> rw [h] <;> decide
  · ext i j
    have h2 := congrFun (hε2 j) i
    rw [mulVec_xvec] at h2
    rw [h2, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul, mono_xvec_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

theorem ah_sign_key1 : ∀ ε : Fin 6 → ZMod 3, (∀ i, ε i ≠ 0) →
    ((fun i => ε i * pt45 1 i) = pt45 1 ∨ (fun i => ε i * pt45 1 i) = -pt45 1) →
    ε 1 = ε 0 ∧ ε 3 = ε 0 ∧ ε 4 = ε 0 := by
  decide +kernel

theorem ah_sign_key3 : ∀ ε : Fin 6 → ZMod 3, (∀ i, ε i ≠ 0) →
    ((fun i => ε i * pt45 3 i) = pt45 3 ∨ (fun i => ε i * pt45 3 i) = -pt45 3) →
    ε 1 = ε 0 ∧ ε 2 = ε 0 ∧ ε 4 = ε 0 := by
  decide +kernel

theorem act45_injective : Function.Injective act45 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ k : Fin 45, ((g : GL6) • pt45 k = pt45 k ∨ (g : GL6) • pt45 k = -pt45 k) := by
    intro k
    rw [← act45_eq_iff, hg]
    rfl
  obtain ⟨h20, h24, h15, h16, h0⟩ := ah_pt45_basis
  have hx : ∀ j : Fin 6, ((g : GL6) : AhMat) *ᵥ xvec j = xvec j ∨
      ((g : GL6) : AhMat) *ᵥ xvec j = -xvec j := by
    intro j
    fin_cases j
    · have := hfix 20
      rw [h20] at this
      exact this
    · have := hfix 24
      rw [h24] at this
      exact this
    · have := hfix 15
      rw [h15] at this
      exact this
    · have := hfix 16
      rw [h16] at this
      exact this
    · have := hfix 0
      rw [h0] at this
      exact this
    · exact M0Dot_mulVec_x6 g.2
  obtain ⟨ε, hne, hdiag⟩ := ah_diag_of_pm hx
  have h1 : ((g : GL6) : AhMat) *ᵥ pt45 1 = pt45 1 ∨ ((g : GL6) : AhMat) *ᵥ pt45 1 = -pt45 1 :=
    hfix 1
  have h3 : ((g : GL6) : AhMat) *ᵥ pt45 3 = pt45 3 ∨ ((g : GL6) : AhMat) *ᵥ pt45 3 = -pt45 3 :=
    hfix 3
  have hmd : ∀ v w : V6, (Matrix.diagonal v *ᵥ w) = fun i => v i * w i := fun v w =>
    funext (Matrix.mulVec_diagonal v w)
  rw [hdiag, hmd] at h1 h3
  obtain ⟨e1, e3, e4⟩ := ah_sign_key1 ε hne h1
  obtain ⟨-, e2, -⟩ := ah_sign_key3 ε hne h3
  refine Subtype.ext (eq_one_of_diag_mem_MDot g.2.1 (c := ε 0) (ε := ε 5) ?_)
  rw [hdiag]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · rfl

theorem ah_qV_pt45_ne (k : Fin 45) : qV (pt45 k) ≠ 0 := by
  rw [ah_qV_pt45]
  exact one_ne_zero

@[expose] def refl45 (k : Fin 45) : GL6 :=
  -1 * refl6 (pt45 k) (ah_qV_pt45_ne k) * refl6 x6 qV_x6_ne_zero

theorem refl45_mulVec (k : Fin 45) {v : V6} (hv : v 5 = 0) :
    ((refl45 k : GL6) : AhMat) *ᵥ v = -(v - bil v (pt45 k) • pt45 k) := by
  have h6 : ((refl6 x6 qV_x6_ne_zero : GL6) : AhMat) *ᵥ v = v :=
    refl6_mulVec_of_bil_eq_zero x6 qV_x6_ne_zero (by rw [bil_x6]; exact hv)
  have hk : ((refl6 (pt45 k) (ah_qV_pt45_ne k) : GL6) : AhMat) *ᵥ v =
      v - bil v (pt45 k) • pt45 k := by
    rw [refl6_mulVec, ah_qV_pt45, inv_one, one_mul]
  show ((-1 * refl6 (pt45 k) (ah_qV_pt45_ne k) * refl6 x6 qV_x6_ne_zero : GL6) : AhMat) *ᵥ v = _
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h6, hk,
    Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem ah_eJ_Iset_mulVec (x : V6) :
    ((eJ Iset : GL6) : AhMat) *ᵥ x = -(((refl6 x6 qV_x6_ne_zero : GL6) : AhMat) *ᵥ x) := by
  have h6 : ((refl6 x6 qV_x6_ne_zero : GL6) : AhMat) *ᵥ x = Function.update x 5 (-x 5) :=
    refl6_xvec_mulVec 5 x
  rw [h6, eJ_val_mulVec]
  funext i
  by_cases hi : i = 5
  · subst hi
    rw [eJd_eq_one_of_notMem (by decide), Pi.neg_apply, Function.update_self]
    simp
  · rw [eJd_eq_neg_one_of_mem (by revert i; decide), Pi.neg_apply, Function.update_of_ne hi]
    simp

theorem refl45_eq (k : Fin 45) :
    refl45 k = refl6 (pt45 k) (ah_qV_pt45_ne k) * eJ Iset := by
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro x
  show ((-1 * refl6 (pt45 k) (ah_qV_pt45_ne k) * refl6 x6 qV_x6_ne_zero : GL6) : AhMat) *ᵥ x = _
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec, Units.val_mul,
    ← Matrix.mulVec_mulVec, ah_eJ_Iset_mulVec, Matrix.mulVec_neg]

theorem refl45_mem_MDot (k : Fin 45) : refl45 k ∈ MDot := by
  obtain ⟨l, hl, hlen, he⟩ := eJ_eq_prod Iset (Finset.Subset.refl _)
  have hprod : refl45 k = ((⟨pt45 k, ah_qV_pt45_ne k⟩ :: l).map reflOf).prod := by
    rw [refl45_eq, List.map_cons, List.prod_cons, he]
    rfl
  rw [hprod, prod_refl_mem_MDot_iff, List.length_cons, hlen]
  refine ⟨⟨3, by decide⟩, ?_⟩
  have h0 : (⟨pt45 k, ah_qV_pt45_ne k⟩ :: l).countP (fun v => qV v.1 = -1) = 0 := by
    refine List.countP_eq_zero.2 fun v hv => ?_
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [ah_qV_pt45]
      decide
    · rw [hl v hv]
      decide
  rw [h0]
  exact ⟨0, rfl⟩

theorem refl45_mulVec_x6 (k : Fin 45) : ((refl45 k : GL6) : AhMat) *ᵥ x6 = x6 := by
  rw [refl45_eq, Units.val_mul, ← Matrix.mulVec_mulVec, eJ_mulVec_x6 Iset (Finset.Subset.refl _)]
  exact refl6_mulVec_x6_of_last _ _ (ah_pt45_last k)

theorem refl45_mem_GDot (k : Fin 45) : refl45 k ∈ GDot :=
  mem_GDot_iff.2 ⟨refl45_mem_MDot k, refl45_mulVec_x6 k⟩

theorem refl45_mem_M0Dot (k : Fin 45) : refl45 k ∈ M0Dot :=
  GDot_le_M0Dot (refl45_mem_GDot k)

@[expose] def refl45El (k : Fin 45) : ↥M0Dot := ⟨refl45 k, refl45_mem_M0Dot k⟩

theorem act45_refl45 (k : Fin 45) : act45 (refl45El k) = tauPerm k := by
  refine Equiv.ext fun j => ?_
  rw [act45_eq_iff]
  show ((refl45 k : GL6) : AhMat) *ᵥ pt45 j = pt45 (tauFun k j) ∨
    ((refl45 k : GL6) : AhMat) *ᵥ pt45 j = -pt45 (tauFun k j)
  rw [refl45_mulVec k (ah_pt45_last j)]
  exact ahK1 k j

@[expose] def ahZ : ↥M0Dot := ⟨zDot, GDot_le_M0Dot zDot_mem_GDot⟩

theorem ahK_z : ∀ j : Fin 45, ahLab (((zDot : GL6) : AhMat) *ᵥ pt45 j) = x45 j := by
  decide +kernel

theorem act45_ahZ : act45 ahZ = x45 := Equiv.ext ahK_z

@[expose] def ahY : ↥M0Dot := refl45El 31 * refl45El 5 * refl45El 36 * refl45El 44

theorem act45_ahY : act45 ahY = y45 := by
  rw [ahY, map_mul, map_mul, map_mul, act45_refl45, act45_refl45, act45_refl45, act45_refl45]
  rfl

@[expose] def ahF : ↥M0Dot :=
  ⟨fDot, fDot_mem_M0Dot⟩ * ⟨eJ {2, 4}, GDot_le_M0Dot (eJ_mem_GDot {2, 4} (by decide) (by decide))⟩

theorem ahK_F : ∀ j : Fin 45, ahLab (((fDot * eJ {2, 4} : GL6) : AhMat) *ᵥ pt45 j) = f45 j := by
  decide +kernel

theorem act45_ahF : act45 ahF = f45 := Equiv.ext ahK_F

@[expose] def ahFh : ↥M0Dot := ⟨fDot, fDot_mem_M0Dot⟩

theorem ahK_fh : ∀ j : Fin 45, ahLab (((fDot : GL6) : AhMat) *ᵥ pt45 j) = fhat j := by
  decide +kernel

theorem act45_ahFh : act45 ahFh = fhat := Equiv.ext ahK_fh

theorem range_act45 : act45.range = QA45.originalSubgroup := by
  have h1 : QA45.originalSubgroup ≤ act45.range := by
    rw [CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45_closure, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact ⟨ahZ, act45_ahZ⟩
    · exact ⟨ahY, act45_ahY⟩
    · exact ⟨ahF, act45_ahF⟩
  have h2 : Nat.card act45.range = Nat.card QA45.originalSubgroup := by
    rw [card_A, ← Nat.card_congr (MonoidHom.ofInjective act45_injective).toEquiv, card_M0Dot]
  exact (Subgroup.eq_of_le_of_card_ge h1 h2.le).symm

@[expose] noncomputable def lamA : Ah ≃* ↥M0Dot :=
  ((MonoidHom.ofInjective act45_injective).trans (MulEquiv.subgroupCongr range_act45)).symm

theorem act45_lamA (a : Ah) :
    act45 (lamA a) = (a : Equiv.Perm (Fin 45)) := by
  show act45 ((MonoidHom.ofInjective act45_injective).symm
    ((MulEquiv.subgroupCongr range_act45).symm a)) = _
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem lamA_eq_iff (a : Ah)
    (g : ↥M0Dot) : lamA a = g ↔ act45 g = (a : Equiv.Perm (Fin 45)) := by
  constructor
  · rintro rfl
    exact act45_lamA a
  · intro h
    apply act45_injective
    rw [act45_lamA, h]

theorem lamA_fhatA :
    ((lamA fhatA : ↥M0Dot) : GL6) = fDot := by
  have h : lamA fhatA = ahFh :=
    (lamA_eq_iff _ _).2 (by rw [act45_ahFh]; rfl)
  rw [h]
  rfl

theorem lamA_xA :
    ((lamA xA : ↥M0Dot) : GL6) = zDot := by
  have h : lamA xA = ahZ :=
    (lamA_eq_iff _ _).2 (by rw [act45_ahZ, ← CFSG.Quasithin.H13.F431.U42.x45_eq]; rfl)
  rw [h]
  rfl

theorem ah_stab_fwd {g : GL6} (hg : g ∈ M0Dot) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (h5 : (g : AhMat) *ᵥ x5 = ε • x5) {v : V6} (hv : v 4 = 0 ∧ v 5 = 0) :
    ((g : AhMat) *ᵥ v) 4 = 0 ∧ ((g : AhMat) *ᵥ v) 5 = 0 := by
  refine ⟨?_, ah_mulVec_last hg hv.2⟩
  have hb := bil_mulVec_of_mem_OVq (MDot_le_OVq hg.1) v x5
  rw [h5, bil_smul_right, show x5 = xvec 4 from rfl, mono_bil_xvec_right _ (by decide),
    mono_bil_xvec_right _ (by decide), hv.1, mul_zero] at hb
  have hε0 : ε ≠ 0 := by
    rcases hε with rfl | rfl <;> decide
  exact quat_two_mul_eq_zero _ ((mul_eq_zero.1 hb).resolve_left hε0)

theorem ah_mem_M1Dot_iff {g : GL6} (hg : g ∈ M0Dot) :
    g ∈ M1Dot ↔ ((g : AhMat) *ᵥ x5 = x5 ∨ (g : AhMat) *ᵥ x5 = -x5) := by
  rw [M1Dot_eq_stab, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hs⟩
    have hS := quat_stab_iff hs
    have hOV : g ∈ OVq := MDot_le_OVq hg.1
    have hx5 : x5 0 = 0 ∧ x5 1 = 0 ∧ x5 2 = 0 ∧ x5 3 = 0 := by decide
    have hq : qV ((g : AhMat) *ᵥ x5) = 1 := (qV_mulVec_of_mem_OVq hOV x5).trans (by decide)
    have h5 : ((g : AhMat) *ᵥ x5) 5 = 0 := ah_mulVec_last hg (by decide)
    have h0 : ∀ j : Fin 6, j.val < 4 → ((g : AhMat) *ᵥ x5) j = 0 := fun j hj =>
      quat_perp hOV hS x5 hx5 j hj
    obtain ⟨a, b, c, d, e, f, hw⟩ :
        ∃ a b c d e f : ZMod 3, (g : AhMat) *ᵥ x5 = ![a, b, c, d, e, f] :=
      ⟨_, _, _, _, _, _, by
        funext i
        fin_cases i <;> rfl⟩
    have ha : a = 0 := by simpa [hw] using h0 0 (by decide)
    have hb : b = 0 := by simpa [hw] using h0 1 (by decide)
    have hc : c = 0 := by simpa [hw] using h0 2 (by decide)
    have hd : d = 0 := by simpa [hw] using h0 3 (by decide)
    have hf : f = 0 := by simpa [hw] using h5
    subst ha hb hc hd hf
    rw [hw] at hq ⊢
    have he : e ^ 2 = 1 := by simpa [qV] using hq
    have key : ∀ e : ZMod 3, e ^ 2 = 1 → ![0, 0, 0, 0, e, 0] = x5 ∨ ![0, 0, 0, 0, e, 0] = -x5 := by
      decide
    exact key e he
  · intro h5
    refine ⟨hg.1, (quat_mem_stabilizer_iff g V4plus).2 fun v => ?_⟩
    rw [quat_mem_V4plus_iff, quat_smul_def, quat_mem_V4plus_iff]
    obtain ⟨ε, hε, hgε⟩ : ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ (g : AhMat) *ᵥ x5 = ε • x5 := by
      rcases h5 with h | h
      · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
      · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
    have hε2 : ε * ε = 1 := by
      rcases hε with rfl | rfl <;> decide
    have e1 : x5 = ε • (((g⁻¹ : GL6) : AhMat) *ᵥ x5) := by
      have h1 := mono_inv_mulVec g x5
      rw [hgε, Matrix.mulVec_smul] at h1
      exact h1.symm
    have hinv : ((g⁻¹ : GL6) : AhMat) *ᵥ x5 = ε • x5 := by
      calc ((g⁻¹ : GL6) : AhMat) *ᵥ x5
          = (ε * ε) • (((g⁻¹ : GL6) : AhMat) *ᵥ x5) := by rw [hε2, one_smul]
        _ = ε • (ε • (((g⁻¹ : GL6) : AhMat) *ᵥ x5)) := mul_smul _ _ _
        _ = ε • x5 := by rw [← e1]
    refine ⟨fun hv => ah_stab_fwd hg hε hgε hv, fun hv => ?_⟩
    have := ah_stab_fwd (M0Dot.inv_mem hg) hε hinv hv
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this

theorem lamA_mem_M1Dot (a : Ah) :
    ((lamA a : ↥M0Dot) : GL6) ∈ M1Dot ↔ a ∈ P1h := by
  rw [mem_P1h_iff, ah_mem_M1Dot_iff (lamA a).2]
  have hx5 : pt45 0 = x5 := ah_pt45_basis.2.2.2.2
  have h := act45_eq_iff (lamA a) 0 0
  rw [act45_lamA, hx5] at h
  exact h.symm

@[expose] def ahLine : Fin 5 → Fin 45 := ![20, 24, 15, 16, 0]

theorem ahLine_spec : ∀ i : Fin 5, pt45 (ahLine i) = xvec i.castSucc := by decide +kernel

theorem ahL0S : ∀ k : Fin 45, k ∈ L0S ↔ ∃ i : Fin 5, k = ahLine i := by
  intro k
  show k.val ∈ U42F431.L0 ↔ _
  revert k
  decide +kernel

theorem ah_line_of_act (g : ↥M0Dot)
    (h : ∀ k ∈ L0S, act45 g k ∈ L0S)
    (i : Fin 5) : ∃ j : Fin 5, ((g : GL6) : AhMat) *ᵥ xvec i.castSucc = xvec j.castSucc ∨
      ((g : GL6) : AhMat) *ᵥ xvec i.castSucc = -xvec j.castSucc := by
  obtain ⟨j, hj⟩ := (ahL0S _).1 (h (ahLine i) ((ahL0S _).2 ⟨i, rfl⟩))
  refine ⟨j, ?_⟩
  have := (act45_eq_iff g (ahLine i) (ahLine j)).1 hj
  rwa [ahLine_spec, ahLine_spec] at this

theorem ah_act_of_line (g : ↥M0Dot)
    (h : ∀ i : Fin 5, ∃ j : Fin 5, ((g : GL6) : AhMat) *ᵥ xvec i.castSucc = xvec j.castSucc ∨
      ((g : GL6) : AhMat) *ᵥ xvec i.castSucc = -xvec j.castSucc)
    (k : Fin 45) (hk : k ∈ L0S) :
    act45 g k ∈ L0S := by
  obtain ⟨i, rfl⟩ := (ahL0S _).1 hk
  obtain ⟨j, hj⟩ := h i
  rw [ahL0S]
  refine ⟨j, (act45_eq_iff g (ahLine i) (ahLine j)).2 ?_⟩
  rwa [ahLine_spec, ahLine_spec]

theorem ah_mem_stab_Lambda {g : GL6}
    (h1 : ∀ i : Fin 6, ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧ (g : AhMat) *ᵥ xvec i = c • xvec j)
    (h2 : ∀ i : Fin 6, ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧
      ((g⁻¹ : GL6) : AhMat) *ᵥ xvec i = c • xvec j) :
    g ∈ MulAction.stabilizer GL6 Lambda := by
  have key : ∀ (g : GL6) (i j : Fin 6) (c : ZMod 3), c ≠ 0 →
      (g : AhMat) *ᵥ xvec i = c • xvec j → g • spn {xvec i} = spn {xvec j} := by
    intro g i j c hc hci
    rw [mono_smul_spn, mono_smul_xvec, hci]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc) _
  rw [MulAction.mem_stabilizer_iff]
  ext S
  constructor
  · intro hS
    obtain ⟨T, ⟨i, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hS
    obtain ⟨j, c, hc, hci⟩ := h1 i
    exact ⟨j, key g i j c hc hci⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, c, hc, hci⟩ := h2 i
    refine Set.mem_smul_set.2 ⟨spn {xvec j}, ⟨j, rfl⟩, ?_⟩
    rw [← key g⁻¹ i j c hc hci, smul_inv_smul]

theorem ah_line_of_M2Dot {g : GL6} (hg : g ∈ M2Dot) (i : Fin 5) :
    ∃ j : Fin 5, (g : AhMat) *ᵥ xvec i.castSucc = xvec j.castSucc ∨
      (g : AhMat) *ᵥ xvec i.castSucc = -xvec j.castSucc := by
  obtain ⟨j, c, hc, hj⟩ := mono_line_map hg.2 i.castSucc
  have hq := qV_mulVec_of_mem_OVq (MDot_le_OVq hg.1) (xvec i.castSucc)
  rw [hj, mono_qV_smul, mono_qV_xvec, mono_qV_xvec] at hq
  have hc2 : c ^ 2 = 1 := by
    have key : ∀ a : ZMod 3, a ≠ 0 → a ^ 2 = 1 := by decide
    exact key _ hc
  have hj5 : j ≠ 5 := by
    rintro rfl
    rw [hc2, if_neg (mono_castSucc_ne_five i), if_pos rfl] at hq
    exact absurd hq (by decide)
  rcases mono_fin_cases j with h | ⟨j', rfl⟩
  · exact absurd h hj5
  · refine ⟨j', ?_⟩
    have key : ∀ a : ZMod 3, a ^ 2 = 1 → a = 1 ∨ a = -1 := by decide
    rcases key c hc2 with rfl | rfl
    · left
      rw [hj, one_smul]
    · right
      rw [hj, neg_one_smul]

theorem ah_lines_of_pm (g : ↥M0Dot)
    (h : ∀ i : Fin 5, ∃ j : Fin 5, ((g : GL6) : AhMat) *ᵥ xvec i.castSucc = xvec j.castSucc ∨
      ((g : GL6) : AhMat) *ᵥ xvec i.castSucc = -xvec j.castSucc) (i : Fin 6) :
    ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧ ((g : GL6) : AhMat) *ᵥ xvec i = c • xvec j := by
  rcases mono_fin_cases i with rfl | ⟨i', rfl⟩
  · rcases M0Dot_mulVec_x6 g.2 with h6 | h6
    · exact ⟨5, 1, one_ne_zero, by rw [one_smul]; exact h6⟩
    · exact ⟨5, -1, by decide, by rw [neg_one_smul]; exact h6⟩
  · obtain ⟨j, hj⟩ := h i'
    rcases hj with hj | hj
    · exact ⟨j.castSucc, 1, one_ne_zero, by rw [hj, one_smul]⟩
    · exact ⟨j.castSucc, -1, by decide, by rw [hj, neg_one_smul]⟩

theorem lamA_mem_M2Dot (a : Ah) :
    ((lamA a : ↥M0Dot) : GL6) ∈ M2Dot ↔ a ∈ P2h := by
  constructor
  · intro hM
    rw [mem_P2h_iff]
    have hM' : ((lamA a⁻¹ : ↥M0Dot) : GL6) ∈ M2Dot := by
      rw [map_inv]
      exact M2Dot.inv_mem hM
    have h1 : ∀ k ∈ L0S, (a : Equiv.Perm (Fin 45)) k ∈ L0S := by
      intro k hk
      have := ah_act_of_line (lamA a) (ah_line_of_M2Dot hM) k hk
      rwa [act45_lamA] at this
    have h2 : ∀ k ∈ L0S, ((a⁻¹ : Ah) : Equiv.Perm (Fin 45)) k ∈ L0S := by
      intro k hk
      have := ah_act_of_line (lamA a⁻¹) (ah_line_of_M2Dot hM') k hk
      rwa [act45_lamA] at this
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact h1 k hk
    · intro y hy
      refine ⟨((a⁻¹ : Ah) : Equiv.Perm (Fin 45)) y, h2 y hy, ?_⟩
      exact Equiv.apply_symm_apply _ _
  · intro hP
    have hP' : a⁻¹ ∈ P2h := Subgroup.inv_mem _ hP
    rw [mem_P2h_iff] at hP hP'
    have h1 : ∀ k ∈ L0S, act45 (lamA a) k ∈ L0S := by
      intro k hk
      rw [act45_lamA]
      have : (a : Equiv.Perm (Fin 45)) k ∈ (a : Equiv.Perm (Fin 45)) '' L0S := ⟨k, hk, rfl⟩
      rwa [hP] at this
    have h2 : ∀ k ∈ L0S, act45 (lamA a⁻¹) k ∈ L0S := by
      intro k hk
      rw [act45_lamA]
      have : ((a⁻¹ : Ah) : Equiv.Perm (Fin 45)) k ∈
          ((a⁻¹ : Ah) : Equiv.Perm (Fin 45)) '' L0S := ⟨k, hk, rfl⟩
      rwa [hP'] at this
    refine ⟨(lamA a).2.1, ah_mem_stab_Lambda (ah_lines_of_pm (lamA a) (ah_line_of_act _ h1)) ?_⟩
    have := ah_lines_of_pm (lamA a)⁻¹ (by
      rw [← map_inv]
      exact ah_line_of_act _ h2)
    exact this

theorem ah_card_QP45 : Nat.card QP45.originalSubgroup = 25920 := by
  rw [← Xs_eq]
  exact card_Xs

theorem ah_QP45_eq_map :
    QP45.originalSubgroup = (GDot.subgroupOf M0Dot).map act45 := by
  have hr : ∀ k : Fin 45, refl45El k ∈ GDot.subgroupOf M0Dot := fun k => refl45_mem_GDot k
  have hle : QP45.originalSubgroup ≤ (GDot.subgroupOf M0Dot).map act45 := by
    rw [CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45_closure, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨ahZ, zDot_mem_GDot, act45_ahZ⟩
    · exact ⟨ahY, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hr 31) (hr 5))
        (hr 36)) (hr 44), act45_ahY⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective act45_injective, ah_card_QP45,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe GDot_le_M0Dot).toEquiv, card_GDot]

theorem lamA_mem_GDot (a : Ah) :
    ((lamA a : ↥M0Dot) : GL6) ∈ GDot ↔ a ∈ Yh := by
  rw [mem_Yh_iff, ah_QP45_eq_map]
  constructor
  · intro h
    exact ⟨lamA a, h, act45_lamA a⟩
  · rintro ⟨g, hg, hga⟩
    rw [(lamA_eq_iff a g).2 hga]
    exact hg

open CFSG.Quasithin.SimsF5Lat (f5P1 f5P2 f5LatCert)

@[expose] def ahGen : Fin 6 → GL6
  | 0 => f5P2 * eJ {0, 3}
  | 1 => f5P1 * f5P2 * eJ {0, 1}
  | 2 => eJ {0, 1} * eJ {0, 3} * eJ {0, 4}
  | 3 => eJ {0, 3}
  | 4 => eJ {0, 1} * eJ {0, 3}
  | 5 => fDot

theorem ah_mem_latT {g : GL6}
    (hg : g ∈ [eJ {0, 1}, eJ {0, 2}, eJ {0, 3}, eJ {0, 4}, f5P1, f5P2, fDot]) : g ∈ latT := by
  have h : g ∈ f5LatCert.tGens := by
    rw [tGens_eq]
    exact hg
  exact Subgroup.subset_closure h

theorem ahGen_mem_TDot (i : Fin 6) : ahGen i ∈ TDot := by
  refine latT_le_TDot ?_
  fin_cases i
  · exact Subgroup.mul_mem _ (ah_mem_latT (by simp)) (ah_mem_latT (by simp))
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ah_mem_latT (by simp)) (ah_mem_latT (by simp)))
      (ah_mem_latT (by simp))
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ah_mem_latT (by simp)) (ah_mem_latT (by simp)))
      (ah_mem_latT (by simp))
  · exact ah_mem_latT (g := eJ {0, 3}) (by simp)
  · exact Subgroup.mul_mem _ (ah_mem_latT (by simp)) (ah_mem_latT (by simp))
  · exact ah_mem_latT (g := fDot) (by simp)

theorem ahGen_mem_M0Dot (i : Fin 6) : ahGen i ∈ M0Dot :=
  (TDot_le_M12.trans (inf_le_left.trans M1Dot_le_M0Dot)) (ahGen_mem_TDot i)

@[expose] def ahGel (i : Fin 6) : ↥M0Dot := ⟨ahGen i, ahGen_mem_M0Dot i⟩

theorem ahK_gen : ∀ k : Fin 5, ∀ j : Fin 45,
    ahLab (((ahGen k.castSucc : GL6) : AhMat) *ᵥ pt45 j) =
      wordP (U42F431.TgW.getD k []) j := by
  decide +kernel

theorem act45_ahGel (k : Fin 5) :
    act45 (ahGel k.castSucc) = ((gTA k : Ah) : Equiv.Perm (Fin 45)) :=
  Equiv.ext (ahK_gen k)

@[expose] def ahWords : List (List (Fin 6)) :=
  [[], [0], [1], [2], [3], [4], [5], [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [1, 0],
    [1, 2], [1, 3], [1, 4], [1, 5], [2, 0], [2, 1], [2, 3], [2, 4], [2, 5], [3, 0], [3, 4], [3, 5],
    [4, 1], [4, 5], [5, 0], [5, 1], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 0, 3], [0, 0, 4],
    [0, 0, 5], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 1, 5], [0, 2, 1], [0, 2, 3], [0, 2, 4],
    [0, 2, 5], [0, 3, 4], [0, 3, 5], [0, 4, 1], [0, 5, 0], [0, 5, 1], [1, 0, 2], [1, 0, 3],
    [1, 0, 5], [1, 2, 0], [1, 2, 3], [1, 2, 4], [1, 2, 5], [1, 3, 4], [1, 4, 5], [1, 5, 0],
    [1, 5, 1], [2, 0, 1], [2, 0, 2], [2, 0, 3], [2, 0, 4], [2, 0, 5], [2, 1, 0], [2, 1, 2],
    [2, 1, 3], [2, 1, 4], [2, 1, 5], [2, 3, 0], [2, 3, 4], [2, 3, 5], [2, 4, 1], [2, 4, 5],
    [2, 5, 0], [2, 5, 1], [3, 0, 2], [3, 0, 4], [3, 0, 5], [3, 4, 1], [3, 4, 5], [3, 5, 1],
    [4, 1, 2], [4, 1, 5], [4, 5, 0], [5, 0, 1], [5, 0, 2], [5, 0, 3], [5, 1, 0], [5, 1, 2],
    [5, 1, 4], [0, 0, 0, 5], [0, 0, 1, 5], [0, 0, 2, 3], [0, 0, 2, 4], [0, 0, 2, 5], [0, 0, 3, 4],
    [0, 0, 5, 0], [0, 0, 5, 1], [0, 1, 2, 3], [0, 1, 2, 5], [0, 1, 3, 4], [0, 1, 4, 5],
    [0, 2, 1, 5], [0, 2, 3, 0], [0, 2, 3, 5], [0, 2, 5, 0], [0, 3, 4, 1], [0, 4, 1, 2],
    [0, 5, 0, 2], [0, 5, 1, 2], [0, 5, 1, 4], [1, 0, 3, 5], [1, 2, 0, 5], [1, 2, 4, 5],
    [1, 5, 0, 2], [1, 5, 1, 2], [2, 0, 1, 5], [2, 0, 3, 5], [2, 1, 0, 5], [2, 1, 4, 5],
    [2, 3, 0, 5], [2, 3, 4, 5], [2, 4, 1, 5], [2, 5, 0, 3], [2, 5, 1, 4], [0, 2, 3, 0, 5]]

@[expose] def ahEval (w : List (Fin 6)) : AhMat := (((w.map ahGen).prod : GL6) : AhMat)

theorem ahWords_nodup : (ahWords.map ahEval).Nodup := by decide +kernel

theorem ahWords_length : ahWords.length = 128 := by decide +kernel

theorem ah_card_gen : 128 ≤ Nat.card (Subgroup.closure (Set.range ahGen)) := by
  set L : List GL6 := ahWords.map fun w => (w.map ahGen).prod with hL
  have hnd : L.Nodup := List.Nodup.of_map Units.val ahWords_nodup
  have hsub : ((L.toFinset : Finset GL6) : Set GL6) ⊆ Subgroup.closure (Set.range ahGen) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hy
    exact Subgroup.subset_closure ⟨t, rfl⟩
  have hcard : L.toFinset.card = 128 := by
    rw [List.toFinset_card_of_nodup hnd, hL, List.length_map, ahWords_length]
  calc 128 = L.toFinset.card := hcard.symm
    _ = ((L.toFinset : Finset GL6) : Set GL6).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ ((Subgroup.closure (Set.range ahGen) : Subgroup GL6) : Set GL6).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (Subgroup.closure (Set.range ahGen)) := (Nat.card_coe_set_eq _).symm

theorem ah_closure_gen : Subgroup.closure (Set.range ahGen) = TDot := by
  have hle : Subgroup.closure (Set.range ahGen) ≤ TDot := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ahGen_mem_TDot i
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_TDot]; exact ah_card_gen)

theorem lamA_gTA (k : Fin 5) :
    lamA (gTA k) = ahGel k.castSucc :=
  (lamA_eq_iff _ _).2 (act45_ahGel k)

theorem lamA_mem_TDot (a : Ah) :
    ((lamA a : ↥M0Dot) : GL6) ∈ TDot ↔ a ∈ That := by
  let φ : Ah →* GL6 := M0Dot.subtype.comp (lamA : Ah ≃* ↥M0Dot).toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp lamA.injective
  have hmap : That.map φ = TDot := by
    rw [That, MonoidHom.map_closure, ← ah_closure_gen]
    congr 1
    ext x
    constructor
    · rintro ⟨y, (⟨k, rfl⟩ | rfl), rfl⟩
      · exact ⟨k.castSucc, by
          show ((ahGel k.castSucc : ↥M0Dot) : GL6) = _
          rw [← lamA_gTA k]
          rfl⟩
      · exact ⟨5, lamA_fhatA.symm⟩
    · rintro ⟨i, rfl⟩
      rcases mono_fin_cases i with rfl | ⟨k, rfl⟩
      · exact ⟨fhatA, Or.inr rfl, lamA_fhatA⟩
      · refine ⟨gTA k, Or.inl ⟨k, rfl⟩, ?_⟩
        show ((lamA (gTA k) : ↥M0Dot) : GL6) = _
        rw [lamA_gTA k]
        rfl
  rw [show ((lamA a : ↥M0Dot) : GL6) = φ a from rfl, ← hmap]
  exact Subgroup.mem_map_iff_mem hφ

end

end CFSG.Quasithin.SimsF5
