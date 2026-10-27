module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.DedekindNormalizer
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

variable {X : Setup Γ G}

namespace Setup

private theorem u4qBase_data {s r d : ℕ} {X : Setup Γ G}
    (C : X.Comm48 s r d) (h1 : d = 1)
    (h2 : X.HasB 0 (d + 1) ∧ 2 * (d + 1) = r ∧
      X.Z ((d : ℤ) + 1) = X.Qg r ∧
      X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 0) ∧
      X.Z 0 ⊓ X.Q ((d : ℤ) + 1) = ⊥ ∧ X.Z 0 ⊓ X.Q (-((d : ℤ) + 1)) = ⊥) :
    r = 4 ∧ s = 5 ∧ X.HasB 0 2 ∧ X.HasB 2 2 ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ Nat.card (X.Z 2) = 2 ^ X.n 0 ∧
      IsElemAbelian 2 (X.Z 0) ∧ IsElemAbelian 2 (X.Z 2) ∧
      X.Z 0 ⊓ X.Q 2 = ⊥ ∧ X.Z 0 ⊓ X.Q (-2) = ⊥ ∧
      X.Z 2 ⊓ X.Q 0 = ⊥ ∧ X.Z 2 ⊓ X.Q 4 = ⊥ := by
  classical
  subst h1
  obtain ⟨hB0', h2r', _, _, hcardZ0, helemZ0, hZ0Q2', hZ0Qm2'⟩ := h2
  have h2r : r = 4 := by omega
  have hs5 : s = 5 := by
    have hle := C.hyp.le_r
    have h5 := C.hyp.five_le
    omega
  have hB0 : X.HasB 0 2 := by simpa using hB0'
  have hB2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 2).mpr hB0
  have hZ0Q2 : X.Z 0 ⊓ X.Q 2 = ⊥ := by simpa using hZ0Q2'
  have hZ0Qm2 : X.Z 0 ⊓ X.Q (-2) = ⊥ := by simpa using hZ0Qm2'
  have hZ2conj : X.Z 2 = conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) := by
    have h := X.Z_add (1 : ℤ) 0
    simpa using h
  have hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0 := by
    rw [hZ2conj, card_conjSub, hcardZ0]
  have helemZ2 : IsElemAbelian 2 (X.Z 2) := by
    rw [hZ2conj]
    exact helemZ0.map (MulAut.conj (X.τ ^ (1 : ℤ))).toMonoidHom
  have hZ2Q0 : X.Z 2 ⊓ X.Q 0 = ⊥ := by
    have hQadd : X.Q 0 = conjSub X.τ (X.Q (-2)) := by
      have h := X.Q_add (1 : ℤ) (-2)
      simpa using h
    have hZ2conj' : X.Z 2 = conjSub X.τ (X.Z 0) := by simpa using hZ2conj
    rw [hZ2conj', hQadd, ← conjSub_inf, hZ0Qm2, conjSub_bot]
  have hZ2Q4 : X.Z 2 ⊓ X.Q 4 = ⊥ := by
    have hQadd4 : X.Q 4 = conjSub X.τ (X.Q 2) := by
      have h := X.Q_add (1 : ℤ) 2
      simpa using h
    have hZ2conj' : X.Z 2 = conjSub X.τ (X.Z 0) := by simpa using hZ2conj
    rw [hZ2conj', hQadd4, ← conjSub_inf, hZ0Q2, conjSub_bot]
  exact ⟨h2r, hs5, hB0, hB2, hcardZ0, hcardZ2, helemZ0, helemZ2,
    hZ0Q2, hZ0Qm2, hZ2Q0, hZ2Q4⟩

private theorem u4qBase_cardS {s r d : ℕ} {X : Setup Γ G}
    (C : X.Comm48 s r d) (hr : r = 4) (hs : s = 5) :
    Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
  have hpGT : pCoreOf 2 X.GT = ⊥ := by
    have hsub : pCoreOf 2 X.GT ≤ X.GT := CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT
    have h := inf_eq_bot_of_odd_of_isPGroup (A := X.GT) (B := pCoreOf 2 X.GT)
      C.hyp.odd_GT (pCoreOf_isPGroup' X.GT)
    rwa [inf_eq_right.mpr hsub] at h
  rw [X.card_S_eq_prod C.hyp.sing, hs]
  have hlong5 : X.arcStab 0 ((5 : ℕ) : ℤ) = X.GT := by
    have h := C.hyp.longReg.2 0 5 (by omega)
    simpa using h
  rw [hlong5, hpGT, Subgroup.card_bot, mul_one]
  rw [show 5 - 1 = 4 by omega]
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  rw [hI]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have h4 : X.n (4 : ℤ) = X.n 0 := by
    rw [show (4 : ℤ) = 2 + 2 * (1 : ℤ) by norm_num, X.n_add, X.n_two]
  have hn1 : X.n ((1 : ℕ) : ℤ) = X.n 1 := by norm_num
  have hn2 : X.n ((2 : ℕ) : ℤ) = X.n 0 := by simpa using X.n_two
  have hn3 : X.n ((3 : ℕ) : ℤ) = X.n 1 := by simpa using X.n_three
  have hn4 : X.n ((4 : ℕ) : ℤ) = X.n 0 := by simpa using h4
  rw [hn1, hn2, hn3, hn4]
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

private theorem u4qBase_cardQ0 {X : Setup Γ G}
    (hcardS : Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1)) :
    Nat.card (X.Q 0) = 2 ^ (X.n 0 + 2 * X.n 1) := by
  have hQ0S : X.Q 0 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow_left 0
  have h := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.S)
  have hinf : X.Q 0 ⊓ X.S = X.Q 0 := inf_of_le_left hQ0S
  rw [show (X.Q 0).relIndex X.S = 2 ^ X.n 0 by
    simpa [X.edgeSylow_zero] using X.relIndex_Q_edgeSylow 0,
    hinf, hcardS] at h
  have hpow : 2 ^ (2 * X.n 0 + 2 * X.n 1) =
      2 ^ X.n 0 * 2 ^ (X.n 0 + 2 * X.n 1) := by
    rw [show 2 * X.n 0 + 2 * X.n 1 = X.n 0 + (X.n 0 + 2 * X.n 1) by ring, pow_add]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (X.n 0)) (h.trans hpow)

private theorem u4qBase_cardQ1 {X : Setup Γ G}
    (hcardS : Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1)) :
    Nat.card (X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1) := by
  have hQ1S : X.Q 1 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow (i := 0)
  have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.S)
  have hinf : X.Q 1 ⊓ X.S = X.Q 1 := inf_of_le_left hQ1S
  rw [show (X.Q 1).relIndex X.S = 2 ^ X.n 1 by
    simpa [X.edgeSylow_zero] using X.relIndex_Q_succ_edgeSylow 0,
    hinf, hcardS] at h
  have hpow : 2 ^ (2 * X.n 0 + 2 * X.n 1) =
      2 ^ X.n 1 * 2 ^ (2 * X.n 0 + X.n 1) := by
    rw [show 2 * X.n 0 + 2 * X.n 1 = X.n 1 + (2 * X.n 0 + X.n 1) by ring, pow_add]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (X.n 1)) (h.trans hpow)

private theorem u4qBase_base {s r d : ℕ} {X : Setup Γ G}
    (C : X.Comm48 s r d) (h1 : d = 1)
    (h2 : X.HasB 0 (d + 1) ∧ 2 * (d + 1) = r ∧
      X.Z ((d : ℤ) + 1) = X.Qg r ∧
      X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 0) ∧
      X.Z 0 ⊓ X.Q ((d : ℤ) + 1) = ⊥ ∧ X.Z 0 ⊓ X.Q (-((d : ℤ) + 1)) = ⊥) :
    r = 4 ∧ s = 5 ∧ X.HasB 0 2 ∧ X.HasB 2 2 ∧
      Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1) ∧
      Nat.card (X.Q 0) = 2 ^ (X.n 0 + 2 * X.n 1) ∧
      Nat.card (X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1) ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ Nat.card (X.Z 2) = 2 ^ X.n 0 ∧
      IsElemAbelian 2 (X.Z 0) ∧ IsElemAbelian 2 (X.Z 2) ∧
      X.Z 0 ⊓ X.Q 2 = ⊥ ∧ X.Z 0 ⊓ X.Q (-2) = ⊥ ∧
      X.Z 2 ⊓ X.Q 0 = ⊥ ∧ X.Z 2 ⊓ X.Q 4 = ⊥ := by
  obtain ⟨hr, hs, hB0, hB2, hcardZ0, hcardZ2, helemZ0, helemZ2,
    hZ0Q2, hZ0Qm2, hZ2Q0, hZ2Q4⟩ := u4qBase_data C h1 h2
  have hcardS := u4qBase_cardS C hr hs
  have hcardQ0 := u4qBase_cardQ0 hcardS
  have hcardQ1 := u4qBase_cardQ1 hcardS
  exact ⟨hr, hs, hB0, hB2, hcardS, hcardQ0, hcardQ1, hcardZ0, hcardZ2,
    helemZ0, helemZ2, hZ0Q2, hZ0Qm2, hZ2Q0, hZ2Q4⟩

private theorem u4qBase_supS (C : X.Comm48 5 4 1) (hB2 : X.HasB 2 2)
    (hZ2Q0 : X.Z 2 ⊓ X.Q 0 = ⊥) (hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0) :
    X.Z 2 ⊔ X.Q 0 = X.S := by
  classical
  have hZ2p : IsPGroup 2 (X.Z 2) :=
    (pCoreOf_isPGroup' (X.Gi 2)).to_le (X.Z_le_Q 2)
  have hZ2G1 : X.Z 2 ≤ X.Gi 1 := by simpa using hB2.1 (-1) (by decide)
  have hZ2G0 : X.Z 2 ≤ X.Gi 0 := by simpa using hB2.1 (-2) (by decide)
  have hZ2S : X.Z 2 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.le_edgeSylow_of_le_inf 0 hZ2p (le_inf hZ2G0 hZ2G1)
  have hK : X.K ⊓ X.L 0 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 2 k (X.K_le_Gi 2 (Subgroup.mem_inf.mp hk).1)
  have hne : X.Z 2 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardZ2
    have h2 : 1 < 2 ^ X.n 0 :=
      Nat.one_lt_two_pow_iff.mpr (by have := C.hyp.two_le_n 0; omega)
    omega
  have hnot : ¬ X.Z 2 ≤ X.Q 0 := by
    intro hle
    have hinf : X.Z 2 ⊓ X.Q 0 = X.Z 2 := inf_of_le_left hle
    rw [hZ2Q0] at hinf
    exact hne hinf.symm
  simpa [X.edgeSylow_zero] using
    X.sup_Q_eq_edgeSylow_of_left_gen (i := 0) hK hZ2S hnot

private theorem u4qBase_A_fixes {X : Setup Γ G} {P : Subgroup G}
    (hPle : P ≤ X.Q 0 ⊓ X.Q 2) (hP_Qm1 : P ≤ X.Q (-1)) (hP_Q3 : P ≤ X.Q 3) :
    P ≤ X.arcStab (-2) ((-2) + (6 : ℕ)) := by
  have hP_Q0 : P ≤ X.Q 0 := hPle.trans inf_le_left
  have hP_Q2 : P ≤ X.Q 2 := hPle.trans inf_le_right
  have hfix_of {Q : Subgroup G} (hPQ : P ≤ Q) {j : ℤ} (hQG : Q ≤ X.Gi j) :
      ∀ p ∈ P, p • X.vert j = X.vert j := by
    intro p hp
    exact MulAction.mem_stabilizer_iff.mp (by simpa [Setup.Gi] using hQG (hPQ hp))
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  · exact hfix_of hP_Qm1 (((X.Q_le_Gi_adj (-1)).trans inf_le_left))
  · exact hfix_of hP_Q0 (((X.Q_le_Gi_adj 0).trans inf_le_left))
  · exact hfix_of hP_Qm1 (((X.Q_le_Gi_adj (-1)).trans inf_le_right))
  · exact hfix_of hP_Q0 (((X.Q_le_Gi_adj 0).trans inf_le_right))
  · exact hfix_of hP_Q3 (((X.Q_le_Gi_adj 3).trans inf_le_left))
  · exact hfix_of hP_Q2 (((X.Q_le_Gi_adj 2).trans inf_le_right))
  · exact hfix_of hP_Q3 (((X.Q_le_Gi_adj 3)).trans inf_le_right)

private theorem u4qBase_A_elem (C : X.Comm48 5 4 1) :
    IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := by
  classical
  set A : Subgroup G := X.Q 0 ⊓ X.Q 2 with hAdef
  have hAGi : A ≤ X.Gi 0 := inf_le_left.trans (X.Q_le_Gi 0)
  haveI : Finite ↥A :=
    finite_of_le_stabilizer X.hyp (α := X.vert 0) (H := A) hAGi
  have hAp : IsPGroup 2 A :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  haveI : Fact (IsPGroup 2 ↥A) := ⟨hAp⟩
  have hAGim1 : A ≤ X.Gi (-1) := inf_le_left.trans (((X.Q_le_Gi_adj 0).trans inf_le_left))
  have hAGi3 : A ≤ X.Gi 3 := inf_le_right.trans (((X.Q_le_Gi_adj 2).trans inf_le_right))
  have hALm1 : A ≤ X.L (-1) := le_oTwoPrime_of_isPGroup hAp hAGim1
  have hAL3 : A ≤ X.L 3 := le_oTwoPrime_of_isPGroup hAp hAGi3
  have hsqm1 := X.sq_comm_mem_Q_of_le_L (-1) hAp hALm1
  have hsq3 := X.sq_comm_mem_Q_of_le_L 3 hAp hAL3
  let P : Subgroup G := (frattini ↥A).map A.subtype
  have hPle : P ≤ A := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := hAp.to_le hPle
  have himg : Subgroup.map A.subtype (⁅(⊤ : Subgroup ↥A), ⊤⁆ : Subgroup ↥A) = ⁅A, A⁆ :=
    Subgroup.map_subtype_commutator A
  have hP_le {j : ℤ} (hsq : (∀ x ∈ A, x ^ 2 ∈ X.Q j) ∧ ⁅A, A⁆ ≤ X.Q j) : P ≤ X.Q j := by
    rw [show P = (frattini ↥A).map A.subtype from rfl]
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥A) (p := 2)]
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    rcases hy with hy | ⟨z, rfl⟩
    · exact hsq.2 (himg ▸ Subgroup.mem_map_of_mem A.subtype hy)
    · exact hsq.1 (z : G) z.2
  have hP_Qm1 : P ≤ X.Q (-1) := hP_le hsqm1
  have hP_Q3 : P ≤ X.Q 3 := hP_le hsq3
  have hfix : P ≤ X.arcStab (-2) ((-2) + (6 : ℕ)) :=
    u4qBase_A_fixes hPle hP_Qm1 hP_Q3
  have hfr_bot : frattini ↥A = ⊥ := by
    by_contra hfr_ne
    have hPne : P ≠ ⊥ := by
      intro hPbot
      apply hfr_ne
      apply Subgroup.map_injective A.subtype_injective
      have hPbot' : (frattini ↥A).map A.subtype = ⊥ := by simpa [P] using hPbot
      rw [hPbot', Subgroup.map_bot]
    have hle := X.le_r_of_fixes C.hyp hP2 hPne hfix
    omega
  haveI hElem : CFSG.IsElementaryAbelian 2 ↥A :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥A) (p := 2)).mp hfr_bot
  exact ⟨inferInstance, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩

private theorem u4qBase_step4 (C : X.Comm48 5 4 1) (hB0 : X.HasB 0 2)
    (hQ0Q1 : X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2))
    (hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1)
    (hnormZ0A : X.Z 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G)) :
    X.Q 1 ⊓ X.Q (-1) = X.Z 0 := by
  classical
  set A : Subgroup G := X.Q 0 ⊓ X.Q 2 with hAdef
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := X.Z_le_Q_of_lt hB0 (j := 1) (by norm_num)
  have hZ0Qm1 : X.Z 0 ≤ X.Q (-1) := X.Z_le_Q_of_lt hB0 (j := -1) (by norm_num)
  have hQm1Q1Q0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 := by
    simpa using (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0).1
  have hleQ0 : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 := by
    rw [inf_comm]
    exact hQm1Q1Q0
  have hleZA : X.Q 1 ⊓ X.Q (-1) ≤ X.Z 0 ⊔ A := by
    refine (le_inf (inf_le_left : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 1) hleQ0).trans ?_
    rw [hQ0Q1]
  have hEq : X.Q 1 ⊓ X.Q (-1) = (X.Z 0 ⊔ A) ⊓ X.Q (-1) := by
    refine le_antisymm (le_inf hleZA inf_le_right) ?_
    exact le_inf (inf_le_left.trans (sup_le hZ0Q1 hAQ1)) inf_le_right
  set B : Subgroup G := A ⊓ X.Q (-1) with hBdef
  have hBp : IsPGroup 2 B :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (inf_le_left.trans (hAdef ▸ inf_le_left))
  have hBQm1 : B ≤ X.Q (-1) := inf_le_right
  have hBQ0 : B ≤ X.Q 0 := (inf_le_left.trans (hAdef ▸ inf_le_left))
  have hBQ2 : B ≤ X.Q 2 := (inf_le_left.trans (hAdef ▸ inf_le_right))
  have hBQ1 : B ≤ X.Q 1 := (inf_le_left.trans (hAdef ▸ hAQ1))
  have hfix_of {Q : Subgroup G} (hBQ : B ≤ Q) {j : ℤ} (hQG : Q ≤ X.Gi j) :
      ∀ p ∈ B, p • X.vert j = X.vert j := by
    intro p hp
    exact MulAction.mem_stabilizer_iff.mp (by simpa [Setup.Gi] using hQG (hBQ hp))
  have hfix : B ≤ X.arcStab (-2) ((-2) + (5 : ℕ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    interval_cases j
    · exact hfix_of hBQm1 (((X.Q_le_Gi_adj (-1)).trans inf_le_left))
    · exact hfix_of hBQ0 (((X.Q_le_Gi_adj 0).trans inf_le_left))
    · exact hfix_of hBQm1 (((X.Q_le_Gi_adj (-1)).trans inf_le_right))
    · exact hfix_of hBQ0 (((X.Q_le_Gi_adj 0).trans inf_le_right))
    · exact hfix_of hBQ1 (((X.Q_le_Gi_adj 1).trans inf_le_right))
    · exact hfix_of hBQ2 (((X.Q_le_Gi_adj 2).trans inf_le_right))
  have hBbot : B = ⊥ := by
    by_contra hne
    have := X.le_r_of_fixes C.hyp hBp hne hfix
    omega
  have hmod : (X.Z 0 ⊔ A) ⊓ X.Q (-1) = X.Z 0 ⊔ A ⊓ X.Q (-1) := by
    rw [show (X.Z 0 ⊔ A) ⊓ X.Q (-1) = X.Q (-1) ⊓ (X.Z 0 ⊔ A) from inf_comm _ _,
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hZ0Qm1 hnormZ0A,
      show X.Q (-1) ⊓ A = A ⊓ X.Q (-1) from inf_comm _ _]
  rw [hEq, hmod, hBdef] at *
  rw [hBbot, sup_bot_eq]

private theorem u4qBase_commutator_Q1_le (hQ1elem : IsElemAbelian 2 (X.Q 1)) :
    ⁅X.Q 0 ⊓ X.Q 1, X.Q 1⁆ ≤ X.Z 0 := by
  have hQ1Q1bot : ⁅X.Q 1, X.Q 1⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (CFSG.Open.IsElemAbelian.comm hQ1elem (a := a) (b := b) ha hb).symm
  have h : ⁅X.Q 0 ⊓ X.Q 1, X.Q 1⁆ ≤ ⁅X.Q 1, X.Q 1⁆ :=
    Subgroup.commutator_mono inf_le_right le_rfl
  rw [hQ1Q1bot] at h
  exact h.trans bot_le

private theorem u4qBase_commutator_inf_S_le (C : X.Comm48 5 4 1)
    (hstep4 : X.Q 1 ⊓ X.Q (-1) = X.Z 0) (hQ1elem : IsElemAbelian 2 (X.Q 1))
    (hQ0dec : X.Q 0 = X.Q 0 ⊓ X.Q 1 ⊔ X.Q 0 ⊓ X.Q (-1)) :
    ⁅X.Q 0 ⊓ X.Q 1, X.S⁆ ≤ X.Z 0 := by
  classical
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hA1def
  set B : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hBdef
  have hQ0Gi1 : X.Q 0 ≤ X.Gi 1 := ((X.Q_le_Gi_adj 0).trans inf_le_right)
  have hQ1Gi0 : X.Q 1 ≤ X.Gi 0 := ((X.Q_le_Gi_adj 1).trans inf_le_left)
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    hQ0Gi1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hQ0NA1 : X.Q 0 ≤ Subgroup.normalizer (A1 : Set G) :=
    CFSG.Quasithin.F7.le_normalizer_inf Subgroup.le_normalizer hQ0NQ1
  have hQ0Gim1 : X.Q 0 ≤ X.Gi (-1) := ((X.Q_le_Gi_adj 0).trans inf_le_left)
  have hQ0NZ0 : X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g (X.Q_le_Gi 0 hg))
  have hQ1NZ0 : X.Q 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g (hQ1Gi0 hg))
  have hA1NZ0 : A1 ≤ Subgroup.normalizer (X.Z 0 : Set G) := inf_le_left.trans hQ0NZ0
  have hBNZ0 : B ≤ Subgroup.normalizer (X.Z 0 : Set G) := inf_le_left.trans hQ0NZ0
  have hQ0NQm1 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    hQ0Gim1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
  have hA1NB : A1 ≤ Subgroup.normalizer (B : Set G) :=
    CFSG.Quasithin.F7.le_normalizer_inf
      (inf_le_left.trans Subgroup.le_normalizer) (inf_le_left.trans hQ0NQm1)
  have hBNA1 : B ≤ Subgroup.normalizer (A1 : Set G) := inf_le_left.trans hQ0NA1
  have hA1B_eq_Z0 : A1 ⊓ B = X.Z 0 := by
    calc A1 ⊓ B = (X.Q 1 ⊓ X.Q (-1)) ⊓ X.Q 0 := by
          rw [hA1def, hBdef]
          ac_rfl
      _ = X.Z 0 := by rw [hstep4, inf_of_le_left (X.Z_le_Q 0)]
  have hA1A1bot : ⁅A1, A1⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hQ1elem.comm ha.2 hb.2).symm
  have hA1A1_le_Z0 : ⁅A1, A1⁆ ≤ X.Z 0 := by rw [hA1A1bot]; exact bot_le
  have hA1B_le_Z0 : ⁅A1, B⁆ ≤ X.Z 0 := by
    rw [← hA1B_eq_Z0]
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hBNA1
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp hA1NB
  have hA1Q1_le_Z0 : ⁅A1, X.Q 1⁆ ≤ X.Z 0 := u4qBase_commutator_Q1_le hQ1elem
  have hA1Q0_le_Z0 : ⁅A1, X.Q 0⁆ ≤ X.Z 0 := by
    rw [hQ0dec]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := A1) (N := X.Z 0)
      hA1NZ0 hBNZ0 hA1A1_le_Z0 hA1B_le_Z0
  have hA1S_le_Z0 : ⁅A1, X.S⁆ ≤ X.Z 0 := by
    have hS : X.S = X.Q 0 ⊔ X.Q 1 := by
      rw [← X.edgeSylow_zero]
      exact (X.sup_Q_eq_edgeSylow C.hyp.char 0).symm
    rw [hS]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := A1) (N := X.Z 0)
      hQ0NZ0 hQ1NZ0 hA1Q0_le_Z0 hA1Q1_le_Z0
  exact hA1S_le_Z0

private theorem u4qBase_hquad (C : X.Comm48 5 4 1)
    (hstep4 : X.Q 1 ⊓ X.Q (-1) = X.Z 0)
    (hQ1elem : IsElemAbelian 2 (X.Q 1)) :
    ⁅⁅X.Q 0, X.S⁆, X.S⁆ ≤ X.Z 0 := by
  classical
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hA1def
  obtain ⟨-, -, hcommQ0, -, -, hQ0dec⟩ :=
    X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 0
  have hcommQ0' : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0 := by
    refine hcommQ0.trans ?_
    rw [inf_comm]
    exact le_of_eq hstep4
  have hZ0Q0 : X.Z 0 ≤ X.Q 0 := X.Z_le_Q 0
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := by
    rw [← hstep4]
    exact inf_le_left
  have hZ0A1 : X.Z 0 ≤ A1 := le_inf hZ0Q0 hZ0Q1
  have hQ0Gi1 : X.Q 0 ≤ X.Gi 1 := ((X.Q_le_Gi_adj 0).trans inf_le_right)
  have hQ1Gi0 : X.Q 1 ≤ X.Gi 0 := ((X.Q_le_Gi_adj 1).trans inf_le_left)
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    hQ0Gi1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hQ1NQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hQ1Gi0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hQ0NA1 : X.Q 0 ≤ Subgroup.normalizer (A1 : Set G) :=
    CFSG.Quasithin.F7.le_normalizer_inf Subgroup.le_normalizer hQ0NQ1
  have hQ1NA1 : X.Q 1 ≤ Subgroup.normalizer (A1 : Set G) :=
    CFSG.Quasithin.F7.le_normalizer_inf hQ1NQ0 Subgroup.le_normalizer
  have hQ0Q1_le_A1 : ⁅X.Q 0, X.Q 1⁆ ≤ A1 := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1NQ0
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQ0NQ1
  have hQ0Q0_le_A1 : ⁅X.Q 0, X.Q 0⁆ ≤ A1 := hcommQ0'.trans hZ0A1
  have hQ0S_le_A1 : ⁅X.Q 0, X.S⁆ ≤ A1 := by
    have hS : X.S = X.Q 0 ⊔ X.Q 1 := by
      rw [← X.edgeSylow_zero]
      exact (X.sup_Q_eq_edgeSylow C.hyp.char 0).symm
    rw [hS]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := X.Q 0) (N := A1)
      hQ0NA1 hQ1NA1 hQ0Q0_le_A1 hQ0Q1_le_A1
  exact (Subgroup.commutator_mono hQ0S_le_A1 le_rfl).trans
    (X.u4qBase_commutator_inf_S_le C hstep4 hQ1elem hQ0dec)

private theorem u4qBase_Q1_Z2_le_Z1 (C : X.Comm48 5 4 1)
    (hQ1prod : X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ (X.Q 0 ⊓ X.Q 2)) (hZ0Z1 : X.Z 0 ≤ X.Z 1) :
    X.Z 2 ≤ X.Z 1 ∧ X.Z 0 ≤ X.Q 1 ∧ X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := by
    rw [hQ1prod]
    exact (le_sup_left : X.Z 0 ≤ X.Z 0 ⊔ X.Z 2).trans le_sup_left
  have hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
    rw [hQ1prod]
    exact le_sup_right
  obtain ⟨t, -, href, -⟩ := X.exists_reflection_oTwoRes C.hyp 1
  have ht0 : t • X.vert 0 = X.vert 2 := by simpa using href (-1)
  have ht1 : t • X.vert 1 = X.vert 1 := by simpa using href 0
  have hZ2t : X.Z 2 = conjSub t (X.Z 0) := by
    rw [X.Z_eq_vertZ, X.Z_eq_vertZ, ← ht0, vertZ_smul]
  have hZ1t : conjSub t (X.Z 1) = X.Z 1 := by
    rw [X.Z_eq_vertZ]
    have h := vertZ_smul t (X.vert 1)
    rw [ht1] at h
    exact h.symm
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := by
    have h := conjSub_mono t hZ0Z1
    rw [← hZ2t, hZ1t] at h
    exact h
  exact ⟨hZ2Z1, hZ0Q1, hAQ1⟩

private theorem u4qBase_Q1_sup_commute (hZ0Q1 : X.Z 0 ≤ X.Q 1)
    (hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1) (hZ0Z1 : X.Z 0 ≤ X.Z 1) (hZ2Z1 : X.Z 2 ≤ X.Z 1)
    (hZ0elem : IsElemAbelian 2 (X.Z 0)) (hZ2elem : IsElemAbelian 2 (X.Z 2))
    (hAelem : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2)) :
    IsElemAbelian 2 (X.Z 0 ⊔ X.Z 2) ∧
      ∀ a ∈ X.Q 0 ⊓ X.Q 2, ∀ b ∈ X.Z 0 ⊔ X.Z 2, a * b = b * a := by
  have hZ0center : X.Z 0 ≤ centerOf (X.Q 1) := hZ0Z1.trans (X.Z_le_center 1)
  have hZ2center : X.Z 2 ≤ centerOf (X.Q 1) := hZ2Z1.trans (X.Z_le_center 1)
  have hZ0Z2comm : ∀ a ∈ X.Z 0, ∀ b ∈ X.Z 2, a * b = b * a := by
    intro a ha b hb
    have hbC : b ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (hZ2center hb)).2
    exact Subgroup.mem_centralizer_iff.mp hbC a (hZ0Q1 ha)
  have hZ0Z2elem : IsElemAbelian 2 (X.Z 0 ⊔ X.Z 2) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hZ0elem hZ2elem hZ0Z2comm
  have hAZ0 : ∀ a ∈ X.Q 0 ⊓ X.Q 2, ∀ z ∈ X.Z 0, a * z = z * a := by
    intro a ha z hz
    have hzC : z ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (hZ0center hz)).2
    exact Subgroup.mem_centralizer_iff.mp hzC a (hAQ1 ha)
  have hAZ2 : ∀ a ∈ X.Q 0 ⊓ X.Q 2, ∀ z ∈ X.Z 2, a * z = z * a := by
    intro a ha z hz
    have hzC : z ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (hZ2center hz)).2
    exact Subgroup.mem_centralizer_iff.mp hzC a (hAQ1 ha)
  have hnormZ0Z2 : X.Z 0 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    intro a ha
    exact Subgroup.centralizer_le_normalizer (X.Z 2 : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hZ0Z2comm a ha y hy).symm)
  have hAZ0Z2 : ∀ a ∈ X.Q 0 ⊓ X.Q 2, ∀ b ∈ X.Z 0 ⊔ X.Z 2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨z0, hz0, z2, hz2, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hnormZ0Z2).mp hb
    have ha0 := hAZ0 a ha z0 hz0
    have ha2 := hAZ2 a ha z2 hz2
    calc a * (z0 * z2) = a * z0 * z2 := by group
      _ = z0 * a * z2 := by rw [ha0]
      _ = z0 * (a * z2) := by group
      _ = z0 * (z2 * a) := by rw [ha2]
      _ = (z0 * z2) * a := by group
  exact ⟨hZ0Z2elem, hAZ0Z2⟩

private theorem u4qBase_Q1_elem (C : X.Comm48 5 4 1)
    (hQ1prod : X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ (X.Q 0 ⊓ X.Q 2))
    (hZ0elem : IsElemAbelian 2 (X.Z 0)) (hZ2elem : IsElemAbelian 2 (X.Z 2))
    (hAelem : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2)) (hZ0Z1 : X.Z 0 ≤ X.Z 1) :
    IsElemAbelian 2 (X.Q 1) := by
  obtain ⟨hZ2Z1, hZ0Q1, hAQ1⟩ := u4qBase_Q1_Z2_le_Z1 C hQ1prod hZ0Z1
  obtain ⟨hZ0Z2elem, hAZ0Z2⟩ :=
    u4qBase_Q1_sup_commute hZ0Q1 hAQ1 hZ0Z1 hZ2Z1 hZ0elem hZ2elem hAelem
  have h := CFSG.Open.IsElemAbelian.sup_of_commute hAelem hZ0Z2elem hAZ0Z2
  have hEq : X.Z 0 ⊔ X.Z 2 ⊔ (X.Q 0 ⊓ X.Q 2) =
      (X.Q 0 ⊓ X.Q 2) ⊔ (X.Z 0 ⊔ X.Z 2) := by ac_rfl
  rw [hQ1prod, hEq]
  exact h

private theorem u4qBase_Z0_inf_Z2 (C : X.Comm48 5 4 1)
    (hB0 : X.HasB 0 2) (hB2 : X.HasB 2 2) : X.Z 0 ⊓ X.Z 2 = ⊥ := by
  by_contra hne
  have hR2 : IsPGroup 2 ↥(X.Z 0 ⊓ X.Z 2 : Subgroup G) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (inf_le_left.trans (X.Z_le_Q 0))
  have hfix : X.Z 0 ⊓ X.Z 2 ≤ X.arcStab (-2) ((-2) + (6 : ℕ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro q hq
    by_cases hj2 : j ≤ 2
    · have hmem : j ∈ Set.Icc (-2 : ℤ) 2 := by rw [Set.mem_Icc]; omega
      have hmem' : j ∈ X.fixSet (X.Z 0) := by
        rw [X.fixSet_Z 0 hB0]
        exact hmem
      exact hmem' q hq.1
    · have hmem : j ∈ Set.Icc (0 : ℤ) 4 := by rw [Set.mem_Icc]; omega
      have hmem' : j ∈ X.fixSet (X.Z 2) := by
        rw [X.fixSet_Z 2 hB2]
        exact hmem
      exact hmem' q hq.2
  have := X.le_r_of_fixes C.hyp hR2 hne hfix
  omega

private theorem u4qBase_card_Q1_Q0
    (hZ2Q1 : X.Z 2 ≤ X.Q 1) (hZ2Q0 : X.Z 2 ⊓ X.Q 0 = ⊥)
    (hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0)
    (hcardQ1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1))
    (hQ1eq1 : X.Q 1 = X.Z 2 ⊔ (X.Q 1 ⊓ X.Q 0)) :
    Nat.card ↥(X.Q 1 ⊓ X.Q 0 : Subgroup G) = 2 ^ (X.n 0 + X.n 1) := by
  set B : Subgroup G := X.Q 1 ⊓ X.Q 0 with hBdef
  have hnormZ2B : B ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    have hQ1G2 : X.Q 1 ≤ X.Gi 2 := ((X.Q_le_Gi_adj 1).trans inf_le_right)
    exact (inf_le_left.trans hQ1G2).trans (by
      intro z hz
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact X.Z_normal 2 z hz)
  have hdisjZ2B : Disjoint (X.Z 2) B := by
    rw [disjoint_iff]
    refine le_bot_iff.mp ?_
    calc X.Z 2 ⊓ B ≤ X.Z 2 ⊓ X.Q 0 := inf_le_inf_left _ (hBdef ▸ inf_le_right)
      _ = ⊥ := hZ2Q0
  have hcardQ1Q0B : Nat.card B = 2 ^ (X.n 0 + X.n 1) := by
    have h : Nat.card ↥(X.Z 2 ⊔ B : Subgroup G) = Nat.card ↥(X.Z 2) * Nat.card ↥B :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (A := X.Z 2) (B := B) hnormZ2B hdisjZ2B
    have hEq : Nat.card ↥(X.Q 1) = Nat.card ↥(X.Z 2) * Nat.card ↥B :=
      (congrArg (fun H : Subgroup G => Nat.card H) hQ1eq1).trans h
    rw [hcardQ1, hcardZ2] at hEq
    have hpow : 2 ^ (2 * X.n 0 + X.n 1) = 2 ^ X.n 0 * 2 ^ (X.n 0 + X.n 1) := by
      rw [show 2 * X.n 0 + X.n 1 = X.n 0 + (X.n 0 + X.n 1) by ring, pow_add]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (X.n 0)) (hEq.symm.trans hpow)
  exact hcardQ1Q0B

private theorem u4qBase_Q1_inf_Q0 (hZ0G1 : X.Z 0 ≤ X.Gi 1) (hZ0G2 : X.Z 0 ≤ X.Gi 2)
    (hZ0Q0 : X.Z 0 ≤ X.Q 0) (hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1)
    (hQ1eq2 : X.Q 1 = X.Z 0 ⊔ (X.Q 1 ⊓ X.Q 2)) :
    X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2) := by
  set A : Subgroup G := X.Q 0 ⊓ X.Q 2 with hAdef
  have hZ0NQ1 : X.Z 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    hZ0G1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hZ0NQ2 : X.Z 0 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    hZ0G2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hZ0NB : X.Z 0 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    CFSG.Quasithin.F7.le_normalizer_inf hZ0NQ1 hZ0NQ2
  have hmod :
      (X.Z 0 ⊔ X.Q 1 ⊓ X.Q 2) ⊓ X.Q 0 = X.Z 0 ⊔ X.Q 1 ⊓ X.Q 2 ⊓ X.Q 0 := by
    rw [show (X.Z 0 ⊔ X.Q 1 ⊓ X.Q 2) ⊓ X.Q 0 =
          X.Q 0 ⊓ (X.Z 0 ⊔ X.Q 1 ⊓ X.Q 2) from inf_comm _ _,
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hZ0Q0 hZ0NB,
      show X.Q 0 ⊓ (X.Q 1 ⊓ X.Q 2) = (X.Q 1 ⊓ X.Q 2) ⊓ X.Q 0 from inf_comm _ _]
  have hL : X.Q 1 ⊓ X.Q 0 = (X.Z 0 ⊔ (X.Q 1 ⊓ X.Q 2)) ⊓ X.Q 0 :=
    congrArg (fun H : Subgroup G => H ⊓ X.Q 0) hQ1eq2
  have hAint : X.Q 1 ⊓ X.Q 2 ⊓ X.Q 0 = A := by
    rw [show X.Q 1 ⊓ X.Q 2 ⊓ X.Q 0 = (X.Q 0 ⊓ X.Q 2) ⊓ X.Q 1 by ac_rfl]
    exact inf_of_le_left hAQ1
  refine (hL.trans hmod).trans ?_
  rw [hAint]

private theorem u4qBase_card_A
    (hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0)
    (hZ0A : X.Z 0 ⊓ (X.Q 0 ⊓ X.Q 2) = ⊥)
    (hnormAZ0 : X.Q 0 ⊓ X.Q 2 ≤ Subgroup.normalizer (X.Z 0 : Set G))
    (hQ0Q1 : X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2))
    (hcardQ1Q0B : Nat.card ↥(X.Q 1 ⊓ X.Q 0 : Subgroup G) = 2 ^ (X.n 0 + X.n 1)) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 2 : Subgroup G) = 2 ^ X.n 1 := by
  set A : Subgroup G := X.Q 0 ⊓ X.Q 2 with hAdef
  set B : Subgroup G := X.Q 1 ⊓ X.Q 0 with hBdef
  have hdisjZ0A : Disjoint (X.Z 0) A := by
    rw [disjoint_iff]
    exact hZ0A
  have hcardA : Nat.card A = 2 ^ X.n 1 := by
    have h : Nat.card ↥(X.Z 0 ⊔ A : Subgroup G) = Nat.card ↥(X.Z 0) * Nat.card ↥A :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (A := X.Z 0) (B := A) hnormAZ0 hdisjZ0A
    have hEq : Nat.card ↥B = Nat.card ↥(X.Z 0) * Nat.card ↥A :=
      (congrArg (fun H : Subgroup G => Nat.card H) hQ0Q1).trans h
    rw [hcardQ1Q0B, hcardZ0] at hEq
    have hpow : 2 ^ (X.n 0 + X.n 1) = 2 ^ X.n 0 * 2 ^ X.n 1 := by rw [pow_add]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (X.n 0)) (hEq.symm.trans hpow)
  exact hcardA

private theorem u4qBase_card_sup_Z0_Z2 (hZ0G2 : X.Z 0 ≤ X.Gi 2) (hZ2G0 : X.Z 2 ≤ X.Gi 0)
    (hZ0Q0 : X.Z 0 ≤ X.Q 0) (hZ2Q0 : X.Z 2 ⊓ X.Q 0 = ⊥)
    (hZ0Z2bot : X.Z 0 ⊓ X.Z 2 = ⊥)
    (hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0)
    (hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0) :
    Nat.card (X.Z 0 ⊔ X.Z 2 : Subgroup G) = 2 ^ (2 * X.n 0) ∧
      (X.Z 0 ⊔ X.Z 2) ⊓ X.Q 0 = X.Z 0 := by
  have hZ0Z2norm : X.Z 0 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 2 z (hZ0G2 hz)
  have hZ2NZ0 : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 z (hZ2G0 hz)
  have hcardZ0Z2 : Nat.card (X.Z 0 ⊔ X.Z 2 : Subgroup G) = 2 ^ (2 * X.n 0) := by
    have h : Nat.card ↥(X.Z 0 ⊔ X.Z 2 : Subgroup G) = Nat.card ↥(X.Z 0) * Nat.card ↥(X.Z 2) :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (A := X.Z 0) (B := X.Z 2) hZ2NZ0 (disjoint_iff.mpr hZ0Z2bot)
    rw [h, hcardZ0, hcardZ2]
    rw [← pow_add]
    congr 1
    omega
  have hmodP : (X.Z 0 ⊔ X.Z 2) ⊓ X.Q 0 = X.Z 0 := by
    have hmod : (X.Z 0 ⊔ X.Z 2) ⊓ X.Q 0 = X.Z 0 ⊔ X.Z 2 ⊓ X.Q 0 := by
      rw [show (X.Z 0 ⊔ X.Z 2) ⊓ X.Q 0 = X.Q 0 ⊓ (X.Z 0 ⊔ X.Z 2) from inf_comm _ _,
        CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hZ0Q0 hZ0Z2norm,
        show X.Q 0 ⊓ X.Z 2 = X.Z 2 ⊓ X.Q 0 from inf_comm _ _]
    rwa [hZ2Q0, sup_bot_eq] at hmod
  exact ⟨hcardZ0Z2, hmodP⟩

private theorem u4qBase_Q1_eq_sup (hZ0G2 : X.Z 0 ≤ X.Gi 2) (hZ2G0 : X.Z 2 ≤ X.Gi 0)
    (hZ0Q0 : X.Z 0 ≤ X.Q 0) (hZ0Q1 : X.Z 0 ≤ X.Q 1) (hZ2Q1 : X.Z 2 ≤ X.Q 1)
    (hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1) (hZ2Q0 : X.Z 2 ⊓ X.Q 0 = ⊥)
    (hZ0A : X.Z 0 ⊓ (X.Q 0 ⊓ X.Q 2) = ⊥)
    (hnormAZ0 : X.Q 0 ⊓ X.Q 2 ≤ Subgroup.normalizer (X.Z 0 : Set G))
    (hZ0Z2bot : X.Z 0 ⊓ X.Z 2 = ⊥)
    (hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0)
    (hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0)
    (hcardA : Nat.card ↥(X.Q 0 ⊓ X.Q 2 : Subgroup G) = 2 ^ X.n 1)
    (hcardQ1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1)) :
    X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ (X.Q 0 ⊓ X.Q 2) := by
  set A : Subgroup G := X.Q 0 ⊓ X.Q 2 with hAdef
  haveI : Finite ↥(X.Q 1) := finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  obtain ⟨hcardZ0Z2, hmodP⟩ :=
    u4qBase_card_sup_Z0_Z2 hZ0G2 hZ2G0 hZ0Q0 hZ2Q0 hZ0Z2bot hcardZ0 hcardZ2
  have hPA : (X.Z 0 ⊔ X.Z 2) ⊓ A = ⊥ := by
    refine le_bot_iff.mp ?_
    have hPZ0 : (X.Z 0 ⊔ X.Z 2) ⊓ A ≤ X.Z 0 :=
      (inf_le_inf_left _ inf_le_left).trans (le_of_eq hmodP)
    exact (le_inf hPZ0 inf_le_right).trans (le_of_eq hZ0A)
  have hnormPA : A ≤ Subgroup.normalizer ((X.Z 0 ⊔ X.Z 2 : Subgroup G) : Set G) := by
    have hAZ0 : A ≤ Subgroup.normalizer (X.Z 0 : Set G) := hnormAZ0
    have hAZ2 : A ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
      have hAG2 : A ≤ X.Gi 2 := inf_le_right.trans (X.Q_le_Gi 2)
      exact hAG2.trans (by
        intro z hz
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        exact X.Z_normal 2 z hz)
    exact CFSG.Quasithin.F1.le_normalizer_sup hAZ0 hAZ2
  have hdisjPA : Disjoint (X.Z 0 ⊔ X.Z 2) A := by
    rw [disjoint_iff]
    exact hPA
  have hcardAll : Nat.card (X.Z 0 ⊔ X.Z 2 ⊔ A : Subgroup G) = 2 ^ (2 * X.n 0 + X.n 1) := by
    have h : Nat.card ↥(X.Z 0 ⊔ X.Z 2 ⊔ A : Subgroup G) =
        Nat.card ↥(X.Z 0 ⊔ X.Z 2 : Subgroup G) * Nat.card ↥A :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (A := X.Z 0 ⊔ X.Z 2) (B := A) hnormPA hdisjPA
    rw [h, hcardZ0Z2, hcardA]
    rw [← pow_add]
  have hsupAll : X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ A := by
    have hle : X.Z 0 ⊔ X.Z 2 ⊔ A ≤ X.Q 1 := sup_le (sup_le hZ0Q1 hZ2Q1) hAQ1
    have hcardge : Nat.card (X.Q 1) ≤ Nat.card (X.Z 0 ⊔ X.Z 2 ⊔ A : Subgroup G) := by
      rw [hcardAll, hcardQ1]
    exact (Subgroup.eq_of_le_of_card_ge hle hcardge).symm
  exact hsupAll

private theorem u4qBase_Q1_eq_sup_Z2 (hZ2G0 : X.Z 2 ≤ X.Gi 0) (hZ2Q1 : X.Z 2 ≤ X.Q 1)
    (hQ1S : X.Q 1 ≤ X.S) (hSsup : X.Z 2 ⊔ X.Q 0 = X.S) :
    X.Q 1 = X.Z 2 ⊔ (X.Q 1 ⊓ X.Q 0) := by
  have hZ2NQ0 : X.Z 2 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hZ2G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hmod : (X.Z 2 ⊔ X.Q 0) ⊓ X.Q 1 = X.Z 2 ⊔ X.Q 0 ⊓ X.Q 1 := by
    rw [show (X.Z 2 ⊔ X.Q 0) ⊓ X.Q 1 = X.Q 1 ⊓ (X.Z 2 ⊔ X.Q 0) from inf_comm _ _,
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hZ2Q1 hZ2NQ0,
      show X.Q 1 ⊓ X.Q 0 = X.Q 0 ⊓ X.Q 1 from inf_comm _ _]
  rw [hSsup, inf_of_le_right hQ1S] at hmod
  exact hmod.trans (by rw [inf_comm])

private theorem u4qBase_Q1_eq_sup_Z0 (C : X.Comm48 5 4 1) (hB0 : X.HasB 0 2)
    (hZ0Q2 : X.Z 0 ⊓ X.Q 2 = ⊥) (hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0) :
    X.Q 1 = X.Z 0 ⊔ (X.Q 1 ⊓ X.Q 2) := by
  have hZ0G1 : X.Z 0 ≤ X.Gi 1 := by simpa using hB0.1 1 (by decide)
  have hZ0G2 : X.Z 0 ≤ X.Gi 2 := by simpa using hB0.1 2 (by decide)
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := X.Z_le_Q_of_lt hB0 (j := 1) (by norm_num)
  have hKZ0 : X.K ⊓ X.L (1 + 1) ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 k (X.K_le_Gi 0 (Subgroup.mem_inf.mp hk).1)
  have hZ0S1 : X.Z 0 ≤ X.edgeSylow 1 := X.le_edgeSylow_of_le_inf 1
    ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)) (le_inf hZ0G1 hZ0G2)
  have hneZ0 : X.Z 0 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardZ0
    have h2 : 1 < 2 ^ X.n 0 :=
      Nat.one_lt_two_pow_iff.mpr (by have := C.hyp.two_le_n 0; omega)
    omega
  have hnotZ0Q2 : ¬ X.Z 0 ≤ X.Q 2 := by
    intro hle
    have hinf : X.Z 0 ⊓ X.Q 2 = X.Z 0 := inf_of_le_left hle
    rw [hZ0Q2] at hinf
    exact hneZ0 hinf.symm
  have hS1sup : X.Z 0 ⊔ X.Q 2 = X.edgeSylow 1 :=
    X.sup_Q_eq_edgeSylow_of_gen (i := 1) hKZ0 hZ0S1 hnotZ0Q2
  have hQ1S1 : X.Q 1 ≤ X.edgeSylow 1 := X.Q_le_edgeSylow_left 1
  have hZ0NQ2 : X.Z 0 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    hZ0G2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hmod : (X.Z 0 ⊔ X.Q 2) ⊓ X.Q 1 = X.Z 0 ⊔ X.Q 2 ⊓ X.Q 1 := by
    rw [show (X.Z 0 ⊔ X.Q 2) ⊓ X.Q 1 = X.Q 1 ⊓ (X.Z 0 ⊔ X.Q 2) from inf_comm _ _,
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hZ0Q1 hZ0NQ2,
      show X.Q 1 ⊓ X.Q 2 = X.Q 2 ⊓ X.Q 1 from inf_comm _ _]
  rw [hS1sup, inf_of_le_right hQ1S1] at hmod
  exact hmod.trans (by rw [inf_comm])

private theorem u4qBase_Q1_decomp (C : X.Comm48 5 4 1)
    (hB0 : X.HasB 0 2) (hB2 : X.HasB 2 2)
    (hZ0Q2 : X.Z 0 ⊓ X.Q 2 = ⊥) (hSsup : X.Z 2 ⊔ X.Q 0 = X.S)
    (hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0) :
    (X.Q 1 = X.Z 2 ⊔ (X.Q 1 ⊓ X.Q 0)) ∧
      (X.Q 1 = X.Z 0 ⊔ (X.Q 1 ⊓ X.Q 2)) ∧
        (X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2)) ∧
          X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
  classical
  have hZ0G1 : X.Z 0 ≤ X.Gi 1 := by simpa using hB0.1 1 (by decide)
  have hZ0G2 : X.Z 0 ≤ X.Gi 2 := by simpa using hB0.1 2 (by decide)
  have hZ2G0 : X.Z 2 ≤ X.Gi 0 := by simpa using hB2.1 (-2) (by decide)
  have hZ0Q0 : X.Z 0 ≤ X.Q 0 := X.Z_le_Q 0
  have hZ2Q1 : X.Z 2 ≤ X.Q 1 := X.Z_le_Q_of_lt hB2 (j := 1) (by norm_num)
  have hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 :=
    (X.Q_quot C.hyp.char C.hyp.sing (Nat.le_of_succ_le C.hyp.five_le) 1).1
  have hQ1S : X.Q 1 ≤ X.S := by
    simpa [X.edgeSylow_zero] using X.Q_le_edgeSylow (i := 0)
  have hQ1eq1 : X.Q 1 = X.Z 2 ⊔ (X.Q 1 ⊓ X.Q 0) :=
    u4qBase_Q1_eq_sup_Z2 hZ2G0 hZ2Q1 hQ1S hSsup
  have hQ1eq2 : X.Q 1 = X.Z 0 ⊔ (X.Q 1 ⊓ X.Q 2) :=
    u4qBase_Q1_eq_sup_Z0 C hB0 hZ0Q2 hcardZ0
  have hQ0Q1 : X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2) :=
    u4qBase_Q1_inf_Q0 hZ0G1 hZ0G2 hZ0Q0 hAQ1 hQ1eq2
  exact ⟨hQ1eq1, hQ1eq2, hQ0Q1, hAQ1⟩

private theorem u4qBase_step1 (C : X.Comm48 5 4 1)
    (hB0 : X.HasB 0 2) (hB2 : X.HasB 2 2)
    (hZ0Q2 : X.Z 0 ⊓ X.Q 2 = ⊥) (hZ2Q0 : X.Z 2 ⊓ X.Q 0 = ⊥)
    (hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0)
    (hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0)
    (hcardQ1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1))
    (hSsup : X.Z 2 ⊔ X.Q 0 = X.S) :
    X.Z 0 ⊓ X.Z 2 = ⊥ ∧
      X.Q 1 = X.Z 2 ⊔ (X.Q 1 ⊓ X.Q 0) ∧
        X.Q 1 = X.Z 0 ⊔ (X.Q 1 ⊓ X.Q 2) ∧
          X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2) ∧
            Nat.card ↥(X.Q 0 ⊓ X.Q 2 : Subgroup G) = 2 ^ X.n 1 ∧
              Nat.card ↥(X.Q 1 ⊓ X.Q 0 : Subgroup G) = 2 ^ (X.n 0 + X.n 1) ∧
                X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ (X.Q 0 ⊓ X.Q 2) := by
  classical
  set A : Subgroup G := X.Q 0 ⊓ X.Q 2 with hAdef
  obtain ⟨hQ1eq1, hQ1eq2, hQ0Q1, hAQ1⟩ :=
    u4qBase_Q1_decomp C hB0 hB2 hZ0Q2 hSsup hcardZ0
  have hZ0G1 : X.Z 0 ≤ X.Gi 1 := by simpa using hB0.1 1 (by decide)
  have hZ0G2 : X.Z 0 ≤ X.Gi 2 := by simpa using hB0.1 2 (by decide)
  have hZ2G0 : X.Z 2 ≤ X.Gi 0 := by simpa using hB2.1 (-2) (by decide)
  have hZ0Q0 : X.Z 0 ≤ X.Q 0 := X.Z_le_Q 0
  have hZ2Q1 : X.Z 2 ≤ X.Q 1 := X.Z_le_Q_of_lt hB2 (j := 1) (by norm_num)
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := X.Z_le_Q_of_lt hB0 (j := 1) (by norm_num)
  have hZ0A : X.Z 0 ⊓ A = ⊥ := by
    rw [hAdef]
    exact le_bot_iff.mp (by
      calc X.Z 0 ⊓ (X.Q 0 ⊓ X.Q 2) ≤ X.Z 0 ⊓ X.Q 2 := inf_le_inf_left _ inf_le_right
        _ = ⊥ := hZ0Q2)
  have hnormAZ0 : A ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    rw [hAdef]
    exact fun z hz => mem_normalizer_iff_conjSub.mpr
      (X.Z_normal 0 z (X.Q_le_Gi 0 (Subgroup.mem_inf.mp hz).1))
  have hZ0Z2bot : X.Z 0 ⊓ X.Z 2 = ⊥ := u4qBase_Z0_inf_Z2 C hB0 hB2
  have hcardQ1Q0B : Nat.card ↥(X.Q 1 ⊓ X.Q 0 : Subgroup G) = 2 ^ (X.n 0 + X.n 1) :=
    u4qBase_card_Q1_Q0 hZ2Q1 hZ2Q0 hcardZ2 hcardQ1 hQ1eq1
  have hcardA : Nat.card A = 2 ^ X.n 1 :=
    u4qBase_card_A hcardZ0 hZ0A hnormAZ0 hQ0Q1 hcardQ1Q0B
  have hsupAll : X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ A :=
    u4qBase_Q1_eq_sup hZ0G2 hZ2G0 hZ0Q0 hZ0Q1 hZ2Q1 hAQ1 hZ2Q0 hZ0A hnormAZ0
      hZ0Z2bot hcardZ0 hcardZ2 hcardA hcardQ1
  exact ⟨hZ0Z2bot, hQ1eq1, hQ1eq2, hQ0Q1, hcardA, hcardQ1Q0B, hsupAll⟩

private theorem u4qBase_Z0_normalizer_A (hB0 : X.HasB 0 2) :
    X.Z 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (X.Q 0 ⊓ X.Q 2).map (MulAut.conj z).toMonoidHom = X.Q 0 ⊓ X.Q 2
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj z).injective,
    show (X.Q 0).map (MulAut.conj z).toMonoidHom = X.Q 0 by
      simpa [conjSub] using conjSub_eq_of_mem (X.Z_le_Q 0 hz),
    show (X.Q 2).map (MulAut.conj z).toMonoidHom = X.Q 2 by
      have hzN : z ∈ Subgroup.normalizer (X.Q 2 : Set G) :=
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
          (hB0.1 2 (by decide) hz)
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hzN]

private theorem u4qBase_struct {s r d : ℕ} {X : Setup Γ G}
    (C : X.Comm48 s r d) (h1 : d = 1)
    (h2 : X.HasB 0 (d + 1) ∧ 2 * (d + 1) = r ∧
      X.Z ((d : ℤ) + 1) = X.Qg r ∧
      X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 0) ∧
      X.Z 0 ⊓ X.Q ((d : ℤ) + 1) = ⊥ ∧ X.Z 0 ⊓ X.Q (-((d : ℤ) + 1)) = ⊥)
    (hZ0L : X.Z 0 = centerOf (X.L 0)) (hZ0Z1 : X.Z 0 ≤ X.Z 1) :
    X.U4qBase := by
  classical
  subst h1
  obtain ⟨hr, hs, hB0, hB2, hcardS, hcardQ0, hcardQ1, hcardZ0, hcardZ2,
    helemZ0, helemZ2, hZ0Q2, hZ0Qm2, hZ2Q0, hZ2Q4⟩ := u4qBase_base C rfl h2
  subst hr
  subst hs
  have hSsup : X.Z 2 ⊔ X.Q 0 = X.S := u4qBase_supS C hB2 hZ2Q0 hcardZ2
  obtain ⟨hZ0Z2bot, hQ1eq1, hQ1eq2, hQ0Q1, hcardA, hcardQ1Q0B, hQ1prod⟩ :=
    u4qBase_step1 C hB0 hB2 hZ0Q2 hZ2Q0 hcardZ0 hcardZ2 hcardQ1 hSsup
  have hAQ1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
    rw [hQ1prod]
    exact le_sup_right
  have hnormZ0A : X.Z 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    u4qBase_Z0_normalizer_A hB0
  have hstep4 : X.Q 1 ⊓ X.Q (-1) = X.Z 0 :=
    u4qBase_step4 C hB0 hQ0Q1 hAQ1 hnormZ0A
  have hAelem : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := u4qBase_A_elem C
  have hQ1elem : IsElemAbelian 2 (X.Q 1) :=
    u4qBase_Q1_elem C hQ1prod helemZ0 helemZ2 hAelem hZ0Z1
  have hquad : ⁅⁅X.Q 0, X.S⁆, X.S⁆ ≤ X.Z 0 := u4qBase_hquad C hstep4 hQ1elem
  have hZ2Qg : X.Z 2 = X.Qg 4 := by simpa using h2.2.2.1
  have hZ0pc : X.Z 0 = pCoreOf 2 (X.arcStab (-2) 2) := by simpa using h2.2.2.2.1
  refine {
    gen := C, hasB0 := hB0, hasB2 := hB2, Z0_eq := hZ0L, Z0_le_Z1 := hZ0Z1,
    card_S := hcardS, card_Q0 := hcardQ0, card_Q1 := hcardQ1,
    Z2_eq := hZ2Qg, Z0_eq_pCore := hZ0pc, card_Z0 := hcardZ0, card_Z2 := hcardZ2,
    elem_Z0 := helemZ0, elem_Z2 := helemZ2,
    Z0_inf_Q2 := hZ0Q2, Z0_inf_Qm2 := hZ0Qm2, Z2_inf_Q0 := hZ2Q0, Z2_inf_Q4 := hZ2Q4,
    Z0_inf_Z2 := hZ0Z2bot, sup_S := hSsup, Q1_eq := hQ1prod, Q1_inf_Q0 := hQ0Q1,
    card_A := hcardA, card_Q0_inf_Q1 := by rw [inf_comm]; exact hcardQ1Q0B,
    Q1_inf_Qm1 := hstep4, elem_A := hAelem, elem_Q1 := hQ1elem, quad := hquad }

theorem Comm48.u4qBase {s r d : ℕ} {X : Setup Γ G} (C : X.Comm48 s r d) (h1 : d = 1)
    (hZ0L : X.Z 0 = centerOf (X.L 0)) (hZ0Z1 : X.Z 0 ≤ X.Z 1)
    (h2 : X.HasB 0 (d + 1) ∧ 2 * (d + 1) = r ∧
      X.Z ((d : ℤ) + 1) = X.Qg r ∧
      X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) ∧
      Nat.card (X.Z 0) = 2 ^ X.n 0 ∧ IsElemAbelian 2 (X.Z 0) ∧
      X.Z 0 ⊓ X.Q ((d : ℤ) + 1) = ⊥ ∧ X.Z 0 ⊓ X.Q (-((d : ℤ) + 1)) = ⊥) :
    X.U4qBase := by
  exact u4qBase_struct C h1 h2 hZ0L hZ0Z1

end Setup

end CFSG.Quasithin.St84

end
