module

public import CFSG.RankThree.PartOne.KF1514B.Constraints
public import CFSG.RankThree.PartOne.KF1514B.Card

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail QuadraticMap Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

structure ElemAb (A : Subgroup ↥(U0 b c)) : Prop where
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  sq : ∀ x ∈ A, x * x = 1

@[expose] noncomputable def Nsub : Subgroup ↥(U0 b c) := (Dhom (b := b) (c := c)).ker

theorem mem_Nsub {g : ↥(U0 b c)} : g ∈ Nsub (b := b) (c := c) ↔ Dm g = 1 := by
  simp [Nsub, MonoidHom.mem_ker, Dhom_apply]

@[expose] noncomputable def Lhom :
    ↥(Nsub (b := b) (c := c)) →* Multiplicative (Fin 3 → Fin 2 → K) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (Lp (x : ↥(U0 b c)))) (fun x y => by
    have hy : Dm (y : ↥(U0 b c)) = 1 := mem_Nsub.1 y.2
    have := Lp_mul_of_Dm_one (n := (x : ↥(U0 b c))) hy
    simp only [Subgroup.coe_mul, this, ofAdd_add])

theorem Lhom_apply (x : ↥(Nsub (b := b) (c := c))) :
    Lhom x = Multiplicative.ofAdd (Lp (x : ↥(U0 b c))) := rfl

@[expose] noncomputable def Zsub : Subgroup ↥(U0 b c) :=
  (Lhom (b := b) (c := c)).ker.map (Nsub (b := b) (c := c)).subtype

theorem mem_Zsub {g : ↥(U0 b c)} : g ∈ Zsub (b := b) (c := c) ↔ Dm g = 1 ∧ Lp g = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mem_Nsub.1 x.2, ?_⟩
    have := MonoidHom.mem_ker.1 hx
    rw [Lhom_apply] at this
    exact ofAdd_eq_one.1 this
  · rintro ⟨h1, h2⟩
    refine ⟨⟨g, mem_Nsub.2 h1⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [Lhom_apply]
    exact ofAdd_eq_one.2 h2

theorem Dm_eq_one_iff {g : ↥(U0 b c)} : Dm g = 1 ↔ da g = 0 ∧ db g = 0 ∧ dc g = 0 := by
  constructor
  · intro h
    simp [da, db, dc, h]
  · rintro ⟨h1, h2, h3⟩
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_one]
    fin_cases i <;> fin_cases j
    · simp [Dm_diag g 0]
    · exact h1
    · exact h3
    · exact Dm_lower g (show (0 : Fin 3) < 1 by decide)
    · simp [Dm_diag g 1]
    · exact h2
    · exact Dm_lower g (show (0 : Fin 3) < 2 by decide)
    · exact Dm_lower g (show (1 : Fin 3) < 2 by decide)
    · simp [Dm_diag g 2]

theorem Dm_ext {g g' : ↥(U0 b c)} (h1 : da g = da g') (h2 : db g = db g') (h3 : dc g = dc g') :
    Dm g = Dm g' := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · simp [Dm_diag g 0, Dm_diag g' 0]
  · exact h1
  · exact h3
  · exact (Dm_lower g (show (0 : Fin 3) < 1 by decide)).trans
      (Dm_lower g' (show (0 : Fin 3) < 1 by decide)).symm
  · simp [Dm_diag g 1, Dm_diag g' 1]
  · exact h2
  · exact (Dm_lower g (show (0 : Fin 3) < 2 by decide)).trans
      (Dm_lower g' (show (0 : Fin 3) < 2 by decide)).symm
  · exact (Dm_lower g (show (1 : Fin 3) < 2 by decide)).trans
      (Dm_lower g' (show (1 : Fin 3) < 2 by decide)).symm
  · simp [Dm_diag g 2, Dm_diag g' 2]

theorem Cp_symm (z : ↥(U0 b c)) (i j : Fin 3) : Cp z j i = Cp z i j := by
  have e := congrFun (congrFun (par_spec z).alt i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at e
  rw [e]
  exact neg_K _

theorem eq_of_Cent {z z' : ↥(U0 b c)} (hz : z ∈ Zsub (b := b) (c := c))
    (hz' : z' ∈ Zsub (b := b) (c := c)) (h01 : Cp z 0 1 = Cp z' 0 1) (h02 : Cp z 0 2 = Cp z' 0 2)
    (h12 : Cp z 1 2 = Cp z' 1 2) : z = z' := by
  obtain ⟨hD, hL⟩ := mem_Zsub.1 hz
  obtain ⟨hD', hL'⟩ := mem_Zsub.1 hz'
  have hC : Cp z = Cp z' := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact ((par_spec z).diag0 0).trans ((par_spec z').diag0 0).symm
    · exact h01
    · exact h02
    · exact (Cp_symm z 0 1).trans (h01.trans (Cp_symm z' 0 1).symm)
    · exact ((par_spec z).diag0 1).trans ((par_spec z').diag0 1).symm
    · exact h12
    · exact (Cp_symm z 0 2).trans (h02.trans (Cp_symm z' 0 2).symm)
    · exact (Cp_symm z 1 2).trans (h12.trans (Cp_symm z' 1 2).symm)
    · exact ((par_spec z).diag0 2).trans ((par_spec z').diag0 2).symm
  apply Subtype.ext
  rw [(par_spec z).eq, (par_spec z').eq, hD, hD', hL, hL', hC]

@[expose] noncomputable def LA (A : Subgroup ↥(U0 b c)) : AddSubgroup (Fin 3 → Fin 2 → K) :=
  Subgroup.toAddSubgroup' ((A.subgroupOf (Nsub (b := b) (c := c))).map Lhom)

theorem mem_LA {A : Subgroup ↥(U0 b c)} {L : Fin 3 → Fin 2 → K} :
    L ∈ LA A ↔ ∃ x : ↥(U0 b c), x ∈ A ∧ Dm x = 1 ∧ Lp x = L := by
  rw [LA, Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyL⟩
    refine ⟨(y : ↥(U0 b c)), hy, mem_Nsub.1 y.2, ?_⟩
    rw [Lhom_apply] at hyL
    exact Multiplicative.ofAdd.injective hyL
  · rintro ⟨x, hxA, hxD, hxL⟩
    refine ⟨⟨x, mem_Nsub.2 hxD⟩, hxA, ?_⟩
    rw [Lhom_apply, hxL]

theorem card_LA (A : Subgroup ↥(U0 b c)) :
    Nat.card ↥(LA A) = Nat.card ↥((A.subgroupOf (Nsub (b := b) (c := c))).map Lhom) :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))

theorem LA_orth {A : Subgroup ↥(U0 b c)} (hA : ElemAb A) : ∀ L ∈ LA A, Orth L := by
  intro L hL
  obtain ⟨x, hxA, hxD, rfl⟩ := mem_LA.1 hL
  exact Orth_Lp_of_sq hxD (hA.sq x hxA)

theorem card_AN_le (A : Subgroup ↥(U0 b c)) :
    Nat.card ↥(A ⊓ Nsub (b := b) (c := c)) ≤ Nat.card ↥(A ⊓ Zsub (b := b) (c := c)) *
      Nat.card ↥(LA A) := by
  rw [card_LA]
  exact card_inf_le_mul_map (Nsub (b := b) (c := c)) A Lhom

theorem card_LA_le_of_third_zero {A : Subgroup ↥(U0 b c)} (hA : ElemAb A)
    (hz : ∀ L ∈ LA A, L 2 = 0) : Nat.card ↥(LA A) ≤ Nat.card K ^ 2 :=
  card_le_sq_of_third_zero (LA A) (LA_orth hA) hz

theorem card_prod_three : Nat.card (K × K × K) = Nat.card K ^ 3 := by
  rw [Nat.card_prod, Nat.card_prod]; ring

theorem card_AZ_le_sq_of_yw {A : Subgroup ↥(U0 b c)} {b0 c0 : K} (hb0 : b0 ≠ 0)
    (hrel : ∀ z ∈ A ⊓ Zsub (b := b) (c := c), b0 * Cp z 0 2 + c0 * Cp z 1 2 = 0) :
    Nat.card ↥(A ⊓ Zsub (b := b) (c := c)) ≤ Nat.card K ^ 2 := by
  calc Nat.card ↥(A ⊓ Zsub (b := b) (c := c)) ≤ Nat.card (K × K) := by
        refine Nat.card_le_card_of_injective
          (fun z => (Cp (z : ↥(U0 b c)) 0 1, Cp (z : ↥(U0 b c)) 1 2)) ?_
        intro z z' h
        apply Subtype.ext
        simp only [Prod.mk.injEq] at h
        refine eq_of_Cent z.2.2 z'.2.2 h.1 ?_ h.2
        have e1 := hrel z z.2
        have e2 := hrel z' z'.2
        have : b0 * (Cp (z : ↥(U0 b c)) 0 2 - Cp (z' : ↥(U0 b c)) 0 2) = 0 := by
          rw [h.2] at e1
          linear_combination e1 - e2
        have := (mul_eq_zero.1 this).resolve_left hb0
        linear_combination this
    _ = Nat.card K ^ 2 := card_prod_self

theorem card_AZ_le_q_of_yw_zero {A : Subgroup ↥(U0 b c)}
    (hy : ∀ z ∈ A ⊓ Zsub (b := b) (c := c), Cp z 0 2 = 0)
    (hw : ∀ z ∈ A ⊓ Zsub (b := b) (c := c), Cp z 1 2 = 0) :
    Nat.card ↥(A ⊓ Zsub (b := b) (c := c)) ≤ Nat.card K := by
  refine Nat.card_le_card_of_injective
    (fun z => Cp (z : ↥(U0 b c)) 0 1) ?_
  intro z z' h
  apply Subtype.ext
  exact eq_of_Cent z.2.2 z'.2.2 h (by rw [hy z z.2, hy z' z'.2]) (by rw [hw z z.2, hw z' z'.2])

theorem AZ_constraints {A : Subgroup ↥(U0 b c)} (hA : ElemAb A) {g : ↥(U0 b c)} (hg : g ∈ A)
    {z : ↥(U0 b c)} (hz : z ∈ A ⊓ Zsub (b := b) (c := c)) :
    db g * Cp z 0 2 + dc g * Cp z 1 2 = 0 ∧ da g * Cp z 1 2 = 0 := by
  obtain ⟨hzD, hzL⟩ := mem_Zsub.1 hz.2
  exact Cp_constraints hzD hzL (hA.comm g hg z hz.1)

theorem card_map_Dhom_le_one {A : Subgroup ↥(U0 b c)} (h : ∀ g ∈ A, Dm g = 1) :
    Nat.card ↥(A.map (Dhom (b := b) (c := c))) ≤ 1 := by
  have : A.map (Dhom (b := b) (c := c)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun M hM => ?_
    obtain ⟨g, hg, rfl⟩ := hM
    rw [Dhom_apply]
    exact h g hg
  rw [this, Subgroup.card_bot]

theorem card_map_Dhom_le_q {A : Subgroup ↥(U0 b c)} (h : ∀ g ∈ A, da g = 0 ∧ db g = 0) :
    Nat.card ↥(A.map (Dhom (b := b) (c := c))) ≤ Nat.card K := by
  refine Nat.card_le_card_of_injective
    (fun M => ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) ?_
  intro M M' hMM
  have hMM' : ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 =
      ((M' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 := hMM
  apply Subtype.ext
  obtain ⟨g, hg, hgM⟩ := M.2
  obtain ⟨g', hg', hgM'⟩ := M'.2
  rw [Dhom_apply] at hgM hgM'
  rw [← hgM, ← hgM'] at hMM' ⊢
  refine Dm_ext ?_ ?_ hMM'
  · rw [(h g hg).1, (h g' hg').1]
  · rw [(h g hg).2, (h g' hg').2]

theorem fin2_eq_zero_of_smul {a : K} (ha : a ≠ 0) {v : Fin 2 → K} (h : a • v = 0) : v = 0 := by
  funext k
  have := congrFun h k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left ha

theorem card_le_pow5_of_db_ne {A : Subgroup ↥(U0 b c)} (hA : ElemAb A) {g0 : ↥(U0 b c)}
    (hg0 : g0 ∈ A) (hb0 : db g0 ≠ 0) : Nat.card ↥A ≤ Nat.card K ^ 5 := by
  have hda : ∀ g ∈ A, da g = 0 := by
    have e0 : da g0 * db g0 = 0 := da_mul_db_of_sq (hA.sq g0 hg0)
    have ha0 : da g0 = 0 := (mul_eq_zero.1 e0).resolve_right hb0
    intro g hg
    have := da_db_comm (hA.comm g hg g0 hg0)
    rw [ha0, zero_mul] at this
    exact (mul_eq_zero.1 this).resolve_right hb0
  let dbhom : ↥(U0 b c) →* Multiplicative K :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (db g)) (fun g g' => by
      simp only [db_mul, ofAdd_add])
  have hdbhom : ∀ g, dbhom g = Multiplicative.ofAdd (db g) := fun g => rfl
  set A' : Subgroup ↥(U0 b c) := A ⊓ dbhom.ker with hA'
  have hA'A : A' ≤ A := inf_le_left
  have hA'el : ElemAb A' :=
    ⟨fun x hx y hy => hA.comm x (hA'A hx) y (hA'A hy), fun x hx => hA.sq x (hA'A hx)⟩
  have hA'b : ∀ g ∈ A', da g = 0 ∧ db g = 0 := fun g hg => ⟨hda g (hA'A hg), by
    have := MonoidHom.mem_ker.1 hg.2
    rw [hdbhom] at this
    exact ofAdd_eq_one.1 this⟩
  have s1 := card_le_ker_mul_map dbhom A
  have s1' : Nat.card ↥(A.map dbhom) ≤ Nat.card K :=
    (Subgroup.card_le_card_group _).trans (by rw [Nat.card_congr Multiplicative.toAdd])
  have s2 := card_le_ker_mul_map (Dhom (b := b) (c := c)) A'
  have hker : (Dhom (b := b) (c := c)).ker = Nsub (b := b) (c := c) := rfl
  rw [hker] at s2
  have s3 := card_AN_le A'
  have hL3 : ∀ L ∈ LA A', L 2 = 0 := by
    intro L hL
    obtain ⟨x, hxA', hxD, rfl⟩ := mem_LA.1 hL
    have := (Lp_constraints hxD (hA.comm g0 hg0 x (hA'A hxA'))).2
    exact fin2_eq_zero_of_smul hb0 this
  have h4 : Nat.card ↥(LA A') ≤ Nat.card K ^ 2 := card_LA_le_of_third_zero hA'el hL3
  have hA'4 : Nat.card ↥A' ≤ Nat.card K ^ 4 := by
    by_cases hall : ∀ h ∈ A', dc h = 0
    · have hD : ∀ h ∈ A', Dm h = 1 := fun h hh => Dm_eq_one_iff.2 ⟨(hA'b h hh).1, (hA'b h hh).2, hall h hh⟩
      have h1 := card_map_Dhom_le_one hD
      have h3 : Nat.card ↥(A' ⊓ Zsub (b := b) (c := c)) ≤ Nat.card K ^ 2 := by
        refine card_AZ_le_sq_of_yw hb0 (c0 := dc g0) fun z hz => ?_
        exact (AZ_constraints hA hg0 ⟨hA'A hz.1, hz.2⟩).1
      calc Nat.card ↥A' ≤ Nat.card ↥(A' ⊓ Nsub (b := b) (c := c)) *
            Nat.card ↥(A'.map (Dhom (b := b) (c := c))) := s2
        _ ≤ (Nat.card K ^ 2 * Nat.card K ^ 2) * 1 :=
          Nat.mul_le_mul (s3.trans (Nat.mul_le_mul h3 h4)) h1
        _ = Nat.card K ^ 4 := by ring
    · push Not at hall
      obtain ⟨h, hh, hdc⟩ := hall
      have h1 := card_map_Dhom_le_q hA'b
      have h3 : Nat.card ↥(A' ⊓ Zsub (b := b) (c := c)) ≤ Nat.card K := by
        have hw : ∀ z ∈ A' ⊓ Zsub (b := b) (c := c), Cp z 1 2 = 0 := by
          intro z hz
          have e := (AZ_constraints hA'el hh hz).1
          rw [(hA'b h hh).2, zero_mul, zero_add] at e
          exact (mul_eq_zero.1 e).resolve_left hdc
        refine card_AZ_le_q_of_yw_zero (fun z hz => ?_) hw
        have e := (AZ_constraints hA hg0 ⟨hA'A hz.1, hz.2⟩).1
        rw [hw z hz, mul_zero, add_zero] at e
        exact (mul_eq_zero.1 e).resolve_left hb0
      calc Nat.card ↥A' ≤ Nat.card ↥(A' ⊓ Nsub (b := b) (c := c)) *
            Nat.card ↥(A'.map (Dhom (b := b) (c := c))) := s2
        _ ≤ (Nat.card K * Nat.card K ^ 2) * Nat.card K :=
          Nat.mul_le_mul (s3.trans (Nat.mul_le_mul h3 h4)) h1
        _ = Nat.card K ^ 4 := by ring
  calc Nat.card ↥A ≤ Nat.card ↥(A ⊓ dbhom.ker) * Nat.card ↥(A.map dbhom) := s1
    _ ≤ Nat.card K ^ 4 * Nat.card K := Nat.mul_le_mul hA'4 s1'
    _ = Nat.card K ^ 5 := by ring

end CFSG.RankThree.PartOne.KF1514B
