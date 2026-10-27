module

public import CFSG.Sporadic.SuzI301.Spec
public import Certificates.Certificate810308

public section

namespace CFSG.Sporadic.SuzI301Cover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzI301
  CFSG.Sporadic.SuzI301Cover.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.HardMathSupport.Dickson.I271.TabSuzFuse

section Check


theorem noAltForm : ∀ C : Matrix (Fin 3) (Fin 3) (ZMod 3), (∀ i, C i i = 0) →
    (∀ i j, C j i = -C i j) → (∀ k : Fin 2, nMat k * C * (nMat k).transpose = C) → C = 0 :=
  Certificates.certificate810308.1

theorem noLinForm : ∀ q : Fin 3 → ZMod 3, (∀ k : Fin 2, (nMat k).mulVec q = q) → q = 0 :=
  Certificates.certificate810308.2.1

theorem suzhCheck_parts : (∀ i < 3, validA 1782 (bArr i) = true) ∧
    (∀ k < 2, validA 1782 (nArr k) = true ∧ inP (levels ()) (nArr k) = true) ∧
    ∀ k < 2, ∀ i < 3, conjOK k i = true := by
  have h := Certificates.certificate810308.2.2
  simp only [suzhCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨fun i hi => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · interval_cases i
    exacts [h1, h2, h3]
  · interval_cases k
    exacts [⟨h4, h5⟩, ⟨h6, h7⟩]
  · interval_cases k <;> interval_cases i
    exacts [h8, h9, h10, h11, h12, h13]

end Check

@[expose] noncomputable def nP (k : ℕ) : Equiv.Perm (Fin 1782) := permOfArr 1782 (nArr k)

@[expose] noncomputable def bP (i : ℕ) : Equiv.Perm (Fin 1782) := permOfArr 1782 (bArr i)

theorem bP_zero : bP 0 = dP := by
  unfold bP dP
  rw [show bArr 0 = sD () from if_pos rfl]

theorem bP_one : bP 1 = b2P := by
  unfold bP b2P
  rw [show bArr 1 = sB2 () by rw [bArr, if_neg one_ne_zero, if_pos rfl]]

theorem bP_two : bP 2 = b3P := by
  unfold bP b3P
  rw [show bArr 2 = sB3 () by rw [bArr, if_neg two_ne_zero, if_neg (by norm_num)]]

section Perms


theorem rep_nP {k : ℕ} (hk : k < 2) : Rep 1782 (nArr k) (nP k) :=
  rep_of_validA (suzhCheck_parts.2.1 k hk).1

theorem rep_nP_inv {k : ℕ} (hk : k < 2) : Rep 1782 (invCand 1782 (nArr k)) (nP k)⁻¹ :=
  rep_inv_of_validA (suzhCheck_parts.2.1 k hk).1

theorem nP_mem {k : ℕ} (hk : k < 2) :
    nP k ∈ suzM :=
  mem_suzM_of_inP (rep_nP hk) (suzhCheck_parts.2.1 k hk).2

theorem rep_bP {i : ℕ} (hi : i < 3) : Rep 1782 (bArr i) (bP i) :=
  rep_of_validA (suzhCheck_parts.1 i hi)

theorem nP_conj {k : ℕ} (hk : k < 2) (i : Fin 3) :
    nP k * bP i * (nP k)⁻¹ = bP 0 ^ ((nMats[k]!)[(i : ℕ)]!)[0]! *
      (bP 1 ^ ((nMats[k]!)[(i : ℕ)]!)[1]! * bP 2 ^ ((nMats[k]!)[(i : ℕ)]!)[2]!) := by
  have h1 : Rep 1782 (conj1782 (nArr k) (invCand 1782 (nArr k)) (bArr i))
      (nP k * bP i * (nP k)⁻¹) := by
    rw [mul_assoc]
    exact rep_compA (rep_nP hk) (rep_compA (rep_bP i.isLt) (rep_nP_inv hk))
  have h2 : Rep 1782 (prodArr ((nMats[k]!)[(i : ℕ)]!)) (bP 0 ^ ((nMats[k]!)[(i : ℕ)]!)[0]! *
      (bP 1 ^ ((nMats[k]!)[(i : ℕ)]!)[1]! * bP 2 ^ ((nMats[k]!)[(i : ℕ)]!)[2]!)) :=
    rep_compA (rep_powArr (rep_bP (by norm_num)) _) (rep_compA (rep_powArr (rep_bP (by norm_num)) _)
      (rep_powArr (rep_bP (by norm_num)) _))
  exact eq_of_eqA h1 h2 (suzhCheck_parts.2.2 k hk i i.isLt)

end Perms

section Model


theorem bP_mem' {i : ℕ} (hi : i < 3) : bP i ∈ suzM := by
  obtain ⟨hd, hb2, hb3, -⟩ := gens_mem
  interval_cases i
  · rw [bP_zero]
    exact (invE_le_centM (by norm_num) hd).2
  · rw [bP_one]
    exact (invE_le_centM (by norm_num) hb2).2
  · rw [bP_two]
    exact (invE_le_centM (by norm_num) hb3).2

theorem bP_mem (i : Fin 3) : bP i ∈ suzM := bP_mem' i.isLt

@[expose] noncomputable def bM (i : Fin 3) : ↥suzM := ⟨bP i, bP_mem i⟩

private theorem bP_comm {i j : ℕ} (hi : i < 3) (hj : j < 3) : Commute (bP i) (bP j) := by
  obtain ⟨h12, h13, h23, -⟩ := commute_facts
  interval_cases i <;> interval_cases j <;> simp only [bP_zero, bP_one, bP_two]
  exacts [Commute.refl _, h12, h13, h12.symm, Commute.refl _, h23, h13.symm, h23.symm,
    Commute.refl _]

theorem bM_comm (i j : Fin 3) : Commute (bM i) (bM j) :=
  Subtype.ext (bP_comm i.isLt j.isLt).eq

private theorem bP_pow_three {i : ℕ} (hi : i < 3) : bP i ^ 3 = 1 := by
  obtain ⟨h1, h2, h3⟩ := pow_facts
  interval_cases i <;> simp only [bP_zero, bP_one, bP_two]
  exacts [h1, h2, h3]

theorem bM_pow_three (i : Fin 3) : bM i ^ 3 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact bP_pow_three i.isLt)

theorem ofFn_prod_three {G : Type*} [Monoid G] (f : Fin 3 → G) :
    (List.ofFn f).prod = f 0 * (f 1 * f 2) := by
  rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, List.ofFn_zero, List.prod_nil, mul_one]
  rfl

theorem bM_indep (e : Fin 3 → ℕ) (he : ∀ i, e i < 3)
    (h : (List.ofFn fun i : Fin 3 => bM i ^ e i).prod = 1) : ∀ i, e i = 0 := by
  rw [ofFn_prod_three] at h
  have h1 := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
  have h' : dP ^ e 0 * b2P ^ e 1 * b3P ^ e 2 = 1 := by
    rw [← bP_zero, ← bP_one, ← bP_two, mul_assoc]
    exact h1
  obtain ⟨h0, h1, h2⟩ := indep_facts (e 0) (e 1) (e 2) (he 0) (he 1) (he 2) h'
  intro i
  fin_cases i
  exacts [h0, h1, h2]

theorem closure_range_bM : Subgroup.closure (Set.range bM) = B1.subgroupOf suzM := by
  apply Subgroup.map_injective suzM.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, B1]
  have hle : Subgroup.closure ({dP, b2P, b3P} : Set (Equiv.Perm (Fin 1782))) ≤ suzM := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · rw [← bP_zero]; exact bP_mem' (by norm_num)
    · rw [← bP_one]; exact bP_mem' (by norm_num)
    · rw [← bP_two]; exact bP_mem' (by norm_num)
  rw [inf_eq_left.2 hle]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
    show bP i = dP ∨ bP i = b2P ∨ bP i = b3P
    interval_cases i
    · exact Or.inl bP_zero
    · exact Or.inr (Or.inl bP_one)
    · exact Or.inr (Or.inr bP_two)
  · rintro (rfl | rfl | rfl)
    · exact ⟨bM 0, ⟨0, rfl⟩, bP_zero⟩
    · exact ⟨bM 1, ⟨1, rfl⟩, bP_one⟩
    · exact ⟨bM 2, ⟨2, rfl⟩, bP_two⟩


@[expose] noncomputable def nM (k : Fin 2) : ↥suzM := ⟨nP k, nP_mem k.isLt⟩

private theorem nMats_lt : ∀ k < 2, ∀ i < 3, ∀ j < 3, ((nMats[k]!)[i]!)[j]! < 3 := by
  decide

theorem nM_conj (k : Fin 2) (i : Fin 3) :
    nM k * bM i * (nM k)⁻¹ = (List.ofFn fun j : Fin 3 => bM j ^ (nMat k i j).val).prod := by
  rw [ofFn_prod_three]
  have hv : ∀ j : Fin 3, (nMat k i j).val = ((nMats[(k : ℕ)]!)[(i : ℕ)]!)[(j : ℕ)]! := by
    intro j
    unfold nMat
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (nMats_lt k k.isLt i i.isLt j j.isLt)]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, hv]
  exact nP_conj k.isLt i

end Model

end CFSG.Sporadic.SuzI301Cover
