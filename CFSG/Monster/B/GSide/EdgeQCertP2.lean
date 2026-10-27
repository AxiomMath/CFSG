module

public import CFSG.Monster.B.TwoA.Unitary.WStab
public import CFSG.Monster.B.Rep4371.Bits
public import CFSG.Monster.VisCert.Basis
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.WStab
public import CFSG.Monster.B.GSide.EdgeQCertP2Inputs
public import Certificates.Certificate3043

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
open CFSG.Monster.B.Rep4371 (RepPerm permWord_bvec)

theorem repPerm_one : RepPerm (1 : Equiv.Perm (Fin 24)) arrId := fun i => by
  simp [arrId]

theorem repPerm_mul {p q : Equiv.Perm (Fin 24)} {ap aq : Array ℕ} (hp : RepPerm p ap)
    (hq : RepPerm q aq) : RepPerm (p * q) (arrMul ap aq) := fun i => by
  have e : (arrMul ap aq)[(i : ℕ)]! = ap[aq[(i : ℕ)]!]! := by simp [arrMul]
  rw [Equiv.Perm.mul_apply, hp, e, ← hq i]

theorem repPerm_gen (k : Fin 6) : RepPerm ((p2Gen k : AutPerm) : Equiv.Perm (Fin 24))
    n6PermArr[(k : ℕ)]! := fun i => n6Aut_apply k i

theorem repPerm_p2Word : ∀ w : List (Fin 6),
    RepPerm ((p2Word w : AutPerm) : Equiv.Perm (Fin 24)) (p2Arr w)
  | [] => repPerm_one
  | k :: w => repPerm_mul (repPerm_p2Word w) (repPerm_gen k)

theorem eq_of_repPerm {p q : P2} {a : Array ℕ}
    (hp : RepPerm ((p : AutPerm) : Equiv.Perm (Fin 24)) a)
    (hq : RepPerm ((q : AutPerm) : Equiv.Perm (Fin 24)) a) : p = q := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  rw [hp, hq]

theorem eq_one_of_repPerm {p : P2} (hp : RepPerm ((p : AutPerm) : Equiv.Perm (Fin 24)) arrId) :
    p = 1 := eq_of_repPerm hp repPerm_one

theorem P2_apply_two (p : P2) : ((p : AutPerm) : Equiv.Perm (Fin 24)) 2 = 2 := (mem_P2.1 p.2).2

theorem P2_apply_gt_two (p : P2) {i : Fin 24} (hi : 2 < (i : ℕ)) :
    2 < (((p : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) := by
  set f := ((p : AutPerm) : Equiv.Perm (Fin 24)) with hf
  have h2 := P2_apply_two p
  have h01 := (mem_Ppair_iff (p : AutPerm)).1 (mem_P2.1 p.2).1
  by_contra h
  push Not at h
  have hcases : f i = 0 ∨ f i = 1 ∨ f i = 2 := by
    have : (f i : ℕ) = 0 ∨ (f i : ℕ) = 1 ∨ (f i : ℕ) = 2 := by omega
    rcases this with h' | h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Or.inl (Fin.ext h'))
    · exact Or.inr (Or.inr (Fin.ext h'))
  have hne : ∀ j : Fin 24, f i = f j → i = j := fun j e => f.injective e
  rcases hcases with e | e | e
  · rcases h01 with ⟨h0, -⟩ | ⟨-, h1⟩
    · have := hne 0 (e.trans h0.symm); omega
    · have := hne 1 (e.trans h1.symm); omega
  · rcases h01 with ⟨-, h1⟩ | ⟨h0, -⟩
    · have := hne 1 (e.trans h1.symm); omega
    · have := hne 0 (e.trans h0.symm); omega
  · have := hne 2 (e.trans h2.symm); omega

abbrev Delta : Type := {i : Fin 24 // 2 < (i : ℕ)}

@[expose, instance_reducible] def deltaAction : MulAction P2 Delta where
  smul p i := ⟨((p : AutPerm) : Equiv.Perm (Fin 24)) i, P2_apply_gt_two p i.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] deltaAction

theorem coe_smul_delta (p : P2) (i : Delta) :
    ((p • i : Delta) : Fin 24) = ((p : AutPerm) : Equiv.Perm (Fin 24)) i := rfl

theorem card_Delta : Nat.card Delta = 21 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem deltaPaths_ok : ∀ j : Fin 21,
    ((p2Arr (deltaPaths.getD j []))[3]!) = (j : ℕ) + 3 := by
  decide

theorem exists_smul_three (δ : Delta) : ∃ p : P2, p • (⟨3, by decide⟩ : Delta) = δ := by
  obtain ⟨⟨d, hd24⟩, hd⟩ := δ
  have hj : d - 3 < 21 := by simp only at hd; omega
  refine ⟨p2Word (deltaPaths.getD (d - 3) []), Subtype.ext (Fin.ext ?_)⟩
  rw [coe_smul_delta, repPerm_p2Word]
  have h := deltaPaths_ok ⟨d - 3, hj⟩
  have e3 : (((⟨3, by decide⟩ : Delta) : Fin 24) : ℕ) = 3 := rfl
  rw [e3]
  simp only at h ⊢
  rw [h]
  simp only at hd
  omega

theorem B1_comp_swap_not_mem : B 1 ∘ ⇑(Equiv.swap (0 : Fin 24) 1) ∉ C := by decide

theorem eq_one_of_fix_two {x : P2}
    (hfix : ∀ i : Fin 24, 2 < (i : ℕ) → ((x : AutPerm) : Equiv.Perm (Fin 24)) i = i) : x = 1 := by
  set f := ((x : AutPerm) : Equiv.Perm (Fin 24)) with hf
  have h2 : f 2 = 2 := P2_apply_two x
  have hge : ∀ i : Fin 24, 2 ≤ (i : ℕ) → f i = i := by
    intro i hi
    rcases Nat.lt_or_ge 2 (i : ℕ) with h | h
    · exact hfix i h
    · have hi2 : i = 2 := Fin.ext (by omega)
      rw [hi2]
      exact h2
  rcases (mem_Ppair_iff (x : AutPerm)).1 (mem_P2.1 x.2).1 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine Subtype.ext (Subtype.ext ?_)
    ext i
    show (f i : ℕ) = i
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ 2 ≤ (i : ℕ) by omega) with hi | hi | hi
    · rw [show i = 0 from Fin.ext hi, h0]
    · rw [show i = 1 from Fin.ext hi, h1]
    · rw [hge i hi]
  · exfalso
    have hsw : f = Equiv.swap (0 : Fin 24) 1 := by
      ext i
      rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ 2 ≤ (i : ℕ) by omega) with hi | hi | hi
      · rw [show i = 0 from Fin.ext hi, h0, Equiv.swap_apply_left]
      · rw [show i = 1 from Fin.ext hi, h1, Equiv.swap_apply_right]
      · rw [hge i hi, Equiv.swap_apply_of_ne_of_ne (fun e => by rw [e] at hi; simp at hi)
          (fun e => by rw [e] at hi; simp at hi)]
    have hmem := comp_mem_of_mem_AutPerm (x : AutPerm).2 (B_mem_C 1)
    rw [← hf, hsw] at hmem
    exact B1_comp_swap_not_mem hmem

theorem P2_normal_isPGroup_eq_bot {X : Subgroup P2} (hn : X.Normal) (h2 : IsPGroup 2 X) :
    X = ⊥ := by
  have hfix := h2.nonempty_fixed_point_of_prime_not_dvd_card Delta (by rw [card_Delta]; decide)
  obtain ⟨δ₀, hδ₀⟩ := hfix
  have hall : ∀ x ∈ X, ∀ δ : Delta, x • δ = δ := by
    intro x hx δ
    obtain ⟨p₀, hp₀⟩ := exists_smul_three δ₀
    obtain ⟨p₁, hp₁⟩ := exists_smul_three δ
    set p := p₁ * p₀⁻¹ with hp
    have hpδ : p • δ₀ = δ := by
      rw [hp, mul_smul, ← hp₀, inv_smul_smul, hp₁]
    have hconj : p⁻¹ * x * p ∈ X := by
      have := hn.conj_mem x hx p⁻¹
      rwa [inv_inv] at this
    have hfx : (p⁻¹ * x * p) • δ₀ = δ₀ := hδ₀ ⟨_, hconj⟩
    rw [← hpδ]
    calc x • p • δ₀ = p • ((p⁻¹ * x * p) • δ₀) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = p • δ₀ := by rw [hfx]
  refine (Subgroup.eq_bot_iff_forall X).2 fun x hx =>
    eq_one_of_fix_two fun i hi => congrArg Subtype.val (hall x hx ⟨i, hi⟩)

theorem exists_fixed_ne_one {G : Type*} [Group G] [Finite G] (φ : MulAut G) (hφ : φ ^ 4 = 1)
    {H : Subgroup G} (hH : ∀ h ∈ H, φ h ∈ H) (h2 : ∃ k, Nat.card H = 2 ^ k) (hne : H ≠ ⊥) :
    ∃ h ∈ H, h ≠ 1 ∧ φ h = h := by
  classical
  have : Fintype H := Fintype.ofFinite _
  have hφ3 : ∀ h ∈ H, (φ ^ 3) h ∈ H := fun h hh => by
    rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_one]
    exact hH _ (hH _ (hH _ hh))
  have hφ4 : ∀ h : G, (φ ^ 3) (φ h) = h := fun h => by
    rw [← MulAut.mul_apply, ← pow_succ, hφ]
    rfl
  let σ : Equiv.Perm H :=
    { toFun := fun h => ⟨φ h, hH _ h.2⟩
      invFun := fun h => ⟨(φ ^ 3) h, hφ3 _ h.2⟩
      left_inv := fun h => Subtype.ext (hφ4 h)
      right_inv := fun h => Subtype.ext (by
        show φ ((φ ^ 3) h) = h
        rw [← MulAut.mul_apply, ← pow_succ', hφ]
        rfl) }
  have hσ : σ ^ 2 ^ 2 = 1 := by
    ext h
    show ((σ ^ 4) h : G) = h
    have key : ∀ n : ℕ, ((σ ^ n) h : G) = (φ ^ n) h := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', MulAut.mul_apply, ← ih]
        rfl
    rw [key, hφ]
    rfl
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 2) hσ
  obtain ⟨k, hk⟩ := h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  have hcard : Fintype.card H % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card, hk]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [pow_succ, Nat.mul_mod_left]
  have h1 : (1 : H) ∈ σ.supportᶜ := by
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    exact Subtype.ext (map_one φ)
  have hcard2 : 2 ≤ σ.supportᶜ.card := by
    have hpos : 0 < σ.supportᶜ.card := Finset.card_pos.2 ⟨1, h1⟩
    have : σ.supportᶜ.card % 2 = 0 := by
      rw [Nat.ModEq] at hmod
      omega
    omega
  obtain ⟨h, hh, hne1⟩ := Finset.exists_mem_ne hcard2 1
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hh
  exact ⟨h, h.2, fun e => hne1 (Subtype.ext e), congrArg Subtype.val hh⟩

abbrev NQ : Type := Multiplicative (C012 ⧸ ΩIn C012)

@[expose] def nOf (m : ℕ) (h : bvec 24 m ∈ C012) : NQ :=
  Multiplicative.ofAdd (Submodule.Quotient.mk ⟨bvec 24 m, h⟩)

theorem bvec_xor_mem {m m' : ℕ} (h : bvec 24 m ∈ C012) (h' : bvec 24 m' ∈ C012) :
    bvec 24 (m ^^^ m') ∈ C012 := by
  rw [bvec_xor]
  exact C012.add_mem h h'

theorem nOf_mul {m m' : ℕ} (h : bvec 24 m ∈ C012) (h' : bvec 24 m' ∈ C012) :
    nOf m h * nOf m' h' = nOf (m ^^^ m') (bvec_xor_mem h h') := by
  show Multiplicative.ofAdd (Submodule.Quotient.mk _ + Submodule.Quotient.mk _) = _
  rw [← Submodule.Quotient.mk_add]
  congr 2
  exact Subtype.ext (bvec_xor 24 m m').symm

theorem bvec_Ω : bvec 24 (2 ^ 24 - 1) = Ω := by
  funext i
  revert i
  decide

theorem nOf_eq_nOf {m m' : ℕ} (h : bvec 24 m ∈ C012) (h' : bvec 24 m' ∈ C012)
    (hrel : m ^^^ m' = 0 ∨ m ^^^ m' = 2 ^ 24 - 1) : nOf m h = nOf m' h' := by
  show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  congr 1
  rw [Submodule.Quotient.eq, mem_ΩIn]
  have e : ((⟨bvec 24 m, h⟩ - ⟨bvec 24 m', h'⟩ : C012) : Fin 24 → ZMod 2) =
      bvec 24 (m ^^^ m') := by
    rw [bvec_xor, Submodule.coe_sub, sub_eq_add_neg, ZModModule.neg_eq_self]
  rw [e]
  rcases hrel with h0 | h0
  · left
    rw [h0, bvec_zero]
  · right
    rw [h0, bvec_Ω]

theorem nOf_eq_nOf_iff {m m' : ℕ} (hm : m < 2 ^ 24) (hm' : m' < 2 ^ 24) (h : bvec 24 m ∈ C012)
    (h' : bvec 24 m' ∈ C012) :
    nOf m h = nOf m' h' ↔ m ^^^ m' = 0 ∨ m ^^^ m' = 2 ^ 24 - 1 := by
  refine ⟨fun e => ?_, nOf_eq_nOf h h'⟩
  have e' : Submodule.Quotient.mk (p := ΩIn C012) ⟨bvec 24 m, h⟩ =
      Submodule.Quotient.mk ⟨bvec 24 m', h'⟩ := congrArg Multiplicative.toAdd e
  rw [Submodule.Quotient.eq, mem_ΩIn] at e'
  have e2 : ((⟨bvec 24 m, h⟩ - ⟨bvec 24 m', h'⟩ : C012) : Fin 24 → ZMod 2) =
      bvec 24 (m ^^^ m') := by
    rw [bvec_xor, Submodule.coe_sub, sub_eq_add_neg, ZModModule.neg_eq_self]
  rw [e2] at e'
  have hx : m ^^^ m' < 2 ^ 24 := Nat.xor_lt_two_pow hm hm'
  rcases e' with e' | e'
  · left
    exact VisCert.bvec_injective hx (by norm_num) (e'.trans (bvec_zero 24).symm)
  · right
    exact VisCert.bvec_injective hx (by norm_num) (e'.trans bvec_Ω.symm)

theorem permWordN_mem {p : P2} {arr : Array ℕ}
    (hp : RepPerm ((p : AutPerm) : Equiv.Perm (Fin 24)) arr) {m : ℕ} (h : bvec 24 m ∈ C012) :
    bvec 24 (Model.permWordN arr m) ∈ C012 := by
  rw [← permWord_bvec hp]
  exact c012Hyp.preserves _ p.2 _ h

theorem permActD_nOf {p : P2} {arr : Array ℕ}
    (hp : RepPerm ((p : AutPerm) : Equiv.Perm (Fin 24)) arr) {m : ℕ} (h : bvec 24 m ∈ C012) :
    permActD c012Hyp p (nOf m h) = nOf (Model.permWordN arr m) (permWordN_mem hp h) := by
  rw [nOf, permActD_mk]
  congr 2
  apply Subtype.ext
  rw [coe_permCD, permWord_bvec hp]

theorem bvec_coeffStep (c : Fin 10 → ZMod 2) (m : ℕ) (i : Fin 10) :
    bvec 24 (coeffStep c m i) = bvec 24 m + c i • signVec i := by
  rw [coeffStep]
  have hz : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hz (c i) with h | h <;> rw [h]
  · rw [ite_eq_right (by decide), zero_smul, add_zero]
  · rw [ite_eq_left rfl, bvec_xor, one_smul, signVec_eq]

theorem bvec_foldl_coeffStep (c : Fin 10 → ZMod 2) :
    ∀ (l : List (Fin 10)) (m : ℕ), bvec 24 (l.foldl (coeffStep c) m) =
      bvec 24 m + (l.map fun i => c i • signVec i).sum
  | [], m => by simp
  | i :: l, m => by
    rw [List.foldl_cons, bvec_foldl_coeffStep c l, bvec_coeffStep, List.map_cons, List.sum_cons,
      add_assoc]

theorem bvec_coeffMask (c : Fin 10 → ZMod 2) :
    bvec 24 (coeffMask c) = ∑ i, c i • signVec i := by
  rw [coeffMask, bvec_foldl_coeffStep, bvec_zero, zero_add, Fin.sum_univ_def]

theorem coeffMask_mem (c : Fin 10 → ZMod 2) : bvec 24 (coeffMask c) ∈ C012 := by
  rw [bvec_coeffMask]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (signVec_mem i)

theorem signMask_lt : ∀ i : Fin 10, signMask i < 2 ^ 24 := by decide

theorem foldl_coeffStep_lt (c : Fin 10 → ZMod 2) :
    ∀ (l : List (Fin 10)) (m : ℕ), m < 2 ^ 24 → l.foldl (coeffStep c) m < 2 ^ 24
  | [], _, h => h
  | i :: l, m, h => by
    rw [List.foldl_cons]
    refine foldl_coeffStep_lt c l _ ?_
    rw [coeffStep]
    split_ifs
    · exact Nat.xor_lt_two_pow h (signMask_lt i)
    · exact h

theorem coeffMask_lt (c : Fin 10 → ZMod 2) : coeffMask c < 2 ^ 24 :=
  foldl_coeffStep_lt c _ 0 (by norm_num)

theorem exists_coeffMask {a : Fin 24 → ZMod 2} (ha : a ∈ C012) :
    ∃ c : Fin 10 → ZMod 2, bvec 24 (coeffMask c) = a := by
  rw [← span_signVec, Submodule.mem_span_range_iff_exists_fun] at ha
  obtain ⟨c, hc⟩ := ha
  exact ⟨c, (bvec_coeffMask c).trans hc⟩

theorem exists_nOf (n : NQ) : ∃ c : Fin 10 → ZMod 2, n = nOf (coeffMask c) (coeffMask_mem c) := by
  induction n using multQD_induction with
  | h a =>
    obtain ⟨c, hc⟩ := exists_coeffMask a.2
    refine ⟨c, ?_⟩
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 2
    exact Subtype.ext hc.symm

@[expose] def p2A : P2 := p2Word wordA

@[expose] def p2B : P2 := p2Word wordB

theorem p2Word_append : ∀ w v : List (Fin 6), p2Word (w ++ v) = p2Word v * p2Word w
  | [], v => by rw [List.nil_append, p2Word, mul_one]
  | k :: w, v => by rw [List.cons_append, p2Word, p2Word_append w v, p2Word, mul_assoc]

theorem arr_checks :
    p2Arr (wordA ++ wordA ++ wordA ++ wordA) = arrId ∧
    p2Arr (wordB ++ wordB ++ wordB ++ wordB) = arrId ∧
    p2Arr (wordB ++ wordA) = p2Arr (wordA ++ wordB) :=
  Certificates.certificate3043.1

theorem pow_four_eq (g : P2) : g ^ 4 = g * g * g * g := by
  rw [pow_succ, pow_succ, pow_succ, pow_one]

theorem p2A_pow_four : p2A ^ 4 = 1 := by
  have e : p2A ^ 4 = p2Word (wordA ++ wordA ++ wordA ++ wordA) := by
    rw [p2Word_append, p2Word_append, p2Word_append, pow_four_eq, p2A, mul_assoc, mul_assoc]
  rw [e]
  refine eq_one_of_repPerm ?_
  rw [← arr_checks.1]
  exact repPerm_p2Word _

theorem p2B_pow_four : p2B ^ 4 = 1 := by
  have e : p2B ^ 4 = p2Word (wordB ++ wordB ++ wordB ++ wordB) := by
    rw [p2Word_append, p2Word_append, p2Word_append, pow_four_eq, p2B, mul_assoc, mul_assoc]
  rw [e]
  refine eq_one_of_repPerm ?_
  rw [← arr_checks.2.1]
  exact repPerm_p2Word _

theorem p2A_mul_p2B : p2A * p2B = p2B * p2A := by
  have e1 : p2A * p2B = p2Word (wordB ++ wordA) := by rw [p2Word_append]; rfl
  have e2 : p2B * p2A = p2Word (wordA ++ wordB) := by rw [p2Word_append]; rfl
  rw [e1, e2]
  refine eq_of_repPerm (repPerm_p2Word _) ?_
  rw [arr_checks.2.2]
  exact repPerm_p2Word _

theorem fixedChecks : ∀ c : Fin 10 → ZMod 2,
    (Model.permWordN (p2Arr wordA) (coeffMask c) ^^^ coeffMask c = 0 ∨
      Model.permWordN (p2Arr wordA) (coeffMask c) ^^^ coeffMask c = 2 ^ 24 - 1) →
    (Model.permWordN (p2Arr wordB) (coeffMask c) ^^^ coeffMask c = 0 ∨
      Model.permWordN (p2Arr wordB) (coeffMask c) ^^^ coeffMask c = 2 ^ 24 - 1) →
    (coeffMask c ^^^ 0 = 0 ∨ coeffMask c ^^^ 0 = 2 ^ 24 - 1 ∨ coeffMask c ^^^ vStar = 0 ∨
      coeffMask c ^^^ vStar = 2 ^ 24 - 1) :=
  Certificates.certificate3043.2

@[expose] def orbL : List ℕ :=
  [1589783, 4331543, 4276519, 8552999, 2392343, 983055, 8463383, 2631719, 1188167, 61455, 8669255,
    4752455, 2245767, 2167367, 4465287, 1315879, 3855, 15728655, 8917383, 1149063, 255]

@[expose] def orbPar : List ℕ := [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4, 5, 6, 10, 17]

@[expose] def orbGen : List (Fin 6) :=
  [0, 0, 1, 2, 3, 4, 0, 1, 3, 4, 0, 1, 2, 3, 2, 1, 4, 2, 3, 0, 3]

@[expose] def orbTargets : List (List ℕ) :=
  [[0, 1, 4, 6], [3, 4, 5, 6, 7], [1, 2, 4, 5, 7], [5], [0, 2, 3, 4, 5], [0, 1, 3, 4, 5, 7],
    [0, 1, 2, 5, 6], [1, 2, 3, 4, 5, 6, 8], [2, 4, 6, 7], [3, 7]]

@[expose] def xorL (l : List ℕ) : ℕ := l.foldl (fun m t => m ^^^ orbL.getD t 0) 0

theorem chainChecks :
    orbL.getD 0 0 = vStar ∧
    (∀ j : Fin 21, 0 < (j : ℕ) → orbPar.getD j 0 < (j : ℕ) ∧
      orbL.getD j 0 = Model.permWordN n6PermArr[((orbGen.getD j 0 : Fin 6) : ℕ)]!
        (orbL.getD (orbPar.getD j 0) 0)) ∧
    (∀ i : Fin 10, signMask i ^^^ xorL (orbTargets.getD i []) = 0 ∨
      signMask i ^^^ xorL (orbTargets.getD i []) = 2 ^ 24 - 1) ∧
    (∀ i : Fin 10, ∀ j ∈ orbTargets.getD i [], j < 21) := by
  decide

theorem combN_lt (f : ℕ → ℕ) (hf : ∀ i < 24, f i < 2 ^ 24) :
    ∀ n, n ≤ 24 → ∀ a, Model.combN f n a < 2 ^ 24
  | 0, _, _ => by simp [Model.combN]
  | n + 1, hn, a => by
    rw [Model.combN]
    refine Nat.xor_lt_two_pow (combN_lt f hf n (by omega) a) ?_
    split_ifs
    · exact hf n (by omega)
    · norm_num

theorem permWordN_lt {p : Equiv.Perm (Fin 24)} {arr : Array ℕ} (hp : RepPerm p arr) (w : ℕ) :
    Model.permWordN arr w < 2 ^ 24 := by
  refine combN_lt _ (fun i hi => ?_) 24 le_rfl w
  have h := hp ⟨i, hi⟩
  simp only at h
  rw [← h]
  exact Nat.pow_lt_pow_right (by norm_num) (p ⟨i, hi⟩).2

theorem natCard_NQ : Nat.card NQ = 2 ^ 9 := by
  rw [← natCard_C012_quot]
  exact Nat.card_congr Multiplicative.toAdd

theorem finite_NQ : Finite NQ := Nat.finite_of_card_ne_zero (by rw [natCard_NQ]; norm_num)

theorem exists_card_two_pow (H : Subgroup NQ) : ∃ k, Nat.card H = 2 ^ k := by
  have h := Subgroup.card_subgroup_dvd_card H
  rw [natCard_NQ] at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨k, hk⟩

theorem nOf_zero (h : bvec 24 0 ∈ C012) : nOf 0 h = 1 := by
  show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
  congr 1
  rw [Submodule.Quotient.mk_eq_zero, mem_ΩIn]
  exact Or.inl (bvec_zero 24)

theorem fixed_iff {p : P2} {arr : Array ℕ}
    (hp : RepPerm ((p : AutPerm) : Equiv.Perm (Fin 24)) arr) {m : ℕ} (hm : m < 2 ^ 24)
    (h : bvec 24 m ∈ C012) :
    permActD c012Hyp p (nOf m h) = nOf m h ↔
      (Model.permWordN arr m ^^^ m = 0 ∨ Model.permWordN arr m ^^^ m = 2 ^ 24 - 1) := by
  rw [permActD_nOf hp, nOf_eq_nOf_iff (permWordN_lt hp m) hm]

theorem vStar_mem {N' : Subgroup NQ}
    (hinv : ∀ p : P2, ∀ n ∈ N', permActD c012Hyp p n ∈ N') (hne : N' ≠ ⊥) :
    ∃ h : bvec 24 vStar ∈ C012, nOf vStar h ∈ N' := by
  have := finite_NQ
  set φa := permActD c012Hyp p2A with hφa
  set φb := permActD c012Hyp p2B with hφb
  have hφa4 : φa ^ 4 = 1 := by rw [hφa, ← map_pow, p2A_pow_four, map_one]
  have hφb4 : φb ^ 4 = 1 := by rw [hφb, ← map_pow, p2B_pow_four, map_one]
  obtain ⟨n₁, hn₁, hn₁1, hn₁a⟩ :=
    exists_fixed_ne_one φa hφa4 (hinv p2A) (exists_card_two_pow N') hne
  let F : Subgroup NQ :=
    { carrier := {n | n ∈ N' ∧ φa n = n}
      mul_mem' := fun ha hb => ⟨N'.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨N'.one_mem, map_one φa⟩
      inv_mem' := fun ha => ⟨N'.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hab : ∀ n, φa (φb n) = φb (φa n) := fun n => by
    rw [hφa, hφb, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, p2A_mul_p2B]
  have hFinv : ∀ n ∈ F, φb n ∈ F := fun n hn => ⟨hinv p2B n hn.1, by rw [hab, hn.2]⟩
  have hFne : F ≠ ⊥ := fun e => by
    have h1 : n₁ ∈ F := ⟨hn₁, hn₁a⟩
    rw [e, Subgroup.mem_bot] at h1
    exact hn₁1 h1
  obtain ⟨n₂, ⟨hn₂N, hn₂a⟩, hn₂1, hn₂b⟩ :=
    exists_fixed_ne_one φb hφb4 hFinv (exists_card_two_pow F) hFne
  obtain ⟨c, rfl⟩ := exists_nOf n₂
  have ha := (fixed_iff (repPerm_p2Word wordA) (coeffMask_lt c) (coeffMask_mem c)).1 hn₂a
  have hb := (fixed_iff (repPerm_p2Word wordB) (coeffMask_lt c) (coeffMask_mem c)).1 hn₂b
  rcases fixedChecks c ha hb with h | h | h | h
  · exact absurd ((nOf_eq_nOf (coeffMask_mem c) (bvec_zero 24 ▸ C012.zero_mem) (Or.inl h)).trans
      (nOf_zero _)) hn₂1
  · exact absurd ((nOf_eq_nOf (coeffMask_mem c) (bvec_zero 24 ▸ C012.zero_mem)
      (Or.inr h)).trans (nOf_zero _)) hn₂1
  · have hv : bvec 24 vStar ∈ C012 := by
      have e : vStar = coeffMask c ^^^ (coeffMask c ^^^ vStar) := by
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e, h, Nat.xor_zero]
      exact coeffMask_mem c
    exact ⟨hv, (nOf_eq_nOf (coeffMask_mem c) hv (Or.inl h)) ▸ hn₂N⟩
  · have hv : bvec 24 vStar ∈ C012 := by
      have e : vStar = coeffMask c ^^^ (coeffMask c ^^^ vStar) := by
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e, h, bvec_xor, bvec_Ω]
      exact C012.add_mem (coeffMask_mem c) c012Hyp.Ω_mem
    exact ⟨hv, (nOf_eq_nOf (coeffMask_mem c) hv (Or.inr h)) ▸ hn₂N⟩

theorem nOf_congr {m m' : ℕ} (e : m = m') (h : bvec 24 m ∈ C012) (h' : bvec 24 m' ∈ C012) :
    nOf m h = nOf m' h' := by
  subst e
  rfl

theorem orbL_mem {N' : Subgroup NQ}
    (hinv : ∀ p : P2, ∀ n ∈ N', permActD c012Hyp p n ∈ N')
    (hv : ∃ h : bvec 24 vStar ∈ C012, nOf vStar h ∈ N') :
    ∀ j : ℕ, j < 21 → ∃ h : bvec 24 (orbL.getD j 0) ∈ C012, nOf (orbL.getD j 0) h ∈ N' := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [chainChecks.1]
      exact hv
    · obtain ⟨hpar, heq⟩ := chainChecks.2.1 ⟨j, hj⟩ hpos
      obtain ⟨h', hmem⟩ := ih _ hpar (hpar.trans hj)
      have hmem' := hinv (p2Gen (orbGen.getD j 0)) _ hmem
      rw [permActD_nOf (repPerm_gen _)] at hmem'
      have hmemC : bvec 24 (orbL.getD j 0) ∈ C012 := by
        rw [heq]
        exact permWordN_mem (repPerm_gen _) h'
      exact ⟨hmemC, (nOf_congr heq.symm _ hmemC) ▸ hmem'⟩

theorem xorL_mem_aux {N' : Subgroup NQ}
    (hL : ∀ j : ℕ, j < 21 → ∃ h : bvec 24 (orbL.getD j 0) ∈ C012, nOf (orbL.getD j 0) h ∈ N') :
    ∀ (l : List ℕ), (∀ j ∈ l, j < 21) → ∀ acc : ℕ, ∀ hacc : bvec 24 acc ∈ C012,
      nOf acc hacc ∈ N' →
      ∃ h : bvec 24 (l.foldl (fun m t => m ^^^ orbL.getD t 0) acc) ∈ C012,
        nOf (l.foldl (fun m t => m ^^^ orbL.getD t 0) acc) h ∈ N'
  | [], _, acc, hacc, hmem => ⟨hacc, hmem⟩
  | t :: l, hl, acc, hacc, hmem => by
    obtain ⟨ht, htmem⟩ := hL t (hl t (List.mem_cons_self ..))
    rw [List.foldl_cons]
    refine xorL_mem_aux hL l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ (bvec_xor_mem hacc ht)
      ?_
    rw [← nOf_mul hacc ht]
    exact N'.mul_mem hmem htmem

theorem signMask_mem (i : Fin 10) : bvec 24 (signMask i) ∈ C012 := by
  rw [← signVec_eq]
  exact signVec_mem i

theorem signMask_nOf_mem {N' : Subgroup NQ}
    (hinv : ∀ p : P2, ∀ n ∈ N', permActD c012Hyp p n ∈ N')
    (hv : ∃ h : bvec 24 vStar ∈ C012, nOf vStar h ∈ N') (i : Fin 10) :
    nOf (signMask i) (signMask_mem i) ∈ N' := by
  have hL := orbL_mem hinv hv
  have hz : bvec 24 0 ∈ C012 := bvec_zero 24 ▸ C012.zero_mem
  obtain ⟨h, hmem⟩ := xorL_mem_aux hL (orbTargets.getD i [])
    (fun j hj => chainChecks.2.2.2 i j hj) 0 hz
    ((nOf_zero hz).symm ▸ N'.one_mem)
  have e := nOf_eq_nOf (signMask_mem i) h (chainChecks.2.2.1 i)
  exact e ▸ hmem

theorem foldl_coeffStep_mem {N' : Subgroup NQ}
    (hs : ∀ i : Fin 10, nOf (signMask i) (signMask_mem i) ∈ N') (c : Fin 10 → ZMod 2) :
    ∀ (l : List (Fin 10)) (acc : ℕ) (hacc : bvec 24 acc ∈ C012), nOf acc hacc ∈ N' →
      ∃ h : bvec 24 (l.foldl (coeffStep c) acc) ∈ C012, nOf (l.foldl (coeffStep c) acc) h ∈ N'
  | [], acc, hacc, hmem => ⟨hacc, hmem⟩
  | i :: l, acc, hacc, hmem => by
    rw [List.foldl_cons]
    have hstep : ∃ h : bvec 24 (coeffStep c acc i) ∈ C012, nOf (coeffStep c acc i) h ∈ N' := by
      rw [coeffStep]
      split_ifs
      · refine ⟨bvec_xor_mem hacc (signMask_mem i), ?_⟩
        rw [← nOf_mul hacc (signMask_mem i)]
        exact N'.mul_mem hmem (hs i)
      · exact ⟨hacc, hmem⟩
    obtain ⟨h', hmem'⟩ := hstep
    exact foldl_coeffStep_mem hs c l _ h' hmem'

theorem eq_top_of_invariant {N' : Subgroup NQ}
    (hinv : ∀ p : P2, ∀ n ∈ N', permActD c012Hyp p n ∈ N') (hne : N' ≠ ⊥) : N' = ⊤ := by
  have hs := signMask_nOf_mem hinv (vStar_mem hinv hne)
  refine (Subgroup.eq_top_iff' N').2 fun n => ?_
  obtain ⟨c, rfl⟩ := exists_nOf n
  have hz : bvec 24 0 ∈ C012 := bvec_zero 24 ▸ C012.zero_mem
  obtain ⟨h, hmem⟩ := foldl_coeffStep_mem hs c (List.finRange 10) 0 hz
    ((nOf_zero hz).symm ▸ N'.one_mem)
  exact (nOf_congr rfl h (coeffMask_mem c)) ▸ hmem

end CFSG.Monster.B.GSide
