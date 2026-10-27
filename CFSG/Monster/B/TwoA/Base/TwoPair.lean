module

public import CFSG.Monster.B.TwoA.Base.PairStab
public import CFSG.Monster.B.TwoA.Base.CodeCheck
public import CFSG.Monster.B.TwoA.Base.GroupAux
public import CFSG.Monster.Code.LatticeCount

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code MulAction

open scoped Pointwise

theorem pair_eq_pair_iff {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    ({a, b} : Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c, d} : Finset α) := h ▸ Finset.mem_insert_self a {b}
    have hb : b ∈ ({c, d} : Finset α) := h ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self b)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
    · exact absurd rfl hab
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm a b

@[expose] def pair23 : Set.powersetCard (Fin 24) 2 := CFSG.Sporadic.Mathieu.duad 2 3 (by decide)

@[expose] def Ftwo : Subgroup AutPerm := Ppair ⊓ MulAction.stabilizer AutPerm pair23

theorem mem_stabilizer_pair23_iff (p : AutPerm) :
    p ∈ MulAction.stabilizer AutPerm pair23 ↔
      ((p : Equiv.Perm (Fin 24)) 2 = 2 ∧ (p : Equiv.Perm (Fin 24)) 3 = 3) ∨
        ((p : Equiv.Perm (Fin 24)) 2 = 3 ∧ (p : Equiv.Perm (Fin 24)) 3 = 2) := by
  rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
  change p • ((pair23 : Set.powersetCard (Fin 24) 2) : Finset (Fin 24)) = _ ↔ _
  rw [pair23, CFSG.Sporadic.Mathieu.duad_val, Finset.smul_finset_insert,
    Finset.smul_finset_singleton]
  exact pair_eq_pair_iff ((p : Equiv.Perm (Fin 24)).injective.ne (by decide)) (by decide)

theorem mem_Ftwo_iff (p : AutPerm) :
    p ∈ Ftwo ↔ p ∈ Ppair ∧ (((p : Equiv.Perm (Fin 24)) 2 = 2 ∧ (p : Equiv.Perm (Fin 24)) 3 = 3) ∨
        ((p : Equiv.Perm (Fin 24)) 2 = 3 ∧ (p : Equiv.Perm (Fin 24)) 3 = 2)) := by
  rw [Ftwo, Subgroup.mem_inf, mem_stabilizer_pair23_iff]

theorem Ftwo_apply_lt {p : AutPerm} (hp : p ∈ Ftwo) {i : Fin 24} (hi : (i : ℕ) < 4) :
    ((p : Equiv.Perm (Fin 24)) i : ℕ) < 4 := by
  obtain ⟨h01, h23⟩ := (mem_Ftwo_iff p).1 hp
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
    (by decide : ∀ i : Fin 24, (i : ℕ) < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i hi
  rcases (mem_Ppair_iff p).1 h01 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;>
    rcases h23 with ⟨e2, e3⟩ | ⟨e2, e3⟩ <;>
    rcases hcases with rfl | rfl | rfl | rfl <;> simp_all

theorem Ftwo_apply_ge {p : AutPerm} (hp : p ∈ Ftwo) {i : Fin 24} (hi : 4 ≤ (i : ℕ)) :
    4 ≤ ((p : Equiv.Perm (Fin 24)) i : ℕ) := by
  by_contra h
  push Not at h
  have hp' : p⁻¹ ∈ Ftwo := Ftwo.inv_mem hp
  have := Ftwo_apply_lt hp' h
  have e : ((p⁻¹ : AutPerm) : Equiv.Perm (Fin 24)) ((p : Equiv.Perm (Fin 24)) i) = i :=
    Equiv.symm_apply_apply _ _
  rw [e] at this
  omega

attribute [local instance] restAction

@[expose] def rest23 : Set.powersetCard Rest 2 :=
  ⟨{⟨2, by decide⟩, ⟨3, by decide⟩}, Set.powersetCard.mem_iff.2 (Finset.card_pair (by decide))⟩

theorem natCard_rest_duads : Nat.card (Set.powersetCard Rest 2) = 231 := by
  rw [Set.powersetCard.card, natCard_rest]
  rfl

instance isPretransitive_rest_duads :
    MulAction.IsPretransitive Ppair (Set.powersetCard Rest 2) :=
  Set.powersetCard.isPretransitive_of_isMultiplyPretransitive Ppair isMultiplyPretransitive_rest

theorem natCard_stabilizer_rest23 :
    Nat.card (MulAction.stabilizer Ppair rest23) = 3840 := by
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer Ppair rest23)
  rw [MulAction.index_stabilizer_of_transitive, natCard_rest_duads, natCard_Ppair] at h1
  omega

theorem mem_stabilizer_rest23_iff (p : Ppair) :
    p ∈ MulAction.stabilizer Ppair rest23 ↔ (p : AutPerm) ∈ Ftwo := by
  rw [mem_Ftwo_iff, MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
  change p • (({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset Rest)) =
    ({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset Rest) ↔ _
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]
  rw [pair_eq_pair_iff (α := Rest) (fun h => absurd (congrArg Subtype.val
    ((MulAction.injective p) h)) (by decide)) (by decide)]
  simp only [Subtype.ext_iff, coe_smul_rest]
  exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩

theorem map_stabilizer_rest23 : (MulAction.stabilizer Ppair rest23).map Ppair.subtype = Ftwo := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_stabilizer_rest23_iff q).1 hq
  · intro hp
    exact ⟨⟨p, ((mem_Ftwo_iff p).1 hp).1⟩, (mem_stabilizer_rest23_iff _).2 hp, rfl⟩

theorem natCard_Ftwo : Nat.card Ftwo = 3840 := by
  rw [← map_stabilizer_rest23, ← Nat.card_congr ((MulAction.stabilizer Ppair
    rest23).equivMapOfInjective Ppair.subtype Subtype.val_injective).toEquiv,
    natCard_stabilizer_rest23]

@[expose] def tetMask (k : ℕ) : ℕ := 15 ||| (15 <<< (4 * (k + 1)))

@[expose] def tetOct (k : Fin 5) : Fin 24 → ZMod 2 := bvec 24 (tetMask k)

@[expose] def tetrad (k : Fin 5) : Finset (Fin 24) :=
  Finset.univ.filter fun i => i.val / 4 = (k : ℕ) + 1

theorem tetOct_mem : ∀ k : Fin 5, tetOct k ∈ C := by decide +kernel

theorem hammingNorm_tetOct : ∀ k : Fin 5, hammingNorm (tetOct k) = 8 := by
  intro k
  rw [tetOct, hammingNorm_bvec]
  revert k
  decide

theorem tetOct_apply : ∀ (k : Fin 5) (i : Fin 24),
    tetOct k i = if (i : ℕ) < 4 ∨ i ∈ tetrad k then 1 else 0 := by decide

theorem tetOct_injective : Function.Injective tetOct := by decide

@[expose] def tetCheck (a : ℕ) : Bool :=
  if popc 24 a = 8 ∧ a.testBit 0 = true ∧ a.testBit 1 = true ∧ a.testBit 2 = true ∧
    a.testBit 3 = true then
    a == tetMask 0 || a == tetMask 1 || a == tetMask 2 || a == tetMask 3 || a == tetMask 4
  else true

theorem tetCount : treeSumN (fun a => if tetCheck a then 0 else 1) Bmask 12 0 = 0 := by
  decide +kernel

theorem bvec_apply_one {a : ℕ} {i : Fin 24} (h : bvec 24 a i = 1) : a.testBit i = true := by
  rw [bvec_apply] at h
  by_contra h'
  rw [ite_eq_right h'] at h
  exact absurd h (by decide)

theorem eq_tetOct_of_mem_C {x : Fin 24 → ZMod 2} (hx : x ∈ C) (h8 : hammingNorm x = 8)
    (h0 : x 0 = 1) (h1 : x 1 = 1) (h2 : x 2 = 1) (h3 : x 3 = 1) : ∃ k, x = tetOct k := by
  refine forall_mem_C_of_count (P := fun x => hammingNorm x = 8 → x 0 = 1 → x 1 = 1 →
    x 2 = 1 → x 3 = 1 → ∃ k, x = tetOct k) tetCheck (fun a ha hw e0 e1 e2 e3 => ?_) tetCount hx
    h8 h0 h1 h2 h3
  rw [hammingNorm_bvec] at hw
  have b0 := bvec_apply_one e0
  have b1 := bvec_apply_one e1
  have b2 := bvec_apply_one e2
  have b3 := bvec_apply_one e3
  rw [tetCheck, ite_eq_left ⟨hw, b0, b1, b2, b3⟩] at ha
  simp only [Bool.or_eq_true, beq_iff_eq] at ha
  rcases ha with (((h | h) | h) | h) | h <;> subst h
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem suppFin_tetOct : ∀ k : Fin 5,
    suppFin (tetOct k) = {0, 1, 2, 3} ∪ tetrad k := by decide

theorem tetrads_eq (S : Finset (Fin 24)) :
    (∃ d ∈ C, hammingNorm d = 8 ∧ ({0, 1, 2, 3} : Finset (Fin 24)) ⊆ suppFin d ∧
      S = suppFin d \ {0, 1, 2, 3}) ↔ ∃ k, S = tetrad k := by
  have hsub : ∀ k : Fin 5, ({0, 1, 2, 3} : Finset (Fin 24)) ⊆ suppFin (tetOct k) := by decide
  have hdiff : ∀ k : Fin 5, suppFin (tetOct k) \ {0, 1, 2, 3} = tetrad k := by decide
  constructor
  · rintro ⟨d, hd, h8, h4, rfl⟩
    have hi : ∀ i : Fin 24, i ∈ ({0, 1, 2, 3} : Finset (Fin 24)) → d i = 1 := by
      intro i hi
      have := mem_suppFin.1 (h4 hi)
      have hc : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      exact hc _ this
    obtain ⟨k, rfl⟩ := eq_tetOct_of_mem_C hd h8 (hi 0 (by decide)) (hi 1 (by decide))
      (hi 2 (by decide)) (hi 3 (by decide))
    exact ⟨k, hdiff k⟩
  · rintro ⟨k, rfl⟩
    exact ⟨tetOct k, tetOct_mem k, hammingNorm_tetOct k, hsub k, (hdiff k).symm⟩

theorem permWord_tetOct_mem {p : AutPerm} (hp : p ∈ Ftwo) (k : Fin 5) :
    ∃ k', permWord p (tetOct k) = tetOct k' := by
  have hmem := permWord_mem_of_mem_AutPerm p.2 (tetOct_mem k)
  have h8 : hammingNorm (permWord p (tetOct k)) = 8 := by
    rw [permWord, hammingNorm_comp_perm, hammingNorm_tetOct]
  have hone : ∀ i : Fin 24, (i : ℕ) < 4 → permWord p (tetOct k) i = 1 := by
    intro i hi
    rw [permWord, Function.comp_apply, tetOct_apply,
      ite_eq_left (.inl (Ftwo_apply_lt (Ftwo.inv_mem hp) hi))]
  exact eq_tetOct_of_mem_C hmem h8 (hone 0 (by decide)) (hone 1 (by decide)) (hone 2 (by decide))
    (hone 3 (by decide))

@[expose] def tetIdx (p : AutPerm) (k : Fin 5) : Fin 5 :=
  ⟨((p : Equiv.Perm (Fin 24)) ⟨4 * ((k : ℕ) + 1), by have := k.isLt; omega⟩ : ℕ) / 4 - 1, by
    have := ((p : Equiv.Perm (Fin 24)) ⟨4 * ((k : ℕ) + 1), by have := k.isLt; omega⟩).isLt
    omega⟩

theorem tetrad_of_tetOct : ∀ (k : Fin 5) (i : Fin 24), 4 ≤ (i : ℕ) → tetOct k i = 1 →
    (i : ℕ) / 4 - 1 = k := by decide

theorem permWord_tetOct {p : AutPerm} (hp : p ∈ Ftwo) (k : Fin 5) :
    permWord p (tetOct k) = tetOct (tetIdx p k) := by
  obtain ⟨k', hk'⟩ := permWord_tetOct_mem hp k
  rw [hk']
  congr 1
  apply Fin.ext
  have hk5 := k.isLt
  have h1 : tetOct k' ((p : Equiv.Perm (Fin 24)) ⟨4 * ((k : ℕ) + 1), by omega⟩) = 1 := by
    rw [← hk', permWord_apply, tetOct_apply, ite_eq_left (.inr (by simp [tetrad]))]
  have h2 := Ftwo_apply_ge hp (i := ⟨4 * ((k : ℕ) + 1), by omega⟩) (by simp)
  have := tetrad_of_tetOct k' _ h2 h1
  rw [tetIdx]
  exact this.symm

theorem tetIdx_unique {p : AutPerm} (hp : p ∈ Ftwo) {k k' : Fin 5}
    (h : permWord p (tetOct k) = tetOct k') : tetIdx p k = k' :=
  tetOct_injective ((permWord_tetOct hp k).symm.trans h)

theorem tetIdx_mul {p q : AutPerm} (hp : p ∈ Ftwo) (hq : q ∈ Ftwo) (k : Fin 5) :
    tetIdx (p * q) k = tetIdx p (tetIdx q k) := by
  apply tetIdx_unique (Ftwo.mul_mem hp hq)
  rw [show ((p * q : AutPerm) : Equiv.Perm (Fin 24)) = (p : Equiv.Perm (Fin 24)) * q from rfl,
    permWord_mul, permWord_tetOct hq, permWord_tetOct hp]

theorem tetIdx_one (k : Fin 5) : tetIdx 1 k = k := by
  apply tetIdx_unique Ftwo.one_mem
  funext i
  simp [permWord]

@[expose] def alpha : Ftwo →* Equiv.Perm (Fin 5) where
  toFun p :=
    { toFun := tetIdx p
      invFun := tetIdx (p⁻¹ : Ftwo)
      left_inv k := by
        rw [← tetIdx_mul (p⁻¹).2 p.2, show ((p⁻¹ : Ftwo) : AutPerm) * (p : AutPerm) = 1 from by
          rw [Subgroup.coe_inv, inv_mul_cancel], tetIdx_one]
      right_inv k := by
        rw [← tetIdx_mul p.2 (p⁻¹).2, show (p : AutPerm) * ((p⁻¹ : Ftwo) : AutPerm) = 1 from by
          rw [Subgroup.coe_inv, mul_inv_cancel], tetIdx_one] }
  map_one' := Equiv.ext fun k => tetIdx_one k
  map_mul' p q := Equiv.ext fun k => tetIdx_mul p.2 q.2 k

theorem alpha_apply (p : Ftwo) (k : Fin 5) : alpha p k = tetIdx p k := rfl

theorem mem_tetrad_iff (p : Ftwo) (k : Fin 5) (i : Fin 24) :
    i ∈ tetrad k ↔ ((p : AutPerm) : Equiv.Perm (Fin 24)) i ∈ tetrad (alpha p k) := by
  rw [alpha_apply]
  have h := congrFun (permWord_tetOct p.2 k) (((p : AutPerm) : Equiv.Perm (Fin 24)) i)
  rw [permWord_apply, tetOct_apply, tetOct_apply] at h
  have hlt : (i : ℕ) < 4 ↔ (((p : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) < 4 :=
    ⟨Ftwo_apply_lt p.2, fun h' => by
      by_contra h''
      have := Ftwo_apply_ge p.2 (not_lt.1 h'')
      omega⟩
  have hdisj : ∀ (k : Fin 5) (j : Fin 24), j ∈ tetrad k → ¬ (j : ℕ) < 4 := by decide
  by_cases hi : (i : ℕ) < 4
  · have hp := hlt.1 hi
    exact ⟨fun h' => absurd hi (hdisj _ _ h'), fun h' => absurd hp (hdisj _ _ h')⟩
  · have hp : ¬ (((p : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) < 4 := fun h' => hi (hlt.2 h')
    simp only [hi, hp, false_or] at h
    constructor
    · intro hm
      rw [ite_eq_left hm] at h
      by_contra hm'
      rw [ite_eq_right hm'] at h
      exact absurd h (by decide)
    · intro hm
      rw [ite_eq_left hm] at h
      by_contra hm'
      rw [ite_eq_right hm'] at h
      exact absurd h (by decide)

@[expose] def pF : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 8, 9, 10, 11, 16, 18, 19, 17, 20, 23, 21, 22, 12, 13, 14, 15, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 20, 21, 22, 23, 4, 5, 6, 7, 16, 17, 18, 19, 8, 11, 9, 10, 12, 14, 15, 13]
  left_inv := by decide
  right_inv := by decide

@[expose] def qF : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 15, 14, 20, 21, 23, 22, 16, 17, 19, 18]
  invFun := ![0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 15, 14, 20, 21, 23, 22, 16, 17, 19, 18]
  left_inv := by decide
  right_inv := by decide

theorem pF_mem : pF ∈ AutPerm :=
  mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem qF_mem : qF ∈ AutPerm :=
  mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem permWord_pF_B : (List.finRange 12).map (fun j => permWord pF (B j)) =
    [1, 4, 16, 32, 8, 2, 576, 896, 1792, 2304, 256, 512].map coeffWord := by decide +kernel

theorem permWord_qF_B : (List.finRange 12).map (fun j => permWord qF (B j)) =
    [1, 2, 4, 8, 32, 16, 64, 192, 256, 768, 1024, 3072].map coeffWord := by decide +kernel

theorem pF_mem_Ftwo : (⟨pF, pF_mem⟩ : AutPerm) ∈ Ftwo :=
  (mem_Ftwo_iff _).2 ⟨mem_Ppair_of_fix _ rfl rfl, .inl ⟨rfl, rfl⟩⟩

theorem qF_mem_Ftwo : (⟨qF, qF_mem⟩ : AutPerm) ∈ Ftwo :=
  (mem_Ftwo_iff _).2 ⟨mem_Ppair_of_fix _ rfl rfl, .inr ⟨rfl, rfl⟩⟩

@[expose] def sigma5 : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 3, 2, 4]

@[expose] def tau5 : Equiv.Perm (Fin 5) := Equiv.swap 3 4

theorem alpha_pF : alpha ⟨⟨pF, pF_mem⟩, pF_mem_Ftwo⟩ = sigma5 := by
  ext k
  rw [alpha_apply]
  refine congrArg Fin.val (tetIdx_unique pF_mem_Ftwo ?_)
  revert k
  decide

theorem alpha_qF : alpha ⟨⟨qF, qF_mem⟩, qF_mem_Ftwo⟩ = tau5 := by
  ext k
  rw [alpha_apply]
  refine congrArg Fin.val (tetIdx_unique qF_mem_Ftwo ?_)
  revert k
  decide

theorem closure_sigma5_tau5 : Subgroup.closure ({sigma5, tau5} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  have hnd : ([0, 1, 3, 2, 4] : List (Fin 5)).Nodup := by decide
  refine Equiv.Perm.closure_prime_cycle_swap (by decide) (List.isCycle_formPerm hnd (by decide))
    ?_ ⟨3, 4, by decide, rfl⟩
  rw [sigma5, List.support_formPerm_of_nodup _ hnd (by decide)]
  decide

theorem alpha_surjective : Function.Surjective alpha := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_sigma5_tau5, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨_, alpha_pF⟩
  · exact ⟨_, alpha_qF⟩

theorem natCard_ker_alpha : Nat.card alpha.ker = 32 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup alpha.ker
  have h2 : Nat.card (Ftwo ⧸ alpha.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective alpha alpha_surjective).toEquiv,
      Nat.card_perm, Nat.card_fin]
    rfl
  rw [h2, natCard_Ftwo] at h1
  omega

theorem eq_bot_of_normal_twoGroup' {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] (hprim : MulAction.IsPreprimitive G X) (hX : ∀ j, Nat.card X ≠ 2 ^ j)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  rw [one_smul]
  have hB := MulAction.IsBlock.orbit_of_normal (G := G) (N := N) x
  rcases hprim.isTrivialBlock_of_isBlock hB with hsub | huniv
  · exact hsub (MulAction.mem_orbit x (⟨n, hn⟩ : N)) (MulAction.mem_orbit_self x)
  · exfalso
    have hcard : (MulAction.orbit N x).ncard = Nat.card X := by
      rw [huniv, Set.ncard_univ]
    have hdvd : (MulAction.orbit N x).ncard ∣ Nat.card N := by
      rw [← MulAction.index_stabilizer N x]
      exact Subgroup.index_dvd_card _
    rw [hcard] at hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact hX j hj

theorem pCore_perm_five : CFSG.pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  have h2 := Equiv.Perm.isMultiplyPretransitive (Fin 5) 2
  refine eq_bot_of_normal_twoGroup' (MulAction.isPreprimitive_of_is_two_pretransitive h2)
    (fun j hj => ?_) CFSG.pCore_isPGroup
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hj
  have : j < 3 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
    omega
  interval_cases j <;> norm_num at hj

theorem ker_alpha : alpha.ker = CFSG.pCore 2 Ftwo := by
  apply le_antisymm
  · refine le_pCore_of_normal alpha.normal_ker ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 5) (by rw [natCard_ker_alpha]; norm_num)
  · have hmap : (CFSG.pCore 2 Ftwo).map alpha = ⊥ := by
      have hn : ((CFSG.pCore 2 Ftwo).map alpha).Normal :=
        Subgroup.Normal.map CFSG.pCore_normal alpha alpha_surjective
      have hp : IsPGroup 2 ((CFSG.pCore 2 Ftwo).map alpha) :=
        CFSG.pCore_isPGroup.map alpha
      exact eq_bot_iff.2 ((le_pCore_of_normal hn hp).trans pCore_perm_five.le)
    rw [← Subgroup.map_eq_bot_iff]
    exact hmap

theorem natCard_pCore_Ftwo : Nat.card (CFSG.pCore 2 Ftwo) = 32 := by
  rw [← ker_alpha, natCard_ker_alpha]

@[expose] noncomputable def quotPCoreEquiv :
    Ftwo ⧸ CFSG.pCore 2 Ftwo ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq ker_alpha.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective alpha alpha_surjective)

theorem native_two_pair_stabilizer_five_tetrad_quotient :
    (∀ S : Finset (Fin 24), (∃ d ∈ C, hammingNorm d = 8 ∧
      ({0, 1, 2, 3} : Finset (Fin 24)) ⊆ suppFin d ∧ S = suppFin d \ {0, 1, 2, 3}) ↔
      ∃ k, S = tetrad k) ∧
    (∀ (p : Ftwo) (k : Fin 5) (i : Fin 24),
      i ∈ tetrad k ↔ ((p : AutPerm) : Equiv.Perm (Fin 24)) i ∈ tetrad (alpha p k)) ∧
    Function.Surjective alpha ∧ Nat.card Ftwo = 3840 ∧ alpha.ker = CFSG.pCore 2 Ftwo ∧
    Nat.card (CFSG.pCore 2 Ftwo) = 32 ∧
    Nonempty (Ftwo ⧸ CFSG.pCore 2 Ftwo ≃* Equiv.Perm (Fin 5)) :=
  ⟨tetrads_eq, mem_tetrad_iff, alpha_surjective, natCard_Ftwo, ker_alpha, natCard_pCore_Ftwo,
    ⟨quotPCoreEquiv⟩⟩

end CFSG.Monster.B.TwoA
