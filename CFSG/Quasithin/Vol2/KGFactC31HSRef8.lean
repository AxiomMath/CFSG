module

public import CFSG.Quasithin.Vol2.KGFactC31HSRef
public import CFSG.Quasithin.Vol2.KGFactC31E8

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.RankThree.Native CFSG.Assembly.LowTwoRank Matrix

@[expose] noncomputable def N8 : Subgroup G₀ := genOf n8GenW

theorem n8GenW_length : n8GenW.length = 2 := rfl
theorem n8Masks_length : n8Masks.length = 2 := rfl

theorem card_N8 :
    Nat.card N8 = 10752 := by
  rw [N8, card_genOf (Q := n8Chain) (certificate_originalSubgroup _ _ _ _ _) c_n8Check,
    c_n8Order]

theorem conj_n8 {j : ℕ}
    (hj : j < 2) (i : Fin 3) :
    elt (n8GenW.getD j []) * vU8 i * (elt (n8GenW.getD j []))⁻¹ =
      eElt vU8 fun r => matOf 3 n8Masks j r i :=
  conj_gen forall₂_u8 c_masks8 (by rw [n8GenW_length]; exact hj)
    (by rw [n8Masks_length]; exact hj) i

theorem N8_le_eNorm :
    N8 ≤ eNorm basis_u8 :=
  genOf_le fun j hj => mem_eNorm basis_u8 (matOf 3 n8Masks j) fun i =>
    conj_n8 (by rw [n8GenW_length] at hj; exact hj) i

theorem N8_eq :
    N8 = eNorm basis_u8 :=
  Subgroup.eq_of_le_of_card_ge N8_le_eNorm (by rw [card_N8]; exact card_eNorm_u8_le)

theorem N8_perfect :
    ⁅N8, N8⁆ = N8 := by
  refine le_antisymm (Subgroup.commutator_le_self _) (genOf_le fun j hj => ?_)
  have hj2 : j < 2 := by rw [n8GenW_length] at hj; exact hj
  have h1 := List.all_eq_true.mp c_n8Perf j (List.mem_range.mpr hj2)
  obtain ⟨u, hu, hue⟩ := evalCodes_mem n8GenW ((n8PerfW.getD j []).getD 0 [])
  obtain ⟨v, hv, hve⟩ := evalCodes_mem n8GenW ((n8PerfW.getD j []).getD 1 [])
  have heq := (tblEq_iff_eq (rep_elt _) (rep_toTable hn100 _)).mp h1
  have hg : elt (n8GenW.getD j []) = u * v * u⁻¹ * v⁻¹ := by
    apply Subtype.ext
    rw [heq, commOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hue, hve]
  rw [hg]
  exact Subgroup.commutator_mem_commutator hu hv

@[expose] noncomputable def Q8 : Subgroup G₀ := genOf qGenW

theorem qGenW_length : qGenW.length = 3 := rfl

theorem card_Q8 :
    Nat.card Q8 = 64 := by
  rw [Q8, card_genOf (Q := qChain) (certificate_originalSubgroup _ _ _ _ _) c_qCheck, c_qOrder]

@[expose] noncomputable def qg (i : Fin 3) : G₀ :=
  elt (qGenW.getD i [])

theorem qg_mem (i : Fin 3) : qg i ∈ Q8 := by
  rw [qg, List.getD_eq_getElem _ _ (by rw [qGenW_length]; exact i.2)]
  exact elt_mem_genOf (List.getElem_mem _)

theorem rep_qg (i : Fin 3) :
    Rep 100 (qT.getD i (idT 100)) ((qg i : G₀) : Equiv.Perm (Fin 100)) :=
  rep_getD_tabsOf qGenW i

theorem qg_comm (i j : Fin 3) :
    qg i * qg j = qg j * qg i := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp c_qComm i (List.mem_range.mpr i.2)) j
    (List.mem_range.mpr j.2)
  rw [commT] at h1
  exact Subtype.ext ((tblEq_iff_eq (Rep.compT (rep_qg i) (rep_qg j))
    (Rep.compT (rep_qg j) (rep_qg i))).mp h1)

theorem qg_mem_centralizer
    (i : Fin 3) : qg i ∈ Subgroup.centralizer (eSub basis_u8 : Set G₀) := by
  have h1 := List.all_eq_true.mp c_qCommU8 i (List.mem_range.mpr i.2)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (mem_eSub_iff basis_u8 y).mp hy
  have hall : ∀ k, vU8 k * qg i = qg i * vU8 k := by
    intro k
    have h2 := (all_iff_of_forall₂ forall₂_u8 (f := fun b => commT 100 (qT.getD i (idT 100)) b)
      (Q := fun g => ((qg i : G₀) : Equiv.Perm (Fin 100)) * g = g * (qg i : G₀))
      fun b g hb => by
        rw [commT]
        exact tblEq_iff_eq (Rep.compT (rep_qg i) hb) (Rep.compT hb (rep_qg i))).mp h1 k
    exact Subtype.ext h2.symm
  exact (commute_eElt (fun k => (hall k).symm) c).eq.symm

theorem qg_sq_mem (i : Fin 3) :
    qg i * qg i ∈ eSub basis_u8 := by
  have h1 := List.all_eq_true.mp c_qSq i (List.mem_range.mpr i.2)
  have hm := rep_maskProd hn100 _ u8T forall₂_u8 (qSq.getD i 0)
  have heq := (tblEq_iff_eq (Rep.compT (rep_qg i) (rep_qg i)) hm).mp h1
  have : qg i * qg i = eElt vU8 (maskVec 3 (qSq.getD i 0)) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, heq]
    exact (map_eElt (v := vU8) hs100P.subtype _).symm
  rw [this]
  exact eElt_mem basis_u8 _

theorem qg_pow_four (i : Fin 3) :
    qg i ^ 4 = 1 := by
  have h := eSub_sq basis_u8 _ (qg_sq_mem i)
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  exact h

theorem tri_comm {G : Type*} [Group G] {A A' B B' C C' : G} (h1 : A' * B = B * A')
    (h2 : A' * C = C * A') (h3 : B' * C = C * B') :
    A * A' * (B * B') * (C * C') = A * B * C * (A' * B' * C') := by
  calc A * A' * (B * B') * (C * C') = A * (A' * B) * (B' * C) * C' := by simp only [mul_assoc]
    _ = A * (B * A') * (C * B') * C' := by rw [h1, h3]
    _ = A * B * (A' * C) * B' * C' := by simp only [mul_assoc]
    _ = A * B * (C * A') * B' * C' := by rw [h2]
    _ = A * B * C * (A' * B' * C') := by simp only [mul_assoc]

@[expose] noncomputable def q8Fun
    (c : Multiplicative (Fin 3 → ZMod 4)) : G₀ :=
  qg 0 ^ (Multiplicative.toAdd c 0).val * qg 1 ^ (Multiplicative.toAdd c 1).val *
    qg 2 ^ (Multiplicative.toAdd c 2).val

theorem pow_val_add (i : Fin 3)
    (a b : ZMod 4) : qg i ^ (a + b).val = qg i ^ a.val * qg i ^ b.val := by
  rw [← pow_add, ZMod.val_add, pow_mod_of_pow_eq_one (qg_pow_four i)]

@[expose] noncomputable def q8Hom :
    Multiplicative (Fin 3 → ZMod 4) →* G₀ where
  toFun := q8Fun
  map_one' := by simp [q8Fun]
  map_mul' c d := by
    simp only [q8Fun, toAdd_mul, Pi.add_apply, pow_val_add]
    exact tri_comm ((Commute.pow_pow (qg_comm 0 1 : Commute (qg 0) (qg 1)) _ _).eq)
      ((Commute.pow_pow (qg_comm 0 2 : Commute (qg 0) (qg 2)) _ _).eq)
      ((Commute.pow_pow (qg_comm 1 2 : Commute (qg 1) (qg 2)) _ _).eq)

theorem q8Hom_single (i : Fin 3) :
    q8Hom (Multiplicative.ofAdd (Pi.single i 1)) = qg i := by
  show q8Fun _ = _
  have h1 : (1 : ZMod 4).val = 1 := rfl
  fin_cases i <;> simp [q8Fun, h1]

theorem range_q8Hom :
    q8Hom.range = Q8 := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    show q8Fun c ∈ Q8
    exact Q8.mul_mem (Q8.mul_mem (Q8.pow_mem (qg_mem 0) _) (Q8.pow_mem (qg_mem 1) _))
      (Q8.pow_mem (qg_mem 2) _)
  · rw [Q8, genOf, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
    have hj3 : j < 3 := by rw [qGenW_length] at hj; exact hj
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨j, hj3⟩ 1), ?_⟩
    rw [q8Hom_single, qg, List.getD_eq_getElem _ _ hj]

theorem card_zmod4cube : Nat.card (Multiplicative (Fin 3 → ZMod 4)) = 64 := by
  rw [Nat.card_eq_fintype_card]
  simp

@[expose] noncomputable def q8HomQ :
    Multiplicative (Fin 3 → ZMod 4) →* ↥Q8 :=
  q8Hom.codRestrict Q8 fun c => range_q8Hom ▸ ⟨c, rfl⟩

theorem q8HomQ_bijective :
    Function.Bijective q8HomQ := by
  have hsurj : Function.Surjective q8HomQ := by
    rintro ⟨q, hq⟩
    rw [← range_q8Hom] at hq
    obtain ⟨c, rfl⟩ := hq
    exact ⟨c, rfl⟩
  have := Fintype.ofFinite ↥Q8
  exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_zmod4cube, card_Q8]⟩

@[expose] noncomputable def q8Equiv :
    Multiplicative (Fin 3 → ZMod 4) ≃* ↥Q8 :=
  MulEquiv.ofBijective q8HomQ q8HomQ_bijective

theorem Q8_comm :
    ∀ a ∈ Q8, ∀ b ∈ Q8, a * b = b * a := by
  intro a ha b hb
  rw [← range_q8Hom] at ha hb
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem cent_u8_eq :
    Subgroup.centralizer (eSub basis_u8 : Set G₀) = Q8 := by
  have hle : Q8 ≤ Subgroup.centralizer (eSub basis_u8 : Set G₀) := by
    rw [Q8, genOf, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
    have hj3 : j < 3 := by rw [qGenW_length] at hj; exact hj
    have := qg_mem_centralizer ⟨j, hj3⟩
    rwa [qg, List.getD_eq_getElem _ _ hj] at this
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_cent_u8, card_Q8])).symm

theorem mem_u8_of_sq {q : G₀}
    (hq : q ∈ Q8) (hq2 : q * q = 1) : q ∈ eSub basis_u8 := by
  rw [← range_q8Hom] at hq
  obtain ⟨c, rfl⟩ := hq
  have hinj : Function.Injective q8Hom := fun c d h =>
    q8HomQ_bijective.1 (Subtype.ext h)
  have hc2 : c * c = 1 := hinj (by rw [map_mul, hq2, map_one])
  have hci : ∀ i, (Multiplicative.toAdd c i = 0 ∨ Multiplicative.toAdd c i = 2) := by
    intro i
    have h1 := congrArg (fun x : Multiplicative (Fin 3 → ZMod 4) => Multiplicative.toAdd x i) hc2
    simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply] at h1
    generalize Multiplicative.toAdd c i = a at h1 ⊢
    revert a
    decide
  have hpow : ∀ i : Fin 3, qg i ^ (Multiplicative.toAdd c i).val ∈ eSub basis_u8 := by
    intro i
    rcases hci i with h | h
    · rw [h, ZMod.val_zero, pow_zero]; exact (eSub basis_u8).one_mem
    · rw [h, show (2 : ZMod 4).val = 2 from rfl, sq]; exact qg_sq_mem i
  show q8Fun c ∈ eSub basis_u8
  exact (eSub basis_u8).mul_mem ((eSub basis_u8).mul_mem (hpow 0) (hpow 1)) (hpow 2)

@[expose] noncomputable def n8Hom :
    ↥N8 →* ↥(StatedSL 3 (ZMod 2)) :=
  E8.e3Hom basis_u8 N8_le_eNorm

theorem Q8_le_N8 :
    Q8 ≤ N8 := by
  rw [N8_eq, ← cent_u8_eq]
  intro r hr
  exact mem_eNorm basis_u8 1 fun i => by
    rw [eElt_one_col]
    have := Subgroup.mem_centralizer_iff.mp hr (vU8 i) (mem_eSub basis_u8 i)
    rw [← this, mul_inv_cancel_right]

theorem ker_n8Hom :
    n8Hom.ker = Q8.subgroupOf N8 := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, n8Hom, E8.e3Hom_eq_one_iff, cent_u8_eq]

theorem n8Hom_surjective :
    Function.Surjective n8Hom := by
  have h1 := card_range_eq Q8_le_N8 n8Hom ker_n8Hom
  rw [card_Q8, card_N8] at h1
  have h2 : Nat.card n8Hom.range = Nat.card ↥(StatedSL 3 (ZMod 2)) := by
    rw [E8.card_statedSL3]; omega
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ h2

end CFSG.Quasithin.KGC31.HS

end
