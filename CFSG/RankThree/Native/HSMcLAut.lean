module

public import CFSG.RankThree.Native.HSMcLOuter

public section

namespace CFSG.RankThree.Native

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.OuterAutomorphisms

theorem automorphism_model_of {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}
    {U : Equiv.Perm (Fin n)} (hR : P ⊔ zpowers U = R) (hU2 : U ^ 2 = 1) (hUP : U ∉ P)
    (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P) (hC : centralizer (P : Set (Equiv.Perm (Fin n))) = ⊥)
    (hout : Nat.card (Outer P) ≤ 2) :
    U ≠ 1 ∧ P.map (MulAut.conj U).toMonoidHom = P ∧
      (∃ e : R ≃* MulAut P,
        (∀ (x : R) (p : P),
          ((e x p : P) : Equiv.Perm (Fin n)) = x * p * (x : Equiv.Perm (Fin n))⁻¹) ∧
        (P.subgroupOf R).map e.toMonoidHom = inner P) ∧
      (P.subgroupOf R).Normal ∧ P ⊓ zpowers U = ⊥ ∧ (P.subgroupOf R).index = 2 ∧
      Nonempty (Outer P ≃* Multiplicative (ZMod 2)) ∧ Nat.card R = 2 * Nat.card P := by
  subst hR
  obtain ⟨hmap, -, hinf, hnormal, hcard, -⟩ := normalizing_model hU2 hUP hUn hC
  obtain ⟨e, he, himage, hout2, -⟩ := full_automorphism_model hU2 hUP hUn hC hout
  have hPle : P ≤ P ⊔ zpowers U := le_sup_left
  have hindex : (P.subgroupOf (P ⊔ zpowers U)).index = 2 := by
    have h := (P.subgroupOf (P ⊔ zpowers U)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPle).toEquiv, hcard] at h
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [mul_comm 2] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  refine ⟨fun h => hUP (h ▸ P.one_mem), hmap, ⟨e, he, himage⟩, hnormal, hinf, hindex, hout2,
    hcard⟩

theorem hs100RChainArrays :
    ChainArrays hs100RChain (hs100RArrs.extract 0 3) hs100RArrs hs100RBaseArr hs100RWords :=
  chainArrays_ofArrays (chainCheckFacts hs100R_chain_check.1).strong_inv

theorem rep_hs100RArr {j : ℕ} (hj : j < 17) :
    Rep 100 hs100RArrs[j]! (permOfArr 100 hs100RArrs[j]!) := by
  have h := (chainCheckFacts hs100R_chain_check.1).strong_inv j (by simp [hs100RArrs]; omega)
  exact (rep_permOfArr h).1

theorem rep_hs100U : Rep 100 (hs100Arr 15) hs100U := (rep_permOfArr hs100_chain_check.2.2.2.1).1

theorem hs100RChain_original_get (k : Fin hs100RChain.originalCount) :
    hs100RChain.original.get k = permOfArr 100 hs100RArrs[(k : ℕ)]! :=
  RawSchreierDatum.ofArrays_original_get k

theorem hs100RChain_original : hs100RChain.original.toList = [hs100A, hs100B, hs100U] := by
  apply List.ext_getElem (by simp [hs100RChain, RawSchreierDatum.ofArrays])
  intro k h1 _
  have hk : k < hs100RChain.originalCount := by simpa using h1
  rw [Vector.getElem_toList]
  have := hs100RChain_original_get ⟨k, hk⟩
  rw [Vector.get] at this
  simp only [Fin.cast_mk] at this
  rw [show hs100RChain.original[k] = hs100RChain.original.toArray[k]'(by simpa using hk) from rfl,
    this]
  have hk3 : k < 3 := hk
  interval_cases k
  · exact eq_of_eqA (rep_hs100RArr (by norm_num)) rep_hs100A hs100R_chain_check.2.2.1
  · exact eq_of_eqA (rep_hs100RArr (by norm_num)) rep_hs100B hs100R_chain_check.2.2.2.1
  · exact eq_of_eqA (rep_hs100RArr (by norm_num)) rep_hs100U hs100R_chain_check.2.2.2.2

theorem hs100R_eq_original : hs100R = hs100RChain.originalSubgroup := by
  rw [hs100R, RawSchreierDatum.originalSubgroup, hs100RChain_original]
  congr 1
  ext g
  simp

theorem card_hs100R : Nat.card hs100R = 88704000 := by
  rw [hs100R_eq_original, card_originalSubgroup_of_chainOK hs100RChainArrays (by norm_num)
    hs100R_chain_check.1, hs100R_chain_check.2.1]
  rfl

theorem hs100R_eq_sup : hs100P ⊔ zpowers hs100U = hs100R := by
  rw [hs100P, hs100R, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

theorem hs100P_le_R : hs100P ≤ hs100R := hs100R_eq_sup ▸ le_sup_left

theorem hs100U_mem_R : hs100U ∈ hs100R := hs100R_eq_sup ▸ mem_sup_right (mem_zpowers _)

theorem hs100U_not_mem_P : hs100U ∉ hs100P := by
  intro hu
  have hle : hs100R ≤ hs100P := by
    rw [← hs100R_eq_sup]
    exact sup_le le_rfl (zpowers_le.2 hu)
  have := Subgroup.card_le_of_le hle
  rw [card_hs100R, card_hs100P] at this
  norm_num at this

theorem hs100U_sq : hs100U ^ 2 = 1 := by
  rw [sq]
  exact eq_of_eqA (rep_compA rep_hs100U rep_hs100U) rep_idA hs100_chain_check.2.2.1

theorem hs100P_normal_R : (hs100P.subgroupOf hs100R).Normal := by
  apply normal_of_index_eq_two
  have h := (hs100P.subgroupOf hs100R).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hs100P_le_R).toEquiv, card_hs100P, card_hs100R] at h
  omega

theorem hs100U_conj_mem {p : Equiv.Perm (Fin 100)} (hp : p ∈ hs100P) :
    hs100U * p * hs100U⁻¹ ∈ hs100P := by
  have := hs100P_normal_R.conj_mem ⟨p, hs100P_le_R hp⟩ (mem_subgroupOf.2 hp)
    ⟨hs100U, hs100U_mem_R⟩
  exact mem_subgroupOf.1 this

theorem mcl275R_eq_sup : mcl275P ⊔ zpowers mcl275U = mcl275R := by
  rw [mcl275P, mcl275R, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

theorem mcl275R_eq : mcl275R = mclR := mcl275R_eq_sup.symm

theorem mcl275U_conj_mem {p : Equiv.Perm (Fin 275)} (hp : p ∈ mcl275P) :
    mcl275U * p * mcl275U⁻¹ ∈ mcl275P := by
  have h := mcl_normalizing_model.2.2.2.1
  rw [mcl275P_eq] at hp ⊢
  rw [← h]
  exact ⟨p, hp, rfl⟩


theorem CTUC_HS_McL_full_automorphism_permutation_models :
    (hs100U ^ 2 = 1 ∧ hs100U ≠ 1 ∧ hs100U ∉ hs100P ∧
      hs100P.map (MulAut.conj hs100U).toMonoidHom = hs100P ∧
      centralizer (hs100P : Set (Equiv.Perm (Fin 100))) = ⊥ ∧
      (∃ e : hs100R ≃* MulAut hs100P,
        (∀ (x : hs100R) (p : hs100P),
          ((e x p : hs100P) : Equiv.Perm (Fin 100)) = x * p * (x : Equiv.Perm (Fin 100))⁻¹) ∧
        (hs100P.subgroupOf hs100R).map e.toMonoidHom = inner hs100P) ∧
      (hs100P.subgroupOf hs100R).Normal ∧ hs100P ⊓ zpowers hs100U = ⊥ ∧
      hs100P ⊔ zpowers hs100U = hs100R ∧ (hs100P.subgroupOf hs100R).index = 2 ∧
      Nonempty (Outer hs100P ≃* Multiplicative (ZMod 2)) ∧ Nat.card hs100R = 88704000) ∧
    (mcl275U ^ 2 = 1 ∧ mcl275U ≠ 1 ∧ mcl275U ∉ mcl275P ∧
      mcl275P.map (MulAut.conj mcl275U).toMonoidHom = mcl275P ∧
      centralizer (mcl275P : Set (Equiv.Perm (Fin 275))) = ⊥ ∧
      (∃ e : mcl275R ≃* MulAut mcl275P,
        (∀ (x : mcl275R) (p : mcl275P),
          ((e x p : mcl275P) : Equiv.Perm (Fin 275)) = x * p * (x : Equiv.Perm (Fin 275))⁻¹) ∧
        (mcl275P.subgroupOf mcl275R).map e.toMonoidHom = inner mcl275P) ∧
      (mcl275P.subgroupOf mcl275R).Normal ∧ mcl275P ⊓ zpowers mcl275U = ⊥ ∧
      mcl275P ⊔ zpowers mcl275U = mcl275R ∧ (mcl275P.subgroupOf mcl275R).index = 2 ∧
      Nonempty (Outer mcl275P ≃* Multiplicative (ZMod 2)) ∧ Nat.card mcl275R = 1796256000) := by
  obtain ⟨hne, hmap, he, hnormal, hinf, hindex, hout, -⟩ :=
    automorphism_model_of hs100R_eq_sup hs100U_sq hs100U_not_mem_P (fun p hp => hs100U_conj_mem hp)
      centralizer_hs100P outer_card_hs100P
  obtain ⟨hU2, -, hUP, -⟩ := mcl_normalizing_model
  obtain ⟨hne', hmap', he', hnormal', hinf', hindex', hout', hcard'⟩ :=
    automorphism_model_of mcl275R_eq_sup hU2 hUP (fun p hp => mcl275U_conj_mem hp)
      centralizer_mcl275P outer_card_mcl275P
  refine ⟨⟨hs100U_sq, hne, hs100U_not_mem_P, hmap, centralizer_hs100P, he, hnormal, hinf,
    hs100R_eq_sup, hindex, hout, card_hs100R⟩,
    ⟨hU2, hne', hUP, hmap', centralizer_mcl275P, he', hnormal', hinf', mcl275R_eq_sup, hindex',
      hout', ?_⟩⟩
  rw [hcard', mcl275P_eq, card_mclP]

end CFSG.RankThree.Native
