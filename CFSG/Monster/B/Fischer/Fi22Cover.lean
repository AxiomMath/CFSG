
module

public import CFSG.Monster.B.Fischer.Fi22CoverBase1

public import CFSG.Monster.B.Fischer.Fi22CoverCheck

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem fi22OuterR_nodup :
    fi22OuterR.Nodup := by
  have hlt := fi22OuterTPointsNat_lt
  rw [fi22OuterR, fi22FinList]
  refine fi22Cover_check.1.map_on fun x hx y hy hxy => ?_
  have := congrArg Fin.val hxy
  simp only at this
  rwa [Nat.mod_eq_of_lt (hlt x hx), Nat.mod_eq_of_lt (hlt y hy)] at this

theorem fi22OuterT_preserves_R :
    ∀ g ∈ fi22OuterT, ∀ x : Fin 3510,
    x ∈ fi22OuterR ↔ g x ∈ fi22OuterR := by
  intro g hg
  rw [fi22OuterT, RawSchreierDatum.originalSubgroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rw [Set.mem_ofPred_eq, fi22OuterChainT, RawSchreierDatum.mem_ofArrays_original] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    have hi9 : i < 9 := hi
    intro x
    rw [mem_fi22OuterR_iff, mem_fi22OuterR_iff, fi22Cover_check.2.1 i hi9 x x.2,
      (rep_fi22OuterTStrong (k := i) (by omega)) x]
  | one => exact fun x => Iff.rfl
  | mul g h _ _ hg hh => exact fun x => (hh x).trans (hg (h x))
  | inv g _ hg =>
    intro x
    have hgx : g (g⁻¹ x) = x := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    rw [hg (g⁻¹ x), hgx]

theorem fi22OuterT_faithful_R :
    ∀ g ∈ fi22OuterT, (∀ x ∈ fi22OuterR, g x = x) → g = 1 := by
  intro g hg hfix
  obtain ⟨x, rfl⟩ := fi22TProd_surj hg
  by_cases hx : x = (0, 0, 0)
  · rw [hx, fi22TProd_zero]
  · exfalso
    have hm : allLt fi22TPointsArr.size (fun k =>
        tr3 fi22TLevels x.1 x.2.1 x.2.2 fi22TPointsArr[k]! == fi22TPointsArr[k]!) = false := by
      simpa [moves3] using fi22Cover_check.2.2.1 x hx
    rw [← Bool.not_eq_true, allLt_iff] at hm
    apply hm
    intro k hk
    have hk' : k < fi22OuterTPointsNat.length := by simpa [fi22TPointsArr] using hk
    have hlt := fi22OuterTPointsNat_lt
    have hmem : fi22OuterTPointsNat[k] ∈ fi22OuterTPointsNat := List.getElem_mem hk'
    have hR : fi22TPointsArr[k]! = fi22OuterTPointsNat[k] := by
      rw [fi22TPointsArr, List.getElem!_toArray, getElem!_pos _ k hk']
    have hpt := hfix ⟨fi22OuterTPointsNat[k], hlt _ hmem⟩
      ((mem_fi22OuterR_iff _).2 (List.contains_iff_mem.2 hmem))
    rw [beq_iff_eq, hR, ← fi22TProd_apply x ⟨_, hlt _ hmem⟩, hpt]

theorem fi22OuterT_involutions :
    Set.ncard {g : Equiv.Perm (Fin 3510) | g ∈ fi22OuterT ∧ orderOf g = 2} = 3263 := by
  have hset : {g : Equiv.Perm (Fin 3510) | g ∈ fi22OuterT ∧ orderOf g = 2} =
      fi22TProd '' ↑(Finset.univ.filter fun x : Fin 1024 × Fin 32 × Fin 4 =>
        isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hg, ho⟩
      obtain ⟨x, rfl⟩ := fi22TProd_surj hg
      exact ⟨x, (isInv3_iff x).2 ho, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fi22TProd_mem x, (isInv3_iff x).1 hx⟩
  rw [hset, Set.ncard_image_of_injective _ fi22TProd_injective, Set.ncard_coe_finset,
    fi22Cover_check.2.2.2.1]

theorem fi22OuterT_involution_conj :
    ∀ g ∈ fi22OuterT, orderOf g = 2 →
    ∃ j < 54, ∃ t ∈ fi22OuterT, t * fi22OuterU j * t⁻¹ = g := by
  intro g hg ho
  obtain ⟨x, rfl⟩ := fi22TProd_surj hg
  obtain ⟨hj, ha, hb, hc, hok⟩ := fi22Cover_check.2.2.2.2.1 x ((isInv3_iff x).2 ho)
  set w := fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!
  refine ⟨w.1, hj, fi22TProd (⟨w.2.1, ha⟩, ⟨w.2.2.1, hb⟩, ⟨w.2.2.2, hc⟩), fi22TProd_mem _, ?_⟩
  exact conjOK3_spec (rep_fi22OuterU hj) hok

theorem fi22OuterU_spec
    {j : ℕ} (hj : j < 54) :
    fi22OuterU j ∈ fi22OuterT ∧ orderOf (fi22OuterU j) = 2 ∧ fi22OuterH j ∈ fi22P ∧
      ∃ i < 3, fi22OuterH j * fi22OuterU j * (fi22OuterH j)⁻¹ = fi22OuterXRep i := by
  obtain ⟨hs, h1, h2, hh, i, hi, hc⟩ := fi22Cover_check.2.2.2.2.2.1 j hj
  refine ⟨(siftA_iff_mem_originalSubgroup fi22OuterChainT_arrays (by norm_num)
      fi22Local_check.2.2.1 (rep_fi22OuterU hj)).1 hs,
    orderOf_eq_two_of_eqA (rep_fi22OuterU hj) h1 h2, mem_fi22P_of_siftA (rep_fi22OuterH hj) hh,
    i, hi, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_of_eqA (rep_compA (rep_fi22OuterH hj) (rep_fi22OuterU hj))
    (rep_compA (rep_fi22OuterXRep hi) (rep_fi22OuterH hj)) hc

theorem fi22OuterXRep_spec
    {i : ℕ} (hi : i < 3) :
    fi22OuterXRep i ∈ fi22P ∧ orderOf (fi22OuterXRep i) = 2 := by
  obtain ⟨hs, h1, h2⟩ := fi22Cover_check.2.2.2.2.2.2.1 i hi
  exact ⟨mem_fi22P_of_siftA (rep_fi22OuterXRep hi) hs,
    orderOf_eq_two_of_eqA (rep_fi22OuterXRep hi) h1 h2⟩

theorem fi22OuterXRep_two :
    fi22OuterXRep 2 = fi22OuterZ :=
  eq_of_eqA (rep_fi22OuterXRep (by norm_num)) rep_fi22OuterZ
    fi22Cover_check.2.2.2.2.2.2.2.2.2.2

theorem fi22P_involution_conj :
    ∀ g ∈ fi22P, orderOf g = 2 →
    ∃ k ∈ fi22P, k * g * k⁻¹ = fi22OuterXRep 0 ∨ k * g * k⁻¹ = fi22OuterXRep 1 ∨
      k * g * k⁻¹ = fi22OuterZ := by
  intro g hg ho
  set gP : fi22P := ⟨g, hg⟩
  have hoP : orderOf gP = 2 := by rw [Subgroup.orderOf_mk, ho]
  have hp : IsPGroup 2 (Subgroup.zpowers gP) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hoP, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨S, hS⟩ := fi22OuterT_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq fi22P Q S
  have hmem : MulAut.conj h • gP ∈ ((h • Q : Sylow 2 fi22P) : Subgroup fi22P) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers gP))
  rw [hS, Subgroup.mem_subgroupOf] at hmem
  have hconj : ((MulAut.conj h • gP : fi22P) : Equiv.Perm (Fin 3510)) =
      (h : Equiv.Perm (Fin 3510)) * g * (h : Equiv.Perm (Fin 3510))⁻¹ := rfl
  rw [hconj] at hmem
  have ho' : orderOf ((h : Equiv.Perm (Fin 3510)) * g * (h : Equiv.Perm (Fin 3510))⁻¹) = 2 := by
    rw [← ho]
    exact MulEquiv.orderOf_eq (MulAut.conj (h : Equiv.Perm (Fin 3510))) g
  obtain ⟨j, hj, t, ht, htg⟩ := fi22OuterT_involution_conj _ hmem ho'
  obtain ⟨-, -, hhj, i, hi, hx⟩ := fi22OuterU_spec hj
  refine ⟨fi22OuterH j * t⁻¹ * (h : Equiv.Perm (Fin 3510)), Subgroup.mul_mem _
    (Subgroup.mul_mem _ hhj (Subgroup.inv_mem _ (fi22OuterT_le ht))) h.2, ?_⟩
  have hg' : g = (h : Equiv.Perm (Fin 3510))⁻¹ * (t * fi22OuterU j * t⁻¹) *
      (h : Equiv.Perm (Fin 3510)) := by
    rw [htg]
    group
  have key : (fi22OuterH j * t⁻¹ * (h : Equiv.Perm (Fin 3510))) * g *
      (fi22OuterH j * t⁻¹ * (h : Equiv.Perm (Fin 3510)))⁻¹ = fi22OuterXRep i := by
    rw [hg', ← hx]
    group
  rw [key]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr fi22OuterXRep_two)

theorem AT_Fi22_Sylow_involution_cover :
    fi22OuterR.length = 256 ∧ fi22OuterR.Nodup ∧
    (∀ g ∈ fi22OuterT, ∀ x : Fin 3510, x ∈ fi22OuterR ↔ g x ∈ fi22OuterR) ∧
    (∀ g ∈ fi22OuterT, (∀ x ∈ fi22OuterR, g x = x) → g = 1) ∧
    Set.ncard {g : Equiv.Perm (Fin 3510) | g ∈ fi22OuterT ∧ orderOf g = 2} = 3263 ∧
    (∀ j < 54, fi22OuterU j ∈ fi22OuterT ∧ orderOf (fi22OuterU j) = 2 ∧ fi22OuterH j ∈ fi22P ∧
      ∃ i < 3, fi22OuterH j * fi22OuterU j * (fi22OuterH j)⁻¹ = fi22OuterXRep i) ∧
    (∀ g ∈ fi22OuterT, orderOf g = 2 → ∃ j < 54, ∃ t ∈ fi22OuterT, t * fi22OuterU j * t⁻¹ = g) ∧
    (∀ i < 3, fi22OuterXRep i ∈ fi22P ∧ orderOf (fi22OuterXRep i) = 2) ∧
    (Finset.univ.filter fun p => fi22OuterXRep 0 p = p).card = 54 ∧
    (Finset.univ.filter fun p => fi22OuterXRep 1 p = p).card = 182 ∧
    (Finset.univ.filter fun p => fi22OuterXRep 2 p = p).card = 694 ∧
    fi22OuterXRep 2 = fi22OuterZ ∧
    (∀ g ∈ fi22P, orderOf g = 2 → ∃ k ∈ fi22P,
      k * g * k⁻¹ = fi22OuterXRep 0 ∨ k * g * k⁻¹ = fi22OuterXRep 1 ∨
        k * g * k⁻¹ = fi22OuterZ) := by
  refine ⟨fi22OuterR_length, fi22OuterR_nodup, fi22OuterT_preserves_R, fi22OuterT_faithful_R,
    fi22OuterT_involutions, fun j hj => fi22OuterU_spec hj, fi22OuterT_involution_conj,
    fun i hi => fi22OuterXRep_spec hi, ?_, ?_, ?_, fi22OuterXRep_two, fi22P_involution_conj⟩
  · rw [filter_fixed_fi22OuterXRep (i := 0) (by norm_num)]
    exact fi22Cover_check.2.2.2.2.2.2.2.1
  · rw [filter_fixed_fi22OuterXRep (i := 1) (by norm_num)]
    exact fi22Cover_check.2.2.2.2.2.2.2.2.1
  · rw [filter_fixed_fi22OuterXRep (i := 2) (by norm_num)]
    exact fi22Cover_check.2.2.2.2.2.2.2.2.2.1

end CFSG.Monster.B.Fischer
