module

public import CFSG.Sporadic.Schreier.RuCentersMain
public import Certificates.Certificate9680

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruZJ_check :
    all2 1920 ruJLevels (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
      eqA 1920 g (idA 1920) || eqA 1920 g (ruEF 0)) = true :=
  Certificates.certificate9680

theorem ruJ_center_le :
    (Subgroup.center ruJ).map ruJ.subtype ≤ Subgroup.zpowers ruZ := by
  rintro _ ⟨x, hx, rfl⟩
  have hxC : (x : Equiv.Perm (Fin 4060)) ∈ ruC := ruJ_leC x.2
  have hmem : ruResFPerm x ∈ ruChainJ.originalSubgroup := by
    rw [ruChainJ_sub]
    exact ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 x.2, (ruResFPerm_of_mem hxC).symm⟩
  have hcomm : ∀ j < 6, ruResFPerm x * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm (ruJGens.getD j 1) * ruResFPerm x := by
    intro j hj
    have hxk := Subgroup.mem_center_iff.1 hx ⟨_, ruJGens_getD_mem j⟩
    have e : (x : Equiv.Perm (Fin 4060)) * ruJGens.getD j 1 = ruJGens.getD j 1 * x :=
      congrArg Subtype.val hxk.symm
    rw [← ruResFPerm_mul hxC (ruJ_leC (ruJGens_getD_mem j)),
      ← ruResFPerm_mul (ruJ_leC (ruJGens_getD_mem j)) hxC, e]
  have h := ruChainJ_check.1
  have hb : ruChainJ.baseCount = 2 := rfl
  have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
    (le_of_eq hb.symm) (fun i hi hi' => by
      have : i < 2 := lt_of_lt_of_eq hi' hb
      omega)
    (P := fun g => (∀ j < 6, g * ruResFPerm (ruJGens.getD j 1) =
      ruResFPerm (ruJGens.getD j 1) * g) → g = 1 ∨ g = ruResFPerm (ruEElt 0))
    (fun t g ht hp hc => by
      have hcs : (allLt 6 fun j => ruComm1920 t (ruJF j)) = true := by
        rw [allLt_iff]
        intro j hj
        exact (eqA_iff (rep_compA ht (rep_ruJF hj)) (rep_compA (rep_ruJF hj) ht)).2 (hc j hj)
      simp only [hcs, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact Or.inl ((eqA_iff ht rep_idA).1 hp)
      · exact Or.inr ((eqA_iff ht (rep_ruEF (by norm_num : 0 < 7))).1 hp))
    ruZJ_check (ruResFPerm x) hmem hcomm
  rcases key with h1 | he
  · rw [ruResFPerm_of_mem hxC, show (1 : Equiv.Perm (Fin 1920)) = ruResF 1 from (map_one _).symm]
      at h1
    have := congrArg Subtype.val (ruResF_injective h1)
    rw [Subgroup.coe_subtype, this]
    exact Subgroup.one_mem _
  · rw [ruResFPerm_of_mem hxC, ruEElt_zero, ruResFPerm_of_mem ruZ_memC] at he
    have := congrArg Subtype.val (ruResF_injective he)
    rw [Subgroup.coe_subtype, this]
    exact Subgroup.mem_zpowers ruZ

theorem ruJ_center_eq
    {x : Equiv.Perm (Fin 4060)} (hx : x ∈ ruJ)
    (hc : ∀ j ∈ ruJ, x * j = j * x) : x = 1 ∨ x = ruZ := by
  have hmem : (⟨x, hx⟩ : ruJ) ∈ Subgroup.center ruJ :=
    Subgroup.mem_center_iff.2 fun j => Subtype.ext (hc j j.2).symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ruJ_center_le ⟨⟨x, hx⟩, hmem, rfl⟩)
  have hk' : ruZ ^ k = x := hk
  rw [← hk', ← zpow_mod_orderOf, orderOf_ruZ]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h | h
  · exact Or.inl (by rw [h, zpow_zero])
  · exact Or.inr (by rw [h, zpow_one])

end CFSG.Sporadic.RuSchreier
