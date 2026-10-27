module

public import CFSG.Quasithin.Background.RonanH143QH

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

@[expose] def betaNatT (a₁ a₂ a₃ a₄ a₅ : ZMod 2) : ℕ :=
  (if a₁ = 1 then 1 else 0) ^^^ (if a₂ = 1 then 15 else 0) ^^^ (if a₃ = 1 then 12 else 0) ^^^
    (if a₄ = 1 then 8 else 0) ^^^ (if a₅ = 1 then 10 else 0)

@[expose] def betaIdx (v : Fin 6 → ZMod 2) : Fin 16 :=
  ⟨betaNatT (v 1) (v 2) (v 3) (v 4) (v 5) % 16, Nat.mod_lt _ (by norm_num)⟩

theorem betaIdx_zero : betaIdx 0 = 0 := by decide +kernel

theorem betaNatT_add : ∀ a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : ZMod 2,
    betaNatT (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) (a₅ + b₅) % 16 =
      ((betaNatT a₁ a₂ a₃ a₄ a₅ % 16) ^^^ (betaNatT b₁ b₂ b₃ b₄ b₅ % 16)) % 16 := by
  decide +kernel

theorem betaIdx_add (v w : Fin 6 → ZMod 2) :
    betaIdx (v + w) = xorF (betaIdx v) (betaIdx w) := by
  apply Fin.ext
  exact betaNatT_add (v 1) (v 2) (v 3) (v 4) (v 5) (w 1) (w 2) (w 3) (w 4) (w 5)

@[expose] def beta6Full : G6.PermMod 6 →* P24 where
  toFun v := koPerm (betaIdx (Multiplicative.toAdd v))
  map_one' := by
    show koPerm (betaIdx 0) = 1
    rw [betaIdx_zero, koPerm_zero]
  map_mul' v w := by
    show koPerm (betaIdx (Multiplicative.toAdd v + Multiplicative.toAdd w)) =
      koPerm (betaIdx (Multiplicative.toAdd v)) * koPerm (betaIdx (Multiplicative.toAdd w))
    rw [betaIdx_add, koPerm_mul]

@[expose] def beta6 : ↥(G6.coreMod 6) →* P24 := beta6Full.comp (G6.coreMod 6).subtype

theorem beta6_apply (u : ↥(G6.coreMod 6)) :
    beta6 u = koPerm (betaIdx (Multiplicative.toAdd (u : G6.PermMod 6))) := rfl

@[expose] def xf6 (s : Fin 16) : Fin 16 :=
  ⟨([0, 10, 7, 13, 14, 4, 9, 3, 5, 15, 2, 8, 11, 1, 12, 6].getD (s : ℕ) 0) % 16,
    Nat.mod_lt _ (by norm_num)⟩

@[expose] def xfT (s : Fin 16) : Fin 16 :=
  ⟨([0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14].getD (s : ℕ) 0) % 16,
    Nat.mod_lt _ (by norm_num)⟩

theorem koPerm_conj_KO : ∀ t s : Fin 16, koPerm t * koPerm s * (koPerm t)⁻¹ = koPerm s := by
  decide +kernel

theorem koPerm_eq_one_iff : ∀ s : Fin 16, koPerm s = 1 ↔ s = 0 := by decide +kernel

theorem x6_conj_KO : ∀ s : Fin 16, x6Perm * koPerm s * x6Perm⁻¹ = koPerm (xf6 s) := by
  decide +kernel

theorem tau_conj_KO : ∀ s : Fin 16, tauPerm * koPerm s * tauPerm⁻¹ = koPerm (xfT s) := by
  decide +kernel

theorem exists_even_betaIdx :
    ∀ t : Fin 16, ∃ v : Fin 6 → ZMod 2, ∑ i, v i = 0 ∧ betaIdx v = t := by
  decide +kernel

theorem betaIdx_eq_zero_iff_even : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    (betaIdx v = 0 ↔ v = 0 ∨ v = fun _ => 1) := by
  decide +kernel

theorem x6_vec : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    betaIdx (fun i => v (sigX⁻¹ i)) = xf6 (betaIdx v) := by
  decide +kernel

theorem tau_vec : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
    betaIdx (fun i => v (sigT⁻¹ i)) = xfT (betaIdx v) := by
  decide +kernel

theorem beta6_range : beta6.range = fixO := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [beta6_apply]
    exact (mem_fixO_iff _).2 ⟨_, rfl⟩
  · intro hx
    obtain ⟨t, rfl⟩ := (mem_fixO_iff x).1 hx
    obtain ⟨v, hv, hvt⟩ := exists_even_betaIdx t
    refine MonoidHom.mem_range.2 ⟨⟨Multiplicative.ofAdd v, G6.mem_coreMod.2 hv⟩, ?_⟩
    show koPerm (betaIdx v) = koPerm t
    rw [hvt]

theorem zpow_eq_zpow_emod_two {G : Type*} [Group G] (a : G) (h : a ^ (2 : ℤ) = 1) (k : ℤ) :
    a ^ k = a ^ (k % 2) := by
  have hk : k = k % 2 + 2 * (k / 2) := by omega
  calc a ^ k = a ^ (k % 2 + 2 * (k / 2)) := by rw [← hk]
    _ = a ^ (k % 2) * (a ^ (2 : ℤ)) ^ (k / 2) := by rw [zpow_add, zpow_mul]
    _ = a ^ (k % 2) := by rw [h, one_zpow, mul_one]

theorem mem_zpowersAllOnes {x : G6.PermMod 6} :
    x ∈ Subgroup.zpowers (G6.allOnes 6) ↔ x = 1 ∨ x = G6.allOnes 6 := by
  have h2 : G6.allOnes 6 * G6.allOnes 6 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    revert i
    decide +kernel
  have h2' : G6.allOnes 6 ^ (2 : ℤ) = 1 := by rw [zpow_two, h2]
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [zpow_eq_zpow_emod_two _ h2' k]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers_iff.2 ⟨1, zpow_one _⟩

theorem beta6_ker : beta6.ker = G6.natKer 6 := by
  ext u
  rw [MonoidHom.mem_ker]
  change beta6 u = 1 ↔ (u : G6.PermMod 6) ∈ Subgroup.zpowers (G6.allOnes 6)
  have hs : ∑ i, Multiplicative.toAdd (u : G6.PermMod 6) i = 0 := G6.mem_coreMod.1 u.2
  have e1 : Multiplicative.toAdd (u : G6.PermMod 6) = 0 ↔ (u : G6.PermMod 6) = 1 :=
    toAdd_eq_zero
  have e2 : Multiplicative.toAdd (u : G6.PermMod 6) = (fun _ => 1) ↔
      (u : G6.PermMod 6) = G6.allOnes 6 :=
    ⟨fun h => Multiplicative.toAdd.injective (h : Multiplicative.toAdd (u : G6.PermMod 6) =
      Multiplicative.toAdd (G6.allOnes 6)), fun h => congrArg Multiplicative.toAdd h⟩
  rw [beta6_apply, koPerm_eq_one_iff, betaIdx_eq_zero_iff_even _ hs, mem_zpowersAllOnes, e1, e2]

theorem beta6_x6 (u : ↥(G6.coreMod 6)) :
    beta6 (G6.coreAct 6 sigX u) = x6Perm * beta6 u * x6Perm⁻¹ := by
  have hs : ∑ i, Multiplicative.toAdd (u : G6.PermMod 6) i = 0 := G6.mem_coreMod.1 u.2
  rw [beta6_apply, beta6_apply, x6_conj_KO]
  exact congrArg koPerm (x6_vec (Multiplicative.toAdd (u : G6.PermMod 6)) hs)

theorem beta6_tau (u : ↥(G6.coreMod 6)) :
    beta6 (G6.coreAct 6 sigT u) = tauPerm * beta6 u * tauPerm⁻¹ := by
  have hs : ∑ i, Multiplicative.toAdd (u : G6.PermMod 6) i = 0 := G6.mem_coreMod.1 u.2
  rw [beta6_apply, beta6_apply, tau_conj_KO]
  exact congrArg koPerm (tau_vec (Multiplicative.toAdd (u : G6.PermMod 6)) hs)

abbrev GoodMH (g : P24) : Prop :=
  ∃ hg : g ∈ MY mog22plus Hstd, ∀ u : ↥(G6.coreMod 6),
    beta6 (G6.coreAct 6 (piH2 ⟨g, hg⟩) u) = g * beta6 u * g⁻¹

theorem goodMH_one :
    GoodMH (1 : P24) := by
  refine ⟨one_mem _, fun u => ?_⟩
  have hp : piH2 ⟨(1 : P24), one_mem _⟩ = 1 :=
    piH2_eq_of_smul _ 1 fun i => by simp
  rw [hp, map_one, MulAut.one_apply]
  simp

theorem goodMH_mul {g h : P24}
    (hg : GoodMH g) (hh : GoodMH h) : GoodMH (g * h) := by
  obtain ⟨hg', eg⟩ := hg
  obtain ⟨hh', eh⟩ := hh
  refine ⟨mul_mem hg' hh', fun u => ?_⟩
  have hp : piH2 ⟨g * h, mul_mem hg' hh'⟩ = piH2 ⟨g, hg'⟩ * piH2 ⟨h, hh'⟩ :=
    map_mul piH2 ⟨g, hg'⟩ ⟨h, hh'⟩
  rw [hp, map_mul, MulAut.mul_apply, eg, eh u]
  simp only [mul_inv_rev, mul_assoc]

theorem goodMH_inv {g : P24}
    (hg : GoodMH g) : GoodMH g⁻¹ := by
  obtain ⟨hg', eg⟩ := hg
  refine ⟨inv_mem hg', fun u => ?_⟩
  have h1 : piH2 ⟨g, hg'⟩ * piH2 ⟨g⁻¹, inv_mem hg'⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨g, hg'⟩ * ⟨g⁻¹, inv_mem hg'⟩ : ↥(MY mog22plus Hstd)) = 1 :=
      Subtype.ext (mul_inv_cancel g)
    rw [e, map_one]
  have hx : G6.coreAct 6 (piH2 ⟨g, hg'⟩) (G6.coreAct 6 (piH2 ⟨g⁻¹, inv_mem hg'⟩) u) = u := by
    rw [← MulAut.mul_apply, ← map_mul, h1, map_one, MulAut.one_apply]
  have key := eg (G6.coreAct 6 (piH2 ⟨g⁻¹, inv_mem hg'⟩) u)
  rw [hx] at key
  have hx' : beta6 (G6.coreAct 6 (piH2 ⟨g⁻¹, inv_mem hg'⟩) u) = g⁻¹ * beta6 u * g := by
    rw [key]
    group
  rw [hx', inv_inv]

theorem goodMH_koPerm (t : Fin 16) :
    GoodMH (koPerm t) := by
  refine ⟨koPerm_mem_MY_H_plus t, fun u => ?_⟩
  have hp : piH2 ⟨koPerm t, koPerm_mem_MY_H_plus t⟩ = 1 :=
    piH2_eq_of_smul _ 1 fun i => by simpa using ko_smul_Tot t i
  rw [hp, map_one, MulAut.one_apply, beta6_apply]
  exact (koPerm_conj_KO t _).symm

theorem goodMH_of_mem_fixO
    {g : P24} (hg : g ∈ fixO) : GoodMH g := by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
  exact goodMH_koPerm t

theorem goodMH_x6 :
    GoodMH x6Perm := by
  refine ⟨x6_mem_MY_H, fun u => ?_⟩
  have hp : piH2 ⟨x6Perm, x6_mem_MY_H⟩ = sigX := piH2_eq_of_smul _ _ x6_smul_Tot
  rw [hp]
  exact beta6_x6 u

theorem goodMH_tau :
    GoodMH tauPerm := by
  refine ⟨tau_mem_MY_H, fun u => ?_⟩
  have hp : piH2 ⟨tauPerm, tau_mem_MY_H⟩ = sigT := piH2_eq_of_smul _ _ tau_smul_Tot
  rw [hp]
  exact beta6_tau u

def goodMHSub : Subgroup P24 where
  carrier := {g | GoodMH g}
  mul_mem' := fun {g h} hg hh => goodMH_mul hg hh
  one_mem' := goodMH_one
  inv_mem' := fun {g} hg => goodMH_inv hg

def genMH : Subgroup P24 := Subgroup.closure ((fixO : Set P24) ∪ {x6Perm, tauPerm})

theorem genMH_le : genMH ≤ MY mog22plus Hstd := by
  unfold genMH
  rw [Subgroup.closure_le]
  rintro g (hg | rfl | rfl)
  · exact fixO_le_MY_H_plus hg
  · exact x6_mem_MY_H
  · exact tau_mem_MY_H

theorem fixO_le_genMH : fixO ≤ genMH := by
  intro g hg
  unfold genMH
  exact Subgroup.subset_closure (Or.inl hg)

theorem x6_mem_genMH : x6Perm ∈ genMH := by
  unfold genMH
  exact Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))

theorem tau_mem_genMH : tauPerm ∈ genMH := by
  unfold genMH
  exact Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem genMH_gens :
    ((fixO : Set P24) ∪ {x6Perm, tauPerm}) ⊆ (goodMHSub : Set P24) := by
  rintro g (hg | rfl | rfl)
  · exact goodMH_of_mem_fixO hg
  · exact goodMH_x6
  · exact goodMH_tau

theorem genMH_le_goodMHSub :
    genMH ≤ goodMHSub := by
  unfold genMH
  exact (Subgroup.closure_le _).2 genMH_gens

theorem genMH_eq :
    genMH = MY mog22plus Hstd := by
  apply Subgroup.eq_of_le_of_card_ge genMH_le
  have hC : (genMH.subgroupOf (MY mog22plus Hstd)).map piH2 = ⊤ := by
    have hm := map_closure_eq_top_of_cycle_swap piH2 sigX sigX_isCycle sigX_support 1
      ⟨x6Perm, x6_mem_MY_H⟩ ⟨tauPerm, tau_mem_MY_H⟩ (piH2_eq_of_smul _ _ x6_smul_Tot)
      (by rw [← sigT_eq]; exact piH2_eq_of_smul _ _ tau_smul_Tot)
    refine eq_top_iff.2 ?_
    rw [← hm]
    refine Subgroup.map_mono ?_
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Subgroup.mem_subgroupOf.2 x6_mem_genMH
    · exact Subgroup.mem_subgroupOf.2 tau_mem_genMH
  have hNC : fixO.subgroupOf (MY mog22plus Hstd) ≤ genMH.subgroupOf (MY mog22plus Hstd) :=
    fun g hg => Subgroup.mem_subgroupOf.2 (fixO_le_genMH (Subgroup.mem_subgroupOf.1 hg))
  have hNk : fixO.subgroupOf (MY mog22plus Hstd) ≤ piH2.ker := le_of_eq ker_piH2.symm
  have key := card_mul_factorial_le piH2 (genMH.subgroupOf (MY mog22plus Hstd))
    (fixO.subgroupOf (MY mog22plus Hstd)) hC hNC hNk
  have hN : Nat.card ↥(fixO.subgroupOf (MY mog22plus Hstd)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_MY_H_plus).toEquiv, card_fixO']
  have hCc : Nat.card ↥(genMH.subgroupOf (MY mog22plus Hstd)) = Nat.card ↥genMH :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe genMH_le).toEquiv
  have h720 : Nat.factorial 6 = 720 := by decide
  rw [hN, hCc, h720] at key
  rw [card_MY_H_L2]
  omega

theorem beta6_equiv
    (g : ↥(MY mog22plus Hstd)) (u : ↥(G6.coreMod 6)) :
    beta6 (G6.coreAct 6 (piH2 g) u) = (g : P24) * beta6 u * (g : P24)⁻¹ := by
  have hmem : (g : P24) ∈ genMH := by
    rw [genMH_eq]
    exact g.2
  have hgood : GoodMH (g : P24) := genMH_le_goodMHSub hmem
  obtain ⟨_, e⟩ := hgood
  exact e u

theorem piH1_eq_piH2
    (g : ↥(MY mog22 Hstd)) :
    piH1 g = piH2 ⟨(g : P24), MY_mog22_le_plus Hstd g.2⟩ := by
  refine Equiv.ext fun i => ?_
  exact Tot_injective ((piH1_spec g i).trans
    (piH2_spec ⟨(g : P24), MY_mog22_le_plus Hstd g.2⟩ i).symm)

theorem conjSymNatural_H_L2 :
    ConjSymNatural (MY mog22plus Hstd) (KY mog22plus Hstd) 6 ⊤ := by
  rw [KY_H_L2]
  unfold ConjSymNatural
  exact ⟨fixO_le_MY_H_plus, piH2, beta6, piH2_range_top, ker_piH2, beta6_range, beta6_ker,
    fun g u => beta6_equiv g u⟩

theorem conjSymNatural_H_L :
    ConjSymNatural (MY mog22 Hstd) (KY mog22 Hstd) 6 (alternatingGroup (Fin 6)) := by
  rw [KY_H_L]
  unfold ConjSymNatural
  refine ⟨fixO_le_MY_H, piH1, beta6, range_piH1, ker_piH1, beta6_range, beta6_ker, ?_⟩
  intro g u
  rw [piH1_eq_piH2]
  exact beta6_equiv ⟨(g : P24), MY_mog22_le_plus Hstd g.2⟩ u

end CFSG.Quasithin.RonanH143
