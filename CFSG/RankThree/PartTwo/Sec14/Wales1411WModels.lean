module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WDefs
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM12
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM22
import CFSG.RankThree.PartTwo.KFacts.K412Alternating
import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7Conj
import CFSG.RankThree.PartTwo.KFacts.KP4Signal

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W

open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem exists_conj_of_le {E H S T : Subgroup Q} (hS : Maximal (InvTwo E H) S)
    (hT : Maximal (InvTwo E H) T) (hST : S ≤ T ∨ T ≤ S) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (E : Set Q), T = S.map (MulAut.conj n).toMonoidHom := by
  have hTS : T = S := by
    rcases hST with h | h
    · exact le_antisymm (hS.2 hT.1 h) h
    · exact le_antisymm h (hT.2 hS.1 h)
  refine ⟨1, one_mem _, ?_⟩
  rw [hTS]
  ext x
  simp

theorem eq_map_conj_of_forall [Finite Q] {U W : Subgroup Q} {n : Q}
    (hle : ∀ u ∈ U, n * u * n⁻¹ ∈ W) (hcard : Nat.card W ≤ Nat.card U) :
    W = U.map (MulAut.conj n).toMonoidHom := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rintro _ ⟨u, hu, rfl⟩
    exact hle u hu
  · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hcard

theorem conj_mem_of_mem_kleinFour {a b n : Q} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} {W : Subgroup Q} (h1 : n * a * n⁻¹ ∈ W) (h2 : n * b * n⁻¹ ∈ W) :
    ∀ u ∈ CFSG.LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf a b ha hb hab,
      n * u * n⁻¹ ∈ W := by
  rintro u (rfl | rfl | rfl | rfl)
  · rw [mul_one, mul_inv_cancel]
    exact one_mem W
  · exact h1
  · exact h2
  · rw [show n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) by group]
    exact mul_mem h1 h2

namespace ModelM12

open CFSG.GH74.M12.Hyp (G12 wordP wordP_mem)
open CFSG.RankThree.PartTwo.Toolkit.M12 (x y basisA)
open CFSG.RankThree.PartTwo.Sec14.Res5GenM12 (W wG wP xP yP zP iSup_W_eq_top)
open CFSG.RankThree.PartTwo.Sec14.Res5TypesM12 (mem_W_iff z_val)
open CFSG.LocalAnalysis.ComponentInitial (FourGroup.kleinFourOf_le
  FourGroup.left_mem_kleinFourOf FourGroup.right_mem_kleinFourOf)

@[expose] def cP : Equiv.Perm (Fin 12) :=
  List.formPerm [3, 11, 7] * List.formPerm [4, 5, 9] * List.formPerm [6, 10, 8]

@[expose] def cWord : List Int := [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2]

theorem cP_eq_wordP : cP = wordP cWord := by
  decide +kernel

@[expose] def cG : G12 := ⟨cP, cP_eq_wordP ▸ wordP_mem _⟩

theorem c_facts_A : cP * zP * cP⁻¹ = zP ∧ cP * (xP * yP) * cP⁻¹ = zP * (xP * yP) := by
  decide +kernel

theorem c_facts_W : ∀ (i j : Fin 3) (l : Fin 2),
    cP ^ ((j - i : Fin 3) : ℕ) * wP i l * (cP ^ ((j - i : Fin 3) : ℕ))⁻¹ = wP j 0 ∨
      cP ^ ((j - i : Fin 3) : ℕ) * wP i l * (cP ^ ((j - i : Fin 3) : ℕ))⁻¹ = wP j 1 ∨
      cP ^ ((j - i : Fin 3) : ℕ) * wP i l * (cP ^ ((j - i : Fin 3) : ℕ))⁻¹ =
        wP j 0 * wP j 1 := by
  decide +kernel

theorem cG_mem_normalizer : cG ∈ Subgroup.normalizer (basisA.sub : Set G12) := by
  obtain ⟨h1, h2⟩ := c_facts_A
  have hx : ((x : G12) : Equiv.Perm (Fin 12)) = xP := Res5GenM12.wordP_wX
  have hy : ((y : G12) : Equiv.Perm (Fin 12)) = yP := Res5GenM12.wordP_wY
  refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
  rintro _ (rfl | rfl)
  · have he : cG * basisA.a * cG⁻¹ = basisA.a := by
      refine Subtype.ext ?_
      change cP * ((⁅x, y⁆ : G12) : Equiv.Perm (Fin 12)) * cP⁻¹ =
        ((⁅x, y⁆ : G12) : Equiv.Perm (Fin 12))
      rw [z_val]
      exact h1
    rw [he]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have he : cG * basisA.b * cG⁻¹ = basisA.a * basisA.b := by
      refine Subtype.ext ?_
      change cP * (((x : G12) : Equiv.Perm (Fin 12)) * ((y : G12) : Equiv.Perm (Fin 12))) * cP⁻¹ =
        ((⁅x, y⁆ : G12) : Equiv.Perm (Fin 12)) *
          (((x : G12) : Equiv.Perm (Fin 12)) * ((y : G12) : Equiv.Perm (Fin 12)))
      rw [z_val, hx, hy]
      exact h2
    rw [he]
    exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem mem_W_of_coe {j : Fin 3} {g : G12}
    (h : (g : Equiv.Perm (Fin 12)) = wP j 0 ∨ (g : Equiv.Perm (Fin 12)) = wP j 1 ∨
      (g : Equiv.Perm (Fin 12)) = wP j 0 * wP j 1) : g ∈ W j := by
  rcases h with h | h | h
  · exact (mem_W_iff j g).mpr (Or.inr (Or.inl (Subtype.ext h)))
  · exact (mem_W_iff j g).mpr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact (mem_W_iff j g).mpr (Or.inr (Or.inr (Or.inr (Subtype.ext h))))

theorem exists_conj (i j : Fin 3) :
    ∃ n ∈ Subgroup.normalizer (basisA.sub : Set G12),
      W j = (W i).map (MulAut.conj n).toMonoidHom := by
  refine ⟨cG ^ ((j - i : Fin 3) : ℕ), pow_mem cG_mem_normalizer _, ?_⟩
  refine eq_map_conj_of_forall (conj_mem_of_mem_kleinFour ?_ ?_) (by
    rw [Res5GenM12.card_W, Res5GenM12.card_W])
  · refine mem_W_of_coe ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact c_facts_W i j 0
  · refine mem_W_of_coe ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact c_facts_W i j 1

theorem third_facts : ∀ i j k : Fin 3, i < j → k ≠ i → k ≠ j →
    wP k 0 = wP i 0 * wP j 1 * wP i 1 * wP j 1 * wP i 0 * wP j 1 * wP i 0 * wP j 0 * wP i 0 *
      wP j 1 ∧
    wP k 1 = wP i 0 * wP j 0 * wP i 0 * wP i 1 * wP j 0 * wP i 0 * wP j 0 * wP i 0 * wP j 1 *
      wP i 0 * wP j 0 := by
  decide +kernel

theorem W_le_sup {i j k : Fin 3} (hij : i < j) (hki : k ≠ i) (hkj : k ≠ j) :
    W k ≤ W i ⊔ W j := by
  obtain ⟨h0, h1⟩ := third_facts i j k hij hki hkj
  have hi : ∀ l, wG i l ∈ W i ⊔ W j := fun l => Subgroup.mem_sup_left (by
    fin_cases l
    · exact FourGroup.left_mem_kleinFourOf
    · exact FourGroup.right_mem_kleinFourOf)
  have hj : ∀ l, wG j l ∈ W i ⊔ W j := fun l => Subgroup.mem_sup_right (by
    fin_cases l
    · exact FourGroup.left_mem_kleinFourOf
    · exact FourGroup.right_mem_kleinFourOf)
  refine FourGroup.kleinFourOf_le ?_ ?_
  · rw [show wG k 0 = wG i 0 * wG j 1 * wG i 1 * wG j 1 * wG i 0 * wG j 1 * wG i 0 * wG j 0 *
        wG i 0 * wG j 1 from Subtype.ext h0]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (hi 0) (hj 1)) (hi 1)) (hj 1)) (hi 0)) (hj 1)) (hi 0)) (hj 0)) (hi 0)) (hj 1)
  · rw [show wG k 1 = wG i 0 * wG j 0 * wG i 0 * wG i 1 * wG j 0 * wG i 0 * wG j 0 * wG i 0 *
        wG j 1 * wG i 0 * wG j 0 from Subtype.ext h1]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (hi 0) (hj 0)) (hi 0)) (hi 1)) (hj 0)) (hi 0)) (hj 0)) (hi 0)) (hj 1)) (hi 0))
      (hj 0)

theorem sup_W_eq_top {i j : Fin 3} (hij : i ≠ j) : W i ⊔ W j = ⊤ := by
  wlog hlt : i < j generalizing i j
  · rw [sup_comm]
    exact this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  rw [eq_top_iff, ← iSup_W_eq_top]
  refine iSup_le fun k => ?_
  by_cases hki : k = i
  · rw [hki]
    exact le_sup_left
  by_cases hkj : k = j
  · rw [hkj]
    exact le_sup_right
  exact W_le_sup hlt hki hkj

theorem invTwo_cases
    {H U : Subgroup G12}
    (hU : InvTwo basisA.sub H U) : U = ⊥ ∨ ∃ k, U = W k := by
  obtain ⟨-, hP, hU2⟩ := hU
  obtain ⟨k, hk⟩ := Res5TypesM12.le_V_of_invariant (not_three_dvd_card_of_isPGroup hU2) hP
  by_cases hb : U = ⊥
  · exact Or.inl hb
  obtain ⟨z1, z2⟩ := Res5TypesM12.z2_conj k
  exact Or.inr ⟨k, Res5TypesM12.eq_of_le_four (mem_W_iff k) z1 z2
    (hP (pow_mem Sec4.Sporadic.M12Sig.z_mem_A 2)) ((Res5TypesM12.W_eq_V k).symm ▸ hk) hb⟩

end ModelM12

theorem etrans_M12 :
    ETrans CFSG.GH74.M12.Hyp.G12 CFSG.RankThree.PartTwo.Toolkit.M12.basisA.sub := by
  intro H _ _ S T hS hT
  rcases ModelM12.invTwo_cases hS.1 with rfl | ⟨i, rfl⟩
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  rcases ModelM12.invTwo_cases hT.1 with rfl | ⟨j, rfl⟩
  · exact exists_conj_of_le hS hT (Or.inr bot_le)
  by_cases hij : i = j
  · subst hij
    exact exists_conj_of_le hS hT (Or.inl le_rfl)
  obtain ⟨n, hnN, hn⟩ := ModelM12.exists_conj i j
  have hH : H = ⊤ :=
    eq_top_iff.mpr ((ModelM12.sup_W_eq_top hij).ge.trans (sup_le hS.1.1 hT.1.1))
  exact ⟨n, ⟨hH ▸ Subgroup.mem_top n, hnN⟩, hn⟩

namespace ModelA7

open Equiv CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec14.Res5TypesA7
  CFSG.RankThree.PartTwo.Sec14.Res4A7

@[expose] def r7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨rFour, Perm.mem_alternatingGroup.mpr rFour_spec.1⟩

theorem rFour_conj_vOneF : ∀ m : Fin 4, ∃ k : Fin 4, rFour * vOneF m * rFour⁻¹ = vTwoF k := by
  decide +kernel

theorem r7_mem_normalizer : r7 ∈ Subgroup.normalizer (P7 : Set ↥(alternatingGroup (Fin 7))) := by
  have hN := (Subgroup.mem_inf.mp KFacts.K412.rFour_mem_normSevenAlt).1
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro h
  exact hN (h : Perm (Fin 7))

theorem V1_eq_map : V1 = V2.map (MulAut.conj r7).toMonoidHom := by
  obtain ⟨h1, h2, -, -⟩ := V_facts
  refine eq_map_conj_of_forall (fun u hu => ?_) (by rw [h1, h2])
  show (rFour * (u : Perm (Fin 7)) * rFour⁻¹) ∈ vOne
  rw [vOne_eq_map_vTwo]
  exact ⟨u, hu, rfl⟩

theorem V2_eq_map : V2 = V1.map (MulAut.conj r7).toMonoidHom := by
  obtain ⟨h1, h2, -, -⟩ := V_facts
  refine eq_map_conj_of_forall (fun u hu => ?_) (by rw [h1, h2])
  obtain ⟨m, hm⟩ := mem_vOne.mp hu
  obtain ⟨k, hk⟩ := rFour_conj_vOneF m
  show (rFour * (u : Perm (Fin 7)) * rFour⁻¹) ∈ vTwo
  rw [show (u : Perm (Fin 7)) = vOneF m from hm, hk]
  exact ⟨k, rfl⟩

theorem sup_V_eq_top : V1 ⊔ V2 = ⊤ := by
  rw [V1, V2, ← Subgroup.subgroupOf_sup vOne_le_alternatingGroup vTwo_le_alternatingGroup,
    vOne_sup_vTwo, Subgroup.subgroupOf_self]

theorem invTwo_cases {H U : Subgroup ↥(alternatingGroup (Fin 7))} (hU : InvTwo P7 H U) :
    U = ⊥ ∨ U = V1 ∨ U = V2 := by
  obtain ⟨-, hP, h2⟩ := hU
  obtain ⟨-, -, -, -, -, -, -, -, a9, a10⟩ := vOne_facts
  obtain ⟨-, -, -, -, -, -, -, -, b9, b10⟩ := vTwo_facts
  by_cases hb : U = ⊥
  · exact Or.inl hb
  rcases le_V_of_invariant (not_three_dvd_card_of_isPGroup h2) hP with h | h
  · exact Or.inr (Or.inl (Res5TypesM12.eq_of_le_four mem_V1_iff (Subtype.ext a9)
      (Subtype.ext a10) (hP c2_mem_P7) h hb))
  · exact Or.inr (Or.inr (Res5TypesM12.eq_of_le_four mem_V2_iff (Subtype.ext b9)
      (Subtype.ext b10) (hP c1_mem_P7) h hb))

end ModelA7

theorem etrans_A7 : ETrans ↥(alternatingGroup (Fin 7)) Res5TypesA7.P7 := by
  intro H _ _ S T hS hT
  have hH : Res5TypesA7.V1 ≤ H → Res5TypesA7.V2 ≤ H →
      ModelA7.r7 ∈ H ⊓ Subgroup.normalizer (Res5TypesA7.P7 : Set ↥(alternatingGroup (Fin 7))) :=
    fun h1 h2 => ⟨eq_top_iff.mpr (ModelA7.sup_V_eq_top.ge.trans (sup_le h1 h2)) ▸
      Subgroup.mem_top _, ModelA7.r7_mem_normalizer⟩
  rcases ModelA7.invTwo_cases hS.1 with rfl | rfl | rfl <;>
    rcases ModelA7.invTwo_cases hT.1 with rfl | rfl | rfl
  · exact exists_conj_of_le hS hT (Or.inl le_rfl)
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  · exact exists_conj_of_le hS hT (Or.inr bot_le)
  · exact exists_conj_of_le hS hT (Or.inl le_rfl)
  · exact ⟨ModelA7.r7, hH hS.1.1 hT.1.1, ModelA7.V2_eq_map⟩
  · exact exists_conj_of_le hS hT (Or.inr bot_le)
  · exact ⟨ModelA7.r7, hH hT.1.1 hS.1.1, ModelA7.V1_eq_map⟩
  · exact exists_conj_of_le hS hT (Or.inl le_rfl)

namespace ModelM22

open Equiv CFSG.RankThree.PartTwo.KFacts.KP4 CFSG.RankThree.PartTwo.Sec14.Res5TypesM22
open CFSG.RankThree.Asc83Table.M22 (x y X Y E)

@[expose] def alphaP (k l : Fin 4) : Perm (Fin 22) :=
  vA k * vA l * vB k * vB l * vA k * vA l * vB k

@[expose] def betaP (k l : Fin 4) : Perm (Fin 22) :=
  vA k * vB l * vB k * vA l * vA k * vB l * vB k

@[expose] def swapP : Fin 4 → Perm (Fin 22) := ![alphaP 0 2, betaP 0 3, betaP 1 2, alphaP 1 3]

@[expose] def swapIdx : Fin 4 → Fin 4 → Fin 4 :=
  ![![2, 3, 0, 1], ![3, 2, 1, 0], ![3, 2, 1, 0], ![2, 3, 0, 1]]

@[expose] def partner : Fin 4 → Fin 4 := ![1, 0, 3, 2]

theorem swap_facts_V : ∀ p m : Fin 4,
    (∃ t : Fin 4, swapP p * vA m * (swapP p)⁻¹ = vElem (swapIdx p m) t) ∧
      ∃ t : Fin 4, swapP p * vB m * (swapP p)⁻¹ = vElem (swapIdx p m) t := by
  decide +kernel

theorem swap_facts_P0 : ∀ p : Fin 4,
    (∃ a b : Fin 3, swapP p * x * (swapP p)⁻¹ = x ^ (a : ℕ) * y ^ (b : ℕ)) ∧
      ∃ a b : Fin 3, swapP p * y * (swapP p)⁻¹ = x ^ (a : ℕ) * y ^ (b : ℕ) := by
  decide +kernel

theorem cross_facts : ∀ k l : Fin 4, (k.val < 2 ↔ 2 ≤ l.val) → ∃ p : Fin 4,
    ((pairFst p = k ∧ pairSnd p = l) ∨ (pairFst p = l ∧ pairSnd p = k)) ∧
      swapIdx p k = l ∧ swapIdx p l = k ∧ swapIdx p (partner k) = partner l ∧
      swapIdx p (partner l) = partner k := by
  decide

theorem partner_cases : ∀ k : Fin 4, (k, partner k) = (0, 1) ∨ (k, partner k) = (2, 3) ∨
    (partner k, k) = (0, 1) ∨ (partner k, k) = (2, 3) := by
  decide

theorem eq_partner : ∀ k l : Fin 4, k ≠ l → ¬ (k.val < 2 ↔ 2 ≤ l.val) → l = partner k := by
  decide

theorem lines_lt_two : ∀ k : Fin 4, k.val < 2 → k = 0 ∨ k = 1 := by
  decide

theorem lines_ge_two : ∀ k : Fin 4, ¬ k.val < 2 → k = 2 ∨ k = 3 := by
  decide


@[expose] def alphaE (k l : Fin 4) : G22 :=
  vAE k * vAE l * vBE k * vBE l * vAE k * vAE l * vBE k

@[expose] def betaE (k l : Fin 4) : G22 :=
  vAE k * vBE l * vBE k * vAE l * vAE k * vBE l * vBE k

@[expose] def swapE : Fin 4 → G22 := ![alphaE 0 2, betaE 0 3, betaE 1 2, alphaE 1 3]

theorem coe_swapE (p : Fin 4) : (swapE p : Perm (Fin 22)) = swapP p := by
  fin_cases p <;> rfl

theorem gens_mem_sup (k l : Fin 4) : vAE k ∈ V k ⊔ V l ∧ vBE k ∈ V k ⊔ V l ∧
    vAE l ∈ V k ⊔ V l ∧ vBE l ∈ V k ⊔ V l :=
  ⟨Subgroup.mem_sup_left (mem_V_iff.mpr (Or.inr (Or.inl rfl))),
    Subgroup.mem_sup_left (mem_V_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))),
    Subgroup.mem_sup_right (mem_V_iff.mpr (Or.inr (Or.inl rfl))),
    Subgroup.mem_sup_right (mem_V_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))⟩

theorem swapE_mem (p : Fin 4) : swapE p ∈ V (pairFst p) ⊔ V (pairSnd p) := by
  have ha : ∀ k l : Fin 4, alphaE k l ∈ V k ⊔ V l := fun k l => by
    obtain ⟨a, b, a', b'⟩ := gens_mem_sup k l
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem a a') b) b') a) a') b
  have hb : ∀ k l : Fin 4, betaE k l ∈ V k ⊔ V l := fun k l => by
    obtain ⟨a, b, a', b'⟩ := gens_mem_sup k l
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem a b') b) a') a) b') b
  fin_cases p
  · exact ha 0 2
  · exact hb 0 3
  · exact hb 1 2
  · exact ha 1 3

theorem swapE_mem_normalizer (p : Fin 4) : swapE p ∈ Subgroup.normalizer (P0 : Set G22) := by
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd⟩⟩ := swap_facts_P0 p
  refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
  rintro _ (rfl | rfl)
  · have he : swapE p * E.a * (swapE p)⁻¹ = X ^ (a : ℕ) * Y ^ (b : ℕ) := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_swapE, Subgroup.coe_mul,
        Subgroup.coe_pow, Subgroup.coe_pow]
      exact hab
    rw [he]
    exact mul_mem (pow_mem X_mem_P0 _) (pow_mem Y_mem_P0 _)
  · have he : swapE p * E.b * (swapE p)⁻¹ = X ^ (c : ℕ) * Y ^ (d : ℕ) := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_swapE, Subgroup.coe_mul,
        Subgroup.coe_pow, Subgroup.coe_pow]
      exact hcd
    rw [he]
    exact mul_mem (pow_mem X_mem_P0 _) (pow_mem Y_mem_P0 _)

theorem map_swap (p m : Fin 4) :
    V (swapIdx p m) = (V m).map (MulAut.conj (swapE p)).toMonoidHom := by
  obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ := swap_facts_V p m
  refine eq_map_conj_of_forall (conj_mem_of_mem_kleinFour ?_ ?_) (by rw [card_V, card_V])
  · refine vElem_mem _ t ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_swapE]
    exact ht
  · refine vElem_mem _ t' ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_swapE]
    exact ht'

theorem exists_swap (k l k' l' : Fin 4)
    (h : k' = partner k ∧ l' = partner l ∧ (k.val < 2 ↔ 2 ≤ l.val)) :
    ∃ n ∈ V k ⊔ V l, n ∈ Subgroup.normalizer (P0 : Set G22) ∧
      V l = (V k).map (MulAut.conj n).toMonoidHom ∧ V k = (V l).map (MulAut.conj n).toMonoidHom ∧
      V l' = (V k').map (MulAut.conj n).toMonoidHom ∧
      V k' = (V l').map (MulAut.conj n).toMonoidHom := by
  obtain ⟨rfl, rfl, hkl⟩ := h
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := cross_facts k l hkl
  refine ⟨swapE p, ?_, swapE_mem_normalizer p, ?_, ?_, ?_, ?_⟩
  · have hmem := swapE_mem p
    rcases hp with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · rwa [hf, hs] at hmem
    · rwa [hf, hs, sup_comm] at hmem
  · rw [← map_swap p k, h1]
  · rw [← map_swap p l, h2]
  · rw [← map_swap p (partner k), h3]
  · rw [← map_swap p (partner l), h4]

theorem not_le_of_cross {Y : Subgroup G22} (hY3 : ¬ 3 ∣ Nat.card Y) {i j : Fin 4}
    (hi : i.val < 2) (hj : 2 ≤ j.val) (hVi : V i ≤ Y) (hVj : V j ≤ Y) : False := by
  have hA : ∀ k, vAE k ∈ V k := fun k => mem_V_iff.mpr (Or.inr (Or.inl rfl))
  have hmem : (vAE i * vAE j) ^ 2 ∈ Y := pow_mem (mul_mem (hVi (hA i)) (hVj (hA j))) 2
  obtain ⟨h3, h1⟩ := nonhexad_facts i j hi hj
  have ho : orderOf ((vAE i * vAE j) ^ 2) = 3 :=
    orderOf_eq_prime (Subtype.ext h3) (fun h => h1 (congrArg Subtype.val h))
  exact hY3 (ho ▸ Subgroup.orderOf_dvd_natCard Y hmem)

theorem le_of_forall_V_le
    {U M : Subgroup G22} (h3 : ¬ 3 ∣ Nat.card U) (hP : P0 ≤ Subgroup.normalizer (U : Set G22))
    (hM : ∀ i, V i ≤ U → V i ≤ M) : U ≤ M :=
  (le_iSup_inf h3 hP).trans (iSup_le fun i => by
    rcases inf_centralizer_cases h3 hP i with h | h
    · rw [h]
      exact bot_le
    · rw [h]
      exact hM i (h ▸ inf_le_left))

theorem invTwo_cases
    {H U : Subgroup G22} (hU : InvTwo P0 H U) :
    U = ⊥ ∨ (∃ k, U = V k) ∨ U = V 0 ⊔ V 1 ∨ U = V 2 ⊔ V 3 := by
  obtain ⟨-, hP, hU2⟩ := hU
  have hU3 := not_three_dvd_card_of_isPGroup hU2
  have gen := fun M => le_of_forall_V_le (M := M) hU3 hP
  have h16 : ∀ {i j : Fin 4}, ((i, j) = (0, 1) ∨ (i, j) = (2, 3)) →
      ¬ 3 ∣ Nat.card ↥(V i ⊔ V j) := fun hij => by
    rw [(hexad_pair hij).2.2.1]
    norm_num
  rcases le_hexad hU3 hP with hX | hX
  · have w2 : ¬ V 2 ≤ U := fun h => not_le_of_cross (h16 (Or.inl rfl)) (i := 0) (j := 2)
      (by decide) (by decide) le_sup_left (h.trans hX)
    have w3 : ¬ V 3 ≤ U := fun h => not_le_of_cross (h16 (Or.inl rfl)) (i := 0) (j := 3)
      (by decide) (by decide) le_sup_left (h.trans hX)
    by_cases v0 : V 0 ≤ U <;> by_cases v1 : V 1 ≤ U
    · exact Or.inr (Or.inr (Or.inl (le_antisymm hX (sup_le v0 v1))))
    · refine Or.inr (Or.inl ⟨0, le_antisymm (gen _ fun i hi => ?_) v0⟩)
      fin_cases i
      · exact le_rfl
      · exact absurd hi v1
      · exact absurd hi w2
      · exact absurd hi w3
    · refine Or.inr (Or.inl ⟨1, le_antisymm (gen _ fun i hi => ?_) v1⟩)
      fin_cases i
      · exact absurd hi v0
      · exact le_rfl
      · exact absurd hi w2
      · exact absurd hi w3
    · refine Or.inl (eq_bot_iff.mpr (gen _ fun i hi => ?_))
      fin_cases i
      · exact absurd hi v0
      · exact absurd hi v1
      · exact absurd hi w2
      · exact absurd hi w3
  · have w0 : ¬ V 0 ≤ U := fun h => not_le_of_cross (h16 (Or.inr rfl)) (i := 0) (j := 2)
      (by decide) (by decide) (h.trans hX) le_sup_left
    have w1 : ¬ V 1 ≤ U := fun h => not_le_of_cross (h16 (Or.inr rfl)) (i := 1) (j := 2)
      (by decide) (by decide) (h.trans hX) le_sup_left
    by_cases v2 : V 2 ≤ U <;> by_cases v3 : V 3 ≤ U
    · exact Or.inr (Or.inr (Or.inr (le_antisymm hX (sup_le v2 v3))))
    · refine Or.inr (Or.inl ⟨2, le_antisymm (gen _ fun i hi => ?_) v2⟩)
      fin_cases i
      · exact absurd hi w0
      · exact absurd hi w1
      · exact le_rfl
      · exact absurd hi v3
    · refine Or.inr (Or.inl ⟨3, le_antisymm (gen _ fun i hi => ?_) v3⟩)
      fin_cases i
      · exact absurd hi w0
      · exact absurd hi w1
      · exact absurd hi v2
      · exact le_rfl
    · refine Or.inl (eq_bot_iff.mpr (gen _ fun i hi => ?_))
      fin_cases i
      · exact absurd hi w0
      · exact absurd hi w1
      · exact absurd hi v2
      · exact absurd hi v3

theorem not_maximal_of_partner {H : Subgroup G22} {k l : Fin 4} (hkl : l = partner k)
    (hk : V k ≤ H) (hl : V l ≤ H) : ¬ Maximal (InvTwo P0 H) (V k) := by
  subst hkl
  have key : ∀ {i j : Fin 4}, ((i, j) = (0, 1) ∨ (i, j) = (2, 3)) → V i ⊔ V j ≤ H →
      V k ≤ V i ⊔ V j → ¬ Maximal (InvTwo P0 H) (V k) := by
    intro i j hij hX hle hmax
    obtain ⟨-, -, hcard, -, hN⟩ := hexad_pair hij
    have h := Subgroup.card_le_of_le (hmax.2 ⟨hX, hN, IsPGroup.of_card (n := 4)
      (by rw [hcard]; norm_num)⟩ hle)
    rw [hcard, card_V] at h
    norm_num at h
  rcases partner_cases k with h | h | h | h
  · exact key (Or.inl h) (sup_le hk hl) le_sup_left
  · exact key (Or.inr h) (sup_le hk hl) le_sup_left
  · exact key (Or.inl h) (sup_le hl hk) le_sup_right
  · exact key (Or.inr h) (sup_le hl hk) le_sup_right

theorem not_maximal_of_cross {H : Subgroup G22} {k l : Fin 4} (hkl : k.val < 2 ↔ 2 ≤ l.val)
    (hk : V k ≤ H) (hl : V l ≤ H) (hl' : V (partner l) ≤ H) :
    ¬ Maximal (InvTwo P0 H) (V k) := by
  obtain ⟨n, hn, -, -, -, -, hpk⟩ := exists_swap k l (partner k) (partner l) ⟨rfl, rfl, hkl⟩
  have hnH : n ∈ H := sup_le hk hl hn
  refine not_maximal_of_partner rfl hk ?_
  rw [hpk]
  rintro _ ⟨u, hu, rfl⟩
  exact mul_mem (mul_mem hnH (hl' hu)) (inv_mem hnH)

theorem le_hexad_of_maximal {H : Subgroup G22} {k : Fin 4} (hS : Maximal (InvTwo P0 H) (V k)) :
    (V 0 ⊔ V 1 ≤ H → V k ≤ V 0 ⊔ V 1) ∧ (V 2 ⊔ V 3 ≤ H → V k ≤ V 2 ⊔ V 3) := by
  constructor
  · intro hX
    by_cases hk : k.val < 2
    · rcases lines_lt_two k hk with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact absurd hS (not_maximal_of_cross (l := 0) (iff_of_false hk (by decide)) hS.1.1
        (le_sup_left.trans hX) (le_sup_right.trans hX))
  · intro hX
    by_cases hk : k.val < 2
    · exact absurd hS (not_maximal_of_cross (l := 2) (iff_of_true hk (by decide)) hS.1.1
        (le_sup_left.trans hX) (le_sup_right.trans hX))
    · rcases lines_ge_two k hk with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right

theorem exists_conj_four {H : Subgroup G22} {k l : Fin 4} (hS : Maximal (InvTwo P0 H) (V k))
    (hT : Maximal (InvTwo P0 H) (V l)) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (P0 : Set G22), V l = (V k).map (MulAut.conj n).toMonoidHom := by
  by_cases hkl : k = l
  · subst hkl
    exact exists_conj_of_le hS hT (Or.inl le_rfl)
  by_cases hc : k.val < 2 ↔ 2 ≤ l.val
  · obtain ⟨n, hn, hnN, hnl, -⟩ := exists_swap k l (partner k) (partner l) ⟨rfl, rfl, hc⟩
    exact ⟨n, ⟨sup_le hS.1.1 hT.1.1 hn, hnN⟩, hnl⟩
  · exact absurd hS (not_maximal_of_partner (eq_partner k l hkl hc) hS.1.1 hT.1.1)

theorem exists_conj_hexad {H : Subgroup G22} (h0 : V 0 ⊔ V 1 ≤ H) (h1 : V 2 ⊔ V 3 ≤ H) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (P0 : Set G22),
      V 2 ⊔ V 3 = (V 0 ⊔ V 1).map (MulAut.conj n).toMonoidHom ∧
        V 0 ⊔ V 1 = (V 2 ⊔ V 3).map (MulAut.conj n).toMonoidHom := by
  obtain ⟨n, -, hnN, e2, e0, e3, e1⟩ := exists_swap 0 2 1 3 (by decide)
  have hH : H = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← Res5Gen.iSup_V_eq_top]
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left.trans h0
    · exact le_sup_right.trans h0
    · exact le_sup_left.trans h1
    · exact le_sup_right.trans h1
  refine ⟨n, ⟨hH ▸ Subgroup.mem_top n, hnN⟩, ?_, ?_⟩
  · rw [Subgroup.map_sup, ← e2, ← e3]
  · rw [Subgroup.map_sup, ← e0, ← e1]

end ModelM22

theorem etrans_M22 :
    ETrans CFSG.RankThree.PartTwo.KFacts.KP4.G22 CFSG.RankThree.PartTwo.KFacts.KP4.P0 := by
  intro H _ _ S T hS hT
  rcases ModelM22.invTwo_cases hS.1 with rfl | ⟨k, rfl⟩ | rfl | rfl <;>
    rcases ModelM22.invTwo_cases hT.1 with rfl | ⟨l, rfl⟩ | rfl | rfl
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  · exact exists_conj_of_le hS hT (Or.inl bot_le)
  · exact exists_conj_of_le hS hT (Or.inr bot_le)
  · exact ModelM22.exists_conj_four hS hT
  · exact exists_conj_of_le hS hT (Or.inl ((ModelM22.le_hexad_of_maximal hS).1 hT.1.1))
  · exact exists_conj_of_le hS hT (Or.inl ((ModelM22.le_hexad_of_maximal hS).2 hT.1.1))
  · exact exists_conj_of_le hS hT (Or.inr bot_le)
  · exact exists_conj_of_le hS hT (Or.inr ((ModelM22.le_hexad_of_maximal hT).1 hS.1.1))
  · exact exists_conj_of_le hS hT (Or.inl le_rfl)
  · obtain ⟨n, hn, h, -⟩ := ModelM22.exists_conj_hexad hS.1.1 hT.1.1
    exact ⟨n, hn, h⟩
  · exact exists_conj_of_le hS hT (Or.inr bot_le)
  · exact exists_conj_of_le hS hT (Or.inr ((ModelM22.le_hexad_of_maximal hT).2 hS.1.1))
  · obtain ⟨n, hn, -, h⟩ := ModelM22.exists_conj_hexad hT.1.1 hS.1.1
    exact ⟨n, hn, h⟩
  · exact exists_conj_of_le hS hT (Or.inl le_rfl)

end CFSG.RankThree.PartTwo.Sec14.Wales1411W
