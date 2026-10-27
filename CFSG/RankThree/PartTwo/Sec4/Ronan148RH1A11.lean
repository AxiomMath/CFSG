module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open Equiv Equiv.Perm

section Move

open scoped Pointwise

theorem moves_map {X : Type} [Group X] {E₀ : Subgroup X} (φ : MulAut X)
    (hmv : ∀ s ∈ E₀, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (E₀ : Set X),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set X)) :
    ∀ s ∈ E₀.map φ.toMonoidHom, s ≠ 1 → ∃ n ∈ Subgroup.normalizer
      ((E₀.map φ.toMonoidHom : Subgroup X) : Set X),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set X) := by
  rintro _ ⟨s', hs', rfl⟩ hs1
  have hs'1 : s' ≠ 1 := by
    rintro rfl
    exact hs1 (map_one _)
  obtain ⟨n, hn, hns⟩ := hmv s' hs' hs'1
  refine ⟨φ n, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨n, hn, rfl⟩
  · intro hn'
    apply hns
    have hZ : (Subgroup.zpowers s').map φ.toMonoidHom =
        Subgroup.zpowers (φ.toMonoidHom s') := MonoidHom.map_zpowers _ s'
    rw [← hZ, ← Subgroup.map_equiv_normalizer_eq] at hn'
    obtain ⟨m, hm, hmn⟩ := hn'
    rwa [φ.injective hmn] at hm

theorem card_a11 : Nat.card A11 = 19958400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem e27Move_a11 (A : Subgroup A11) (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (s : A11) (hs : s ∈ A) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (A : Set A11), n ∉ Subgroup.normalizer
      ((Subgroup.zpowers s : Subgroup A11) : Set A11) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (Nat.card A11).factorization 3 = 4 := by
    rw [card_a11]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show (19958400 : ℕ) = 3 ^ 4 * 246400 by norm_num) (by norm_num)
  let Q : Sylow 3 A11 := Sylow.ofCard a11P0 (by rw [a11P0_spec.1, h3]; norm_num)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  haveI : Finite (Sylow 3 A11) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A11 Q P
  have hPg : (P : Subgroup A11) = a11P0.map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun R : Sylow 3 A11 => (R : Subgroup A11)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    exact h.symm
  set A' : Subgroup A11 := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hA'P : A' ≤ a11P0 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hAP hx
    rw [hPg] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hxy : (MulAut.conj g⁻¹).toMonoidHom x = y := by
      rw [← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hxy]
    exact hy
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' := Ronan148S.isElemAbelian_map _ hA
  have hA'c : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hA27]
  have hA'0 := eq_a11A0_of_le hA'e hA'c hA'P
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id A11 := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hAeq : A = a11A0.map (MulAut.conj g).toMonoidHom := by
    rw [← hA'0, hA', Subgroup.map_map, hcomp, Subgroup.map_id]
  rw [hAeq] at hs ⊢
  exact moves_map (MulAut.conj g) a11_move s hs hs1

end Move

section Row


theorem a11t_comm
    (i j : Fin 3) :
    a11t * (a11c1 ^ (i : ℕ) * a11c2 ^ (j : ℕ)) = a11c1 ^ (i : ℕ) * a11c2 ^ (j : ℕ) * a11t := by
  revert i j
  decide

theorem a11_orderChecks
    :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 19958400 →
      19958400 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 19958400 →
      19958400 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 10) (by norm_num) (by decide +kernel)

theorem row427_a11
    {S : Type} [Group S] [Finite S] (eS : S ≃* A11) : Row427 S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK htype
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hcardL : Nat.card (↥L ⧸ Subgroup.center ↥L) = 19958400 :=
    (Nat.card_congr (e.trans eS).toEquiv).trans card_a11
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_card (sectionFourHyp_subgroup hG L) hL.1 hZ3 hcardL a11_orderChecks.1
      a11_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  let eL : ↥L ≃* A11 := (quotCenterEquivOfEqBot hZ).trans (e.trans eS)
  have hcube : CubeInner ↥L := cubeInner_of_mulEquiv eL
    (cubeInner_of_not_three_dvd_card_outer (not_three_dvd_outer_alternatingGroup (by norm_num)))
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  let ι : A11 →* G := L.subtype.comp eL.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp eL.symm.injective
  have hιL : ∀ x : A11, ι x ∈ L := fun x => (eL.symm x).2
  have hZ' : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1 := by
    intro x hxL hxC
    have hc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hFF' : a11F.map ι ≤ a11A0.map ι := Subgroup.map_mono le_sup_left
  have hF'L : a11A0.map ι ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact hιL x
  have htF : ∀ f ∈ a11F.map ι, ι a11t * f = f * ι a11t := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, j, hi, hj, rfl⟩ := mem_a11F hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact a11t_comm ⟨i, hi⟩ ⟨j, hj⟩
  have hC : ∀ w ∈ Subgroup.centralizer (L : Set G), w ^ 3 = 1 → w = 1 := fun w hw hw3 =>
    eq_one_of_mem_centralizer_of_partTwo hEF hZ' hF'L hFF' (Ronan148S.isElemAbelian_map _ a11F_e9.1)
      (by rw [Subgroup.card_map_of_injective hι, a11F_e9.2])
      (Ronan148S.isElemAbelian_map _ a11A0_e27.1)
      (by rw [Subgroup.card_map_of_injective hι, a11A0_e27.2]) (hιL a11t)
      (by rw [Ne, map_eq_one_iff ι hι]; decide) (by rw [← map_pow]; rw [show a11t ^ 2 = 1 by decide, map_one])
      htF hw hw3
  have hAL : A ≤ L := le_of_inner_of_centralizer hZ hcube hAN hA.1 hC
  set A₁ : Subgroup A11 := (A.subgroupOf L).map eL.toMonoidHom with hA₁
  have hA₁e : CFSG.Assembly.IsElemAbelian 3 A₁ :=
    Ronan148S.isElemAbelian_map _ (isElemAbelian_comap L.subtype L.subtype_injective hA.1)
  have hA₁c : Nat.card A₁ = 27 := by
    rw [hA₁, Subgroup.card_map_of_injective eL.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA.2]
  have hdL : d ∈ L := hAL hdA
  have hd₁ : eL ⟨d, hdL⟩ ∈ A₁ := ⟨⟨d, hdL⟩, hdA, rfl⟩
  have hd₁1 : eL ⟨d, hdL⟩ ≠ 1 := by
    rw [Ne, map_eq_one_iff _ eL.injective]
    intro h
    exact hd1 (congrArg Subtype.val h)
  obtain ⟨n, hn, hnd⟩ := e27Move_a11 A₁ hA₁e hA₁c _ hd₁ hd₁1
  have hnL : eL.symm n ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    have h := Subgroup.map_equiv_normalizer_eq (A.subgroupOf L) eL
    have hn' : n ∈ ((Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
        eL.toMonoidHom) := by
      rw [h]
      exact hn
    obtain ⟨m, hm, hmn⟩ := hn'
    rw [← hmn]
    simpa using hm
  have hnG : ((eL.symm n : ↥L) : G) ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_subgroupOf hAL hnL
  have hnd' := hN hnG
  apply hnd
  have h1 : eL.symm n ∈ Subgroup.normalizer
      (((Subgroup.zpowers d).subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hdL) hnd'
  rw [zpowers_subgroupOf hdL] at h1
  have h2 := Subgroup.map_equiv_normalizer_eq (Subgroup.zpowers (⟨d, hdL⟩ : ↥L)) eL
  rw [MonoidHom.map_zpowers] at h2
  have h3 : eL (eL.symm n) ∈ (Subgroup.normalizer
      ((Subgroup.zpowers (⟨d, hdL⟩ : ↥L) : Subgroup ↥L) : Set ↥L)).map eL.toMonoidHom :=
    ⟨_, h1, rfl⟩
  rw [h2] at h3
  simpa using h3

theorem rowOf427_alt11
    : RowOf427 (alternatingGroup (Fin 11)) := by
  intro S _ _ _ _ ⟨e⟩
  exact row427_a11 e

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
