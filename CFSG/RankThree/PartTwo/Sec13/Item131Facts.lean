module

public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem isPerfect_subgroupOf_lBar (h : Sec13Data G A c L) :
    Group.IsPerfect ((Sec12.lBar c L).subgroupOf (lBarA c L A)) := by
  have := isPerfect_lBar h
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective

theorem subgroupOf_lBar_ne_bot (h : Sec13Data G A c L) :
    (Sec12.lBar c L).subgroupOf (lBarA c L A) ≠ ⊥ := by
  intro hbot
  apply lBar_ne_bot h
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, lBar_le_lBarA hx⟩ : lBarA c L A) ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem false_of_isSolvable (h : Sec13Data G A c L) {S : Type*} [Group S]
    (hS : Group.IsSolvable S) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) : False := by
  have : Group.IsSolvable (lBarA c L A) :=
    Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar h
  have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot _).mpr (subgroupOf_lBar_ne_bot h)
  exact Group.IsPerfect.not_isSolvable Λ inferInstance

theorem facts_of_prod (h : Sec13Data G A c L) {S : Type*} [Group S] (hS : Group.IsPerfect S)
    (hZ : Subgroup.center S = ⊥) (φ : lBarA c L A ≃* Multiplicative (ZMod 3) × S) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* S) :=
  ⟨not_mem_of_center_inf_commutator h φ (by rw [hZ, bot_inf_eq]), card_inf_eq_nine h hS φ,
    nonempty_lBarA_equiv_prod h hS φ, nonempty_thetaQuot_equiv h hS φ⟩

theorem mem_of_isSLThreePiTwo (hSLC : SLTwoCenter) (h : Sec13Data G A c L)
    (hSL : Sec4.IsSLThreePiTwo (lBarA c L A)) : c ∈ L := by
  have := lBar_normal h
  have hle := hSLC (lBarA c L A) hSL _ this (isPerfect_subgroupOf_lBar h)
    (subgroupOf_lBar_ne_bot h)
  exact mem_of_mkC_mem h (hle (mkC_mem_center h))

theorem cases131 (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h : Sec13Data G A c L) :
    (c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      ((IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧
          (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
            Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
          Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)))) ∨
    (c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
      Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
    (c ∉ L ∧ Sec8.IsZ3PGLThreePi (lBarA c L A) ∧
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧ ∃ x ∈ A, Sec4.InducesTypeOn L x 3) ∨
    (c ∈ L ∧ (Sec4.IsSLThreePiTwo (lBarA c L A) ∨
      (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
        Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers c : Set G)))) := by
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
  rcases h131 G A c L h with ⟨hL3, hstar⟩ | ⟨hPGL, hstar, hx⟩ | ⟨⟨φ⟩, hstar⟩ | ⟨⟨φ⟩, hstar⟩ |
      ⟨⟨φ⟩, hstar⟩ | ⟨⟨φ⟩, hstar⟩ | ⟨h7, hH, -⟩
  ·
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hS, hZ⟩ := isPerfect_center_projSL p e he hq
      obtain ⟨hcL, h9, hprod, ⟨ψ⟩⟩ := facts_of_prod h hS hZ φ
      exact Or.inl ⟨hcL, h9, hprod, Or.inl ⟨⟨p, e, hp, he, Or.inl ⟨hq, ⟨ψ⟩⟩⟩, hstar⟩⟩
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hZ⟩ := isPerfect_center_projSU p e he hq hq2
        obtain ⟨hcL, h9, hprod, ⟨ψ⟩⟩ := facts_of_prod h hS hZ φ
        exact Or.inl ⟨hcL, h9, hprod, Or.inl ⟨⟨p, e, hp, he, Or.inr ⟨hq, ⟨ψ⟩⟩⟩, hstar⟩⟩
      · exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable h isSolvable_projSU_two φ
  ·
    obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
    refine Or.inr (Or.inr (Or.inl ⟨?_, ⟨π, p, f, K, inferInstance, hK, hq, ⟨φ⟩⟩, hstar, hx⟩))
    by_cases hq2 : 2 < p ^ f
    · exact not_mem_of_center_inf_commutator h φ
        (by rw [center_projImage_glPi hK hq hq2, bot_inf_eq])
    · exfalso
      have h2 : p ^ f = 2 := by
        have hf : f ≠ 0 := by have := hK.one_le; omega
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
      · change p ^ f % 3 = 1 at hq
        omega
  ·
    obtain ⟨hS, hZ⟩ := isPerfect_center_alt7
    obtain ⟨hcL, h9, hprod, ⟨ψ⟩⟩ := facts_of_prod h hS hZ φ
    exact Or.inl ⟨hcL, h9, hprod, Or.inr (Or.inl ⟨⟨ψ⟩, hstar⟩)⟩
  ·
    obtain ⟨hcL, h9, hprod, ⟨ψ⟩⟩ := facts_of_prod h hM22p hM22z φ
    exact Or.inl ⟨hcL, h9, hprod, Or.inr (Or.inr ⟨⟨ψ⟩, hstar⟩)⟩
  ·
    obtain ⟨hcL, h9, -, -⟩ := facts_of_prod h hM12p hM12z φ
    exact Or.inr (Or.inl ⟨hcL, h9, Or.inl ⟨φ⟩, hstar⟩)
  ·
    obtain ⟨hcL, h9, -, -⟩ := facts_of_prod h hJ2p hJ2z φ
    exact Or.inr (Or.inl ⟨hcL, h9, Or.inr ⟨φ⟩, hstar⟩)
  ·
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
    · rcases h7 with hSL | ⟨hHeis, -⟩
      · exact mem_of_isSLThreePiTwo hSLC h hSL
      · exact mem_of_isHeisCentral h hHeis
    · rcases h7 with hSL | ⟨hHeis, -⟩
      · exact Or.inl hSL
      · exact Or.inr ⟨hHeis, hH hHeis⟩

end CFSG.RankThree.PartTwo.Sec13
