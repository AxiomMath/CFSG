module

public import CFSG.RankThree.PartTwo.Sec13.Item131a
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item136Lift

public section

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem types_of_not_mem (h131a : Item131a) (hspor : SporadicModels131)
    (h : Sec13Data G A c L) (hcL : c ∉ L) :
    (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2)) ∧
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
    ∃ D : Subgroup G, D ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 9 := by
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
  have hAL : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) := isElemAbelian_inf_right h.isElemAbelian L
  rcases h131a G A c L h with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | hSL | ⟨hHeis, -⟩
  ·
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hS, hZ⟩ := isPerfect_center_projSL p e he hq
      obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod h hS hZ φ
      exact ⟨Or.inl ⟨p, e, hp, he, Or.inl ⟨hq, ⟨ψ⟩⟩⟩, center_eq_bot_of_mulEquiv ψ hZ,
        A ⊓ L, inf_le_right, hAL, h9⟩
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hZ⟩ := isPerfect_center_projSU p e he hq hq2
        obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod h hS hZ φ
        exact ⟨Or.inl ⟨p, e, hp, he, Or.inr ⟨hq, ⟨ψ⟩⟩⟩, center_eq_bot_of_mulEquiv ψ hZ,
          A ⊓ L, inf_le_right, hAL, h9⟩
      · exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable h isSolvable_projSU_two φ
  ·
    obtain ⟨hL3, hZ, D, hDL, hDe, hD9⟩ := facts_of_isZ3PGLThreePi h hPGL
    exact ⟨Or.inl hL3, hZ, D, hDL, hDe, hD9⟩
  ·
    obtain ⟨hS, hZ⟩ := isPerfect_center_alt7
    obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod h hS hZ φ
    exact ⟨Or.inr (Or.inl ⟨ψ⟩), center_eq_bot_of_mulEquiv ψ hZ, A ⊓ L, inf_le_right, hAL, h9⟩
  ·
    obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod h hM22p hM22z φ
    exact ⟨Or.inr (Or.inr (Or.inl ⟨ψ⟩)), center_eq_bot_of_mulEquiv ψ hM22z, A ⊓ L, inf_le_right,
      hAL, h9⟩
  ·
    obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod h hM12p hM12z φ
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ⟩))), center_eq_bot_of_mulEquiv ψ hM12z,
      A ⊓ L, inf_le_right, hAL, h9⟩
  ·
    obtain ⟨-, h9, -, ⟨ψ⟩⟩ := facts_of_prod h hJ2p hJ2z φ
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ⟩))), center_eq_bot_of_mulEquiv ψ hJ2z,
      A ⊓ L, inf_le_right, hAL, h9⟩
  · exact absurd (mem_of_isSLThreePiTwo slTwoCenter h hSL) hcL
  · exact absurd (mem_of_isHeisCentral h hHeis) hcL

theorem isSLThreePi_of_isSLThreePiTwo (h : Sec13Data G A c L)
    (hSL : Sec4.IsSLThreePiTwo (lBarA c L A)) :
    Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hΛn : Λ.Normal := lBar_normal h
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar h
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot h
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hΛL₀ : Λ = D.L₀ := le_antisymm (D.le_of_isPerfect hΛp) (D.le_of_normal hq2 hΛn hΛp hΛ1)
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  let e : L ⧸ aschbacherSolvableCore 3 L ≃* Sec4.slPi π 3 (p ^ f) K :=
    η.trans ((Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.trans
      ((MulEquiv.subgroupCongr hΛL₀).trans D.e))
  exact Sec4.isSLThreePi_of_equiv D.piField D.modThree e

theorem types_of_mem (h131a : Item131a) (hspor : SporadicModels131) (h : Sec13Data G A c L)
    (hcL : c ∈ L) :
    Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := hspor
  rcases h131a G A c L h with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | hSL | ⟨-, hty⟩
  · exfalso
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact not_mem_of_center_eq_bot_prod h (isPerfect_center_projSL p e he hq).2 φ hcL
    · by_cases hq2 : 2 < p ^ e
      · exact not_mem_of_center_eq_bot_prod h (isPerfect_center_projSU p e he hq hq2).2 φ hcL
      · have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable h isSolvable_projSU_two φ
  · exfalso
    obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
    by_cases hq2 : 2 < p ^ f
    · exact not_mem_of_center_eq_bot_prod h (center_projImage_glPi hK hq hq2) φ hcL
    · have hf : f ≠ 0 := by have := hK.one_le; omega
      have h2 : p ^ f = 2 := by
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
      · change p ^ f % 3 = 1 at hq
        omega
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h isPerfect_center_alt7.2 φ)
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h hM22z φ)
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h hM12z φ)
  · exact absurd hcL (not_mem_of_center_eq_bot_prod h hJ2z φ)
  · exact Or.inl (isSLThreePi_of_isSLThreePiTwo h hSL)
  · exact hty

theorem exists_exponent_three_card_nine_of_le {D : Subgroup G} (hDL : D ≤ L)
    (hDe : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∃ E : Subgroup (L ⧸ aschbacherSolvableCore 3 L), Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  set D' : Subgroup L := D.subgroupOf L with hD'
  have hD'9 : Nat.card D' = 9 := by
    rw [← hD9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hD'p : IsPGroup 3 D' := IsPGroup.of_card (n := 2) (by rw [hD'9]; norm_num)
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hD'p
  refine ⟨D'.map (QuotientGroup.mk' _), ?_, ?_⟩
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, ⟨d, hd, rfl⟩⟩
    apply Subtype.ext
    have hd3 : d ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hDe.2 _ (Subgroup.mem_subgroupOf.mp hd))
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hd3, map_one]
  · rw [card_map_eq_of_injOn _ hinj, hD'9]

end CFSG.RankThree.PartTwo.Sec13.ResProof
