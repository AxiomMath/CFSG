module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.Background.E2TwoLieQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement MatrixGroups

namespace E2

theorem isQuasisimple_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  have hperf : Group.IsPerfect X := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator X := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  have hsimple : IsSimpleGroup (X ⧸ (⊥ : Subgroup X)) :=
    (QuotientGroup.quotientBot (G := X)).isSimpleGroup
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient ⊥ bot_le hperf hsimple
    ⟨QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab (by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_bot] at h
      exact inv_mul_eq_one.mp h)⟩

theorem exists_noncomm_of_isSimpleGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h2 : 2 ∣ Nat.card X) (hgt : 2 < Nat.card X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hN : (Subgroup.zpowers g).Normal := by
    constructor
    intro n hn x
    have : x * n * x⁻¹ = n := by rw [hall x n, mul_inv_cancel_right]
    rw [this]
    exact hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h | h
  · have hg1 : g = 1 := by
      have : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have hc : Nat.card (Subgroup.zpowers g) = Nat.card X := by
      rw [h, Subgroup.card_top]
    rw [Nat.card_zpowers, hg] at hc
    omega

theorem isPSL_two_of_mulEquiv_SL2' {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    {k : ℕ} (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k) (e : X ≃* SL(2, F)) : IsPSL 2 2 k X := by
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have hk4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq CFSG.Quasithin.Vol2.KGNat.center_SL2_eq_bot).trans
      QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, F, inferInstance,
    inferInstance, hF, ⟨e.trans (ePSL.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F))⟩⟩
  · have := congrArg Prod.snd h
    simp only at this
    omega
  · have := congrArg Prod.snd h
    simp only at this
    omega

theorem card_SL2 {F : Type} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)]
  have hI : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
  rw [hI, Finset.prod_singleton]
  norm_num

variable {W : Type} [CommGroup W]

theorem card_of_isL2Natural_one {L : Subgroup (MulAut W)} {C : Subgroup W}
    (h : IsL2Natural L C 1) : Nat.card L = 6 := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  rw [Nat.card_congr e.toEquiv, card_SL2, Nat.card_eq_fintype_card, hF]
  norm_num

theorem sixty_le_card_of_block {L : Subgroup (MulAut W)} {C : Subgroup W}
    (h : (∃ m : ℕ, IsL2Natural L C m) ∨ IsA5Module L) (hne : ¬ IsL2Natural L C 1) :
    60 ≤ Nat.card L := by
  rcases h with ⟨m, hm⟩ | ⟨θ, -⟩
  · have hm2 : 2 ≤ m := by
      have h1 := hm.1
      by_contra hlt
      have : m = 1 := by omega
      exact hne (this ▸ hm)
    obtain ⟨-, F, _, _, hF, e, -⟩ := hm
    rw [Nat.card_congr e.toEquiv, card_SL2, Nat.card_eq_fintype_card, hF]
    have h4 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h16 : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
    calc 60 = 4 * (4 ^ 2 - 1) := by norm_num
      _ ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
        Nat.mul_le_mul h4 (Nat.sub_le_sub_right (by nlinarith) 1)
  · rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem exists_simple_normal_of_block {L : Subgroup (MulAut W)}
    {C : Subgroup W} (h : (∃ m : ℕ, IsL2Natural L C m) ∨ IsA5Module L)
    (hne : ¬ IsL2Natural L C 1) :
    ∃ S : Subgroup (MulAut W), S ≤ L ∧ (S.subgroupOf L).Normal ∧ IsSimpleGroup ↥S ∧
      (∃ a b : ↥S, a * b ≠ b * a) ∧ ∃ k : ℕ, 2 ≤ k ∧ IsE22LieType k ↥S := by
  rcases h with ⟨m, hm⟩ | ⟨θ, -⟩
  · have hm2 : 2 ≤ m := by
      have h1 := hm.1
      by_contra hlt
      have : m = 1 := by omega
      exact hne (this ▸ hm)
    obtain ⟨-, F, _, _, hF, e, -⟩ := hm
    have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hF]
    have hPSL : IsPSL 2 2 m ↥L := isPSL_two_of_mulEquiv_SL2' hF' hm2 e
    have hsimp : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m hPSL).2
    have hcard : Nat.card ↥L = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_SL2, hF']
    have h4 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hfin : Finite ↥L := by
      apply Nat.finite_of_card_ne_zero
      rw [hcard]
      exact Nat.mul_ne_zero (by positivity) (by
        have : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
        omega)
    have h2 : 2 ∣ Nat.card ↥L := by
      rw [hcard]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have hgt : 2 < Nat.card ↥L := by
      rw [hcard]
      have : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
      have : 15 ≤ (2 ^ m) ^ 2 - 1 := by omega
      nlinarith
    refine ⟨L, le_rfl, ?_, hsimp, exists_noncomm_of_isSimpleGroup h2 hgt, m, hm2,
      Or.inl ⟨hm2, Or.inl hPSL⟩⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  ·
    set A : Subgroup ↥L := (alternatingGroup (Fin 5)).comap θ.toMonoidHom with hA
    have hAn : A.Normal := Subgroup.Normal.comap inferInstance _
    set S : Subgroup (MulAut W) := A.map L.subtype with hS
    have hSL : S ≤ L := Subgroup.map_subtype_le A
    have hSA : S.subgroupOf L = A :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective A
    have eA : ↥A ≃* alternatingGroup (Fin 5) :=
      (θ.subgroupMap A).trans (MulEquiv.subgroupCongr (by
        rw [hA]
        exact Subgroup.map_comap_eq_self_of_surjective (f := θ.toMonoidHom) θ.surjective _))
    have eS : ↥S ≃* alternatingGroup (Fin 5) :=
      (A.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eA
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 2 2) (Or.inl (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num))
    have hPSL : IsPSL 2 2 2 ↥S :=
      ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
        inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num),
        ⟨eS.trans e5.symm⟩⟩
    have hsimp : IsSimpleGroup ↥S := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 hPSL).2
    have hcard : Nat.card ↥S = 60 := by
      rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have hfin : Finite ↥S := by
      apply Nat.finite_of_card_ne_zero
      rw [hcard]
      norm_num
    refine ⟨S, hSL, ?_, hsimp, exists_noncomm_of_isSimpleGroup (by rw [hcard]; norm_num)
      (by rw [hcard]; norm_num), 2, le_rfl, Or.inl ⟨le_rfl, Or.inl hPSL⟩⟩
    rw [hSA]
    exact hAn

end E2

end CFSG.Quasithin
