module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Gen
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEU6
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8Inner
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFF4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)
open scoped commutatorElement

theorem pow_three_and_ne_one {S T : Type} [Group S] [Group T] (φ : S ≃* T) {s : S}
    (hs : orderOf s = 3) : φ s ^ 3 = 1 ∧ φ s ≠ 1 := by
  have hs3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  refine ⟨by rw [← map_pow, hs3, map_one], fun h => ?_⟩
  have : s = 1 := φ.injective (by rw [h, map_one])
  rw [this, orderOf_one] at hs
  norm_num at hs

theorem not_mem_commutator_centralizer_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S]
    (φ : S ≃* T) {s : S}
    (h : φ s ∉ ⁅Subgroup.centralizer ({φ s} : Set T), Subgroup.centralizer ({φ s} : Set T)⁆) :
    s ∉ ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆ := by
  intro hs
  apply h
  rw [← Ronan148S.map_centralizer_singleton_equiv φ s, ← Subgroup.map_commutator]
  exact ⟨s, hs, rfl⟩

theorem not_dvd_or_not_mem_commutator {G : Type} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {y : G} (hy : orderOf y = r) (hr2 : ¬ r ^ 2 ∣ Nat.card G)
    (hC : ∀ t : G, t * y = y * t → t ^ 3 = 1 → t ≠ 1 →
      t ∉ ⁅Subgroup.centralizer ({t} : Set G), Subgroup.centralizer ({t} : Set G)⁆)
    {s : G} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ¬ r ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) ∨
      s ∉ ⁅Subgroup.centralizer ({s} : Set G), Subgroup.centralizer ({s} : Set G)⁆ := by
  by_cases hd : r ∣ Nat.card (Subgroup.centralizer ({s} : Set G))
  · right
    obtain ⟨x, hx⟩ := RonanK429F.exists_conj_commute_of_dvd hr hy hr2 hd
    have hconj : (MulAut.conj x⁻¹) s = x⁻¹ * s * x := by
      rw [MulAut.conj_apply, inv_inv]
    have ht3 : (x⁻¹ * s * x) ^ 3 = 1 := by rw [← hconj, ← map_pow, hs3, map_one]
    have ht1 : x⁻¹ * s * x ≠ 1 := by
      rw [← hconj]
      intro h
      exact hs1 ((MulAut.conj x⁻¹).injective (by rw [h, map_one]))
    refine not_mem_commutator_centralizer_of_mulEquiv (MulAut.conj x⁻¹) ?_
    rw [hconj]
    exact hC _ hx ht3 ht1
  · exact Or.inl hd

theorem typeOrders_of_not_dvd {M B r c : ℕ}
    (hr : ∀ t ∈ typeOrders425 M B, t = 1080 ∨ r ∣ t) (hc : ¬ r ∣ c) :
    ∀ t ∈ typeOrders425 M B, t = 1080 ∨ ¬ t ∣ c := fun t ht =>
  (hr t ht).imp_right fun hrt htc => hc (hrt.trans htc)

theorem u62_not_five_seven (α : MulAut Item434SmallTwoIVU62.P6) (h3 : α ^ 3 = 1) (h1 : α ≠ 1)
    {g5 g7 : Item434SmallTwoIVU62.P6} (hg5 : α g5 = g5) (ho5 : orderOf g5 = 5)
    (hg7 : α g7 = g7) (ho7 : orderOf g7 = 7) : False := by
  obtain ⟨A, rfl⟩ := Item434SmallTwoIVU62.exists_conj6_eq_of_pow_three h3
  have hA3 := RonanK429E.U6.exists_pow_three_eq_scalar h3
  have hns : ∀ d : CFSG.GH74.Uniqueness.SU.SU5.F4c,
      RonanK429E.U6.matC (A : GL (Fin 6) Item434SmallTwoIVU62.F4) ≠ Matrix.scalar (Fin 6) d :=
    fun d h => h1 (RonanK429E.U6.conj6_eq_one_of_matC h)
  exact RonanK429E.U6.pow_three_ne_one_of_seven hns hg7 ho7
    (RonanK429E.U6.pow_three_eq_one_of_five hA3 hg5 ho5)

section Sp8

open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sp8E sp8E_pow_three)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8 (y0 e8 matH8 iota6 rho2)

theorem sp8_not_mem_commutator (t : H8) (ht : t * y0 = y0 * t) (h3 : t ^ 3 = 1) (h1 : t ≠ 1) :
    t ∉ ⁅Subgroup.centralizer ({t} : Set H8), Subgroup.centralizer ({t} : Set H8)⁆ := by
  have hE : sp8E ∉ iota6.range := by
    rintro ⟨g, hg⟩
    have h := congrArg (fun z => RonanK429F.bl e8 (matH8 z)) hg
    simp only [RonanK429F.Sp8.matH8_iota6, RonanK429F.Sp8.bl_emb6,
      RonanK429F.Sp8.bl_sp8E] at h
    exact (by decide : rho2 ≠ 1) (Matrix.fromBlocks_inj.mp h).2.2.2.symm
  have hle : ⁅Subgroup.centralizer ({sp8E} : Set H8), Subgroup.centralizer ({sp8E} : Set H8)⁆ ≤
      iota6.range :=
    Subgroup.commutator_le.mpr fun a ha b hb =>
      RonanK429F.Sp8.commutator_mem_range_iota6 a ha b hb
  rcases RonanK429F.Sp8.eq_of_commute_y0 t ht h3 with rfl | rfl | rfl
  · exact absurd rfl h1
  · exact fun hm => hE (hle hm)
  · rw [RonanK429H.centralizer_pow_of_pow_three sp8E_pow_three (Or.inr rfl)]
    intro hm
    apply hE
    have h4 : sp8E = (sp8E ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, sp8E_pow_three, one_mul, pow_one]
    rw [h4]
    exact pow_mem (hle hm) 2

end Sp8

section Om8

open CFSG.RankThree.PartTwo.Sec4.RonanK429F (Om8)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8 (y7 eO matO psiD rho)

theorem om8_not_mem_commutator (t : Om8) (ht : t * y7 = y7 * t) (h3 : t ^ 3 = 1) (h1 : t ≠ 1) :
    t ∉ ⁅Subgroup.centralizer ({t} : Set Om8), Subgroup.centralizer ({t} : Set Om8)⁆ := by
  have hT := RonanK429F.Om8.t_form ht h3 h1
  have hle : ⁅Subgroup.centralizer ({t} : Set Om8), Subgroup.centralizer ({t} : Set Om8)⁆ ≤
      psiD.range :=
    Subgroup.commutator_le.mpr fun a ha b hb =>
      RonanK429F.Om8.comm_mem_D (RonanK429F.Om8.isTForm_of hT) ha hb
  intro hm
  obtain ⟨P, hP⟩ := hle hm
  have h := congrArg (fun z => RonanK429F.bl eO (matO z)) hP
  have hPm : matO (psiD P) =
      RonanK429F.Om8.emb ((P : GL RonanK429F.Om8.ι6 (ZMod 2)) :
        Matrix RonanK429F.Om8.ι6 RonanK429F.Om8.ι6 (ZMod 2)) := rfl
  simp only [hPm, RonanK429F.Om8.bl_emb] at h
  rcases hT with h' | h'
  · rw [h'] at h
    exact (by decide : rho ≠ 1) (Matrix.fromBlocks_inj.mp h).2.2.2.symm
  · rw [h'] at h
    exact (by decide : rho ^ 2 ≠ 1) (Matrix.fromBlocks_inj.mp h).2.2.2.symm

end Om8

section Theta


theorem card_theta_quot_dvd_three_mul {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (hT : IsType425 (K ⧸ aschbacherSolvableCore 3 K)) :
    Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∧
      Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 3 * Nat.card (K ⧸ Subgroup.center K) := by
  have hθ : aschbacherSolvableCore 3 K ≤ Subgroup.center K :=
    Sec4.aschbacherSolvableCore_le_center hK
  have hcard : Nat.card (K ⧸ aschbacherSolvableCore 3 K) =
      Nat.card ((Subgroup.center K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) *
        Nat.card (K ⧸ Subgroup.center K) := by
    have e := QuotientGroup.quotientQuotientEquivQuotient
      (aschbacherSolvableCore 3 K) (Subgroup.center K) hθ
    rw [← Nat.card_congr e.toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hMbZ : (Subgroup.center K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) ≤
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
  have h3 : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3 :=
    card_center_of_isType425 (isQuasisimple_theta_quot hK) hT
  have hMb3 := Subgroup.card_dvd_of_le hMbZ
  rw [h3] at hMb3
  rw [hcard]
  exact ⟨Dvd.intro_left _ rfl, Nat.mul_dvd_mul_right hMb3 _⟩

end Theta

section Eight


theorem noCC425_of_lie_at' {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (h : ∀ s : S, orderOf s = 3 →
      (∃ M B : ℕ, Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M ∧ 0 < M ∧ M < B ^ 3 ∧
        ∀ t ∈ typeOrders425 M B, t = 1080 ∨ ¬ t ∣ Nat.card (Subgroup.centralizer ({s} : Set S))) ∨
      s ∉ ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆) :
    NoCC425 S := by
  intro s K hcc
  rcases h s hcc.orderOf_eq with ⟨M, B, hC, hM0, hB, hfree⟩ | hcomm
  · have hKC : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣
        Nat.card (Subgroup.centralizer ({s} : Set S)) :=
      (card_theta_quot_dvd K).trans (Subgroup.card_dvd_of_le hcc.le_centralizer)
    rcases hfree _ (card_mem_typeOrders425 (isQuasisimple_theta_quot hcc.isQuasisimple) hM0 hB
      hcc.isType (hKC.trans hC)) with h1 | h1
    · exact card_theta_ne_1080 hs hna idx he hcc h1
    · exact h1 hKC
  · exact noCQAt_of_not_mem_commutator hcomm K hcc.mem hcc.le_centralizer hcc.isQuasisimple
      hcc.isType

theorem kT2_eight_SU6 : RowOf425 (projSU 6 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : (LieTypeIndex.twistedA 5 ⟨2, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_twistedA (by norm_num) (by omega)
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  let φ : S ≃* Item434SmallTwoIVU62.P6 := e.trans Item434SmallTwoIVU62.u6Equiv
  refine noCC425_of_lie_at' hs hna ⟨_, hv⟩
    ⟨e.trans (Census.typeTwistedAGroupEquivProjSU 5 ⟨2, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩
    fun s hs3 => Or.inl ⟨27590492160, 3100, ?_, by norm_num, by norm_num, ?_⟩
  · rw [← RonanK429H.card_centralizer_mulEquiv φ s]
    exact (Subgroup.card_subgroup_dvd_card _).trans RonanK429E.U6.card_P6_dvd
  · have hlist : typeOrders425 27590492160 3100 = [1080, 7560, 1330560, 60480] := by
      decide +kernel
    intro t ht
    rw [hlist] at ht
    have h57 : ¬ (5 ∣ Nat.card (Subgroup.centralizer ({s} : Set S)) ∧
        7 ∣ Nat.card (Subgroup.centralizer ({s} : Set S))) := by
      rintro ⟨h5, h7⟩
      rw [← RonanK429H.card_centralizer_mulEquiv φ s] at h5 h7
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨g5, hg5⟩ := exists_prime_orderOf_dvd_card' 5 h5
      obtain ⟨g7, hg7⟩ := exists_prime_orderOf_dvd_card' 7 h7
      obtain ⟨hx3, hx1⟩ := pow_three_and_ne_one φ hs3
      have hα3 : MulAut.conj (φ s) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
      have hZ : Subgroup.center Item434SmallTwoIVU62.P6 = ⊥ := by
        haveI : IsSimpleGroup Item434SmallTwoIVU62.P6 := (MulEquiv.isSimpleGroup_congr φ).1 hs
        obtain ⟨a, b, hab⟩ := hna
        exact b3Lie_center_eq_bot ⟨φ a, φ b, fun h => hab (φ.injective (by
          rw [map_mul, map_mul, h]))⟩
      have hα1 : MulAut.conj (φ s) ≠ 1 := by
        intro h1
        apply hx1
        have hc : φ s ∈ Subgroup.center Item434SmallTwoIVU62.P6 := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun β : MulAut Item434SmallTwoIVU62.P6 => β g) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * φ s = φ s * g * (φ s)⁻¹ * φ s := by rw [this]
            _ = φ s * g := by group
        rwa [hZ, Subgroup.mem_bot] at hc
      have hfix : ∀ g : Subgroup.centralizer ({φ s} : Set Item434SmallTwoIVU62.P6),
          MulAut.conj (φ s) g = g := by
        intro g
        have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
        rw [MulAut.conj_apply, ← hg]
        group
      exact u62_not_five_seven _ hα3 hα1 (hfix g5) (by rw [Subgroup.orderOf_coe, hg5])
        (hfix g7) (by rw [Subgroup.orderOf_coe, hg7])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    all_goals
      right
      intro hd
      exact h57 ⟨(by norm_num : 5 ∣ _).trans hd, (by norm_num : 7 ∣ _).trans hd⟩

theorem kT2_eight_Sp6 : RowOf425 (projSp 3 (GaloisField 2 1)) := by
  obtain ⟨eB⟩ := Census.bridgeSp6Two _ (valid_B_of_three_le le_rfl le_rfl) rfl rfl
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  let φ : S ≃* CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 :=
    e.trans Item434SmallTwoIII.sp62Equiv
  refine noCC425_of_lie_at' hs hna _ ⟨e.trans eB.symm⟩
    fun s hs3 => Or.inl ⟨1451520, 114, ?_, by norm_num, by norm_num, ?_⟩
  · rw [← RonanK429H.card_centralizer_mulEquiv φ s,
      ← CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.card_H6]
    exact Subgroup.card_subgroup_dvd_card _
  · obtain ⟨hx3, hx1⟩ := pow_three_and_ne_one φ hs3
    refine typeOrders_of_not_dvd (r := 7) (by decide +kernel) ?_
    rw [← RonanK429H.card_centralizer_mulEquiv φ s]
    exact RonanK429E.not_dvd_card_centralizer_of_sylow (by norm_num) RonanK429E.Sp6.orderOf_y0
      RonanK429E.Sp6.not_sq_seven_dvd RonanK429E.Sp6.eq_one_of_commute_y0 hx3 hx1

theorem kT2_eight_OmegaPlus : RowOf425 (projOmegaPlus 4 (GaloisField 2 1)) := by
  have hv : (LieTypeIndex.D 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, id⟩
  obtain ⟨eB⟩ := Census.bridgeOmega8PlusTwo _ hv rfl rfl
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  let φ : S ≃* RonanK429E.O8.OM := e.trans RonanK429E.O8.projEquiv
  refine noCC425_of_lie_at' hs hna _ ⟨e.trans eB.symm⟩
    fun s hs3 => Or.inl ⟨174182400, 559, ?_, by norm_num, by norm_num, ?_⟩
  · rw [← RonanK429H.card_centralizer_mulEquiv φ s, ← RonanK429E.O8.card_OM]
    exact Subgroup.card_subgroup_dvd_card _
  · obtain ⟨hx3, hx1⟩ := pow_three_and_ne_one φ hs3
    refine typeOrders_of_not_dvd (r := 7) (by decide +kernel) ?_
    rw [← RonanK429H.card_centralizer_mulEquiv φ s]
    exact RonanK429E.not_dvd_card_centralizer_of_sylow (by norm_num) RonanK429E.O8.orderOf_y0
      RonanK429E.O8.not_sq_seven_dvd RonanK429E.O8.eq_one_of_commute_y0 hx3 hx1

theorem kT2_eight_Sp8 : RowOf425 (projSp 4 (GaloisField 2 1)) := by
  obtain ⟨eB⟩ := Census.bridgeSp8Two _ (valid_B_of_three_le (by norm_num) le_rfl) rfl rfl
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  let φ : S ≃* RonanK432.H8 := e.trans RonanK432.sp82Equiv
  refine noCC425_of_lie_at' hs hna _ ⟨e.trans eB.symm⟩ fun s hs3 => ?_
  obtain ⟨hx3, hx1⟩ := pow_three_and_ne_one φ hs3
  rcases not_dvd_or_not_mem_commutator (by norm_num) RonanK429F.Sp8.orderOf_y0
      RonanK429F.Sp8.not_sq_seven_dvd sp8_not_mem_commutator hx3 hx1 with h7 | hc
  · refine Or.inl ⟨47377612800, 3620, ?_, by norm_num, by norm_num, ?_⟩
    · rw [← RonanK429H.card_centralizer_mulEquiv φ s, ← RonanK429F.Sp8.card_H8]
      exact Subgroup.card_subgroup_dvd_card _
    · refine typeOrders_of_not_dvd (r := 7) (by decide +kernel) ?_
      rwa [← RonanK429H.card_centralizer_mulEquiv φ s]
  · exact Or.inr (not_mem_commutator_centralizer_of_mulEquiv φ hc)

theorem kT2_eight_OmegaMinus : ∀ b c : GaloisField 2 1,
    (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      RowOf425 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  intro b c hbc
  have hv : (LieTypeIndex.twistedD 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, id⟩
  obtain ⟨b', c', hbc', ⟨eB⟩⟩ := Census.bridgeOmega8MinusTwo _ hv rfl rfl
  obtain ⟨rfl, rfl⟩ := RonanK429F.eq_one_of_irreducible_gf2 hbc
  obtain ⟨rfl, rfl⟩ := RonanK429F.eq_one_of_irreducible_gf2 hbc'
  obtain ⟨ψ⟩ := RonanK429F.nonempty_projOmegaMinus_equiv_om8 hbc
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  let φ : S ≃* RonanK429F.Om8 := e.trans ψ
  refine noCC425_of_lie_at' hs hna _ ⟨e.trans eB.symm⟩ fun s hs3 => ?_
  obtain ⟨hx3, hx1⟩ := pow_three_and_ne_one φ hs3
  rcases not_dvd_or_not_mem_commutator (by norm_num) RonanK429F.Om8.orderOf_y7
      (RonanK429F.Om8.not_sq_seven_dvd hbc) om8_not_mem_commutator hx3 hx1 with h7 | hc
  · refine Or.inl ⟨197406720, 583, ?_, by norm_num, by norm_num, ?_⟩
    · rw [← RonanK429H.card_centralizer_mulEquiv φ s, ← RonanK429F.Om8.card_Om8 hbc]
      exact Subgroup.card_subgroup_dvd_card _
    · refine typeOrders_of_not_dvd (r := 7) (by decide +kernel) ?_
      rwa [← RonanK429H.card_centralizer_mulEquiv φ s]
  · exact Or.inr (not_mem_commutator_centralizer_of_mulEquiv φ hc)

end Eight

section F4


open CFSG.HardMathSupport.Dickson.Bal207 in
open CFSG.LieType.Ree CFSG.Blueprint.Chevalley in
theorem kT2_eight_F4 : RowOf425 (TauCeti.CFSGIndex.lie f4TwoIndex).Group := by
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => ?_
  obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := Sec4.Item434F42.exists_model e
  intro s K hcc
  let e'' : S ≃* adjointGroup Tag.F4 F := e'
  have hx : orderOf (e'' s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hcc.orderOf_eq
  have hcongr : MulAut.congr e'' (MulAut.conj s) = MulAut.conj (e'' s) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hS : CompShape FamF42.F42CompType (MulAut.conj s) :=
    CompShape.of_congr FamF42.isoInvariant_f42CompType e''
      (by rw [hcongr]; exact FamF42.compShape_conj_F4_two hF (e'' s) hx)
  have hcomp : CFSG.Open.IsComponentOf K (fixSubgroup (MulAut.conj s)) := by
    rw [RonanK429F.F4.fixSubgroup_conj s]
    exact ⟨hcc.le_centralizer,
      (CFSG.Open.IsSubnormal.iff_subgroupOf hcc.le_centralizer).2 hcc.isSubnormal,
      (Group.isPerfect_def (G := K)).1 hcc.isQuasisimple.1, hcc.isQuasisimple.2.1⟩
  obtain ⟨F', _, _, hF', ⟨eQ⟩⟩ := hS.type K hcomp
  have hZ : Nat.card (K ⧸ Subgroup.center K) = 1451520 := by
    rw [Nat.card_congr eQ.toEquiv, RonanK429F.F4.card_statedSp_quot hF']
  obtain ⟨h1, h2⟩ := card_theta_quot_dvd_three_mul hcc.isQuasisimple hcc.isType
  rw [hZ] at h1 h2
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hcc.isQuasisimple)
    (M := 4354560) (B := 164) (by norm_num) (by norm_num) hcc.isType h2
  exact (by decide +kernel : ∀ t ∈ typeOrders425 4354560 164, ¬ 1451520 ∣ t) _ hmem h1

end F4

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
