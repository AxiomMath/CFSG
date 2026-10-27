module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutElemL

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section ElemK

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem nonCentral_of_perfect_core_le {K I : Subgroup G} (hIK : I ≤ K)
    (eI : Nonempty (↥I ≃* alternatingGroup (Fin 6)))
    (e : ↥K ⧸ Subgroup.center ↥K ≃* NativeSporadic.J3) {k : ↥K} (hk3 : k ^ 3 = 1)
    (hkZ : k ∉ Subgroup.center ↥K) (hcomm : ∀ x ∈ I, x * (k : G) = (k : G) * x) :
    NonCentral 3 (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨eI⟩ := eI
  have hI360 : Nat.card I = 360 := by
    rw [Nat.card_congr eI.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]; decide
  have hq3 : (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hk3]; rfl
  have hq1 : (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) ≠ 1 := fun h1 =>
    hkZ ((QuotientGroup.eq_one_iff _).1 h1)
  set IK : Subgroup ↥K := I.subgroupOf K with hIKdef
  have hIKmem : ∀ x : ↥K, x ∈ IK ↔ (x : G) ∈ I := fun x => Subgroup.mem_subgroupOf
  have hIKcard : Nat.card IK = 360 := by
    rw [hIKdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIK).toEquiv, hI360]
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center ↥K)).comp IK.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : ↥K) ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff _).1 hx
    have hxI : (x : G) ∈ I := (hIKmem x).1 x.2
    have hc : (⟨(x : G), hxI⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyK : (y : G) ∈ K := hIK y.2
      have := Subgroup.mem_center_iff.1 hxZ ⟨(y : G), hyK⟩
      exact Subtype.ext (congrArg (fun z : ↥K => (z : G)) this)
    rw [center_eq_bot_of_equiv_alt6 I eI, Subgroup.mem_bot] at hc
    have h1 : ((x : ↥K) : G) = 1 := by simpa using congrArg Subtype.val hc
    exact Subtype.ext (Subtype.ext (by simpa using h1))
  set IQ : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
    IK.map (QuotientGroup.mk' (Subgroup.center ↥K)) with hIQ
  have hIQcard : Nat.card IQ = 360 := by
    rw [← hIKcard]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : IK => (⟨QuotientGroup.mk' (Subgroup.center ↥K) (x : ↥K), ⟨x, x.2, rfl⟩⟩ : IQ))
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩)).symm
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hIQC : IQ ≤ Subgroup.centralizer
      ({(QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K)} : Set (↥K ⧸ Subgroup.center ↥K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk x * QuotientGroup.mk k = QuotientGroup.mk k * QuotientGroup.mk x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact hcomm x ((hIKmem x).1 hx)
  exact nonCentral_of_card_dvd e hq3 hq1 hIQcard hIQC

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OutSecond.exists_v (h45 : Sec4.Item4_5) {a : G} {U₀ K : Subgroup G}
    (hS : OutSecond A E U c L a U₀ K) :
    ∃ v : G, v ∈ K ∧ v ∈ Subgroup.normalizer (A : Set G) ∧
      v ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) ∧
      v ∉ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) ∧
      orderOf v = 8 ∧ a * v = v * a ∧
      v ∈ Subgroup.normalizer ((iCore L a : Subgroup G) : Set G) ∧
      v ∈ Subgroup.normalizer ((A ⊓ iCore L a : Subgroup G) : Set G) ∧
      v ^ 4 ∉ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
  have h : CoverOut A E U c L := hS.base
  have hfr := hS.frame
  have hEA : E ≤ A := h.pair.mem_E.2
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hcE : c ∈ E := (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1
  have hc1 : c ≠ 1 := h.c_ne_one
  have haA : a ∈ A := hEA hfr.mem
  have ha3 : a ^ 3 = 1 := hab.2 a haA
  have ha1 : a ≠ 1 := fun h1 => hfr.not_mem (h1 ▸ Subgroup.one_mem _)
  have hnot : c ∉ Subgroup.zpowers a := fun hca' =>
    hfr.not_mem (mem_zpowers_of_mem_zpowers ha3 hc1 hca')
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hS.mem_K.2
  have hp : Sec21Pair G A E U₀ a K :=
    { h.pair.toSec21Std with
      mem_E := h.pair.mem_E
      mem_U := fourGroupsMinus_subset E hS.mem_U₀
      mem_pair := hS.pair }
  obtain ⟨⟨eI⟩, -⟩ := h.iCore_structure h45 hfr
  have hperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ eI
  have hI360 : Nat.card ↥(iCore L a) = 360 := by
    rw [Nat.card_congr eI.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]; decide
  have hIle : iCore L a ≤ iCore K c := by
    refine le_sSup ⟨fun x hx => ⟨?_, hS.I_le_K hx⟩, hperf⟩
    show x ∈ Subgroup.centralizer ({c} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.c_comm x (iCore_le L a hx).2).symm
  have hdsymm : dGroup c a = dGroup a c := sup_comm _ _
  by_cases haK : a ∈ K
  ·
    have haord : orderOf (⟨a, haK⟩ : ↥K) = 3 := by
      rw [← Subgroup.orderOf_coe]; exact orderOf_eq_prime ha3 ha1
    have htri : Sec4.IsTripleCover (lBar K) NativeSporadic.J3 := by
      rcases hS.type with ⟨⟨e⟩⟩ | htri
      · exfalso
        obtain ⟨hTs, hTch, hT3, -⟩ :=
          solvable_prime_complement_core_characterization (H := K) Nat.prime_three
        have hcen : (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : lBar K) ∈ Subgroup.center (lBar K) := by
          rw [Subgroup.mem_center_iff]
          intro q
          obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hKC k.2))
        have hZbot : Subgroup.center (lBar K) = ⊥ := center_eq_bot_of_equiv_J3 e
        rw [hZbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
        apply hT3
        have := Subgroup.orderOf_dvd_natCard _ hcen
        rw [haord] at this
        exact this
      · exact htri
    have hquot : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* NativeSporadic.J3) := by
      obtain ⟨-, ⟨e⟩⟩ := htri
      exact nonempty_quot_center_of_lBar (S := NativeSporadic.J3) hS.quasi e
    have hKcov : Cover217 A E U₀ a K :=
      { pair := hp, quot := hquot, mem := haK, cover := htri, card := h.card, ext := hS.ext }
    have hθK := sec217ThetaOne_holds A E U₀ a K hKcov
    have hAK := sec217ALe_of h45 A E U₀ a K hKcov
    have hcK : c ∈ K := hAK h.c_mem_A
    have hfrK : Frame217 E a K c := by
      refine ⟨hcE, hnot, ⟨⟨c, hcK⟩, ⟨1, Subgroup.one_mem _, by simp⟩, ?_⟩⟩
      have hZc : (⟨c, hcK⟩ : ↥K) ∉ Subgroup.center ↥K := by
        intro hz
        rw [hKcov.center_eq hθK] at hz
        apply hnot
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact ⟨n, congrArg Subtype.val hn⟩
      exact nonCentral_of_perfect_core_le hS.I_le_K ⟨eI⟩ hKcov.quot.some
        (k := ⟨c, hcK⟩) (Subtype.ext (by simpa using h.c_cubed)) hZc
        (fun x hx => (h.c_comm x (iCore_le L a hx).2).symm)
    have hvK : Valid217 A a K c := hfrK.valid hEA
    have hcard360K : Nat.card ↥(iCore K c) = 360 := hKcov.card_iCore hθK hAK hvK
    have hIeq : iCore K c = iCore L a :=
      (Subgroup.eq_of_le_of_card_ge hIle (by rw [hcard360K, hI360])).symm
    obtain ⟨v, hvK', hvN, hvD, hvC, hvord, hav, hvI, hv4⟩ := hKcov.exists_u hθK hAK hvK
    rw [hIeq] at hvI hv4
    refine ⟨v, hvK', hvN, ?_, ?_, hvord, hav, hvI, mem_normalizer_inf_out hvN hvI, hv4⟩
    · rwa [hdsymm] at hvD
    · intro hc'
      apply hvC
      have hcD : c ∈ dGroup a c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hc' c hcD).symm
  ·
    have hquot : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* NativeSporadic.J3) := by
      rcases hS.type with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
      · have hZ : Subgroup.center (lBar K) = ⊥ := center_eq_bot_of_equiv_J3 e
        exact nonempty_quot_center_of_lBar (S := NativeSporadic.J3) hS.quasi
          ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e))
      · exact nonempty_quot_center_of_lBar (S := NativeSporadic.J3) hS.quasi e
    have hKout : CoverOut A E U₀ a K :=
      { pair := hp, quot := hquot, notMem := haK, card := h.card, ext := hS.ext }
    have hZK := hKout.center_eq_bot h45
    have hfrK : Frame217 E a K c := by
      obtain ⟨k, hk, j, hkj⟩ := hKout.decomp_A h45 c h.c_mem_A
      have hkK : k ∈ K := hk.2
      have hk1 : k ≠ 1 := by
        intro hk1
        apply hnot
        rw [hk1, one_mul] at hkj
        rw [hkj]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j
      refine ⟨hcE, hnot, ⟨⟨k, hkK⟩, ⟨a ^ j, ?_, hkj⟩, ?_⟩⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 (hKC hx)
        exact ((show Commute x a from hxa).zpow_right j).eq
      · have hkZ : (⟨k, hkK⟩ : ↥K) ∉ Subgroup.center ↥K := by
          rw [hZK]
          intro hz
          apply hk1
          have := Subgroup.mem_bot.1 hz
          simpa using congrArg Subtype.val this
        have hk3 : (⟨k, hkK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hab.2 k hk.1)
        refine nonCentral_of_perfect_core_le hS.I_le_K ⟨eI⟩ hquot.some hk3 hkZ ?_
        intro x hx
        have hxL : x ∈ L := (iCore_le L a hx).2
        have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 (iCore_le L a hx).1
        have hxc : x * c = c * x := (h.c_comm x hxL).symm
        have hxaj : x * a ^ j = a ^ j * x := ((show Commute x a from hxa).zpow_right j).eq
        have hk' : k = c * (a ^ j)⁻¹ := by rw [hkj]; group
        show x * k = k * x
        rw [hk']
        calc x * (c * (a ^ j)⁻¹) = (x * c) * (a ^ j)⁻¹ := by group
          _ = (c * x) * (a ^ j)⁻¹ := by rw [hxc]
          _ = c * (x * (a ^ j)⁻¹) := by group
          _ = c * ((a ^ j)⁻¹ * x) := by
              congr 1
              exact ((show Commute x (a ^ j) from hxaj).inv_right).eq
          _ = (c * (a ^ j)⁻¹) * x := by group
    have hcard360K : Nat.card ↥(iCore K c) = 360 := by
      obtain ⟨⟨eK⟩, -⟩ := hKout.iCore_structure h45 hfrK
      rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    have hIeq : iCore K c = iCore L a :=
      (Subgroup.eq_of_le_of_card_ge hIle (by rw [hcard360K, hI360])).symm
    obtain ⟨v, hvK', hvN, hvD, hvC, hvord, hav, hvI, hvAI, hv4⟩ := hKout.exists_u h45 hfrK
    rw [hIeq] at hvI hvAI hv4
    refine ⟨v, hvK', hvN, ?_, ?_, hvord, hav, hvI, hvAI, hv4⟩
    · rwa [hdsymm] at hvD
    · rwa [hdsymm] at hvC

end ElemK

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
