module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL32Defs
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C9
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

section Helpers

variable {G : Type} [Group G] [Finite G]

private theorem pCoreOf_subgroupOf_nsb41 (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  unfold pCoreOf
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

private theorem card_modO2_eq_relIndex_nsb41 (L : Subgroup G) :
    Nat.card (ModO2 L) = (pCoreOf 2 L).relIndex L := by
  rw [Subgroup.relIndex, pCoreOf_subgroupOf_nsb41, Subgroup.index_eq_card]

private theorem relIndex_ne_zero_nsb41 {A : Type} [Group A] [Finite A] (P Q : Subgroup A) :
    P.relIndex Q ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem isPSL_modO2_of_eq_nsb41 {X Y : Subgroup G} {n p e : ℕ} (h : X = Y)
    (hP : IsPSL n p e (ModO2 X)) : IsPSL n p e (ModO2 Y) := by
  subst h
  exact hP

private theorem le_of_le_sup_pCoreOf_nsb41 {K X Y : Subgroup G} (hXK : X ≤ K)
    (hXO : X ⊓ pCoreOf 2 K ≤ pCoreOf 2 X) (hcard : Nat.card (ModO2 K) = Nat.card (ModO2 X))
    (hXY : X ≤ Y) (hOY : pCoreOf 2 K ≤ Y) : K ≤ Y := by
  obtain ⟨Ku, hKu⟩ : ∃ A : Subgroup K, A = X.subgroupOf K := ⟨_, rfl⟩
  obtain ⟨Uu, hUu⟩ : ∃ A : Subgroup K, A = (pCoreOf 2 K).subgroupOf K := ⟨_, rfl⟩
  obtain ⟨Uo, hUo⟩ : ∃ A : Subgroup K, A = (pCoreOf 2 X).subgroupOf K := ⟨_, rfl⟩
  have hUuN : Uu.Normal := by
    rw [hUu]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K)).mpr
      (le_normalizer_pCoreOf 2 K)
  have hidxU : Uu.index = Nat.card (ModO2 K) := by
    rw [hUu, pCoreOf_subgroupOf_nsb41, Subgroup.index_eq_card]
  have hidxO : Uo.relIndex Ku = Nat.card (ModO2 X) := by
    rw [hUo, hKu, Subgroup.relIndex_subgroupOf hXK, card_modO2_eq_relIndex_nsb41]
  have hYX : Uu ⊓ Ku ≤ Uo ⊓ Ku := by
    intro x hx
    obtain ⟨hxU, hxK⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, hxK⟩
    rw [hUu, Subgroup.mem_subgroupOf] at hxU
    rw [hKu, Subgroup.mem_subgroupOf] at hxK
    rw [hUo, Subgroup.mem_subgroupOf]
    exact hXO (Subgroup.mem_inf.mpr ⟨hxK, hxU⟩)
  have hle : Uo.relIndex Ku ≤ Uu.relIndex Ku := by
    have h1 : Uu.relIndex Ku = (Uu ⊓ Ku).relIndex Ku :=
      (Subgroup.inf_relIndex_right Uu Ku).symm
    have h2 : (Uu ⊓ Ku).relIndex Ku = (Uu ⊓ Ku).relIndex (Uo ⊓ Ku) * (Uo ⊓ Ku).relIndex Ku :=
      (Subgroup.relIndex_mul_relIndex (Uu ⊓ Ku) (Uo ⊓ Ku) Ku hYX inf_le_right).symm
    have h3 : (Uo ⊓ Ku).relIndex Ku = Uo.relIndex Ku := Subgroup.inf_relIndex_right Uo Ku
    rw [h1, h2, h3]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (relIndex_ne_zero_nsb41 _ _))
  have hsup : Uu.relIndex (Ku ⊔ Uu) = Uu.relIndex Ku := by
    haveI := hUuN
    exact Subgroup.relIndex_sup_right Ku Uu
  have hmul : Uu.relIndex (Ku ⊔ Uu) * (Ku ⊔ Uu).index = Uu.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have hUuidx : Uu.index = Uo.relIndex Ku := by
    rw [hidxU, hidxO]
    exact hcard
  have hPidx : (Ku ⊔ Uu).index = 1 := by
    have hpos : Uu.relIndex (Ku ⊔ Uu) ≠ 0 := relIndex_ne_zero_nsb41 _ _
    have hp0 : (Ku ⊔ Uu).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcle : Uu.relIndex (Ku ⊔ Uu) * (Ku ⊔ Uu).index ≤ Uu.relIndex (Ku ⊔ Uu) * 1 := by
      rw [hmul, hUuidx, mul_one, hsup]
      exact hle
    have hp1 := Nat.le_of_mul_le_mul_left hcle (Nat.pos_of_ne_zero hpos)
    omega
  have hPtop : Ku ⊔ Uu = ⊤ := Subgroup.index_eq_one.mp hPidx
  have hsub : Ku ⊔ Uu ≤ Y.subgroupOf K := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [hKu, Subgroup.mem_subgroupOf] at hy
      exact Subgroup.mem_subgroupOf.mpr (hXY hy)
    · intro y hy
      rw [hUu, Subgroup.mem_subgroupOf] at hy
      exact Subgroup.mem_subgroupOf.mpr (hOY hy)
  intro g hg
  have hmem : (⟨g, hg⟩ : K) ∈ Ku ⊔ Uu := by
    rw [hPtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp (hsub hmem)

theorem card_alt5_nsb41 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_psl3_nsb41 {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nat.card X = 168 := by
  rw [C489.card_of_isPSL_two h]
  decide

theorem psl22_ne_nsb41 (n : ℕ) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 20160 := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num
  · have h32 : 32 ≤ 2 ^ n := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1024 : 32 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h32 2
    have h1 : 1023 ≤ (2 ^ n) ^ 2 - 1 :=
      Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num) h1024)
    have h2 : 32 * 1023 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h32 h1
    constructor
    · intro h
      rw [h] at h2
      norm_num at h2
    · intro h
      rw [h] at h2
      norm_num at h2

end Helpers

theorem c41Case4Of_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    C41Case4Of := by
  intro G _ _ T M L Mm I H K m k hd hK
  obtain ⟨hy, -, hc, hm, -, -, hPSLLH, -⟩ := hd
  obtain ⟨hKc, hCT, hqs, hKM, hC⟩ := hK
  have hLHM : perfectCore (L ⊓ H) ≤ H ⊓ M := le_of_mem_cComp hc.LH_mem
  have hLHK : perfectCore (L ⊓ H) ≤ K := hc.LH_le
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hcK : conjClosure K H = K := hC.2.2.1
  have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
    conjClosure_eq_self hc.LH_normal
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    have h := le_normalizer_conjClosure K H
    rwa [hcK] at h
  have hK2 : pCoreOf 2 K ≠ ⊥ := by
    intro h0
    have hcore : CFSG.pCore 2 ↥K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxO : (x : G) ∈ pCoreOf 2 K := by
        unfold pCoreOf
        exact Subgroup.mem_map_of_mem K.subtype hx
      rw [h0, Subgroup.mem_bot] at hxO
      exact Subtype.ext hxO
    have hq : CFSG.IsQuasisimple ↥K :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot) hqs
    exact C489.not_charTwo_of_quasisimple (ne_bot_of_mem_cComp hKc) (perfect_of_mem_cComp hKc)
      hq hCT
  have hO2H : pCoreOf 2 K ≤ H := (pCoreOf_le 2 K).trans hKH
  have hHNK : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hOH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hO2H hHNK (pCoreOf_isPGroup 2 K)
  have h5 := lemma_4_1_4_five (hy.hyp4_1_1 h37 h38 h39) hy.sigma hy.gammaStar hc.inH hc.not_le
  have hOM : pCoreOf 2 K ≤ H ⊓ M :=
    (hOH.trans (h5.2.2.1.trans h5.2.2.2)).trans
      ((pCoreOf_le 2 I).trans (le_inf hc.inH.1 hc.I_le))
  have hXO : perfectCore (L ⊓ H) ⊓ pCoreOf 2 K ≤ pCoreOf 2 (perfectCore (L ⊓ H)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
        (le_normalizer_pCoreOf 2 K (hLHK hg)))
      ((pCoreOf_isPGroup 2 K).to_le inf_le_right)
  have hLHcard : (Nat.card (ModO2 (perfectCore (L ⊓ H))) = 168 ∧ m = 3) ∨
      (Nat.card (ModO2 (perfectCore (L ⊓ H))) = 20160 ∧ m = 4) := by
    rcases hm with rfl | rfl
    · exact Or.inl ⟨card_psl3_nsb41 hPSLLH, rfl⟩
    · exact Or.inr ⟨F420.card_of_l42 hPSLLH, rfl⟩
  rcases hC.2.2.2 with h1 | h2 | h3 | h4
  ·
    exfalso
    obtain ⟨n, hn, hAlt, -⟩ := h1
    rw [hcc] at hAlt
    obtain ⟨-, α, hα, hker, -⟩ := hAlt
    have hcardA : Nat.card (ModO2 (perfectCore (L ⊓ H))) = Nat.card (alternatingGroup (Fin n)) := by
      have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
      exact Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl
    · rw [card_alt5_nsb41] at hcardA
      rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rw [C489.card_alt6] at hcardA
      rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpsl⟩ := h2
    have hpsl' := isPSL_modO2_of_eq_nsb41 hcc hpsl
    have hcard := C489.card_of_isPSL_two_two hpsl'
    rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩
    · exact (psl22_ne_nsb41 2).1 (hcard.symm.trans h)
    · exact (psl22_ne_nsb41 2).2 (hcard.symm.trans h)
  ·
    exfalso
    obtain ⟨n, _, _, _, -, -, -, -, -, -, hpsl, -⟩ := h3
    have hpsl' := isPSL_modO2_of_eq_nsb41 hcc hpsl
    have hcard := C489.card_of_isPSL_two_two hpsl'
    rcases hLHcard with ⟨h, -⟩ | ⟨h, -⟩
    · exact (psl22_ne_nsb41 n).1 (hcard.symm.trans h)
    · exact (psl22_ne_nsb41 n).2 (hcard.symm.trans h)
  ·
    obtain ⟨hK45, -, -⟩ := h4
    rcases hK45 with hK4 | hK5
    ·
      have hm3 : m = 3 := by
        rcases hLHcard with ⟨-, h3⟩ | ⟨hc20, -⟩
        · exact h3
        · exfalso
          have hcK20 : Nat.card (ModO2 K) = 20160 := F420.card_of_l42 hK4
          have hKLH : K ≤ H ⊓ M :=
            le_of_le_sup_pCoreOf_nsb41 hLHK hXO (hcK20.trans hc20.symm) hLHM hOM
          exact hKM hKLH
      exact ⟨hHK, hK2, 4, Or.inl ⟨rfl, hm3⟩, hK4⟩
    · refine ⟨hHK, hK2, 5, ?_, hK5⟩
      rcases hLHcard with ⟨-, h3⟩ | ⟨-, h4'⟩
      · exact Or.inr (Or.inl ⟨rfl, h3⟩)
      · exact Or.inr (Or.inr ⟨rfl, h4'⟩)

end CFSG.Quasithin.H13.Ch4.NSB
