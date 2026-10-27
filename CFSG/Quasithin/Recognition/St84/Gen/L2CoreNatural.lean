module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIASL2
import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridgeAux
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.NFa2
open CFSG.QuasithinUnique.Setup.X7
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]


private theorem pCore_card_eq_pow {G : Type} [Group G] {L : Subgroup G} [Finite ↥L] {n : ℕ}
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (2 * n)) :
    Nat.card ↥(CFSG.pCore 2 ↥L) = 2 ^ (2 * n) := by
  rw [show CFSG.pCore 2 ↥L = (pCoreOf 2 L).subgroupOf L from
    (CFSG.openPCoreOf_subgroupOf 2 L).symm]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (CFSG.openPCoreOf_le 2 L)).toEquiv).trans hcard

private theorem isElemAbelian_pCore {G : Type} [Group G] {L : Subgroup G} [Finite ↥L]
    (he : IsElemAbelian 2 (pCoreOf 2 L)) :
    IsElemAbelian 2 (CFSG.pCore 2 ↥L) := by
  rw [show CFSG.pCore 2 ↥L = (pCoreOf 2 L).subgroupOf L from
    (CFSG.openPCoreOf_subgroupOf 2 L).symm]
  exact he.subgroupOf L

private theorem irreducible_pCore {G : Type} [Group G] {L : Subgroup G} [Finite ↥L]
    (hirr : ∀ W : Subgroup G, W ≤ pCoreOf 2 L → L ≤ Subgroup.normalizer (W : Set G) →
      W = ⊥ ∨ W = pCoreOf 2 L) :
    ∀ W : Subgroup ↥L, W ≤ CFSG.pCore 2 ↥L →
      (⊤ : Subgroup ↥L) ≤ Subgroup.normalizer (W : Set ↥L) →
        W = ⊥ ∨ W = CFSG.pCore 2 ↥L := by
  intro W hWle hWnorm
  have hWmap_le : W.map L.subtype ≤ pCoreOf 2 L := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.map_mono hWle
  have hWmap_norm : L ≤ Subgroup.normalizer ((W.map L.subtype : Subgroup G) : Set G) := by
    have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top hWnorm)
    have hsub : W.map L.subtype ≤ L := by
      intro x hx
      obtain ⟨w, -, rfl⟩ := hx
      exact w.2
    have hpull : ((W.map L.subtype).subgroupOf L) = W := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_iff_mem L.subtype_injective
    have hnormal : ((W.map L.subtype).subgroupOf L).Normal := by
      rw [hpull]
      exact hWn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mp hnormal
  rcases hirr (W.map L.subtype) hWmap_le hWmap_norm with h | h
  · left
    apply Subgroup.map_injective L.subtype_injective
    rw [h, Subgroup.map_bot]
  · right
    apply Subgroup.map_injective L.subtype_injective
    rw [h, CFSG.openPCoreOf_eq_map_pCore]

private theorem centralizer_pCore_le {G : Type} [Group G] {L : Subgroup G} [Finite ↥L]
    (hc : CharTwo L) :
    Subgroup.centralizer ((CFSG.pCore 2 ↥L : Subgroup ↥L) : Set ↥L) ≤
      CFSG.pCore 2 ↥L := by
  intro x hx
  rw [← CFSG.mem_openPCoreOf_iff]
  have hmem : (x : G) ∈ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqL : q ∈ L := CFSG.openPCoreOf_le 2 L hq
    have hqH : (⟨q, hqL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (CFSG.mem_openPCoreOf_iff _).mp hq
    have hcxy := Subgroup.mem_centralizer_iff.mp hx ⟨q, hqL⟩ hqH
    simpa using congrArg Subtype.val hcxy
  exact hc hmem

private theorem isSylowTwoOf_subgroupOf_top {G : Type} [Group G] {L T : Subgroup G}
    [Finite ↥L] (hT : IsSylowTwoOf T L) :
    IsSylowTwoOf (T.subgroupOf L) (⊤ : Subgroup ↥L) := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  · have hidx : ((T.subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index =
        (T.subgroupOf L).index := by
      rw [← Subgroup.relIndex_top_right (H := (T.subgroupOf L).subgroupOf ⊤),
        ← Subgroup.relIndex_top_right (H := T.subgroupOf L),
        ← Subgroup.relIndex_subgroupOf (H := T.subgroupOf L) (K := ⊤) (L := ⊤) le_rfl,
        Subgroup.subgroupOf_self]
    rw [hidx]
    exact hT.2.2

private theorem card_centralizer_pCore_ge {G : Type} [Group G] {L T : Subgroup G}
    [Finite ↥L] {n : ℕ}
    (hC : 2 ^ n ≤ Nat.card ↥(pCoreOf 2 L ⊓ Subgroup.centralizer (T : Set G))) :
    2 ^ n ≤ Nat.card ↥(CFSG.pCore 2 ↥L ⊓
      Subgroup.centralizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)) := by
  let f : ↥(pCoreOf 2 L ⊓ Subgroup.centralizer (T : Set G)) →
      ↥(CFSG.pCore 2 ↥L ⊓
        Subgroup.centralizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)) := fun y =>
    ⟨⟨(y.1 : G), CFSG.openPCoreOf_le 2 L y.2.1⟩,
      Subgroup.mem_inf.mpr ⟨(CFSG.mem_openPCoreOf_iff _).mp y.2.1,
        Subgroup.mem_centralizer_iff.mpr fun s hs => by
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2.2 (s : G) hs)⟩⟩
  have hinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun w => ((w.1 : ↥L) : G)) hyz
  exact le_trans hC (Nat.card_le_card_of_injective f hinj)

private theorem exists_not_mem_centralizer_pCore {H : Type} [Group H] [Finite H] {n : ℕ}
    (hn : 1 ≤ n)
    (hcent : Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H) ≤
      CFSG.pCore 2 H)
    (hquot : IsL2Quot n (oTwoQuot H)) :
    ∃ l : H, l ∉ Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H) := by
  classical
  by_contra hcon
  push Not at hcon
  have htop_le_cent : (⊤ : Subgroup H) ≤
      Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H) := fun x _ => hcon x
  have htop_le_QH : (⊤ : Subgroup H) ≤ CFSG.pCore 2 H := fun x _ =>
    hcent (htop_le_cent (Subgroup.mem_top x))
  have hQHtop : CFSG.pCore 2 H = ⊤ := le_antisymm le_top htop_le_QH
  have hquotcard1 : Nat.card (H ⧸ CFSG.pCore 2 H) = 1 := by
    haveI : Subsingleton (H ⧸ ⊤) := QuotientGroup.subsingleton_quotient_top
    rw [hQHtop]
    exact Nat.card_of_subsingleton (1 : H ⧸ ⊤)
  have hqcard := CFSG.Quasithin.IsL2Quot.card hn hquot
  rw [hquotcard1] at hqcard
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4n : 4 ≤ 4 ^ n := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq1 : 3 ≤ 4 ^ n - 1 := by omega
  have hge : 6 ≤ 2 ^ n * (4 ^ n - 1) := by
    calc 6 = 2 * 3 := by norm_num
      _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h2n hq1
  omega

private theorem shortU_eq_pCore {H : Type} [Group H] [Finite H]
    (hirr : ∀ W : Subgroup H, W ≤ CFSG.pCore 2 H →
      (⊤ : Subgroup H) ≤ Subgroup.normalizer (W : Set H) →
        W = ⊥ ∨ W = CFSG.pCore 2 H)
    (hnc : ∃ l : H, l ∉ Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)) :
    CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H := by
  classical
  let QH : Subgroup H := CFSG.pCore 2 H
  have hcomm_ne : (⁅QH, (⊤ : Subgroup H)⁆ : Subgroup H) ≠ ⊥ := by
    intro hbot
    obtain ⟨l, hl⟩ := hnc
    apply hl
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hmem : ⁅q, l⁆ ∈ (⁅QH, (⊤ : Subgroup H)⁆ : Subgroup H) :=
      Subgroup.commutator_mem_commutator hq (Subgroup.mem_top l)
    rw [hbot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hcomm_le : (⁅QH, (⊤ : Subgroup H)⁆ : Subgroup H) ≤ QH := by
    haveI : QH.Normal := CFSG.pCore_normal
    haveI : (⊤ : Subgroup H).Normal := inferInstance
    exact (Subgroup.commutator_le_inf QH (⊤ : Subgroup H)).trans inf_le_left
  have hcomm_norm : (⁅QH, (⊤ : Subgroup H)⁆ : Subgroup H).Normal := by
    haveI : QH.Normal := CFSG.pCore_normal
    haveI : (⊤ : Subgroup H).Normal := inferInstance
    exact Subgroup.commutator_normal QH ⊤
  have hcases := hirr _ hcomm_le
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hcomm_norm])
  rcases hcases with h | h
  · exact absurd h hcomm_ne
  · exact h

private theorem shortC_eq_bot {H : Type} [Group H] [Finite H]
    (hirr : ∀ W : Subgroup H, W ≤ CFSG.pCore 2 H →
      (⊤ : Subgroup H) ≤ Subgroup.normalizer (W : Set H) →
        W = ⊥ ∨ W = CFSG.pCore 2 H)
    (hnc : ∃ l : H, l ∉ Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)) :
    CFSG.RankThree.PartOne.shortC H = ⊥ := by
  classical
  let QH : Subgroup H := CFSG.pCore 2 H
  have hZ_norm : (QH ⊓ Subgroup.center H).Normal := by
    haveI : QH.Normal := CFSG.pCore_normal
    haveI : (Subgroup.center H).Normal := inferInstance
    exact inferInstance
  have hcases := hirr _ inf_le_left
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hZ_norm])
  have hZ_ne : (QH ⊓ Subgroup.center H) ≠ QH := by
    intro hEq
    obtain ⟨l, hl⟩ := hnc
    apply hl
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqZ : q ∈ QH ⊓ Subgroup.center H := by rw [hEq]; exact hq
    exact (Subgroup.mem_center_iff.mp hqZ.2 l).symm
  rw [CFSG.RankThree.PartOne.shortC, shortU_eq_pCore hirr hnc]
  rcases hcases with h | h
  · exact h
  · exact absurd h hZ_ne

private theorem secHyp_top_bot_pCore {H : Type} [Group H] [Finite H]
    (he : IsElemAbelian 2 (CFSG.pCore 2 H)) :
    SecHyp (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) := by
  classical
  have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup H) : Set H) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hQHnorm : Subgroup.normalizer ((CFSG.pCore 2 H : Subgroup H) : Set H) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr (CFSG.pCore_normal (p := 2) (G := H))
  refine ⟨bot_le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbotnorm]
  · rw [hQHnorm]
  · rw [hbotnorm]
    exact le_top
  · intro a ha b hb
    rw [Subgroup.mem_bot]
    have hcomm : a * b = b * a :=
      congrArg Subtype.val (he.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [hcomm]
    group
  · intro a ha
    rw [Subgroup.mem_bot]
    simpa [pow_two] using he.2 a ha

private theorem isChiefPair_top_bot_pCore {H : Type} [Group H] [Finite H]
    (hne : CFSG.pCore 2 H ≠ ⊥)
    (hirr : ∀ W : Subgroup H, W ≤ CFSG.pCore 2 H →
      (⊤ : Subgroup H) ≤ Subgroup.normalizer (W : Set H) →
        W = ⊥ ∨ W = CFSG.pCore 2 H) :
    IsChiefPair (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) := by
  classical
  have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup H) : Set H) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hQHnorm : Subgroup.normalizer ((CFSG.pCore 2 H : Subgroup H) : Set H) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr (CFSG.pCore_normal (p := 2) (G := H))
  refine ⟨⟨bot_le, fun h => hne (le_antisymm h bot_le)⟩, ?_, ?_, ?_, ?_⟩
  · rw [hbotnorm]
  · rw [hQHnorm]
  · rw [hbotnorm]
    exact le_top
  · intro N _ hN hnorm
    exact hirr N hN hnorm

private theorem card_SL_eq_card_quotient {H : Type} [Group H] {n : ℕ}
    (hquot : IsL2Quot n (oTwoQuot H)) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      Nat.card (H ⧸ CFSG.pCore 2 H) := by
  obtain ⟨eL⟩ := hquot
  rw [← Nat.card_congr (CFSG.Quasithin.pslTwoGf2EquivSl n).toEquiv]
  exact (Nat.card_congr eL.toEquiv).symm

private theorem ker_eq_pCore_of_surjective {H : Type} [Group H] [Finite H] {n : ℕ}
    (hn : 1 ≤ n)
    {ψ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψ : Function.Surjective ψ) (hquot : IsL2Quot n (oTwoQuot H))
    (hQHcard : Nat.card ↥(CFSG.pCore 2 H) = 2 ^ (2 * n)) :
    ψ.ker = CFSG.pCore 2 H := by
  classical
  let F := GaloisField 2 n
  letI : Fintype F := Fintype.ofFinite _
  have h1 : Nat.card ↥ψ.ker * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card H := Subgroup.card_ker_mul_card_of_surjective hψ
  have h2 : Nat.card H = Nat.card (H ⧸ CFSG.pCore 2 H) * Nat.card ↥(CFSG.pCore 2 H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card (H ⧸ CFSG.pCore 2 H) := card_SL_eq_card_quotient hquot
  have hSLpos : 0 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := Nat.card_pos
  have hmul : Nat.card ↥ψ.ker * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card ↥(CFSG.pCore 2 H) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [h1, h2, h3]
    ring
  have hker_card : Nat.card ↥ψ.ker = 2 ^ (2 * n) := by
    rw [Nat.eq_of_mul_eq_mul_right hSLpos hmul, hQHcard]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ψ.ker ≤ CFSG.pCore 2 H := by
    have hp : IsPGroup 2 ↥ψ.ker := IsPGroup.of_card (n := 2 * n) hker_card
    refine fun x hx => le_sSup (show ψ.ker ∈
      {K : Subgroup H | K.Normal ∧ IsPGroup 2 K} from ⟨ψ.normal_ker, hp⟩) hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hker_card, hQHcard]

private theorem sylow_image_sq_eq_one {H : Type} [Group H] [Finite H] {n : ℕ}
    {S : Subgroup H} (hS : IsSylowTwoOf S (⊤ : Subgroup H))
    {ψ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)} :
    ∀ a ∈ S.map ψ, a * a = 1 := by
  classical
  intro a ha
  obtain ⟨t, ht, rfl⟩ := ha
  obtain ⟨j, hj⟩ := hS.2.1 ⟨t, ht⟩
  have hpow : (ψ t) ^ (2 ^ j) = 1 := by
    have h := congrArg (fun x : ↥S => ψ (x : H)) hj
    simpa using h
  exact CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl.sl2_sq_eq_one_of_char_two
    (CharP.cast_eq_zero (GaloisField 2 n) 2) (ψ t) hpow

private theorem not_two_dvd_index_of_isSylowTwoOf_top {H : Type} [Group H] {S : Subgroup H}
    (hS : IsSylowTwoOf S (⊤ : Subgroup H)) : ¬ 2 ∣ S.index := by
  rw [← Subgroup.relIndex_top_right]
  exact hS.2.2

private theorem sylow_image_mul_index {H : Type} [Group H] [Finite H] {n : ℕ} (hn : 1 ≤ n)
    {S : Subgroup H} (hS : IsSylowTwoOf S (⊤ : Subgroup H))
    {ψ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψ : Function.Surjective ψ) (hψker : ψ.ker = CFSG.pCore 2 H)
    (hquot : IsL2Quot n (oTwoQuot H))
    (hQHcard : Nat.card ↥(CFSG.pCore 2 H) = 2 ^ (2 * n)) :
    Nat.card ↥(S.map ψ) * S.index = 2 ^ n * (4 ^ n - 1) := by
  classical
  let F := GaloisField 2 n
  letI : Fintype F := Fintype.ofFinite _
  have hQHleS : CFSG.pCore 2 H ≤ S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := CFSG.pCore_normal (p := 2) (G := H)
    exact IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup
      (hS.2.1.toSylow (not_two_dvd_index_of_isSylowTwoOf_top hS))
  have hkeq : (ψ.comp S.subtype).ker = (CFSG.pCore 2 H).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, ← hψker,
      MonoidHom.mem_ker]
    rfl
  have hcardker : Nat.card ↥((ψ.comp S.subtype).ker) = Nat.card ↥(CFSG.pCore 2 H) := by
    rw [hkeq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQHleS).toEquiv
  have hrange : (ψ.comp S.subtype).range = S.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card ↥(CFSG.pCore 2 H) * Nat.card ↥(S.map ψ) = Nat.card ↥S := by
    have h := Subgroup.card_ker_mul_card_range (ψ.comp S.subtype)
    rwa [hcardker, hrange] at h
  have hScard : Nat.card ↥S * S.index = Nat.card H := Subgroup.card_mul_index S
  have hHcard : Nat.card ↥(CFSG.pCore 2 H) *
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card H := by
    have h := Subgroup.card_ker_mul_card_of_surjective hψ
    rwa [hψker] at h
  have hquotcard : Nat.card (H ⧸ CFSG.pCore 2 H) = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.IsL2Quot.card hn hquot
  have hSLcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card (H ⧸ CFSG.pCore 2 H) := card_SL_eq_card_quotient hquot
  have hcombine : Nat.card ↥(CFSG.pCore 2 H) *
      (Nat.card ↥(S.map ψ) * S.index) =
      Nat.card ↥(CFSG.pCore 2 H) * (2 ^ n * (4 ^ n - 1)) := by
    calc Nat.card ↥(CFSG.pCore 2 H) * (Nat.card ↥(S.map ψ) * S.index)
        = (Nat.card ↥(CFSG.pCore 2 H) * Nat.card ↥(S.map ψ)) * S.index := by ring
      _ = Nat.card ↥S * S.index := by rw [h1]
      _ = Nat.card H := hScard
      _ = Nat.card ↥(CFSG.pCore 2 H) *
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := hHcard.symm
      _ = Nat.card ↥(CFSG.pCore 2 H) * Nat.card (H ⧸ CFSG.pCore 2 H) := by rw [hSLcard]
      _ = Nat.card ↥(CFSG.pCore 2 H) * (2 ^ n * (4 ^ n - 1)) := by rw [hquotcard]
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos) hcombine

private theorem eq_pow_of_mul_odd_index {A m n : ℕ} (hm : ¬ 2 ∣ m) (hn : 1 ≤ n)
    (hA : ∃ k, A = 2 ^ k) (hmul : A * m = 2 ^ n * (4 ^ n - 1)) : A = 2 ^ n := by
  obtain ⟨k, hk⟩ := hA
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  have hqodd : (4 ^ n - 1).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    obtain ⟨a, ha⟩ := h
    have h4 : 2 ∣ 4 ^ n := by
      have h4eq : 4 ^ n = 2 ^ (2 * n) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
      rw [h4eq]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨b, hb⟩ := h4
    have h4pos : 0 < 4 ^ n := pow_pos (by norm_num) n
    omega
  have hmodd : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hm
  have hAfac : A.factorization 2 = k := by
    rw [hk, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hfac : (A * m).factorization = (2 ^ n * (4 ^ n - 1)).factorization :=
    congrArg _ hmul
  have h4n : 4 ≤ 4 ^ n := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqne : 4 ^ n - 1 ≠ 0 := by omega
  rw [Nat.factorization_mul (by rw [hk]; positivity) hm0,
    Nat.factorization_mul (by positivity : 2 ^ n ≠ 0) hqne] at hfac
  have hfac2 := congrArg (fun f : ℕ →₀ ℕ => f 2) hfac
  simp only [Finsupp.add_apply, hAfac, hmodd, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, hqodd, add_zero] at hfac2
  rw [hk, hfac2]

private theorem sylow_image_card {H : Type} [Group H] [Finite H] {n : ℕ} (hn : 1 ≤ n)
    {S : Subgroup H} (hS : IsSylowTwoOf S (⊤ : Subgroup H))
    {ψ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψ : Function.Surjective ψ) (hψker : ψ.ker = CFSG.pCore 2 H)
    (hquot : IsL2Quot n (oTwoQuot H))
    (hQHcard : Nat.card ↥(CFSG.pCore 2 H) = 2 ^ (2 * n)) :
    Nat.card ↥(S.map ψ) = 2 ^ n := by
  have hSidx : ¬ 2 ∣ S.index := not_two_dvd_index_of_isSylowTwoOf_top hS
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (G := ↥(S.map ψ)) (hS.2.1.map ψ)
  exact eq_pow_of_mul_odd_index hSidx hn ⟨k, hk⟩
    (sylow_image_mul_index hn hS hψ hψker hquot hQHcard)

private def secRepToAdd {H : Type} [Group H] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W) :
    ↥(CFSG.pCore 2 H) → W :=
  fun q => Multiplicative.toAdd (s.cls q : Multiplicative W)

private theorem secRepToAdd_one {H : Type} [Group H] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W) :
    secRepToAdd s 1 = 0 := by
  show Multiplicative.toAdd (s.cls (1 : ↥(CFSG.pCore 2 H)) : Multiplicative W) = 0
  rw [map_one]
  rfl

private theorem secRepToAdd_mul {H : Type} [Group H] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W) (a b : ↥(CFSG.pCore 2 H)) :
    secRepToAdd s (a * b) = secRepToAdd s a + secRepToAdd s b := by
  show Multiplicative.toAdd (s.cls (a * b) : Multiplicative W) =
    Multiplicative.toAdd (s.cls a : Multiplicative W) +
      Multiplicative.toAdd (s.cls b : Multiplicative W)
  rw [map_mul]
  rfl

private theorem secRep_cls_injective {H : Type} [Group H] [Finite H] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W) :
    Function.Injective s.cl := by
  intro a b hab
  have hab' : s.cls a = s.cls b := hab
  have h1 : s.cls (a * b⁻¹) = (1 : Multiplicative W) := by
    rw [map_mul, map_inv, hab']
    exact mul_inv_cancel _
  have h2 : ((a * b⁻¹ : ↥(CFSG.pCore 2 H)) : H) ∈ (⊥ : Subgroup H) :=
    (s.ker (a * b⁻¹)).mp h1
  have h3 : (a * b⁻¹ : ↥(CFSG.pCore 2 H)) = (1 : ↥(CFSG.pCore 2 H)) :=
    Subtype.ext (Subgroup.mem_bot.mp h2)
  exact mul_inv_eq_one.mp h3

private theorem exists_nontrivial_secRep_action {H : Type} [Group H] [Finite H]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (hcls_inj : Function.Injective s.cl)
    (hnc : ∃ l : H, l ∉ Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)) :
    ∃ (l' : ↥(⊤ : Subgroup H)) (v0 : ↥(CFSG.pCore 2 H)),
      (s.ρ l') (secRepToAdd s v0) ≠ secRepToAdd s v0 := by
  classical
  obtain ⟨l, hl⟩ := hnc
  rw [Subgroup.mem_centralizer_iff] at hl
  push Not at hl
  obtain ⟨q, hqQ, hql⟩ := hl
  let l' : ↥(⊤ : Subgroup H) := ⟨l, Subgroup.mem_top l⟩
  let v0 : ↥(CFSG.pCore 2 H) := ⟨q, hqQ⟩
  have hconjQ : l * q * l⁻¹ ∈ CFSG.pCore 2 H :=
    (CFSG.pCore_normal (p := 2) (G := H)).conj_mem q hqQ l
  have hfix : (s.ρ l') (secRepToAdd s v0) ≠ secRepToAdd s v0 := by
    intro heq
    let m : ↥(CFSG.pCore 2 H) := ⟨l * q * l⁻¹, hconjQ⟩
    have hact := s.act l' v0 m (by rfl)
    have hact' : (s.ρ l') (secRepToAdd s v0) = secRepToAdd s m := hact
    have hcls : s.cl m = s.cl v0 := by
      apply Multiplicative.toAdd.injective
      rw [hact'] at heq
      exact heq
    have hm : m = v0 := hcls_inj hcls
    have hconj_eq : l * q * l⁻¹ = q := congrArg Subtype.val hm
    have hcomm : l * q = q * l := by
      have := congrArg (fun x => x * l) hconj_eq
      simpa [mul_assoc] using this
    exact hql hcomm.symm
  exact ⟨l', v0, hfix⟩

private theorem card_of_secRep {H : Type} [Group H] [Finite H] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (hcls_inj : Function.Injective s.cl)
    (hQHcard : Nat.card ↥(CFSG.pCore 2 H) = 2 ^ (2 * n)) :
    Nat.card W = 2 ^ (2 * n) := by
  have hbij : Function.Bijective s.cl := ⟨hcls_inj, s.surj⟩
  calc Nat.card W = Nat.card (Multiplicative W) := rfl
    _ = Nat.card ↥(CFSG.pCore 2 H) :=
        (Nat.card_congr (Equiv.ofBijective s.cl hbij)).symm
    _ = 2 ^ (2 * n) := hQHcard

private theorem fixedSub_card_ge {H : Type} [Group H] [Finite H] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (hcls_inj : Function.Injective s.cl)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W)
    {ψ : H →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hψeq : ∀ t : H,
      ρ (ψ t) = (s.ρ ((Subgroup.topEquiv (G := H)).symm t)).toLinearMap)
    {S : Subgroup H}
    (hC' : 2 ^ n ≤ Nat.card ↥((CFSG.pCore 2 H) ⊓
      Subgroup.centralizer (S : Set H))) :
    2 ^ n ≤ Nat.card (fixedSub ρ (S.map ψ)) := by
  classical
  have hfixmem : ∀ v : ↥((CFSG.pCore 2 H) ⊓ Subgroup.centralizer (S : Set H)),
      secRepToAdd s ⟨v.1, v.2.1⟩ ∈ fixedSub ρ (S.map ψ) := by
    intro v
    rw [mem_fixedSub]
    intro a ha
    obtain ⟨t, ht, rfl⟩ := ha
    rw [hψeq t]
    have hcomm : t * v.1 = v.1 * t :=
      Subgroup.mem_centralizer_iff.mp v.2.2 t ht
    have hact := s.act ((Subgroup.topEquiv (G := H)).symm t)
      ⟨v.1, v.2.1⟩ ⟨v.1, v.2.1⟩ (by
        simp only [Subgroup.topEquiv_symm_apply_coe]
        rw [hcomm]
        group)
    exact hact
  let g : ↥((CFSG.pCore 2 H) ⊓ Subgroup.centralizer (S : Set H)) →
      fixedSub ρ (S.map ψ) := fun v =>
    ⟨secRepToAdd s ⟨v.1, v.2.1⟩, hfixmem v⟩
  have ginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    have h1 : (⟨v.1, v.2.1⟩ : ↥(CFSG.pCore 2 H)) = ⟨w.1, w.2.1⟩ := by
      apply hcls_inj
      apply Multiplicative.toAdd.injective
      exact congrArg Subtype.val hvw
    exact congrArg (fun z : ↥(CFSG.pCore 2 H) => (z.1 : H)) h1
  exact le_trans hC' (Nat.card_le_card_of_injective g ginj)

private theorem card_lt_fixedSub_pow_four {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {F : Type} [Field F] [Fintype F]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hn : 2 ≤ n)
    (hWcard : Nat.card W = 2 ^ (2 * n))
    (hfixcard : 2 ^ n ≤ Nat.card (fixedSub ρ A)) :
    Nat.card W < Nat.card (fixedSub ρ A) ^ 4 := by
  rw [hWcard]
  have hpow : (2 ^ n) ^ 4 = 2 ^ (4 * n) := by
    rw [← pow_mul]
    ring_nf
  calc 2 ^ (2 * n) < 2 ^ (4 * n) :=
        (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
    _ = (2 ^ n) ^ 4 := hpow.symm
    _ ≤ Nat.card (fixedSub ρ A) ^ 4 := Nat.pow_le_pow_left hfixcard 4

private def naturalModuleMap {H : Type} [Group H] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (φT : W ≃+ (Fin 2 → GaloisField 2 n))
    (hshortU : CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H) :
    ↥(CFSG.RankThree.PartOne.shortU H) →* Multiplicative (Fin 2 → GaloisField 2 n) :=
  { toFun := fun u => Multiplicative.ofAdd
      (φT (secRepToAdd s ⟨u.1, hshortU ▸ u.2⟩))
    map_one' := by
      show Multiplicative.ofAdd (φT (secRepToAdd s ⟨1, _⟩)) = 1
      rw [show (⟨1, _⟩ : ↥(CFSG.pCore 2 H)) = 1 from Subtype.ext rfl,
        secRepToAdd_one, map_zero]
      rfl
    map_mul' := fun a b => by
      show Multiplicative.ofAdd (φT (secRepToAdd s ⟨(a * b).1, _⟩)) =
        Multiplicative.ofAdd (φT (secRepToAdd s ⟨a.1, _⟩)) *
          Multiplicative.ofAdd (φT (secRepToAdd s ⟨b.1, _⟩))
      rw [show (⟨(a * b).1, _⟩ : ↥(CFSG.pCore 2 H)) = ⟨a.1, _⟩ * ⟨b.1, _⟩ from
        Subtype.ext rfl, secRepToAdd_mul, map_add]
      rfl }

private theorem naturalModuleMap_surjective {H : Type} [Group H] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (φT : W ≃+ (Fin 2 → GaloisField 2 n))
    (hshortU : CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H) :
    Function.Surjective (naturalModuleMap s φT hshortU) := by
  intro y
  obtain ⟨q, hq⟩ := s.surj
    (Multiplicative.ofAdd (φT.symm (Multiplicative.toAdd y)))
  refine ⟨(⟨q.1, hshortU.symm ▸ q.2⟩ : ↥(CFSG.RankThree.PartOne.shortU H)), ?_⟩
  change φT (secRepToAdd s ⟨q.1, _⟩) = Multiplicative.toAdd y
  rw [show (⟨q.1, _⟩ : ↥(CFSG.pCore 2 H)) = q from Subtype.ext rfl]
  have hq' : secRepToAdd s q = φT.symm (Multiplicative.toAdd y) := by
    show Multiplicative.toAdd (s.cls q : Multiplicative W) =
      φT.symm (Multiplicative.toAdd y)
    rw [hq]
    rfl
  rw [hq']
  simp

private theorem naturalModuleMap_ker {H : Type} [Group H] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (φT : W ≃+ (Fin 2 → GaloisField 2 n))
    (hshortU : CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H)
    (hshortC : CFSG.RankThree.PartOne.shortC H = ⊥) :
    (naturalModuleMap s φT hshortU).ker =
      (CFSG.RankThree.PartOne.shortC H).subgroupOf
        (CFSG.RankThree.PartOne.shortU H) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hshortC, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : φT (secRepToAdd s ⟨u.1, hshortU ▸ u.2⟩) = 0 := by
      change Multiplicative.ofAdd (φT (secRepToAdd s ⟨u.1, hshortU ▸ u.2⟩)) =
        (1 : Multiplicative (Fin 2 → GaloisField 2 n)) at h
      exact h
    have h2 : secRepToAdd s ⟨u.1, hshortU ▸ u.2⟩ = 0 :=
      φT.injective (by simpa using h1)
    have h3 : s.cls ⟨u.1, hshortU ▸ u.2⟩ = (1 : Multiplicative W) := by
      apply Multiplicative.toAdd.injective
      change secRepToAdd s ⟨u.1, hshortU ▸ u.2⟩ = (0 : W)
      rw [h2]
    have h4 : ((⟨u.1, hshortU ▸ u.2⟩ : ↥(CFSG.pCore 2 H)) : H) ∈ (⊥ : Subgroup H) :=
      (s.ker _).mp h3
    have h5 : (⟨u.1, hshortU ▸ u.2⟩ : ↥(CFSG.pCore 2 H)) = (1 : ↥(CFSG.pCore 2 H)) := by
      apply Subtype.ext
      simpa using Subgroup.mem_bot.mp h4
    exact congrArg Subtype.val h5
  · intro h
    have hu : (⟨u.1, hshortU ▸ u.2⟩ : ↥(CFSG.pCore 2 H)) = (1 : ↥(CFSG.pCore 2 H)) :=
      Subtype.ext h
    change Multiplicative.ofAdd (φT (secRepToAdd s ⟨u.1, hshortU ▸ u.2⟩)) =
      (1 : Multiplicative (Fin 2 → GaloisField 2 n))
    rw [hu, secRepToAdd_one, map_zero]
    rfl

private theorem naturalModuleMap_equivariant {H : Type} [Group H] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (φT : W ≃+ (Fin 2 → GaloisField 2 n))
    (hshortU : CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) W)
    {ψH : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψeq : ∀ t : H,
      ρ (ψH t) = (s.ρ ((Subgroup.topEquiv (G := H)).symm t)).toLinearMap)
    (hφT : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) (w : W),
      φT (ρ g w) = (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (φT w))
    (φ : (H ⧸ CFSG.pCore 2 H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφmk : ∀ x : H, φ (QuotientGroup.mk x) = ψH x) :
    ∀ (l u : H) (hu : u ∈ CFSG.RankThree.PartOne.shortU H)
      (hu' : l * u * l⁻¹ ∈ CFSG.RankThree.PartOne.shortU H),
      naturalModuleMap s φT hshortU ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd
        (((φ (l : H ⧸ CFSG.pCore 2 H) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (naturalModuleMap s φT hshortU ⟨u, hu⟩))) := by
  intro l u hu hu'
  set uQ : ↥(CFSG.pCore 2 H) := ⟨u, hshortU ▸ hu⟩
  set vQ : ↥(CFSG.pCore 2 H) := ⟨l * u * l⁻¹, hshortU ▸ hu'⟩
  set l' : ↥(⊤ : Subgroup H) := ⟨l, Subgroup.mem_top l⟩
  have hact := s.act l' uQ vQ (by rfl)
  have hact' : (s.ρ l') (secRepToAdd s uQ) = secRepToAdd s vQ := hact
  have hρapply : ∀ w : W, (s.ρ l') w = (ρ (ψH l)) w := by
    intro w
    have hρeq : (s.ρ l').toLinearMap = ρ (ψH l) := by
      rw [hψeq l]
      congr 1
    rw [← hρeq]
    rfl
  calc naturalModuleMap s φT hshortU ⟨l * u * l⁻¹, hu'⟩
      = Multiplicative.ofAdd (φT (secRepToAdd s vQ)) := rfl
    _ = Multiplicative.ofAdd (φT ((s.ρ l') (secRepToAdd s uQ))) := by rw [hact']
    _ = Multiplicative.ofAdd (φT ((ρ (ψH l)) (secRepToAdd s uQ))) := by rw [hρapply]
    _ = Multiplicative.ofAdd
        (((ψH l : Matrix (Fin 2) (Fin 2) (GaloisField 2 n))).mulVec
          (φT (secRepToAdd s uQ))) := by rw [hφT]
    _ = Multiplicative.ofAdd
        (((φ (QuotientGroup.mk l) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n))).mulVec
          (φT (secRepToAdd s uQ))) := by rw [← hφmk l]
    _ = Multiplicative.ofAdd
        (((φ (QuotientGroup.mk l) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (naturalModuleMap s φT hshortU ⟨u, hu⟩))) := rfl

private theorem isNaturalSLTwoModule_of_data {H : Type} [Group H] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W]
    (s : SecRep (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H) W)
    (φT : W ≃+ (Fin 2 → GaloisField 2 n))
    (hshortU : CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H)
    (hshortC : CFSG.RankThree.PartOne.shortC H = ⊥)
    {ρ : Representation (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) W}
    {ψH : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψeq : ∀ t : H,
      ρ (ψH t) = (s.ρ ((Subgroup.topEquiv (G := H)).symm t)).toLinearMap)
    (hφT : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) (w : W),
      φT (ρ g w) = (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (φT w))
    (φ : (H ⧸ CFSG.pCore 2 H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφmk : ∀ x : H, φ (QuotientGroup.mk x) = ψH x) :
    CFSG.RankThree.PartOne.IsNaturalSLTwoModule H n := by
  refine ⟨φ, naturalModuleMap s φT hshortU, ?_, ?_, ?_⟩
  · exact naturalModuleMap_surjective s φT hshortU
  · exact naturalModuleMap_ker s φT hshortU hshortC
  · exact naturalModuleMap_equivariant s φT hshortU ρ hψeq hφT φ hφmk

private theorem isNaturalSLTwoModule_of_local_data {H : Type} [Group H] [Finite H] {n : ℕ}
    (hn : 2 ≤ n) (hquot : IsL2Quot n (oTwoQuot H))
    (hshortU : CFSG.RankThree.PartOne.shortU H = CFSG.pCore 2 H)
    (hshortC : CFSG.RankThree.PartOne.shortC H = ⊥)
    (hsec : SecHyp (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H))
    (hchief : IsChiefPair (⊤ : Subgroup H) ⊥ (CFSG.pCore 2 H))
    (hnc : ∃ l : H, l ∉ Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H))
    (hQHcard : Nat.card ↥(CFSG.pCore 2 H) = 2 ^ (2 * n))
    {S : Subgroup H} (hS : IsSylowTwoOf S (⊤ : Subgroup H))
    (hC' : 2 ^ n ≤ Nat.card ↥((CFSG.pCore 2 H) ⊓
      Subgroup.centralizer (S : Set H))) :
    CFSG.RankThree.PartOne.IsNaturalSLTwoModule H n := by
  classical
  obtain ⟨W, hWadd, hWmod, hWfin, ⟨s⟩⟩ := exists_secRep hsec
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hcls_inj : Function.Injective s.cl := secRep_cls_injective s
  obtain ⟨l', v0, hfix⟩ := exists_nontrivial_secRep_action s hcls_inj hnc
  have hkerP : CFSG.pCore 2 ↥(⊤ : Subgroup H) ≤ s.ρ.ker :=
    pCore_le_secRep_ker s hsec hchief
  have hquotTop : IsL2Quot n (oTwoQuot ↥(⊤ : Subgroup H)) := by
    obtain ⟨eL⟩ := hquot
    let eTop : H ≃* ↥(⊤ : Subgroup H) := (Subgroup.topEquiv (G := H)).symm
    exact ⟨((QuotientGroup.congr (CFSG.pCore 2 H)
      (CFSG.pCore 2 ↥(⊤ : Subgroup H)) eTop (CFSG.pCore_map_iso 2 eTop))).symm.trans eL⟩
  obtain ⟨ρ, hρirr, hρnt, ψ, hψsurj, hψeq⟩ :=
    exists_irreducible_SL2_rep hquotTop hsec hchief s hkerP l' v0 hfix
  let F := GaloisField 2 n
  letI : Fintype F := Fintype.ofFinite _
  haveI : CharP F 2 := inferInstance
  have hFcard : Fintype.card F = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card] <;> omega
  let ψH : H →* Matrix.SpecialLinearGroup (Fin 2) F :=
    ψ.comp (Subgroup.topEquiv (G := H)).symm.toMonoidHom
  have hψHsurj : Function.Surjective ψH :=
    hψsurj.comp (Subgroup.topEquiv (G := H)).symm.surjective
  have hψHker : ψH.ker = CFSG.pCore 2 H :=
    ker_eq_pCore_of_surjective (by omega) hψHsurj hquot hQHcard
  let φ : (H ⧸ CFSG.pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    QuotientGroup.liftEquiv (CFSG.pCore 2 H) hψHsurj hψHker.symm
  have hφmk : ∀ x : H, φ (QuotientGroup.mk x) = ψH x := fun x =>
    QuotientGroup.liftEquiv_coe _ hψHsurj hψHker.symm x
  have hA2 : ∀ a ∈ S.map ψH, a * a = 1 := sylow_image_sq_eq_one hS
  have hA : Nat.card ↥(S.map ψH) = 2 ^ n :=
    sylow_image_card (by omega) hS hψHsurj hψHker hquot hQHcard
  have hψHeq : ∀ t : H,
      ρ (ψH t) = (s.ρ ((Subgroup.topEquiv (G := H)).symm t)).toLinearMap := fun t =>
    hψeq ((Subgroup.topEquiv (G := H)).symm t)
  have hIn : Nat.card W < Nat.card (fixedSub ρ (S.map ψH)) ^ 4 :=
    card_lt_fixedSub_pow_four ρ (S.map ψH) hn (card_of_secRep s hcls_inj hQHcard)
      (fixedSub_card_ge s hcls_inj ρ hψHeq hC')
  haveI : Fact ρ.IsIrreducible := ⟨hρirr⟩
  obtain ⟨φT, hφT⟩ := CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_of_card_lt
    (by omega : 1 ≤ n) hFcard ρ hρnt (S.map ψH) hA2 hA hIn
  exact isNaturalSLTwoModule_of_data s φT hshortU hshortC hψHeq hφT φ hφmk
theorem isLin2Type_of_card_centralizer {L T : Subgroup G} [Finite ↥L] {n : ℕ} (hn : 2 ≤ n)
    (hc : CharTwo L) (hquot : IsL2Quot n (oTwoQuot ↥L)) (he : IsElemAbelian 2 (pCoreOf 2 L))
    (hirr : ∀ W : Subgroup G, W ≤ pCoreOf 2 L → L ≤ Subgroup.normalizer (W : Set G) →
      W = ⊥ ∨ W = pCoreOf 2 L)
    (hcard : Nat.card (pCoreOf 2 L) = 2 ^ (2 * n)) (hT : IsSylowTwoOf T L)
    (hC : 2 ^ n ≤ Nat.card ↥(pCoreOf 2 L ⊓ Subgroup.centralizer (T : Set G))) :
    IsLin2Type L n := by
  classical
  let QH : Subgroup ↥L := CFSG.pCore 2 ↥L
  let SH : Subgroup ↥L := T.subgroupOf L
  have hQHcard : Nat.card ↥QH = 2 ^ (2 * n) := pCore_card_eq_pow hcard
  have heH : IsElemAbelian 2 QH := isElemAbelian_pCore he
  have hirrH : ∀ W : Subgroup ↥L, W ≤ QH →
      (⊤ : Subgroup ↥L) ≤ Subgroup.normalizer (W : Set ↥L) → W = ⊥ ∨ W = QH :=
    irreducible_pCore hirr
  have hcentH : Subgroup.centralizer ((QH : Subgroup ↥L) : Set ↥L) ≤ QH :=
    centralizer_pCore_le hc
  have hSHsyl : IsSylowTwoOf SH (⊤ : Subgroup ↥L) := isSylowTwoOf_subgroupOf_top hT
  have hC' : 2 ^ n ≤ Nat.card ↥(QH ⊓
      Subgroup.centralizer ((SH : Subgroup ↥L) : Set ↥L)) :=
    card_centralizer_pCore_ge hC
  have hnc : ∃ l : ↥L, l ∉ Subgroup.centralizer ((QH : Subgroup ↥L) : Set ↥L) :=
    exists_not_mem_centralizer_pCore (by omega) hcentH hquot
  have hshortU : CFSG.RankThree.PartOne.shortU ↥L = QH := shortU_eq_pCore hirrH hnc
  have hshortC : CFSG.RankThree.PartOne.shortC ↥L = ⊥ := shortC_eq_bot hirrH hnc
  have hQHne : QH ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot QH]
    rw [hQHcard]
    exact Nat.one_lt_two_pow (by omega)
  have hsec : SecHyp (⊤ : Subgroup ↥L) ⊥ QH := secHyp_top_bot_pCore heH
  have hchief : IsChiefPair (⊤ : Subgroup ↥L) ⊥ QH :=
    isChiefPair_top_bot_pCore hQHne hirrH
  exact CFSG.AGLEmbedding.LocalCGT.isLin2Type_of_isNaturalSLTwoModule (by omega)
    (isNaturalSLTwoModule_of_local_data hn hquot hshortU hshortC hsec hchief hnc
      hQHcard hSHsyl hC')

end CFSG.Quasithin.St84
