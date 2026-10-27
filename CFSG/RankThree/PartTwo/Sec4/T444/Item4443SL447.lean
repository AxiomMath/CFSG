module

import CFSG.RankThree.PartTwo.Sec4.Item447Proof
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec4.Steps444
import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup CFSG.RankThreeEvenClassification.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_complement {A C : Subgroup G} (hCA : C ≤ centralizer (A : Set G))
    (h3 : ∀ y ∈ C, y ^ 3 = 1 → y ∈ A) :
    ∃ N : Subgroup G, N ≤ C ∧ C ≤ normalizer (N : Set G) ∧ ¬ 3 ∣ Nat.card N ∧
      ∀ y ∈ C, ¬ 3 ∣ orderOf y → y ∈ N := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcrit : ∀ Q : Subgroup C, IsPGroup 3 Q → IsPGroup 3 (normalizer (Q : Set C) ⧸
      (centralizer (Q : Set C)).subgroupOf (normalizer (Q : Set C))) := by
    intro Q hQ g
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨e, m, hm3, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    set y := n ^ (3 ^ e) with hy
    have hyord : orderOf y = m := by
      rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) ⟨m, hord⟩, hord,
        Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
    set yC : C := (y : C) with hyC
    have hyN : yC ∈ normalizer (Q : Set C) := y.2
    have hyN' : zpowers yC ≤ normalizer (Q : Set C) := zpowers_le.mpr hyN
    let _ : MulDistribMulAction (zpowers yC) Q :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (zpowers yC) Q hyN'
    have hsmul : ∀ (a : zpowers yC) (q : Q), (((a • q : Q) : C) : C) =
        (a : C) * (q : C) * (a : C)⁻¹ := fun _ _ => rfl
    have : Fact (IsPGroup 3 Q) := ⟨hQ⟩
    have hcop : Nat.Coprime (Nat.card (zpowers yC)) (Nat.card Q) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
    have hE : ∃ _ : Fact (IsPGroup 3 (⊥ : Subgroup Q)), IsElementaryAbelian 3 (⊥ : Subgroup Q) :=
      ⟨⟨IsPGroup.of_card (n := 0) (by simp)⟩,
        { toIsMulCommutative := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
            Subsingleton.elim _ _ }⟩
    have htriv : ActsTrivially (zpowers yC) Q := by
      refine corollary_1_12 (p := 3) (by norm_num) ⊥ hE hcop ?_
      intro g _ hg a
      have hg3 : (((g : C) : G)) ^ 3 = 1 := by
        have : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
        simpa using congrArg (fun z : Q => ((z : C) : G)) this
      have hgA : ((g : C) : G) ∈ A := h3 _ (g : C).2 hg3
      apply Subtype.ext
      apply Subtype.ext
      rw [hsmul]
      have hcomm := mem_centralizer_iff.mp (hCA ((a : C).2)) _ hgA
      change (((a : C) : G) * ((g : C) : G) * ((a : C) : G)⁻¹) = ((g : C) : G)
      rw [← hcomm, mul_inv_cancel_right]
    refine Subgroup.mem_subgroupOf.mpr (mem_centralizer_iff.mpr fun q hq => ?_)
    have h1 := htriv ⟨yC, mem_zpowers yC⟩ ⟨q, hq⟩
    have h2 := congrArg (fun z : Q => (z : C)) h1
    simp only at h2
    rw [hsmul] at h2
    change yC * q * yC⁻¹ = q at h2
    calc q * yC = (yC * q * yC⁻¹) * yC := by rw [h2]
      _ = yC * q := by group
  obtain ⟨N₀, hN₀n, hN₀c, k, hk⟩ := (CFSG.GroupTheory.frobenius_normal_p_complement 3).1.2 hcrit
  refine ⟨N₀.map C.subtype, map_subtype_le _, fun c hc => ?_, ?_, fun y hy hy3 => ?_⟩
  · have h := le_normalizer_map (H := N₀) C.subtype
    rw [normalizer_eq_top_iff.mpr hN₀n, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h hc
  · rw [card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN₀c.symm
  · refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have h1 : orderOf (QuotientGroup.mk' N₀ (⟨y, hy⟩ : C)) ∣ orderOf y := by
      rw [← Subgroup.orderOf_mk y hy]
      exact orderOf_map_dvd _ _
    have h2 : orderOf (QuotientGroup.mk' N₀ (⟨y, hy⟩ : C)) ∣ 3 ^ k := by
      rw [← hk, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf y) (3 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hy3).symm
    have h3' := CFSG.GroupTheory.FrobeniusNormalComplement.orderOf_eq_one_of_dvd hcop h1 h2
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3'

theorem mem_normalizer_of_mem_centralizer (h45 : Item4_5) {A M : Subgroup G} (h : Ctx444 G A M)
    {s : G} (hsA : s ∈ centralizer (A : Set G)) (hs3 : ¬ 3 ∣ Nat.card (zpowers s))
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M) :
    s ∈ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  set K := L.map ρ with hKdef
  set Z : Subgroup (G ⧸ N) := (center K).map K.subtype with hZdef
  set W := Z ⊔ A.map ρ with hWdef
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hAL : A ≤ normalizer (L : Set G) :=
    h45 G h.sectionFourHyp A hA3 (Or.inr ⟨h.isE27.1, 3, le_rfl, by rw [h.isE27.2]; norm_num⟩) L hL
  obtain ⟨hNs, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := G)
    Nat.prime_three
  have hK : IsComponent K := isComponent_map_of_mem_thetaComponents Nat.prime_three hL
  have hθ : aschbacherSolvableCore 3 (G ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers Nat.prime_three N hNs hN3).2.2.1
  have hZO : Z ≤ CFSG.pCore 3 (G ⧸ N) := Item447.center_component_le_pCore_three hθ hK
  have hZp : IsPGroup 3 Z := CFSG.pCore_isPGroup.to_le hZO
  have h3L : 3 ∣ Nat.card L := by
    by_contra h3
    exact hLM (h.le_of_le_normalizer hAL h3)
  have h3K := Item447.three_dvd_card_map_quotient_center hL h3L
  have hAK : A.map ρ ≤ normalizer (K : Set (G ⧸ N)) :=
    (map_mono hAL).trans (le_normalizer_map ρ)
  have hcore := Item447.inSubgroup_pPrimeCore_centralizer_le_normalizer hK hZp h3K (hA3.map ρ) hAK
  have hAs : A ≤ normalizer (zpowers s : Set G) := fun a ha => by
    have hsa : a * s = s * a := (mem_centralizer_iff.mp hsA a ha)
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    change a * s * a⁻¹ = s
    rw [hsa, mul_inv_cancel_right]
  have hS3 : ¬ 3 ∣ Nat.card ((zpowers s).map ρ) := fun h' => hs3 (h'.trans (card_map_dvd _ ρ))
  have hAS : A.map ρ ≤ normalizer (((zpowers s).map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    (map_mono hAs).trans (le_normalizer_map ρ)
  have hPtop : normalizer ((CFSG.pCore 3 (G ⧸ N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = ⊤ :=
    normalizer_eq_top_iff.mpr CFSG.pCore_normal
  have hbender : ⁅CFSG.pCore 3 (G ⧸ N), (zpowers s).map ρ⁆ = ⊥ :=
    commutator_eq_bot_of_bender_quotient h.isE27.1 (fun y hy hy3 => h.rank3II_4_45 hy hy3) hN3
      hS3 hAS CFSG.pCore_isPGroup (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
  have hsZ : ρ s ∈ centralizer (Z : Set (G ⧸ N)) := by
    have hO : (zpowers s).map ρ ≤ centralizer (CFSG.pCore 3 (G ⧸ N) : Set (G ⧸ N)) := by
      rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm, hbender]
    exact centralizer_le hZO (hO (mem_map_of_mem ρ (mem_zpowers s)))
  have hsW : ρ s ∈ centralizer (W : Set (G ⧸ N)) := by
    rw [mem_centralizer_iff]
    have hle : W ≤ centralizer ({ρ s} : Set (G ⧸ N)) := by
      refine sup_le (fun z hz => ?_) ?_
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp hsZ z hz
      · rintro _ ⟨a, ha, rfl⟩
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          (mem_centralizer_iff.mp hsA a ha)]
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hle hw)
  obtain ⟨Nc, hNcC, hCNc, hNc3, hNcmem⟩ := exists_normal_complement (A := A)
    (C := centralizer (A : Set G)) le_rfl (fun y hy hy3 => h.rank3II_4_45 hy hy3)
  have hsNc : s ∈ Nc := hNcmem s hsA (fun h3 => hs3 (by
    rw [Nat.card_zpowers]; exact h3))
  have hCWN : centralizer (W : Set (G ⧸ N)) ≤
      normalizer ((Nc.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro c hc
    have hcA : c ∈ centralizer ((A.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
      centralizer_le (le_sup_right : A.map ρ ≤ W) hc
    obtain ⟨m, hmC, rfl⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel 3
      Nat.prime_three ρ (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk']) A hA3
      c hcA
    exact le_normalizer_map ρ ⟨m, hCNc hmC, rfl⟩
  have hNb3 : ¬ 3 ∣ Nat.card (Nc.map ρ) := fun h' => hNc3 (h'.trans (card_map_dvd Nc ρ))
  have hle : Nc.map ρ ⊓ centralizer (W : Set (G ⧸ N)) ≤
      inSubgroup (CFSG.pPrimeCore 3) (centralizer (W : Set (G ⧸ N))) :=
    le_inSubgroup_pPrimeCore inf_le_right
      (fun c hc => inf_normalizer_le_normalizer_inf ⟨hCWN hc, le_normalizer hc⟩)
      (fun h' => hNb3 (h'.trans (card_dvd_of_le inf_le_left)))
  rw [mem_normalizer_iff_mk_mem_normalizer Nat.prime_three hL]
  exact hcore (hle ⟨mem_map_of_mem ρ hsNc, hsW⟩)

theorem Ctx4443.not_three_dvd_card_zpowers
    {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) : ¬ 3 ∣ Nat.card (zpowers s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (zpowers s) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).to_le (zpowers_le.mpr h.concl4442.1)
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem rank3II_4_47_3_of
    (h45 : Item4_5) :
    ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G), Ctx4443 G A M H s →
      ∀ L ∈ thetaComponents 3 G, ¬ L ≤ M → s ∈ Subgroup.normalizer (L : Set G) := by
  intro G _ _ A M H s h L hL hLM
  exact mem_normalizer_of_mem_centralizer h45 h.ctx444 h.concl4442.2.1
    (Ctx4443.not_three_dvd_card_zpowers h) hL hLM

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
