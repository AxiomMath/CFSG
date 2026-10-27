module

public import CFSG.OddTranspositions.O4CloseReduction
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
import CFSG.LocalAnalysis.OddStandard.SmallAltFiveAlt5
import CFSG.OddTranspositions.O4PairCommSet
import CFSG.OddTranspositions.HalphaNonsolvable
import CFSG.OddTranspositions.FixKS5
import CFSG.OddTranspositions.PartThree.EightEight.OFourMinus
import CFSG.GroupTheory.InvolutionPow
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.SixEight
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.QZ

private theorem N1_eq_bot_of_map_eq_bot {N₁ : Subgroup Yten}
    (hKbot : N₁.map leftHomYten = ⊥) (hN₁odd : Odd (Nat.card N₁)) : N₁ = ⊥ := by
  have hle_ker : N₁ ≤ leftHomYten.ker := (Subgroup.map_eq_bot_iff N₁).1 hKbot
  apply le_bot_iff.mp
  intro n hn
  have hnker : leftHomYten n = 1 := hle_ker hn
  have hn1 : n = 1 := by
    rcases CFSG.OddTranspositions.PartThree.EightEight.eq_one_or_eq_inr_frob25_of_leftHomYten_eq_one
      hnker with h | h
    · exact Subtype.ext h
    · have hn2 : n * n = 1 := by
        apply Subtype.ext
        show (n : PSigmaL225) * (n : PSigmaL225) = 1
        rw [h, ← map_mul, frob25_mul_self, map_one]
      exact (CFSG.GroupTheory.pow_eq_self_of_odd_of_mul_self_eq_one hn2
        (hN₁odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₁ hn))).symm.trans
        (pow_orderOf_eq_one n)
  exact hn1

private theorem closure_leftY_top : Subgroup.closure (Set.range leftY) = ⊤ := by
  have hpre : FixK.subtype ⁻¹' Set.range (fun i : Fin 10 => (y i).left) =
      Set.range (fun i => leftY i) := by
    ext q
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have h := Subgroup.closure_preimage_eq_top (s := Set.range (fun i : Fin 10 => (y i).left))
  rw [closure_left_y_eq_FixK] at h
  rw [← hpre]
  exact h

private theorem o4_K_normal {X : Type} [Group X] {E : Set X} {c : X}
    {φ : X ≃* PSigmaL225} {N : Subgroup X} {N₁ : Subgroup Yten}
    (hN₁ : ∀ n : Yten, n ∈ N₁ ↔ (n : PSigmaL225) ∈ N.map (φ : X →* PSigmaL225))
    (hN₁odd : Odd (Nat.card N₁))
    (hcommimage : φ '' commSet E c = Set.range y)
    (hnorm : ∀ t ∈ commSet E c, ∀ n ∈ N, t * n * t⁻¹ ∈ N) :
    (N₁.map leftHomYten).Normal ∧ Odd (Nat.card (N₁.map leftHomYten)) := by
  have ht : ∀ i : Fin 10, ∃ u ∈ commSet E c, φ u = y i := by
    intro i
    have hi : y i ∈ φ '' commSet E c := by rw [hcommimage]; exact ⟨i, rfl⟩
    obtain ⟨u, hu, hueq⟩ := hi
    exact ⟨u, hu, hueq⟩
  choose t htmem htphi using ht
  have hyten (i : Fin 10) : y i ∈ Yten := Subgroup.subset_closure (Set.mem_range_self i)
  have hN₁conj : ∀ (i : Fin 10) (n : Yten), n ∈ N₁ →
      (⟨y i, hyten i⟩ : Yten) * n * (⟨y i, hyten i⟩ : Yten)⁻¹ ∈ N₁ := by
    intro i n hn
    obtain ⟨n', hn', hn'eq⟩ := (hN₁ n).1 hn
    have hconj : t i * n' * (t i)⁻¹ ∈ N := hnorm (t i) (htmem i) n' hn'
    refine (hN₁ _).2 ⟨t i * n' * (t i)⁻¹, hconj, ?_⟩
    calc φ (t i * n' * (t i)⁻¹)
        = φ (t i) * φ n' * (φ (t i))⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = Yten.subtype (⟨y i, hyten i⟩ * n * ⟨y i, hyten i⟩⁻¹) := by
            rw [htphi i]
            rw [show φ n' = Yten.subtype n from hn'eq]
            rfl
  let K : Subgroup FixK := N₁.map leftHomYten
  have hgen_eq : (fun i : Fin 10 => leftHomYten (⟨y i, hyten i⟩ : Yten)) = leftY := by
    funext i
    apply Subtype.ext
    rfl
  have hKconj : ∀ (i : Fin 10) (k : FixK), k ∈ K →
      leftHomYten (⟨y i, hyten i⟩ : Yten) * k * (leftHomYten (⟨y i, hyten i⟩ : Yten))⁻¹ ∈ K := by
    intro i k hk
    obtain ⟨n, hn, rfl⟩ := hk
    refine ⟨(⟨y i, hyten i⟩ : Yten) * n * (⟨y i, hyten i⟩ : Yten)⁻¹,
      hN₁conj i n hn, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hclosure : Subgroup.closure (Set.range
      (fun i : Fin 10 => leftHomYten (⟨y i, hyten i⟩ : Yten))) = ⊤ := by
    rw [hgen_eq, closure_leftY_top]
  have hKnormal : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hclosure, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_normalizer_fintype fun k hk => hKconj i k hk
  have hKodd : Odd (Nat.card K) :=
    hN₁odd.of_dvd_nat (Subgroup.card_map_dvd N₁ leftHomYten)
  exact ⟨hKnormal, hKodd⟩

private theorem o4_N1_bot {X : Type} [Group X] {E : Set X} {c : X}
    {φ : X ≃* PSigmaL225} {N : Subgroup X} {N₁ : Subgroup Yten}
    (hN₁ : ∀ n : Yten, n ∈ N₁ ↔ (n : PSigmaL225) ∈ N.map (φ : X →* PSigmaL225))
    (hN₁odd : Odd (Nat.card N₁))
    (hcommimage : φ '' commSet E c = Set.range y)
    (hnorm : ∀ t ∈ commSet E c, ∀ n ∈ N, t * n * t⁻¹ ∈ N) : N₁ = ⊥ := by
  obtain ⟨hKnormal, hKodd⟩ := o4_K_normal hN₁ hN₁odd hcommimage hnorm
  obtain ⟨e, -⟩ := fixK_equiv_s5
  have hKmap_bot : (N₁.map leftHomYten).map (e : FixK →* Equiv.Perm (Fin 5)) = ⊥ := by
    have : ((N₁.map leftHomYten).map (e : FixK →* Equiv.Perm (Fin 5))).Normal :=
      hKnormal.map (e : FixK →* Equiv.Perm (Fin 5)) e.surjective
    exact CFSG.OddStandard.eq_bot_of_normal_odd_perm_five _
      (hKodd.of_dvd_nat (Subgroup.card_map_dvd _ (e : FixK →* Equiv.Perm (Fin 5))))
  have hKbot : N₁.map leftHomYten = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hKmap_bot
  exact N1_eq_bot_of_map_eq_bot hKbot hN₁odd

theorem eq_bot_of_o4PairData {X : Type} [Group X] {E : Set X} (hO4 : O4PairData X E) {c : X}
    (hc : c ∈ E) {N : Subgroup X} (hN : Odd (Nat.card N))
    (hle : N ≤ Subgroup.closure (commSet E c))
    (hnorm : ∀ t ∈ commSet E c, ∀ n ∈ N, t * n * t⁻¹ ∈ N) : N = ⊥ := by
  classical
  obtain ⟨φ, hφD, hφc⟩ := exists_mulEquiv_of_mem hO4 hc
  have hcommimage : φ '' commSet E c = Set.range y := image_commSet_eq_range_y hφD hφc
  have hNmap_le : N.map (φ : X →* PSigmaL225) ≤ Yten := by
    rintro x ⟨n, hn, rfl⟩
    have hncl : n ∈ Subgroup.closure (commSet E c) := hle hn
    have hmem : φ n ∈ (Subgroup.closure (commSet E c)).map (φ : X →* PSigmaL225) :=
      ⟨n, hncl, rfl⟩
    rw [MonoidHom.map_closure] at hmem
    have hmem' : φ n ∈ Subgroup.closure (φ '' commSet E c) := by simpa using hmem
    rwa [hcommimage] at hmem'
  let N₁ : Subgroup Yten := (N.map φ).subgroupOf Yten
  have hN₁card : Nat.card N₁ = Nat.card (N.map (φ : X →* PSigmaL225)) := by
    change Nat.card ((N.map (φ : X →* PSigmaL225)).subgroupOf Yten) =
      Nat.card (N.map (φ : X →* PSigmaL225))
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNmap_le).toEquiv
  have hN₁odd : Odd (Nat.card N₁) := by
    rw [hN₁card]
    exact hN.of_dvd_nat (Subgroup.card_map_dvd N (φ : X →* PSigmaL225))
  have hN₁bot : N₁ = ⊥ := o4_N1_bot (fun n => Iff.rfl) hN₁odd hcommimage hnorm
  have hmap_bot : N.map (φ : X →* PSigmaL225) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxY : x ∈ Yten := hNmap_le hx
    have hmem : (⟨x, hxY⟩ : Yten) ∈ N₁ := hx
    rw [hN₁bot] at hmem
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
  exact (Subgroup.map_eq_bot_iff_of_injective N φ.injective).mp hmap_bot

end CFSG.OddTranspositions.PartThree.ElevenThree
