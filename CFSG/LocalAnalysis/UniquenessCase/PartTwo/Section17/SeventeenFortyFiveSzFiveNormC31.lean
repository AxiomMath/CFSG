module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusProd
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.Quasithin.SteinbergCCOddPlaneActionBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem sz32_card_of_isSz {Y : Type} [Group Y] (hY : IsSz Y 5) :
    Nat.card Y = 32537600 := by
  obtain ⟨a, ha, hn, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hY
  rw [Nat.card_congr (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
    CFSG.SectionRank.card_suzukiMatrixGroup a ha, ← hn]
  norm_num

theorem sz32_normalizer_c31 {Y : Type} [Group Y] [Finite Y]
    (hY : IsSz Y 5) (C : Subgroup Y) (hC : Nat.card C = 31) :
    Nat.card (normalizer (C : Set Y)) = 62 ∧
      ∀ g ∈ normalizer (C : Set Y), g ∉ C → ∀ c ∈ C, g * c * g⁻¹ = c⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hcardY : Nat.card Y = 32537600 := sz32_card_of_isSz hY
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 31 (by rw [hC])
  have hxord : orderOf (x : Y) = 31 := by rw [Subgroup.orderOf_coe, hx]
  have ha1 : (x : Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    omega
  have ha : (x : Y) ^ (2 ^ 5 - 1) = 1 := by
    rw [show 2 ^ 5 - 1 = 31 by norm_num, ← hxord]
    exact pow_orderOf_eq_one _
  obtain ⟨hcomm_cent, hcent_card_a⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.centralizer_of_pow_eq_one_of_isSz hY ha1 ha
  have hCa : C = Subgroup.zpowers (x : Y) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
    rw [Nat.card_zpowers, hxord, hC]
  have hset : (C : Set Y) = (Subgroup.closure ({(x : Y)} : Set Y) : Set Y) :=
    (congrArg (fun H : Subgroup Y => (H : Set Y)) hCa).trans
      (congrArg (fun H : Subgroup Y => (H : Set Y)) (Subgroup.zpowers_eq_closure (x : Y)))
  have hcentC : Subgroup.centralizer (C : Set Y) =
      Subgroup.centralizer ({(x : Y)} : Set Y) := by
    rw [hset, Subgroup.centralizer_closure]
  have hcent_card : Nat.card (Subgroup.centralizer (C : Set Y)) = 31 := by
    rw [hcentC, hcent_card_a]
    norm_num
  have hCcomm : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c := by
    intro c hc d hd
    have hc' : c ∈ Subgroup.zpowers (x : Y) := by rw [← hCa]; exact hc
    have hd' : d ∈ Subgroup.zpowers (x : Y) := by rw [← hCa]; exact hd
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hd'
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow (Commute.refl (x : Y)) m n).eq
  have hle_cent : C ≤ Subgroup.centralizer (C : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hCcomm d hd c hc
  have hcent_eq : Subgroup.centralizer (C : Set Y) = C := by
    have h := Subgroup.eq_of_le_of_card_ge hle_cent (by rw [hcent_card, hC])
    exact h.symm
  let N : Subgroup Y := Subgroup.normalizer (C : Set Y)
  let ρ : ↥N →* MulAut ↥C := Subgroup.normalizerMonoidHom C
  have hker : Nat.card ρ.ker = 31 := by
    rw [Subgroup.normalizerMonoidHom_ker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (C : Set Y))).toEquiv]
    rw [hcent_eq, hC]
  have hmul := Subgroup.card_ker_mul_card_range ρ
  rw [hker] at hmul
  have hcardN : Nat.card N = 31 * Nat.card ρ.range := hmul.symm
  have hdvd30 : Nat.card ρ.range ∣ 30 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    have hAut : Nat.card (MulAut ↥C) = 30 := by
      letI : IsCyclic ↥C := isCyclic_of_prime_card hC
      rw [IsCyclic.card_mulAut, hC]
      norm_num [Nat.totient_prime (by norm_num : Nat.Prime 31)]
    rwa [hAut] at h
  have hfac : (Nat.card Y).factorization 31 = 1 := by
    rw [hcardY, show (32537600 : ℕ) = 31 ^ 1 * 1049600 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 31), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 31 ∣ 1049600), add_zero]
  let S : Sylow 31 Y := Sylow.ofCard C (by rw [hC, hfac]; norm_num)
  have hS : (S : Subgroup Y) = C := Sylow.coe_ofCard C _
  have hnsyl : Nat.card (Sylow 31 Y) ≡ 1 [MOD 31] := card_sylow_modEq_one 31 Y
  have hidxN : Nat.card (Sylow 31 Y) = N.index := by
    rw [Sylow.card_eq_index_normalizer S]
    change (normalizer (S : Set Y)).index = N.index
    rw [show normalizer (S : Set Y) = N by rw [← Sylow.coe_coe, hS]]
  have hmod : N.index ≡ 1 [MOD 31] := by
    rw [← hidxN]; exact hnsyl
  have hNidx : Nat.card N * N.index = Nat.card Y := Subgroup.card_mul_index N
  have hdix : Nat.card ρ.range * N.index = 1049600 := by
    have h : 31 * (Nat.card ρ.range * N.index) = 31 * 1049600 := by
      calc 31 * (Nat.card ρ.range * N.index) = (31 * Nat.card ρ.range) * N.index := by ring
        _ = Nat.card N * N.index := by rw [← hcardN]
        _ = Nat.card Y := hNidx
        _ = 32537600 := hcardY
        _ = 31 * 1049600 := by norm_num
    exact Nat.mul_left_cancel (by norm_num) h
  have hd2 : Nat.card ρ.range = 2 := by
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    have hle : Nat.card ρ.range ≤ 30 := Nat.le_of_dvd (by norm_num) hdvd30
    have hdmod : Nat.card ρ.range ≡ 2 [MOD 31] := by
      have h1 : Nat.card ρ.range * N.index ≡ Nat.card ρ.range * 1 [MOD 31] :=
        hmod.mul_left _
      rw [hdix, mul_one] at h1
      have h2 : (1049600 : ℕ) ≡ 2 [MOD 31] := by norm_num [Nat.ModEq]
      exact h1.symm.trans h2
    have hdlt : Nat.card ρ.range < 31 := by omega
    have h : Nat.card ρ.range % 31 = 2 % 31 := hdmod
    rw [Nat.mod_eq_of_lt hdlt, show 2 % 31 = 2 by norm_num] at h
    exact h
  have hcardN62 : Nat.card N = 62 := by
    rw [hcardN, hd2]
  refine ⟨by simpa [N] using hcardN62, ?_⟩
  intro g hgN hgC c hc
  let s : MulAut ↥C := (Subgroup.normalizerMonoidHom C) ⟨g, hgN⟩
  have hCsub : Nat.card (C.subgroupOf N) = 31 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show C ≤ N from Subgroup.le_normalizer)).toEquiv, hC]
  have hidx2 : (C.subgroupOf N).index = 2 := by
    have h := Subgroup.card_mul_index (C.subgroupOf N)
    rw [hCsub, hcardN62] at h
    omega
  have hg2C : g ^ 2 ∈ C := by
    have h := Subgroup.sq_mem_of_index_two hidx2 (⟨g, hgN⟩ : ↥N)
    simpa [Subgroup.mem_subgroupOf] using h
  have hss : ∀ v : ↥C, s (s v) = v := by
    intro v
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hg2comm : g ^ 2 * (v : Y) = (v : Y) * g ^ 2 :=
      hCcomm (g ^ 2) hg2C (v : Y) v.2
    rw [show g * (g * (v : Y) * g⁻¹) * g⁻¹ = (g ^ 2) * (v : Y) * (g ^ 2)⁻¹ by
      rw [pow_two]; group]
    rw [hg2comm]; group
  have hx_top : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hx, hC]
  have hsu : s x ∈ Subgroup.zpowers x := by
    rw [hx_top]; exact Subgroup.mem_top _
  have hcases := CFSG.Quasithin.SteinbergCC.forall_zpowers_apply_eq_or_inv
    (p := 31) (by norm_num) hx s hss hsu
  have hnotfix : ¬ (∀ v ∈ Subgroup.zpowers x, s v = v) := by
    intro hfix
    apply hgC
    have hcent : g ∈ Subgroup.centralizer (C : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hfixd : s ⟨d, hd⟩ = ⟨d, hd⟩ := by
        apply hfix
        rw [hx_top]; exact Subgroup.mem_top _
      have hval := congrArg Subtype.val hfixd
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hval
      have hcomm : g * d = d * g := by
        calc g * d = (g * d * g⁻¹) * g := by group
          _ = d * g := by rw [hval]
      exact hcomm.symm
    exact hcent_eq ▸ hcent
  have hinv : ∀ v ∈ Subgroup.zpowers x, s v = v⁻¹ := hcases.resolve_left hnotfix
  have hc' : s ⟨c, hc⟩ = (⟨c, hc⟩ : ↥C)⁻¹ :=
    hinv ⟨c, hc⟩ (by rw [hx_top]; exact Subgroup.mem_top _)
  have hval := congrArg Subtype.val hc'
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hval
  simpa using hval

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
