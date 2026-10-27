module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CL5
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCaseA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CQ
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanInv
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CL4
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5Sz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFixed
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_isCyclic_of_odd_le_normalizer
    {S : Type} [Group S] [Finite S] {m : ℕ} (hSz : IsSz S m) (U : Sylow 2 S)
    {D : Subgroup S} (hD : D ≤ Subgroup.normalizer ((U : Subgroup S) : Set S))
    (hodd : Odd (Nat.card D)) : IsCyclic ↥D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup S := Subgroup.normalizer ((U : Subgroup S) : Set S)
  let U' : Subgroup ↥N := (U : Subgroup S).subgroupOf N
  haveI hU'norm : U'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  haveI hcyc : IsCyclic (↥N ⧸ U') :=
    uc22r3e5c_isCyclic_normalizer_quotient
      (CFSG.LocalAnalysis.WeakClosure81.isSz_iff_isSz.mp hSz) U
  have hDinf : D ⊓ (U : Subgroup S) = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨a, ha⟩ := (U : Sylow 2 S).isPGroup'.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_right a hodd.coprime_two_right
  let f : ↥D →* ↥N ⧸ U' := (QuotientGroup.mk' U').comp (Subgroup.inclusion hD)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hxker
    have hx1 : f ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp hxker
    have hxU' : (Subgroup.inclusion hD ⟨x, hx⟩ : ↥N) ∈ U' :=
      (QuotientGroup.eq_one_iff _).mp hx1
    have hxU : x ∈ (U : Subgroup S) := Subgroup.mem_subgroupOf.mp hxU'
    have hxbot : x ∈ D ⊓ (U : Subgroup S) := ⟨hx, hxU⟩
    rw [hDinf] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  exact isCyclic_of_injective f hf

theorem uc22r3e5c_stable_pairs {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hset : conjSetOf D.M L = {L, K})
    {C : Subgroup G} (hCX : C ≤ conjClosure D.M L) {b : G}
    (hbC : b ∈ normalizer (C : Set G)) (hbX : b ∈ normalizer (conjClosure D.M L : Set G))
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G))
    (hbT : b ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G))
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage (conjClosure D.M L) C).map e.toMonoidHom = DL.prod DK)
    (hDLle : DL ≤ normalizer (barImage L (D.T ⊓ L) : Set (Bar2 L)))
    (hDKle : DK ≤ normalizer (barImage K (D.T ⊓ K) : Set (Bar2 K))) :
    ∃ UL : Sylow 2 (Bar2 L), ∃ UK : Sylow 2 (Bar2 K),
      (UL : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) ∧
      (UK : Subgroup (Bar2 K)) = barImage K (D.T ⊓ K) ∧
      (UL : Subgroup (Bar2 L)).map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = UL ∧
      (UK : Subgroup (Bar2 K)).map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = UK ∧
      DL ≤ normalizer (UL : Set (Bar2 L)) ∧
      DK ≤ normalizer (UK : Set (Bar2 K)) ∧
      DL.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = DL ∧
      DK.map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = DK := by
  have hLmem : L ∈ conjSetOf D.M L :=
    ⟨1, D.M.one_mem, by ext z; simp [MulAut.conj_apply]⟩
  have hLX : L ≤ conjClosure D.M L :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf D.M L) => K) L hLmem le_rfl
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hKX : K ≤ conjClosure D.M L :=
    le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf D.M L) => K) K hKmem le_rfl
  obtain ⟨UL, hULcoe, hUL⟩ := uc22r3e5c_exists_sylow_rhoL_stable hL hbL hbT
  have hXeq : conjClosure D.M K = conjClosure D.M L :=
    uc22r3e5c_conjClosure_eq_of_mem hKmem
  have hbTK : b ∈ normalizer ((D.T ⊓ conjClosure D.M K : Subgroup G) : Set G) := by
    rw [hXeq]; exact hbT
  obtain ⟨UK, hUKcoe, hUK⟩ := uc22r3e5c_exists_sylow_rhoL_stable hKC hbK hbTK
  have hCb : (barImage (conjClosure D.M L) C).map
      (UC6S846.rhoL (conjClosure D.M L) ⟨b, hbX⟩).toMonoidHom =
      barImage (conjClosure D.M L) C :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_maps_barImage hCX hbC hbX
  obtain ⟨hDLα, hDKα⟩ :=
    uc22r3e5c_link_map_rhoL_eq hLX hKX e heL heK hCe hbX hbL hbK hCb
  refine ⟨UL, UK, hULcoe, hUKcoe, hUL, hUK, ?_, ?_, hDLα, hDKα⟩
  · show DL ≤ normalizer ((UL : Subgroup (Bar2 L)) : Set (Bar2 L))
    rw [hULcoe]
    exact hDLle
  · show DK ≤ normalizer ((UK : Subgroup (Bar2 K)) : Set (Bar2 K))
    rw [hUKcoe]
    exact hDKle

theorem uc22r3e5c_exponent_pair {L K : Subgroup G} {b g : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G)) (hb3 : b ^ 3 = 1)
    (hgb : g * b * g⁻¹ = b⁻¹) (hLg : L.map (MulAut.conj g).toMonoidHom = K)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) (hSzK : IsSz (Bar2 K) n) (h3 : 3 ∣ n)
    (hni : UC6S846.rhoL L ⟨b, hbL⟩ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))
    (UL : Sylow 2 (Bar2 L)) {DL : Subgroup (Bar2 L)}
    (hDL : DL ≤ normalizer ((UL : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (hDLc : Nat.card DL = 2 ^ n - 1)
    (hUL : (UL : Subgroup (Bar2 L)).map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = UL)
    (hDLα : DL.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = DL)
    (UK : Sylow 2 (Bar2 K)) {DK : Subgroup (Bar2 K)}
    (hDK : DK ≤ normalizer ((UK : Subgroup (Bar2 K)) : Set (Bar2 K)))
    (hDKc : Nat.card DK = 2 ^ n - 1)
    (hUK : (UK : Subgroup (Bar2 K)).map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = UK)
    (hDKα : DK.map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = DK) :
    ∃ j ∈ ({1, 2} : Finset ℕ),
      (∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ ((2 ^ (n / 3)) ^ j)) ∧
      (∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d =
        d ^ ((2 ^ (n / 3)) ^ j * (2 ^ (n / 3)) ^ j)) := by
  obtain ⟨j, hj, hαL⟩ := uc22r3e5c_torusExp_of_order_three hSz h3
    (UC6S846.rhoL L ⟨b, hbL⟩) (uc22r3e5c_rhoL_pow_three hbL hb3) hni UL DL hDL hDLc hUL hDLα
  exact ⟨j, hj, hαL,
    uc22r3e5c_torusExp_swap hbL hbK hb3 hgb hLg hSzK UL hDL hDLc hUL hDLα
      UK hDK hDKc hUK hDKα hαL⟩

private theorem uc22r3e5c_isCyclic_of_card_two_pow_sub_one
    {S : Type} [Group S] [Finite S]
    {n : ℕ} (hSz : IsSz S n) (U : Sylow 2 S) {D : Subgroup S}
    (hD : D ≤ Subgroup.normalizer ((U : Subgroup S) : Set S))
    (hDc : Nat.card D = 2 ^ n - 1) (hn : 2 < n) : IsCyclic ↥D :=
  uc22r3e5c_isCyclic_of_odd_le_normalizer hSz U hD (by
    rw [hDc]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Even.pow_of_ne_zero (by norm_num) (by omega : n ≠ 0)) odd_one)

theorem uc22r3e5c_false_of_inverter
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (hSg : UC6S846.SigmaStd D) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (he : CFSG.Open.evenRank G = 3)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) (h3 : 3 ∣ n) {b : G} (hb : b ∈ c.B0)
    (hbo : orderOf b = 3)
    (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M)
    (hB0 : ∀ a ∈ c.B0, a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G))
    {g : G} (hgM : g ∈ D.M) (hgb : g * b * g⁻¹ = b⁻¹)
    (hgL : g ∉ normalizer (L : Set G)) : False := by
  obtain ⟨C, hCX, hCodd, hCcomm, hperm, hCTs, hbC, hbC₁, hbC₂, hCmul, K, hKne, hKC, hset,
    hSzK, e, DL, DK, heL, heK, hCe, hDLle, hDKle, hDLcard, hDKcard⟩ :=
    uc22r3e5c_exists_cartan_inv h5 h1930 c hH₁ hH₂ hL0 hfX hL hc2 hn hSz hb hbo
  have hLg : L.map (MulAut.conj g).toMonoidHom = K :=
    uc22r3e5_map_conj_eq_second hset hgM hgL
  have hKmem : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hcK : (conjSetOf D.M K).ncard = 2 := by
    rw [uc22p2214_conjSetOf_eq hKmem]; exact hc2
  have hbK : b ∈ normalizer (K : Set G) :=
    uc22p2214_mem_normalizer_of_odd hcK (c.hBM hb) (hbo ▸ ⟨1, by norm_num⟩)
  have hbX : b ∈ normalizer (conjClosure D.M L : Set G) :=
    uc22r3e5c_B0_le_normalizer_conjClosure h5 h1930 c hL hc2 hb
  obtain ⟨UL, UK, hULcoe, hUKcoe, hUL, hUK, hDLU, hDKU, hDLα, hDKα⟩ :=
    uc22r3e5c_stable_pairs hL hKC hset hCX hbC hbX hbL hbK (hB0 b hb) heL heK hCe hDLle hDKle
  have hni : UC6S846.rhoL L ⟨b, hbL⟩ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) :=
    uc22r3e5c_rhoL_not_inner hL hbL hninn
  obtain ⟨j, hj, hαL, hαK⟩ :=
    uc22r3e5c_exponent_pair hbL hbK (hbo ▸ pow_orderOf_eq_one b) hgb hLg hSz hSzK h3 hni
      UL hDLU hDLcard hUL hDLα UK hDKU hDKcard hUK hDKα
  obtain ⟨r, hr, hr2, hrn, hre⟩ :=
    uc22r3e5c_exists_prime_pow_ne (uc22r3e5c_odd_of_isSz hSz) h3
  have hDLcyc : IsCyclic ↥DL :=
    uc22r3e5c_isCyclic_of_card_two_pow_sub_one hSz UL hDLU hDLcard hn
  have hDKcyc : IsCyclic ↥DK :=
    uc22r3e5c_isCyclic_of_card_two_pow_sub_one hSzK UK hDKU hDKcard hn
  exact uc22r3e5c_false_of_caseA hSg h15 hU2 h211 h1930 c he hH₁ hH₂ hL hKC hc2 hKne hset
    hSz hSzK hCX hCodd hCcomm hperm hCTs hbC₁ hbC₂ hCmul e heL heK hCe hDLcyc hDKcyc hDLcard
    hbL hbK hr hr2 hrn (hre j hj) hαL hαK

theorem uc22r3e5c_false_of_sz_core
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (hSg : UC6S846.SigmaStd D) (h72 : F07.R72 D) (hK72 : KStrongEmbedded72) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (he : CFSG.Open.evenRank G = 3) (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) (h3 : 3 ∣ n) {b : G} (hb : b ∈ c.B0)
    (hbo : orderOf b = 3)
    (hcent : ∀ Y ∈ conjSetOf D.M L, ¬ ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    False := by
  have hB0 : ∀ a ∈ c.B0,
      a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G) :=
    uc22r3e5c_normalizes_inf h5 h1930 c hL hc2 hn hSz
  by_cases h5n : 5 ∣ n
  · have hn3' : n ≠ 3 := by
      rintro rfl
      norm_num at h5n
    have hbL : b ∈ normalizer (L : Set G) :=
      uc22p2214_mem_normalizer_of_odd hc2 (c.hBM hb) (hbo ▸ ⟨1, by norm_num⟩)
    have hninn : ¬ ∃ y ∈ L, ∀ x ∈ L,
        b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M :=
      uc22r3e5_not_inner c hL hc2 hSz hb hbo hcent L
        ⟨1, D.M.one_mem, by ext x; simp [Subgroup.mem_map]⟩
    obtain ⟨g, hgM, hg⟩ :=
      uc22r3e5_invertedIn_of_ne_three hSg h15 hU2 h1930 c he hL hc2 hSz hn3' hb hbo hbL hninn
    have hgb : g * b * g⁻¹ = b⁻¹ := hg b (Subgroup.mem_zpowers b)
    have hgL : g ∉ normalizer (L : Set G) := fun h =>
      uc22r3e5_false_of_inv_normalizer c hL hc2 hSz hb hbo hcent h hgb
    exact uc22r3e5c_false_of_inverter h5 h15 hSg hU2 h211 h1930 c hH₁ hH₂ hL0 hfX he hL hc2 hn
      hSz h3 hb hbo hbL hninn hB0 hgM hgb hgL
  · exact uc22r3e5c_false_of_not_five_dvd h5 h15 hSg h72 hK72 h1930 c hn3 hpow hL hc2 hn hSz
      h5n hB0

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
