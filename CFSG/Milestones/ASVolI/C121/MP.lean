module

public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Milestones.ASVolI.C1
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups Pointwise

theorem burnsideC121_not_le_normalizer_sylow {Γ : Type*} [Group Γ] [Finite Γ] {L S : Subgroup Γ}
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* SL(2, F)) (hS : IsSylowTwoOf S L) :
    ¬ L ≤ Subgroup.normalizer (S : Set Γ) := by
  intro hN
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : CharP F 2 := charP_of_card_eq_prime_pow hF'
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsimple : IsSimpleGroup SL(2, F) := CFSG.Quasithin.C126.Nat.isSimpleGroup_sl2 h4
  have hsL : IsSimpleGroup ↥L := e.isSimpleGroup
  have hSL : S ≤ L := hS.1
  have hnorm : (S.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSL).2 hN
  have hcS : Nat.card S = 2 ^ n :=
    CFSG.Quasithin.C126.Nat.card_sylow_of_equiv_sl2 (by omega) hF e hS
  have hcS' : Nat.card (S.subgroupOf L) = 2 ^ n := by
    rw [← hcS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  have hcL : Nat.card ↥L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.CGT.Timmesfeld75.card_sl2, hF]
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf L) with h | h
  · rw [h, Subgroup.card_bot] at hcS'
    have : 1 < 2 ^ n := by omega
    omega
  · rw [h, Subgroup.card_top, hcL] at hcS'
    have h1 : (2 ^ n) ^ 2 - 1 = 1 := by
      have hpos : 0 < 2 ^ n := by positivity
      have := Nat.eq_of_mul_eq_mul_left hpos (hcS'.trans (mul_one _).symm)
      exact this
    have h2 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega

variable {G : Type} [Group G] [Finite G]

theorem burnsideC121_minParabolic_of_sl2 {Y T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hT2 : IsPGroup 2 T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Y) Y) (hC : Y ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥(autI hV Y) ≃* SL(2, F)) (hnorm : ¬ Y ≤ Subgroup.normalizer (T : Set G)) :
    ∃ M : Subgroup G, MinParabolic (Y ⊔ T) T M := by
  classical
  have hsylP : IsSylowTwoOf T (Y ⊔ T) :=
    CFSG.Quasithin.C124.L2.isSylowTwoOf_sup_of_normalizing hTY hT2 hsyl
  have hDs : IsSylowTwoOf (autI hV (T ⊓ Y)) (autI hV Y) := B2F.isSylowTwoOf_autI hV hYN hsyl
  have hTT : T ≤ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTY ht⟩
  have hTn : autI hV T ≤ Subgroup.normalizer (autI hV (T ⊓ Y) : Set (MulAut (IntMod V hV))) :=
    CFSG.Quasithin.C124.L2.autI_le_normalizer_of_le_normalizer hV hTT
  set B : Subgroup (MulAut (IntMod V hV)) :=
    Subgroup.normalizer (autI hV (T ⊓ Y) : Set (MulAut (IntMod V hV))) with hB
  set M₀ : Subgroup G := preI hV Y hYN B with hM₀
  have hM₀Y : M₀ ≤ Y := preI_le hV
  have hTYM₀ : T ⊓ Y ≤ M₀ := fun d hd =>
    (mem_preI hV).2 ⟨hd.2, Subgroup.le_normalizer (convI_mem_autI hV hd (hYN hd.2))⟩
  have hTM₀ : T ≤ Subgroup.normalizer (M₀ : Set G) := by
    have key : ∀ t ∈ T, ∀ y ∈ M₀, t * y * t⁻¹ ∈ M₀ := by
      intro t ht y hy
      obtain ⟨hyY, hyB⟩ := (mem_preI hV).1 hy
      have hty : t * y * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hTY ht) y).1 hyY
      refine (mem_preI hV).2 ⟨hty, ?_⟩
      have htB : convI hV ⟨t, hTN ht⟩ ∈ B := hTn (convI_mem_autI hV ht (hTN ht))
      have h1 : convHom hV Y hYN ⟨t * y * t⁻¹, hty⟩ =
          convI hV ⟨t, hTN ht⟩ * convHom hV Y hYN ⟨y, hyY⟩ * (convI hV ⟨t, hTN ht⟩)⁻¹ := by
        rw [convHom_apply, convHom_apply, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1]
      exact B.mul_mem (B.mul_mem htB hyB) (B.inv_mem htB)
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key t ht y, fun hy => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hy
    simpa [mul_assoc] using this
  set M : Subgroup G := M₀ ⊔ T with hM
  have hTM : T ≤ M := le_sup_right
  have hMP : M ≤ Y ⊔ T := sup_le (hM₀Y.trans le_sup_left) le_sup_right
  have hmul : ((M₀ ⊔ T : Subgroup G) : Set G) = (M₀ : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M₀ T hTM₀
  have hmax : ∀ K : Subgroup G, T ≤ K → K < Y ⊔ T → K ≤ M := by
    intro K hTK hKP
    have hdec : ∀ k ∈ K, ∃ y ∈ K ⊓ Y, ∃ t ∈ T, k = y * t := by
      intro k hk
      have hk' : k ∈ ((Y ⊔ T : Subgroup G) : Set G) := hKP.le hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY] at hk'
      obtain ⟨y, hy, t, ht, rfl⟩ := hk'
      refine ⟨y, ⟨?_, hy⟩, t, ht, rfl⟩
      have := K.mul_mem hk (K.inv_mem (hTK ht))
      simpa using this
    have hKYle : autI hV (K ⊓ Y) ≤ autI hV Y := autI_mono hV inf_le_right
    have hDK : autI hV (T ⊓ Y) ≤ autI hV (K ⊓ Y) := autI_mono hV (inf_le_inf_right Y hTK)
    rcases CFSG.Quasithin.C126.Nat.sylow_dichotomy_of_equiv_sl2 (n := n) (by omega) hF e hDs
      hKYle hDK with h | h
    · exfalso
      have hYK : Y ≤ K := by
        intro y hy
        have hmem : convI hV ⟨y, hYN hy⟩ ∈ autI hV (K ⊓ Y) := by
          rw [h]
          exact convI_mem_autI hV hy (hYN hy)
        obtain ⟨k, hkK, hk⟩ := (mem_autI hV).1 hmem
        have h1 : convI hV (⟨y, hYN hy⟩ * k⁻¹) = 1 := by
          rw [map_mul, map_inv, ← hk, mul_inv_cancel]
        have h2 : y * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          (convI_eq_one_iff hV _).1 h1
        have h3 : y * (k : G)⁻¹ ∈ T := hC ⟨Y.mul_mem hy (Y.inv_mem hkK.2), h2⟩
        have h4 : y = (y * (k : G)⁻¹) * k := by group
        rw [h4]
        exact K.mul_mem (hTK h3) hkK.1
      exact absurd hKP (not_lt_of_ge (sup_le hYK hTK))
    · intro k hk
      obtain ⟨y, hy, t, ht, rfl⟩ := hdec k hk
      have hyM₀ : y ∈ M₀ := (mem_preI hV).2 ⟨hy.2, h (convI_mem_autI hV hy (hYN hy.2))⟩
      exact Subgroup.mul_mem_sup hyM₀ ht
  have hMP' : M < Y ⊔ T := by
    refine lt_of_le_of_ne hMP fun hEq => ?_
    have hYM : Y ≤ M := by
      rw [hEq]
      exact le_sup_left
    have hYM₀ : Y ≤ M₀ := by
      intro y hy
      have hy' : y ∈ ((M₀ ⊔ T : Subgroup G) : Set G) := hYM hy
      rw [hmul] at hy'
      obtain ⟨m, hm, t, ht, rfl⟩ := hy'
      have htY : t ∈ T ⊓ Y := ⟨ht, by simpa using Y.mul_mem (Y.inv_mem (hM₀Y hm)) hy⟩
      exact M₀.mul_mem hm (hTYM₀ htY)
    apply burnsideC121_not_le_normalizer_sylow hn hF e hDs
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact ((mem_preI hV).1 (hYM₀ hg)).2
  have hTn' : ¬ Y ⊔ T ≤ Subgroup.normalizer (T : Set G) := fun h => hnorm (le_sup_left.trans h)
  exact ⟨M, CFSG.QuasithinUnique.Setup.minParabolic_of_uniqueMax hsylP hTn' hTM hMP' hmax⟩

theorem burnsideC121_minParabolic_of_three {Y T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hsyl : IsSylowTwoOf (T ⊓ Y) Y)
    (h3 : (T ⊓ Y).relIndex Y = 3) (hnorm : ¬ Y ≤ Subgroup.normalizer (T : Set G)) :
    MinParabolic (Y ⊔ T) T T := by
  have hsylP : IsSylowTwoOf T (Y ⊔ T) :=
    CFSG.Quasithin.C124.L2.isSylowTwoOf_sup_of_normalizing hTY hT2 hsyl
  have hTn' : ¬ Y ⊔ T ≤ Subgroup.normalizer (T : Set G) := fun h => hnorm (le_sup_left.trans h)
  have hYT : ¬ Y ≤ T := fun h => hnorm (h.trans Subgroup.le_normalizer)
  have hlt : T < Y ⊔ T := lt_of_le_of_ne le_sup_right fun h => hYT (h ▸ le_sup_left)
  refine CFSG.QuasithinUnique.Setup.minParabolic_of_uniqueMax hsylP hTn' le_rfl hlt
    fun K hTK hKP => ?_
  have hle : T ⊓ Y ≤ K ⊓ Y := inf_le_inf_right Y hTK
  have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ Y) (K ⊓ Y) Y hle inf_le_right
  rw [h3] at hmul
  have hdvd : (K ⊓ Y).relIndex Y ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exfalso
    have hYK : Y ≤ K := fun y hy => (Subgroup.relIndex_eq_one.1 h1 hy).1
    exact absurd hKP (not_lt_of_ge (sup_le hYK hTK))
  · rw [h1] at hmul
    have h2 : (T ⊓ Y).relIndex (K ⊓ Y) = 1 := by omega
    have hKT : K ⊓ Y ≤ T ⊓ Y := Subgroup.relIndex_eq_one.1 h2
    intro k hk
    have hk' : k ∈ ((Y ⊔ T : Subgroup G) : Set G) := hKP.le hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY] at hk'
    obtain ⟨y, hy, t, ht, rfl⟩ := hk'
    have hyK : y ∈ K := by
      have := K.mul_mem hk (K.inv_mem (hTK ht))
      simpa using this
    exact T.mul_mem (hKT ⟨hyK, hy⟩).1 ht

end CFSG.ASVolI
