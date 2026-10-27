module

public import CFSG.Quasithin.Background.C126NatDSimple
public import CFSG.Quasithin.Background.C126A5Core1
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.L2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_sup_of_normalizing {Y T : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hT2 : IsPGroup 2 T)
    (hsyl : IsSylowTwoOf (T ⊓ Y) Y) : IsSylowTwoOf T (Y ⊔ T) := by
  refine ⟨le_sup_right, hT2, ?_⟩
  have h1 := Subgroup.relIndex_mul_card T (Y ⊔ T)
  rw [inf_eq_left.2 (le_sup_right : T ≤ Y ⊔ T)] at h1
  have h2 := card_sup_mul_card_inf_of_le_normalizer hTY
  have h3 := Subgroup.relIndex_mul_card (Y ⊓ T) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ T ≤ Y)] at h3
  have hpos : 0 < Nat.card ↥(Y ⊓ T) := Nat.card_pos
  have hposT : 0 < Nat.card T := Nat.card_pos
  have key : T.relIndex (Y ⊔ T) = (Y ⊓ T).relIndex Y := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposT hpos)
    calc T.relIndex (Y ⊔ T) * (Nat.card T * Nat.card ↥(Y ⊓ T))
        = Nat.card ↥(Y ⊔ T) * Nat.card ↥(Y ⊓ T) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card T := h2
      _ = (Y ⊓ T).relIndex Y * (Nat.card T * Nat.card ↥(Y ⊓ T)) := by rw [← h3]; ring
  have hidx : (T.subgroupOf (Y ⊔ T)).index = (Y ⊓ T).relIndex Y := key
  rw [hidx]
  have hs := hsyl.2.2
  rwa [inf_comm] at hs

theorem autI_le_normalizer_of_le_normalizer {H K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    autI hV H ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hn
  refine (mem_autI hV).2 ⟨g * k * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.1 (hK hgH) (k : G)).1 hkK
  simpa using this

section Dickson

variable {Y V : Subgroup G} {F : Type} [Field F] [Finite F]

theorem card_eq_four_of_sylow (hV : IsElemAbelian 2 V) (hF : Nat.card F = 4)
    {S : Subgroup (MulAut (IntMod V hV))} (e : ↥(autI hV Y) ≃* SL(2, F))
    (hS : IsSylowTwoOf S (autI hV Y)) : Nat.card S = 4 := by
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  rw [C126.Nat.card_sylow_of_equiv_sl2 (by norm_num) hF4 e hS]
  norm_num

omit [Finite G] in
theorem card_sl2_four (hF : Nat.card F = 4) : Nat.card SL(2, F) = 60 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  norm_num

theorem not_le_normalizer_sylow (hV : IsElemAbelian 2 V) (hF : Nat.card F = 4)
    {S : Subgroup (MulAut (IntMod V hV))} (e : ↥(autI hV Y) ≃* SL(2, F))
    (hS : IsSylowTwoOf S (autI hV Y)) :
    ¬ autI hV Y ≤ Subgroup.normalizer (S : Set (MulAut (IntMod V hV))) := by
  intro hN
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hF4
  have hsimple : IsSimpleGroup SL(2, F) := C126.Nat.isSimpleGroup_sl2 (by omega)
  have hsY : IsSimpleGroup ↥(autI hV Y) := e.isSimpleGroup
  have hSY : S ≤ autI hV Y := hS.1
  have hnorm : (S.subgroupOf (autI hV Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSY).2 hN
  have hc4 := card_eq_four_of_sylow hV hF e hS
  have hcS : Nat.card (S.subgroupOf (autI hV Y)) = 4 := by
    rw [← hc4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv
  have h60 : Nat.card ↥(autI hV Y) = 60 := by
    rw [Nat.card_congr e.toEquiv, card_sl2_four hF]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf (autI hV Y)) with h | h
  · rw [h, Subgroup.card_bot] at hcS
    omega
  · rw [h, Subgroup.card_top, h60] at hcS
    omega

theorem minParabolic_of_sl2 {Y T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hT2 : IsPGroup 2 T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Y) Y) (hC : Y ⊓ Subgroup.centralizer (V : Set G) ≤ T)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (e : ↥(autI hV Y) ≃* SL(2, F))
    (hnorm : ¬ Y ≤ Subgroup.normalizer (T : Set G)) :
    ∃ M : Subgroup G, MinParabolic (Y ⊔ T) T M := by
  classical
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hsylP : IsSylowTwoOf T (Y ⊔ T) := isSylowTwoOf_sup_of_normalizing hTY hT2 hsyl
  have hDs : IsSylowTwoOf (autI hV (T ⊓ Y)) (autI hV Y) := B2F.isSylowTwoOf_autI hV hYN hsyl
  have hTT : T ≤ Subgroup.normalizer ((T ⊓ Y : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTY ht⟩
  have hTn : autI hV T ≤ Subgroup.normalizer (autI hV (T ⊓ Y) : Set (MulAut (IntMod V hV))) :=
    autI_le_normalizer_of_le_normalizer hV hTT
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
    rcases C126.Nat.sylow_dichotomy_of_equiv_sl2 (n := 2) (by norm_num) hF4 e hDs hKYle hDK
      with h | h
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
    apply not_le_normalizer_sylow hV hF e hDs
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    exact ((mem_preI hV).1 (hYM₀ hg)).2
  have hTn' : ¬ Y ⊔ T ≤ Subgroup.normalizer (T : Set G) := fun h => hnorm (le_sup_left.trans h)
  exact ⟨M, CFSG.QuasithinUnique.Setup.minParabolic_of_uniqueMax hsylP hTn' hTM hMP' hmax⟩

end Dickson

end CFSG.Quasithin.C124.L2
