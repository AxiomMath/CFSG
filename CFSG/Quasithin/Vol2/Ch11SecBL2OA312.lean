module

public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem lemma_1_2_4_refined {G : Type} [Group G] [Finite G] {H S B L : Subgroup G}
    (h312 : A312Refined (↥H ⧸ CFSG.pCore 2 ↥H)) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) (hL : L ∈ cComp H) (hBL : B ≤ L) :
    modO2Image H B = modO2Image H L ∨
      (CFSG.IsQuasisimple ↥(modO2Image H L) ∧ A312Case (modO2Image H B) (modO2Image H L)) ∨
      (¬ CFSG.IsQuasisimple ↥(modO2Image H L) ∧
        A312Nonquasi (modO2Image H B) (modO2Image H L)) := by
  have hSbar := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  obtain ⟨L', hL', hBL', huniq, hlist⟩ := h312 _ hSbar _ (modO2Image_mem_lFamily hS hBH hB)
  have hLbar : modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_mem_cComp hL
  have hBLbar : modO2Image H B ≤ modO2Image H L := Subgroup.map_mono (fun x hx => hBL hx)
  have heq : modO2Image H L = L' := huniq _ hLbar hBLbar
  rw [heq]
  exact hlist

theorem pCore_two_quotient_eq_bot (X : Type) [Group X] :
    CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  set N := CFSG.pCore 2 X with hN
  set Q := CFSG.pCore 2 (X ⧸ N) with hQ
  have hNn : N.Normal := CFSG.pCore_normal
  have hQnorm : Q.Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hpre : (Q.comap (QuotientGroup.mk' N)).Normal := hQnorm.comap _
  have hpre2 : IsPGroup 2 (Q.comap (QuotientGroup.mk' N)) := by
    intro x
    obtain ⟨a, ha⟩ := hQ2 ⟨QuotientGroup.mk' N (x : X), x.2⟩
    have ha' : QuotientGroup.mk' N ((x : X) ^ (2 ^ a)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have hmem : (x : X) ^ (2 ^ a) ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
    obtain ⟨b, hb⟩ := hN2 ⟨(x : X) ^ (2 ^ a), hmem⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((x : X) ^ (2 ^ a)) ^ (2 ^ b) = 1 := congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at hb'
    exact hb'
  have hle : Q.comap (QuotientGroup.mk' N) ≤ N := le_sSup ⟨hpre, hpre2⟩
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hle hq

theorem eq_bot_of_normal_of_isPGroup_quotient {X : Type} [Group X]
    {P : Subgroup (X ⧸ CFSG.pCore 2 X)} (hPn : P.Normal) (hP : IsPGroup 2 P) : P = ⊥ := by
  have hle : P ≤ CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) := le_sSup ⟨hPn, hP⟩
  rw [pCore_two_quotient_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem mulEquiv_modO2_of_surjective {K Y : Type} [Group K] [Group Y] (ρ : K →* Y)
    (hρ : Function.Surjective ρ) (hker : IsPGroup 2 ρ.ker)
    (hY : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥) :
    Nonempty ((K ⧸ CFSG.pCore 2 K) ≃* Y) := by
  have hk1 : ρ.ker ≤ CFSG.pCore 2 K := le_sSup ⟨inferInstance, hker⟩
  have hk2 : CFSG.pCore 2 K ≤ ρ.ker := by
    have hn : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
    have h1 := hY ((CFSG.pCore 2 K).map ρ) (hn.map ρ hρ) (CFSG.pCore_isPGroup.map ρ)
    exact (Subgroup.map_eq_bot_iff _).mp h1
  have heq : ρ.ker = CFSG.pCore 2 K := le_antisymm hk1 hk2
  have : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
