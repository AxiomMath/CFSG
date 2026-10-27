module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.JRgenInner
public import CFSG.Walter.Bender1970

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (IsJankoReeType10)

theorem exists_mul_ne_mul_of_isJankoReeType10 {X : Type} [Group X] (hJR : IsJankoReeType10 X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨-, J, L, F, _, _, -, -, hF3, -, -, -, ⟨eL⟩⟩ := hJR
  obtain ⟨a, b, hab⟩ := CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2
    (by rw [Nat.card_eq_fintype_card]; omega) eL
  exact ⟨a, b, fun h => hab (Subtype.ext h)⟩

theorem not_isTypeL2Even_of_isJankoReeType10 {X : Type} [Group X] [Finite X]
    (hJR : IsJankoReeType10 X) : ¬ CFSG.Walter.IsTypeL2Even X := by
  rintro ⟨f, hf, ⟨e⟩⟩
  obtain ⟨-, J, L, F, _, _, hJ, -, hF3, -, hLC, -, ⟨eL⟩⟩ := hJR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huo : orderOf (e J) = 2 := by rw [MulEquiv.orderOf_eq, hJ]
  obtain ⟨U, hU⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, huo, pow_one]) : IsPGroup 2 (zpowers (e J))).exists_le_sylow
  have huU : e J ∈ (U : Subgroup _) := hU (mem_zpowers (e J))
  have hu1 : e J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    omega
  have hCU := CFSG.Walter.psl2_even_centralizer_involution hf U huU hu1
  obtain ⟨hUel, -⟩ := CFSG.Walter.psl2_even_sylow_two hf U
  have hmem : ∀ x ∈ centralizer ({J} : Set X), e x ∈ (U : Subgroup _) := by
    intro x hx
    rw [← hCU, mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp hx
    have h2 := congrArg e h1
    rwa [map_mul, map_mul] at h2
  obtain ⟨a, b, hab⟩ := CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2
    (by rw [Nat.card_eq_fintype_card]; omega) eL
  apply hab
  apply Subtype.ext
  apply e.injective
  rw [coe_mul, coe_mul, map_mul, map_mul]
  exact congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨e a, hmem _ (hLC a.2)⟩
    ⟨e b, hmem _ (hLC b.2)⟩)

theorem involutionCentralizersGenerate_of_isJankoReeType10
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hJR : IsJankoReeType10 X) :
    CFSG.Walter.InvolutionCentralizersGenerate X := by
  have hab : CFSG.Walter.HasAbelianSylowTwo X := fun P =>
    ⟨⟨fun x y => Subtype.ext ((hJR.1 P).2 x x.2 y y.2).1⟩⟩
  have hSC := CFSG.Walter.simpleCaseHyp_of_benderHyp CFSG.Walter.benderHyp
  have hL := hSC X inferInstance (exists_mul_ne_mul_of_isJankoReeType10 hJR) hab fun H _ =>
    CFSG.Walter.isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup H)
  exact CFSG.Walter.involutionCentralizersGenerate_of_not_even hL
    (not_isTypeL2Even_of_isJankoReeType10 hJR)

theorem k_19_JRgen_holds :
    K_19_JRgen := by
  intro Y _ _ Kb hKn hKs hC _ hJR v₁ v₂ hv₁ hv₂ hne _
  haveI := hKs
  haveI := hKn
  have hT : ∀ T : Sylow 2 Kb, Nat.card (T : Subgroup Kb) = 8 ∧
      IsMulCommutative (T : Subgroup Kb) ∧ ∀ t ∈ (T : Subgroup Kb), t * t = 1 := fun T =>
    ⟨(hJR.1 T).1, ⟨⟨fun x y => Subtype.ext ((hJR.1 T).2 x x.2 y y.2).1⟩⟩,
      fun t ht => by rw [← pow_two]; exact ((hJR.1 T).2 t ht t ht).2⟩
  have hmem : ∀ v : Y, orderOf v = 2 → v ∈ Kb := fun v hv =>
    mem_of_mul_self_eq_one_of_sylow_eight hC (exists_mul_ne_mul_of_isJankoReeType10 hJR) hT
      (by rw [← pow_two, ← hv, pow_orderOf_eq_one])
  have hgen := involutionCentralizersGenerate_of_isJankoReeType10 hJR
    ⟨v₁, hmem v₁ hv₁⟩ ⟨v₂, hmem v₂ hv₂⟩ (by rw [Subgroup.orderOf_mk, hv₁])
    (by rw [Subgroup.orderOf_mk, hv₂]) (fun h => hne (congrArg Subtype.val h))
  have hle : ∀ w : Kb, (centralizer ({w} : Set Kb)).map Kb.subtype ≤
      Kb ⊓ centralizer ({(w : Y)} : Set Y) := by
    rintro w _ ⟨k, hk, rfl⟩
    have hk' : k * w = w * k := mem_centralizer_singleton_iff.mp hk
    exact mem_inf.mpr ⟨k.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hk')⟩
  calc Kb = (⊤ : Subgroup Kb).map Kb.subtype := by
        rw [← MonoidHom.range_eq_map, range_subtype]
    _ = (centralizer ({⟨v₁, hmem v₁ hv₁⟩} : Set Kb) ⊔
          centralizer ({⟨v₂, hmem v₂ hv₂⟩} : Set Kb)).map Kb.subtype := by rw [hgen]
    _ = (centralizer ({⟨v₁, hmem v₁ hv₁⟩} : Set Kb)).map Kb.subtype ⊔
          (centralizer ({⟨v₂, hmem v₂ hv₂⟩} : Set Kb)).map Kb.subtype := map_sup _ _ _
    _ ≤ _ := sup_le_sup (hle _) (hle _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
