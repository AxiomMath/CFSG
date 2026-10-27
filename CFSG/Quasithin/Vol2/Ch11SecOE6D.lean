module

public import CFSG.Quasithin.Vol2.Ch11SecOE6C
public import CFSG.Quasithin.Vol2.Ch11SecOE6A
public import CFSG.Quasithin.Vol2.Ch11SecOE6B
public import CFSG.Quasithin.Vol2.Ch11SecQ9bJ1

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T H K Y : Subgroup G} (S : Setting G T H K Y)
include S

theorem exists_prime : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card Y ∧
    ∃ P : Subgroup G, IsSylowIn p P Y := by
  obtain ⟨p, hp, hp2, hpY, -, -⟩ := S.xi.exists_prime_sup_eq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPS, -⟩ := exists_isSylowIn_ge p (bot_le : ⊥ ≤ Y) IsPGroup.of_bot
  exact ⟨p, hp, S.five p hp hp2 hpY, hpY, P, hPS⟩

theorem bar_data {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpY : p ∣ Nat.card Y)
    {P : Subgroup G} (hSyl : IsSylowIn p P Y) :
    IsPGroup p (modO2Image H P) ∧ (∀ x ∈ modO2Image H P, x ^ p = 1) ∧
      p ^ 2 ≤ Nat.card (modO2Image H P) ∧ Nat.card (modO2Image H P) ≤ p ^ 3 ∧
      modO2Image H (T ⊓ Subgroup.normalizer (P : Set G)) ≤
        Subgroup.normalizer (modO2Image H P : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ∧
      ∀ U : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), ⁅modO2Image H P, modO2Image H P⁆ ≤ U →
        U ≤ modO2Image H P →
        modO2Image H (T ⊓ Subgroup.normalizer (P : Set G)) ≤
          Subgroup.normalizer (U : Set (↥H ⧸ CFSG.pCore 2 ↥H)) →
        U = ⁅modO2Image H P, modO2Image H P⁆ ∨ U = modO2Image H P := by
  have hexp := H13.NQCore.exp_bar_of_sylow (H := H) S.xi hp2 hpY hSyl
  have hPH : P ≤ H := hSyl.1.trans S.YH
  have hcard : Nat.card (modO2Image H P) = (pCoreOf 2 Y).relIndex Y :=
    (H13.NQCore.card_bar_of_sylow S.YH hp2 hSyl).trans (S.xi.card_sylow hp2 hpY hSyl)
  obtain ⟨k, hk2, hk3, hk⟩ := S.xi.relIndex_eq hp.out hp2 hpY
  refine ⟨fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩, hexp, ?_, ?_,
    P134.modO2Image_le_normalizer inf_le_right,
    H13.NQCore.irr_modO2Image' hPH (inf_le_left.trans S.TH) inf_le_right
      (H13.NQCore.irr_of_sylow S.sylowIn S.YH S.xi hp2 hpY hSyl)⟩
  · rw [hcard, hk]
    exact Nat.pow_le_pow_right hp.out.pos hk2
  · rw [hcard, hk]
    exact Nat.pow_le_pow_right hp.out.pos hk3

theorem le_normalizer_of_shape
    (hdesc : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      (∃ q : ℕ, q.Prime ∧ 11 ≤ q ∧ IsPSL 2 q 1 (↥K ⧸ CFSG.pCore 2 ↥K)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F))) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨p, hp, hp5, hpY, P, hSyl⟩ := S.exists_prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPp, hexp, hc2, -, hNP, hirr⟩ := S.bar_data hp2 hpY hSyl
  have := S.normal_bar
  obtain ⟨e⟩ := SecA.C11P9B.modO2Image_equiv S.KH S.normal_subgroupOf
  have hcyc : ∀ U : Subgroup (MulAut ↥(modO2Image H K)), IsPGroup p U → IsCyclic ↥U := by
    intro U hU
    refine isCyclic_of_mulEquiv e.symm (fun V hV => ?_) hU
    rcases hdesc with h | ⟨q, hq, hq11, h⟩ | ⟨F, _, _, hF, ⟨f⟩⟩
    · exact isCyclic_mulAut_psl34 h hp5 hV
    · exact isCyclic_mulAut_psl2 hq (by omega) h hp2 hV
    · exact isCyclic_mulAut_sl2_four hF f hp2 hV
  have hle := le_centralizer_of_isCyclic hPp hexp hc2 hNP hirr
    (hcyc _ (hPp.map (MulAut.conjNormal : (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut ↥(modO2Image H K))))
  exact S.le_normalizer_of_le_centralizer hp2 hpY hSyl hle

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE6
