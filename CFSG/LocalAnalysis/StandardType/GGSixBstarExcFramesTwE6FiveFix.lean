module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LieType.Chevalley.IntrinsicDiagramPermutation

public section

namespace CFSG.StandardType.ExcFrames

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance : NeZero (5 : ℕ) := ⟨by norm_num⟩

private abbrev wordE6FiveW : WeylGroup .E6 := (coxeterSystem .E6).wordProd TableBExc.wordE6Five

private theorem card_fix_torusWord_wordE6Five_le :
    Nat.card {x : Fin Tag.E6.rank → ZMod 5 //
      TableBExc.torusWord .E6 5 TableBExc.wordE6Five x = x} ≤ 5 ^ 2 := by
  have h := TableBExc.card_fix_torusWord_le (τ := .E6) (p := 5) TableBExc.wordE6Five
    (R := (![0, 2, 3, 4] : Fin 4 → Fin 6)) (C := (![0, 1, 2, 3] : Fin 4 → Fin 6))
    (by decide : Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 6))
    (N := ![![1, 2, 2, 2], ![2, 2, 2, 2], ![3, 3, 4, 4], ![0, 0, 0, 1]]) (by decide +kernel)
  exact h

private theorem card_fix_torusAct_wordE6Five_le :
    Nat.card {x : Fin Tag.E6.rank → ZMod 5 //
      TableBExc.torusAct .E6 5 wordE6FiveW x = x} ≤ 5 ^ 2 := by
  rw [NoOffExc.card_fix_torusAct_eq (cartan_symm_of_E (Or.inl rfl)) TableBExc.wordE6Five]
  exact card_fix_torusWord_wordE6Five_le

theorem card_fix_torusAct_eq_card_fix_zpowers {τ : Tag} {p : ℕ} [NeZero p]
    (w : WeylGroup τ) :
    Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p w x = x} =
    Nat.card {x : Fin τ.rank → ZMod p //
      ∀ a ∈ Subgroup.zpowers w, TableBExc.torusAct τ p a x = x} := by
  letI : MulAction (WeylGroup τ) (Fin τ.rank → ZMod p) :=
    MulAction.compHom _ (TableBExc.torusPerm τ p)
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · intro hx a ha
    exact smul_eq_self_of_mem_zpowers ha hx
  · exact fun hx => hx w (Subgroup.mem_zpowers w)

section Certificates


theorem card_fix_torusAct_E6_five {w : WeylGroup .E6} (hw : orderOf w = 5) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 5 // TableBExc.torusAct .E6 5 w x = x} ≤ 5 ^ 2 := by
  have hcardw : Nat.card (Subgroup.zpowers w) = 5 := by
    rw [Nat.card_zpowers, hw]
  have hPw : IsPGroup 5 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [hcardw]; norm_num)
  have hidxw : ¬ 5 ∣ (Subgroup.zpowers w).index := by
    rw [NoOffExc.index_eq_of_card hcardw NoOffExc.card_weyl_E6
      (show 5 * 10368 = 51840 by norm_num) (by norm_num)]
    norm_num
  have hcardw0 : Nat.card (Subgroup.zpowers wordE6FiveW) = 5 := by
    rw [Nat.card_zpowers, TableBExc.orderOf_wordE6Five]
  have hPw0 : IsPGroup 5 (Subgroup.zpowers wordE6FiveW) :=
    IsPGroup.of_card (n := 1) (by rw [hcardw0]; norm_num)
  have hidxw0 : ¬ 5 ∣ (Subgroup.zpowers wordE6FiveW).index := by
    rw [NoOffExc.index_eq_of_card hcardw0 NoOffExc.card_weyl_E6
      (show 5 * 10368 = 51840 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup .E6)
    (hPw.toSylow hidxw) (hPw0.toSylow hidxw0)
  have hg' : (Subgroup.zpowers w).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers wordE6FiveW := by
    have h1 := congrArg
      (fun P : Sylow 5 (WeylGroup .E6) => (P : Subgroup (WeylGroup .E6))) hg
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe,
      Subgroup.pointwise_smul_def] at h1
    exact h1
  rw [card_fix_torusAct_eq_card_fix_zpowers w,
    ← NoOffExc.card_fix_map_conj (Subgroup.zpowers w) g, hg']
  exact (NoOffExc.card_fixAll_le (Subgroup.mem_zpowers wordE6FiveW)).trans
    card_fix_torusAct_wordE6Five_le

end Certificates

end CFSG.StandardType.ExcFrames
