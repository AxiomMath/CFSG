module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem exists_mem_irrSet_le [Finite W] {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    {S : Subgroup W} (hS : StableUnder L S) (hS1 : S ≠ ⊥) : ∃ I ∈ irrSet L, I ≤ S := by
  have hfin : Finite (Subgroup W) :=
    Finite.of_injective (fun K : Subgroup W => (K : Set W)) SetLike.coe_injective
  let P : Set (Subgroup W) := {I | StableUnder L I ∧ I ≠ ⊥ ∧ I ≤ S}
  have hPne : P.Nonempty := ⟨S, hS, hS1, le_rfl⟩
  obtain ⟨I, hImin⟩ := (Set.toFinite P).exists_minimal hPne
  obtain ⟨hIstab, hIbot, hIle⟩ := hImin.prop
  have hcommStab : StableUnder L (commSub I L) :=
    CFSG.LocalAnalysis.WeakClosure81.stableUnder_commSub
      (fun h hh x hx => L.mul_mem (L.mul_mem hh hx) (L.inv_mem hh)) hIstab
  have hcommLe : commSub I L ≤ I := commSub_le_of_invariant hIstab
  have hcommNe : commSub I L ≠ ⊥ := by
    intro hbot
    have hle : I ≤ fixV L := commSub_eq_bot_iff.mp hbot
    rw [hfix] at hle
    exact hIbot (le_bot_iff.mp hle)
  have hcommMem : commSub I L ∈ P := ⟨hcommStab, hcommNe, hcommLe.trans hIle⟩
  have hcommEq : commSub I L = I := le_antisymm hcommLe (hImin.2 hcommMem hcommLe)
  have hfixStab : StableUnder L (fixV L) :=
    CFSG.LocalAnalysis.WeakClosure81.stableUnder_fixV
      (fun y hy h hh => L.mul_mem (L.mul_mem hy hh) (L.inv_mem hy))
  have hinfBot : I ⊓ fixV L = ⊥ := by
    by_contra hne
    have hmem : I ⊓ fixV L ∈ P :=
      ⟨CFSG.LocalAnalysis.WeakClosure81.stableUnder_inf hIstab hfixStab, hne,
        inf_le_left.trans hIle⟩
    have hIleInf : I ≤ I ⊓ fixV L := hImin.2 hmem inf_le_left
    have hle : I ≤ fixV L := hIleInf.trans inf_le_right
    have hbot : commSub I L = ⊥ := commSub_eq_bot_iff.mpr hle
    rw [hcommEq] at hbot
    exact hIbot hbot
  have hirrBot : IsIrrOn L I ⊥ := by
    refine ⟨?_, hIstab, ?_, ?_⟩
    · exact bot_lt_iff_ne_bot.mpr hIbot
    · intro x hx u hu
      rw [Subgroup.mem_bot] at hu
      simp [hu]
    · intro J hJ hbotJ hJI
      by_cases hJbot : J = ⊥
      · exact Or.inl hJbot
      · exact Or.inr (le_antisymm hJI (hImin.2 ⟨hJ, hJbot, hJI.trans hIle⟩ hJI))
  exact ⟨I, ⟨hcommEq, by rw [hinfBot]; exact hirrBot⟩, hIle⟩

private theorem le_sup_of_maximal_compl {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    {C D : Subgroup W} (hC : StableUnder L C) (hD : StableUnder L D)
    (hCD : C ⊓ D = ⊥)
    (hmax : ∀ E : Subgroup W, StableUnder L E → C ⊓ E = ⊥ → D ≤ E → E ≤ D) :
    ∀ I ∈ irrSet L, I ≤ C ⊔ D := by
  intro I hI
  have hIfix : I ⊓ fixV L = ⊥ := by rw [hfix]; simp
  have hirrBot : IsIrrOn L I ⊥ := by
    simpa [hIfix] using hI.2
  have hJstab : StableUnder L (I ⊓ (C ⊔ D)) :=
    CFSG.LocalAnalysis.WeakClosure81.stableUnder_inf hI.2.2.1
      (CFSG.LocalAnalysis.WeakClosure81.stableUnder_sup hC hD)
  have hJle : I ⊓ (C ⊔ D) ≤ I := inf_le_left
  rcases hirrBot.2.2.2 (I ⊓ (C ⊔ D)) hJstab bot_le hJle with hJbot | hJI
  · exfalso
    have hIbot : I ≠ ⊥ := by
      have hlt := hI.2.1
      rw [hIfix] at hlt
      exact bot_lt_iff_ne_bot.mp hlt
    have hIDbot : I ⊓ D = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      have hxJ : x ∈ I ⊓ (C ⊔ D) := ⟨hx.1, Subgroup.mem_sup_right hx.2⟩
      rw [hJbot] at hxJ
      exact hxJ
    have hD'stab : StableUnder L (D ⊔ I) :=
      CFSG.LocalAnalysis.WeakClosure81.stableUnder_sup hD hI.2.2.1
    have hCD'bot : C ⊓ (D ⊔ I) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro c hc
      obtain ⟨hcC, hcD'I⟩ := hc
      change c ∈ D ⊔ I at hcD'I
      rw [Subgroup.mem_sup] at hcD'I
      obtain ⟨d, hdD, i, hiI, hci⟩ := hcD'I
      have hiJ : i ∈ I ⊓ (C ⊔ D) := by
        refine ⟨hiI, ?_⟩
        have hi_eq : i = d⁻¹ * c := by
          rw [← hci, inv_mul_cancel_left]
        rw [hi_eq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hdD))
          (Subgroup.mem_sup_left hcC)
      rw [hJbot] at hiJ
      have hi1 : i = 1 := Subgroup.mem_bot.mp hiJ
      have hcD : c ∈ D := by
        rw [← hci, hi1, mul_one]
        exact hdD
      have hcCD : c ∈ C ⊓ D := ⟨hcC, hcD⟩
      rw [hCD] at hcCD
      exact hcCD
    have hle : D ≤ D ⊔ I := le_sup_left
    have hle' : D ⊔ I ≤ D := hmax (D ⊔ I) hD'stab hCD'bot hle
    have hIleD : I ≤ D := le_sup_right.trans hle'
    have hIleBot : I ≤ ⊥ := by
      rw [← hIDbot]
      exact le_inf le_rfl hIleD
    exact hIbot (le_bot_iff.mp hIleBot)
  · rw [← hJI]
    exact inf_le_right

theorem exists_stableUnder_compl [Finite W] {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {C : Subgroup W} (hC : StableUnder L C) :
    ∃ D : Subgroup W, StableUnder L D ∧ C ⊓ D = ⊥ ∧ C ⊔ D = ⊤ := by
  have hfin : Finite (Subgroup W) :=
    Finite.of_injective (fun K : Subgroup W => (K : Set W)) SetLike.coe_injective
  let P : Set (Subgroup W) := {D | StableUnder L D ∧ C ⊓ D = ⊥}
  have hPne : P.Nonempty := by
    refine ⟨⊥, ?_, ?_⟩
    · intro x hx u hu
      rw [Subgroup.mem_bot] at hu
      simp [hu]
    · simp
  obtain ⟨D, hDmax⟩ := (Set.toFinite P).exists_maximal hPne
  obtain ⟨hDstab, hCDbot⟩ := hDmax.prop
  have hmax : ∀ E : Subgroup W, StableUnder L E → C ⊓ E = ⊥ → D ≤ E → E ≤ D :=
    fun E hEstab hCE hDE => hDmax.2 ⟨hEstab, hCE⟩ hDE
  have hID : ∀ I ∈ irrSet L, I ≤ C ⊔ D :=
    le_sup_of_maximal_compl hfix hC hDstab hCDbot hmax
  refine ⟨D, hDstab, hCDbot, le_antisymm le_top ?_⟩
  rw [← hspan]
  exact iSup₂_le hID

theorem exists_stableUnder_compl_le [Finite W] {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {C S : Subgroup W} (hC : StableUnder L C)
    (hS : StableUnder L S) (hCS : C ≤ S) :
    ∃ D ≤ S, StableUnder L D ∧ C ⊓ D = ⊥ ∧ C ⊔ D = S := by
  obtain ⟨D₀, hD₀stab, hCD₀bot, hCD₀top⟩ := exists_stableUnder_compl hfix hspan hC
  refine ⟨S ⊓ D₀, inf_le_left, ?_, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.WeakClosure81.stableUnder_inf hS hD₀stab
  · refine le_antisymm ?_ bot_le
    intro x hx
    have hxCD₀ : x ∈ C ⊓ D₀ := ⟨hx.1, hx.2.2⟩
    rw [hCD₀bot] at hxCD₀
    exact hxCD₀
  · refine le_antisymm (sup_le hCS inf_le_left) ?_
    intro s hs
    have hsTop : s ∈ C ⊔ D₀ := by rw [hCD₀top]; exact Subgroup.mem_top s
    rw [Subgroup.mem_sup] at hsTop
    obtain ⟨c, hcC, d₀, hd₀D₀, hcd⟩ := hsTop
    have hd₀S : d₀ ∈ S := by
      have hd₀_eq : d₀ = c⁻¹ * s := by
        rw [← hcd, inv_mul_cancel_left]
      rw [hd₀_eq]
      exact S.mul_mem (S.inv_mem (hCS hcC)) hs
    have hd₀ : d₀ ∈ S ⊓ D₀ := ⟨hd₀S, hd₀D₀⟩
    rw [← hcd]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right hd₀)

theorem card_inf_fixV_sup {X : Subgroup (MulAut W)} {A B : Subgroup W} (hA : StableUnder X A)
    (hB : StableUnder X B) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥((A ⊔ B) ⊓ fixV X) = Nat.card ↥(A ⊓ fixV X) * Nat.card ↥(B ⊓ fixV X) := by
  let f : ↥(A ⊓ fixV X) × ↥(B ⊓ fixV X) → ↥((A ⊔ B) ⊓ fixV X) :=
    fun p => ⟨p.1.1 * p.2.1, by
      refine ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2.1)
        (Subgroup.mem_sup_right p.2.2.1), ?_⟩
      change p.1.1 * p.2.1 ∈ fixV X
      rw [mem_fixV]
      intro x hx
      rw [map_mul, mem_fixV.mp p.1.2.2 x hx, mem_fixV.mp p.2.2.2 x hx]⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have hval : p.1.1 * p.2.1 = q.1.1 * q.2.1 := by
      simpa [f] using congrArg Subtype.val hpq
    have hxy : ((⟨p.1.1, p.1.2.1⟩ : ↥A), (⟨p.2.1, p.2.2.1⟩ : ↥B)) =
        ((⟨q.1.1, q.1.2.1⟩ : ↥A), (⟨q.2.1, q.2.2.1⟩ : ↥B)) :=
      Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hAB) (by simpa using hval)
    have hp1 : p.1.1 = q.1.1 := congrArg (fun z : ↥A × ↥B => (z.1 : W)) hxy
    have hp2 : p.2.1 = q.2.1 := congrArg (fun z : ↥A × ↥B => (z.2 : W)) hxy
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hwAB, hwFix⟩
    change w ∈ A ⊔ B at hwAB
    rw [Subgroup.mem_sup] at hwAB
    obtain ⟨a, haA, b, hbB, hw_eq⟩ := hwAB
    have hfix_prod : ∀ x ∈ X, x a * x b = a * b := by
      intro x hx
      have hxw : x w = w := mem_fixV.mp hwFix x hx
      calc x a * x b = x (a * b) := (map_mul x a b).symm
        _ = x w := by rw [hw_eq]
        _ = w := hxw
        _ = a * b := hw_eq.symm
    have haFix : a ∈ fixV X := by
      rw [mem_fixV]
      intro x hx
      have hpair := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hAB)
        (a₁ := ((⟨x a, hA x hx a haA⟩ : ↥A), (⟨x b, hB x hx b hbB⟩ : ↥B)))
        (a₂ := ((⟨a, haA⟩ : ↥A), (⟨b, hbB⟩ : ↥B)))
        (by simpa using hfix_prod x hx)
      exact congrArg (fun z : ↥A × ↥B => (z.1 : W)) hpair
    have hbFix : b ∈ fixV X := by
      rw [mem_fixV]
      intro x hx
      have hpair := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hAB)
        (a₁ := ((⟨x a, hA x hx a haA⟩ : ↥A), (⟨x b, hB x hx b hbB⟩ : ↥B)))
        (a₂ := ((⟨a, haA⟩ : ↥A), (⟨b, hbB⟩ : ↥B)))
        (by simpa using hfix_prod x hx)
      exact congrArg (fun z : ↥A × ↥B => (z.2 : W)) hpair
    refine ⟨(⟨a, ⟨haA, haFix⟩⟩, ⟨b, ⟨hbB, hbFix⟩⟩), ?_⟩
    simpa [f] using Subtype.ext hw_eq
  have hcard : Nat.card (↥(A ⊓ fixV X) × ↥(B ⊓ fixV X)) = Nat.card ↥((A ⊔ B) ⊓ fixV X) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
