module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddGroup
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSL2Aut
public import CFSG.RankThree.PartTwo.Sec18.Item187NAut

public section

namespace CFSG.RankThree.PartTwo.Sec20.L3OddAut

open scoped commutatorElement

section InvData

open CFSG.GH74.KGroups.L3Eps
open scoped commutatorElement

theorem le_of_isPerfect_of_le_centralizer {K : Type*} [Group K] {q : ℕ} {t : K}
    {S : Subgroup K} (hI : InvData q K t S) {L : Subgroup K} (hL : Group.IsPerfect L)
    (hLt : L ≤ Subgroup.centralizer ({t} : Set K)) : L ≤ S := by
  have hLL : ⁅L, L⁆ = L := (Subgroup.isPerfect_iff).mp hL
  rw [← hLL, Subgroup.commutator_le]
  intro x hx y hy
  exact hI.commutator_mem x (hLt hx) y (hLt hy)

theorem map_eq_of_invData {K : Type*} [Group K] [Finite K] {q : ℕ} {t : K} {S : Subgroup K}
    (hI : InvData q K t S) (α : MulAut K) (hα : α t = t) : S.map α.toMonoidHom = S := by
  have hC : ∀ x, x ∈ Subgroup.centralizer ({t} : Set K) →
      α.symm x ∈ Subgroup.centralizer ({t} : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hαt : α.symm t = t := by
      conv_lhs => rw [← hα]
      exact α.symm_apply_apply t
    rw [← hαt, ← map_mul, ← map_mul, hx]
  have hle : S ≤ S.map α.toMonoidHom := by
    have hSS : ⁅S, S⁆ = S := (Subgroup.isPerfect_iff).mp hI.quasisimple.1
    calc S = ⁅S, S⁆ := hSS.symm
      _ ≤ S.map α.toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        refine ⟨⁅α.symm x, α.symm y⁆, hI.commutator_mem _ (hC x (hI.le_centralizer hx)) _
          (hC y (hI.le_centralizer hy)), ?_⟩
        simp [map_commutatorElement]
  exact (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective α.injective).le).symm

theorem fixes_of_invData {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {t : Y} {S : Subgroup Y} (hI : CFSG.GH74.KGroups.L3Eps.InvData p Y t S)
    (eS : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) {σ : MulAut Y} {a : ℕ}
    (hσ : σ ^ 2 ^ a = 1) (hσt : σ t = t) {L : Subgroup Y} (hLS : L ≤ S)
    (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥) (hfix : ∀ l ∈ L, σ l = l) : ∀ s ∈ S, σ s = s := by
  have hS := map_eq_of_invData hI σ hσt
  have hτ : Sec18.Item187Proof.restrictAut σ S hS ^ 2 ^ a = 1 := by
    ext s
    rw [Sec18.Item187Proof.coe_pow_restrictAut, hσ]
    rfl
  have hM : Group.IsPerfect (L.subgroupOf S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLS).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hMZ : ¬ L.subgroupOf S ≤ Subgroup.center S := fun h =>
    hL1 (disjoint_self.mp ((Subgroup.subgroupOf_eq_bot.mp
      (CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot _ h)).mono_right hLS))
  have hτ1 := SL2Aut.eq_one_of_fixes_isPerfect hp5 eS hτ hM hMZ fun l hl =>
    Subtype.ext ((Sec18.Item187Proof.coe_restrictAut σ S hS l).trans
      (hfix _ (Subgroup.mem_subgroupOf.mp hl)))
  intro s hs
  simpa [Sec18.Item187Proof.coe_restrictAut] using
    congrArg Subtype.val (DFunLike.congr_fun hτ1 ⟨s, hs⟩)

end InvData

section Outer

open CFSG.GH74.GLS.IVK (L2 L2Field)

private theorem eq_one_of_commute_of_fixes {Y : Type} [Group Y]
    [Finite Y] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : 3 < p) {σ : MulAut Y}
    {N : Subgroup Y} (hN : ∀ x y, σ x = x → σ y = y → ⁅x, y⁆ ∈ N)
    (ψ : ↥N ≃* L2 (GaloisField p 1)) {L : Subgroup Y} (hL : Group.IsPerfect L)
    (hfix : ∀ l ∈ L, σ l = l) {z : Y} (hzL : z ∈ L) (hz : ∀ l ∈ L, z * l = l * z) : z = 1 := by
  have hcard : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have hF : L2Field (GaloisField p 1) := by
    refine ⟨?_, ?_⟩ <;> rw [hcard]
    · exact (Fact.out : p.Prime).odd_of_ne_two hp2
    · exact hp3
  have hLN : L ≤ N := by
    rw [← (Subgroup.isPerfect_iff).mp hL, Subgroup.commutator_le]
    exact fun x hx y hy => hN x y (hfix x hx) (hfix y hy)
  by_contra hz1
  have hM : Group.IsPerfect (L.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLN).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hM1 : L.subgroupOf N ≠ ⊥ := by
    intro h
    have hmem : (⟨z, hLN hzL⟩ : ↥N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr hzL
    rw [h, Subgroup.mem_bot] at hmem
    exact hz1 (congrArg Subtype.val hmem)
  have := L2OddGroup.isSimpleGroup_of_isPerfect hF ψ hM hM1
  have hzc : (⟨⟨z, hLN hzL⟩, Subgroup.mem_subgroupOf.mpr hzL⟩ : ↥(L.subgroupOf N)) ∈
      Subgroup.center ↥(L.subgroupOf N) :=
    Subgroup.mem_center_iff.mpr fun m =>
      Subtype.ext (Subtype.ext (hz _ (Subgroup.mem_subgroupOf.mp m.2)).symm)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(L.subgroupOf N)) with h | h
  · rw [h, Subgroup.mem_bot] at hzc
    exact hz1 (congrArg (fun m : ↥(L.subgroupOf N) => ((m : ↥N) : Y)) hzc)
  · exact Group.IsPerfect.not_isMulCommutative ↥(L.subgroupOf N)
      (Subgroup.center_eq_top_iff.mp h)

theorem false_of_fixes_center_L3 {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : p % 3 = 2)
    (e : Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p 1)) {σ : MulAut Y}
    (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : Y →* MulAut Y).range) {L : Subgroup Y}
    (hL : Group.IsPerfect L) (hfix : ∀ l ∈ L, σ l = l) {z : Y} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hz : ∀ l ∈ L, z * l = l * z) : False := by
  obtain ⟨N, -, -, hN, ⟨ψ⟩⟩ :=
    L3OddGroup.exists_L2_of_not_inner_L3 (f := 1) hp2 (by rwa [pow_one]) e hσ hout
  have hp := (Fact.out : p.Prime).two_le
  exact hz1 (eq_one_of_commute_of_fixes hp2 (by omega) hN ψ hL hfix hzL hz)

theorem false_of_fixes_center_U3 {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : p % 3 = 1)
    (e : Y ≃* CFSG.Assembly.RankThreeEven.projSU 3 p 1) {σ : MulAut Y}
    (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : Y →* MulAut Y).range) {L : Subgroup Y}
    (hL : Group.IsPerfect L) (hfix : ∀ l ∈ L, σ l = l) {z : Y} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hz : ∀ l ∈ L, z * l = l * z) : False := by
  obtain ⟨N, -, -, hN, ⟨ψ⟩⟩ := L3OddGroup.exists_L2_of_not_inner_U3 hq e hσ hout
  have hp7 := L3OddGroup.seven_le_of_mod_three_eq_one (Fact.out : p.Prime) hq
  exact hz1 (eq_one_of_commute_of_fixes hp2 (by omega) hN ψ hL hfix hzL hz)

end Outer

end CFSG.RankThree.PartTwo.Sec20.L3OddAut
