module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Clique
public import CFSG.RankThree.GF2n.Stroth80.Sec101Orbit
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatCtx
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem IsClique101.comm_root (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y)
    (hYQ : ∀ E, IsRootB M B E → E ≤ X → Y ≤ QB E) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  by_cases hXZ : X = Z
  · subst X
    exact (Ctx.Z_central hc hx ((IsRootB.ctx hc hY).le hy)).symm
  · have hnot : ¬ X ≤ Z := fun h => hXZ (le_antisymm h hX.Z_le)
    obtain ⟨x₀, hx₀X, hx₀Z⟩ := Set.not_subset.mp hnot
    obtain ⟨E, hE, hx₀E, hEX⟩ := hX.cover x₀ hx₀X hx₀Z
    have hxI : x ∈ Q ⊓ QB E := ⟨hX.le_Q hx, hX.le_QB E hE hEX hx⟩
    have hyI : y ∈ Q ⊓ QB E := ⟨(IsRootB.ctx hc hY).le hy, hYQ E hE hEX hy⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (n12l3_comm_inf_QB (hE.ctx hc) x hxI y hyI)

private theorem IsClique101.conj_sup_le_of_mem_Q (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y) {p : G} (hpQ : p ∈ Q) :
    conjSubgroup p (X ⊔ Y) ≤ X ⊔ Y := by
  have hmapX : conjSubgroup p X ≤ X := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    have hcomm : ⁅p, p⁻¹ * z * p⁆ ∈ Z := Smith81.comm_mem_Z hc.hyp hpQ (hX.le_Q hz)
    have hid : p * (p⁻¹ * z * p) * p⁻¹ = ⁅p, p⁻¹ * z * p⁆ * (p⁻¹ * z * p) := by
      rw [commutatorElement_def]; group
    have hz' : p * (p⁻¹ * z * p) * p⁻¹ = z := by group
    rw [← hz', hid]
    exact X.mul_mem (hX.Z_le hcomm) hz
  have hmapY : conjSubgroup p Y ≤ X ⊔ Y := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    have hcomm : ⁅p, p⁻¹ * z * p⁆ ∈ Z :=
      Smith81.comm_mem_Z hc.hyp hpQ ((IsRootB.ctx hc hY).le hz)
    have hid : p * (p⁻¹ * z * p) * p⁻¹ = ⁅p, p⁻¹ * z * p⁆ * (p⁻¹ * z * p) := by
      rw [commutatorElement_def]; group
    have hz' : p * (p⁻¹ * z * p) * p⁻¹ = z := by group
    rw [← hz', hid]
    exact (X ⊔ Y).mul_mem (Subgroup.mem_sup_left (hX.Z_le hcomm)) (Subgroup.mem_sup_right hz)
  rw [conjSubgroup_sup']
  exact sup_le (hmapX.trans le_sup_left) hmapY

private theorem IsClique101.conj_sup_le_of_mem_QB (hc : Ctx M Q Z B) {X Y E : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y) (hE : IsRootB M B E) (hEX : E ≤ X)
    (hYQ : ∀ E, IsRootB M B E → E ≤ X → Y ≤ QB E) {s : G} (hsQB : s ∈ QB E) :
    conjSubgroup s (X ⊔ Y) ≤ X ⊔ Y := by
  have hXE : X ≤ QB E := hX.le_QB E hE hEX
  have hYE : Y ≤ QB E := hYQ E hE hEX
  have hmapX : conjSubgroup s X ≤ X := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    have hcomm : ⁅s, s⁻¹ * z * s⁆ ∈ E := (hE.ctx hc).QB_comm_mem hsQB (hXE hz)
    have hid : s * (s⁻¹ * z * s) * s⁻¹ = ⁅s, s⁻¹ * z * s⁆ * (s⁻¹ * z * s) := by
      rw [commutatorElement_def]; group
    have hz' : s * (s⁻¹ * z * s) * s⁻¹ = z := by group
    rw [← hz', hid]
    exact X.mul_mem (hEX hcomm) hz
  have hmapY : conjSubgroup s Y ≤ X ⊔ Y := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    have hcomm : ⁅s, s⁻¹ * z * s⁆ ∈ E := (hE.ctx hc).QB_comm_mem hsQB (hYE hz)
    have hid : s * (s⁻¹ * z * s) * s⁻¹ = ⁅s, s⁻¹ * z * s⁆ * (s⁻¹ * z * s) := by
      rw [commutatorElement_def]; group
    have hz' : s * (s⁻¹ * z * s) * s⁻¹ = z := by group
    rw [← hz', hid]
    exact (X ⊔ Y).mul_mem (Subgroup.mem_sup_left (hEX hcomm)) (Subgroup.mem_sup_right hz)
  rw [conjSubgroup_sup']
  exact sup_le (hmapX.trans le_sup_left) hmapY

private theorem exists_conj_root_of_mem_sup_mem_Z (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y) {x y : G} (hxX : x ∈ X)
    (hxZ : x ∈ Z) (hyY : y ∈ Y) (hwX : x * y ∉ X) :
    ∃ p : G, IsRootB M B (conjSubgroup p Y) ∧ x * y ∈ conjSubgroup p Y ∧
      conjSubgroup p (X ⊔ Y) = X ⊔ Y := by
  have hyX : y ∉ X := fun h => hwX (X.mul_mem hxX h)
  have hyQ : y ∈ Q := (IsRootB.ctx hc hY).le hyY
  have hxy : x * y = y * x := (Ctx.Z_central hc hxZ hyQ).symm
  have hmem : x * y ∈ Y ⊔ Z := by
    rw [hxy]
    exact (Y ⊔ Z).mul_mem (Subgroup.mem_sup_left hyY) (Subgroup.mem_sup_right hxZ)
  have hnotZ : x * y ∉ Z := fun h => hyX (by
    have h' : y = x⁻¹ * (x * y) := by group
    rw [h']
    exact hX.Z_le (Z.mul_mem (Z.inv_mem hxZ) h))
  obtain ⟨p, hpQ, hpw⟩ := (IsRootB.ctx hc hY).exists_mem_conj_of_mem_sup hmem hnotZ
  have heq : conjSubgroup p (X ⊔ Y) = X ⊔ Y :=
    Subgroup.eq_of_le_of_card_ge (hX.conj_sup_le_of_mem_Q hc hY hpQ) (card_conjSubgroup p _).ge
  exact ⟨p, hY.conj (hc.hyp.Q_normal.1 hpQ), hpw, heq⟩

private theorem exists_conj_root_of_mem_sup_not_mem_Z (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y)
    (hYQ : ∀ E, IsRootB M B E → E ≤ X → Y ≤ QB E) (hYX : ¬ Y ≤ X)
    {x y : G} (hxX : x ∈ X) (hxZ : x ∉ Z) (hyY : y ∈ Y) (hwX : x * y ∉ X) :
    ∃ s : G, IsRootB M B (conjSubgroup s Y) ∧ x * y ∈ conjSubgroup s Y ∧
      conjSubgroup s (X ⊔ Y) = X ⊔ Y := by
  have hyX : y ∉ X := fun h => hwX (X.mul_mem hxX h)
  have hy1 : y ≠ 1 := fun h => hyX (h ▸ X.one_mem)
  obtain ⟨E, hE, hxE, hEX⟩ := hX.cover x hxX hxZ
  have hyQB : y ∈ QB E := hYQ E hE hEX hyY
  have hnotE : y ∉ E := by
    intro hyE
    have hEq : Y = E :=
      Smith81.IsZConjugate.eq_of_mem hc.hyp (hY.isZConjugate hc) (hE.isZConjugate hc)
        hy1 hyY hyE
    exact hYX (hEq ▸ hEX)
  have hnotSup : y ∉ Z ⊔ E := fun h => hyX (sup_le hX.Z_le hEX h)
  obtain ⟨s, hs, hsy⟩ := (hE.ctx hc).exists_mem_QB_M_comm_eq hyQB hnotSup hxE
  have hw : x * y = s * y * s⁻¹ := by
    rw [show s * y * s⁻¹ = ⁅s, y⁆ * y by rw [commutatorElement_def]; group, hsy]
  have hmem : x * y ∈ conjSubgroup s Y := by
    rw [hw, mem_conjSubgroup]
    rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group]
  have heq : conjSubgroup s (X ⊔ Y) = X ⊔ Y :=
    Subgroup.eq_of_le_of_card_ge (hX.conj_sup_le_of_mem_QB hc hY hE hEX hYQ hs.1)
      (card_conjSubgroup s _).ge
  exact ⟨s, hY.conj hs.2, hmem, heq⟩

private theorem exists_conj_root_of_mem_sup (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y)
    (hYQ : ∀ E, IsRootB M B E → E ≤ X → Y ≤ QB E) (hYX : ¬ Y ≤ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ w ∈ X ⊔ Y, w ∉ X → ∃ g : G, IsRootB M B (conjSubgroup g Y) ∧
      w ∈ conjSubgroup g Y ∧ conjSubgroup g (X ⊔ Y) = X ⊔ Y := by
  intro w hw hwX
  obtain ⟨x, hxX, y, hyY, rfl⟩ := exists_mul_of_mem_sup hcomm hw
  by_cases hxZ : x ∈ Z
  · exact exists_conj_root_of_mem_sup_mem_Z hc hX hY hxX hxZ hyY hwX
  · exact exists_conj_root_of_mem_sup_not_mem_Z hc hX hY hYQ hYX hxX hxZ hyY hwX

private theorem IsClique101.le_QB_sup_root (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y)
    (hYQ : ∀ E, IsRootB M B E → E ≤ X → Y ≤ QB E) (hYX : ¬ Y ≤ X) :
    X ⊔ Y ≤ QB Y := by
  have hZ : Z ≤ QB Y := (IsRootB.ctx hc hY).Z_le_QB.1
  have hroot : ∀ E, IsRootB M B E → E ≤ X → E ≤ QB Y := by
    intro E hE hEX
    have hne : E ≠ Y := fun h => hYX (h ▸ hEX)
    exact (StrothHyp.le_QB_iff_le_QB hc.hyp (hE.isZConjugate hc) (hY.isZConjugate hc)
      hne).mpr (hYQ E hE hEX)
  exact sup_le (hX.le_of_roots hZ hroot)
    (Smith81.IsZConjugate.le_QB_self hc.hyp (hY.isZConjugate hc))

theorem IsClique101.sup_root (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hY : IsRootB M B Y)
    (hYQ : ∀ E, IsRootB M B E → E ≤ X → Y ≤ QB E) (hYX : ¬ Y ≤ X) :
    IsClique101 M Q Z B (X ⊔ Y) ∧ Nat.card X < Nat.card ↥(X ⊔ Y) := by
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := hX.comm_root hc hY hYQ
  have hleY : X ⊔ Y ≤ QB Y := hX.le_QB_sup_root hc hY hYQ hYX
  refine ⟨⟨hX.Z_le.trans le_sup_left, sup_le hX.le_Q ((IsRootB.ctx hc hY).le), ?_, ?_⟩, ?_⟩
  · intro w hw hwZ
    by_cases hwX : w ∈ X
    · obtain ⟨E, hE, hwE, hEX⟩ := hX.cover w hwX hwZ
      exact ⟨E, hE, hwE, hEX.trans le_sup_left⟩
    · obtain ⟨g, hg, hwg, hEq⟩ :=
        exists_conj_root_of_mem_sup hc hX hY hYQ hYX hcomm w hw hwX
      exact ⟨conjSubgroup g Y, hg, hwg, hEq ▸ Subgroup.map_mono le_sup_right⟩
  · intro D hD hDle
    by_cases hDX : D ≤ X
    · exact sup_le (hX.le_QB D hD hDX) (hYQ D hD hDX)
    · obtain ⟨w, hwD, hwX⟩ := Set.not_subset.mp hDX
      obtain ⟨g, hg, hwg, hEq⟩ :=
        exists_conj_root_of_mem_sup hc hX hY hYQ hYX hcomm w (hDle hwD) hwX
      have hw1 : w ≠ 1 := fun h => hwX (h ▸ X.one_mem)
      have hDeq : D = conjSubgroup g Y :=
        Smith81.IsZConjugate.eq_of_mem hc.hyp (hD.isZConjugate hc) (hg.isZConjugate hc)
          hw1 hwD hwg
      calc X ⊔ Y = conjSubgroup g (X ⊔ Y) := hEq.symm
        _ ≤ conjSubgroup g (QB Y) := Subgroup.map_mono hleY
        _ = QB (conjSubgroup g Y) := (QB_conj g Y).symm
        _ = QB D := by rw [hDeq]
  · have hlt : X < X ⊔ Y := lt_of_le_of_ne le_sup_left (fun h => hYX (h.symm ▸ le_sup_right))
    exact Subgroup.card_lt_of_lt hlt

end CFSG.RankThree.GF2n.Stroth80
