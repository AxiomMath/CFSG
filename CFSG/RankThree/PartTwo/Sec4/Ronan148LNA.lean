module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Interface
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)

@[expose] def E27Move (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup S, Late.IsE27 E → ∀ s ∈ E, s ≠ 1 →
    ∃ n ∈ Subgroup.normalizer (E : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)

section Core

variable {G : Type} [Group G] [Finite G]

theorem not_normalizer_le_of_e27Move {S : Type} [Group S] {L A : Subgroup G} (φ : L ≃* S)
    (hmove : E27Move S) (hAL : A ≤ L) (hA : Late.IsE27 A) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro hN
  have hcL : c ∈ L := hAL hcA
  have hASe : Late.IsE27 ((A.subgroupOf L).map φ.toMonoidHom) :=
    ⟨isElemAbelian_map _ (isElemAbelian_comap L.subtype L.subtype_injective hA.1), by
      rw [Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA.2]⟩
  have hsAS : φ ⟨c, hcL⟩ ∈ (A.subgroupOf L).map φ.toMonoidHom := ⟨⟨c, hcL⟩, hcA, rfl⟩
  have hs1 : φ ⟨c, hcL⟩ ≠ 1 := by
    rw [Ne, map_eq_one_iff _ φ.injective]
    exact fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨n, hn, hns⟩ := hmove _ hASe _ hsAS hs1
  rw [← Subgroup.map_equiv_normalizer_eq] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  have hmc := hN (mem_normalizer_of_subgroupOf hAL hm)
  apply hns
  have hZc : (Subgroup.zpowers (⟨c, hcL⟩ : L)).map φ.toMonoidHom =
      Subgroup.zpowers (φ ⟨c, hcL⟩) := MonoidHom.map_zpowers _ _
  rw [← hZc, ← Subgroup.map_equiv_normalizer_eq]
  refine ⟨m, ?_, rfl⟩
  rw [← zpowers_subgroupOf hcL]
  exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hcL) hmc

theorem eq_one_of_mem_centralizer_of_rank (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {L E : Subgroup G} (hZ : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1)
    (hEL : E ≤ L) (hE : Late.IsE27 E) {w : G} (hw : w ∈ Subgroup.centralizer (L : Set G))
    (hw3 : w ^ 3 = 1) : w = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hw1
  have hW : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers w) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hw3
  have hWc : Nat.card (Subgroup.zpowers w) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have hc : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers w, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right
      (show Commute x w from Subgroup.mem_centralizer_iff.mp hw x (hEL hx)) k).eq
  have hinf : E ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxW⟩
    rw [Subgroup.mem_bot]
    refine hZ x (hEL hxE) ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxW
    exact Subgroup.zpow_mem _ hw k
  have hB := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hE.1 hW hc
  have hBc := Ronan148R.card_sup_of_commute_of_inf hc hinf
  rw [hE.2, hWc] at hBc
  have hle := card_le_of_pRank_le h3 hB
  rw [hBc] at hle
  norm_num at hle

end Core

section Row

theorem center_eq_bot_of_noThreeCover {G : Type} [Group G] [Finite G] {S : Type} [Group S]
    (h3 : NoThreeCover S) (hθ : aschbacherSolvableCore 3 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) (eL : L ⧸ Subgroup.center L ≃* S) : Subgroup.center L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (RonanK429.isPGroup_center_of_isComponent hθ hL).exists_card_eq
  have hn3 : ¬ 3 ∣ Nat.card (Subgroup.center L) :=
    h3 L (HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hL.1) ⟨eL⟩
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd (hk ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)) hn3

theorem row425_of_e27Move {S : Type} [Group S] (h3 : NoThreeCover S) (hcube : CubeInner S)
    (hE : ∃ E : Subgroup S, Late.IsE27 E) (hmove : E27Move S) : Row425 S := by
  intro G _ _ _ A hA hrk hθ L hL ⟨eL⟩ c hLc K _ K' hK' _ hAZ hN
  exfalso
  have hcmem : c ∈ A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) :=
    hAZ ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcmem.1
  have hK'L : K' ≤ L := (hK' ▸ Subgroup.map_subtype_le K).trans inf_le_left
  have hcL : c ∈ L := hK'L hcmem.2.1
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hLc fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_noThreeCover h3 hθ hL eL
  let φ : L ≃* S := (RonanK429.quotCenterEquivOfEqBot hZ).trans eL
  have hAc : ∀ a ∈ A, a * c = c * a := fun a ha =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨c, hcA⟩)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases CFSG.LocalCores.distinct_components_commute
        (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hL) hL with h | h
    · exact h
    · exfalso
      have hcLa : c ∈ L.map (MulAut.conj a).toMonoidHom := by
        refine ⟨c, hcL, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hAc a ha, mul_inv_cancel_right]
      have hcC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hcLa
      exact hLc fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcC x hx)
  have hLE : ∃ E : Subgroup G, E ≤ L ∧ Late.IsE27 E := by
    obtain ⟨E, hE⟩ := hE
    refine ⟨(E.map φ.symm.toMonoidHom).map L.subtype, Subgroup.map_subtype_le _,
      isElemAbelian_map _ (isElemAbelian_map _ hE.1), ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective φ.symm.injective, hE.2]
  obtain ⟨E, hEL, hEe⟩ := hLE
  have hLC : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → x = 1 := by
    intro x hxL hxC
    have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hAL : A ≤ L := Ronan148R.le_of_inner_of_centralizer hZ (cubeInner_of_mulEquiv φ hcube) hAN
    hA.1 fun w hw hw3 => eq_one_of_mem_centralizer_of_rank hrk.le hLC hEL hEe hw hw3
  exact not_normalizer_le_of_e27Move φ hmove hAL hA hcA hc1 hN

theorem row425_of_e81 {S : Type} [Group S] (h3 : NoThreeCover S)
    (hE : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81) : Row425 S := by
  intro G _ _ _ A hA hrk hθ L hL ⟨eL⟩ c hLc K _ K' hK' _ hAZ hN
  exfalso
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_noThreeCover h3 hθ hL eL
  let φ : L ≃* S := (RonanK429.quotCenterEquivOfEqBot hZ).trans eL
  obtain ⟨E, hE, hE81⟩ := hE
  have hle := card_le_of_pRank_le hrk.le
    (isElemAbelian_map L.subtype (isElemAbelian_map φ.symm.toMonoidHom hE))
  rw [Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective φ.symm.injective, hE81] at hle
  norm_num at hle

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
