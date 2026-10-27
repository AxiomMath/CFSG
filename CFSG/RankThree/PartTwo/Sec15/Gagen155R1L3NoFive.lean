module

public import CFSG.RankThree.PartTwo.Sec15.Gagen148FivePair
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Step3
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_of_tau {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z) (hQE9 : Sylow155R1.Res1QE9 Q) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro h hh
  have hD := τ.sec15.toSec13Data
  have hhn : h ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := τ.norm hh
  have hL' : L.map (MulAut.conj h).toMonoidHom ∈ lA A (h * c * h⁻¹) :=
    (Sec13.map_conj_mem_lA_iff hh).mpr hD.mem_lA
  have hz : Subgroup.zpowers (h * c * h⁻¹) = Subgroup.zpowers c := by
    have h1 : (Subgroup.zpowers c).map (MulAut.conj h).toMonoidHom =
        Subgroup.zpowers (h * c * h⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← h1, CFSG.RankThree.PartTwo.Late.map_conj_eq_of_mem_normalizer hhn]
  have hc' : Subgroup.zpowers (h * c * h⁻¹) ∈ omegaA A := by
    rw [τ.omega]
    exact Set.mem_singleton_iff.mpr hz
  have hLeq : L.map (MulAut.conj h).toMonoidHom = L :=
    eq_of_mem_lA_of_tau τ hQE9 hc' hL'
  rwa [Subgroup.mem_normalizer_iff_map_conj_eq]

section Main


theorem not_case148Five_of_even (h135 : Item135) {P : ∀ (Y : Type) [Group Y], Prop}
    {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}
    (τ : Sylow155R1.Res1Tau Res1L3QEven P A c L X K Y M T P' Yc z)
    (h152 : Item152 A (lB A)) (h1511 : Item1511 A (lB A) c L)
    {Y' : Subgroup G} (hY' : Y' ∈ scriptY2 A) (hXY' : X ≤ Y')
    (hF : generalizedFitting ↥Y' = CFSG.pCore 2 ↥Y') [(ker148 A Y').Normal] :
    ¬ Case148Five A (lB A) Y' := by
  intro h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c', hc'A, -, n, -, -, -, hn, -, hX, -, -, hfield, -, -⟩ := h5
  have hD := τ.sec15.toSec13Data
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => τ.sec15.isElemAbelian.2 a ha
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := hY'.1.2
  obtain ⟨R, hR3, hAR, hRA, hRY, g, hgR, hg3, hgA⟩ :=
    exists_isPGroup_mem_not_mem_of_field hAY' hAc hA3 hc'A hn hX hfield
  have hQE9 : Sylow155R1.Res1QE9 Res1L3QEven :=
    res1QE9_of_le (Q := Res1L3QEven) fun _ _ h => h.1
  have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
    hRA.trans (normalizer_le_normalizer_of_tau τ hQE9)
  have hL4 : L ∈ scriptY4 A (lB A) := by
    have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
    have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one
      τ.sec15.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hD.le_centralizer))
    have h3L : 3 ∣ Nat.card L := by
      obtain ⟨E, -, hE9⟩ := (hQE9 _ τ.q).2
      have h3E : 3 ∣ Nat.card E := by rw [hE9]; norm_num
      exact Proof1515.three_dvd_card_of_thetaQuot (h3E.trans (Subgroup.card_subgroup_dvd_card E))
    exact ⟨⟨hLtop, hD.le_normalizer⟩,
      CFSG.RankThree.PartTwo.Sec16.eq_oPrimeResidualOf_of_isSimpleGroup
        (Sec6.isPerfect_of_mem_thetaComponentsAt hLc) τ.q.1.2.1 h3L,
      le_antisymm τ.l_delta (delta_le L), h135 G A c L hD τ.sec15.hypS_or_hypT⟩
  obtain ⟨X'', hX''c, hLX'', hX''0⟩ := h152 L hL4 Y' hY' (τ.l_le.trans hXY') hF
  have hRX'' : R ≤ Subgroup.normalizer (X'' : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hRY hX''c hLX''
      (isPerfect_of_mem_scriptY4 hL4) (ne_bot_of_mem_scriptY4 hL4) hRL
  have hRc : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hRA.trans τ.norm
  obtain ⟨P, hP, hRP⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge
    (K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (X'' : Set G)) (le_inf hRc hRX'') hR3
  obtain ⟨-, e, he, hLe⟩ := τ.q
  have hΩ : A = omegaOneThree P :=
    (h1511 2 e he hLe X'' hX''0 ⟨L, hL4, le_inf le_rfl hLX''⟩ P (hAR.trans hRP) hP).2.2.2.2
  exact hgA (hΩ.symm ▸ Subgroup.subset_closure ⟨hRP hgR, hg3⟩)

end Main

end CFSG.RankThree.PartTwo.Sec15.GagenL3
