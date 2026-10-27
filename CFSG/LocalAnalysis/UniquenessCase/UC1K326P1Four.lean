module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Loc
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Inner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem excluded_cover_data (hat : K326AtlasData) {L : Type} [Group L] (hex : ExcludedCover L) :
    ∃ (X : Type) (_ : Group X) (k : ℕ), (k = 2 ∨ k = 4) ∧
      Nonempty ((L ⧸ Subgroup.center L) ≃* X) ∧ CFSG.Quasithin.OddInner X ∧
      3 ^ k ∣ Nat.card X ∧ ¬ 3 ^ (k + 1) ∣ Nat.card X := by
  obtain ⟨hA6, hA7, hM22, hON, c6, c7, cM, cO⟩ := hat
  rcases hex with ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩
  · exact ⟨_, inferInstance, 2, Or.inl rfl, ⟨e⟩, hA6, by rw [c6]; norm_num, by rw [c6]; norm_num⟩
  · exact ⟨_, inferInstance, 2, Or.inl rfl, ⟨e⟩, hA7, by rw [c7]; norm_num, by rw [c7]; norm_num⟩
  · exact ⟨_, inferInstance, 2, Or.inl rfl, ⟨e⟩, hM22, by rw [cM]; norm_num, by rw [cM]; norm_num⟩
  · exact ⟨_, inferInstance, 4, Or.inr rfl, ⟨e⟩, hON, by rw [cO]; norm_num, by rw [cO]; norm_num⟩

theorem card_inf_centralizer_le (h : Hyp326 G n P) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hnorm : P ≤ Subgroup.normalizer (L : Set G))
    (hz : Subgroup.center ↥L ≠ ⊥) :
    Nat.card ↥(P ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 ^ n := by
  obtain ⟨ew⟩ := h.wr
  obtain ⟨-, -, hc⟩ := zwr_card_center h.one_le ew
  have hTn : ((P ⊓ L).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
    refine ⟨(g * x * g⁻¹ : ↥P).2, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hnorm g.2) (x : G)).1 hx.2
    simpa using this
  have hTnab : ¬ IsMulCommutative ((P ⊓ L).subgroupOf P) := by
    intro hcomm
    refine comp_sylow_not_commutative hL.2.2 (comp_center_isPGroup h.core hL) hz
      (comp_isSylowOf_inf h.sylow hL) ?_
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : (⟨(x : G), x.2.1⟩ : ↥P) ∈ (P ⊓ L).subgroupOf P := x.2
    have hy : (⟨(y : G), y.2.1⟩ : ↥P) ∈ (P ⊓ L).subgroupOf P := y.2
    have hc := congrArg (fun t => ((t : ↥P) : G))
      (Subtype.ext_iff.1 (hcomm.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩))
    apply Subtype.ext
    simpa using hc
  have hle : ((P ⊓ Subgroup.centralizer (L : Set G)).subgroupOf P) ≤ Subgroup.center ↥P := by
    refine le_trans ?_ (zwr_centralizer_nonabelian_normal h.one_le ew hTn hTnab)
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ht)).2
    have := Subgroup.mem_centralizer_iff.1 hx.2 (t : G) ht'
    exact Subtype.ext (by simpa using this)
  have hcard := Subgroup.card_le_of_le hle
  rw [hc, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ Subgroup.centralizer (L : Set G) ≤ P)).toEquiv]
    at hcard
  exact hcard

theorem excluded_numerics {n k a q t : ℕ} (hn : 1 ≤ n) (hk : k = 2 ∨ k = 4)
    (ha : a = 3 ^ (3 * n + 1)) (hq : q ≤ 3 ^ n) (haq : a ≤ q * 3 ^ k) (ht : t = 3 ^ (k + 1))
    (hta : t ≤ a) : False := by
  have h1 : a ≤ 3 ^ (n + k) := by
    calc a ≤ q * 3 ^ k := haq
      _ ≤ 3 ^ n * 3 ^ k := Nat.mul_le_mul_right _ hq
      _ = 3 ^ (n + k) := (pow_add 3 n k).symm
  subst ha ht
  have h2 : 3 * n + 1 ≤ n + k := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have h3 : k + 1 ≤ 3 * n + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hta
  omega

theorem excluded_cover_false (hat : K326AtlasData) (h : Hyp326 G n P) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hnorm : P ≤ Subgroup.normalizer (L : Set G))
    (hex : ExcludedCover ↥L) : False := by
  obtain ⟨X, _, k, hk, ⟨e⟩, hX, hk1, hk2⟩ := excluded_cover_data hat hex
  have hz3 : Nat.card (Subgroup.center ↥L) = 3 := by
    rcases hex with hh | hh | hh | hh <;> exact hh.2.1
  have hzne : Subgroup.center ↥L ≠ ⊥ := by
    intro hb
    rw [hb] at hz3
    simp at hz3
  have hk1' : 3 ^ k ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Nat.card_congr e.toEquiv]
    exact hk1
  have hk2' : ¬ 3 ^ (k + 1) ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Nat.card_congr e.toEquiv]
    exact hk2
  obtain ⟨ew⟩ := h.wr
  obtain ⟨hcardP, -, -⟩ := zwr_card_center h.one_le ew
  have hPp : IsPGroup 3 ↥P := h.sylow.isPGroup
  have hin : ∀ x ∈ P, ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.centralizer (L : Set G) := by
    intro x hx
    have hodd : Odd (orderOf x) := by
      obtain ⟨m, hm⟩ := hPp ⟨x, hx⟩
      have hdvd : orderOf x ∣ 3 ^ m := by
        apply orderOf_dvd_of_pow_eq_one
        simpa using congrArg (fun y : ↥P => (y : G)) hm
      exact (Odd.pow (by decide : Odd 3)).of_dvd_nat hdvd
    exact normalizer_odd_inner hL.2.2 e hX (hnorm hx) hodd
  exact excluded_numerics h.one_le hk hcardP (card_inf_centralizer_le h hL hnorm hzne)
    (card_le_of_inner hPp hin hk2')
    (card_sylow_of_cover (comp_isSylowOf_inf h.sylow hL) hz3 hk1' hk2')
    (Subgroup.card_le_of_le (inf_le_left : P ⊓ L ≤ P))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
