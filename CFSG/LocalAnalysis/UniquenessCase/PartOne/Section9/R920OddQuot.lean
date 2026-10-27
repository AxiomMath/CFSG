module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem opp_le (p : ℕ) (Y : Subgroup G) : Opp p Y ≤ Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

theorem mem_opp_of_orderOf {p : ℕ} {Y : Subgroup G} {x : G} (hx : x ∈ Y)
    (hk : ∃ k : ℕ, orderOf x = p ^ k) : x ∈ Opp p Y :=
  Subgroup.subset_closure ⟨hx, hk⟩

theorem opp_conj_mem {p : ℕ} {Y : Subgroup G} {w : G} (hw : w ∈ Y) {x : G}
    (hx : x ∈ Opp p Y) : w * x * w⁻¹ ∈ Opp p Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨Y.mul_mem (Y.mul_mem hw hx.1) (Y.inv_mem hw), ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    exact ⟨k, by rw [← hk]; exact MulEquiv.orderOf_eq (MulAut.conj w) x⟩
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [show w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

theorem le_normalizer_opp (p : ℕ) (Y : Subgroup G) : Y ≤ normalizer (Opp p Y : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => opp_conj_mem hw hx, fun hx => ?_⟩
  have := opp_conj_mem (Y.inv_mem hw) hx
  simpa [mul_assoc] using this

theorem opp_opp (p : ℕ) (Y : Subgroup G) : Opp p (Opp p Y) = Opp p Y := by
  refine le_antisymm (opp_le p _) ?_
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  rw [Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem exists_three_elem_mk_ne_one {Y : Subgroup G} {N : Subgroup ↥Y} [N.Normal]
    (h3 : 3 ∣ Nat.card (↥Y ⧸ N)) :
    ∃ y : ↥Y, (∃ k : ℕ, orderOf y = 3 ^ k) ∧ (y : ↥Y ⧸ N) ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y ⧸ N) 3 h3
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective b
  have hpos : 0 < orderOf y₀ := orderOf_pos y₀
  obtain ⟨e, m, hm3, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 3 (by norm_num)
  refine ⟨y₀ ^ m, ⟨e, ?_⟩, ?_⟩
  · have hm : m ∣ orderOf y₀ := ⟨3 ^ e, by rw [hem]; ring⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hem
      omega
    rw [orderOf_pow_of_dvd hm0 hm, hem]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  · intro h1
    have : (y₀ : ↥Y ⧸ N) ^ m = 1 := by rw [← QuotientGroup.mk_pow]; exact h1
    exact hm3 (hb ▸ orderOf_dvd_of_pow_eq_one this)

theorem surjective_mk_inclusion_of_sup {L Y : Subgroup G} (hYL : Y ≤ L)
    (hL : L = Y ⊔ pCoreOf 2 L) :
    Function.Surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hYL)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYN : Y ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hYL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hl : (l : G) ∈ (Y : Set G) * (pCoreOf 2 L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y _ hYN, ← hL]
    exact l.2
  obtain ⟨a, ha, b, hb, hab⟩ := hl
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff]
  have e : (((Subgroup.inclusion hYL ⟨a, ha⟩)⁻¹ * l : ↥L) : G) = b := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hab]
    group
  rw [e]
  exact hb

theorem pCoreOf_le_pCoreOf_of_sup {L Y : Subgroup G} (hYL : Y ≤ L) (hL : L = Y ⊔ pCoreOf 2 L) :
    pCoreOf 2 Y ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥Y →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hYL) with hφ
  have hsurj : Function.Surjective φ := surjective_mk_inclusion_of_sup hYL hL
  have hn : ((CFSG.pCore 2 ↥Y).map φ).Normal := CFSG.pCore_normal.map φ hsurj
  have hp : IsPGroup 2 ((CFSG.pCore 2 ↥Y).map φ) := CFSG.pCore_isPGroup.map φ
  have hle : (CFSG.pCore 2 ↥Y).map φ ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    le_sSup ⟨hn, hp⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
  intro x hx
  have hxY : (⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 Y hx⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y :=
    (CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff _).2 hx
  have h1 : φ ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 Y hx⟩ = 1 :=
    Subgroup.mem_bot.1 (hle (Subgroup.mem_map_of_mem φ hxY))
  rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff] at h1
  exact h1

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem isSimpleGroup_bar2 (S : SliceCore D L D₃ Y H) : IsSimpleGroup (Bar2 Y) :=
  S.facts.simple

theorem three_dvd_card_bar2 (S : SliceCore D L D₃ Y H) : 3 ∣ Nat.card (Bar2 Y) :=
  S.facts.three_dvd

theorem Y_eq_opp_sup (S : SliceCore D L D₃ Y H) : Y = Opp 3 Y ⊔ pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (Bar2 Y) := S.isSimpleGroup_bar2
  set Q : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hQdef
  haveI hQ : Q.Normal := CFSG.pCore_normal
  set N : Subgroup ↥Y := (Opp 3 Y).subgroupOf Y with hNdef
  haveI hN : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (opp_le 3 Y)).2 (le_normalizer_opp 3 Y)
  set π : ↥Y →* Bar2 Y := QuotientGroup.mk' Q with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Q
  haveI : (N.map π).Normal := hN.map π hsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  · exfalso
    obtain ⟨y, ⟨k, hk⟩, hy1⟩ := exists_three_elem_mk_ne_one (N := Q) S.three_dvd_card_bar2
    have hyN : y ∈ N := by
      rw [hNdef, Subgroup.mem_subgroupOf]
      exact mem_opp_of_orderOf y.2 ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
    have hmem : π y ∈ N.map π := Subgroup.mem_map_of_mem π hyN
    rw [hbot] at hmem
    exact hy1 (Subgroup.mem_bot.1 hmem)
  · refine le_antisymm ?_ (sup_le (opp_le 3 Y) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
    intro y hy
    have hmem : π ⟨y, hy⟩ ∈ N.map π := by rw [htop]; trivial
    obtain ⟨n, hn, hnπ⟩ := Subgroup.mem_map.1 hmem
    have h1 : (n : G)⁻¹ * y ∈ pCoreOf 2 Y := by
      have h2 : (n⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ Q := by
        rw [← QuotientGroup.eq]
        exact hnπ
      exact (CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff _).1 h2
    have hn' : (n : G) ∈ Opp 3 Y := (Subgroup.mem_subgroupOf.1 hn)
    have : y = (n : G) * ((n : G)⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hn' h1

theorem L_eq_opp_sup (S : SliceCore D L D₃ Y H) : L = Opp 3 Y ⊔ pCoreOf 2 L := by
  have hY := S.Y_eq_opp_sup
  have hO := pCoreOf_le_pCoreOf_of_sup S.yl S.L_eq
  refine le_antisymm ?_ (sup_le ((opp_le 3 Y).trans S.yl) (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  have hYle : Y ≤ Opp 3 Y ⊔ pCoreOf 2 L := by
    calc Y = Opp 3 Y ⊔ pCoreOf 2 Y := hY
      _ ≤ Opp 3 Y ⊔ pCoreOf 2 L := sup_le_sup_left hO _
  have hle : Y ⊔ pCoreOf 2 L ≤ Opp 3 Y ⊔ pCoreOf 2 L := sup_le hYle le_sup_right
  intro l hl
  rw [S.L_eq] at hl
  exact hle hl

theorem opp_le_L (S : SliceCore D L D₃ Y H) : Opp 3 Y ≤ L := (opp_le 3 Y).trans S.yl

theorem opp_le_M (S : SliceCore D L D₃ Y H) : Opp 3 Y ≤ D.M := (opp_le 3 Y).trans S.Y_le_M

theorem nonempty_bar2_opp_equiv (S : SliceCore D L D₃ Y H) :
    Nonempty (Bar2 Y ≃* Bar2 (Opp 3 Y)) :=
  CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv (opp_le 3 Y)
    S.Y_eq_opp_sup

theorem nonempty_bar2_L_opp_equiv (S : SliceCore D L D₃ Y H) :
    Nonempty (Bar2 L ≃* Bar2 (Opp 3 Y)) :=
  CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv S.opp_le_L
    S.L_eq_opp_sup

theorem nonempty_bar2_L_equiv (S : SliceCore D L D₃ Y H) : Nonempty (Bar2 L ≃* Bar2 Y) :=
  CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv S.yl S.L_eq

theorem facts_opp (S : SliceCore D L D₃ Y H) : Shape919 (Bar2 (Opp 3 Y)) := by
  obtain ⟨e⟩ := S.nonempty_bar2_opp_equiv
  exact S.facts.of_mulEquiv e

theorem facts_L (S : SliceCore D L D₃ Y H) : Shape919 (Bar2 L) := by
  obtain ⟨e⟩ := S.nonempty_bar2_L_equiv
  exact S.facts.of_mulEquiv e.symm

end SliceCore

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem shape_opp (S : Slice D L D₃ Y H q) : IsL2Odd (Bar2 (Opp 3 Y)) q := by
  obtain ⟨e⟩ := S.nonempty_bar2_opp_equiv
  exact CFSG.Blueprint.LieModel.of_mulEquiv e S.shape

theorem shape_L (S : Slice D L D₃ Y H q) : IsL2Odd (Bar2 L) q := by
  obtain ⟨e⟩ := S.nonempty_bar2_L_equiv
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm S.shape

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
