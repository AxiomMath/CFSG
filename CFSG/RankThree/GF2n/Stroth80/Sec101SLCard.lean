module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Transv
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Dim
public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec10Hyp.Rt_ne_LB_of_SLMNat (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} {m : ℕ} (hm2 : 2 ≤ m) (hm : SLMNat hc t m) :
    Rt M (LB M Q B) t ≠ LB M Q B := by
  intro hRL
  have hp : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 H.width H.n_gt H.noA2 H.gen
  obtain ⟨K, fK, finK, hK, φ, hφr, -, -⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpR : IsPGroup 2 ↥(Rt M (LB M Q B) t) := hRL.symm ▸ hp
  have hpr : IsPGroup 2 ↥(StatedSL m K) := by
    rw [← hφr]
    exact hpR.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  have hq : CFSG.IsQuasisimple ↥(StatedSL m K) :=
    statedSL_quasisimple_of_card m K hm2 (hK ▸ hc.hyp.q4)
  haveI : Group.IsPerfect ↥(StatedSL m K) := hq.1
  haveI : Nontrivial (↥(StatedSL m K) ⧸ Subgroup.center ↥(StatedSL m K)) := hq.2.1.toNontrivial
  have hnt : Nontrivial ↥(StatedSL m K) :=
    (QuotientGroup.mk_surjective :
      Function.Surjective (QuotientGroup.mk : ↥(StatedSL m K) →
        ↥(StatedSL m K) ⧸ Subgroup.center ↥(StatedSL m K))).nontrivial
  haveI : Nontrivial ↥(StatedSL m K) := hnt
  exact Group.IsPerfect.not_isNilpotent ↥(StatedSL m K) hpr.isNilpotent

theorem Sec10Hyp.card_LB_le_mul_card_LB_inf_CN_of_SL (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    {m : ℕ} (hm2 : 2 ≤ m) (hm : SLMNat hc t m) :
    Nat.card ↥(LB M Q B) ≤ Nat.card Z ^ (m - 1) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
  have h5 : Sec5Hyp hc n t := H.toSec5 ht htQ
  have hSL : SLNat hc t := SLMNat.toSLNat hm hm2
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t h5 hSL
  obtain ⟨K, fK, finK, hchar, hKcard, m', hm'2, φ, hker, hSA, -, -, ⟨u, hu, hel⟩, -⟩ :=
    stroth310SLTransv_of_34 h34 G M Q Z B hc n t h5
      (H.Rt_ne_LB_of_SLMNat h34 hm2 hm) hVQB
  have hm' : m' = m := by
    have hq : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
    have hpow : Nat.card Z ^ (m' + 1) = Nat.card Z ^ (m + 1) :=
      (card_Vt_of_sectionAct (t := t) (φ := φ) hKcard hSA).symm.trans (SLMNat.card_Vt hm)
    have := Nat.pow_right_injective hq hpow
    omega
  have hXle : Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) ≤
      Nat.card K ^ (m' - 1) := by
    refine card_le_pow_of_elations
      (X := ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) (u := u) hu ?_ ?_
    · rintro g ⟨l, hl, rfl⟩ x
      exact hel l (Subgroup.mem_subgroupOf.mp hl) x
    · rintro g ⟨l, hl, rfl⟩
      have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
      have h2CN : (l : G) ^ 2 ∈ hc.CN t :=
        Ctx.Q_le_CN hc ht (hc.sq_mem_Q_of_mem_LB hlL)
      have hll : l * l ∈ φ.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using h2CN)
      show φ l * φ l = 1
      rw [← map_mul]
      exact hll
  rw [hKcard] at hXle
  have hmap := card_inf_mul_card_map (le_Rt (LB M Q B) ht) φ hker
  rw [← hmap, ← hm']
  calc Nat.card ↥(LB M Q B ⊓ hc.CN t) *
        Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ)
      ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (m' - 1) :=
        Nat.mul_le_mul_left _ hXle
    _ = Nat.card Z ^ (m' - 1) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := mul_comm _ _

theorem Sec10Hyp.pow_le_card_bar_LB_inf_CN [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) {m : ℕ} (hm2 : 2 ≤ m) (hm : SLMNat hc t m) :
    Nat.card Z ^ m ≤ Nat.card ↥(bar M Q (LB M Q B ⊓ hc.CN t)) := by
  have hΛ := hc.card_bar_LB_of_34 h34 H.width H.n_gt H.noA2 H.gen
  have hL := bar_card_mul_card_of_le (M := M) (S := LB M Q B) sec39_Q_le_LB hc.LB_le_M
  have hC := bar_card_mul_card_of_le (M := M) (S := LB M Q B ⊓ hc.CN t)
    (le_inf sec39_Q_le_LB (Ctx.Q_le_CN hc ht)) (inf_le_left.trans hc.LB_le_M)
  have hle := H.card_LB_le_mul_card_LB_inf_CN_of_SL h34 ht htQ hm2 hm
  rw [← hL, ← hC, ← mul_assoc] at hle
  have hbar : Nat.card (bar M Q (LB M Q B)) ≤
      Nat.card Z ^ (m - 1) * Nat.card ↥(bar M Q (LB M Q B ⊓ hc.CN t)) :=
    Nat.le_of_mul_le_mul_right hle Nat.card_pos
  have hdim := stroth6SLDim_of_34 h34 G M Q Z B hc n t (H.toSec5 ht htQ) m hm2 (Or.inl hm)
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hsplit : Nat.card Z ^ (m - 1) * Nat.card Z ^ m ≤
      Nat.card Z ^ (m - 1) * Nat.card ↥(bar M Q (LB M Q B ⊓ hc.CN t)) := by
    calc Nat.card Z ^ (m - 1) * Nat.card Z ^ m
        = Nat.card Z ^ ((m - 1) + m) := (pow_add _ _ _).symm
      _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right hq (by omega)
      _ = Nat.card (bar M Q (LB M Q B)) := hΛ.symm
      _ ≤ _ := hbar
  exact Nat.le_of_mul_le_mul_left hsplit (pow_pos hq (m - 1))

theorem Ctx.exists_bar_hom_of_SLMNat [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {m : ℕ} (hm : SLMNat hc t m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
      ∃ π : ↥(bar M Q (Rt M (LB M Q B) t)) →* ↥(StatedSL m K), Function.Surjective π ∧
        ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t) := by
  obtain ⟨K, fK, finK, hK, φ, hφr, hφk, -⟩ := hm
  obtain ⟨π, hπ, hker⟩ := hc.exists_bar_hom ht φ hφr hφk
  exact ⟨K, fK, finK, hK, π, hπ, hker⟩

theorem Sec10Hyp.exists_SLMNat_of_le_bar_Rt [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    {C : Subgroup (Mbar M Q)} (hCR : C ≤ bar M Q (Rt M (LB M Q B) t))
    (hC : ∃ a b : ↥C, a * b ≠ b * a) : ∃ m, 2 ≤ m ∧ SLMNat hc t m := by
  rcases H.alt t ht htQ with hR | hsl
  · exfalso
    obtain ⟨a, b, hab⟩ := hC
    rw [hR] at hCR
    exact hab (Subtype.ext ((hc.swapHyp H.width H.n_gt H.noA2).comm _ (hCR a.2) _ (hCR b.2)))
  · exact hsl.exists_SLMNat

end CFSG.RankThree.GF2n.Stroth80
