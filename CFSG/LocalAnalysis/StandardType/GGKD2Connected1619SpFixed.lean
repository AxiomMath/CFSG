module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
public import CFSG.LocalAnalysis.StandardType.GGK1ADvd
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
  (card_statedSp_one_of_card_two card_statedSp_two_of_card_two isQuasisimple_statedSp_of_not_small
    subsingleton_statedSp_zero)

private theorem ltrspb2_exists_mul_of_mem_sup_of_commute {G : Type*} [Group G]
    {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have hba : b * a' = a' * b := (hcomm a' ha' b hb).symm
        calc (a * b) * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hba]
          _ = (a * a') * (b * b') := by group
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hba : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ :=
          (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := hba }
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBP : B ≤ P := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact sup_le hAP hBP hx

theorem spFixedBlock_action {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {x : ↥(StatedSp m K)} {A₁ A₂ : Subgroup ↥(StatedSp m K)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hY : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set ↥(StatedSp m K)))
    {s : ℕ} (e₁ : A₁ ≃* ↥(StatedSp s K)) {C : Subgroup ↥(StatedSp m K)}
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({x} : Set ↥(StatedSp m K))))
    (hle : C ≤ A₁) (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C))
    {y : ↥(StatedSp m K)} (hxy : x * y = y * x) (hyC : ∀ c ∈ C, MulAut.conj y c ∈ C) :
    QuotientInner C (MulAut.conj y) := by
  classical
  have h7 : 7 ∣ Nat.card (StatedSp s K) := by
    have h7proj : 7 ∣ Nat.card (↥C ⧸ Subgroup.center ↥C) := by
      unfold GGHasLabel at hlab
      dsimp only [CFSG.StandardType.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeLinear] at hlab
      obtain ⟨F, hFfield, hFfinite, hFcard, hQF⟩ := hlab
      letI : Field F := hFfield
      letI : Finite F := hFfinite
      obtain ⟨e₀⟩ := hQF
      rw [Nat.card_congr e₀.toEquiv]
      rw [CFSG.Assembly.largeEvenProj_eq_statedProj,
        CFSG.Assembly.largeEvenSLGroup_eq_statedSL 2]
      refine CFSG.StandardType.prime_dvd_card_statedProj_statedSL (p := 7) (a := 2)
        Nat.prime_seven (by norm_num) (by norm_num) ?_ ?_
      · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        letI : Fintype F := Fintype.ofFinite F
        have hchar : CharP F 2 :=
          charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
            rw [Fintype.card_eq_nat_card, hFcard])
        exact CharP.cast_eq_zero F 2
      · rw [hFcard]
        norm_num
    have h7C : 7 ∣ Nat.card ↥C :=
      h7proj.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥C))
    have h7A : 7 ∣ Nat.card ↥A₁ := by
      have hcard : Nat.card ↥C = Nat.card ↥(C.subgroupOf A₁) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).symm.toEquiv
      rw [hcard] at h7C
      exact h7C.trans (Subgroup.card_subgroup_dvd_card (C.subgroupOf A₁))
    have hcardA : Nat.card ↥A₁ = Nat.card (StatedSp s K) :=
      Nat.card_congr e₁.toEquiv
    rwa [hcardA] at h7A
  have h1 : ¬ (s = 1 ∧ Nat.card K = 2) := by
    rintro ⟨rfl, hK2⟩
    rw [card_statedSp_one_of_card_two
      (K := K) hK2] at h7
    norm_num at h7
  have h2 : ¬ (s = 2 ∧ Nat.card K = 2) := by
    rintro ⟨rfl, hK2⟩
    rw [card_statedSp_two_of_card_two
      (K := K) hK2] at h7
    norm_num at h7
  have hs : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    subst hs0
    haveI : Subsingleton (StatedSp 0 K) :=
      subsingleton_statedSp_zero
        (K := K)
    have hcard0 : Nat.card (StatedSp 0 K) = 1 := by
      haveI : Unique ↥(StatedSp 0 K) := ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
      exact Nat.card_unique
    rw [hcard0] at h7
    norm_num at h7
  have hQo : CFSG.Open.IsQuasisimple ↥(StatedSp s K) :=
    isQuasisimple_statedSp_of_not_small
      hs h1 h2
  have hQoA₁ : CFSG.Open.IsQuasisimple ↥A₁ :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e₁ hQo
  have hcompA₁ : CFSG.Assembly.IsComponentOf C A₁ :=
    hC.of_le_of_le hle (le_sup_left.trans hY.le)
  have hsub_ml : (C.subgroupOf A₁).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).1 hcompA₁.2.1
  have hsub_open : CFSG.Open.IsSubnormal (C.subgroupOf A₁) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib hsub_ml
  have hqs_sub : CFSG.Open.IsQuasisimple ↥(C.subgroupOf A₁) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hcompA₁.2.2
  have htop : C.subgroupOf A₁ = ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.eq_top_of_isComponentOf_of_isQuasisimple hQoA₁
      ⟨le_top, hsub_open, hqs_sub⟩
  have hCA : A₁ ≤ C := Subgroup.subgroupOf_eq_top.1 htop
  have hyY : y ∈ A₁ ⊔ A₂ := by
    rw [hY]
    exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hxy)
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ A₁, ∃ b ∈ A₂, y = a * b :=
    ltrspb2_exists_mul_of_mem_sup_of_commute hcomm hyY
  have haC : a ∈ C := hCA ha
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥C) ⟨a, haC⟩, ?_⟩
  intro c c' hcc'
  have hbc : b * (c : ↥(StatedSp m K)) * b⁻¹ = (c : ↥(StatedSp m K)) := by
    rw [(hcomm (c : ↥(StatedSp m K)) (hle c.2) b hb).symm]
    group
  have hconj : MulAut.conj y (c : ↥(StatedSp m K)) =
      a * (c : ↥(StatedSp m K)) * a⁻¹ := by
    rw [hab, MulAut.conj_apply]
    calc (a * b) * (c : ↥(StatedSp m K)) * (a * b)⁻¹
        = a * (b * (c : ↥(StatedSp m K)) * b⁻¹) * a⁻¹ := by group
      _ = a * (c : ↥(StatedSp m K)) * a⁻¹ := by rw [hbc]
  have hconj_eq : (c' : ↥(StatedSp m K)) = a * (c : ↥(StatedSp m K)) * a⁻¹ := by
    rw [← hcc', hconj]
  have hCe : (⟨c', c'.2⟩ : ↥C) = ⟨a, haC⟩ * c * ⟨a, haC⟩⁻¹ := by
    apply Subtype.ext
    simpa using hconj_eq
  have hq := congrArg (QuotientGroup.mk' (Subgroup.center ↥C)) hCe
  change QuotientGroup.mk' (Subgroup.center ↥C) c' =
      QuotientGroup.mk' (Subgroup.center ↥C) ⟨a, haC⟩ *
        QuotientGroup.mk' (Subgroup.center ↥C) c *
        (QuotientGroup.mk' (Subgroup.center ↥C) ⟨a, haC⟩)⁻¹
  simpa only [map_mul, map_inv] using hq

end S2MathAs3_1619Final

end
