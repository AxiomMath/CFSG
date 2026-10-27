module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section M1Fitting

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem m1Fit_bar_conj_mem [(Q.subgroupOf M).Normal] {L A : Subgroup G}
    (hnorm : ∀ s ∈ L, conjSubgroup s A = A) {g n : Mbar M Q}
    (hg : g ∈ bar M Q L) (hn : n ∈ bar M Q A) : g * n * g⁻¹ ∈ bar M Q A := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
  have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
  have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
  have hy' : (y : G) ∈ conjSubgroup (x : G)⁻¹ A := by
    rw [hnorm _ (L.inv_mem hxL)]
    exact hyA
  rw [mem_conjSubgroup, inv_inv] at hy'
  have hmem : x * y * x⁻¹ ∈ A.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hy'
  have e : (QuotientGroup.mk' (Q.subgroupOf M)) (x * y * x⁻¹) =
      QuotientGroup.mk' (Q.subgroupOf M) x * QuotientGroup.mk' (Q.subgroupOf M) y *
        (QuotientGroup.mk' (Q.subgroupOf M) x)⁻¹ := by
    simp [map_mul, map_inv]
  rw [← e]
  exact Subgroup.mem_map_of_mem _ hmem

private theorem m1Fit_bar_subgroupOf_normal [(Q.subgroupOf M).Normal] {L A : Subgroup G}
    (hnorm : ∀ s ∈ L, conjSubgroup s A = A) :
    ((bar M Q A).subgroupOf (bar M Q L)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := m1Fit_bar_conj_mem hnorm g.2 hn
  simpa using h

private theorem m1Fit_le_normalizer [(Q.subgroupOf M).Normal] {L A : Subgroup G}
    (hnorm : ∀ s ∈ L, conjSubgroup s A = A) {g : Mbar M Q} (hg : g ∈ bar M Q L) :
    g ∈ Subgroup.normalizer ((bar M Q A : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact m1Fit_bar_conj_mem hnorm hg hn
  · intro hn
    have h := m1Fit_bar_conj_mem hnorm (Subgroup.inv_mem _ hg) hn
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rw [e] at h
    exact h

private theorem m1Fit_bar_mono {S T : Subgroup G} [(Q.subgroupOf M).Normal] (h : S ≤ T) :
    bar M Q S ≤ bar M Q T :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

private theorem m1Fit_pCore_bar_eq_one [(Q.subgroupOf M).Normal] {L : Subgroup G}
    (hN : (bar M Q L).Normal) (h0 : CFSG.pCore 2 (Mbar M Q) = ⊥)
    {y : ↥(bar M Q L)} (hy : y ∈ CFSG.pCore 2 ↥(bar M Q L)) : (y : Mbar M Q) = 1 := by
  haveI := hN
  have hp : IsPGroup 2 ((CFSG.pCore 2 ↥(bar M Q L)).map (bar M Q L).subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(bar M Q L))).map (bar M Q L).subtype
  have hle : (CFSG.pCore 2 ↥(bar M Q L)).map (bar M Q L).subtype ≤ CFSG.pCore 2 (Mbar M Q) :=
    le_sSup ⟨inferInstance, hp⟩
  rw [h0] at hle
  exact Subgroup.mem_bot.mp (hle ⟨y, hy, rfl⟩)

private theorem m1Fit_odd_card {X : Type} [Group X] [Finite X] (S : Subgroup X) [S.Normal]
    (hnil : Group.IsNilpotent ↥S) (hcore : ∀ y ∈ CFSG.pCore 2 X, y = 1) :
    Odd (Nat.card ↥S) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hzp
  have hmem : S.subtype x ∈ CFSG.pCore 2 X :=
    Sylow.map_le_pCore (G := X) inferInstance hnil 2 P
      (Subgroup.mem_map_of_mem S.subtype (hP (Subgroup.mem_zpowers x)))
  have h1 : (S.subtype x : X) = 1 := hcore _ hmem
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

private theorem m1Fit_isNilpotent_bar [(Q.subgroupOf M).Normal] {L A : Subgroup G}
    (hAM : A ≤ M) (hAL : A ≤ L) [(Q.subgroupOf A).Normal]
    (hnil : Group.IsNilpotent (↥A ⧸ Q.subgroupOf A)) :
    Group.IsNilpotent ↥((bar M Q A).subgroupOf (bar M Q L)) := by
  let f₁ : ↥A →* Mbar M Q := (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hAM)
  have hf₁L : ∀ a : ↥A, f₁ a ∈ bar M Q L := fun a =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hAL a.2))
  let f₂ : ↥A →* ↥(bar M Q L) := f₁.codRestrict (bar M Q L) hf₁L
  have hf₂A : ∀ a : ↥A, f₂ a ∈ (bar M Q A).subgroupOf (bar M Q L) := fun a =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2))
  let f₃ : ↥A →* ↥((bar M Q A).subgroupOf (bar M Q L)) := f₂.codRestrict _ hf₂A
  have hker : Q.subgroupOf A ≤ f₃.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx))
  let F : (↥A ⧸ Q.subgroupOf A) →* ↥((bar M Q A).subgroupOf (bar M Q L)) :=
    QuotientGroup.lift (Q.subgroupOf A) f₃ hker
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp y.2)
    refine ⟨QuotientGroup.mk' (Q.subgroupOf A) ⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hmy
  haveI := hnil
  exact Group.nilpotent_of_surjective F hF

theorem m1FittingTrivial_of (h44 : Stroth44Statement) : M1FittingTrivialStatement := by
  intro G _ _ M Q Z B t hH A hQA hAL hnorm hnil
  have hc : Ctx M Q Z B := hH.ctx
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨hAn, hnilA⟩ := hnil
  haveI := hAn
  have hLM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.LB_le_M
  have hAM : A ≤ M := hAL.trans hLM
  have hĀL : bar M Q A ≤ bar M Q (Lgen M (LB M Q B)) := m1Fit_bar_mono hAL
  have hĀH : bar M Q A ≤ bar M Q (H0 M Z) := m1Fit_bar_mono (hAL.trans (Lgen_le_H0 hc))
  have hLBL : bar M Q (LB M Q B) ≤ bar M Q (Lgen M (LB M Q B)) :=
    m1Fit_bar_mono (le_Lgen _)
  haveI := hc.normal_bar_Lgen
  have hodd : Odd (Nat.card ↥(bar M Q A)) := by
    haveI : ((bar M Q A).subgroupOf (bar M Q (Lgen M (LB M Q B)))).Normal :=
      m1Fit_bar_subgroupOf_normal hnorm
    have hcore : ∀ y ∈ CFSG.pCore 2 ↥(bar M Q (Lgen M (LB M Q B))), y = 1 := fun y hy =>
      Subtype.ext (m1Fit_pCore_bar_eq_one hc.normal_bar_Lgen hc.pCore_two_Mbar hy)
    have hcard := m1Fit_odd_card ((bar M Q A).subgroupOf (bar M Q (Lgen M (LB M Q B))))
      (m1Fit_isNilpotent_bar hAM hAL hnilA) hcore
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hĀL).toEquiv] at hcard
  have hbot : bar M Q A = ⊥ :=
    h44 G M Q Z B hc 4 hH.sec.width hH.sec.n_gt hH.sec.noA2 hH.sec.gen (bar M Q A) hĀH
      (fun _ hg => m1Fit_le_normalizer hnorm (hLBL hg)) hodd
  refine le_antisymm ?_ hQA
  intro a ha
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨a, hAM ha⟩ : ↥M) ∈ (⊥ : Subgroup (Mbar M Q)) := by
    rw [← hbot]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  have h2 := (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp h1)
  exact Subgroup.mem_subgroupOf.mp h2

end M1Fitting

end CFSG.RankThree.GF2n.Smith81.Smith23E1
