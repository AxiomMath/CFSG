module

public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGInnLocal

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_ne_one_of_dvd {p : ℕ} (hp : p.Prime) {S J : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (J : Set G)) (hSp : IsPGroup p S)
    (hSC : ∀ g ∈ Subgroup.centralizer (S : Set G), g ^ p = 1 → g ∈ S)
    (hpJ : p ∣ Nat.card J) : ∃ b ∈ S ⊓ J, b ≠ 1 ∧ b ^ p = 1 := by
  have := Fact.mk hp
  let _ : MulDistribMulAction ↥S ↥J :=
    { smul := fun s j => ⟨(s : G) * j * (s : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hSN s.2) j).mp j.2⟩
      one_smul := fun j => Subtype.ext (by
        change (1 : G) * j * (1 : G)⁻¹ = j
        group)
      mul_smul := fun a b j => Subtype.ext (by
        change ((a : G) * b) * j * ((a : G) * b)⁻¹ = a * (b * j * (b : G)⁻¹) * (a : G)⁻¹
        group)
      smul_mul := fun s j k => Subtype.ext (by
        change (s : G) * (j * k) * (s : G)⁻¹ = (s * j * (s : G)⁻¹) * (s * k * (s : G)⁻¹)
        group)
      smul_one := fun s => Subtype.ext (by
        change (s : G) * 1 * (s : G)⁻¹ = 1
        group) }
  have hmod := hSp.card_modEq_card_fixedPoints (↥J)
  have hdvd : p ∣ Nat.card (FixedPoints.subgroup ↥S ↥J) := by
    have hc : Nat.card ↑(MulAction.fixedPoints ↥S ↥J) =
        Nat.card (FixedPoints.subgroup ↥S ↥J) := rfl
    rw [← hc]
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpJ))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hfix := (FixedPoints.mem_subgroup ↥S ↥J (c : ↥J)).mp c.2
  have hcp : ((c : ↥J) : G) ^ p = 1 := by
    have h1 : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
    have h2 := congrArg (fun z : FixedPoints.subgroup ↥S ↥J => ((z : ↥J) : G)) h1
    simpa using h2
  have hc1 : ((c : ↥J) : G) ≠ 1 := by
    intro h1
    have : c = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hc
    exact hp.one_lt.ne hc
  have hcC : ((c : ↥J) : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := congrArg Subtype.val (hfix ⟨s, hs⟩)
    change s * ((c : ↥J) : G) * s⁻¹ = ((c : ↥J) : G) at h1
    calc s * ((c : ↥J) : G) = s * ((c : ↥J) : G) * s⁻¹ * s := by group
      _ = ((c : ↥J) : G) * s := by rw [h1]
  exact ⟨((c : ↥J) : G), ⟨hSC _ hcC hcp, (c : ↥J).2⟩, hc1, hcp⟩

theorem centralizer_le_normalizer_stdSub {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hDJ : LargeEvenStdSubPre p B x L D J) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have hCx : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hS.2.1)
  have hCD : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hDJ.1
  rw [hDJ.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
    (mem_normalizer_inf_centralizer (mem_normalizer_of_sstar hS hnc (hCx hg)) (hCD hg))

theorem exists_mem_bstar_inf_of_not_dvd {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hpJ : p ∣ Nat.card J)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) :
    ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBsN : Bs ≤ Subgroup.normalizer (J : Set G) :=
    hcfg.2.1.le_centralizer.trans (centralizer_le_normalizer_stdSub hS hnc hcfg.2.2.1)
  have hBsp : IsPGroup p Bs := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hcfg.2.1.2.1.2 g g.2)⟩
  obtain ⟨b, ⟨hbBs, hbJ⟩, hb1, hbp⟩ :=
    exists_mem_inf_ne_one_of_dvd hp hBsN hBsp hcfg.2.1.2.2.2 hpJ
  refine ⟨b, ⟨hbBs, hbJ⟩, fun hbC => hZ ?_⟩
  have hcen : (⟨b, hbJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hbC) j j.2)
  have hord : orderOf (⟨⟨b, hbJ⟩, hcen⟩ : Subgroup.center ↥J) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hbp hb1
  exact hord ▸ orderOf_dvd_natCard _

@[expose] def GGStdSubOrderInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → LargeEvenStdSub p B x L D J → p ∣ Nat.card J

@[expose] def GGStdSubCenterMeetInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → p ∣ Nat.card (Subgroup.center J) →
      ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)

theorem ggStdSubBstarMeetInput_of_center (ha₀ : GGLNoncyclicInput) (hord : GGStdSubOrderInput)
    (hcen : GGStdSubCenterMeetInput) : GGStdSubBstarMeetInput := by
  intro G _ _ p B Bs x L D J hcfg
  by_cases hZ : p ∣ Nat.card (Subgroup.center J)
  · exact hcen G p B Bs x L D J hcfg hZ
  · exact exists_mem_bstar_inf_of_not_dvd hcfg (ha₀ G p B x L hcfg.1)
      (hord G p B x L D J hcfg.1 hcfg.2.2) hZ

theorem inf_centralizer_le_of_twoSubgroup {p : ℕ} (hp : p.Prime) {B Bs J T : Subgroup G}
    (hBmax : LargeEvenIsBmax p B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian p Bs) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ B := by
  rintro e ⟨heBs, heJ⟩
  have hEBs : B ⊔ Subgroup.zpowers e ≤ Bs := sup_le hBBs (Subgroup.zpowers_le.mpr heBs)
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers e) := TableB.isElemAbelian_mono hBs hEBs
  have heT : e ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hTJ heJ)
  have hET : B ⊔ Subgroup.zpowers e ≤ Subgroup.normalizer (T : Set G) :=
    sup_le hBT (Subgroup.zpowers_le.mpr heT)
  have hcard := TableB.card_le_of_twoLocal hp ⟨T, hT, hT2, rfl⟩ hET hE
  rw [← hBmax.2.1] at hcard
  have hBE : B = B ⊔ Subgroup.zpowers e := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [hBE]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)

theorem ggStdSubBstarCentralizer_of_twoSubgroup {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
      B ≤ Subgroup.normalizer (T : Set G)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  obtain ⟨T, hT1, hT2, hTJ, hBT⟩ := hT
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hle := inf_centralizer_le_of_twoSubgroup hp hcfg.1.2.2.2.2.2.2.1.1 hcfg.2.1.1
    hcfg.2.1.2.1 hT1 hT2 hTJ hBT
  intro e he
  rw [hcfg.2.2.1.2.2.2.2.2.2]
  exact ⟨hle he, he.2⟩

theorem ggStdSubBstarCentralizer_of_ggBeta {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hBN : B ≤ Subgroup.normalizer (J : Set G))
    {R : Type} [Group R] (θ : J ⧸ Subgroup.center J ≃* R)
    (h : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ (ggBeta J θ hBN).range, ∀ u ∈ U, a u ∈ U) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  obtain ⟨U, hUJ, hU1, hU2, hBU⟩ := exists_two_subgroup_of_ggBeta hBN θ h
  exact ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨U, hU1, hU2, hUJ, hBU⟩

end CFSG.StandardType

end
