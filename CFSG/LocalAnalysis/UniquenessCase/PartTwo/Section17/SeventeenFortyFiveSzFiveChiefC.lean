module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveChiefB
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveConfig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace ChiefSetup

variable {D : Data G} {V₀ V : Subgroup G} (s : ChiefSetup D V₀ V)

section Data


section AlmostSimple

variable {r : ℕ} {S : Fin r → Subgroup s.Q}

section Checks

theorem im_inf_eq (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) (U W V : Subgroup s.Q)
    (hV : V ≤ s.NQ (S i₀))
    (hVC : V ⊓ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) = ⊥)
    (hU : U ≤ V) (hW : W ≤ V) :
    s.im (S i₀) U ⊓ s.im (S i₀) W = s.im (S i₀) (U ⊓ W) := by
  refine le_antisymm ?_ (le_inf (s.im_mono (S i₀) inf_le_left) (s.im_mono (S i₀) inf_le_right))
  intro z hz
  obtain ⟨hzU, hzW⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨u, hu, huz⟩ := (s.mem_im_iff (S i₀) (hU.trans hV)).mp hzU
  obtain ⟨v, hv, hvz⟩ := (s.mem_im_iff (S i₀) (hW.trans hV)).mp hzW
  have h1 : s.ψ (S i₀) ((⟨u, hV (hU hu)⟩ : ↥(s.NQ (S i₀))) *
      (⟨v, hV (hW hv)⟩ : ↥(s.NQ (S i₀)))⁻¹) = 1 := by
    rw [map_mul, map_inv, huz, hvz]
    simp
  have h2 : ((⟨u, hV (hU hu)⟩ : ↥(s.NQ (S i₀))) *
      (⟨v, hV (hW hv)⟩ : ↥(s.NQ (S i₀)))⁻¹) ∈ s.CN (S i₀) :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h3 : (u * v⁻¹) ∈ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) :=
    Subgroup.mem_subgroupOf.mp h2
  have h4 : u * v⁻¹ ∈ V ⊓ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) :=
    ⟨V.mul_mem (hU hu) (V.inv_mem (hW hv)), h3⟩
  rw [hVC, Subgroup.mem_bot] at h4
  have huv : u = v := by
    calc u = u * v⁻¹ * v := by group
      _ = v := by rw [h4, one_mul]
  have hmem : u ∈ U ⊓ W := ⟨hu, huv ▸ hv⟩
  exact (s.mem_im_iff (S i₀) (inf_le_left.trans (hU.trans hV))).mpr ⟨u, hmem, huz⟩

theorem im_bot (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) : s.im (S i₀) ⊥ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨u, hu, huz⟩ := (s.mem_im_iff (S i₀) bot_le).mp hz
  rw [Subgroup.mem_bot] at hu
  rw [Subgroup.mem_bot]
  subst hu
  rw [← huz]
  rfl

theorem A₁'_inf_A₂' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.A₁' hFac i₀ ⊓ s.A₂' hFac i₀ = ⊥ := by
  rw [A₁', A₂', s.im_inf_eq hFac i₀ (s.bar s.A₁) (s.bar s.A₂) (s.bar s.A)
    (s.bar_A_le_N hFac i₀) (s.bar_A_inf_centralizer_factor hFac i₀)
    (s.bar_mono s.A₁_le_A) (s.bar_mono s.A₂_le_A), s.bar_A₁_inf_bar_A₂, s.im_bot hFac i₀]

theorem A₁'_le_centralizer_A₂' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.A₁' hFac i₀ ≤ Subgroup.centralizer ((s.A₂' hFac i₀ : Subgroup (s.Xq (S i₀))) :
      Set (s.Xq (S i₀))) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨a, ha, haz⟩ := (s.mem_im_iff (S i₀) (s.bar_A₁_le_N hFac i₀)).mp hz
  obtain ⟨b, hb, hbw⟩ := (s.mem_im_iff (S i₀) (s.bar_A₂_le_N hFac i₀)).mp hw
  have hcomm : (⟨b, s.bar_A₂_le_N hFac i₀ hb⟩ : ↥(s.NQ (S i₀))) *
      ⟨a, s.bar_A₁_le_N hFac i₀ ha⟩ = ⟨a, s.bar_A₁_le_N hFac i₀ ha⟩ *
        ⟨b, s.bar_A₂_le_N hFac i₀ hb⟩ := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (s.bar_A₁_le_centralizer_bar_A₂ ha) b hb
  rw [← haz, ← hbw]
  show s.ψ (S i₀) ⟨b, _⟩ * s.ψ (S i₀) ⟨a, _⟩ = s.ψ (S i₀) ⟨a, _⟩ * s.ψ (S i₀) ⟨b, _⟩
  rw [← map_mul, ← map_mul, hcomm]

theorem B'_le_normalizer_A₁' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.B' hFac i₀ ≤ Subgroup.normalizer ((s.A₁' hFac i₀ : Subgroup (s.Xq (S i₀))) :
      Set (s.Xq (S i₀))) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  obtain ⟨β, hβ, hβb⟩ := (s.mem_im_iff (S i₀) (s.bar_B_le_N hFac i₀)).mp hb
  obtain ⟨α, hα, hαa⟩ := (s.mem_im_iff (S i₀) (s.bar_A₁_le_N hFac i₀)).mp ha
  have hconj : (s.ψ (S i₀)) ((⟨β, s.bar_B_le_N hFac i₀ hβ⟩ : ↥(s.NQ (S i₀))) *
      (⟨α, s.bar_A₁_le_N hFac i₀ hα⟩ : ↥(s.NQ (S i₀))) *
      (⟨β, s.bar_B_le_N hFac i₀ hβ⟩ : ↥(s.NQ (S i₀)))⁻¹) =
      s.ψ (S i₀) ⟨β, s.bar_B_le_N hFac i₀ hβ⟩ * s.ψ (S i₀) ⟨α, s.bar_A₁_le_N hFac i₀ hα⟩ *
        (s.ψ (S i₀) ⟨β, s.bar_B_le_N hFac i₀ hβ⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← hβb, ← hαa, ← hconj]
  refine (s.mem_im_iff (S i₀) (s.bar_A₁_le_N hFac i₀)).mpr ⟨_, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (s.bar_B_le_normalizer_bar_A₁ hβ) α).mp hα

theorem B'_le_normalizer_A₂' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.B' hFac i₀ ≤ Subgroup.normalizer ((s.A₂' hFac i₀ : Subgroup (s.Xq (S i₀))) :
      Set (s.Xq (S i₀))) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  obtain ⟨β, hβ, hβb⟩ := (s.mem_im_iff (S i₀) (s.bar_B_le_N hFac i₀)).mp hb
  obtain ⟨α, hα, hαa⟩ := (s.mem_im_iff (S i₀) (s.bar_A₂_le_N hFac i₀)).mp ha
  have hconj : (s.ψ (S i₀)) ((⟨β, s.bar_B_le_N hFac i₀ hβ⟩ : ↥(s.NQ (S i₀))) *
      (⟨α, s.bar_A₂_le_N hFac i₀ hα⟩ : ↥(s.NQ (S i₀))) *
      (⟨β, s.bar_B_le_N hFac i₀ hβ⟩ : ↥(s.NQ (S i₀)))⁻¹) =
      s.ψ (S i₀) ⟨β, s.bar_B_le_N hFac i₀ hβ⟩ * s.ψ (S i₀) ⟨α, s.bar_A₂_le_N hFac i₀ hα⟩ *
        (s.ψ (S i₀) ⟨β, s.bar_B_le_N hFac i₀ hβ⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← hβb, ← hαa, ← hconj]
  refine (s.mem_im_iff (S i₀) (s.bar_A₂_le_N hFac i₀)).mpr ⟨_, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (s.bar_B_le_normalizer_bar_A₂ hβ) α).mp hα

theorem Abar'_commutator_B' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    ⁅s.A₁' hFac i₀ ⊔ s.A₂' hFac i₀, s.B' hFac i₀⁆ =
      s.A₁' hFac i₀ ⊔ s.A₂' hFac i₀ := by
  rw [← s.Abar'_eq_sup hFac i₀]
  have hAB : s.im (S i₀) (⁅s.bar s.A, s.bar s.B⁆) = s.im (S i₀) (s.bar s.A) := by
    rw [s.bar_commutator]
  have hsub : (⁅s.bar s.A, s.bar s.B⁆).subgroupOf (s.NQ (S i₀)) =
      ⁅(s.bar s.A).subgroupOf (s.NQ (S i₀)), (s.bar s.B).subgroupOf (s.NQ (S i₀))⁆ :=
    (CFSG.GroupTheory.commutator_subgroupOf_eq (s.bar_A_le_N hFac i₀)
      (s.bar_B_le_N hFac i₀)).symm
  calc ⁅s.Abar' hFac i₀, s.B' hFac i₀⁆
      = ⁅s.im (S i₀) (s.bar s.A), s.im (S i₀) (s.bar s.B)⁆ := rfl
    _ = ((⁅s.bar s.A, s.bar s.B⁆).subgroupOf (s.NQ (S i₀))).map (s.ψ (S i₀)) := by
        rw [hsub, Subgroup.map_commutator]
        rfl
    _ = s.im (S i₀) (s.bar s.A) := by
        show s.im (S i₀) ⁅s.bar s.A, s.bar s.B⁆ = s.im (S i₀) (s.bar s.A)
        rw [s.bar_commutator]
    _ = s.Abar' hFac i₀ := rfl

theorem lines (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    (D' : Subgroup (s.Xq (S i₀)))
    (hD'A : D' ≤ s.A₁' hFac i₀ ⊔ s.A₂' hFac i₀)
    (hcard : Nat.card D' = 31)
    (hBD' : s.B' hFac i₀ ≤ Subgroup.normalizer (D' : Set (s.Xq (S i₀)))) :
    D' = s.A₁' hFac i₀ ∨ D' = s.A₂' hFac i₀ := by
  classical
  have hA' : s.A₁' hFac i₀ ⊔ s.A₂' hFac i₀ = s.im (S i₀) (s.bar s.A) :=
    (s.Abar'_eq_sup hFac i₀).symm
  obtain ⟨D, hDA, hDmap⟩ :=
    s.exists_preimage (S i₀) (s.bar_A_le_N hFac i₀) (hA' ▸ hD'A)
  have hDcard : Nat.card D = 31 := by
    rw [← hcard, ← hDmap, s.card_im (S i₀) (hDA.trans (s.bar_A_le_N hFac i₀))]
    refine le_antisymm ?_ bot_le
    exact le_trans (inf_le_inf_right _ hDA)
      (le_of_eq (s.bar_A_inf_centralizer_factor hFac i₀))
  have hBD : s.bar s.B ≤ Subgroup.normalizer (D : Set s.Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb d hd
    have hb' : s.ψ (S i₀) ⟨b, s.bar_B_le_N hFac i₀ hb⟩ ∈ s.B' hFac i₀ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
    have hd' : s.ψ (S i₀) ⟨d, (hDA.trans (s.bar_A_le_N hFac i₀)) hd⟩ ∈ D' := by
      rw [← hDmap]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hd)
    have h1 : s.ψ (S i₀) ⟨b, s.bar_B_le_N hFac i₀ hb⟩ *
        s.ψ (S i₀) ⟨d, (hDA.trans (s.bar_A_le_N hFac i₀)) hd⟩ *
        (s.ψ (S i₀) ⟨b, s.bar_B_le_N hFac i₀ hb⟩)⁻¹ ∈ D' :=
      (Subgroup.mem_normalizer_iff.mp (hBD' hb') _).mp hd'
    have hbA : b * d * b⁻¹ ∈ s.bar s.A :=
      (Subgroup.mem_normalizer_iff.mp (s.bar_B_le_normalizer_bar_A hb) d).mp (hDA hd)
    have heq : (⟨b * d * b⁻¹, s.bar_A_le_N hFac i₀ hbA⟩ : ↥(s.NQ (S i₀))) =
        (⟨b, s.bar_B_le_N hFac i₀ hb⟩ : ↥(s.NQ (S i₀))) *
          ⟨d, (hDA.trans (s.bar_A_le_N hFac i₀)) hd⟩ *
          (⟨b, s.bar_B_le_N hFac i₀ hb⟩ : ↥(s.NQ (S i₀)))⁻¹ := rfl
    have hval : s.ψ (S i₀) ((⟨b, s.bar_B_le_N hFac i₀ hb⟩ : ↥(s.NQ (S i₀))) *
        ⟨d, (hDA.trans (s.bar_A_le_N hFac i₀)) hd⟩ *
        (⟨b, s.bar_B_le_N hFac i₀ hb⟩ : ↥(s.NQ (S i₀)))⁻¹) =
        s.ψ (S i₀) ⟨b, s.bar_B_le_N hFac i₀ hb⟩ *
          s.ψ (S i₀) ⟨d, (hDA.trans (s.bar_A_le_N hFac i₀)) hd⟩ *
          (s.ψ (S i₀) ⟨b, s.bar_B_le_N hFac i₀ hb⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have him : s.ψ (S i₀) ⟨b * d * b⁻¹, s.bar_A_le_N hFac i₀ hbA⟩ ∈ s.im (S i₀) D := by
      rw [hDmap, heq, hval]
      exact h1
    obtain ⟨e, he, heψ⟩ := (s.mem_im_iff (S i₀) (hDA.trans (s.bar_A_le_N hFac i₀))).mp him
    have hinj := s.ψ_injective_of_inf_bot (S i₀) (s.bar_A_le_N hFac i₀)
      (s.bar_A_inf_centralizer_factor hFac i₀)
    have hEq : (⟨e, hDA he⟩ : ↥(s.bar s.A)) = ⟨b * d * b⁻¹, hbA⟩ := by
      refine hinj ?_
      simpa using heψ
    have hfin : e = b * d * b⁻¹ := congrArg Subtype.val hEq
    rw [← hfin]
    exact he
  rcases s.bar_line_eq D hDA hDcard hBD with h | h
  · left
    rw [← hDmap, h]
    rfl
  · right
    rw [← hDmap, h]
    rfl

end Checks

section SylowTwo

variable (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)

theorem T'_isPGroup : IsPGroup 2 (s.T' hFac i₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : IsPGroup 2 (s.bar D.T) := s.Tbar_isSylow.isPGroup
  exact (h.comap_subtype).map (s.ψ (S i₀))

theorem im_mul_comm {U W : Subgroup s.Q} (hU : U ≤ s.NQ (S i₀)) (hW : W ≤ s.NQ (S i₀))
    (h : (U : Set s.Q) * (W : Set s.Q) = (W : Set s.Q) * (U : Set s.Q)) :
    ((s.im (S i₀) U : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
        ((s.im (S i₀) W : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) =
      ((s.im (S i₀) W : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
        ((s.im (S i₀) U : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) := by
  have key : ∀ {U W : Subgroup s.Q} (hU : U ≤ s.NQ (S i₀)) (hW : W ≤ s.NQ (S i₀)),
      (U : Set s.Q) * (W : Set s.Q) = (W : Set s.Q) * (U : Set s.Q) →
      ((s.im (S i₀) U : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
          ((s.im (S i₀) W : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) ⊆
        ((s.im (S i₀) W : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
          ((s.im (S i₀) U : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) := by
    intro U W hU hW h z hz
    rw [Set.mem_mul] at hz ⊢
    obtain ⟨u, hu, w, hw, rfl⟩ := hz
    obtain ⟨u', hu', rfl⟩ := (s.mem_im_iff (S i₀) hU).mp hu
    obtain ⟨w', hw', rfl⟩ := (s.mem_im_iff (S i₀) hW).mp hw
    have hmem : ((⟨u', hU hu'⟩ * ⟨w', hW hw'⟩ : ↥(s.NQ (S i₀))) : s.Q) ∈
        (W : Set s.Q) * (U : Set s.Q) := by
      rw [← h]
      exact Set.mem_mul.mpr ⟨u', hu', w', hw', rfl⟩
    obtain ⟨w'', hw'', u'', hu'', hEq⟩ := Set.mem_mul.mp hmem
    exact Set.mem_mul.mpr ⟨s.ψ (S i₀) ⟨w'', hW hw''⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw''),
      s.ψ (S i₀) ⟨u'', hU hu''⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu''), by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hEq⟩
  exact le_antisymm (key hU hW h) (key hW hU h.symm)

theorem bar_mul_eq {U W : Subgroup G} (hU : U ≤ s.H) (hW : W ≤ s.H)
    (h : (U : Set G) * (W : Set G) = (W : Set G) * (U : Set G)) :
    ((s.bar U : Subgroup s.Q) : Set s.Q) * ((s.bar W : Subgroup s.Q) : Set s.Q) =
      ((s.bar W : Subgroup s.Q) : Set s.Q) * ((s.bar U : Subgroup s.Q) : Set s.Q) := by
  have key : ∀ {U W : Subgroup G} (hU : U ≤ s.H) (hW : W ≤ s.H),
      (U : Set G) * (W : Set G) = (W : Set G) * (U : Set G) →
      ((s.bar U : Subgroup s.Q) : Set s.Q) * ((s.bar W : Subgroup s.Q) : Set s.Q) ⊆
        ((s.bar W : Subgroup s.Q) : Set s.Q) * ((s.bar U : Subgroup s.Q) : Set s.Q) := by
    intro U W hU hW h z hz
    rw [Set.mem_mul] at hz ⊢
    obtain ⟨u, hu, w, hw, rfl⟩ := hz
    obtain ⟨u', hu', rfl⟩ := (s.mem_bar_iff hU).mp hu
    obtain ⟨w', hw', rfl⟩ := (s.mem_bar_iff hW).mp hw
    have hmem : (u' * w') ∈ (W : Set G) * (U : Set G) := by
      rw [← h]
      exact Set.mem_mul.mpr ⟨u', hu', w', hw', rfl⟩
    obtain ⟨w'', hw'', u'', hu'', hEq⟩ := Set.mem_mul.mp hmem
    exact Set.mem_mul.mpr ⟨s.π ⟨w'', hW hw''⟩, (s.mem_bar_iff hW).mpr ⟨w'', hw'', rfl⟩,
      s.π ⟨u'', hU hu''⟩, (s.mem_bar_iff hU).mpr ⟨u'', hu'', rfl⟩, by
        rw [← map_mul, ← map_mul]
        exact congrArg s.π (Subtype.ext hEq)⟩
  exact le_antisymm (key hU hW h) (key hW hU h.symm)

theorem bar_A_mul_TL :
    ((s.bar s.A : Subgroup s.Q) : Set s.Q) * ((s.TL hFac i₀ : Subgroup s.Q) : Set s.Q) =
      ((s.TL hFac i₀ : Subgroup s.Q) : Set s.Q) * ((s.bar s.A : Subgroup s.Q) : Set s.Q) := by
  have hAT := s.bar_mul_eq s.A_le_H s.T_le_H s.hAT
  refine le_antisymm ?_ ?_
  · rintro z ⟨a, ha, t, ht, rfl⟩
    have hmem : a * t ∈ (s.bar D.T : Set s.Q) * (s.bar s.A : Set s.Q) := by
      rw [← hAT]
      exact Set.mem_mul.mpr ⟨a, ha, t, ht.1, rfl⟩
    obtain ⟨t', ht', a', ha', hEq⟩ := Set.mem_mul.mp hmem
    have h1 : a * t ∈ s.NQ (S i₀) :=
      (s.NQ (S i₀)).mul_mem (s.bar_A_le_N hFac i₀ ha) ht.2
    have h2 : a' ∈ s.NQ (S i₀) := s.bar_A_le_N hFac i₀ ha'
    have ht'N : t' ∈ s.NQ (S i₀) := by
      have heq : t' = (a * t) * a'⁻¹ := by rw [← hEq]; group
      rw [heq]
      exact (s.NQ (S i₀)).mul_mem h1 ((s.NQ (S i₀)).inv_mem h2)
    exact Set.mem_mul.mpr ⟨t', ⟨ht', ht'N⟩, a', ha', hEq⟩
  · rintro z ⟨t, ht, a, ha, rfl⟩
    have hmem : t * a ∈ (s.bar s.A : Set s.Q) * (s.bar D.T : Set s.Q) := by
      rw [hAT]
      exact Set.mem_mul.mpr ⟨t, ht.1, a, ha, rfl⟩
    obtain ⟨a', ha', t', ht', hEq⟩ := Set.mem_mul.mp hmem
    have h1 : t * a ∈ s.NQ (S i₀) :=
      (s.NQ (S i₀)).mul_mem ht.2 (s.bar_A_le_N hFac i₀ ha)
    have h2 : a' ∈ s.NQ (S i₀) := s.bar_A_le_N hFac i₀ ha'
    have ht'N : t' ∈ s.NQ (S i₀) := by
      have heq : t' = a'⁻¹ * (t * a) := by rw [← hEq]; group
      rw [heq]
      exact (s.NQ (S i₀)).mul_mem ((s.NQ (S i₀)).inv_mem h2) h1
    exact Set.mem_mul.mpr ⟨a', ha', t', ⟨ht', ht'N⟩, hEq⟩

theorem bar_B_mul_TL :
    ((s.bar s.B : Subgroup s.Q) : Set s.Q) * ((s.TL hFac i₀ : Subgroup s.Q) : Set s.Q) =
      ((s.TL hFac i₀ : Subgroup s.Q) : Set s.Q) * ((s.bar s.B : Subgroup s.Q) : Set s.Q) := by
  have hBT := s.bar_mul_eq s.B_le_H s.T_le_H s.hBT
  refine le_antisymm ?_ ?_
  · rintro z ⟨a, ha, t, ht, rfl⟩
    have hmem : a * t ∈ (s.bar D.T : Set s.Q) * (s.bar s.B : Set s.Q) := by
      rw [← hBT]
      exact Set.mem_mul.mpr ⟨a, ha, t, ht.1, rfl⟩
    obtain ⟨t', ht', a', ha', hEq⟩ := Set.mem_mul.mp hmem
    have h1 : a * t ∈ s.NQ (S i₀) :=
      (s.NQ (S i₀)).mul_mem (s.bar_B_le_N hFac i₀ ha) ht.2
    have h2 : a' ∈ s.NQ (S i₀) := s.bar_B_le_N hFac i₀ ha'
    have ht'N : t' ∈ s.NQ (S i₀) := by
      have heq : t' = (a * t) * a'⁻¹ := by rw [← hEq]; group
      rw [heq]
      exact (s.NQ (S i₀)).mul_mem h1 ((s.NQ (S i₀)).inv_mem h2)
    exact Set.mem_mul.mpr ⟨t', ⟨ht', ht'N⟩, a', ha', hEq⟩
  · rintro z ⟨t, ht, a, ha, rfl⟩
    have hmem : t * a ∈ (s.bar s.B : Set s.Q) * (s.bar D.T : Set s.Q) := by
      rw [hBT]
      exact Set.mem_mul.mpr ⟨t, ht.1, a, ha, rfl⟩
    obtain ⟨a', ha', t', ht', hEq⟩ := Set.mem_mul.mp hmem
    have h1 : t * a ∈ s.NQ (S i₀) :=
      (s.NQ (S i₀)).mul_mem ht.2 (s.bar_B_le_N hFac i₀ ha)
    have h2 : a' ∈ s.NQ (S i₀) := s.bar_B_le_N hFac i₀ ha'
    have ht'N : t' ∈ s.NQ (S i₀) := by
      have heq : t' = a'⁻¹ * (t * a) := by rw [← hEq]; group
      rw [heq]
      exact (s.NQ (S i₀)).mul_mem ((s.NQ (S i₀)).inv_mem h2) h1
    exact Set.mem_mul.mpr ⟨a', ha', t', ⟨ht', ht'N⟩, hEq⟩

theorem im_TL_eq_T' : s.im (S i₀) (s.TL hFac i₀) = s.T' hFac i₀ := by
  unfold im T'
  congr 1
  ext n
  simp [TL, Subgroup.mem_subgroupOf]

theorem Abar'_mul_T' :
    ((s.Abar' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
        ((s.T' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) =
      ((s.T' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
        ((s.Abar' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) := by
  have h := s.im_mul_comm i₀ (s.bar_A_le_N hFac i₀) (s.TL_le_N hFac i₀)
    (s.bar_A_mul_TL hFac i₀)
  rwa [s.im_TL_eq_T' hFac i₀] at h

theorem B'_mul_T' :
    ((s.B' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
        ((s.T' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) =
      ((s.T' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) *
        ((s.B' hFac i₀ : Subgroup (s.Xq (S i₀))) : Set (s.Xq (S i₀))) := by
  have h := s.im_mul_comm i₀ (s.bar_B_le_N hFac i₀) (s.TL_le_N hFac i₀)
    (s.bar_B_mul_TL hFac i₀)
  rwa [s.im_TL_eq_T' hFac i₀] at h

theorem TSL'_le_L' : s.TSL' hFac i₀ ≤ s.L' hFac i₀ :=
  s.im_mono (S i₀) (inf_le_right : s.TSL hFac i₀ ≤ S i₀)

theorem TSL'_isSylow : CFSG.ABGLocalTools.IsSylowOf 2 (s.TSL' hFac i₀) (s.L' hFac i₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card (s.TSL'_le_L' hFac i₀) ?_
  rw [s.card_TSL' hFac i₀, s.card_L' hFac i₀]
  exact (s.SL_isSylow hFac i₀).card_eq

theorem TSL'_le_T' : s.TSL' hFac i₀ ≤ s.T' hFac i₀ := by
  rw [← s.im_TL_eq_T' hFac i₀]
  exact s.im_mono (S i₀) (s.TSL_le_TL hFac i₀)

theorem T'_inf_L'_eq : s.T' hFac i₀ ⊓ s.L' hFac i₀ = s.TSL' hFac i₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.IsSylowOf.eq_of_le (s.TSL'_isSylow hFac i₀)
    (le_inf (s.TSL'_le_T' hFac i₀) (s.TSL'_le_L' hFac i₀)) inf_le_right
    (s.T'_isPGroup hFac i₀).to_inf_left

theorem ML_le_L' : s.ML hFac i₀ ≤ s.L' hFac i₀ :=
  s.im_mono (S i₀) (inf_le_right : s.Mbar ⊓ S i₀ ≤ S i₀)

theorem TSL'_le_ML : s.TSL' hFac i₀ ≤ s.ML hFac i₀ := by
  refine s.im_mono (S i₀) ?_
  intro z hz
  obtain ⟨hzT, hzL⟩ := Subgroup.mem_inf.mp hz
  exact Subgroup.mem_inf.mpr ⟨s.bar_le_Mbar s.T_le_H D.sylowM.le hzT, hzL⟩

theorem T'_inf_L'_le_ML : s.T' hFac i₀ ⊓ s.L' hFac i₀ ≤ s.ML hFac i₀ := by
  rw [s.T'_inf_L'_eq hFac i₀]
  exact s.TSL'_le_ML hFac i₀

theorem ML_ne_L' : s.ML hFac i₀ ≠ s.L' hFac i₀ := by
  intro heq
  apply s.factor_not_le_Mbar hFac i₀
  intro l hl
  have hmem : s.ψ (S i₀) ⟨l, s.le_NQ (S i₀) hl⟩ ∈ s.ML hFac i₀ := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
  obtain ⟨m, hm, hmψ⟩ := (s.mem_im_iff (S i₀)
    (inf_le_right.trans (s.le_NQ (S i₀)))).mp hmem
  have hinj := s.ψ_injective_of_inf_bot (S i₀) (s.le_NQ (S i₀))
    (s.factor_inf_centralizer hFac i₀)
  have hEq : (⟨m, hm.2⟩ : ↥(S i₀)) = ⟨l, hl⟩ := by
    refine hinj ?_
    simpa using hmψ
  have hml : m = l := congrArg Subtype.val hEq
  rw [← hml]
  exact hm.1

end SylowTwo

section StrongFive

variable (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)

theorem Mbar_strong :
    ∀ g : s.Q, g ∉ s.Mbar →
      ¬ 5 ∣ Nat.card (s.Mbar ⊓ s.Mbar.map (MulAut.conj g).toMonoidHom : Subgroup s.Q) := by
  intro g hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective s.YH g
  have hp5 : s.p = 5 := by rw [← s.hBcard, s.B_card5]
  have hgM : (h : G) ∉ D.M := by
    intro hh
    apply hg
    exact (s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mpr ⟨(h : G), ⟨hh, h.2⟩, rfl⟩
  have hnot : ¬ s.p ∣
      Nat.card (D.M ⊓ D.M.map (MulAut.conj (h : G)).toMonoidHom : Subgroup G) :=
    s.hsp.2.2 h hgM
  rw [hp5] at hnot
  set W : Subgroup G := D.M ⊓ s.H with hW
  have hWle : W ≤ s.H := inf_le_right
  have hXH : W ⊓ W.map (MulAut.conj (h : G)).toMonoidHom ≤ s.H :=
    fun x hx => hWle (Subgroup.mem_inf.mp hx).1
  have hbar_le : s.Mbar ⊓ s.Mbar.map (MulAut.conj (QuotientGroup.mk' s.YH h)).toMonoidHom ≤
      s.bar (W ⊓ W.map (MulAut.conj (h : G)).toMonoidHom) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨w, hw, hwz⟩ := (s.mem_bar_iff hWle).mp hz1
    obtain ⟨z', hz', hz'z⟩ := Subgroup.mem_map.mp hz2
    obtain ⟨w', hw', hw'z'⟩ := (s.mem_bar_iff hWle).mp hz'
    have hxH : (h : G) * w' * (h : G)⁻¹ ∈ s.H :=
      s.H.mul_mem (s.H.mul_mem h.2 (hWle hw')) (s.H.inv_mem h.2)
    have hz'eq : z = s.π ⟨(h : G) * w' * (h : G)⁻¹, hxH⟩ := by
      rw [← hz'z, ← hw'z']
      show s.π h * s.π ⟨w', hWle hw'⟩ * (s.π h)⁻¹ =
        s.π ⟨(h : G) * w' * (h : G)⁻¹, hxH⟩
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    have hY : ((h : G) * w' * (h : G)⁻¹) * w⁻¹ ∈ s.Y := by
      have h1 : s.π (⟨(h : G) * w' * (h : G)⁻¹, hxH⟩ * (⟨w, hWle hw⟩ : ↥s.H)⁻¹) = 1 := by
        rw [map_mul, map_inv, hz'eq.symm, hwz]
        simp
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      simpa using Subgroup.mem_subgroupOf.mp h2
    refine (s.mem_bar_iff hXH).mpr ⟨(h : G) * w' * (h : G)⁻¹, ⟨?_, ?_⟩, hz'eq.symm⟩
    ·
      refine ⟨?_, hxH⟩
      have heq : (h : G) * w' * (h : G)⁻¹ =
          ((h : G) * w' * (h : G)⁻¹ * w⁻¹) * w := by group
      rw [heq]
      exact D.M.mul_mem (s.Y_le_M hY) hw.1
    ·
      exact Subgroup.mem_map.mpr ⟨w', hw', rfl⟩
  set X : Subgroup G := W ⊓ W.map (MulAut.conj (h : G)).toMonoidHom with hX
  have hXH' : X ≤ s.H := hXH
  have hdiv1 : Nat.card (s.bar X) ∣ Nat.card X := by
    have h := Subgroup.card_map_dvd (X.subgroupOf s.H) s.π
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH').toEquiv] at h
    exact h
  have hdiv2 : Nat.card X ∣
      Nat.card (D.M ⊓ D.M.map (MulAut.conj (h : G)).toMonoidHom : Subgroup G) :=
    Subgroup.card_dvd_of_le (hX ▸ inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left))
  intro hdvd
  exact hnot (hdvd.trans ((Subgroup.card_dvd_of_le hbar_le).trans (hdiv1.trans hdiv2)))

theorem five_dvd_Mbar : 5 ∣ Nat.card s.Mbar := by
  have h := Subgroup.card_dvd_of_le (s.bar_le_Mbar s.B_le_H s.hBM)
  rwa [s.bar_B_card] at h

theorem L'_strong (h5 : 5 ∣ Nat.card (s.L' hFac i₀)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 ((s.ML hFac i₀).subgroupOf (s.L' hFac i₀)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpMbar : 5 ∣ Nat.card s.Mbar := s.five_dvd_Mbar
  have hpL : 5 ∣ Nat.card (S i₀) := by rw [← s.card_L' hFac i₀]; exact h5
  haveI : s.Rbar.Normal := s.Rbar_normal
  haveI : ((S i₀).subgroupOf s.Rbar).Normal := s.factor_normal_in_Rbar hFac i₀
  have hMne : s.Mbar ≠ ⊤ := by
    intro htop
    apply s.factor_not_le_Mbar hFac i₀
    rw [htop]
    exact le_top
  have hMbarSP : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 s.Mbar :=
    ⟨hMne, hpMbar, s.Mbar_strong⟩
  obtain ⟨P, hP, hPM⟩ := hMbarSP.exists_isSylowOf_le
  have hHsub : CFSG.Open.IsSubnormal (S i₀) ⊤ := s.factor_isSubnormal hFac i₀
  have hP' : CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, hP.2.1, by simpa [Subgroup.relIndex_top_right] using hP.2.2⟩
  have hPS : CFSG.ABGLocalTools.IsSylowOf 5 (P ⊓ S i₀) (S i₀) :=
    hP'.inf_of_isSubnormal hHsub
  have hPSne : ((P : Subgroup s.Q) ⊓ (S i₀) : Subgroup s.Q) ≠ ⊥ := by
    let S5 : Sylow 5 s.Q := hP.2.1.toSylow (by
      simpa [Subgroup.relIndex_top_right] using hP.2.2)
    have h := CFSG.Walter.sylow_inf_ne_bot_of_isSubnormal S5
      ((CFSG.Open.IsSubnormal.top_iff).mp hHsub) hpL
    simpa [S5, IsPGroup.toSylow_coe] using h
  have hdvdPS : 5 ∣ Nat.card ↥((P : Subgroup s.Q) ⊓ (S i₀)) := by
    rw [hPS.card_eq]
    have hfac : 0 < (Nat.card (S i₀)).factorization 5 :=
      (by norm_num : Nat.Prime 5).factorization_pos_of_dvd Nat.card_pos.ne' hpL
    exact dvd_pow_self 5 hfac.ne'
  have hdvdMS : 5 ∣ Nat.card ↥(s.Mbar ⊓ S i₀) :=
    hdvdPS.trans (Subgroup.card_dvd_of_le (inf_le_inf hPM le_rfl))
  have h : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5
      ((s.Mbar ⊓ S i₀).subgroupOf (S i₀)) := by
    simpa [inf_comm] using
      hMbarSP.subgroupOf (s.factor_not_le_Mbar hFac i₀) (by simpa [inf_comm] using hdvdMS)
  have h' := CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_map_mulEquiv
    (s.L_equiv hFac i₀) h
  have heq : ((s.Mbar ⊓ S i₀).subgroupOf (S i₀)).map (s.L_equiv hFac i₀).toMonoidHom =
      (s.ML hFac i₀).subgroupOf (s.L' hFac i₀) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map.mpr ⟨⟨(y : s.Q), s.le_NQ (S i₀) y.2⟩,
          Subgroup.mem_subgroupOf.mpr ⟨hy1, hy2⟩, rfl⟩)
    · intro hz
      obtain ⟨n, hn, hnz⟩ := (s.mem_im_iff (S i₀)
        (inf_le_right.trans (s.le_NQ (S i₀)))).mp (Subgroup.mem_subgroupOf.mp hz)
      refine ⟨⟨n, hn.2⟩, Subgroup.mem_subgroupOf.mpr hn, ?_⟩
      exact Subtype.ext hnz
  rw [heq] at h'
  exact h'

end StrongFive

section Lifting

variable (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)

@[expose] def NN (C' : Subgroup (s.Xq (S i₀))) : Subgroup ↥(s.NQ (S i₀)) :=
  (S i₀).subgroupOf (s.NQ (S i₀)) ⊓
    Subgroup.comap (s.ψ (S i₀)) (Subgroup.normalizer (C' : Set (s.Xq (S i₀))))

theorem mem_NN_iff {C' : Subgroup (s.Xq (S i₀))} {n : ↥(s.NQ (S i₀))} :
    n ∈ s.NN i₀ C' ↔
      (n : s.Q) ∈ S i₀ ∧ s.ψ (S i₀) n ∈ Subgroup.normalizer (C' : Set (s.Xq (S i₀))) := by
  rw [NN, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]

theorem NN_le_L (C' : Subgroup (s.Xq (S i₀))) :
    s.NN i₀ C' ≤ (S i₀).subgroupOf (s.NQ (S i₀)) := inf_le_left

theorem NN_one_mem (C' : Subgroup (s.Xq (S i₀))) : (1 : ↥(s.NQ (S i₀))) ∈ s.NN i₀ C' := by
  rw [s.mem_NN_iff]
  exact ⟨(S i₀).one_mem, by rw [map_one]; exact (Subgroup.normalizer _).one_mem⟩

@[expose] def gen (U : Subgroup s.Q) (C' : Subgroup (s.Xq (S i₀))) : Set ↥(s.NQ (S i₀)) :=
  {z | ∃ n ∈ s.NN i₀ C',
    z ∈ (U.subgroupOf (s.NQ (S i₀))).map (MulAut.conj n).toMonoidHom}

@[expose] def X0 (U : Subgroup s.Q) (C' : Subgroup (s.Xq (S i₀))) : Subgroup ↥(s.NQ (S i₀)) :=
  Subgroup.closure (s.gen i₀ U C')

theorem gen_subset_X0 {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))} :
    s.gen i₀ U C' ⊆ (s.X0 i₀ U C' : Set ↥(s.NQ (S i₀))) :=
  Subgroup.subset_closure

theorem le_X0_of_le {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))} :
    U.subgroupOf (s.NQ (S i₀)) ≤ s.X0 i₀ U C' := by
  intro u hu
  exact Subgroup.subset_closure (show u ∈ s.gen i₀ U C' from
    ⟨1, s.NN_one_mem i₀ C', by simpa using hu⟩)

theorem image_X0_le {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))}
    (hU' : s.im (S i₀) U ≤ C') :
    (s.X0 i₀ U C').map (s.ψ (S i₀)) ≤ C' := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hz
  have key : ∀ x ∈ s.X0 i₀ U C', s.ψ (S i₀) x ∈ C' := by
    intro x hx
    rw [X0] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨m, hm, hmy⟩ := hy
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hmy
        obtain ⟨-, hmN⟩ := (s.mem_NN_iff i₀).mp hm
        have hψu : s.ψ (S i₀) u ∈ C' := hU' (Subgroup.mem_map_of_mem _ hu)
        exact (Subgroup.mem_normalizer_iff.mp hmN _).mp hψu
    | one => rw [map_one]; exact C'.one_mem
    | mul x y hx hy ihx ihy => rw [map_mul]; exact C'.mul_mem ihx ihy
    | inv x hx ih => rw [map_inv]; exact C'.inv_mem ih
  exact key n hn

theorem X0_le_sup {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))} :
    s.X0 i₀ U C' ≤ U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀)) := by
  rw [X0]
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨n, hn, hz⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
  have hnL : n ∈ U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀)) :=
    Subgroup.mem_sup_right (s.NN_le_L i₀ C' hn)
  have huU : u ∈ U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀)) :=
    Subgroup.mem_sup_left hu
  have hconj : (MulEquiv.toMonoidHom (MulAut.conj n)) u = n * u * n⁻¹ := rfl
  rw [hconj]
  exact (U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀))).mul_mem
    ((U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀))).mul_mem hnL huU)
    ((U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀))).inv_mem hnL)

theorem bar_A₁_commutative : IsMulCommutative ↥(s.bar s.A₁) := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact (isCyclic_of_prime_card s.bar_A₁_card).isMulCommutative

theorem bar_A₂_commutative : IsMulCommutative ↥(s.bar s.A₂) := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact (isCyclic_of_prime_card s.bar_A₂_card).isMulCommutative

theorem bar_B_commutative : IsMulCommutative ↥(s.bar s.B) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact (isCyclic_of_prime_card s.bar_B_card).isMulCommutative

theorem commutator_sup_le {U : Subgroup s.Q} (hUab : IsMulCommutative ↥U) :
    ⁅U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀)),
      U.subgroupOf (s.NQ (S i₀)) ⊔ (S i₀).subgroupOf (s.NQ (S i₀))⁆ ≤
      (S i₀).subgroupOf (s.NQ (S i₀)) := by
  haveI hLn : ((S i₀).subgroupOf (s.NQ (S i₀))).Normal := s.normal_in_NQ (S i₀)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨u₁, hu₁, m₁, hm₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
  obtain ⟨u₂, hu₂, m₂, hm₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  have hm₁' : (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) m₁ = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff m₁).mpr hm₁
  have hm₂' : (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) m₂ = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff m₂).mpr hm₂
  have hρa : (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) (u₁ * m₁) =
      (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) u₁ := by
    rw [map_mul, hm₁', mul_one]
  have hρb : (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) (u₂ * m₂) =
      (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) u₂ := by
    rw [map_mul, hm₂', mul_one]
  have hprod : u₁ * u₂ = u₂ * u₁ := by
    apply Subtype.ext
    simpa using congrArg Subtype.val ((isMulCommutative_iff.mp hUab)
      ⟨(u₁ : s.Q), Subgroup.mem_subgroupOf.mp hu₁⟩
      ⟨(u₂ : s.Q), Subgroup.mem_subgroupOf.mp hu₂⟩)
  have hcomm : (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) u₁ *
      (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) u₂ =
      (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) u₂ *
        (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) u₁ := by
    rw [← map_mul, ← map_mul, hprod]
  have h1 : (QuotientGroup.mk' ((S i₀).subgroupOf (s.NQ (S i₀)))) ⁅u₁ * m₁, u₂ * m₂⁆ = 1 := by
    rw [map_commutatorElement, hρa, hρb]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  exact (QuotientGroup.eq_one_iff ⁅u₁ * m₁, u₂ * m₂⁆).mp h1

theorem commutator_X0_le_ker {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))}
    (hC' : IsMulCommutative ↥C') (hU' : s.im (S i₀) U ≤ C') :
    ⁅s.X0 i₀ U C', s.X0 i₀ U C'⁆ ≤ (s.ψ (S i₀)).ker := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker]
  have ha' : s.ψ (S i₀) a ∈ C' := s.image_X0_le i₀ hU' (Subgroup.mem_map_of_mem _ ha)
  have hb' : s.ψ (S i₀) b ∈ C' := s.image_X0_le i₀ hU' (Subgroup.mem_map_of_mem _ hb)
  have hcomm : s.ψ (S i₀) a * s.ψ (S i₀) b = s.ψ (S i₀) b * s.ψ (S i₀) a := by
    simpa using congrArg Subtype.val ((isMulCommutative_iff.mp hC') ⟨_, ha'⟩ ⟨_, hb'⟩)
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem LN_inf_ker (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    (S i₀).subgroupOf (s.NQ (S i₀)) ⊓ (s.ψ (S i₀)).ker = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro n hn
  obtain ⟨hnL, hnK⟩ := Subgroup.mem_inf.mp hn
  rw [MonoidHom.mem_ker] at hnK
  have h1 : ((n : s.Q)) ∈ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) :=
    (s.ψ_eq_one_iff (S i₀)).mp hnK
  have h2 : (n : s.Q) ∈ S i₀ := Subgroup.mem_subgroupOf.mp hnL
  have h3 : (n : s.Q) ∈ S i₀ ⊓ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) := ⟨h2, h1⟩
  rw [s.factor_inf_centralizer hFac i₀, Subgroup.mem_bot] at h3
  exact Subgroup.mem_bot.mpr (Subtype.ext h3)

theorem X0_commutator_eq_bot (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))}
    (hUab : IsMulCommutative ↥U) (hC' : IsMulCommutative ↥C')
    (hU' : s.im (S i₀) U ≤ C') :
    ⁅s.X0 i₀ U C', s.X0 i₀ U C'⁆ = ⊥ := by
  have h : ⁅s.X0 i₀ U C', s.X0 i₀ U C'⁆ ≤
      (S i₀).subgroupOf (s.NQ (S i₀)) ⊓ (s.ψ (S i₀)).ker :=
    le_inf (le_trans (Subgroup.commutator_mono (s.X0_le_sup (C' := C'))
      (s.X0_le_sup (C' := C'))) (s.commutator_sup_le i₀ hUab))
      (s.commutator_X0_le_ker i₀ hC' hU')
  rw [s.LN_inf_ker hFac i₀] at h
  exact eq_bot_iff.mpr h

theorem X0_le_centralizer (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))}
    (hUab : IsMulCommutative ↥U) (hC' : IsMulCommutative ↥C') (hU' : s.im (S i₀) U ≤ C') :
    s.X0 i₀ U C' ≤ Subgroup.centralizer
      ((U.subgroupOf (s.NQ (S i₀)) : Subgroup ↥(s.NQ (S i₀))) : Set ↥(s.NQ (S i₀))) := by
  have hbot := s.X0_commutator_eq_bot hFac i₀ hUab hC' hU'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hmem : ⁅u, x⁆ ∈ ⁅s.X0 i₀ U C', s.X0 i₀ U C'⁆ :=
    Subgroup.commutator_mem_commutator (s.le_X0_of_le (i₀ := i₀) (U := U) (C' := C') hu) hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem X0_mem_Mbar (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    {UG : Subgroup G} {C' : Subgroup (s.Xq (S i₀))}
    (hU : UG ∈ uniqueSet D.M) (hUH : UG ≤ s.H) (hUN : s.bar UG ≤ s.NQ (S i₀))
    (hUab : IsMulCommutative ↥(s.bar UG)) (hC' : IsMulCommutative ↥C')
    (hU' : s.im (S i₀) (s.bar UG) ≤ C')
    {x : ↥(s.NQ (S i₀))} (hx : x ∈ s.X0 i₀ (s.bar UG) C') :
    (x : s.Q) ∈ s.Mbar := by
  refine s.mem_Mbar_of_centralizes hU hUH ?_
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm := (Subgroup.mem_centralizer_iff.mp
    (s.X0_le_centralizer hFac i₀ hUab hC' hU' hx))
    (⟨u, hUN hu⟩ : ↥(s.NQ (S i₀))) (Subgroup.mem_subgroupOf.mpr hu)
  exact congrArg Subtype.val hcomm

theorem NN_le_normalizer_X0 {U : Subgroup s.Q} {C' : Subgroup (s.Xq (S i₀))}
    {l : ↥(s.NQ (S i₀))} (hl : l ∈ s.NN i₀ C') :
    l ∈ Subgroup.normalizer (s.X0 i₀ U C' : Set ↥(s.NQ (S i₀))) := by
  have hgen : ∀ z ∈ s.gen i₀ U C', (MulEquiv.toMonoidHom (MulAut.conj l)) z ∈ s.gen i₀ U C' := by
    rintro z ⟨n, hn, hz⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    refine ⟨l * n, (s.NN i₀ C').mul_mem hl hn, ?_⟩
    refine Subgroup.mem_map.mpr ⟨u, hu, ?_⟩
    show (l * n) * u * (l * n)⁻¹ = l * (n * u * n⁻¹) * l⁻¹
    group
  have hclosure : ∀ (y : ↥(s.NQ (S i₀))), y ∈ s.X0 i₀ U C' →
      (MulEquiv.toMonoidHom (MulAut.conj l)) y ∈ s.X0 i₀ U C' := by
    intro y hy
    rw [X0] at hy ⊢
    refine Subgroup.closure_induction (p := fun y _ =>
      (MulEquiv.toMonoidHom (MulAut.conj l)) y ∈ Subgroup.closure (s.gen i₀ U C')) ?_ ?_ ?_ ?_ hy
    · intro z hz
      exact Subgroup.subset_closure (hgen z hz)
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b _ _ iha ihb
      rw [map_mul]
      exact Subgroup.mul_mem _ iha ihb
    · intro a _ iha
      rw [map_inv]
      exact Subgroup.inv_mem _ iha
  have hmaple : (s.X0 i₀ U C').map (MulEquiv.toMonoidHom (MulAut.conj l)) ≤ s.X0 i₀ U C' := by
    rintro z ⟨y, hy, rfl⟩
    exact hclosure y hy
  have hcard : Nat.card ↥((s.X0 i₀ U C').map (MulEquiv.toMonoidHom (MulAut.conj l))) =
      Nat.card ↥(s.X0 i₀ U C') :=
    Subgroup.card_map_of_injective (K := s.X0 i₀ U C')
      (f := MulEquiv.toMonoidHom (MulAut.conj l)) (MulAut.conj l).injective
  have heq : (s.X0 i₀ U C').map (MulEquiv.toMonoidHom (MulAut.conj l)) = s.X0 i₀ U C' :=
    Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem lifting_of_le (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    (C' : Subgroup (s.Xq (S i₀))) (hC' : IsMulCommutative ↥C')
    {UG : Subgroup G} (hU : UG ∈ uniqueSet D.M) (hUH : UG ≤ s.H)
    (hUN : s.bar UG ≤ s.NQ (S i₀))
    (hUab : IsMulCommutative ↥(s.bar UG)) (hU' : s.im (S i₀) (s.bar UG) ≤ C') :
    s.L' hFac i₀ ⊓ Subgroup.normalizer (C' : Set (s.Xq (S i₀))) ≤ s.ML hFac i₀ := by
  intro z hz
  obtain ⟨hzL, hzN⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨l, hlS, hlz⟩ := (s.mem_im_iff (S i₀) (s.le_NQ (S i₀))).mp hzL
  have hlNN : (⟨l, s.le_NQ (S i₀) hlS⟩ : ↥(s.NQ (S i₀))) ∈ s.NN i₀ C' := by
    rw [s.mem_NN_iff i₀]
    exact ⟨hlS, by rw [hlz]; exact hzN⟩
  have hlNnorm : (⟨l, s.le_NQ (S i₀) hlS⟩ : ↥(s.NQ (S i₀))) ∈
      Subgroup.normalizer (s.X0 i₀ (s.bar UG) C' : Set ↥(s.NQ (S i₀))) :=
    s.NN_le_normalizer_X0 (i₀ := i₀) (U := s.bar UG) (C' := C') hlNN
  set X0Q : Subgroup s.Q := (s.X0 i₀ (s.bar UG) C').map (s.NQ (S i₀)).subtype with hX0Q
  set W : Subgroup G := (X0Q.comap s.π).map s.H.subtype with hW
  have hX0Q_M : X0Q ≤ s.Mbar := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact s.X0_mem_Mbar hFac i₀ hU hUH hUN hUab hC' hU' hx
  have hWsub : W.subgroupOf s.H = X0Q.comap s.π := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
      have hweq : w = x := Subtype.ext hwx
      rwa [← hweq]
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hbarW : s.bar W = X0Q := by
    unfold bar
    rw [hWsub]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective s.YH) X0Q
  have hUleX0Q : s.bar UG ≤ X0Q := by
    rw [hX0Q]
    have h := Subgroup.map_mono (f := (s.NQ (S i₀)).subtype)
      (s.le_X0_of_le (i₀ := i₀) (U := s.bar UG) (C' := C'))
    rwa [Subgroup.map_subgroupOf_eq_of_le hUN] at h
  have hUleW : UG ≤ W := by
    intro u hu
    have huH : u ∈ s.H := hUH hu
    refine Subgroup.mem_map.mpr ⟨⟨u, huH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hUleX0Q ((s.mem_bar_iff hUH).mpr ⟨u, hu, rfl⟩)
  have hWleH : W ≤ s.H := Subgroup.map_subtype_le _
  have hWleM : W ≤ D.M := by
    haveI hYH : (s.Y.subgroupOf s.H).Normal := s.YH_normal
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyX : s.π y ∈ X0Q := Subgroup.mem_comap.mp hy
    have hyMbar : s.π y ∈ s.Mbar := hX0Q_M hyX
    obtain ⟨m, hm, hmy⟩ := (s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mp hyMbar
    have hker : s.π ((⟨m, hm.2⟩ : ↥s.H)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hmy]
      simp
    have hmemY : (((⟨m, hm.2⟩ : ↥s.H)⁻¹ * y : ↥s.H) : G) ∈ s.Y :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hker)
    have hM' : (m : G)⁻¹ * (y : G) ∈ D.M := s.Y_le_M hmemY
    change (y : G) ∈ D.M
    have heq : (y : G) = m * (m⁻¹ * y) := by group
    rw [heq]
    exact D.M.mul_mem hm.1 hM'
  have key : ∀ (g : s.Q) (hgn : g ∈ s.NQ (S i₀)),
      (⟨g, hgn⟩ : ↥(s.NQ (S i₀))) ∈ Subgroup.normalizer (s.X0 i₀ (s.bar UG) C') →
      ∀ x ∈ X0Q, g * x * g⁻¹ ∈ X0Q := by
    intro g hgn hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    exact Subgroup.mem_map.mpr
      ⟨(MulEquiv.toMonoidHom (MulAut.conj (⟨g, hgn⟩ : ↥(s.NQ (S i₀))))) y, h1, rfl⟩
  have hlNQ : l ∈ Subgroup.normalizer (X0Q : Set s.Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key l (s.le_NQ (S i₀) hlS) hlNnorm x
    · intro hx
      have h2 := key l⁻¹ ((s.NQ (S i₀)).inv_mem (s.le_NQ (S i₀) hlS))
        ((Subgroup.normalizer _).inv_mem hlNnorm) (l * x * l⁻¹) hx
      rwa [show (l⁻¹)⁻¹ = l from inv_inv l,
        show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h2
  have hlM : l ∈ s.Mbar :=
    s.mem_Mbar_of_normalizes hU hUH hUleW hWleH hWleM (by rw [hbarW]; exact hlNQ)
  exact (s.mem_im_iff (S i₀) (inf_le_right.trans (s.le_NQ (S i₀)))).mpr
    ⟨l, ⟨hlM, hlS⟩, hlz⟩

theorem lifting_C5 (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    ∀ C' : Subgroup (s.Xq (S i₀)), IsMulCommutative ↥C' →
      (s.A₁' hFac i₀ ≤ C' ∨ s.A₂' hFac i₀ ≤ C' ∨ s.B' hFac i₀ ≤ C') →
      s.L' hFac i₀ ⊓ Subgroup.normalizer (C' : Set (s.Xq (S i₀))) ≤ s.ML hFac i₀ := by
  intro C' hC' h
  rcases h with h | h | h
  · exact s.lifting_of_le hFac i₀ C' hC' s.A₁_mem_uniqueSet s.A₁_le_H
      (s.bar_A₁_le_N hFac i₀) s.bar_A₁_commutative h
  · exact s.lifting_of_le hFac i₀ C' hC' s.A₂_mem_uniqueSet s.A₂_le_H
      (s.bar_A₂_le_N hFac i₀) s.bar_A₂_commutative h
  · exact s.lifting_of_le hFac i₀ C' hC' s.B_mem_uniqueSet s.B_le_H
      (s.bar_B_le_N hFac i₀) s.bar_B_commutative h

end Lifting

end AlmostSimple

end Data

theorem nonempty_fin_of_factorization {r : ℕ}
    {S : Fin r → Subgroup s.Q} (hFac : IsFactorization s.Rbar S) : Nonempty (Fin r) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · exfalso
    subst h
    have hbot : (⨆ i : Fin 0, S i) = ⊥ := iSup_eq_bot.mpr (fun i => i.elim0)
    have hiSup := hFac.iSup_eq
    rw [hbot] at hiSup
    exact s.Rbar_ne_bot hiSup.symm
  · exact ⟨⟨0, h⟩⟩

end ChiefSetup

theorem nonabComponentConfig_holds
    (D : Data G) (V₀ V : Subgroup G) :
    NonabComponentConfig D V₀ V := by
  intro L X p n l r C Dc Gamma x A₀ A B hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT
    hcent hsp hR8101 N H R hN hne hD₀H hHN hHM hmin hYR hRH hRn hminR hab hF
  classical
  let s : ChiefSetup D V₀ V :=
    { L := L, X := X, p := p, n := n, l := l, r := r, C := C, Dc := Dc, Gamma := Gamma, x := x,
      A₀ := A₀, A := A, B := B, hV₀ := hV₀, ctx := ctx, h8100 := h8100, hc4 := hc4,
      hAsyl := hAsyl, hAT := hAT, hBM := hBM, hBcard := hBcard, hAB := hAB, hBT := hBT,
      hcent := hcent, hsp := hsp, hR8101 := hR8101, N := N, H := H, R := R, hN := hN, hne := hne,
      hD₀H := hD₀H, hHN := hHN, hHM := hHM, hmin := hmin, hYR := hYR, hRH := hRH, hRn := hRn,
      hminR := hminR, hab := hab }
  obtain ⟨r', S', hFac⟩ := s.exists_factorization_Rbar
  let i₀ : Fin r' := Classical.choice (s.nonempty_fin_of_factorization hFac)
  haveI hCN : (s.CN (S' i₀)).Normal := s.CN_normal (S' i₀)
  haveI hGrp : Group (s.Xq (S' i₀)) := inferInstance
  haveI hfin : Finite (s.Xq (S' i₀)) :=
    Finite.of_surjective (s.ψ (S' i₀)) (QuotientGroup.mk'_surjective _)
  refine ⟨s.Xq (S' i₀), QuotientGroup.Quotient.group (s.CN (S' i₀)), hfin,
    s.L' hFac i₀, s.A₁' hFac i₀, s.A₂' hFac i₀, s.B' hFac i₀, s.T' hFac i₀, s.ML hFac i₀,
    s.L'_normal hFac i₀, s.L'_simple hFac i₀, s.L'_nonab hFac i₀, s.L'_K hFac i₀,
    s.centralizer_L'_eq_bot hFac i₀, s.card_A₁' hFac i₀, s.card_A₂' hFac i₀,
    s.A₁'_inf_A₂' hFac i₀, s.A₁'_le_centralizer_A₂' hFac i₀, s.card_B' hFac i₀,
    s.B'_le_normalizer_A₁' hFac i₀, s.B'_le_normalizer_A₂' hFac i₀,
    s.Abar'_commutator_B' hFac i₀, s.lines hFac i₀, s.T'_isPGroup hFac i₀, ?_, ?_,
    ?_, s.ML_le_L' hFac i₀, s.ML_ne_L' hFac i₀, s.T'_inf_L'_le_ML hFac i₀,
    s.lifting_C5 hFac i₀, s.L'_strong hFac i₀⟩
  · rw [← s.Abar'_eq_sup hFac i₀]
    exact s.Abar'_mul_T' hFac i₀
  · exact s.B'_mul_T' hFac i₀
  · rw [s.T'_inf_L'_eq hFac i₀]
    exact s.TSL'_isSylow hFac i₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem gap17_45_nonabChief_of_nonabComponent (D : Data G)
    (V₀ V : Subgroup G) (hC : Gap17_45_NonabComponent) :
    Gap17_45_NonabChief D V₀ V :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive.gap17_45_nonabChief_of_config D V₀ V hC
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive.nonabComponentConfig_holds D V₀ V)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
