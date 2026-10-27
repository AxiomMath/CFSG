module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Frame
import CFSG.OddTranspositions.FusionStep
import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ElevenOneHyp.exists_sylow_le_centralizer {hC : HypothesisC D} (h : ElevenOneHyp hC) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer {hC.d} := by
  classical
  let H := Halpha D hC.alpha
  let T : Sylow 2 H := default
  have hP : IsPGroup 2 ((T : Subgroup H).map H.subtype) := T.isPGroup'.map H.subtype
  obtain ⟨S, hTS⟩ := hP.exists_le_sylow
  obtain ⟨v, hv⟩ := h.exists_frame S T hTS
  have hd_not_range : hC.d ∉ Set.range v := by
    rintro ⟨i, hi⟩
    have hdDstar : hC.d ∈ DalphaStar D hC.alpha := by
      rw [← hi]
      exact hv.mem i
    have hdE : hC.d ∈ hC.E := by rwa [hC.DalphaStar_alpha] at hdDstar
    have hdα : hC.d ∈ hC.alpha := hC.d_mem_alpha
    rw [hC.alpha_eq_normSet_diff] at hdα
    exact hdα.2 hdE
  let Δ : Set G := (S : Set G) ∩ D
  have hΔdef : Δ = (S : Set G) ∩ D := rfl
  have hΔeq : Δ = insert hC.d (Set.range v) := hv.inter_eq
  have hcard : Nat.card ↥Δ = 5 := by
    have h : Δ.ncard = 5 := by
      rw [hΔeq, Set.ncard_insert_of_notMem hd_not_range,
        Set.ncard_range_of_injective hv.injective, Nat.card_fin]
    rwa [Nat.card_coe_set_eq]
  have hΔmem : ∀ (s : ↥(S : Subgroup G)) {x : G}, x ∈ Δ →
      (s : G) * x * (s : G)⁻¹ ∈ Δ := by
    intro s x hx
    rw [hΔdef] at hx ⊢
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ s.2 hx.1) (Subgroup.inv_mem _ s.2),
      hC.setup.normal s x hx.2⟩
  letI : MulAction ↥(S : Subgroup G) ↥Δ :=
    { smul := fun s x => ⟨(s : G) * (x : G) * (s : G)⁻¹, hΔmem s x.2⟩
      one_smul := fun x => Subtype.ext (by
        change (↑(1 : ↥(S : Subgroup G)) : G) * (x : G) *
            (↑(1 : ↥(S : Subgroup G)) : G)⁻¹ = (x : G)
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change (↑(s * t : ↥(S : Subgroup G)) : G) * (x : G) *
            (↑(s * t : ↥(S : Subgroup G)) : G)⁻¹ =
          (s : G) * ((t : G) * (x : G) * (t : G)⁻¹) * (s : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hsmul : ∀ (s : ↥(S : Subgroup G)) (x : ↥Δ),
      ((s • x : ↥Δ) : G) = (s : G) * (x : G) * (s : G)⁻¹ := fun s x => rfl
  have hnotdvd : ¬ 2 ∣ Nat.card ↥Δ := by
    rw [hcard]
    norm_num
  obtain ⟨δ, hδ⟩ := (S.isPGroup').nonempty_fixed_point_of_prime_not_dvd_card ↥Δ hnotdvd
  have hS_le_Cδ : (S : Subgroup G) ≤ Subgroup.centralizer ({(δ : G)} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : s * (δ : G) * s⁻¹ = (δ : G) := by
      have h' := congrArg Subtype.val (hδ ⟨s, hs⟩)
      rw [hsmul ⟨s, hs⟩ δ] at h'
      simpa using h'
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hdΔ : hC.d ∈ Δ := by
    rw [hΔeq]
    exact Set.mem_insert _ _
  obtain ⟨n, _hn, hnd⟩ := sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S
    (show (δ : G) ∈ (S : Set G) ∩ D from by rw [← hΔdef]; exact δ.2)
    (show hC.d ∈ (S : Set G) ∩ D from by rw [← hΔdef]; exact hdΔ)
  refine ⟨n • S, ?_⟩
  intro x hx
  have hx' : x ∈ ((n • S : Sylow 2 G) : Set G) := hx
  rw [Sylow.coe_smul, Set.mem_smul_set] at hx'
  obtain ⟨y, hyS, hyx⟩ := hx'
  rw [MulAut.smul_def, MulAut.conj_apply] at hyx
  have hyc : y * (δ : G) * y⁻¹ = (δ : G) := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hS_le_Cδ hyS)
    rw [hcomm]
    group
  have hconj : (n * y * n⁻¹) * hC.d * (n * y * n⁻¹)⁻¹ = hC.d := by
    calc (n * y * n⁻¹) * hC.d * (n * y * n⁻¹)⁻¹
        = (n * y * n⁻¹) * (n * (δ : G) * n⁻¹) * (n * y * n⁻¹)⁻¹ := by rw [← hnd]
      _ = n * (y * (δ : G) * y⁻¹) * n⁻¹ := by group
      _ = n * (δ : G) * n⁻¹ := by rw [hyc]
      _ = hC.d := hnd
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : x * hC.d * x⁻¹ = hC.d := by
    rw [← hyx]
    exact hconj
  exact mul_inv_eq_iff_eq_mul.mp h2

end CFSG.OddTranspositions.PartThree
