module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77PairModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightWildWild

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step76EightWildMovesStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    ∃ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t), ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∉ Z

@[expose] def Step76EightWildMeetStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    ∀ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t),
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup y (Vt M (LB M Q B) B Z t) ≠ Z

theorem step76EightWildWitness_of_moves_meet (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h71 : Stroth71Statement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hSec : Sec7WVSecCardStatement)
    (hMoves : Step76EightWildMovesStatement) (hMeet : Step76EightWildMeetStatement) :
    Step76EightWildWitnessStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g hgM hΓ hwild
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hQM : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hVU : Ut Q Z t = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs.toSec5.notQ
  have hUt : ∀ h ∈ M, Ut Q Z (h * t * h⁻¹) = conjSubgroup h (Vt M (LB M Q B) B Z t) :=
    fun h hh => by
      rw [Ut_conj_of_normalizes (hc.conj_Q_eq hh) (hc.conj_Z_eq hh) t, hVU]
  have hcommt : ∀ h : G, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup h Z0, ⁅z, y⁆ ∈ Q) →
      ⁅h * t * h⁻¹, t⁆ ∈ Q := by
    intro h hΓ'
    have hxmem : h * t * h⁻¹ ∈ conjSubgroup h Z0 := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using htZ0
    have := Q.inv_mem (hΓ' t htZ0 _ hxmem)
    rwa [commutatorElement_inv] at this
  have hQx : ∀ h ∈ M, ∀ w ∈ Q, ⁅h * t * h⁻¹, w⁆ ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) := by
    intro h hh w hw
    have h1 : ⁅w, h * t * h⁻¹⁆ ∈ ⁅Q, Subgroup.zpowers (h * t * h⁻¹)⁆ :=
      Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers _)
    have h2 : ⁅h * t * h⁻¹, w⁆ ∈ Ut Q Z (h * t * h⁻¹) := by
      rw [← commutatorElement_inv]
      exact (Ut Q Z (h * t * h⁻¹)).inv_mem (Subgroup.mem_sup_left h1)
    rwa [hUt h hh] at h2
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hs1 : g * t * g⁻¹ * (g * t * g⁻¹)⁻¹ ∈ Q := by
    rw [mul_inv_cancel]
    exact Q.one_mem
  have hs2 : ⁅g * t * g⁻¹, t⁆ ∈ Q := hcommt g hΓ
  have huV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
    sec7_pair_vanish h71 hc hs hno hgM hs1 hs2
  obtain ⟨hVinf, -⟩ := sec7_wild_join h52a hA h310chi hSec hc hs h4 hgM hguM hs2 huV
    (hQx g hgM) hwild
  have huZ0 : g * t * g⁻¹ ∉ Z0 := by
    intro hu
    obtain ⟨w₀, hw₀, hw₀V⟩ := hwild
    exact hw₀V (sec39_Z_le_Vt ((hZc G M Q Z B hc n t hs Z0 hZ0 _ hu).2 w₀ hw₀))
  obtain ⟨y, hy, v, hv, hyv⟩ :=
    hMoves G M Q Z B hc n t hs hno h4 Z0 hZ0 g hgM _ hs1 hs2 huZ0 hVinf
  have hD1 : ∀ y₀ ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t), y₀ ∈ M ∧ y₀ ∈ H0 M Z ∧
      ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y₀, v⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro y₀ hy₀
    have hd : g⁻¹ * y₀ * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy₀
    have hdM : g⁻¹ * y₀ * g ∈ M := hc.LB_le_M hd.1
    have hyM : y₀ ∈ M := by
      have h3 := M.mul_mem (M.mul_mem hgM hdM) (M.inv_mem hgM)
      simpa [mul_assoc] using h3
    refine ⟨hyM, ⟨hyM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, fun v hv => ?_⟩
    · have hz' : g⁻¹ * z * g ∈ Z := by
        have : z ∈ conjSubgroup g Z := by rw [hc.conj_Z_eq hgM]; exact hz
        exact mem_conjSubgroup.mp this
      have h1 := hc.LB_centralizes_Z hd.1 _ hz'
      calc z * y₀ = g * (g⁻¹ * z * g) * g⁻¹ * y₀ := by group
        _ = g * ((g⁻¹ * y₀ * g) * (g⁻¹ * z * g) * (g⁻¹ * y₀ * g)⁻¹) * g⁻¹ * y₀ := by rw [h1]
        _ = y₀ * z := by group
    · have hmem := sec7_D1_comm_mem h71 h310chi h52a hA hc hs hno hgM hs1 hs2 hy₀ v hv
      have h2 := sec7_pair_mem_W h71 h310chi hc hs hno hgM hs1 hs2 (g⁻¹ * ⁅y₀, v⁆ * g)
        (mem_conjSubgroup.mp hmem)
      have e : g * (g⁻¹ * ⁅y₀, v⁆ * g) * g⁻¹ = ⁅y₀, v⁆ := by group
      rwa [e] at h2
  obtain ⟨hyM, hyH, hyW⟩ := hD1 y hy
  obtain ⟨-, -, hyiW⟩ := hD1 y⁻¹ ((conjSubgroup g (LB M Q B ⊓ hc.CN t)).inv_mem hy)
  have hcZ0 : ∀ z' ∈ Z0, ∀ v' ∈ Vt M (LB M Q B) B Z t, ⁅y * z' * y⁻¹, v'⁆ ∈ Z := by
    intro z' hz' v' hv'
    have h1 : y⁻¹ * v' * y ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have e : y⁻¹ * v' * y = ⁅y⁻¹, v'⁆ * v' := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem (hyiW v' hv') (hVW hv')
    have h2 := hZn y hyM _ ((hZc G M Q Z B hc n t hs Z0 hZ0 z' hz').2 _ h1)
    have e : y * ⁅z', y⁻¹ * v' * y⁆ * y⁻¹ = ⁅y * z' * y⁻¹, v'⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h2
  have hΓy : ∀ z ∈ Z0, ∀ y' ∈ conjSubgroup y Z0, ⁅z, y'⁆ ∈ Q := by
    intro z hz y' hy'
    have hz' : y⁻¹ * y' * y ∈ Z0 := mem_conjSubgroup.mp hy'
    have e : y' = y * (y⁻¹ * y' * y) * y⁻¹ := by group
    have hcH : y' ∈ H0 M Z := by
      rw [e]
      exact sec7_conj_mem_H0 hc hyM (hc.Rt_le_H0 t (hZ0.le hz'))
    have hcV : ∀ v' ∈ Vt M (LB M Q B) B Z t, ⁅y', v'⁆ ∈ Z := by
      intro v' hv'
      rw [e]
      exact hcZ0 _ hz' v' hv'
    have h1 := sec7_comm_Z0_of_vanish h34 h310chi hZc hZV hZcard hc hs hZ0 hcH hcV z hz
    have := Q.inv_mem h1
    rwa [commutatorElement_inv] at this
  refine ⟨y, hyM, hΓy, ?_, ?_, ?_⟩
  ·
    by_contra hnt
    push Not at hnt
    have hyt : y * t * y⁻¹ ∈ M := M.mul_mem (M.mul_mem hyM htM) (M.inv_mem hyM)
    obtain ⟨hVinf', -⟩ := sec7_wild_join h52a hA h310chi hSec hc hs h4 hyM hyt (hcommt y hΓy)
      (hcZ0 t htZ0) (hQx y hyM) hnt
    exact hMeet G M Q Z B hc n t hs hno h4 Z0 hZ0 g hgM _ hs1 hs2 huZ0 hVinf y hy hVinf'
  ·
    rw [hUt y hyM, hUt g hgM]
    intro z hz
    have hv' : y⁻¹ * z * y ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hz
    have hmem := sec7_D1_comm_mem h71 h310chi h52a hA hc hs hno hgM hs1 hs2 hy _ hv'
    have e : z = ⁅y, y⁻¹ * z * y⁆ * (y⁻¹ * z * y) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left hv')
  ·
    rw [hUt y hyM]
    intro hle
    have h1 : y * v * y⁻¹ ∈ conjSubgroup y (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup]
      have e : y⁻¹ * (y * v * y⁻¹) * y = v := by group
      rw [e]
      exact hv
    have h2 : ⁅y, v⁆ ∈ Vt M (LB M Q B) B Z t := by
      have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
      rw [e]
      exact (Vt M (LB M Q B) B Z t).mul_mem (hle h1) ((Vt M (LB M Q B) B Z t).inv_mem hv)
    have h3 := sec7_D1_comm_mem h71 h310chi h52a hA hc hs hno hgM hs1 hs2 hy v hv
    have h4' : ⁅y, v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      ⟨h2, h3⟩
    rw [hVinf] at h4'
    exact hyv h4'

end CFSG.RankThree.GF2n.Stroth80
