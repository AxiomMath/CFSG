module

public import CFSG.Quasithin.MS93.S46T

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

namespace LastHyp

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] [Fintype F]
  {K Q Lt U Z0 Z V : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (h : LastHyp K Q Lt U Z0 Z V ψ)
include h

omit [Fintype F] in
theorem eq_one_of_mem_u {u : 𝔾} (hu : u ∈ U) (hl : ∀ l ∈ Lt, l * u * l⁻¹ = u) : u = 1 := by
  set N := NatSec.ofIsSum h.nat
  refine N.eq_one_of_coord_eq_zero hu (eq_zero_of_fixed fun g => ?_)
  obtain ⟨l, hl', rfl⟩ := h.exists_lt_toSL3_eq g
  have e := N.coord_conj l hu
  rw [hl l hl', natAct_false] at e
  exact e.symm

omit [Fintype F] in
theorem le_z_of_comm {B : Subgroup 𝔾} (hBV : B ≤ centerOf V) (hBL : ∀ b ∈ B, ∀ l ∈ Lt, ⁅b, l⁆ ∈ Z)
    (hBQ : ⁅B, Q⁆ ≤ U) (hV2 : ∀ v ∈ V, v ^ 2 ∈ U)
    (hΩ : ∀ x ∈ Q, x ∈ Subgroup.centralizer (Q : Set 𝔾) → x ^ 2 = 1 → x ∈ Z) : B ≤ Z := by
  intro b hb
  have hbV : b ∈ V := (hBV hb).1
  have hbc : b ∈ Subgroup.centralizer (V : Set 𝔾) := (hBV hb).2
  have hbQ : b ∈ Q := h.vq hbV
  have hZQ : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z := fun z hz y hy => h.comm_z_q hz hy
  have hlb : ∀ l ∈ Lt, l * b * l⁻¹ = ⁅b, l⁆⁻¹ * b := fun l _ => by
    simp only [commutatorElement_def]
    group
  have hcomm : ∀ x ∈ Q, ⁅b, x⁆ = 1 := by
    intro x hx
    have hcU : ⁅b, x⁆ ∈ U := hBQ (Subgroup.commutator_mem_commutator hb hx)
    refine h.eq_one_of_mem_u hcU fun l hl => ?_
    have hz : ⁅b, l⁆⁻¹ ∈ Z := Z.inv_mem (hBL b hb l hl)
    have hv : ⁅l, x⁆ ∈ V := by
      have h1 := h.ql (Subgroup.commutator_mem_commutator hx hl)
      rw [← commutatorElement_inv]
      exact V.inv_mem h1
    have hvQ : ⁅l, x⁆ ∈ Q := h.vq hv
    set z := ⁅b, l⁆⁻¹ with hzdef
    set v := ⁅l, x⁆ with hvdef
    have hlx : l * x * l⁻¹ = v * x := by
      rw [hvdef]
      simp only [commutatorElement_def]
      group
    have hbv : b * v = v * b := (Subgroup.mem_centralizer_iff.mp hbc v hv).symm
    have hcv : ⁅b, x⁆ * v = v * ⁅b, x⁆ := hZQ _ (h.uZ hcU) v hvQ
    have hzb : z * b = b * z := hZQ z hz b hbQ
    have hzvx : z * (v * x) = (v * x) * z := hZQ z hz _ (Q.mul_mem hvQ hx)
    calc l * ⁅b, x⁆ * l⁻¹ = ⁅l * b * l⁻¹, l * x * l⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅z * b, v * x⁆ := by rw [hlb l hl, hlx]
      _ = ⁅b, v * x⁆ := by
          rw [hzb, commutatorElement_mul_left_conj,
            commutatorElement_eq_one_iff_mul_comm.mpr hzvx, mul_one, mul_inv_cancel, one_mul]
      _ = ⁅b, x⁆ := by
          rw [commutatorElement_mul_right_conj, commutatorElement_eq_one_iff_mul_comm.mpr hbv,
            one_mul, ← hcv, mul_inv_cancel_right]
  have hbC : b ∈ Subgroup.centralizer (Q : Set 𝔾) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hcomm x hx
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hb2 : b ^ 2 = 1 := by
    refine h.eq_one_of_mem_u (hV2 b hbV) fun l hl => ?_
    have hz : ⁅b, l⁆⁻¹ ∈ Z := Z.inv_mem (hBL b hb l hl)
    have hzb : ⁅b, l⁆⁻¹ * b = b * ⁅b, l⁆⁻¹ := hZQ _ hz b hbQ
    have hz2 : (⁅b, l⁆⁻¹) ^ 2 = 1 := h.z2 _ hz
    calc l * b ^ 2 * l⁻¹ = (l * b * l⁻¹) ^ 2 := conj_pow.symm
      _ = (⁅b, l⁆⁻¹ * b) ^ 2 := by rw [hlb l hl]
      _ = (⁅b, l⁆⁻¹) ^ 2 * b ^ 2 := by
          rw [sq, sq, sq, mul_assoc, ← mul_assoc b, ← hzb]
          group
      _ = b ^ 2 := by rw [hz2, one_mul]
  exact hΩ b hbQ hbC hb2

end LastHyp

section VStar

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) (L : Subgroup G)

@[expose] noncomputable def vStarB (α β : Vtx (puAmalgam hTM)) :
    Subgroup (puAmalgam hTM).Universal :=
  ⨆ ρ ∈ {ρ : Vtx (puAmalgam hTM) | (puAmalgam hTM).treeGraph.Adj β ρ ∧
    ¬ ZM (puAmalgam hTM) ρ ≤ Bloc hTM L α}, ZM (puAmalgam hTM) ρ

@[expose] noncomputable def vStar (α : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  ⨆ β ∈ (puAmalgam hTM).treeGraph.neighborSet α, vStarB hTM L α β

end VStar

section Comm

variable {𝔾 : Type} [Group 𝔾]

private def commSub (K W N : Subgroup 𝔾) (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {g | g ∈ K ∧ ∀ w ∈ W, ⁅g, w⁆ ∈ N}
  one_mem' := ⟨K.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact N.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨K.mul_mem hg.1 hg'.1, fun w hw => by
    rw [commutatorElement_mul_left_conj]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hg.1) _).mp (hg'.2 w hw)) (hg.2 w hw)⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun w hw => by
    have h := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hg.1)) _).mp
      (N.inv_mem (hg.2 w hw))
    have e : ⁅g⁻¹, w⁆ = g⁻¹ * ⁅g, w⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h⟩

end Comm

section I4610

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commutator_vStar_qv_le_cfg (h469 : I469Cfg M T L φ) (c : Hyp46 M T L φ)
    {α : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx _ α) :
    ⁅vStar c.pu.le L α, Qv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hUN : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Uloc h.le L α : Set _) := hψ.1
  have hle : vStar h.le L α ≤ commSub (stab (puAmalgam h.le) α) (Qv _ α) (Uloc h.le L α) hUN := by
    refine iSup₂_le fun β hβ => iSup₂_le fun ρ hρ => ?_
    have hαβ : (puAmalgam h.le).treeGraph.Adj α β := hβ
    obtain ⟨hβρ, hρB⟩ := hρ
    obtain ⟨-, -, -, h9⟩ := h469 ⟨h, hmin, hb4, hφ⟩ α β hα hαβ
    obtain ⟨-, hUU, -⟩ := h9 ρ hβρ hρB
    have hρ : IsMVtx (puAmalgam h.le) ρ := by
      have h1 := isMVtx_iff_of_adj _ hαβ
      have h2 := isMVtx_iff_of_adj _ hβρ
      tauto
    have hαρ : α ≠ ρ := by
      rintro rfl
      exact hρB (zm_le_bloc h (by omega) hα)
    have hd : (puAmalgam h.le).treeGraph.dist ρ α = 2 := by
      rw [tdist_comm]
      exact dist_eq_two_of_adj_adj _ hαβ hβρ hαρ
    have hZK : ZM (puAmalgam h.le) ρ ≤ stab _ α :=
      (zm_le_qv_of_dist_le_three hb4 hρ (by omega)).trans (qv_le_stab _ α)
    have hQβ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
    have hcomm : ⁅ZM (puAmalgam h.le) ρ, Qv _ α⁆ ≤ Uloc h.le L α := by
      calc ⁅ZM (puAmalgam h.le) ρ, Qv _ α⁆ ≤ ⁅ZM (puAmalgam h.le) ρ, Qv _ β⁆ :=
            Subgroup.commutator_mono le_rfl hQβ
        _ = Usup _ ρ β := by rw [Usup, zv_of_isMVtx _ hρ]
        _ = Usup _ α β := hUU
        _ = ⁅Uloc h.le L α, Qv _ β⁆ := usup_eq_commutator_uloc h hfull hα hαβ
        _ ≤ Uloc h.le L α :=
            Subgroup.le_normalizer_iff_commutator_le_left.mp
              ((qv_le_stab_of_adj _ hαβ.symm).trans hUN)
    intro z hz
    exact ⟨hZK hz, fun x hx => hcomm (Subgroup.commutator_mem_commutator hz hx)⟩
  rw [Subgroup.commutator_le]
  intro b hb x hx
  exact (hle hb).2 x hx

theorem vStar_inf_bloc_le_cfg (h463 : I463) (h465 : I465) (h466b : I466b) (h467 : I467)
    (h469 : I469Cfg M T L φ) (c : Hyp46 M T L φ) {α : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx _ α) :
    vStar c.pu.le L α ⊓ Bloc c.pu.le L α ≤ ZM (puAmalgam c.pu.le) α := by
  obtain ⟨β, hαβ⟩ := exists_adj (puAmalgam c.pu.le) α
  obtain ⟨hQL, hVV, -, -⟩ := h469 c α β hα hαβ
  obtain ⟨ψ, hψs, hψU⟩ := exists_natural_Uloc c.pu c.via hα
  have hLH := lastHyp_of h463 h465 h466b h467 c hα hψs hψU hQL
  have hB := h467 G M T L F φ c α hα
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  refine hLH.le_z_of_comm (inf_le_right.trans hB.le)
    (fun b hb' l hl => ((mem_bloc_iff c.pu hb hα).mp hb'.2).2 l hl) ?_ ?_ ?_
  · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (commutator_vStar_qv_le_cfg h469 c hα)
  · intro v hv
    rw [← hVV]
    exact sq_mem_commutator_vv c.pu c.pu.critDist_pos hv
  · intro x hxQ hxC hx2
    rw [← xm_eq_zm c.pu hfull hα, XM, omegaOneCenterOf, omegaOneOf]
    exact Subgroup.subset_closure ⟨⟨hxQ, hxC⟩, hx2⟩

end I4610

end CFSG.Quasithin.MS93.S46
