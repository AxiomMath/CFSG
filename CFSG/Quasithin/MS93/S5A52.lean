module

public import CFSG.Quasithin.MS93.S38EBase
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5

section GroupTheory

variable {Γ : Type*} [Group Γ]

private theorem le_normalizer_of_conj'' {S E : Subgroup Γ}
    (h : ∀ g ∈ S, ∀ e ∈ E, g * e * g⁻¹ ∈ E) : S ≤ Subgroup.normalizer (E : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨h g hg e, fun he => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ he
  simpa [mul_assoc] using this

private theorem conj_mem_of_commutator_mem'' {K : Subgroup Γ} {x l : Γ} (hx : x ∈ K)
    (hxl : ⁅x, l⁆ ∈ K) : l * x * l⁻¹ ∈ K := by
  have e : l * x * l⁻¹ = ⁅x, l⁆⁻¹ * x := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact K.mul_mem (K.inv_mem hxl) hx

end GroupTheory

section Amalgam

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem commutator_zm_eq_bot_of_lt (h : Hyp20 X) {γ γ' : Vtx X} (hγ : IsMVtx X γ)
    (hγ' : IsMVtx X γ') (hd : X.treeGraph.dist γ γ' < critDist X) :
    ⁅ZM X γ, ZM X γ'⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (zm_le_qv_of_dist_lt X hγ hd).trans ?_
  rw [Subgroup.le_centralizer_iff]
  exact zm_le_centralizer_qv X h hγ'

theorem commutator_vv_eq_bot (h : Hyp20 X) (hb : 4 < critDist X) {α : Vtx X}
    (hα : IsMVtx X α) : ⁅Vv X α, Vv X α⁆ = ⊥ := by
  rw [eq_bot_iff, S38E.vv_eq_iSup]
  refine S38E.commutator_iSup_le _ (fun _ => ?_) (fun ρ ρ' => ?_)
  · rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
    exact le_top
  · obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm X hα ρ.2
    obtain ⟨γ', hγ', hdγ', hle'⟩ := S38E.exists_zv_le_zm X hα ρ'.2
    have hd : X.treeGraph.dist γ γ' < critDist X := by
      have := dist_triangle X γ α γ'
      rw [tdist_comm X γ α] at this
      omega
    rw [← commutator_zm_eq_bot_of_lt X h hγ hγ' hd]
    exact Subgroup.commutator_mono hle hle'

theorem commutator_xm_vv_eq_bot_of {α : Vtx X} (hVQ : ⁅Vv X α, Qv X α⁆ ≤ centerOf (Vv X α))
    (α' γ : Vtx X) :
    ⁅⁅XM X α' ⊓ Qv X α, Vv X α ⊓ Qv X γ⁆, Vv X α ⊓ Qv X γ⁆ = ⊥ := by
  have h1 : ⁅XM X α' ⊓ Qv X α, Vv X α ⊓ Qv X γ⁆ ≤ centerOf (Vv X α) := by
    refine le_trans ?_ hVQ
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono inf_le_left inf_le_right
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  have hxc := (h1 hx).2
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.1 hxc y hy.1).symm

theorem commutator_vv_le_xm_of (h : Hyp20 X) (hb : 2 < critDist X) {α : Vtx X}
    (hα : IsMVtx X α) (hVQ : ⁅Vv X α, Qv X α⁆ ≤ centerOf (Vv X α)) :
    ⁅Vv X α, Vv X α⁆ ≤ XM X α := by
  set V := Vv X α with hV
  set Q := Qv X α with hQ
  have hVQα : V ≤ Q := S38E.vv_le_qv X hb hα
  have hVV : ⁅V, V⁆ ≤ centerOf V := (Subgroup.commutator_mono le_rfl hVQα).trans hVQ
  have hcen : ∀ c ∈ centerOf V, ∀ v ∈ V, c * v = v * c := fun c hc v hv =>
    (Subgroup.mem_centralizer_iff.1 hc.2 v hv).symm
  have h1 : ⁅⁅V, Q⁆, V⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcen x (hVQ hx) y hy
  have h2 : ⁅⁅Q, V⁆, V⁆ = ⊥ := by rw [Subgroup.commutator_comm Q V]; exact h1
  have h3 : ⁅⁅V, V⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  let S : Subgroup X.Universal :=
    { carrier := {v | v ∈ V ∧ v * v ∈ Subgroup.centralizer (V : Set X.Universal)}
      one_mem' := ⟨V.one_mem, by rw [mul_one]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro v w ⟨hv, hv2⟩ ⟨hw, hw2⟩
        refine ⟨V.mul_mem hv hw, ?_⟩
        have hc : ⁅w, v⁆ ∈ centerOf V := hVV (Subgroup.commutator_mem_commutator hw hv)
        have e : v * w * (v * w) = ⁅w, v⁆ * (v * v) * (w * w) := by
          have e1 : w * v = ⁅w, v⁆ * v * w := by
            simp only [commutatorElement_def]
            group
          calc v * w * (v * w) = v * (w * v) * w := by group
            _ = v * (⁅w, v⁆ * v * w) * w := by rw [e1]
            _ = (v * ⁅w, v⁆) * v * w * w := by group
            _ = (⁅w, v⁆ * v) * v * w * w := by rw [hcen _ hc v hv]
            _ = ⁅w, v⁆ * (v * v) * (w * w) := by group
        rw [e]
        exact mul_mem (mul_mem hc.2 hv2) hw2
      inv_mem' := by
        rintro v ⟨hv, hv2⟩
        refine ⟨V.inv_mem hv, ?_⟩
        rw [← _root_.mul_inv_rev]
        exact inv_mem hv2 }
  have hVS : V ≤ S := by
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm X hα hρ
    have hab := isElemAbelian_zm X h (by omega) hγ
    intro z hz
    have hzγ := hle hz
    refine ⟨S38E.zm_le_vv X hγ hdγ hzγ, ?_⟩
    rw [← pow_two, hab.2 z hzγ]
    exact Subgroup.one_mem _
  rw [Subgroup.commutator_le]
  intro v hv w hw
  refine Subgroup.subset_closure ⟨⟨hVQα (V.commutator_mem_commutator hv hw |> fun h' =>
    (hVV h').1), ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have := h3 ▸ Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hv hw) hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · have hc : ⁅v, w⁆ ∈ centerOf V := hVV (Subgroup.commutator_mem_commutator hv hw)
    have hv2 := (hVS hv).2
    have e : ⁅v * v, w⁆ = ⁅v, w⁆ * ⁅v, w⁆ := by
      simp only [commutatorElement_def]
      have hcw := hcen _ hc w hw
      have hcv := hcen _ hc v hv
      calc v * v * w * (v * v)⁻¹ * w⁻¹ = v * (v * w * v⁻¹ * w⁻¹) * w * v⁻¹ * w⁻¹ := by group
        _ = (v * w * v⁻¹ * w⁻¹) * v * w * v⁻¹ * w⁻¹ := by
          rw [show v * w * v⁻¹ * w⁻¹ = ⁅v, w⁆ by simp [commutatorElement_def]] at *
          rw [hcv]
        _ = v * w * v⁻¹ * w⁻¹ * (v * w * v⁻¹ * w⁻¹) := by group
    rw [pow_two, ← e, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hv2 w hw).symm

theorem commutator_vv_qv_le_center_of (h : Hyp20 X) (hb : 2 < critDist X) {α β : Vtx X}
    (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β) {N : Subgroup X.Universal}
    (hN : stab X α = N ⊔ Qv X β)
    (hdich : ⁅⁅Vv X α, Qv X α⁆ ⊔ ZM X α, N⁆ ≤ ZM X α ∨
      ⁅Vv X α, N⁆ ≤ ⁅Vv X α, Qv X α⁆ ⊔ ZM X α) :
    ⁅Vv X α, Qv X α⁆ ≤ centerOf (Vv X α) := by
  set V := Vv X α with hVdef
  set Q := Qv X α with hQdef
  set Vβ := Vi X β 1 with hVβdef
  have hβ : ¬ IsMVtx X β := (isMVtx_iff_of_adj X hαβ).1 hα
  have hVs : stab X α ≤ Subgroup.normalizer (V : Set X.Universal) :=
    stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ 2) (fun g ρ => vi_smul X g ρ 2) α
  have hQs : stab X α ≤ Subgroup.normalizer (Q : Set X.Universal) := stab_le_normalizer_qv X α
  have hZs : stab X α ≤ Subgroup.normalizer (ZM X α : Set X.Universal) :=
    stab_le_normalizer_zm X α
  have hVQ : V ≤ Q := S38E.vv_le_qv X hb hα
  have hQst : Q ≤ stab X α := qv_le_stab X α
  have hVst : V ≤ stab X α := hVQ.trans hQst
  have hZV : ZM X α ≤ V := S38E.zm_le_vv X hα (by simp)
  have hNst : N ≤ stab X α := hN ▸ le_sup_left
  have hTs : Qv X β ≤ stab X α := hN ▸ le_sup_right
  have hQβ : Q ≤ Qv X β := qv_le_qv X h hα hαβ
  have hTVβ : Qv X β ≤ Subgroup.normalizer (Vβ : Set X.Universal) :=
    (qv_le_stab X β).trans (stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ 1)
      (fun g ρ => vi_smul X g ρ 1) β)
  have hVβV : Vβ ≤ V := S38E.vi_one_le_vv X hαβ
  have hZVβ : ZM X α ≤ Vβ := by
    rw [← zv_of_isMVtx X hα]
    refine le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist β ρ ≤ 1}) =>
      Zv X ρ) α ?_ le_rfl
    simp only [Set.mem_ofPred_eq]
    rw [tdist_comm X β α, dist_eq_one_of_adj X hαβ]
  have hVβab := S38E.commutator_vi_one_eq_bot X h hb β
  have hVQV : ⁅V, Q⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.1 (hQst.trans hVs)
  set H := ⁅V, Q⁆ ⊔ ZM X α with hHdef
  have hHV : H ≤ V := sup_le hVQV hZV
  have hHs : stab X α ≤ Subgroup.normalizer (H : Set X.Universal) :=
    le_normalizer_sup (S38E.le_normalizer_commutator' hVs hQs) hZs
  rcases hdich with hHN | hVN
  ·
    set N₂ := ⁅Vβ, Q⁆ ⊔ ZM X α with hN₂def
    have hN₂H : N₂ ≤ H := sup_le_sup_right (Subgroup.commutator_mono hVβV le_rfl) _
    have hN₂n : stab X α ≤ Subgroup.normalizer (N₂ : Set X.Universal) := by
      rw [hN]
      refine sup_le (le_normalizer_of_conj'' fun l hl x hx => conj_mem_of_commutator_mem'' hx
        (Subgroup.mem_sup_right (hHN (Subgroup.commutator_mem_commutator (hN₂H hx) hl)))) ?_
      exact le_normalizer_sup (S38E.le_normalizer_commutator' hTVβ (hTs.trans hQs))
        (hTs.trans hZs)
    let K : Subgroup X.Universal :=
      { carrier := {g | g ∈ V ∧ g ∈ Subgroup.normalizer (N₂ : Set X.Universal) ∧
          ∀ a ∈ Q, ⁅g, a⁆ ∈ N₂}
        one_mem' := ⟨V.one_mem, Subgroup.one_mem _, fun a _ => by
          rw [commutatorElement_one_left]; exact N₂.one_mem⟩
        mul_mem' := by
          rintro g k ⟨hgV, hg, hg'⟩ ⟨hkV, hk, hk'⟩
          refine ⟨V.mul_mem hgV hkV, Subgroup.mul_mem _ hg hk, fun a ha => ?_⟩
          have e : ⁅g * k, a⁆ = (g * ⁅k, a⁆ * g⁻¹) * ⁅g, a⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact N₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hg _).mp (hk' a ha)) (hg' a ha)
        inv_mem' := by
          rintro g ⟨hgV, hg, hg'⟩
          refine ⟨V.inv_mem hgV, Subgroup.inv_mem _ hg, fun a ha => ?_⟩
          have e : ⁅g⁻¹, a⁆ = g⁻¹ * ⁅g, a⁆⁻¹ * g⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp
            (N₂.inv_mem (hg' a ha)) }
    have hKs : stab X α ≤ Subgroup.normalizer (K : Set X.Universal) := by
      refine le_normalizer_of_conj'' fun g hg x hx => ?_
      obtain ⟨hxV, hxN, hx'⟩ := hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hVs hg) x).mp hxV,
        mul_mem (mul_mem (hN₂n hg) hxN) (inv_mem (hN₂n hg)), fun a ha => ?_⟩
      have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQs (inv_mem hg)) a).mp ha
      have e : ⁅g * x * g⁻¹, a⁆ = g * ⁅x, g⁻¹ * a * g⁻¹⁻¹⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hN₂n hg) _).mp (hx' _ ha')
    have hVK : V ≤ K := by
      refine S38E.vv_le_of_vi_le X hαβ hKs fun b hb => ⟨hVβV hb, hN₂n (hVst (hVβV hb)),
        fun q hq => Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb hq)⟩
    have hVQN₂ : ⁅V, Q⁆ ≤ N₂ := Subgroup.commutator_le.mpr fun v hv q hq => (hVK hv).2.2 q hq
    have hN₂Vβ : N₂ ≤ Vβ :=
      sup_le (Subgroup.le_normalizer_iff_commutator_le_left.1 (hQβ.trans hTVβ)) hZVβ
    have hCVβ : ⁅V, Q⁆ ≤ Vβ := hVQN₂.trans hN₂Vβ
    have hcs : stab X α ≤ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ((⁅V, Q⁆ : Subgroup X.Universal) : Set X.Universal) :
          Subgroup X.Universal) : Set X.Universal) := by
      refine le_normalizer_of_conj'' fun g hg x hx => ⟨(Subgroup.mem_normalizer_iff.mp
        (hVs hg) x).mp hx.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
      have hc' : g⁻¹ * c * g⁻¹⁻¹ ∈ ⁅V, Q⁆ :=
        (Subgroup.mem_normalizer_iff.mp (S38E.le_normalizer_commutator' hVs hQs
          (inv_mem hg)) c).mp hc
      have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hc'
      calc c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g⁻¹⁻¹) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * c * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * c := by group
    have hVC : V ≤ V ⊓ Subgroup.centralizer ((⁅V, Q⁆ : Subgroup X.Universal) :
        Set X.Universal) := by
      refine S38E.vv_le_of_vi_le X hαβ hcs (le_inf hVβV fun b hb => ?_)
      refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
      have := Subgroup.commutator_mem_commutator hb (hCVβ hc)
      rw [hVβab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    refine le_inf hVQV fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hVC hy).2 x hx).symm
  ·
    have hKn : stab X α ≤ Subgroup.normalizer ((Vβ ⊔ H : Subgroup X.Universal) :
        Set X.Universal) := by
      rw [hN]
      refine sup_le ?_ (le_normalizer_sup hTVβ (hTs.trans hHs))
      exact le_normalizer_of_conj'' fun l hl x hx => conj_mem_of_commutator_mem'' hx
        (Subgroup.mem_sup_right (hVN (Subgroup.commutator_mem_commutator
          (sup_le hVβV hHV hx) hl)))
    have hVK : V ≤ Vβ ⊔ H := S38E.vv_le_of_vi_le X hαβ hKn le_sup_left
    have hVK' : V ≤ Vβ ⊔ ⁅V, Q⁆ := hVK.trans (sup_le le_sup_left (sup_le le_sup_right
      (hZVβ.trans le_sup_left)))
    have hVeq : V = Vβ :=
      eq_of_le_sup_commutator (isNilpotent_qv X h hβ) (hVβV.trans (hVQ.trans hQβ))
        (hVQ.trans hQβ) hQβ (hQβ.trans hTVβ) hVβV hVK'
    refine le_inf hVQV fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hx' : x ∈ Vβ := hVeq ▸ hVQV hx
    have hy' : y ∈ Vβ := hVeq ▸ hy
    have := Subgroup.commutator_mem_commutator hy' hx'
    rw [hVβab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

theorem commutator_vv_qv_le_center_of_pairs {α : Vtx X} (hα : IsMVtx X α)
    (hpair : ∀ γ δ : Vtx X, IsMVtx X γ → IsMVtx X δ → X.treeGraph.dist α γ ≤ 2 →
      X.treeGraph.dist α δ ≤ 2 →
        ⁅ZM X γ, Qv X α⁆ ≤ Subgroup.centralizer (ZM X δ : Set X.Universal)) :
    ⁅Vv X α, Qv X α⁆ ≤ centerOf (Vv X α) := by
  set V := Vv X α with hVdef
  set Q := Qv X α with hQdef
  have hVs : stab X α ≤ Subgroup.normalizer (V : Set X.Universal) :=
    stab_le_normalizer_of_smul X (F := fun ρ => Vi X ρ 2) (fun g ρ => vi_smul X g ρ 2) α
  have hQst : Q ≤ stab X α := qv_le_stab X α
  have hVQV : ⁅V, Q⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.1 (hQst.trans hVs)
  have hcent : ∀ γ, IsMVtx X γ → X.treeGraph.dist α γ ≤ 2 →
      ⁅ZM X γ, Q⁆ ≤ Subgroup.centralizer (V : Set X.Universal) := by
    intro γ hγ hdγ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ ((⨆ ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}, Zv X ρ :
        Subgroup X.Universal) : Set X.Universal) := hy
    have hle : (⨆ ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}, Zv X ρ : Subgroup X.Universal) ≤
        Subgroup.centralizer ({x} : Set X.Universal) := by
      refine iSup₂_le fun ρ hρ => ?_
      obtain ⟨δ, hδ, hdδ, hle⟩ := S38E.exists_zv_le_zm X hα hρ
      refine hle.trans fun w hw => Subgroup.mem_centralizer_singleton_iff.2 ?_
      exact Subgroup.mem_centralizer_iff.1 (hpair γ δ hγ hδ hdγ hdδ hx) w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy')
  let S : Subgroup X.Universal :=
    { carrier := {v | v ∈ V ∧ ∀ q ∈ Q, ⁅v, q⁆ ∈ Subgroup.centralizer (V : Set X.Universal)}
      one_mem' := ⟨V.one_mem, fun q _ => by
        rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
        refine ⟨V.mul_mem hv hw, fun q hq => ?_⟩
        have e : ⁅v * w, q⁆ = (v * ⁅w, q⁆ * v⁻¹) * ⁅v, q⁆ := by
          simp only [commutatorElement_def]
          group
        have hc : v * ⁅w, q⁆ * v⁻¹ = ⁅w, q⁆ := by
          rw [Subgroup.mem_centralizer_iff.1 (hw' q hq) v hv, mul_inv_cancel_right]
        rw [e, hc]
        exact mul_mem (hw' q hq) (hv' q hq)
      inv_mem' := by
        rintro v ⟨hv, hv'⟩
        refine ⟨V.inv_mem hv, fun q hq => ?_⟩
        have e : ⁅v⁻¹, q⁆ = v⁻¹ * ⁅v, q⁆⁻¹ * v⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        have hc : v⁻¹ * ⁅v, q⁆⁻¹ * v⁻¹⁻¹ = ⁅v, q⁆⁻¹ := by
          rw [Subgroup.mem_centralizer_iff.1 (inv_mem (hv' q hq)) _ (V.inv_mem hv),
            mul_inv_cancel_right]
        rw [e, hc]
        exact inv_mem (hv' q hq) }
  have hVS : V ≤ S := by
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨γ, hγ, hdγ, hle⟩ := S38E.exists_zv_le_zm X hα hρ
    intro z hz
    refine ⟨S38E.zm_le_vv X hγ hdγ (hle hz), fun q hq => ?_⟩
    exact hcent γ hγ hdγ (Subgroup.commutator_mem_commutator (hle hz) hq)
  rw [Subgroup.commutator_le]
  intro v hv q hq
  exact ⟨hVQV (Subgroup.commutator_mem_commutator hv hq), (hVS hv).2 q hq⟩

end Amalgam

end S5

end CFSG.Quasithin.MS93
