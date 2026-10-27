module

public import CFSG.Quasithin.MS93.S4A441D
import CFSG.Quasithin.MS93.S46SL2Sec
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A.X441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Odd

variable {Γ : Type*} [Group Γ]

theorem eq_one_of_odd {U D : Subgroup Γ} (hUD : U ⊓ D = ⊥)
    (hcomm : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u) {k : Γ} (hk : Odd (orderOf k))
    (hkU : ∀ u ∈ U, k * u * k⁻¹ ∈ U) {x u₀ d : Γ} (hu₀ : u₀ ∈ U) (hd : d ∈ D) (hd2 : d * d = 1)
    (hkd : k * d * k⁻¹ = d) (hx : k * x * k⁻¹ = x * u₀ * d) : d = 1 := by
  have hkdj : ∀ j : ℕ, k * d ^ j * k⁻¹ = d ^ j := fun j => by
    rw [← conj_pow, hkd]
  have key : ∀ j : ℕ, ∃ u ∈ U, k ^ j * x * (k ^ j)⁻¹ = x * u * d ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨u, hu, hj⟩ := ih
      have hc := hcomm _ (hkU u hu) d hd
      refine ⟨u₀ * (k * u * k⁻¹), U.mul_mem hu₀ (hkU u hu), ?_⟩
      calc k ^ (j + 1) * x * (k ^ (j + 1))⁻¹ = k * (k ^ j * x * (k ^ j)⁻¹) * k⁻¹ := by group
        _ = k * (x * u * d ^ j) * k⁻¹ := by rw [hj]
        _ = (k * x * k⁻¹) * (k * u * k⁻¹) * (k * d ^ j * k⁻¹) := by group
        _ = x * u₀ * (d * (k * u * k⁻¹)) * d ^ j := by rw [hx, hkdj j]; group
        _ = x * (u₀ * (k * u * k⁻¹)) * d ^ (j + 1) := by rw [← hc, pow_succ']; group
  obtain ⟨u, hu, hm⟩ := key (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
  have hum : u * d ^ orderOf k = 1 := by
    have := congrArg (x⁻¹ * ·) hm
    simpa [mul_assoc] using this.symm
  have hdm : d ^ orderOf k = 1 := by
    have h1 : d ^ orderOf k = u⁻¹ := eq_inv_of_mul_eq_one_right hum
    have h2 : d ^ orderOf k ∈ U ⊓ D := ⟨h1 ▸ U.inv_mem hu, D.pow_mem hd _⟩
    rw [hUD] at h2
    exact (Subgroup.mem_bot).mp h2
  obtain ⟨r, hr⟩ := hk
  rw [hr, pow_succ, pow_mul, sq, hd2, one_pow, one_mul] at hdm
  exact hdm

end Odd

section Row

variable {F : Type} [Field F]

private noncomputable def rot3 : SL3 F := rootElt 1 2 1 * rootElt 2 1 1

private theorem rot3_mulVec [CharP F 2] (v : Fin 3 → F) :
    ((rot3 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 0, v 2, v 1 + v 2] := by
  rw [rot3, coe_mul_SL3, ← Matrix.mulVec_mulVec, rootElt_mulVec (by decide),
    rootElt_mulVec (by decide)]
  funext i
  fin_cases i
  · simp
  · simp
    linear_combination CharTwo.add_self_eq_zero (v 1)
  · simp
    ring

private theorem rot3_mem_rowLevi : (rot3 : SL3 F) ∈ (rowLevi : Subgroup (SL3 F)) :=
  Subgroup.mul_mem _ (rootElt_mem_rowLevi (by decide) (by decide) _)
    (rootElt_mem_rowLevi (by decide) (by decide) _)

private theorem rot3_pow_three [CharP F 2] : (rot3 : SL3 F) ^ 3 = 1 := by
  have hmv : ∀ w : Fin 3 → F,
      (((rot3 : SL3 F) ^ 3 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    intro w
    rw [pow_succ, pow_succ, pow_one, coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, rot3_mulVec, rot3_mulVec, rot3_mulVec]
    funext i
    fin_cases i
    · simp
    · simp
      linear_combination CharTwo.add_self_eq_zero (w 2)
    · simp
      linear_combination CharTwo.add_self_eq_zero (w 1) + CharTwo.add_self_eq_zero (w 2)
  apply Subtype.ext
  ext i j
  have := congrFun (hmv (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this, coe_one_SL3]
  simp [Matrix.one_apply, Pi.single_apply]

private theorem odd_orderOf_rot3 [CharP F 2] : Odd (orderOf (rot3 : SL3 F)) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one rot3_pow_three)

private theorem eq_zero_of_rot3 [CharP F 2] {v : Fin 3 → F} (hv0 : v 0 = 0)
    (hv : ((rot3 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : v = 0 := by
  rw [rot3_mulVec] at hv
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp at h1 h2
  funext i
  fin_cases i
  · simpa using hv0
  · simpa using h2
  · simp
    rw [h1, h2]

end Row

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem usup_eq_of_isSecD (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : L441.IsSecD h.le L γ ψ true (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C) :
    Usup 𝔛 α β = Usup 𝔛 γ β := by
  classical
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := h.centHyp
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := hφ.1
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card, hn])
  obtain ⟨x, hx, y₀, hy₀, hxy₀⟩ : ∃ x ∈ ZM 𝔛 α, ∃ y₀ ∈ Qv 𝔛 γ, ⁅x, y₀⁆ ∉ Dloc h.le L γ := by
    by_contra hcon
    push Not at hcon
    exact hH (Subgroup.commutator_le.mpr hcon)
  obtain ⟨ψ', hψ's, hψ', hrow, hcl, hUD, hcoord⟩ :=
    L441.dual_point h hfull hb hφ hα hγ hαβ hβγ hψs hψ hs hx hy₀ hxy₀
  obtain ⟨-, -, hUUD⟩ := L441.dual_local h hfull hC hb hφ hα hγ hαβ hβγ hH hψs hψ hs
  obtain ⟨-, -, -, -, hCK⟩ := hs
  have hγs := finite_stab h hγ
  have hQs : Qv 𝔛 γ ≤ stab 𝔛 γ := qv_le_stab _ γ
  have hUs : Uloc h.le L γ ≤ stab 𝔛 γ :=
    (uloc_le_zm h hfull hγ).trans ((zm_le_qv_self _ hγ hb0).trans hQs)
  have hDn := stab_le_normalizer_dloc h γ
  have hUn := stab_le_normalizer_uloc h γ
  have hUc : Uloc h.le L γ ≤ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘) :=
    (uloc_le_zm h hfull hγ).trans (zm_le_centralizer_qv _ h20 hγ)
  have hDQ : Dloc h.le L γ ≤ Qv 𝔛 γ := dloc_le_qv h hγ
  have hUDc : ∀ u ∈ Uloc h.le L γ, ∀ d ∈ Dloc h.le L γ, u * d = d * u := fun u hu d hd =>
    (Subgroup.mem_centralizer_iff.mp (hUc hu) d (hDQ hd)).symm
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α ≤ 2 := by
    have := dist_triangle 𝔛 γ β α
    rw [dist_eq_one_of_adj _ hβγ.symm, dist_eq_one_of_adj _ hαβ.symm] at this
    exact this
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 γ := by
    have := zv_le_vv h (α := γ) (ρ := α) hdγα
    rwa [zv_of_isMVtx _ hα] at this
  have hWV : conjCl (stab 𝔛 γ) (ZM 𝔛 α) ≤ Vv 𝔛 γ :=
    L441.conjCl_le_of_le_normalizer' hZαV (stab_le_normalizer_vv h γ)
  have hUV : Uloc h.le L γ ≤ Vv 𝔛 γ := (uloc_le_zm h hfull hγ).trans (zm_le_vv h hγ)
  have hV2 : ∀ v ∈ Vv 𝔛 γ, v * v = 1 := fun v hv => by
    rw [← sq]
    exact (S45.isElemAbelian_vi _ h20 hb0 (δ := γ) (i := 2) (by omega)).2 v hv
  have hxW : x ∈ conjCl (stab 𝔛 γ) (ZM 𝔛 α) := le_conjCl _ _ hx
  have hLs : Ltil h.le L γ ≤ stab 𝔛 γ := ltil_le_stab h γ
  have : Finite ↥(Ltil h.le L γ) := Finite.of_injective _ (Subgroup.inclusion_injective hLs)
  set θ : ↥(Ltil h.le L γ) →* SL3 F := (toSL3 ψ').comp (Subgroup.inclusion hLs) with hθ
  have hθs : Function.Surjective θ := by
    intro g
    obtain ⟨l, hl, hlg⟩ := exists_ltil_toSL3_eq h hfull hγ hψ's hψ' g
    exact ⟨⟨l, hl⟩, hlg⟩
  obtain ⟨a, ha, hodd⟩ := S46.exists_odd_preimage_of_surjective hθs (odd_orderOf_rot3 (F := F))
  set k : 𝔘 := ((a : ↥(Ltil h.le L γ)) : 𝔘) with hk
  have hks : k ∈ stab 𝔛 γ := hLs a.2
  have hψk : toSL3 ψ' ⟨k, hks⟩ = rot3 := ha
  have hkodd : Odd (orderOf k) := by rw [hk, Subgroup.orderOf_coe]; exact hodd
  have hkD : ∀ d ∈ Dloc h.le L γ, k * d * k⁻¹ = d := fun d hd => by
    have := Subgroup.mem_centralizer_iff.mp (dloc_le_centralizer_ltil h hγ hd) k a.2
    rw [this, mul_inv_cancel_right]
  have hc : x⁻¹ * (k * x * k⁻¹) ∈ C := (hrow ⟨k, hks⟩).mp (hψk ▸ rot3_mem_rowLevi)
  have hcUD := hCK x hxW k hks hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hUs.trans hDn)] at hcUD
  obtain ⟨u₀, hu₀, d₀, hd₀, hcud⟩ := hcUD
  have hcud' : u₀ * d₀ = x⁻¹ * (k * x * k⁻¹) := hcud
  have hxk : k * x * k⁻¹ = x * u₀ * d₀ := by
    calc k * x * k⁻¹ = x * (x⁻¹ * (k * x * k⁻¹)) := by group
      _ = x * u₀ * d₀ := by rw [← hcud']; group
  have hd₀V : d₀ ∈ Vv 𝔛 γ := by
    have hcV : x⁻¹ * (k * x * k⁻¹) ∈ Vv 𝔛 γ :=
      (Vv 𝔛 γ).mul_mem ((Vv 𝔛 γ).inv_mem (hWV hxW))
        (hWV ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjCl _ _ hks) x).mp hxW))
    have : d₀ = u₀⁻¹ * (x⁻¹ * (k * x * k⁻¹)) := by rw [← hcud']; group
    rw [this]
    exact (Vv 𝔛 γ).mul_mem ((Vv 𝔛 γ).inv_mem (hUV hu₀)) hcV
  have hd₁ : d₀ = 1 := eq_one_of_odd (uloc_inf_dloc h hφ γ) hUDc hkodd
    (fun u hu => (Subgroup.mem_normalizer_iff.mp (hUn hks) u).mp hu) hu₀ hd₀ (hV2 d₀ hd₀V)
    (hkD d₀ hd₀) hxk
  rw [hd₁, mul_one] at hxk
  have hkS : ∀ y ∈ Qv 𝔛 γ, k * ⁅x, y⁆ * k⁻¹ = ⁅x, k * y * k⁻¹⁆ := by
    intro y hy
    have hy' : k * y * k⁻¹ ∈ Qv 𝔛 γ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ γ hks) y).mp hy
    have hcu : u₀ * (k * y * k⁻¹) = (k * y * k⁻¹) * u₀ :=
      (Subgroup.mem_centralizer_iff.mp (hUc hu₀) _ hy').symm
    calc k * ⁅x, y⁆ * k⁻¹ = ⁅k * x * k⁻¹, k * y * k⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x * u₀, k * y * k⁻¹⁆ := by rw [hxk]
      _ = ⁅x, k * y * k⁻¹⁆ := by
          simp only [commutatorElement_def]
          calc x * u₀ * (k * y * k⁻¹) * (x * u₀)⁻¹ * (k * y * k⁻¹)⁻¹ =
              x * (u₀ * (k * y * k⁻¹)) * u₀⁻¹ * x⁻¹ * (k * y * k⁻¹)⁻¹ := by group
            _ = x * ((k * y * k⁻¹) * u₀) * u₀⁻¹ * x⁻¹ * (k * y * k⁻¹)⁻¹ := by rw [hcu]
            _ = x * (k * y * k⁻¹) * x⁻¹ * (k * y * k⁻¹)⁻¹ := by group
  have hkU : ∀ t ∈ Usup 𝔛 α β, k * t * k⁻¹ ∈ Usup 𝔛 α β := by
    intro t ht
    rw [← hcl] at ht ⊢
    induction ht using Subgroup.closure_induction with
    | mem r hr =>
      obtain ⟨y, hy, rfl⟩ := hr
      rw [hkS y hy]
      exact Subgroup.subset_closure ⟨_, (Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_qv _ γ hks) y).mp hy, rfl⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ iha ihb
    | inv a _ iha =>
      have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ iha
  have hγβ : 𝔄 γ β := hβγ.symm
  have hUγβ : Usup 𝔛 γ β ≤ Uloc h.le L γ := by
    rw [usup_eq_commutator_uloc h hfull hγ hγβ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hγβ.symm).trans hUn)
  have hdec : ∀ t ∈ Usup 𝔛 α β, ∃ u ∈ Usup 𝔛 γ β, ∃ d ∈ Dloc h.le L γ, u * d = t := by
    intro t ht
    have ht' : t ∈ ((Usup 𝔛 γ β ⊔ Dloc h.le L γ : Subgroup 𝔘) : Set 𝔘) := by
      rw [SetLike.mem_coe, ← hUUD]
      exact Subgroup.mem_sup_left ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hUγβ.trans hUs).trans hDn)] at ht'
    obtain ⟨u, hu, d, hd, hud⟩ := ht'
    exact ⟨u, hu, d, hd, hud⟩
  have hfix : ∀ s ∈ Usup 𝔛 α β, k * s * k⁻¹ = s → s = 1 := by
    intro s hs hks'
    obtain ⟨u, hu, d, hd, rfl⟩ := hdec s hs
    have hku : k * u * k⁻¹ = u := by
      have e : k * (u * d) * k⁻¹ = (k * u * k⁻¹) * (k * d * k⁻¹) := by group
      rw [e, hkD d hd] at hks'
      exact mul_right_cancel hks'
    have huU : u ∈ Uloc h.le L γ := hUγβ hu
    have hku' : k * u * k⁻¹ ∈ Uloc h.le L γ := by rw [hku]; exact huU
    have hvec := natVec_conj hψ' ⟨k, hks⟩ ⟨u, huU⟩ ⟨k * u * k⁻¹, hku'⟩ rfl
    have hsame : (⟨k * u * k⁻¹, hku'⟩ : ↥(Uloc h.le L γ)) = ⟨u, huU⟩ := Subtype.ext hku
    rw [hsame, hψk] at hvec
    have hu0 : natVec hψ' ⟨u, huU⟩ ∈ (coordZero 0 : Submodule F (Fin 3 → F)) := by
      rw [← hcoord, hUUD]
      exact Subgroup.mem_sup_left hu
    have hz := eq_zero_of_rot3 hu0 hvec.symm
    have hu1 : u = 1 := by
      have : (⟨u, huU⟩ : ↥(Uloc h.le L γ)) = 1 :=
        natVec_injective hψ' (by rw [hz, natVec_one])
      exact congrArg Subtype.val this
    subst hu1
    rw [one_mul] at hs ⊢
    have : d ∈ Usup 𝔛 α β ⊓ Dloc h.le L γ := ⟨hs, hd⟩
    rw [hUD] at this
    exact (Subgroup.mem_bot).mp this
  have hfin : Finite ↥(Usup 𝔛 α β ⊓ Uloc h.le L γ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hUs))
  have hmem : ∀ t : ↥(Usup 𝔛 α β), k * (t : 𝔘) * k⁻¹ * (t : 𝔘)⁻¹ ∈
      Usup 𝔛 α β ⊓ Uloc h.le L γ := by
    intro t
    refine ⟨(Usup 𝔛 α β).mul_mem (hkU t t.2) ((Usup 𝔛 α β).inv_mem t.2), ?_⟩
    obtain ⟨u, hu, d, hd, hud⟩ := hdec t t.2
    have e : k * (t : 𝔘) * k⁻¹ * (t : 𝔘)⁻¹ = (k * u * k⁻¹) * u⁻¹ := by
      rw [← hud]
      have e2 : k * (u * d) * k⁻¹ = (k * u * k⁻¹) * (k * d * k⁻¹) := by group
      rw [e2, hkD d hd]
      group
    rw [e]
    exact (Uloc h.le L γ).mul_mem ((Subgroup.mem_normalizer_iff.mp (hUn hks) u).mp (hUγβ hu))
      ((Uloc h.le L γ).inv_mem (hUγβ hu))
  have hinj : Function.Injective (fun t : ↥(Usup 𝔛 α β) =>
      (⟨k * (t : 𝔘) * k⁻¹ * (t : 𝔘)⁻¹, hmem t⟩ : ↥(Usup 𝔛 α β ⊓ Uloc h.le L γ))) := by
    intro t₁ t₂ he
    have he' : k * (t₁ : 𝔘) * k⁻¹ * (t₁ : 𝔘)⁻¹ = k * (t₂ : 𝔘) * k⁻¹ * (t₂ : 𝔘)⁻¹ :=
      congrArg Subtype.val he
    have hs : (t₂ : 𝔘)⁻¹ * t₁ ∈ Usup 𝔛 α β :=
      (Usup 𝔛 α β).mul_mem ((Usup 𝔛 α β).inv_mem t₂.2) t₁.2
    have hfx : k * ((t₂ : 𝔘)⁻¹ * t₁) * k⁻¹ = (t₂ : 𝔘)⁻¹ * t₁ := by
      have e1 : k * ((t₂ : 𝔘)⁻¹ * t₁) * k⁻¹ =
          (k * (t₂ : 𝔘) * k⁻¹)⁻¹ * (k * (t₁ : 𝔘) * k⁻¹) := by group
      have e2 : k * (t₁ : 𝔘) * k⁻¹ = k * (t₂ : 𝔘) * k⁻¹ * (t₂ : 𝔘)⁻¹ * t₁ := by
        have := congrArg (· * (t₁ : 𝔘)) he'
        simpa [mul_assoc] using this
      rw [e1, e2]
      group
    have h1 := hfix _ hs hfx
    apply Subtype.ext
    have : (t₂ : 𝔘)⁻¹ * t₁ = 1 := h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hcard := Nat.card_le_card_of_injective _ hinj
  have hle : Usup 𝔛 α β ≤ Uloc h.le L γ := by
    have heq : Usup 𝔛 α β ⊓ Uloc h.le L γ = Usup 𝔛 α β := by
      have : Finite ↥(Usup 𝔛 α β) := Nat.finite_of_card_ne_zero (by
        rw [card_usup_eq_sq h hφ hC hb hα hαβ]
        exact pow_ne_zero _ Fintype.card_ne_zero)
      exact Subgroup.eq_of_le_of_card_ge inf_le_left hcard
    rw [← heq]
    exact inf_le_right
  have hle' : Usup 𝔛 α β ≤ Usup 𝔛 γ β := by
    intro t ht
    obtain ⟨u, hu, d, hd, rfl⟩ := hdec t ht
    have hdU : d ∈ Uloc h.le L γ := by
      have : d = u⁻¹ * (u * d) := by group
      rw [this]
      exact (Uloc h.le L γ).mul_mem ((Uloc h.le L γ).inv_mem (hUγβ hu)) (hle ht)
    have : d ∈ Uloc h.le L γ ⊓ Dloc h.le L γ := ⟨hdU, hd⟩
    rw [uloc_inf_dloc h hφ γ] at this
    rw [(Subgroup.mem_bot).mp this, mul_one]
    exact hu
  have : Finite ↥(Usup 𝔛 γ β) := Nat.finite_of_card_ne_zero (by
    rw [card_usup_eq_sq h hφ hC hb hγ hγβ]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  exact Subgroup.eq_of_le_of_card_ge hle' (by
    rw [card_usup_eq_sq h hφ hC hb hα hαβ, card_usup_eq_sq h hφ hC hb hγ hγβ])

theorem commutator_zm_qv_eq_usup (hb : 4 < critDist 𝔛) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {α β γ : Vtx 𝔛}
    (hα : IsMVtx 𝔛 α) (hγ : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ)
    (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : L441.IsSecD h.le L γ ψ true (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C) :
    ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ = Usup 𝔛 α β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  obtain ⟨x, hx, y₀, hy₀, hxy₀⟩ : ∃ x ∈ ZM 𝔛 α, ∃ y₀ ∈ Qv 𝔛 γ, ⁅x, y₀⁆ ∉ Dloc h.le L γ := by
    by_contra hcon
    push Not at hcon
    exact hH (Subgroup.commutator_le.mpr hcon)
  obtain ⟨-, -, -, -, hcl, -, -⟩ :=
    L441.dual_point h hfull hb hφ hα hγ hαβ hβγ hψs hψ hs hx hy₀ hxy₀
  apply le_antisymm
  · rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono le_rfl (qv_le_qv _ h.hyp20 hγ hβγ.symm)
  · rw [← hcl, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.commutator_mem_commutator hx hy

end Vertex

end CFSG.Quasithin.MS93.S4A.X441
