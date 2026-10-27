module

public import CFSG.Quasithin.MS93.S4A432J
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A.D432

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Transv

variable {F : Type} [Field F]

theorem eq_of_mulVec_eq {g g' : SL3 F}
    (h : ∀ v, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) : g = g' :=
  Subtype.ext (Matrix.ext_of_mulVec_single fun _ => h _)

theorem mulVec_mulVec_inv (g : SL3 F) (v : Fin 3 → F) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem mulVec_eq_add_of_fix {g : SL3 F}
    (hfix : ∀ p : Fin 3 → F, p 0 = 0 → ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p)
    (v : Fin 3 → F) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      v + v 0 • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] - ![1, 0, 0]) := by
  have hv : v = v 0 • ![1, 0, 0] + (v - v 0 • ![1, 0, 0]) := by abel
  have h0 : (v - v 0 • (![1, 0, 0] : Fin 3 → F)) 0 = 0 := by simp
  conv_lhs => rw [hv]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hfix _ h0, smul_sub]
  abel

theorem mem_rowLevi_of_mulVec_zero {g : SL3 F}
    (h : ∀ v : Fin 3 → F, (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0) :
    g ∈ (rowLevi : Subgroup (SL3 F)) := by
  rw [mem_rowLevi_iff]
  have hinv : ∀ v : Fin 3 → F,
      ((((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v) 0 = v 0 := by
    intro v
    have := h (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
    rw [mulVec_mulVec_inv] at this
    exact this.symm
  funext i
  have := hinv (Pi.single i 1)
  simp only [dualMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
    at this ⊢
  fin_cases i <;> simp_all

theorem exists_rowLevi_mulVec_eq {c c' : Fin 3 → F} (hc0 : c 0 = 0) (hc : c ≠ 0)
    (hc'0 : c' 0 = 0) (hc' : c' ≠ 0) :
    ∃ k ∈ (rowLevi : Subgroup (SL3 F)), ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ c = c' := by
  obtain ⟨a, ha, hac⟩ := exists_rowLevi_mulVec_eq_e1 hc0 hc
  obtain ⟨b, hb, hbc⟩ := exists_rowLevi_mulVec_eq_e1 hc'0 hc'
  refine ⟨b⁻¹ * a, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha, ?_⟩
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hac, ← hbc, Matrix.mulVec_mulVec, ← coe_mul_SL3,
    inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem exists_split {c : Fin 3 → F} (hc0 : c 0 = 0) :
    ∃ c' : Fin 3 → F, c' 0 = 0 ∧ c' ≠ 0 ∧ (c - c') 0 = 0 ∧ c - c' ≠ 0 := by
  by_cases h1 : c = ![0, 1, 0]
  · refine ⟨![0, 0, 1], rfl, ?_, by simp [hc0], ?_⟩
    · intro h; have := congrFun h 2; simp at this
    · rw [h1]; intro h; have := congrFun h 1; simp at this
  · refine ⟨![0, 1, 0], rfl, ?_, by simp [hc0], ?_⟩
    · intro h; have := congrFun h 1; simp at this
    · intro h; exact h1 (sub_eq_zero.mp h)

theorem mulVec_conj_of_transv {k t : SL3 F} (hk : k ∈ (rowLevi : Subgroup (SL3 F)))
    {c : Fin 3 → F} (ht : ∀ v, ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + v 0 • c)
    (v : Fin 3 → F) :
    ((k * t * k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      v + v 0 • (((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ c) := by
  rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ht,
    rowLevi_mulVec_zero (Subgroup.inv_mem _ hk), Matrix.mulVec_add, Matrix.mulVec_smul,
    mulVec_mulVec_inv]

theorem mulVec_mul_of_transv {t₁ t₂ : SL3 F} {c₁ c₂ : Fin 3 → F} (hc₂ : c₂ 0 = 0)
    (h₁ : ∀ v, ((t₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + v 0 • c₁)
    (h₂ : ∀ v, ((t₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + v 0 • c₂) (v : Fin 3 → F) :
    ((t₁ * t₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + v 0 • (c₁ + c₂) := by
  rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, h₂, h₁]
  have : (v + v 0 • c₂) 0 = v 0 := by simp [hc₂]
  rw [this, smul_add]
  abel

end Transv

section Split

variable {Γ : Type*} [Group Γ]

theorem commutator_mem_of_split {S U Z : Subgroup Γ} (hUZ : U ≤ Z)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ a ∈ Z, a * a = 1)
    (hUn : S ≤ Subgroup.normalizer (U : Set Γ)) (hZS : ∀ z ∈ Z, ∀ g ∈ S, ⁅z, g⁆ ∈ U)
    {p t k₁ k₂ q : Γ} (hp : p ∈ S) (ht : t ∈ S) (hk₁ : k₁ ∈ S) (hk₂ : k₂ ∈ S)
    (hpk₁ : p⁻¹ * (k₁⁻¹ * p * k₁) ∈ Z) (hpk₂ : p⁻¹ * (k₂⁻¹ * p * k₂) ∈ Z)
    (ha : ⁅p, t⁆ ∈ Z) (ha₁ : ⁅p, k₁ * t * k₁⁻¹⁆ ∈ Z) (ha₂ : ⁅p, k₂ * t * k₂⁻¹⁆ ∈ Z)
    (hq : ⁅p, q⁆ ∈ U) (htq : t = (k₁ * t * k₁⁻¹) * (k₂ * t * k₂⁻¹) * q) : ⁅p, t⁆ ∈ U := by
  have hconjU : ∀ g ∈ S, ∀ u ∈ U, g * u * g⁻¹ ∈ U :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp (hUn hg) u).mp hu
  have hshift : ∀ k ∈ S, p⁻¹ * (k⁻¹ * p * k) ∈ Z → ⁅p, k * t * k⁻¹⁆ ∈ Z →
      ⁅p, t⁆⁻¹ * ⁅p, k * t * k⁻¹⁆ ∈ U := by
    intro k hk hpk hak
    set z := p⁻¹ * (k⁻¹ * p * k) with hz
    have e1 : ⁅p, k * t * k⁻¹⁆ = k * (p * ⁅z, t⁆ * p⁻¹ * ⁅p, t⁆) * k⁻¹ := by
      rw [hz]; simp only [commutatorElement_def]; group
    have hu1 : p * ⁅z, t⁆ * p⁻¹ ∈ U := hconjU p hp _ (hZS z hpk t ht)
    have e2 : k * (p * ⁅z, t⁆ * p⁻¹ * ⁅p, t⁆) * k⁻¹ =
        (k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹) * (⁅p, t⁆ * ⁅⁅p, t⁆⁻¹, k⁆) := by
      simp only [commutatorElement_def]; group
    have hu2 : k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹ ∈ U := hconjU k hk _ hu1
    have hu3 : ⁅⁅p, t⁆⁻¹, k⁆ ∈ U := hZS _ (Subgroup.inv_mem _ ha) k hk
    rw [e1, e2]
    have e3 : ⁅p, t⁆⁻¹ * ((k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹) * (⁅p, t⁆ * ⁅⁅p, t⁆⁻¹, k⁆)) =
        (k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹) * ⁅⁅p, t⁆⁻¹, k⁆ := by
      have hc := hZab _ (Subgroup.inv_mem _ ha) _ (hUZ hu2)
      calc ⁅p, t⁆⁻¹ * ((k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹) * (⁅p, t⁆ * ⁅⁅p, t⁆⁻¹, k⁆))
          = (⁅p, t⁆⁻¹ * (k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹)) * ⁅p, t⁆ * ⁅⁅p, t⁆⁻¹, k⁆ := by group
        _ = ((k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹) * ⁅p, t⁆⁻¹) * ⁅p, t⁆ * ⁅⁅p, t⁆⁻¹, k⁆ := by rw [hc]
        _ = (k * (p * ⁅z, t⁆ * p⁻¹) * k⁻¹) * ⁅⁅p, t⁆⁻¹, k⁆ := by group
    rw [e3]
    exact Subgroup.mul_mem _ hu2 hu3
  have h1 := hshift k₁ hk₁ hpk₁ ha₁
  have h2 := hshift k₂ hk₂ hpk₂ ha₂
  set t₁ := k₁ * t * k₁⁻¹ with ht₁
  set t₂ := k₂ * t * k₂⁻¹ with ht₂
  have ht₁S : t₁ ∈ S := Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁ ht) (Subgroup.inv_mem _ hk₁)
  have ht₂S : t₂ ∈ S := Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₂ ht) (Subgroup.inv_mem _ hk₂)
  have h3 : (⁅p, t₁⁆ * ⁅p, t₂⁆)⁻¹ * ⁅p, t⁆ ∈ U := by
    have e1 : ⁅p, t⁆ = ⁅p, t₁⁆ * (t₁ * (⁅p, t₂⁆ * (t₂ * ⁅p, q⁆ * t₂⁻¹)) * t₁⁻¹) := by
      conv_lhs => rw [htq]
      simp only [commutatorElement_def]; group
    have hu4 : t₂ * ⁅p, q⁆ * t₂⁻¹ ∈ U := hconjU t₂ ht₂S _ hq
    have e2 : t₁ * (⁅p, t₂⁆ * (t₂ * ⁅p, q⁆ * t₂⁻¹)) * t₁⁻¹ =
        ⁅p, t₂⁆ * (⁅⁅p, t₂⁆⁻¹, t₁⁆ * (t₁ * (t₂ * ⁅p, q⁆ * t₂⁻¹) * t₁⁻¹)) := by
      simp only [commutatorElement_def]; group
    have hu5 : ⁅⁅p, t₂⁆⁻¹, t₁⁆ ∈ U := hZS _ (Subgroup.inv_mem _ ha₂) t₁ ht₁S
    have hu6 : t₁ * (t₂ * ⁅p, q⁆ * t₂⁻¹) * t₁⁻¹ ∈ U := hconjU t₁ ht₁S _ hu4
    rw [e1, e2]
    have e3 : (⁅p, t₁⁆ * ⁅p, t₂⁆)⁻¹ * (⁅p, t₁⁆ * (⁅p, t₂⁆ * (⁅⁅p, t₂⁆⁻¹, t₁⁆ *
        (t₁ * (t₂ * ⁅p, q⁆ * t₂⁻¹) * t₁⁻¹)))) =
        ⁅⁅p, t₂⁆⁻¹, t₁⁆ * (t₁ * (t₂ * ⁅p, q⁆ * t₂⁻¹) * t₁⁻¹) := by group
    rw [e3]
    exact Subgroup.mul_mem _ hu5 hu6
  set a := ⁅p, t⁆ with hadef
  set u₁ := a⁻¹ * ⁅p, t₁⁆ with hu₁
  set u₂ := a⁻¹ * ⁅p, t₂⁆ with hu₂
  set u₃ := (⁅p, t₁⁆ * ⁅p, t₂⁆)⁻¹ * a with hu₃
  have hu₁Z : u₁ ∈ Z := hUZ h1
  have e : a = u₁ * u₂ * u₃ := by
    have ea₁ : ⁅p, t₁⁆ = a * u₁ := by rw [hu₁]; group
    have ea₂ : ⁅p, t₂⁆ = a * u₂ := by rw [hu₂]; group
    have ea : a = ⁅p, t₁⁆ * ⁅p, t₂⁆ * u₃ := by rw [hu₃]; group
    have hc : u₁ * a = a * u₁ := hZab _ hu₁Z _ ha
    calc a = ⁅p, t₁⁆ * ⁅p, t₂⁆ * u₃ := ea
      _ = a * u₁ * (a * u₂) * u₃ := by rw [ea₁, ea₂]
      _ = a * (u₁ * a) * u₂ * u₃ := by group
      _ = a * (a * u₁) * u₂ * u₃ := by rw [hc]
      _ = (a * a) * u₁ * u₂ * u₃ := by group
      _ = u₁ * u₂ * u₃ := by rw [hZ2 a ha, one_mul]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3

end Split

section Count

variable {𝔾 : Type} [Group 𝔾] {L V K₀ : Subgroup 𝔾} {F : Type} [Field F]
  {ψ : ↥L →* ↥(StatedSL 3 F)} {dual : Bool}

theorem eq_of_card_img (N : NatSec L V K₀ ψ dual) {K B Z : Subgroup 𝔾} [Finite ↥Z]
    (hKB : K ≤ B) (hBZ : B ≤ Z) (hBV : B ≤ V) (hKK₀ : K ≤ K₀)
    (hZ : Nat.card ↥Z = Nat.card F * Nat.card ↥K) (himg : Nat.card F ≤ Nat.card ↥(N.img B)) :
    B = Z := by
  have hfinB : Finite ↥B := Finite.of_injective _ (Subgroup.inclusion_injective hBZ)
  set f : ↥B →* Multiplicative (Fin 3 → F) := N.β.comp (Subgroup.inclusion hBV) with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have hfinR : Finite ↥f.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective f)
  have hrange : Nat.card ↥(N.img B) ≤ Nat.card ↥f.range := by
    refine Nat.card_le_card_of_injective
      (fun z => ⟨Multiplicative.ofAdd (z : Fin 3 → F), ?_⟩) ?_
    · obtain ⟨v, hvB, hvV, hv⟩ := N.mem_img.mp z.2
      refine ⟨⟨v, hvB⟩, ?_⟩
      rw [hf, MonoidHom.comp_apply, ← hv, N.coord_of_mem hvV]
      rfl
    · intro a b hab
      have := congrArg (fun x : ↥f.range => Multiplicative.toAdd (x : Multiplicative (Fin 3 → F)))
        hab
      exact Subtype.ext this
  have hker : Nat.card ↥K ≤ Nat.card ↥f.ker := by
    have hfinK : Finite ↥f.ker := Finite.of_injective _ (Subgroup.subtype_injective _)
    refine Nat.card_le_card_of_injective (fun k => ⟨⟨k, hKB k.2⟩, ?_⟩) ?_
    · show N.β (Subgroup.inclusion hBV ⟨k, hKB k.2⟩) = 1
      exact (N.ker _).mpr (hKK₀ k.2)
    · intro a b hab
      have := congrArg (fun x : ↥f.ker => ((x : ↥B) : 𝔾)) hab
      exact Subtype.ext this
  have hle : Nat.card ↥Z ≤ Nat.card ↥B := by
    rw [hZ, ← h1, mul_comm (Nat.card ↥f.ker)]
    exact Nat.mul_le_mul (himg.trans hrange) hker
  exact Subgroup.eq_of_le_of_card_ge hBZ hle

end Count

namespace Ctx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  {α₀ α₀' : Vtx (puAmalgam h.le)} (c : Ctx h φ α₀ α₀')
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem commutator_zm_stab_le {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) :
    ⁅ZM 𝔛 μ, stab 𝔛 μ⁆ ≤ Uloc h.le L μ := by
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hZs : ZM 𝔛 μ ≤ stab 𝔛 μ := (zm_le_qv_self _ hμ h.critDist_pos).trans (qv_le_stab _ μ)
  rw [zm_eq_uloc_sup_zloc h c.full hμ] at hZs ⊢
  refine commutator_sup_left_le ((le_sup_left.trans hZs).trans hUn)
    ((le_sup_right.trans hZs).trans hUn) ?_ ?_
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hUn
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (zloc_le_centralizer_stab h c.full hμ)]
    exact bot_le

theorem commutator_commutator_pv_le {μ ν : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) :
    ⁅⁅Pv 𝔛 μ, Qv 𝔛 ν⁆, Qv 𝔛 ν⁆ ≤ Uloc h.le L μ := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hb2 := c.b2
  have hTs : Qv 𝔛 ν ≤ stab 𝔛 μ := qv_le_stab_of_adj _ hμν.symm
  have hPs : Pv 𝔛 μ ≤ stab 𝔛 μ :=
    (pv_le_vv h hμ).trans ((vv_le_qv h hb2 hμ).trans (qv_le_stab _ μ))
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  obtain ⟨hUZ, hUq, -, hrel⟩ := c.edge hμ hμν
  obtain ⟨ψ, hψs, hU, hP⟩ := c.exists_dual hμ
  have hfin : Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 ν))) = 2 := by
    have := hUq
    rw [usup_eq_commutator_uloc h c.full hμ hμν, card_commutator_eq hU hTs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have hfin0 : Module.finrank F ↥(coordZero 0 : Submodule F (Fin 3 → F)) = 2 := by
    have := card_coordZero_zero (F := F)
    rw [Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  obtain ⟨s, hs⟩ := exists_map_plane_eq hfin hfin0
  set ψ' := conjSL s ψ with hψ'
  have hψ's : Function.Surjective ψ' := conjSL_surjective hψs
  have hU' := isSumOfNaturalModulesVia_conjSL hU s
  have hP' := isSumOfNaturalModulesVia_conjSL_true hP s
  have hcomm : commN (natImage ψ' (Qv 𝔛 ν)) = coordZero 0 := by
    rw [hψ', natImage_conjSL', commN_map_conj, hs]
  have hTQ : ¬ Qv 𝔛 ν ≤ Qv 𝔛 μ := by
    intro hle
    have h1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hrel] at h1
    have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hfixN : fixN (natImage ψ' (Qv 𝔛 ν)) = coordZero 0 := by
    rw [fixN_eq_commN_of_le_qv h c.full c.hyp.2.2 hμ hμν hUZ hUq hU' le_rfl hTQ, hcomm]
  have hfixT : ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν → ∀ p : Fin 3 → F, p 0 = 0 →
      ((toSL3 ψ' t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p := by
    intro t ht p hp
    have hp' : p ∈ fixN (natImage ψ' (Qv 𝔛 ν)) := by rw [hfixN]; exact hp
    exact mem_fixN.mp hp' _ (mem_natImage.mpr ⟨t, ht, rfl⟩)
  have hc0 : ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν →
      ((((toSL3 ψ' t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] - ![1, 0, 0] :
        Fin 3 → F)) 0 = 0 := by
    intro t ht
    have := sub_mem_commN (mem_natImage.mpr ⟨t, ht, rfl⟩ :
      toSL3 ψ' t ∈ natImage ψ' (Qv 𝔛 ν)) ![1, 0, 0]
    rw [hcomm] at this
    exact this
  have hrow : ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν →
      toSL3 ψ' t ∈ (rowLevi : Subgroup (SL3 F)) := by
    intro t ht
    refine mem_rowLevi_of_mulVec_zero fun v => ?_
    rw [mulVec_eq_add_of_fix (hfixT t ht), Pi.add_apply, Pi.smul_apply, hc0 t ht, smul_zero,
      add_zero]
  set N := NatSec.ofIsSum hP' with hN
  have hDj : ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν → ∀ v : Fin 3 → F, ∀ j : Fin 3, j ≠ 0 →
      (dualMat (toSL3 ψ' t) *ᵥ v) j = v j := by
    intro t ht v j hj
    have h1 := dualMat_mulVec_dotProduct (toSL3 ψ' t) v (Pi.single j 1)
    rw [hfixT t ht _ (by simp [hj.symm]), dotProduct_single, dotProduct_single,
      mul_one, mul_one] at h1
    exact h1
  have hfixpt : ∀ g : ↥(stab 𝔛 μ), toSL3 ψ' g ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ p ∈ Pv 𝔛 μ, N.coord p ∈ pt0 → N.coord ((g : 𝔘) * p * (g : 𝔘)⁻¹) = N.coord p := by
    intro g hg p hp hpt
    rw [N.coord_conj g hp, natAct_true, eq_smul_e0_of_mem_pt0 hpt, Matrix.mulVec_smul,
      (mem_rowLevi_iff.mp hg)]
  have hcommZ : ∀ g : ↥(stab 𝔛 μ), toSL3 ψ' g ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ p ∈ Pv 𝔛 μ, N.coord p ∈ pt0 → ⁅p, (g : 𝔘)⁆ ∈ ZM 𝔛 μ := by
    intro g hg p hp hpt
    have hgp : (g : 𝔘) * p⁻¹ * (g : 𝔘)⁻¹ ∈ Pv 𝔛 μ := N.conj_mem g (Subgroup.inv_mem _ hp)
    have e : ⁅p, (g : 𝔘)⁆ = p * ((g : 𝔘) * p⁻¹ * (g : 𝔘)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, ← N.coord_eq_zero_iff (Subgroup.mul_mem _ hp hgp), N.coord_mul hp hgp,
      N.coord_conj g (Subgroup.inv_mem _ hp), N.coord_inv hp, natAct_true, Matrix.mulVec_neg,
      ← natAct_true, ← N.coord_conj g hp, hfixpt g hg p hp hpt, add_neg_cancel]
  have hconjZ : ∀ g : ↥(stab 𝔛 μ), toSL3 ψ' g ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ p ∈ Pv 𝔛 μ, N.coord p ∈ pt0 → p⁻¹ * ((g : 𝔘)⁻¹ * p * (g : 𝔘)) ∈ ZM 𝔛 μ := by
    intro g hg p hp hpt
    have hgi : toSL3 ψ' g⁻¹ ∈ (rowLevi : Subgroup (SL3 F)) := by
      rw [map_inv]; exact Subgroup.inv_mem _ hg
    have hc := hfixpt g⁻¹ hgi p hp hpt
    have hmem : ((g⁻¹ : ↥(stab 𝔛 μ)) : 𝔘) * p * ((g⁻¹ : ↥(stab 𝔛 μ)) : 𝔘)⁻¹ ∈ Pv 𝔛 μ :=
      N.conj_mem g⁻¹ hp
    have h1 := N.inv_mul_mem_of_coord_eq hp hmem hc.symm
    simpa using h1
  have hpt : ∀ x ∈ Pv 𝔛 μ, ∀ t ∈ Qv 𝔛 ν, N.coord ⁅x, t⁆ ∈ pt0 := by
    intro x hx t ht
    have hxs := hPs hx
    have htx : t * x⁻¹ * t⁻¹ ∈ Pv 𝔛 μ := N.conj_mem ⟨t, hTs ht⟩ (Subgroup.inv_mem _ hx)
    have e : ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [e, N.coord_mul hx htx]
    have hc := N.coord_conj ⟨t, hTs ht⟩ (Subgroup.inv_mem _ hx)
    simp only at hc
    rw [hc, N.coord_inv hx, natAct_true, Matrix.mulVec_neg, mem_pt0]
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Pi.neg_apply]
      rw [hDj ⟨t, hTs ht⟩ ht _ 1 (by decide), add_neg_cancel]
    · simp only [Pi.add_apply, Pi.neg_apply]
      rw [hDj ⟨t, hTs ht⟩ ht _ 2 (by decide), add_neg_cancel]
  have hZab : ∀ a ∈ ZM 𝔛 μ, ∀ b ∈ ZM 𝔛 μ, a * b = b * a :=
    isMulCommutative_subgroup_iff.mp (isElemAbelian_zm _ h.hyp20 h.critDist_pos hμ).1
  have hZ2 : ∀ a ∈ ZM 𝔛 μ, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact (isElemAbelian_zm _ h.hyp20 h.critDist_pos hμ).2 a ha
  have hZS : ∀ z ∈ ZM 𝔛 μ, ∀ g ∈ stab 𝔛 μ, ⁅z, g⁆ ∈ Uloc h.le L μ := fun z hz g hg =>
    c.commutator_zm_stab_le hμ (Subgroup.commutator_mem_commutator hz hg)
  have hlevi : ∀ p ∈ Pv 𝔛 μ, N.coord p ∈ pt0 → ∀ t ∈ Qv 𝔛 ν, ⁅p, t⁆ ∈ Uloc h.le L μ := by
    intro p hp hpp t₀ ht₀
    set t : ↥(stab 𝔛 μ) := ⟨t₀, hTs ht₀⟩ with htdef
    have ht : (t : 𝔘) ∈ Qv 𝔛 ν := ht₀
    obtain ⟨cv, hcv⟩ : ∃ cv : Fin 3 → F,
        cv = ((toSL3 ψ' t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] - ![1, 0, 0] :=
      ⟨_, rfl⟩
    have hform : ∀ v, ((toSL3 ψ' t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + v 0 • cv := by
      intro v
      rw [hcv]
      exact mulVec_eq_add_of_fix (hfixT t ht) v
    have hcv0 : cv 0 = 0 := by rw [hcv]; exact hc0 t ht
    by_cases hc : cv = 0
    ·
      have h1 : toSL3 ψ' t = 1 := eq_one_of_mulVec_eq_self fun v => by
        rw [hform, hc, smul_zero, add_zero]
      have htQ := (S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hμ hU' t).mp h1
      exact c.commutator_pv_qv hμ (Subgroup.commutator_mem_commutator hp htQ)
    obtain ⟨c', hc'0, hc'ne, hcc'0, hcc'ne⟩ := exists_split hcv0
    obtain ⟨g₁, hg₁, hg₁c⟩ := exists_rowLevi_mulVec_eq hcv0 hc hc'0 hc'ne
    obtain ⟨g₂, hg₂, hg₂c⟩ := exists_rowLevi_mulVec_eq hcv0 hc hcc'0 hcc'ne
    obtain ⟨k₁, hk₁⟩ := toSL3_surjective hψ's g₁
    obtain ⟨k₂, hk₂⟩ := toSL3_surjective hψ's g₂
    have hk₁r : toSL3 ψ' k₁ ∈ (rowLevi : Subgroup (SL3 F)) := hk₁ ▸ hg₁
    have hk₂r : toSL3 ψ' k₂ ∈ (rowLevi : Subgroup (SL3 F)) := hk₂ ▸ hg₂
    have hform₁ : ∀ v, ((toSL3 ψ' (k₁ * t * k₁⁻¹) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        v + v 0 • c' := by
      intro v
      rw [map_mul, map_mul, map_inv, hk₁, mulVec_conj_of_transv hg₁ hform v, hg₁c]
    have hform₂ : ∀ v, ((toSL3 ψ' (k₂ * t * k₂⁻¹) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        v + v 0 • (cv - c') := by
      intro v
      rw [map_mul, map_mul, map_inv, hk₂, mulVec_conj_of_transv hg₂ hform v, hg₂c]
    have hprod : toSL3 ψ' ((k₁ * t * k₁⁻¹) * (k₂ * t * k₂⁻¹)) = toSL3 ψ' t := by
      refine eq_of_mulVec_eq fun v => ?_
      rw [map_mul, mulVec_mul_of_transv hcc'0 hform₁ hform₂, hform, add_sub_cancel]
    set q := ((k₁ * t * k₁⁻¹) * (k₂ * t * k₂⁻¹))⁻¹ * t with hqdef
    have hqQ : (q : 𝔘) ∈ Qv 𝔛 μ := by
      refine (S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hμ hU' q).mp ?_
      rw [hqdef, map_mul, map_inv, hprod, inv_mul_cancel]
    have hrowt₁ : toSL3 ψ' (k₁ * t * k₁⁻¹) ∈ (rowLevi : Subgroup (SL3 F)) := by
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁r (hrow t ht)) (Subgroup.inv_mem _ hk₁r)
    have hrowt₂ : toSL3 ψ' (k₂ * t * k₂⁻¹) ∈ (rowLevi : Subgroup (SL3 F)) := by
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₂r (hrow t ht)) (Subgroup.inv_mem _ hk₂r)
    have ha₁ := hcommZ _ hrowt₁ p hp hpp
    have ha₂ := hcommZ _ hrowt₂ p hp hpp
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at ha₁ ha₂
    refine commutator_mem_of_split (S := stab 𝔛 μ) (uloc_le_zm h c.full hμ) hZab hZ2 hUn hZS
      (hPs hp) t.2 k₁.2 k₂.2 (hconjZ k₁ hk₁r p hp hpp) (hconjZ k₂ hk₂r p hp hpp)
      (hcommZ t (hrow t ht) p hp hpp) ha₁ ha₂ (q := (q : 𝔘))
      (c.commutator_pv_qv hμ (Subgroup.commutator_mem_commutator hp hqQ)) ?_
    have htt : (t : 𝔘) = t₀ := rfl
    rw [hqdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, htt]
    group
  have hX : ⁅Pv 𝔛 μ, Qv 𝔛 ν⁆ ≤ N.pre (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    have hxt : ⁅x, t⁆ ∈ Pv 𝔛 μ := by
      have htx : t * x⁻¹ * t⁻¹ ∈ Pv 𝔛 μ := N.conj_mem ⟨t, hTs ht⟩ (Subgroup.inv_mem _ hx)
      have e : ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hx htx
    exact N.mem_pre.mpr ⟨hxt, hpt x hx t ht⟩
  refine (Subgroup.commutator_mono hX le_rfl).trans ?_
  rw [Subgroup.commutator_le]
  intro p hp t ht
  exact hlevi p (N.mem_pre.mp hp).1 (N.mem_pre.mp hp).2 t ht

theorem exists_dual_vv {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) :
    ∃ ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Uloc h.le L μ) ⊥ ψ false 1 ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Vv 𝔛 μ) (Bloc h.le L μ) ψ true 1 := by
  obtain ⟨ψ, hψs, hU, hP⟩ := c.exists_dual hμ
  obtain ⟨hPiB, hPB, -⟩ := c.decomp hμ
  have hVs : Vv 𝔛 μ ≤ stab 𝔛 μ := (vv_le_qv h c.b2 hμ).trans (qv_le_stab _ μ)
  have hVn := stab_le_normalizer_vv h μ
  have hBn : stab 𝔛 μ ≤ Subgroup.normalizer (Bloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hBV : Bloc h.le L μ ≤ Vv 𝔛 μ := bloc_le_vv h μ
  have hVB := isSumOfNaturalModulesVia_transfer hP hPB hPiB le_rfl (sup_eq_left.mpr hBV) hVn hBn
    (((pv_le_vv h hμ).trans hVs).trans hBn)
  rw [inf_eq_right.mpr hBV] at hVB
  exact ⟨ψ, hψs, hU, hVB⟩

omit [Fintype F] c in
theorem commutator_pv_qv_le_pv {α ν μ : Vtx 𝔛} (hα : IsMVtx 𝔛 α) (hαν : 𝔄 α ν) (hνμ : 𝔄 ν μ) :
    ⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ≤ Pv 𝔛 μ := by
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    (((qv_le_qv _ h.hyp20 hα hαν).trans (qv_le_stab_of_adj _ hνμ)).trans
      (stab_le_normalizer_pv _ μ))

theorem commutator_commutator_eq_bot (hb6 : 6 < critDist 𝔛) {α α' ν₁ μ : Vtx 𝔛}
    (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hαν₁ : 𝔄 α ν₁) (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) (hμ : μ ∈ Snu h.le L α ν₁) :
    ⁅⁅Pv 𝔛 μ, Qv 𝔛 α⁆, Qv 𝔛 α⁆ = ⊥ := by
  classical
  have hb := hb6
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  obtain ⟨ν, hαν, hνμ, hμn, -⟩ := id hμ
  have hμM := (zm_le_vv_of_mem_nablaSet h hα hμn).1
  have hdμ : (puAmalgam h.le).treeGraph.dist μ α = 2 := by rw [tdist_comm]; exact hμn.1
  have hQαν : Qv 𝔛 α ≤ Qv 𝔛 ν := qv_le_qv _ h20 hα hαν
  have hVμα : Vv 𝔛 μ ≤ Subgroup.centralizer (Vv 𝔛 α : Set 𝔘) :=
    S45.vi_le_centralizer_vi _ h20 hb0 (by omega)
  have hVμμ : Vv 𝔛 μ ≤ Subgroup.centralizer (Vv 𝔛 μ : Set 𝔘) :=
    S45.vi_le_centralizer_vi _ h20 hb0 (by rw [SimpleGraph.dist_self]; omega)
  have hVαμ : Vv 𝔛 α ≤ Subgroup.centralizer (Vv 𝔛 μ : Set 𝔘) :=
    Subgroup.le_centralizer_iff.mp hVμα
  have hPμV : Pv 𝔛 μ ≤ Vv 𝔛 μ := pv_le_vv h hμM
  have hZαVμ : ZM 𝔛 α ≤ Vv 𝔛 μ := by
    have := zv_le_vv h (α := μ) (ρ := α) (by omega)
    rwa [zv_of_isMVtx _ hα] at this
  have hPQ := commutator_pv_qv_le_pv (h := h) hα hαν hνμ
  set N := ⁅⁅Pv 𝔛 μ, Qv 𝔛 α⁆, Qv 𝔛 α⁆ with hNdef
  have hNU : N ≤ Uloc h.le L μ :=
    (Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hQαν) hQαν).trans
      (c.commutator_commutator_pv_le hμM hνμ.symm)
  have hNV : N ≤ Vv 𝔛 μ := hNU.trans ((uloc_le_zm h c.full hμM).trans (zm_le_vv h hμM))
  have hcn : ∀ X Y : Subgroup 𝔘, X ≤ Subgroup.centralizer (Vv 𝔛 μ : Set 𝔘) → Y ≤ Vv 𝔛 μ →
      X ≤ Subgroup.normalizer (Y : Set 𝔘) := fun X Y hX hY =>
    (hX.trans (Subgroup.centralizer_le hY)).trans (Subgroup.centralizer_le_normalizer _)
  have hNA : ⁅⁅Pv 𝔛 μ ⊔ Vv 𝔛 α, Qv 𝔛 α⁆, Qv 𝔛 α⁆ = N := by
    apply le_antisymm
    · have hN1V : ⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α ≤ Vv 𝔛 μ := sup_le (hPQ.trans hPμV) hZαVμ
      have h1 : ⁅Pv 𝔛 μ ⊔ Vv 𝔛 α, Qv 𝔛 α⁆ ≤ ⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZM 𝔛 α :=
        commutator_sup_left_le (hcn _ _ (hPμV.trans hVμμ) hN1V) (hcn _ _ hVαμ hN1V) le_sup_left
          ((c.commutator_vv_qv hα).trans le_sup_right)
      refine (Subgroup.commutator_mono h1 le_rfl).trans ?_
      refine commutator_sup_left_le (hcn _ _ ((hPQ.trans hPμV).trans hVμμ) hNV)
        (hcn _ _ (hZαVμ.trans hVμμ) hNV) le_rfl ?_
      rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (zm_le_centralizer_qv _ h20 hα)]
      exact bot_le
    · exact Subgroup.commutator_mono (Subgroup.commutator_mono le_sup_left le_rfl) le_rfl
  have hQn := stab_le_normalizer_qv _ α
  have hNn : stab 𝔛 α ≤ Subgroup.normalizer (N : Set 𝔘) := by
    rw [← hNA]
    exact le_normalizer_commutator
      (le_normalizer_commutator (c.stab_le_normalizer_pv_sup hb6 hs h4 hαν₁ hR hμ) hQn) hQn
  obtain ⟨ψ, hψs, hU, hVB⟩ := c.exists_dual_vv hα
  set NB := NatSec.ofIsSum hVB with hNBdef
  have hZμVα : ZM 𝔛 μ ≤ Vv 𝔛 α := by
    have := zv_le_vv h (α := α) (ρ := μ) (by rw [hμn.1])
    rwa [zv_of_isMVtx _ hμM] at this
  have hNVα : N ≤ Vv 𝔛 α := hNU.trans ((uloc_le_zm h c.full hμM).trans hZμVα)
  have hNB : N ≤ Bloc h.le L α := by
    by_contra hNB
    obtain ⟨n, hnN, hnB⟩ := Set.not_subset.mp hNB
    obtain ⟨t, htT, htQ⟩ : ∃ t ∈ Qv 𝔛 ν, t ∉ Qv 𝔛 α := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.relIndex_eq_one.mpr hcon
      rw [(c.edge hα hαν).2.2.2] at h1
      have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    have hts : t ∈ stab 𝔛 α := qv_le_stab_of_adj _ hαν.symm htT
    have ht1 : toSL3 ψ ⟨t, hts⟩ ≠ 1 := fun h1 =>
      htQ ((S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hα hU _).mp h1)
    obtain ⟨y, hy⟩ : ∃ y, dualMat (toSL3 ψ ⟨t, hts⟩) *ᵥ y ≠ y := by
      by_contra hcon
      push Not at hcon
      apply ht1
      have h1 : transposeInv (toSL3 ψ ⟨t, hts⟩) = 1 :=
        eq_one_of_mulVec_eq_self fun v => by rw [coe_transposeInv]; exact hcon v
      rw [← transposeInv_transposeInv (toSL3 ψ ⟨t, hts⟩), h1, map_one]
    obtain ⟨v, hv, hvy⟩ := NB.exists_coord_eq y
    obtain ⟨w, hwN, hwV, hwv⟩ := NB.exists_inv_mul_mem_of_invariant hψs
      (fun l x hx => (Subgroup.mem_normalizer_iff.mp (hNn l.2) x).mp hx) hnN (hNVα hnN) hnB hv
    have hwc : NB.coord w = y := by
      have h0 := (NB.coord_eq_zero_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwV) hv)).mpr hwv
      rw [NB.coord_mul (Subgroup.inv_mem _ hwV) hv, NB.coord_inv hwV, neg_add_eq_zero] at h0
      rw [h0, hvy]
    have htw : (t : 𝔘) * w * t⁻¹ ∈ Vv 𝔛 α := NB.conj_mem ⟨t, hts⟩ hwV
    have hmem : w⁻¹ * (t * w * t⁻¹) ∈ Bloc h.le L α := by
      have e : w⁻¹ * (t * w * t⁻¹) = ⁅w⁻¹, t⁆ := by simp only [commutatorElement_def]; group
      rw [e]
      have hc : ⁅w⁻¹, t⁆ ∈ Usup 𝔛 μ ν := by
        rw [usup_eq_commutator_uloc h c.full hμM hνμ.symm]
        exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hNU hwN)) htT
      exact zm_le_bloc h c.b2 hα (zh_le_zm _ hαν ((c.edge hμM hνμ.symm).1 hc))
    have h0 := (NB.coord_eq_zero_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwV) htw)).mpr hmem
    rw [NB.coord_mul (Subgroup.inv_mem _ hwV) htw, NB.coord_inv hwV, neg_add_eq_zero] at h0
    have hc := NB.coord_conj ⟨t, hts⟩ hwV
    simp only at hc
    rw [hc, natAct_true, hwc] at h0
    exact hy h0.symm
  have hNUs : N ≤ Usup 𝔛 α ν := by
    rw [← c.uloc_inf_bloc hα hαν hνμ hμn]
    exact le_inf hNU hNB
  have hUs := c.usup_le_uloc hα hαν
  have hNZl : N ≤ Zloc h.le L α := by
    by_contra hNZ
    have hle := uloc_le_of_normal h c.full c.hyp.2.2 hα
      ((hNUs.trans hUs).trans (uloc_le_zm h c.full hα)) hNn hNZ
    have hfinS := finite_stab h hα
    have hfinH : Finite ↥(Usup 𝔛 α ν) := Finite.of_injective _ (Subgroup.inclusion_injective
      (hUs.trans ((uloc_le_zm h c.full hα).trans
        ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α)))))
    have h1 := Subgroup.card_le_of_le (hle.trans hNUs)
    obtain ⟨ψ₀, -, hψ₀⟩ := exists_natural_Uloc h c.hyp.2.2 hα
    rw [card_eq_of_natural hψ₀, (c.edge hα hαν).2.1, Nat.card_eq_fintype_card (α := F)] at h1
    have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 :=
      Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  rw [eq_bot_iff, ← uloc_inf_zloc h c.full α]
  exact le_inf (hNUs.trans hUs) hNZl

theorem commutator_pv_qv_le_zm (hb6 : 6 < critDist 𝔛) {α α' ν₁ μ : Vtx 𝔛}
    (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hαν₁ : 𝔄 α ν₁) (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) (hμ : μ ∈ Snu h.le L α ν₁) :
    ⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ≤ ZM 𝔛 α := by
  have hb := hb6
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  obtain ⟨ν, hαν, hνμ, hμn, -⟩ := id hμ
  have hμM := (zm_le_vv_of_mem_nablaSet h hα hμn).1
  have hdμ : (puAmalgam h.le).treeGraph.dist μ α = 2 := by rw [tdist_comm]; exact hμn.1
  have hN := c.commutator_commutator_eq_bot hb6 hs h4 hαν₁ hR hμ
  have hC := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hN
  have hPQ := commutator_pv_qv_le_pv (h := h) hα hαν hνμ
  have hPμV : Pv 𝔛 μ ≤ Vv 𝔛 μ := pv_le_vv h hμM
  have hQ : ⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ≤ Qv 𝔛 α :=
    (hPQ.trans hPμV).trans (S45.vi_le_qv _ (by omega))
  have hE := S45.isElemAbelian_vi _ h20 hb0 (δ := μ) (i := 2) (by omega)
  rw [← xm_eq_zm h c.full hα]
  intro x hx
  exact mem_omegaOneCenterOf (hQ hx) (fun y hy => Subgroup.mem_centralizer_iff.mp (hC hx) y hy)
    (hE.2 x (hPμV (hPQ hx)))

theorem zm_le_pv_of_mem (hb6 : 6 < critDist 𝔛) {α α' ν₁ μ : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hαν₁ : 𝔄 α ν₁) (hR : ¬ critR 𝔛 α α' ≤ Usup 𝔛 α ν₁) (hμ : μ ∈ Snu h.le L α ν₁) :
    ZM 𝔛 α ≤ Pv 𝔛 μ := by
  classical
  have h20 := h.hyp20
  have hα := hs.1.1
  obtain ⟨ν, hαν, hνμ, hμn, -⟩ := id hμ
  have hμM := (zm_le_vv_of_mem_nablaSet h hα hμn).1
  have hA₁Z := c.commutator_pv_qv_le_zm hb6 hs h4 hαν₁ hR hμ
  have hPQ := commutator_pv_qv_le_pv (h := h) hα hαν hνμ
  have hZνα : ZH 𝔛 ν ≤ ZM 𝔛 α := zh_le_zm _ hαν
  have hZνμ : ZH 𝔛 ν ≤ ZM 𝔛 μ := zh_le_zm _ hνμ.symm
  have hBP : ⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZH 𝔛 ν ≤ Pv 𝔛 μ := sup_le hPQ (hZνμ.trans (zm_le_pv _ μ))
  obtain ⟨ψ, hψs, hU, hP⟩ := c.exists_dual hμM
  set N := NatSec.ofIsSum hP with hN
  have hfinS := finite_stab h hα
  have hfinZ : Finite ↥(ZM 𝔛 α) := Finite.of_injective _ (Subgroup.inclusion_injective
    ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α)))
  have hcard : Nat.card ↥(ZM 𝔛 α) = Nat.card F * Nat.card ↥(ZH 𝔛 ν) := by
    have h1 := Subgroup.relIndex_mul_card (ZH 𝔛 ν) (ZM 𝔛 α)
    rw [inf_of_le_left hZνα, (c.edge hα hαν).2.2.1, ← Nat.card_eq_fintype_card] at h1
    exact h1.symm
  have hQs : Qv 𝔛 α ≤ stab 𝔛 μ := (qv_le_qv _ h20 hα hαν).trans (qv_le_stab_of_adj _ hνμ)
  obtain ⟨a, haQ, haQμ⟩ : ∃ a ∈ Qv 𝔛 α, a ∉ Qv 𝔛 μ := by
    by_contra hcon
    push Not at hcon
    have h1 : ⁅ZM 𝔛 μ, Qv 𝔛 α⁆ = ⊥ := by
      rw [eq_bot_iff, ← (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (zm_le_centralizer_qv _ h20 hμM)]
      exact Subgroup.commutator_mono le_rfl hcon
    have h2 := (c.edge hα hαν).2.1
    rw [← (c.three hα hαν hνμ hμn).1, h1, Subgroup.card_bot] at h2
    have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have has : a ∈ stab 𝔛 μ := hQs haQ
  have ha1 : toSL3 ψ ⟨a, has⟩ ≠ 1 := fun h1 =>
    haQμ ((S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hμM hU _).mp h1)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ v₀ ≠ v₀ := by
    by_contra hcon
    push Not at hcon
    apply ha1
    have h1 : transposeInv (toSL3 ψ ⟨a, has⟩) = 1 :=
      eq_one_of_mulVec_eq_self fun v => by rw [coe_transposeInv]; exact hcon v
    rw [← transposeInv_transposeInv (toSL3 ψ ⟨a, has⟩), h1, map_one]
  set D := dualMat (toSL3 ψ ⟨a, has⟩) with hD
  set w := v₀ - D *ᵥ v₀ with hw
  have hw0 : w ≠ 0 := fun h0 => hv₀ (sub_eq_zero.mp h0).symm
  have hline : ∀ l : F, l • w ∈ N.img (⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZH 𝔛 ν) := by
    intro l
    obtain ⟨x, hx, hxc⟩ := N.exists_coord_eq (l • v₀)
    have hax : a * x⁻¹ * a⁻¹ ∈ Pv 𝔛 μ := N.conj_mem ⟨a, has⟩ (Subgroup.inv_mem _ hx)
    have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    refine N.mem_img.mpr ⟨⁅x, a⁆, Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator hx haQ), e ▸ Subgroup.mul_mem _ hx hax, ?_⟩
    rw [e, N.coord_mul hx hax]
    have hc := N.coord_conj ⟨a, has⟩ (Subgroup.inv_mem _ hx)
    simp only at hc
    rw [hc, N.coord_inv hx, natAct_true, ← hD, hxc, hw, Matrix.mulVec_neg, Matrix.mulVec_smul,
      smul_sub, sub_eq_add_neg]
  have himg : Nat.card F ≤ Nat.card ↥(N.img (⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZH 𝔛 ν)) := by
    have hfinI : Finite ↥(N.img (⁅Pv 𝔛 μ, Qv 𝔛 α⁆ ⊔ ZH 𝔛 ν)) := inferInstance
    refine Nat.card_le_card_of_injective (fun l => ⟨l • w, hline l⟩) ?_
    intro l l' hll
    have := congrArg Subtype.val hll
    exact smul_left_injective F hw0 this
  have hEq := eq_of_card_img N le_sup_right (sup_le hA₁Z hZνα) hBP hZνμ hcard himg
  rw [← hEq]
  exact hBP

end Ctx

end CFSG.Quasithin.MS93.S4A.D432
