module

public import CFSG.Quasithin.MS93.S4A43XD
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

local notation "Stab₃" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer
local notation "Flag₃" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagSpace

section SL3

variable {F : Type} [Field F]

@[expose] def transvGrp (P : Submodule F (Fin 3 → F)) : Subgroup (SL3 F) where
  carrier := {s | (∀ p ∈ P, ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p) ∧
    ∀ v, ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ P}
  mul_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    refine ⟨fun p hp => ?_, fun v => ?_⟩
    · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, ht1 p hp, hs1 p hp]
    · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec]
      have := P.add_mem (hs2 (((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) (ht2 v)
      rwa [sub_add_sub_cancel] at this
  one_mem' := ⟨fun p _ => by simp, fun v => by simp⟩
  inv_mem' := by
    rintro s ⟨hs1, hs2⟩
    refine ⟨fun p hp => ?_, fun v => ?_⟩
    · have := congrArg (((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ·) (hs1 p hp)
      simp only [S46.inv_mulVec_mulVec_SL3] at this
      exact this.symm
    · have h := hs2 (((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
      rw [S46.mulVec_inv_mulVec_SL3] at h
      have := P.neg_mem h
      rwa [neg_sub] at this

theorem card_transvGrp_le [Finite F] {P : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) : Nat.card ↥(transvGrp P) ≤ Nat.card ↥P := by
  obtain ⟨v₀, hv₀⟩ := S46.exists_not_mem_of_finrank_eq_two hP
  have htop := S46.sup_span_eq_top hP hv₀
  refine Nat.card_le_card_of_injective
    (fun s : ↥(transvGrp P) => (⟨((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v₀ - v₀,
      s.2.2 v₀⟩ : ↥P)) ?_
  intro s t hst
  have he : ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v₀ =
      ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v₀ := by
    have := congrArg Subtype.val hst
    simpa using this
  have hk : ∀ v, (((t⁻¹ * s : ↥(transvGrp P)) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    have hv : v ∈ P ⊔ F ∙ v₀ := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hwk : (((t⁻¹ * s : ↥(transvGrp P)) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w :=
      (t⁻¹ * s).2.1 w hw
    have hv₀k : (((t⁻¹ * s : ↥(transvGrp P)) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v₀ = v₀ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_mul_SL3, ← Matrix.mulVec_mulVec, he,
        S46.inv_mulVec_mulVec_SL3]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hwk, hv₀k]
  have h1 : t⁻¹ * s = 1 := Subtype.ext (eq_one_of_mulVec_eq_self hk)
  rw [← mul_left_cancel_iff (a := t⁻¹), h1, inv_mul_cancel]

theorem mulVec_mem_of_mem_stabilizer {P : Submodule F (Fin 3 → F)} {s : SL3 F}
    (hs : s ∈ Stab₃ P) {v : Fin 3 → F} (hv : v ∈ P) :
    ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ P := by
  have hs' : P.map (Matrix.mulVecLin ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = P := hs
  rw [← hs']
  exact ⟨v, hv, rfl⟩

theorem conj_mem_transvGrp {P : Submodule F (Fin 3 → F)} {s g : SL3 F} (hs : s ∈ Stab₃ P)
    (hg : g ∈ transvGrp P) : s * g * s⁻¹ ∈ transvGrp P := by
  have hsi : s⁻¹ ∈ Stab₃ P := Subgroup.inv_mem _ hs
  refine ⟨fun p hp => ?_, fun v => ?_⟩
  · rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hg.1 _ (mulVec_mem_of_mem_stabilizer hsi hp), S46.mulVec_inv_mulVec_SL3]
  · have h := mulVec_mem_of_mem_stabilizer hs
      (hg.2 (((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v))
    rw [Matrix.mulVec_sub, S46.mulVec_inv_mulVec_SL3] at h
    rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h

theorem eq_top_of_stabilizer_le {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {A : Subgroup (SL3 F)} (hA : Stab₃ P ≤ A) (hne : ¬ A ≤ Stab₃ P) : A = ⊤ := by
  obtain ⟨g₀, hg₀⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_flagSpace_eq P
  rw [hP] at hg₀
  have hconj := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stabilizer_map_conj g₀ (Flag₃ 3 F 2)
  rw [hg₀] at hconj
  set A' := A.map (MulAut.conj g₀⁻¹ : SL3 F →* SL3 F) with hA'
  have hle : Stab₃ (Flag₃ 3 F 2) ≤ A' := by
    intro x hx
    refine ⟨g₀ * x * g₀⁻¹, hA ?_, ?_⟩
    · rw [← hconj]
      exact ⟨x, hx, rfl⟩
    · simp [mul_assoc]
  rcases CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_of_stabilizer_flagSpace_le A' hle with
    h1 | h1
  · exfalso
    apply hne
    intro a ha
    have : g₀⁻¹ * a * g₀ ∈ A' := ⟨a, ha, by simp⟩
    rw [h1] at this
    rw [← hconj]
    exact ⟨_, this, by simp [mul_assoc]⟩
  · rw [eq_top_iff]
    intro a _
    have : g₀⁻¹ * a * g₀ ∈ A' := by rw [h1]; exact Subgroup.mem_top _
    obtain ⟨b, hb, hbe⟩ := this
    have : b = a := by
      have := congrArg (fun y => g₀ * y * g₀⁻¹) hbe
      simpa [mul_assoc] using this
    rw [← this]
    exact hb

theorem le_of_finrank_eq_one {r H : Submodule F (Fin 3 → F)} (hr : Module.finrank F r = 1)
    {x : Fin 3 → F} (hx : x ∈ r) (hx0 : x ≠ 0) (hxH : x ∈ H) : r ≤ H := by
  have hspan : Submodule.span F {x} = r :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hx)
      (by rw [finrank_span_singleton hx0, hr])
  rw [← hspan]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxH

theorem exists_mem_not_mem_span_ne {P r : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    (hr : Module.finrank F r = 1) (hrP : r ≤ P) (m : Submodule F (Fin 3 → F)) :
    ∃ v ∈ P, v ∉ r ∧ Submodule.span F {v} ≠ m := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := r)
    (fun h => by rw [h, finrank_bot] at hr; omega)
  obtain ⟨w, hwP, hwr⟩ : ∃ w ∈ P, w ∉ r := by
    by_contra hall
    push Not at hall
    have : P = r := le_antisymm hall hrP
    rw [this, hr] at hP
    omega
  by_cases hwm : Submodule.span F {w} = m
  · refine ⟨u + w, P.add_mem (hrP hu) hwP, fun h => hwr ?_, fun h => ?_⟩
    · have := r.sub_mem h hu
      rwa [add_sub_cancel_left] at this
    · have huw : u + w ∈ Submodule.span F {w} := by
        rw [hwm, ← h]
        exact Submodule.mem_span_singleton_self _
      have hu' : u ∈ Submodule.span F {w} := by
        have := (Submodule.span F {w}).sub_mem huw (Submodule.mem_span_singleton_self w)
        rwa [add_sub_cancel_right] at this
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu'
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hu0 hc.symm
      apply hwr
      have : w = c⁻¹ • u := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact r.smul_mem _ hu
  · exact ⟨w, hwP, hwr, hwm⟩

theorem finrank_span_sup_eq_and_inf {P : Submodule F (Fin 3 → F)} (hP : Module.finrank F P = 2)
    {v w : Fin 3 → F} (hvP : v ∈ P) (hv0 : v ≠ 0) (hwP : w ∉ P) :
    Module.finrank F ↥(Submodule.span F {v} ⊔ Submodule.span F {w}) = 2 ∧
      (Submodule.span F {v} ⊔ Submodule.span F {w}) ⊓ P = Submodule.span F {v} := by
  have hw0 : w ≠ 0 := fun h => hwP (h ▸ P.zero_mem)
  have hinf : Submodule.span F {v} ⊓ Submodule.span F {w} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hx2
    by_cases hb0 : b = 0
    · rw [hb0, zero_smul] at hb
      rw [Submodule.mem_bot, ← hb]
    · exfalso
      apply hwP
      have : w = b⁻¹ • (a • v) := by rw [← hb, smul_smul, inv_mul_cancel₀ hb0, one_smul]
      rw [this]
      exact P.smul_mem _ (P.smul_mem _ hvP)
  have h2 : Module.finrank F ↥(Submodule.span F {v} ⊔ Submodule.span F {w}) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {v})
      (Submodule.span F {w})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0, finrank_span_singleton hw0]
      at this
    exact this
  refine ⟨h2, ?_⟩
  have hle : Submodule.span F {v} ≤ (Submodule.span F {v} ⊔ Submodule.span F {w}) ⊓ P :=
    le_inf le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hvP)
  have htop : (Submodule.span F {v} ⊔ Submodule.span F {w}) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← S46.sup_span_eq_top hP hwP]
    exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span F {v} ⊔ Submodule.span F {w}) P
  rw [htop, finrank_top, Module.finrank_fin_fun, h2, hP] at h3
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hv0]; omega)).symm

theorem exists_map_eq_of_finrank_eq_two {P H : Submodule F (Fin 3 → F)}
    (hP : Module.finrank F P = 2) (hH : Module.finrank F H = 2) :
    ∃ s : SL3 F, P.map (Matrix.mulVecLin ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = H := by
  obtain ⟨g₁, hg₁⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_flagSpace_eq P
  obtain ⟨g₂, hg₂⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_flagSpace_eq H
  rw [hP] at hg₁
  rw [hH] at hg₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← hg₁, ← hg₂, ← Submodule.map_comp, ← Matrix.mulVecLin_mul, ← coe_mul_SL3,
    inv_mul_cancel_right]

end SL3

section NatImage

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

theorem natImage_map_conj (g : ↥K) {A : Subgroup G} :
    natImage φ (A.map (MulAut.conj (g : G)).toMonoidHom) =
      (natImage φ A).map (MulAut.conj (toSL3 φ g)).toMonoidHom := by
  ext s
  constructor
  · intro hs
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hs
    rw [mem_map_conj] at ha
    refine ⟨toSL3 φ (g⁻¹ * a * g), mem_natImage.mpr ⟨g⁻¹ * a * g, ha, rfl⟩, ?_⟩
    simp [map_mul, mul_assoc]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp ht
    refine mem_natImage.mpr ⟨g * a * g⁻¹, ?_, by simp [map_mul]⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_map_conj ha

end NatImage

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

section Coord

variable {α : Vtx (puAmalgam h.le)} (hα : IsMVtx (puAmalgam h.le) α)
  {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
  (hψ : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α) (Uloc h.le L α) ⊥ ψ false 1)
include hα hψ

theorem finrank_commN_qv {ρ : Vtx 𝔛} (hαρ : 𝔄 α ρ) :
    Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 ρ))) = 2 := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hc := c.card_usup hα hαρ
  have hTs : Qv 𝔛 ρ ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαρ.symm
  have h1 := usup_eq_commutator_uloc h c.full hα hαρ
  have h2 := card_commutator_eq hψ hTs
  rw [h1, h2, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card (α := F)] at hc
  exact Nat.pow_right_injective hq hc

theorem fixN_qv_eq {ρ : Vtx 𝔛} (hαρ : 𝔄 α ρ) :
    fixN (natImage ψ (Qv 𝔛 ρ)) = commN (natImage ψ (Qv 𝔛 ρ)) := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hTs : Qv 𝔛 ρ ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαρ.symm
  have hle : commN (natImage ψ (Qv 𝔛 ρ)) ≤ fixN (natImage ψ (Qv 𝔛 ρ)) := by
    intro w hw
    obtain ⟨u, rfl⟩ := natVec_surjective hψ w
    have hu := (mem_commutator_iff_natVec hψ hTs u).mpr hw
    rw [← usup_eq_commutator_uloc h c.full hα hαρ] at hu
    exact (mem_centralizer_iff_natVec hψ hTs u).mp
      ((c.usup_le_zh hα hαρ).trans (zh_le_centralizer _ ρ) hu)
  have h2 : Module.finrank F ↥(fixN (natImage ψ (Qv 𝔛 ρ))) = 2 := by
    have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hcard := c.card_uloc_inf_zh hα hαρ
    have e1 := zh_inf_uloc h c.full hα hαρ
    have e2 := card_inf_centralizer_eq hψ hTs
    rw [inf_comm, e1, e2, Module.natCard_eq_pow_finrank (K := F),
      Nat.card_eq_fintype_card (α := F)] at hcard
    exact Nat.pow_right_injective hq' hcard
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, c.finrank_commN_qv hα hψ hαρ])).symm

theorem natImage_qv_eq {ρ : Vtx 𝔛} (hαρ : 𝔄 α ρ) :
    natImage ψ (Qv 𝔛 ρ) = transvGrp (commN (natImage ψ (Qv 𝔛 ρ))) := by
  have hTs : Qv 𝔛 ρ ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαρ.symm
  have hle : natImage ψ (Qv 𝔛 ρ) ≤ transvGrp (commN (natImage ψ (Qv 𝔛 ρ))) := by
    intro g hg
    refine ⟨fun p hp => ?_, fun v => sub_mem_commN hg v⟩
    rw [← c.fixN_qv_eq hα hψ hαρ] at hp
    exact mem_fixN.mp hp g hg
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [S46.card_natImage_eq_relIndex h c.via hα hψ hTs, c.relIndex_qv hα hαρ]
  refine (card_transvGrp_le (c.finrank_commN_qv hα hψ hαρ)).trans ?_
  rw [Module.natCard_eq_pow_finrank (K := F), c.finrank_commN_qv hα hψ hαρ,
    Nat.card_eq_fintype_card]

theorem conj_mem_qv_of_mem_stabilizer {ρ : Vtx 𝔛} (hαρ : 𝔄 α ρ) {g : ↥(stab 𝔛 α)}
    (hg : toSL3 ψ g ∈ Stab₃ (commN (natImage ψ (Qv 𝔛 ρ)))) {x : 𝔘} (hx : x ∈ Qv 𝔛 ρ) :
    (g : 𝔘) * x * (g : 𝔘)⁻¹ ∈ Qv 𝔛 ρ := by
  have hTs : Qv 𝔛 ρ ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαρ.symm
  have hxs := hTs hx
  have hmem : toSL3 ψ (g * ⟨x, hxs⟩ * g⁻¹) ∈ natImage ψ (Qv 𝔛 ρ) := by
    rw [map_mul, map_mul, map_inv, c.natImage_qv_eq hα hψ hαρ]
    refine conj_mem_transvGrp hg ?_
    rw [← c.natImage_qv_eq hα hψ hαρ]
    exact mem_natImage.mpr ⟨⟨x, hxs⟩, hx, rfl⟩
  obtain ⟨a, ha, hae⟩ := mem_natImage.mp hmem
  have h1 : toSL3 ψ (a⁻¹ * (g * ⟨x, hxs⟩ * g⁻¹)) = 1 := by
    rw [map_mul, map_inv, hae, inv_mul_cancel]
  have h2 := (S46.toSL3_eq_one_iff_mem_qv h c.via hα hψ _).mp h1
  have h3 : ((a⁻¹ * (g * ⟨x, hxs⟩ * g⁻¹) : ↥(stab 𝔛 α)) : 𝔘) ∈ Qv 𝔛 ρ :=
    qv_le_qv _ h.hyp20 hα hαρ h2
  have h4 := (Qv 𝔛 ρ).mul_mem ha h3
  simpa [mul_assoc] using h4

theorem mem_gab_of_mem_stabilizer {ρ : Vtx 𝔛} (hαρ : 𝔄 α ρ) {g : ↥(stab 𝔛 α)}
    (hg : toSL3 ψ g ∈ Stab₃ (commN (natImage ψ (Qv 𝔛 ρ)))) : (g : 𝔘) ∈ Gab 𝔛 α ρ := by
  refine ⟨g.2, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx =>
    c.conj_mem_qv_of_mem_stabilizer hα hψ hαρ hg hx, fun hx => ?_⟩⟩
  have hgi : toSL3 ψ g⁻¹ ∈ Stab₃ (commN (natImage ψ (Qv 𝔛 ρ))) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  have := c.conj_mem_qv_of_mem_stabilizer hα hψ hαρ hgi hx
  simpa [mul_assoc] using this

theorem eq_stab_of_gab_le (hsurj : Function.Surjective ψ) {ρ : Vtx 𝔛} (hαρ : 𝔄 α ρ)
    {K : Subgroup 𝔘} (hK : K ≤ stab 𝔛 α) (hgab : Gab 𝔛 α ρ ≤ K) {z : ↥(stab 𝔛 α)}
    (hzK : (z : 𝔘) ∈ K) (hz : toSL3 ψ z ∉ Stab₃ (commN (natImage ψ (Qv 𝔛 ρ)))) :
    K = stab 𝔛 α := by
  have hA : Stab₃ (commN (natImage ψ (Qv 𝔛 ρ))) ≤ natImage ψ K := by
    intro s hs
    obtain ⟨g, rfl⟩ := toSL3_surjective hsurj s
    exact mem_natImage.mpr ⟨g, hgab (c.mem_gab_of_mem_stabilizer hα hψ hαρ hs), rfl⟩
  have hne : ¬ natImage ψ K ≤ Stab₃ (commN (natImage ψ (Qv 𝔛 ρ))) := fun hle =>
    hz (hle (mem_natImage.mpr ⟨z, hzK, rfl⟩))
  have htop := eq_top_of_stabilizer_le (c.finrank_commN_qv hα hψ hαρ) hA hne
  refine le_antisymm hK fun g hg => ?_
  have hmem : toSL3 ψ ⟨g, hg⟩ ∈ natImage ψ K := htop ▸ Subgroup.mem_top _
  obtain ⟨k, hk, hke⟩ := mem_natImage.mp hmem
  have h1 : toSL3 ψ (k⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hke, inv_mul_cancel]
  have h2 := (S46.toSL3_eq_one_iff_mem_qv h c.via hα hψ _).mp h1
  have h3 : ((k⁻¹ * ⟨g, hg⟩ : ↥(stab 𝔛 α)) : 𝔘) ∈ K :=
    hgab ⟨(k⁻¹ * ⟨g, hg⟩).2, (stab_le_normalizer_qv _ ρ)
      (qv_le_stab _ ρ (qv_le_qv _ h.hyp20 hα hαρ h2))⟩
  have h4 := K.mul_mem hk h3
  simpa using h4

end Coord

theorem exists_gen_ne {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {ρ₀ : Vtx 𝔛} (hρ₀ : 𝔄 α ρ₀) :
    ∃ ρ : Vtx 𝔛, 𝔄 α ρ ∧ Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α ∧
      Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≠ Usup 𝔛 α ρ₀ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) := by
  have hα := hs.1.1
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨ψ, hsurj, hψ⟩ := exists_natural_Uloc h c.via hα
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hZβ : ZM 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 α α' 1) := zm_le_qv_geo_one_of_star h hs
  have hZs : ZM 𝔛 α' ≤ stab 𝔛 α := zm_le_stab_of_star h hs
  have hP₀ := c.finrank_commN_qv hα hψ hαβ
  have hr : Module.finrank F ↥(commN (natImage ψ (ZM 𝔛 α'))) = 1 := by
    have hcR := c.card_critR hs
    have e0 := commutator_zm_eq_uloc h c.full hα hZs
    have e1 := card_commutator_eq hψ hZs
    rw [critR, e0, e1, Module.natCard_eq_pow_finrank (K := F),
      Nat.card_eq_fintype_card (α := F)] at hcR
    exact Nat.pow_right_injective hq (show Fintype.card F ^ _ = Fintype.card F ^ 1 by
      rw [hcR, pow_one])
  have hrP₀ : commN (natImage ψ (ZM 𝔛 α')) ≤ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) :=
    commN_mono (natImage_mono hZβ)
  obtain ⟨v, hvP, hvr, hvm⟩ := exists_mem_not_mem_span_ne hP₀ hr hrP₀
    (commN (natImage ψ (Qv 𝔛 ρ₀)) ⊓ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))))
  have hv0 : v ≠ 0 := fun h0 => hvr (h0 ▸ Submodule.zero_mem _)
  obtain ⟨w, hw⟩ := S46.exists_not_mem_of_finrank_eq_two hP₀
  obtain ⟨hH2, hHP⟩ := finrank_span_sup_eq_and_inf hP₀ hvP hv0 hw
  obtain ⟨s, hsH⟩ := exists_map_eq_of_finrank_eq_two hP₀ hH2
  obtain ⟨g, hg⟩ := toSL3_surjective hsurj s
  have hgα : (g : 𝔘) • α = α := (mem_stab _).mp g.2
  have hαρ : 𝔄 α ((g : 𝔘) • geo 𝔛 α α' 1) := by
    have := (adj_smul _ (g : 𝔘) _ _).mpr hαβ
    rwa [hgα] at this
  have hlin : ((Matrix.SpecialLinearGroup.toLin' s : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
        Matrix.mulVecLin ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
    ext x
    simp [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  have hPρ : commN (natImage ψ (Qv 𝔛 ((g : 𝔘) • geo 𝔛 α α' 1))) =
      Submodule.span F {v} ⊔ Submodule.span F {w} := by
    rw [qv_smul, natImage_map_conj, commN_map_conj, hg, hlin, hsH]
  refine ⟨_, hαρ, ?_, fun heq => ?_⟩
  · obtain ⟨z, hzZ, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp (c.not_zm_le_qv hs)
    have hzs : z ∈ stab 𝔛 α := hZs hzZ
    refine c.eq_stab_of_gab_le hα hψ hsurj hαρ (sup_le inf_le_left hZs) le_sup_left
      (z := ⟨z, hzs⟩) (le_sup_right (a := Gab 𝔛 α _) hzZ) ?_
    rw [hPρ]
    intro hstab
    have htT : toSL3 ψ ⟨z, hzs⟩ ∈
        transvGrp (commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1)))) := by
      rw [← c.natImage_qv_eq hα hψ hαβ]
      exact mem_natImage.mpr ⟨_, hZβ hzZ, rfl⟩
    have htr := sub_mem_commN (mem_natImage.mpr ⟨⟨z, hzs⟩, hzZ, rfl⟩ :
      toSL3 ψ ⟨z, hzs⟩ ∈ natImage ψ (ZM 𝔛 α')) w
    have htw : ((toSL3 ψ ⟨z, hzs⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ≠ w := by
      intro heq
      apply hzQ
      refine (S46.toSL3_eq_one_iff_mem_qv h c.via hα hψ ⟨z, hzs⟩).mp ?_
      refine eq_one_of_mulVec_eq_self fun x => ?_
      have hx : x ∈ commN (natImage ψ (Qv 𝔛 (geo 𝔛 α α' 1))) ⊔ Submodule.span F {w} :=
        (S46.sup_span_eq_top hP₀ hw) ▸ Submodule.mem_top
      obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, htT.1 p hp, heq]
    have hwH : w ∈ Submodule.span F {v} ⊔ Submodule.span F {w} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
    have hdiff := Submodule.sub_mem _ (mulVec_mem_of_mem_stabilizer hstab hwH) hwH
    have hrH := le_of_finrank_eq_one hr htr (sub_ne_zero.mpr htw) hdiff
    apply hvr
    have hle : commN (natImage ψ (ZM 𝔛 α')) ≤ Submodule.span F {v} := hHP ▸ le_inf hrH hrP₀
    have hreq : commN (natImage ψ (ZM 𝔛 α')) = Submodule.span F {v} :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, finrank_span_singleton hv0])
    rw [hreq]
    exact Submodule.mem_span_singleton_self v
  · apply hvm
    rw [← hHP, ← hPρ]
    ext x
    obtain ⟨u, rfl⟩ := natVec_surjective hψ x
    have key : ∀ (A : Subgroup 𝔘) (hA : A ≤ stab 𝔛 α),
        natVec hψ u ∈ commN (natImage ψ A) ↔ (u : 𝔘) ∈ ⁅Uloc h.le L α, A⁆ :=
      fun A hA => (mem_commutator_iff_natVec hψ hA u).symm
    have e1 := usup_eq_commutator_uloc h c.full hα hαρ
    have e2 := usup_eq_commutator_uloc h c.full hα hαβ
    have e3 := usup_eq_commutator_uloc h c.full hα hρ₀
    simp only [Submodule.mem_inf]
    rw [key _ (qv_le_stab_of_adj _ hαρ.symm), key _ (qv_le_stab_of_adj _ hαβ.symm),
      key _ (qv_le_stab_of_adj _ hρ₀.symm), ← e1, ← e2, ← e3, ← Subgroup.mem_inf, heq,
      Subgroup.mem_inf]

end Ctx43

end CFSG.Quasithin.MS93.S4A
