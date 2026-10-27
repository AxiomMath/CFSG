module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep3
public import CFSG.Quasithin.Vol2.Ch12Sec8OnePara

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

section KMap

variable {Γ Δ : Type} [Group Γ] [Group Δ]

@[expose] def kmapOf (Ω : Subgroup Γ) (e : ↥Ω ≃* Δ) (H : Subgroup Γ) : Subgroup Δ :=
  (H.subgroupOf Ω).map e.toMonoidHom

theorem kmapOf_index (Ω : Subgroup Γ) (e : ↥Ω ≃* Δ) (H : Subgroup Γ) :
    (kmapOf Ω e H).index = H.relIndex Ω := by
  unfold kmapOf Subgroup.relIndex
  exact Subgroup.index_map_equiv (H.subgroupOf Ω) e

theorem kmapOf_mono (Ω : Subgroup Γ) (e : ↥Ω ≃* Δ) {H H' : Subgroup Γ} (h : H ≤ H') :
    kmapOf Ω e H ≤ kmapOf Ω e H' :=
  Subgroup.map_mono (by intro x hx; exact h hx)

theorem kmapOf_isPGroup (Ω : Subgroup Γ) (e : ↥Ω ≃* Δ) {H : Subgroup Γ}
    (hH : IsPGroup 2 (H.subgroupOf Ω)) : IsPGroup 2 (kmapOf Ω e H) :=
  hH.map e.toMonoidHom

end KMap

section Stab

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

theorem mem_stabS_span_of_fix {v : M} {γ : M ≃ₗ[ZMod 2] M} (h : γ v = v) :
    γ ∈ stabS (Submodule.span (ZMod 2) {v}) := by
  have h2 : γ.symm v = v := by
    conv_lhs => rw [← h]
    exact γ.symm_apply_apply v
  rw [mem_stabS_iff]
  intro w
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [map_smul, h]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hw : w = γ.symm (γ w) := (γ.symm_apply_apply w).symm
    rw [hw, ← hc, map_smul, h2]

end Stab

section Flags

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem overgroup_index_35 (F1 : FactF1) (hM : Module.finrank (ZMod 2) M = 4) {p ℓ Pl : Submodule (ZMod 2) M}
    (hp : Module.finrank (ZMod 2) p = 1) (hℓ : Module.finrank (ZMod 2) ℓ = 2)
    (hPl : Module.finrank (ZMod 2) Pl = 3) (hpℓ : p < ℓ) (hℓPl : ℓ < Pl)
    {X : Subgroup (M ≃ₗ[ZMod 2] M)} (hX : stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X)
    (hXi : X.index = 35) : X = stabS ℓ := by
  obtain ⟨h35, h15p, h15P, h105a, h105b, h105c, h315, hcls⟩ :=
    F1.2 M hM p ℓ Pl hp hℓ hPl hpℓ hℓPl
  rcases hcls X hX with h | h | h | h | h | h | h | h
  · rw [h, Subgroup.index_top] at hXi
    norm_num at hXi
  · rw [h] at hXi
    omega
  · exact h
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega

theorem overgroup_index_15 (F1 : FactF1) (hM : Module.finrank (ZMod 2) M = 4) {p ℓ Pl : Submodule (ZMod 2) M}
    (hp : Module.finrank (ZMod 2) p = 1) (hℓ : Module.finrank (ZMod 2) ℓ = 2)
    (hPl : Module.finrank (ZMod 2) Pl = 3) (hpℓ : p < ℓ) (hℓPl : ℓ < Pl)
    {X : Subgroup (M ≃ₗ[ZMod 2] M)} (hX : stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X)
    (hXi : X.index = 15) : X = stabS p ∨ X = stabS Pl := by
  obtain ⟨h35, h15p, h15P, h105a, h105b, h105c, h315, hcls⟩ :=
    F1.2 M hM p ℓ Pl hp hℓ hPl hpℓ hℓPl
  rcases hcls X hX with h | h | h | h | h | h | h | h
  · rw [h, Subgroup.index_top] at hXi
    norm_num at hXi
  · exact Or.inl h
  · rw [h] at hXi
    omega
  · exact Or.inr h
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega
  · rw [h] at hXi
    omega

end Flags

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylow_T_img (h1222 : Stmt12_2_2) {T L V V₁ V₂ K₁ : Subgroup G}
    (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁))
    (hTΩ : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ D.img K₁)
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2) :
    IsSylowTwoOf (D.img T) (D.img K₁) ∧ IsPGroup 2 (D.img T) := by
  have hTH : T ≤ Subgroup.normalizer (V₁ : Set G) := hs.v1.2.2
  have hHU : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    le_normalizer_conjClosure V _
  have hT2 : IsPGroup 2 T := hcx.hyp.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (V₁ : Set G)) := by
    refine ⟨hTH, hT2, ?_⟩
    have h1 := Subgroup.relIndex_mul_index hTH
    have h2 : T.relIndex (Subgroup.normalizer (V₁ : Set G)) ∣ T.index := ⟨_, h1.symm⟩
    intro h2'
    exact hcx.hyp.hyp.sylow.2 (h2'.trans h2)
  have hHsyl := L1294.isSylowTwoOf_img D hTsyl hHU
  have hTp : IsPGroup 2 (D.img T) := by
    have h : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (u128 V V₁ : Set G))) :=
      hT2.comap_subtype
    exact h.map D.ρ
  have hTΩ' : D.img T ≤ D.img K₁ := by
    intro γ hγ
    obtain ⟨t, ht, hN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    exact hTΩ t ht hN
  have hOH : D.img K₁ ≤ D.img (Subgroup.normalizer (V₁ : Set G)) :=
    L1294.img_mono D hK₁H
  have hmul := Subgroup.relIndex_mul_relIndex (D.img T) (D.img K₁) (D.img (Subgroup.normalizer (V₁ : Set G))) hTΩ' hOH
  have hsyl : ¬ 2 ∣ (D.img T).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) :=
    hHsyl.2.2
  have hΩodd : ¬ 2 ∣ (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) := by
    intro h
    apply hsyl
    rw [← hmul]
    exact Dvd.dvd.mul_left h _
  have hΩ1 : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) = 1 := by
    omega
  have hTrel1 : (D.img T).relIndex (D.img K₁) =
      (D.img T).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) := by
    rw [← hmul, hΩ1, mul_one]
  refine ⟨⟨hTΩ', hTp, ?_⟩, hTp⟩
  show ¬ 2 ∣ (D.img T).relIndex (D.img K₁)
  rw [hTrel1]
  exact hsyl

end Sylow

section Fix

variable {G : Type} [Group G] [Finite G]

theorem T_fix_pi (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂)
    (D : HatModelU (u128 V V₁)) {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁) {t : G} (ht : t ∈ T)
    (htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G)) :
    D.ρ ⟨t, htU⟩ (D.π a) = D.π a := by
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, -⟩ := L128P.exists_gens hV₁2 hV₂4
  have hUV : ∀ v ∈ V, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ hv
  have haU : a ∈ u128 V V₁ := hUV a (hs.v2.1 haV₂)
  have hπz : D.π z = 0 := by
    have hzZ : z ∈ V ⊓ zU128 V V₁ := by
      rw [lemma12_8_8_three h1222 h12213 hs]
      exact hz
    exact (L128A.HatU.π_eq_zero_iff D (hUV z (hs.v1.1 hz))).2 (Subgroup.mem_inf.1 hzZ).2
  have hw2 : t * a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 (hs.v2.2.2 ht) a).1 haV₂
  have hw1 : t * a * t⁻¹ ∉ V₁ := fun hw =>
    haV₁ ((Subgroup.mem_normalizer_iff.1 (hs.v1.2.2 ht) a).2 hw)
  have e := L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ haV₂ hw2
  have hρ : D.ρ ⟨t, htU⟩ (D.π a) = D.π (t * a * t⁻¹) := D.ρ_π ⟨t, htU⟩ a haU
  rw [hρ]
  rcases e with h | h | h | h
  · exfalso
    apply haV₁
    have h2 : a = 1 := by
      calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
    rw [h2]
    exact V₁.one_mem
  · exact absurd (h ▸ hz) hw1
  · rw [h]
  · rw [h, D.π_mul z (hUV z (hs.v1.1 hz)) a haU, hπz, zero_add]

end Fix

section Main5

variable {G : Type} [Group G] [Finite G]

theorem step5_main (F1 : FactF1) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V V₁ V₂ K₁ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    (hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hM : Module.finrank (ZMod 2) M = 4)
    (D : HatModelU (u128 V V₁)) {q : D.V → ZMod 2}
    (hΩF4 : F4Out q D.B (D.img K₁))
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2)
    (hTΩ : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ D.img K₁)
    (S : Submodule (ZMod 2) D.V) (hS3 : Module.finrank (ZMod 2) S = 3)
    (hSq : ∀ s ∈ S, q s = 0) (hSV : ∀ v ∈ V, D.π v ∈ S)
    (hTS : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ stabS S)
    {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁)
    (e : ↥(D.img K₁) ≃* (M ≃ₗ[ZMod 2] M)) :
    ∃ p ℓ Pl : Submodule (ZMod 2) M, Module.finrank (ZMod 2) p = 1 ∧
      Module.finrank (ZMod 2) ℓ = 2 ∧ Module.finrank (ZMod 2) Pl = 3 ∧ p < ℓ ∧ ℓ < Pl ∧
      kmapOf (D.img K₁) e (D.img T) = stabS p ⊓ stabS ℓ ⊓ stabS Pl ∧
      kmapOf (D.img K₁) e (stabS (Submodule.span (ZMod 2) {D.π a})) = stabS ℓ ∧
      (kmapOf (D.img K₁) e (stabS S) = stabS p ∨ kmapOf (D.img K₁) e (stabS S) = stabS Pl) := by
  classical
  obtain ⟨hTsyl, hTp⟩ := isSylow_T_img h1222 hcx hs hK₁H D hTΩ himg
  have hπa0 : D.π a ≠ 0 := by
    intro h0
    have hU : a ∈ u128 V V₁ := le_conjClosure V _ (hs.v2.1 haV₂)
    have h1 : a ∈ V ⊓ zU128 V V₁ :=
      ⟨hs.v2.1 haV₂, (L128A.HatU.π_eq_zero_iff D hU).1 h0⟩
    rw [lemma12_8_8_three h1222 h12213 hs] at h1
    exact haV₁ h1
  have hqa : q (D.π a) = 0 := hSq _ (hSV a (hs.v2.1 haV₂))
  have hidx35 : (stabS (Submodule.span (ZMod 2) {D.π a})).relIndex (D.img K₁) = 35 :=
    hΩF4.2.1 (D.π a) hπa0 hqa
  have hidx15 : (stabS S).relIndex (D.img K₁) = 15 :=
    ((hΩF4.2.2.1 S hS3 hSq).2.1)
  have hB₀p : IsPGroup 2 (kmapOf (D.img K₁) e (D.img T)) :=
    kmapOf_isPGroup _ e hTsyl.2.1.comap_subtype
  have hB₀i : ¬ 2 ∣ (kmapOf (D.img K₁) e (D.img T)).index := by
    rw [kmapOf_index]
    exact hTsyl.2.2
  obtain ⟨p, ℓ, Pl, hp, hℓ, hPl, hpℓ, hℓPl, hB⟩ := F1.1 M hM _ hB₀p hB₀i
  have hTspan : D.img T ≤ stabS (Submodule.span (ZMod 2) {D.π a}) := by
    intro γ hγ
    obtain ⟨t, ht, htU, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    exact mem_stabS_span_of_fix (T_fix_pi h1222 h12213 hs D haV₂ haV₁ ht htU)
  have hTS' : D.img T ≤ stabS S := by
    intro γ hγ
    obtain ⟨t, ht, htU, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    exact hTS t ht htU
  have hX1 : kmapOf (D.img K₁) e (stabS (Submodule.span (ZMod 2) {D.π a})) = stabS ℓ := by
    apply overgroup_index_35 F1 hM hp hℓ hPl hpℓ hℓPl (X := kmapOf (D.img K₁) e
      (stabS (Submodule.span (ZMod 2) {D.π a})))
    · rw [← hB]
      exact kmapOf_mono _ e hTspan
    · rw [kmapOf_index, hidx35]
  have hX2 : kmapOf (D.img K₁) e (stabS S) = stabS p ∨
      kmapOf (D.img K₁) e (stabS S) = stabS Pl := by
    apply overgroup_index_15 F1 hM hp hℓ hPl hpℓ hℓPl (X := kmapOf (D.img K₁) e (stabS S))
    · rw [← hB]
      exact kmapOf_mono _ e hTS'
    · rw [kmapOf_index, hidx15]
  exact ⟨p, ℓ, Pl, hp, hℓ, hPl, hpℓ, hℓPl, hB, hX1, hX2⟩

end Main5

end CFSG.Quasithin.H13.C1294
