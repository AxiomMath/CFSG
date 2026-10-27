module

public import CFSG.Milestones.ASVolI.F429.aR5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section Algebra

variable {Y : Type} [Group Y]

theorem burnsideF429a_conj_mul_conj (g g' : Y) (σ σ' : MulAut Y) :
    MulAut.conj g * σ * (MulAut.conj g' * σ') = MulAut.conj (g * σ g') * (σ * σ') := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_inv_rev, mul_assoc]

theorem burnsideF429a_conj_mul_inv (g : Y) (σ : MulAut Y) :
    (MulAut.conj g * σ)⁻¹ = MulAut.conj (σ⁻¹ g⁻¹) * σ⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]

theorem burnsideF429a_conj_mul_pow {H : Subgroup Y} {F : Subgroup (MulAut Y)}
    (hFH : ∀ σ ∈ F, ∀ h ∈ H, σ h ∈ H) {h : Y} (hh : h ∈ H) {σ : MulAut Y} (hσ : σ ∈ F) :
    ∀ n : ℕ, ∃ N ∈ H, (MulAut.conj h * σ) ^ n = MulAut.conj N * σ ^ n := by
  intro n
  induction n with
  | zero => exact ⟨1, H.one_mem, by rw [pow_zero, pow_zero, map_one, one_mul]⟩
  | succ n ih =>
    obtain ⟨N, hN, e⟩ := ih
    refine ⟨N * (σ ^ n) h, H.mul_mem hN (hFH _ (F.pow_mem hσ n) h hh), ?_⟩
    rw [pow_succ, e, burnsideF429a_conj_mul_conj, ← pow_succ]

theorem burnsideF429a_F_conj_eq_one {U H : Subgroup Y} {F : Subgroup (MulAut Y)}
    (D : BorelAutData U H F) {σ : MulAut Y} (hσ : σ ∈ F) {b : Y}
    (hb : b ∈ Subgroup.normalizer (U : Set Y)) (h : σ = MulAut.conj b) : σ = 1 := by
  obtain ⟨u₀, hu₀, h₀, hh₀, rfl⟩ := D.B_eq b hb
  refine D.F_faithful σ hσ fun x hx => ?_
  have hσx : σ x ∈ H := D.F_H σ hσ x hx
  have e1 : σ x = u₀ * x * u₀⁻¹ := by
    rw [h, MulAut.conj_apply]
    have hc := D.H_comm h₀ hh₀ x hx
    calc u₀ * h₀ * x * (u₀ * h₀)⁻¹ = u₀ * (h₀ * x) * h₀⁻¹ * u₀⁻¹ := by group
      _ = u₀ * (x * h₀) * h₀⁻¹ * u₀⁻¹ := by rw [hc]
      _ = u₀ * x * u₀⁻¹ := by group
  have hmem : σ x * x⁻¹ ∈ U := by
    rw [e1]
    have hx1 : x * u₀⁻¹ * x⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (D.H_le hx) u₀⁻¹).1 (U.inv_mem hu₀)
    have e2 : u₀ * x * u₀⁻¹ * x⁻¹ = u₀ * (x * u₀⁻¹ * x⁻¹) := by group
    rw [e2]
    exact U.mul_mem hu₀ hx1
  exact mul_inv_eq_one.1 (D.U_inf_H _ hmem (H.mul_mem hσx (H.inv_mem hx)))

end Algebra

section Generic

theorem burnsideF429a_mem_normalizer_sbar {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    {s : E} (hs : s ∈ M₁ ⊓ M₂) :
    s ∈ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) := by
  have hrX : s ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG s,
        (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hs hxM) ((M₁ ⊓ M₂).inv_mem hs)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG s⁻¹
        simpa [mul_assoc] using this
      · have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hs) hxM) hs
        simpa [mul_assoc] using this
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrX

theorem burnsideF429a_c2ab_of_borelAutData {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {B U H : Subgroup C} {F : Subgroup (MulAut C)}
    (D : BorelAutData U H F) [IsCyclic F]
    (hB : (M₁ ⊓ M₂).subgroupOf Gp = B.map Ψ.toMonoidHom) (hU : pCoreOf 2 B = U)
    (hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      ∃ Hc : Subgroup E, IsComplementIn Hc (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite C := Finite.of_injective _ (Gp.subtype_injective.comp Ψ.injective)
  obtain ⟨hSB, hTinf⟩ := burnsideF429a_T_inf_Gp hSG hT
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set φ : C →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = B.map φ := burnsideF429_inf_eq_map Ψ hB
  have hS : S = U.map φ := by
    rw [hSdef, hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, hU]
  have hmemS : ∀ y : C, y ∈ U ↔ φ y ∈ S := fun y => by
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  let act : E →* MulAut C := (MulAut.congr Ψ.symm).toMonoidHom.comp (burnsideF4d_rho Gp)
  have hact : ∀ (s : E) (x : C), φ (act s x) = s * φ x * s⁻¹ := by
    intro s x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp s (Ψ x))) : ↥Gp) : E) = s * ((Ψ x : ↥Gp) : E) * s⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply s (Ψ x)
  have hact_phi : ∀ x : C, act (φ x) = MulAut.conj x := by
    intro x
    ext y
    apply hφ
    rw [hact, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hact_inner : ∀ (s : E) (g : C), act s = MulAut.conj g → s = φ g := by
    intro s g h
    have h1 : act s = act (φ g) := by rw [h, hact_phi]
    have h2 : burnsideF4d_rho Gp s = burnsideF4d_rho Gp (φ g) :=
      (MulAut.congr Ψ.symm).injective h1
    exact burnsideF4d_rho_injective hc h2
  have hrN : ∀ s ∈ M₁ ⊓ M₂, ∀ x : C, act s x ∈ U ↔ x ∈ U := by
    intro s hs x
    have hN := burnsideF429a_mem_normalizer_sbar (Gp := Gp) hs
    rw [hmemS, hmemS, hact]
    exact ((Subgroup.mem_normalizer_iff.1 hN) (φ x)).symm
  have hnf : ∀ t ∈ T, ∃ g ∈ Subgroup.normalizer (U : Set C), ∃ σ ∈ F,
      act t = MulAut.conj g * σ := fun t ht => D.normal_form (act t) (hrN t (hT.1 ht))
  have hTG : ∀ t ∈ T, t ∈ Gp → t ∈ S := fun t ht htG => by
    rw [← hTinf]
    exact ⟨ht, htG⟩
  have hmemG : ∀ y : C, φ y ∈ Gp := fun y => (Ψ y).2
  let Sg : Subgroup (MulAut C) :=
    { carrier := {σ | σ ∈ F ∧ ∃ t ∈ T, ∃ g ∈ Subgroup.normalizer (U : Set C),
        act t = MulAut.conj g * σ}
      mul_mem' := fun {σ₁ σ₂} h1 h2 => by
        obtain ⟨hσ₁, t₁, ht₁, g₁, hg₁, e₁⟩ := h1
        obtain ⟨hσ₂, t₂, ht₂, g₂, hg₂, e₂⟩ := h2
        refine ⟨F.mul_mem hσ₁ hσ₂, t₁ * t₂, T.mul_mem ht₁ ht₂, g₁ * σ₁ g₂,
          Subgroup.mul_mem _ hg₁ ((D.F_B σ₁ hσ₁ g₂).2 hg₂), ?_⟩
        rw [map_mul act t₁ t₂, e₁, e₂, burnsideF429a_conj_mul_conj]
      one_mem' := ⟨F.one_mem, 1, T.one_mem, 1, Subgroup.one_mem _, by
        rw [map_one act, map_one MulAut.conj, one_mul]⟩
      inv_mem' := fun {σ} h => by
        obtain ⟨hσ, t, ht, g, hg, e⟩ := h
        refine ⟨F.inv_mem hσ, t⁻¹, T.inv_mem ht, σ⁻¹ g⁻¹,
          (D.F_B σ⁻¹ (F.inv_mem hσ) g⁻¹).2 (Subgroup.inv_mem _ hg), ?_⟩
        rw [map_inv act t, e, burnsideF429a_conj_mul_inv] }
  have hSgF : Sg ≤ F := fun σ hσ => hσ.1
  haveI : IsCyclic Sg := Subgroup.isCyclic_of_le hSgF
  obtain ⟨⟨σ₀, hσ₀⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥Sg)
  have hpow : ∀ σ ∈ Sg, ∃ m : ℕ, σ₀ ^ m = σ := by
    intro σ hσ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨σ, hσ⟩)
    have hk' : σ₀ ^ k = σ := by simpa using congrArg Subtype.val hk
    exact (Submonoid.mem_powers_iff _ _).1
      (mem_powers_iff_mem_zpowers.2 (Subgroup.mem_zpowers_iff.2 ⟨k, hk'⟩))
  obtain ⟨hσ₀F, t₀, ht₀, g₀, hg₀, e₀⟩ := hσ₀
  obtain ⟨u, hu, h, hh, rfl⟩ := D.B_eq g₀ hg₀
  set t₁ := (φ u)⁻¹ * t₀ with ht₁def
  have ht₁T : t₁ ∈ T := T.mul_mem (T.inv_mem (hSB ((hmemS u).1 hu))) ht₀
  have hact₁ : act t₁ = MulAut.conj h * σ₀ := by
    have e1 : act t₁ = (MulAut.conj u)⁻¹ * (MulAut.conj (u * h) * σ₀) := by
      rw [ht₁def, map_mul act, map_inv act, hact_phi, e₀]
    rw [e1, ← mul_assoc, ← map_inv MulAut.conj u, ← map_mul MulAut.conj, inv_mul_cancel_left]
  have hNpow := burnsideF429a_conj_mul_pow D.F_H hh hσ₀F
  have hnpos : 0 < orderOf σ₀ := orderOf_pos σ₀
  have ht₁n : t₁ ^ orderOf σ₀ = 1 := by
    obtain ⟨Nn, hNn, eNn⟩ := hNpow (orderOf σ₀)
    have h1 : act (t₁ ^ orderOf σ₀) = MulAut.conj Nn := by
      rw [map_pow act, hact₁, eNn, pow_orderOf_eq_one, mul_one]
    have h2 := hact_inner _ _ h1
    have h3 : t₁ ^ orderOf σ₀ ∈ S := hTG _ (T.pow_mem ht₁T _) (by rw [h2]; exact hmemG Nn)
    rw [h2] at h3
    have h5 := D.U_inf_H Nn ((hmemS Nn).2 h3) hNn
    rw [h2, h5, map_one]
  have hdec : ∀ g ∈ T, ∃ m : ℕ, g * (t₁ ^ m)⁻¹ ∈ S := by
    intro g hg
    obtain ⟨g', hg', σ, hσF, eg⟩ := hnf g hg
    obtain ⟨m, hm⟩ := hpow σ ⟨hσF, g, hg, g', hg', eg⟩
    obtain ⟨Nm, -, eNm⟩ := hNpow m
    refine ⟨m, ?_⟩
    have h1 : act (g * (t₁ ^ m)⁻¹) = MulAut.conj (g' * Nm⁻¹) := by
      rw [map_mul act, map_inv act, map_pow act, hact₁, eNm, eg, ← hm, map_mul MulAut.conj,
        map_inv MulAut.conj]
      group
    have h2 := hact_inner _ _ h1
    exact hTG _ (T.mul_mem hg (T.inv_mem (T.pow_mem ht₁T m))) (by rw [h2]; exact hmemG _)
  refine ⟨⟨t₁, ht₁T, ?_⟩, Subgroup.zpowers t₁, hSB, Subgroup.zpowers_le.2 ht₁T, ?_, ?_⟩
  ·
    refine le_antisymm (fun g hg => ?_) (sup_le (Subgroup.zpowers_le.2 ht₁T) hSB)
    obtain ⟨m, hm⟩ := hdec g hg
    have e : g = g * (t₁ ^ m)⁻¹ * t₁ ^ m := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hm)
      (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers t₁ m))
  ·
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxZ⟩
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hxZ)
    rw [pow_eq_pow_mod m ht₁n] at hxS ⊢
    have hm'n : m % orderOf σ₀ < orderOf σ₀ := Nat.mod_lt _ hnpos
    obtain ⟨Nm, hNm, eNm⟩ := hNpow (m % orderOf σ₀)
    have hxS' : t₁ ^ (m % orderOf σ₀) ∈ U.map φ := hS ▸ hxS
    obtain ⟨x', hx', hxx'⟩ := hxS'
    have h1 : act (t₁ ^ (m % orderOf σ₀)) = MulAut.conj x' := by rw [← hxx', hact_phi]
    rw [map_pow act, hact₁, eNm] at h1
    have h2 : σ₀ ^ (m % orderOf σ₀) = MulAut.conj (Nm⁻¹ * x') := by
      rw [map_mul MulAut.conj, map_inv MulAut.conj, ← h1]
      group
    have h3 := burnsideF429a_F_conj_eq_one D (F.pow_mem hσ₀F _)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (D.H_le hNm)) (Subgroup.le_normalizer hx')) h2
    have h5 : m % orderOf σ₀ = 0 := Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_of_pow_eq_one h3) hm'n
    rw [h5, pow_zero]
    exact Subgroup.one_mem _
  ·
    intro g hg
    obtain ⟨m, hm⟩ := hdec g hg
    exact ⟨g * (t₁ ^ m)⁻¹, hm, t₁ ^ m, Subgroup.npow_mem_zpowers t₁ m, by group⟩

end Generic

section U4

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF429a_c2ab_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    (∃ t ∈ T, T = Subgroup.zpowers t ⊔ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      ∃ H : Subgroup E, IsComplementIn H (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, e1, e2⟩ := burnsideF4gU4_exists_equiv marking
  have hB : (M₁ ⊓ M₂).subgroupOf Gp =
      (parP (burnsideF4gU4_fieldData marking) ⊓ parP2 (burnsideF4gU4_fieldData marking)).map
        Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, h1, h2, e1, e2, Subgroup.map_inf_eq _ _ _ Φ.injective]
  haveI := (burnsideF4gU4_fieldData marking).finite
  haveI : IsCyclic (marking.field ≃+* marking.field) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic _
  haveI : IsCyclic (MonoidHom.range (fieldAutHom (burnsideF4gU4_fieldData marking) 2 0)) :=
    isCyclic_of_surjective _ (fieldAutHom (burnsideF4gU4_fieldData marking) 2 0).rangeRestrict_surjective
  exact burnsideF429a_c2ab_of_borelAutData hyp.centralizer_trivial Φ
    (borelAutData_u4 (burnsideF4gU4_fieldData marking)) hB
    (burnsideF4gU4Inv_pCore_borel (burnsideF4gU4_fieldData marking))
    (burnsideF429a_U4_sylow_of_model _ Φ (h1.trans e1) (h2.trans e2)) hT

end U4

end CFSG.ASVolI
