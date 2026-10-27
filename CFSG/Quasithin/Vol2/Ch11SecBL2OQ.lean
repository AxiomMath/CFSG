module

public import CFSG.Quasithin.Vol2.Ch11SecBL2OMain
public import CFSG.Quasithin.Background.A3Structure36BCaseAux
public import CFSG.Quasithin.Vol2.Ch11SecBL2OA312

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_ker_modO2 {H K : Subgroup G} (hKH : K ≤ H) :
    IsPGroup 2 ↥(((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom).ker := by
  set σ := ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hσ
  have hmem : ∀ x : ↥σ.ker, (⟨((x : ↥K) : G), hKH (x : ↥K).2⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := by
    intro x
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  let j : ↥σ.ker →* ↥(CFSG.pCore 2 ↥H) :=
    { toFun := fun x => ⟨⟨((x : ↥K) : G), hKH (x : ↥K).2⟩, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine IsPGroup.of_injective CFSG.pCore_isPGroup j fun a b hab => ?_
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg (fun y : ↥(CFSG.pCore 2 ↥H) => ((y : ↥H) : G)) hab
  simpa [j] using this

theorem nonempty_mulEquiv_modO2_of_eq {H K Kp : Subgroup G} (hKH : K ≤ H) (hL : Kp ∈ cComp H)
    (heq : modO2Image H K = modO2Image H Kp) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) := by
  set σ : ↥K →* ↥(modO2Image H K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hσ
  have hσs : Function.Surjective σ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  obtain ⟨e₁⟩ := modO2_mulEquiv hL
  set ρ : ↥K →* ↥(modO2Image H Kp) := (MulEquiv.subgroupCongr heq).toMonoidHom.comp σ with hρ
  have hρs : Function.Surjective ρ := (MulEquiv.subgroupCongr heq).surjective.comp hσs
  have hρk : IsPGroup 2 ↥ρ.ker := by
    rw [hρ, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr heq).injective]
    exact isPGroup_ker_modO2 hKH
  have hY' : ∀ P : Subgroup ↥(modO2Image H Kp), P.Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hPn hP2
    have h1 := eq_bot_of_normal_of_isPGroup_quotient
      (hPn.map e₁.symm.toMonoidHom e₁.symm.surjective) (hP2.map e₁.symm.toMonoidHom)
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₁.symm.injective).mp h1
  obtain ⟨e₂⟩ := mulEquiv_modO2_of_surjective ρ hρs hρk hY'
  exact ⟨e₂.trans e₁.symm⟩

theorem false_of_a312Nonquasi
    {K Y : Type} [Group K] [Group Y] [Finite Y] [Group.IsPerfect K]
    {k : ℕ} (hk : 2 ≤ k) (hY : L2BadType k Y)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ CFSG.Open.pCore 2 K)) (ψ : K →* Y)
    (hψ : Function.Surjective ψ) {Γ : Type} [Group Γ] {Bb Lb : Subgroup Γ} (hBL : Bb ≤ Lb)
    (σ : K →* ↥Bb) (hσs : Function.Surjective σ) (hnon : A312Nonquasi Bb Lb) : False := by
  unfold A312Nonquasi at hnon
  rcases hnon with ⟨-, hLeq, p, hp, hp2, hSL⟩ | ⟨-, -, N, hNn, hN, hSL⟩
  · obtain ⟨e⟩ : Nonempty (↥Lb ⧸ CFSG.oddCore ↥Lb ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := hSL
    set τ : ↥Lb →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥Lb)) with hτ
    have hτs : Function.Surjective τ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hOL : (CFSG.oddCore ↥Lb).map Lb.subtype ≤ Lb := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hsup : Bb.subgroupOf Lb ⊔ CFSG.oddCore ↥Lb = ⊤ := by
      have h1 : (Bb ⊔ (CFSG.oddCore ↥Lb).map Lb.subtype).subgroupOf Lb = ⊤ := by
        rw [← hLeq]
        exact Subgroup.subgroupOf_self Lb
      rw [Subgroup.subgroupOf_sup hBL hOL] at h1
      have h2 : ((CFSG.oddCore ↥Lb).map Lb.subtype).subgroupOf Lb = CFSG.oddCore ↥Lb :=
        Subgroup.comap_map_eq_self_of_injective Lb.subtype_injective _
      rwa [h2] at h1
    have hker : CFSG.oddCore ↥Lb ≤ τ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
    have hτB := surjective_comp_subtype_of_sup_eq_top τ hτs hsup hker
    exact false_of_surjective_SL2 hk hY hKq ψ hψ hp hp2
      ((τ.comp (Bb.subgroupOf Lb).subtype).comp
        ((Subgroup.subgroupOfEquivOfLe hBL).symm.toMonoidHom.comp σ))
      (hτB.comp ((Subgroup.subgroupOfEquivOfLe hBL).symm.surjective.comp hσs))
  · have := hNn
    obtain ⟨e⟩ : Nonempty (↥(Bb ⊔ (CFSG.oddCore ↥Lb).map Lb.subtype) ⧸ N ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := hSL
    set τ : ↥(Bb ⊔ (CFSG.oddCore ↥Lb).map Lb.subtype) →*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      e.toMonoidHom.comp (QuotientGroup.mk' N) with hτ
    have hτs : Function.Surjective τ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hsup : Bb.subgroupOf (Bb ⊔ (CFSG.oddCore ↥Lb).map Lb.subtype) ⊔ N = ⊤ := by
      rw [hN, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hker : N ≤ τ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
    have hτB := surjective_comp_subtype_of_sup_eq_top τ hτs hsup hker
    exact false_of_surjective_SL2 hk hY hKq ψ hψ Nat.prime_five (by norm_num)
      ((τ.comp (Bb.subgroupOf (Bb ⊔ (CFSG.oddCore ↥Lb).map Lb.subtype)).subtype).comp
        ((Subgroup.subgroupOfEquivOfLe
          (le_sup_left : Bb ≤ Bb ⊔ (CFSG.oddCore ↥Lb).map Lb.subtype)).symm.toMonoidHom.comp σ))
      (hτB.comp ((Subgroup.subgroupOfEquivOfLe le_sup_left).symm.surjective.comp hσs))

theorem isQuasisimple_overgroup
    {T K Kp : Subgroup G} {Y : Type} [Group Y] [Finite Y] {k : ℕ}
    (hk : 2 ≤ k) (hY : L2BadType k Y) (hKl : quasithinIsLocal T K)
    (hKpl : quasithinIsLocal T Kp) (hKKp : K ≤ Kp)
    (hKq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) (ψ : ↥K →* Y)
    (hψ : Function.Surjective ψ)
    (h312 : A312Refined (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T))) :
    CFSG.IsQuasisimple (↥Kp ⧸ CFSG.pCore 2 ↥Kp) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Kp ⊔ T with hHdef
  have hS : IsSylowTwoOf T H := ⟨le_sup_right, hKpl.1, hKpl.2.2.1⟩
  have hBH : K ≤ H := hKKp.trans le_sup_left
  have hL : Kp ∈ cComp H := hKpl.2.1
  have hB : K ∈ lFamily T := hKl.2.1
  have hKp : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  set Lb := modO2Image H Kp with hLb
  set Bb := modO2Image H K with hBb
  set σ : ↥K →* ↥Bb :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom with hσ
  have hσs : Function.Surjective σ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  have hBL : Bb ≤ Lb := Subgroup.map_mono fun x hx => hKKp hx
  obtain ⟨e₁⟩ := modO2_mulEquiv hL
  rcases lemma_1_2_4_refined h312 hS hBH hB hL hKKp with heq | hq | ⟨-, hnon⟩
  ·
    obtain ⟨e₂⟩ := nonempty_mulEquiv_modO2_of_eq hBH hL heq
    have hon : (CFSG.Open.pCore 2 ↥K).Normal := by
      exact CFSG.pCore_normal
    have hn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    have hKq' : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
      A36B.isQuasisimple_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).symm
        (A3.isQuasisimple_iff_open.mpr hKq)
    exact A36B.isQuasisimple_of_mulEquiv e₂ hKq'
  · exact A36B.isQuasisimple_of_mulEquiv e₁.symm hq.1
  · exact (false_of_a312Nonquasi hk hY hKq ψ hψ hBL σ hσs hnon).elim

end CFSG.Quasithin.Vol2.Ch11.SecB
