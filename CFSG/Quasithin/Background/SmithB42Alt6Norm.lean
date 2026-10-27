module

public import CFSG.Quasithin.Background.SmithB42Alt6Mod
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointA
public import CFSG.Quasithin.Background.S1549DA6Dict
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin

namespace B42Alt6

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm CFSG.Quasithin.S143

variable {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}

theorem realizesVia_of_modEquiv {D : FFModel} (hD : D.IsActionModel) (H : Subgroup (MulAut S))
    (π : D.Gam →* ↥H) (hπ : Function.Surjective π) (e : S ≃* D.Mod)
    (he : ∀ (γ : D.Gam) (v : S) (m : ↥D.sec) (hm : D.act γ (m : D.Amb) ∈ D.sec),
      e v = QuotientGroup.mk m →
        e (((π γ : ↥H) : MulAut S) v) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩) :
    D.RealizesVia H ⊤ ⊥ π := by
  refine ⟨hπ, bot_le, hD.ker_le, fun _ _ _ => trivial, fun _ z hz => by simpa using hz,
    hD.sec_inv, hD.ker_inv, ?_⟩
  refine ⟨e.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨v, rfl⟩ := e.surjective q
    exact ⟨⟨v, trivial⟩, rfl⟩
  · intro u
    show e (u : S) = 1 ↔ (u : S) ∈ (⊥ : Subgroup S)
    rw [MulEquiv.map_eq_one_iff, Subgroup.mem_bot]
  · intro γ u m hu hm hum
    exact he γ (u : S) m hm hum

namespace N6Model

variable (M : N6Model L)

@[expose] noncomputable def modEquiv : S ≃* (FFModel.symDn 6).Mod := M.Θ.trans S1549D.psiN6.symm

theorem modEquiv_act (σ : Perm (Fin 6)) (v : S) (m : ↥(G6.coreMod 6))
    (hm : G6.permAct 6 σ (m : G6.PermMod 6) ∈ G6.coreMod 6)
    (hv : M.modEquiv v = QuotientGroup.mk m) :
    M.modEquiv (M.ρ σ v) = QuotientGroup.mk ⟨G6.permAct 6 σ (m : G6.PermMod 6), hm⟩ := by
  have h1 : M.Θ v = S1549D.n6Rep m := by
    have := congrArg S1549D.psiN6 hv
    simp only [modEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at this
    rw [this]
    rfl
  show S1549D.psiN6.symm (M.Θ (M.ρ σ v)) = _
  rw [M.Θ_ρ, h1, ← S1549D.n6Rep_permAct σ m, MulEquiv.symm_apply_eq]
  rfl

theorem ρ_mem_L {γ : Perm (Fin 6)} (hγ : γ ∈ alternatingGroup (Fin 6)) : M.ρ γ ∈ L := by
  have h : M.ρ γ ∈ (alternatingGroup (Fin 6)).map M.ρ := ⟨γ, hγ, rfl⟩
  rwa [M.ρ_alt] at h

theorem mem_L_iff {x : MulAut S} : x ∈ L ↔ ∃ γ ∈ alternatingGroup (Fin 6), M.ρ γ = x := by
  constructor
  · intro hx
    have h : x ∈ (alternatingGroup (Fin 6)).map M.ρ := by rw [M.ρ_alt]; exact hx
    exact h
  · rintro ⟨γ, hγ, rfl⟩
    exact M.ρ_mem_L hγ

@[expose] noncomputable def ρL : ↥(alternatingGroup (Fin 6)) →* ↥L :=
  (M.ρ.comp (alternatingGroup (Fin 6)).subtype).codRestrict L fun γ => M.ρ_mem_L γ.2

theorem ρL_surjective : Function.Surjective M.ρL := by
  intro l
  have hl : (l : MulAut S) ∈ (alternatingGroup (Fin 6)).map M.ρ := by rw [M.ρ_alt]; exact l.2
  obtain ⟨γ, hγ, hγl⟩ := hl
  exact ⟨⟨γ, hγ⟩, Subtype.ext hγl⟩

theorem realizesVia_alt : (FFModel.altDn 6).RealizesVia L ⊤ ⊥ M.ρL :=
  realizesVia_of_modEquiv (FFModel.altDn_isActionModel 6) L M.ρL M.ρL_surjective M.modEquiv
    fun (γ : ↥(alternatingGroup (Fin 6))) v m hm hv => M.modEquiv_act γ.1 v m hm hv

include M in
theorem alternatingNatural : AlternatingNatural L ⊤ ⊥ 6 := ⟨M.ρL, M.realizesVia_alt⟩

theorem card_fixV_map (E : Subgroup (Perm (Fin 6))) :
    Nat.card (fixV (E.map M.ρ)) = Nat.card {a : N6 // ∀ σ ∈ E, n6Act σ a = a} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨M.Θ v, fun σ hσ => ?_⟩
      invFun := fun a => ⟨M.Θ.symm a, fun x hx => ?_⟩
      left_inv := fun v => Subtype.ext (M.Θ.symm_apply_apply _)
      right_inv := fun a => Subtype.ext (M.Θ.apply_symm_apply _) }
  · rw [← M.Θ_ρ, v.2 _ ⟨σ, hσ, rfl⟩]
  · obtain ⟨σ, hσ, rfl⟩ := hx
    apply M.Θ.injective
    rw [M.Θ_ρ, M.Θ.apply_symm_apply, a.2 σ hσ]

include M in
theorem card_eq : Nat.card S = 16 := by
  rw [Nat.card_congr M.Θ.toEquiv, n6_card]

theorem le_range [Finite S] (hS : ∀ s : S, s * s = 1) (ι : ↥L ≃* alternatingGroup (Fin 6))
    {g : MulAut S} (hg : g ∈ Subgroup.normalizer (L : Set (MulAut S))) : ∃ σ, M.ρ σ = g := by
  classical
  let _ : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul, pow_two]
      exact hS _
    exact toMul_eq_one.1 h3
  have : Finite (Additive S) := inferInstanceAs (Finite S)
  have : Module.Finite (ZMod 2) (Additive S) := Module.Finite.of_finite
  let θ : S ≃* Multiplicative (Additive S) := (MulEquiv.multiplicativeAdditive S).symm
  let ψ := Setup.Layer.binPsi θ
  have hd : Module.finrank (ZMod 2) (Additive S) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive S)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive S) = 2 ^ 4 := by
      rw [show Nat.card (Additive S) = Nat.card S from rfl, M.card_eq]
      norm_num
    rw [h2] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  set LW := L.map ψ.toMonoidHom with hLW
  have hLW' : Nonempty (↥LW ≃* alternatingGroup (Fin 6)) :=
    ⟨(L.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans ι⟩
  obtain ⟨θ', hθ'inj, -, -⟩ := Setup.X3.four_binary_normalizer_six_point hd LW hLW'
  have hmapN : ∀ x ∈ Subgroup.normalizer (L : Set (MulAut S)),
      ψ x ∈ Subgroup.normalizer (LW : Set (Additive S ≃ₗ[ZMod 2] Additive S)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨x * l * x⁻¹, (hx l).1 hl, ?_⟩
      simp [map_mul, map_inv]
    · intro hy
      obtain ⟨l, hl, hlx⟩ := hy
      have hlx' : ψ l = ψ x * y * (ψ x)⁻¹ := hlx
      have hl' : x⁻¹ * l * x ∈ L := by
        refine (hx (x⁻¹ * l * x)).2 ?_
        rw [show x * (x⁻¹ * l * x) * x⁻¹ = l by group]
        exact hl
      refine ⟨x⁻¹ * l * x, hl', ?_⟩
      show ψ (x⁻¹ * l * x) = y
      rw [map_mul, map_mul, map_inv, hlx']
      group
  set N := Subgroup.normalizer (L : Set (MulAut S)) with hN
  have hcardN : Nat.card N ≤ 720 := by
    let f : ↥N → Perm (Fin 6) := fun x => θ' ⟨ψ x, hmapN x x.2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 := hθ'inj hxy
      have h2 : ψ x = ψ y := congrArg Subtype.val h1
      exact Subtype.ext (ψ.injective h2)
    calc Nat.card N ≤ Nat.card (Perm (Fin 6)) := Nat.card_le_card_of_injective f hf
      _ = 720 := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have hρN : M.ρ.range ≤ N := by
    rintro _ ⟨σ, rfl⟩
    rw [hN, Subgroup.mem_normalizer_iff]
    intro l
    rw [M.mem_L_iff, M.mem_L_iff]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨σ * γ * σ⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact (alternatingGroup.normal (α := Fin 6)).conj_mem γ hγ σ
    · rintro ⟨γ, hγ, hγl⟩
      refine ⟨σ⁻¹ * γ * σ, ?_, ?_⟩
      · have := (alternatingGroup.normal (α := Fin 6)).conj_mem γ hγ σ⁻¹
        simpa using this
      · have h1 : M.ρ σ * M.ρ (σ⁻¹ * γ * σ) * (M.ρ σ)⁻¹ = M.ρ γ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          group
        have h2 : M.ρ (σ⁻¹ * γ * σ) = (M.ρ σ)⁻¹ * M.ρ γ * M.ρ σ := by
          rw [← h1]
          group
        rw [h2, hγl]
        group
  have hcardR : Nat.card M.ρ.range = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective M.ρ_inj).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have heq : M.ρ.range = N := Subgroup.eq_of_le_of_card_ge hρN (by rw [hcardR]; exact hcardN)
  have hgR : g ∈ M.ρ.range := by rw [heq]; exact hg
  obtain ⟨σ, hσ⟩ := hgR
  exact ⟨σ, hσ⟩

end N6Model

end B42Alt6

end CFSG.Quasithin
