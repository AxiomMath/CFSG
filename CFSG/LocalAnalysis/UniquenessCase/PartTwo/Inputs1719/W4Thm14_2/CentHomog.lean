module

public import CFSG.Quasithin.Background.L34OutFacts
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.Quasithin.Background.SmithB42SL3Label
public import CFSG.Quasithin.Background.SmithB42SL3Trace

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification
open scoped MatrixGroups Matrix

open CFSG.ComponentClassification in
private theorem isGraphType_graph_conj {K : Type} [Field K] {ν : MulAut SL(3, K)}
    (h : L34Out.IsGraphType ν) :
    L34Out.IsGraphType (CatalogueBGraphForm.slGraphAut 3 K * ν *
      CatalogueBGraphForm.slGraphAut 3 K) := by
  obtain ⟨A, σ, rfl⟩ := h
  have hδδ : CatalogueBGraphForm.slGraphAut 3 K * CatalogueBGraphForm.slGraphAut 3 K = 1 :=
    LinearFlag.slGraph_mul_slGraph
  have hδinv : (CatalogueBGraphForm.slGraphAut 3 K)⁻¹ =
      CatalogueBGraphForm.slGraphAut 3 K := inv_eq_of_mul_eq_one_right hδδ
  have h1 : CatalogueBGraphForm.slGraphAut 3 K *
      CatalogueBHigherLinearAction.slConjugation 3 K A =
      CatalogueBHigherLinearAction.slConjugation 3 K
        (Matrix.GeneralLinearGroup.inverseTranspose A) *
        CatalogueBGraphForm.slGraphAut 3 K := by
    have h := eq_mul_inv_of_mul_eq (LinearFlag.slGraph_mul_slConjugation_mul_slGraph A)
    rwa [hδinv] at h
  have h2 : CatalogueBGraphForm.slGraphAut 3 K *
      CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ =
      CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
        CatalogueBGraphForm.slGraphAut 3 K := by
    have h := eq_mul_inv_of_mul_eq (LinearFlag.slGraph_mul_slField_mul_slGraph (K := K) (n := 3) σ)
    rwa [hδinv] at h
  refine ⟨Matrix.GeneralLinearGroup.inverseTranspose A, σ, ?_⟩
  have e : CatalogueBGraphForm.slGraphAut 3 K *
      (CatalogueBHigherLinearAction.slConjugation 3 K A *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
        CatalogueBGraphForm.slGraphAut 3 K) *
      CatalogueBGraphForm.slGraphAut 3 K =
      CatalogueBGraphForm.slGraphAut 3 K *
        CatalogueBHigherLinearAction.slConjugation 3 K A *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ := by
    have h : CatalogueBGraphForm.slGraphAut 3 K *
        (CatalogueBHigherLinearAction.slConjugation 3 K A *
          CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
          CatalogueBGraphForm.slGraphAut 3 K) *
        CatalogueBGraphForm.slGraphAut 3 K =
        CatalogueBGraphForm.slGraphAut 3 K *
          CatalogueBHigherLinearAction.slConjugation 3 K A *
          CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
          (CatalogueBGraphForm.slGraphAut 3 K *
            CatalogueBGraphForm.slGraphAut 3 K) := by group
    rw [h, hδδ, mul_one]
  rw [e]
  calc CatalogueBGraphForm.slGraphAut 3 K *
        CatalogueBHigherLinearAction.slConjugation 3 K A *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ =
      (CatalogueBHigherLinearAction.slConjugation 3 K
          (Matrix.GeneralLinearGroup.inverseTranspose A) *
          CatalogueBGraphForm.slGraphAut 3 K) *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ := by rw [h1]
    _ = CatalogueBHigherLinearAction.slConjugation 3 K
          (Matrix.GeneralLinearGroup.inverseTranspose A) *
        (CatalogueBGraphForm.slGraphAut 3 K *
          CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ) := by group
    _ = CatalogueBHigherLinearAction.slConjugation 3 K
          (Matrix.GeneralLinearGroup.inverseTranspose A) *
        (CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
          CatalogueBGraphForm.slGraphAut 3 K) := by rw [h2]
    _ = CatalogueBHigherLinearAction.slConjugation 3 K
          (Matrix.GeneralLinearGroup.inverseTranspose A) *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
          CatalogueBGraphForm.slGraphAut 3 K := by group

theorem exists_natRep_equiv_id_or_tauSL {F : Type} [Field F] [CharP F 2] {j : ℕ}
    {ℓ : Bool × Bool} (hℓ : B42SL3.IsSingle ℓ) :
    ∃ ψ : SL(3, F) →* SL(3, F), (ψ = MonoidHom.id (SL(3, F)) ∨ ψ = X7a.tauSL F) ∧
      (∀ g, ψ (ψ g) = g) ∧
      Nonempty ((X7.matRep (X7a.locRep (F := F) F ℓ.1 ℓ.2 j)).Equiv
        (X7.matRep ((X7a.natRep (F := F) F j).comp ψ))) := by
  rcases hℓ with rfl | rfl
  · refine ⟨MonoidHom.id _, Or.inl rfl, fun g => rfl, ?_⟩
    rw [MonoidHom.comp_id]
    exact ⟨Representation.Equiv.refl _⟩
  · refine ⟨X7a.tauSL F, Or.inr rfl, fun g => X7a.tauSL_tauSL g, ?_⟩
    rw [show (X7a.natRep (F := F) F j).comp (X7a.tauSL F) = X7a.dualRep (F := F) F j from
      MonoidHom.ext fun g => X7a.natRep_tauSL (F := F) F j g]
    exact ⟨Representation.Equiv.refl _⟩

private theorem exists_natRep_cases {F : Type} [Field F] [CharP F 2] {j : ℕ} {ℓ : Bool × Bool}
    (hℓ : B42SL3.IsSingle ℓ) :
    ∃ ψ : SL(3, F) →* SL(3, F), (ψ = MonoidHom.id (SL(3, F)) ∨ ψ = X7a.tauSL F) ∧
      (∀ g, ψ (ψ g) = g) ∧
      Nonempty ((X7.matRep (X7a.locRep (F := F) F ℓ.1 ℓ.2 j)).Equiv
        (X7.matRep ((X7a.natRep (F := F) F j).comp ψ))) :=
  exists_natRep_equiv_id_or_tauSL hℓ

private theorem exists_natural_or_dual {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) SL(3, F) U) {n : ℕ} (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible) {a b : Fin f → Bool}
    (hS : X7a.cntS a b = 1) (hH : X7a.cntH a b = 0)
    (W₀ : Subrepresentation (X7.matRep (X7.matMap (ZMod.castHom (dvd_refl 2) F)
      (X7b.toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (X7.matRep (X7a.tensorRep (F := F) F a b))) :
    (∃ E : U ≃+ (Fin 3 → F), ∀ g u, E (ρ g u) =
        ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u) ∨
    (∃ E : U ≃+ (Fin 3 → F), ∀ g u, E (ρ g u) =
        ((X7a.tauSL F g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u) := by
  obtain ⟨i₀, hsingle, hrest⟩ := B42SL3.exists_single_pos hS hH
  obtain ⟨e₁⟩ := B42SL3.nonempty_equiv_locRep (F := F) (fun i : Fin f => (a i, b i))
    (fun i => (i : ℕ)) (i₀ := i₀) hrest
  obtain ⟨ψ, hψ, hψinv, ⟨e₂⟩⟩ := exists_natRep_cases (F := F) (j := (i₀ : ℕ)) hsingle
  obtain ⟨E, hE⟩ := B42SL3.exists_addEquiv_of_sub hF ρ bas hirr W₀ hψinv
    ((e₀.trans e₁).trans e₂)
  obtain ⟨E', hE'⟩ := B42SL3.exists_untwist ρ (i₀ : ℕ) E hE
  rcases hψ with hψ | hψ
  · exact Or.inl ⟨E', by rw [hψ] at hE'; simpa using hE'⟩
  · exact Or.inr ⟨E', by rw [hψ] at hE'; exact hE'⟩

theorem false_of_isGraphType_of_homogeneous {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsSL3 ↥L 2)
    (hrk : rk ↥(⊤ : Subgroup W) ≤ 12) {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : SL(3, K) →* ↥L) (hα : Function.Surjective α)
    {x : MulAut W}
    (ν : MulAut SL(3, K)) (hν : ∀ s, ((α (ν s) : ↥L) : MulAut W) = x * (α s : MulAut W) * x⁻¹)
    (hgraph : L34Out.IsGraphType ν) {W₁ W₂ : Subgroup W} (h₁ : IsIrrOn L W₁ ⊥)
    (h₂ : IsIrrOn L W₂ ⊥) (hint : W₁ ⊓ W₂ = ⊥) (hsup : W₁ ⊔ W₂ = ⊤) {c : MulAut W}
    (hc : ∀ l ∈ L, c * l = l * c) (hcW : W₁.map c.toMonoidHom = W₂) : False := by
  classical
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun t => by
    have h2 : (Additive.toMul t) ^ 2 = 1 := hW _
    have h3 : Additive.toMul (2 • t) = 1 := by rw [toMul_nsmul]; exact h2
    exact toMul_eq_one.1 h3
  let lin : MulAut W ≃* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    CFSG.QuasithinUnique.Setup.Layer.binPsi ((MulEquiv.multiplicativeAdditive W).symm)
  have lin_apply : ∀ (φ : MulAut W) (w : W),
      lin φ (Additive.ofMul w) = Additive.ofMul (φ w) := by
    intro φ w
    rw [CFSG.QuasithinUnique.Setup.Layer.binPsi_apply]
    rfl
  let ρ : Representation (ZMod 2) SL(3, K) (Additive W) :=
    { toFun := fun s => (lin ((α s : ↥L) : MulAut W)).toLinearMap
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro s t
        ext u
        simp only [map_mul, LinearEquiv.coe_toLinearMap, Module.End.mul_apply]
        rfl }
  have ρ_apply : ∀ (s : SL(3, K)) (w : W),
      ρ s (Additive.ofMul w) = Additive.ofMul (((α s : ↥L) : MulAut W) w) := by
    intro s w
    exact lin_apply ((α s : ↥L) : MulAut W) w
  let X : Additive W ≃ₗ[ZMod 2] Additive W := lin x
  let Cc : Additive W ≃ₗ[ZMod 2] Additive W := lin c
  let subOf : Subgroup W ≃o Submodule (ZMod 2) (Additive W) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  have mem_subOf : ∀ (H : Subgroup W) (w : W), Additive.ofMul w ∈ subOf H ↔ w ∈ H := by
    intro H w
    exact Iff.rfl
  let U₁ : Submodule (ZMod 2) (Additive W) := subOf W₁
  let U₂ : Submodule (ZMod 2) (Additive W) := subOf W₂
  have hU₁_ne : U₁ ≠ ⊥ := by
    intro hbot
    have hW₁ : W₁ = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have h1 : Additive.ofMul w ∈ U₁ := (mem_subOf W₁ w).mpr hw
      rw [hbot, Submodule.mem_bot] at h1
      exact Additive.ofMul.injective (by simpa using h1)
    rw [hW₁] at h₁
    exact absurd h₁.1 (lt_irrefl ⊥)
  have stable : ∀ (H : Subgroup W), StableUnder L H → ∀ (s : SL(3, K)) (u : Additive W),
      u ∈ subOf H → ρ s u ∈ subOf H := by
    intro H hH s u hu
    rw [show u = Additive.ofMul (Additive.toMul u) from rfl, ρ_apply]
    exact (mem_subOf H _).mpr (hH _ (α s).2 _ ((mem_subOf H _).mp hu))
  have hU₁ρ : ∀ (s : SL(3, K)) (u : Additive W), u ∈ U₁ → ρ s u ∈ U₁ :=
    stable W₁ h₁.2.1
  have hU₂ρ : ∀ (s : SL(3, K)) (u : Additive W), u ∈ U₂ → ρ s u ∈ U₂ :=
    stable W₂ h₂.2.1
  let ρ₁ : Representation (ZMod 2) SL(3, K) ↥U₁ :=
    { toFun := fun s => (((lin ((α s : ↥L) : MulAut W)).toLinearMap.comp U₁.subtype).codRestrict
        U₁ (fun u => hU₁ρ s u.1 u.2))
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro s t
        ext u
        simp only [map_mul, LinearEquiv.coe_toLinearMap, Module.End.mul_apply,
          LinearMap.comp_apply, LinearMap.codRestrict_apply]
        rfl }
  have ρ₁_apply : ∀ (s : SL(3, K)) (u : Additive W) (hu : u ∈ U₁),
      ((ρ₁ s ⟨u, hu⟩ : ↥U₁) : Additive W) = ρ s u := by
    intro s u hu
    rfl
  have simple_sub : ∀ (H : Subgroup W), IsIrrOn L H ⊥ →
      ∀ (S : Submodule (ZMod 2) (Additive W)), S ≤ subOf H →
        (∀ (s : SL(3, K)) (u : Additive W), u ∈ S → ρ s u ∈ S) → S = ⊥ ∨ S = subOf H := by
    intro H hH S hSH hSinv
    obtain ⟨J, hJeq, hJle⟩ : ∃ J : Subgroup W, subOf J = S ∧ J ≤ H := by
      refine ⟨subOf.symm S, subOf.apply_symm_apply S, ?_⟩
      rw [← subOf.le_iff_le, subOf.apply_symm_apply]
      exact hSH
    have hJstable : StableUnder L J := by
      intro l hl w hw
      obtain ⟨s, hs⟩ := hα ⟨l, hl⟩
      have h1 : Additive.ofMul w ∈ S := by rw [← hJeq]; exact (mem_subOf J w).mpr hw
      have h2 := hSinv s _ h1
      rw [ρ_apply] at h2
      have h3 : ((α s : ↥L) : MulAut W) w ∈ J := (mem_subOf J _).mp (hJeq ▸ h2)
      change ((⟨l, hl⟩ : ↥L) : MulAut W) w ∈ J
      rw [← hs]
      exact h3
    rcases hH.2.2.2 J hJstable bot_le hJle with hbot | htop
    · exact Or.inl (by rw [← hJeq, hbot, subOf.map_bot])
    · exact Or.inr (by rw [← hJeq, htop])
  have hIrr : ρ₁.IsIrreducible := by
    rw [X7.isIrreducible_iff]
    refine ⟨by rw [Submodule.nontrivial_iff_ne_bot]; exact hU₁_ne, ?_⟩
    intro S hS
    have hSle : S.map U₁.subtype ≤ U₁ := by
      rintro x ⟨y, hy, rfl⟩
      exact y.2
    have hSinv : ∀ (s : SL(3, K)) (u : Additive W), u ∈ S.map U₁.subtype →
        ρ s u ∈ S.map U₁.subtype := by
      rintro s u ⟨y, hy, rfl⟩
      exact ⟨ρ₁ s y, hS s y hy, ρ₁_apply s y.1 y.2⟩
    rcases simple_sub W₁ h₁ (S.map U₁.subtype) hSle hSinv with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have h2 : (x : Additive W) ∈ S.map U₁.subtype := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at h2
      exact Submodule.coe_eq_zero.mp h2
    · right
      rw [eq_top_iff]
      intro x _
      have hx : (x : Additive W) ∈ S.map U₁.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
      have h3 : y = x := Subtype.ext hyx
      rwa [← h3]
  have hnt : ∃ s : SL(3, K), ρ₁ s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hfix₁ : ∀ (l : ↥L) (w : W), w ∈ W₁ → (l : MulAut W) w = w := by
      intro l w hw
      obtain ⟨s, hs⟩ := hα l
      have hw' : Additive.ofMul w ∈ U₁ := (mem_subOf W₁ w).mpr hw
      have h1 : ρ₁ s ⟨Additive.ofMul w, hw'⟩ = ⟨Additive.ofMul w, hw'⟩ := by
        rw [hcon s]; rfl
      have h2 : ρ s (Additive.ofMul w) = Additive.ofMul w := by
        rw [← ρ₁_apply s (Additive.ofMul w) hw']
        exact congrArg Subtype.val h1
      rw [ρ_apply] at h2
      have h3 : ((α s : ↥L) : MulAut W) w = w := Additive.ofMul.injective h2
      rw [← hs]
      exact h3
    have hcinv : ∀ w : W, w ∈ W₂ → c⁻¹ w ∈ W₁ := by
      intro w hw
      rw [← hcW] at hw
      obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
      have hyw' : c y = w := hyw
      rw [← hyw', MulAut.inv_apply_self]
      exact hy
    have hfix₂ : ∀ (l : ↥L) (w : W), w ∈ W₂ → (l : MulAut W) w = w := by
      intro l w hw
      have h1 := hfix₁ l (c⁻¹ w) (hcinv w hw)
      have h2 : (c : MulAut W) ((l : MulAut W) (c⁻¹ w)) =
          (l : MulAut W) ((c : MulAut W) (c⁻¹ w)) :=
        congrArg (fun f : MulAut W => f (c⁻¹ w)) (hc (l : MulAut W) l.2)
      rw [h1, MulAut.apply_inv_self] at h2
      exact h2.symm
    have hLbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      ext w
      change (l : MulAut W) w = w
      have hw : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hw
      rw [← hab, map_mul, hfix₁ ⟨l, hl⟩ a ha, hfix₂ ⟨l, hl⟩ b hb]
    have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2
    haveI := hsimple
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (↥L ⧸ Subgroup.center ↥L)).exists_pair_ne
    haveI hsub : Subsingleton ↥L := by rw [hLbot]; infer_instance
    have hsubq : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
    exact hab (hsubq.elim a b)
  obtain ⟨f, hf0, hcard⟩ := CFSG.CGT.Timmesfeld75.exists_natCard_eq_two_pow (F := K)
  have hf1 : 1 ≤ f := Nat.succ_le_of_lt hf0
  haveI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  let bas : Module.Basis (Fin (Module.finrank (ZMod 2) ↥U₁)) (ZMod 2) ↥U₁ :=
    Module.finBasis (ZMod 2) ↥U₁
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ :=
    B42SL3.exists_label hcard' hf1 ρ₁ bas hIrr hnt
  have hcardW : Nat.card W = 2 ^ rk ↥(⊤ : Subgroup W) := by
    rw [← Nat.card_congr (Subgroup.topEquiv (G := W)).toEquiv]
    exact card_eq_two_pow hW ⊤
  have hfinW : Module.finrank (ZMod 2) (Additive W) = rk ↥(⊤ : Subgroup W) := by
    have hcardAdd : Nat.card (Additive W) = Nat.card W :=
      Nat.card_congr (Equiv.mk Additive.toMul Additive.ofMul (fun _ => rfl) (fun _ => rfl))
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod, hcardAdd, hcardW] at h1
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) h1).symm
  have hfin_le : Module.finrank (ZMod 2) (Additive W) ≤ 12 := by
    rw [hfinW]; exact hrk
  have hcard_subOf : ∀ (H : Subgroup W), Nat.card ↥(subOf H) = Nat.card ↥H := by
    intro H
    exact Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, (mem_subOf H _).mp x.2⟩
        invFun := fun y => ⟨Additive.ofMul y.1, (mem_subOf H _).mpr y.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  have hUinf : U₁ ⊓ U₂ = ⊥ := by
    rw [← subOf.map_inf, hint, subOf.map_bot]
  have hUsup : U₁ ⊔ U₂ = ⊤ := by
    rw [← subOf.map_sup, hsup, subOf.map_top]
  have hcompl : IsCompl U₁ U₂ := by
    rw [isCompl_iff]
    exact ⟨by rw [disjoint_iff, hUinf], by rw [codisjoint_iff, hUsup]⟩
  have hfin_add : Module.finrank (ZMod 2) ↥U₁ + Module.finrank (ZMod 2) ↥U₂ =
      Module.finrank (ZMod 2) (Additive W) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    rw [hUinf, hUsup] at h
    simpa using h.symm
  have hfin12 : Module.finrank (ZMod 2) ↥U₁ = Module.finrank (ZMod 2) ↥U₂ := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U₁)
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U₂)
    rw [Nat.card_zmod] at h1 h2
    have hcard : Nat.card ↥U₁ = Nat.card ↥U₂ := by
      rw [hcard_subOf W₁, hcard_subOf W₂, ← hcW, Subgroup.card_map_of_injective c.injective]
    rw [hcard] at h1
    exact Nat.pow_right_injective (by norm_num : 1 < 2) (h1.symm.trans h2)
  have hdimU₁ : Module.finrank (ZMod 2) ↥U₁ ≤ 6 := by
    have h := hfin_add
    rw [← hfin12] at h
    omega
  have hdimW₀ : Module.finrank K ↥W₀.toSubmodule =
      3 ^ X7a.cntS a b * 8 ^ X7a.cntH a b := by
    rw [e₀.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, X7a.card_TIdx_eq]
  have hdim_le : 3 ^ X7a.cntS a b * 8 ^ X7a.cntH a b ≤ Module.finrank (ZMod 2) ↥U₁ := by
    rw [← hdimW₀]
    calc Module.finrank K ↥W₀.toSubmodule
        ≤ Module.finrank K (Fin (Module.finrank (ZMod 2) ↥U₁) → K) :=
          Submodule.finrank_le W₀.toSubmodule
      _ = Module.finrank (ZMod 2) ↥U₁ := by rw [Module.finrank_fintype_fun_eq_card]; simp
  have hle6 : 3 ^ X7a.cntS a b * 8 ^ X7a.cntH a b ≤ 6 := hdim_le.trans hdimU₁
  have hHc : X7a.cntH a b = 0 := by
    by_contra h
    have h1 : 1 ≤ X7a.cntH a b := Nat.one_le_iff_ne_zero.mpr h
    have h8 : 8 ≤ 8 ^ X7a.cntH a b := by
      calc 8 = 8 ^ 1 := by norm_num
        _ ≤ 8 ^ X7a.cntH a b := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : 1 ≤ 3 ^ X7a.cntS a b := Nat.one_le_pow _ _ (by norm_num)
    have h4 : 8 ^ X7a.cntH a b ≤ 3 ^ X7a.cntS a b * 8 ^ X7a.cntH a b :=
      Nat.le_mul_of_pos_left _ h3
    omega
  have hSc : X7a.cntS a b = 1 := by
    have hS0 : X7a.cntS a b ≠ 0 := by
      intro h0
      have heq : ∀ i, a i = b i := by
        intro i
        by_contra h
        have h2 : i ∈ Finset.univ.filter (fun j => a j ≠ b j) := by simp [h]
        have h3 : (Finset.univ.filter (fun j => a j ≠ b j)).card = 0 := h0
        rw [Finset.card_eq_zero] at h3
        rw [h3] at h2
        exact absurd h2 (by simp)
      have hfalse : ∀ i, a i ≠ true := by
        intro i ha
        have h3 : a i = true ∧ b i = true := ⟨ha, by rw [← heq i]; exact ha⟩
        have h4 : i ∈ Finset.univ.filter (fun j => a j = true ∧ b j = true) := by simp [h3]
        have h5 : (Finset.univ.filter (fun j => a j = true ∧ b j = true)).card = 0 := hHc
        rw [Finset.card_eq_zero] at h5
        rw [h5] at h4
        exact absurd h4 (by simp)
      have ha : a = X7a.zeros f := by
        funext i
        exact Bool.eq_false_iff.mpr (hfalse i)
      have hb : b = X7a.zeros f := by
        rw [← ha]
        exact funext fun i => (heq i).symm
      rcases hne with h | h
      · exact h ha
      · exact h hb
    have h1 : 1 ≤ X7a.cntS a b := Nat.one_le_iff_ne_zero.mpr hS0
    have h3 : 3 ≤ 3 ^ X7a.cntS a b := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ X7a.cntS a b := Nat.pow_le_pow_right (by norm_num) h1
    have hle : 3 ^ X7a.cntS a b ≤ 6 := by
      have h : 3 ^ X7a.cntS a b * 8 ^ X7a.cntH a b = 3 ^ X7a.cntS a b := by
        rw [hHc, pow_zero, mul_one]
      omega
    rcases Nat.lt_or_ge (X7a.cntS a b) 2 with hlt | hge
    · omega
    · have h9 : 9 ≤ 3 ^ X7a.cntS a b := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ X7a.cntS a b := Nat.pow_le_pow_right (by norm_num) hge
      omega
  obtain ⟨i₀, hsingle, hrest⟩ := B42SL3.exists_single_pos hSc hHc
  have key := exists_natural_or_dual hcard' hf1 ρ₁ bas hIrr hSc hHc W₀ e₀
  let N : Submodule (ZMod 2) (Additive W) := U₁.map X.toLinearMap
  have hNdim : Module.finrank (ZMod 2) ↥N = Module.finrank (ZMod 2) ↥U₁ :=
    (Submodule.equivMapOfInjective X.toLinearMap X.injective U₁).finrank_eq.symm
  have hXrel : ∀ (s : SL(3, K)) (u : Additive W), X (ρ s u) = ρ (ν s) (X u) := by
    intro s u
    have hrel : ((α (ν s) : ↥L) : MulAut W) * x = x * ((α s : ↥L) : MulAut W) := by
      rw [hν s]
      group
    calc X (ρ s u) = lin (x * ((α s : ↥L) : MulAut W)) u := by
          show lin x (lin ((α s : ↥L) : MulAut W) u) = _
          rw [← LinearEquiv.mul_apply, ← map_mul]
      _ = lin (((α (ν s) : ↥L) : MulAut W) * x) u := by rw [hrel]
      _ = ρ (ν s) (X u) := by
          show lin (((α (ν s) : ↥L) : MulAut W) * x) u =
            lin ((α (ν s) : ↥L) : MulAut W) (lin x u)
          rw [← LinearEquiv.mul_apply, ← map_mul]
  have hNinv : ∀ (s : SL(3, K)) (u : Additive W), u ∈ N → ρ s u ∈ N := by
    rintro s u ⟨v, hv, rfl⟩
    refine ⟨ρ (ν⁻¹ s) v, hU₁ρ (ν⁻¹ s) v hv, ?_⟩
    have h := hXrel (ν⁻¹ s) v
    rwa [show ν (ν⁻¹ s) = s from MulAut.apply_inv_self _ ν s] at h
  have hNint : N ⊓ U₂ = ⊥ ∨ N ⊓ U₂ = U₂ :=
    simple_sub W₂ h₂ (N ⊓ U₂) inf_le_right
      (fun s u hu => ⟨hNinv s u hu.1, hU₂ρ s u hu.2⟩)
  let π₁ : Additive W →ₗ[ZMod 2] ↥U₁ := U₁.projectionOnto U₂ hcompl
  have hπ₁_left : ∀ x : ↥U₁, π₁ (x : Additive W) = x :=
    Submodule.linearProjOfIsCompl_apply_left hcompl
  have hπ₁_right : ∀ x : ↥U₂, π₁ (x : Additive W) = 0 :=
    Submodule.linearProjOfIsCompl_apply_right hcompl
  have hπ₁_add : ∀ (x : ↥U₁) (y : ↥U₂), π₁ ((x : Additive W) + y) = x := by
    intro x y
    rw [map_add, hπ₁_left, hπ₁_right, add_zero]
  have hπ₁_nat : ∀ (T : Additive W →ₗ[ZMod 2] Additive W), (∀ u ∈ U₁, T u ∈ U₁) →
      (∀ u ∈ U₂, T u ∈ U₂) → ∀ u : Additive W,
      (π₁ (T u) : Additive W) = T ((π₁ u : ↥U₁) : Additive W) := by
    intro T hT₁ hT₂ u
    have hu : u ∈ U₁ ⊔ U₂ := by rw [hUsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
    have e1 : π₁ (T u) = ⟨T a, hT₁ a ha⟩ := by
      have h : T u = T a + T b := by rw [← hab, map_add]
      rw [h]
      exact hπ₁_add ⟨T a, hT₁ a ha⟩ ⟨T b, hT₂ b hb⟩
    have e2 : (π₁ u : ↥U₁) = ⟨a, ha⟩ := by
      have h : u = a + b := hab.symm
      rw [h]
      exact hπ₁_add ⟨a, ha⟩ ⟨b, hb⟩
    rw [e1, e2]
  have hCρ : ∀ (t : SL(3, K)) (w : Additive W),
      Cc ((lin ((α t : ↥L) : MulAut W)) w) = (lin ((α t : ↥L) : MulAut W)) (Cc w) := by
    intro t w
    have h1 : (lin c) * (lin ((α t : ↥L) : MulAut W)) =
        (lin ((α t : ↥L) : MulAut W)) * (lin c) := by
      rw [← map_mul, ← map_mul, hc ((α t : ↥L) : MulAut W) (α t).2]
    calc (lin c) ((lin ((α t : ↥L) : MulAut W)) w) =
          ((lin c) * (lin ((α t : ↥L) : MulAut W))) w := (LinearEquiv.mul_apply ..).symm
      _ = ((lin ((α t : ↥L) : MulAut W)) * (lin c)) w := by rw [h1]
      _ = (lin ((α t : ↥L) : MulAut W)) ((lin c) w) := LinearEquiv.mul_apply ..
  have hcomm : ∀ (t : SL(3, K)) (w : Additive W),
      Cc.symm ((lin ((α t : ↥L) : MulAut W)) w) = (lin ((α t : ↥L) : MulAut W)) (Cc.symm w) := by
    intro t w
    apply Cc.injective
    rw [LinearEquiv.apply_symm_apply]
    have h := hCρ t (Cc.symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have b_exists : ∃ b : ↥U₁ ≃ₗ[ZMod 2] ↥U₁,
      ∀ (s : SL(3, K)) (u : ↥U₁), b (ρ₁ s u) = ρ₁ (ν s) (b u) := by
    have hxN : ∀ u : ↥U₁, (X (u : Additive W)) ∈ N := fun u =>
      Submodule.mem_map.mpr ⟨(u : Additive W), u.2, rfl⟩
    have hCinv : ∀ w : Additive W, w ∈ U₂ → Cc.symm w ∈ U₁ := by
      intro w hw
      have hw' : Additive.toMul w ∈ W₂ := (mem_subOf W₂ _).mp (by
        rwa [show Additive.ofMul (Additive.toMul w) = w from rfl])
      rw [← hcW] at hw'
      obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw'
      have h1 : Cc (Additive.ofMul y) = w := by
        rw [lin_apply, show c y = Additive.toMul w from hyw]
        rfl
      rw [← h1, LinearEquiv.symm_apply_apply]
      exact (mem_subOf W₁ y).mpr hy
    rcases hNint with hcase | hcase
    ·
      have hinj : Function.Injective (π₁.comp N.subtype) := by
        intro u v huv
        have huv' : π₁ ((u : Additive W)) = π₁ ((v : Additive W)) := huv
        have h1 : π₁ ((u : Additive W) - (v : Additive W)) = 0 := by
          rw [map_sub, huv', sub_self]
        have h2 : (u : Additive W) - (v : Additive W) ∈ π₁.ker := (LinearMap.mem_ker).mpr h1
        have h3 : (u : Additive W) - (v : Additive W) ∈ U₂ := by
          rwa [Submodule.linearProjOfIsCompl_ker hcompl] at h2
        have h4 : (u : Additive W) - (v : Additive W) ∈ N := N.sub_mem u.2 v.2
        have h5 : (u : Additive W) - (v : Additive W) = 0 := by
          have h6 : (u : Additive W) - (v : Additive W) ∈ N ⊓ U₂ := ⟨h4, h3⟩
          rw [hcase, Submodule.mem_bot] at h6
          exact h6
        exact Subtype.ext (sub_eq_zero.mp h5)
      let πe : ↥N ≃ₗ[ZMod 2] ↥U₁ := LinearEquiv.ofBijective (π₁.comp N.subtype)
        ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (f := π₁.comp N.subtype) hNdim).mp hinj⟩
      let Xe : ↥U₁ ≃ₗ[ZMod 2] ↥N := Submodule.equivMapOfInjective X.toLinearMap X.injective U₁
      refine ⟨Xe.trans πe, ?_⟩
      intro s u
      apply Subtype.ext
      calc ((Xe.trans πe) (ρ₁ s u) : Additive W) = π₁ (X (ρ₁ s u : Additive W)) := rfl
        _ = π₁ (X (ρ s (u : Additive W))) := by rw [ρ₁_apply s u.1 u.2]
        _ = π₁ (ρ (ν s) (X (u : Additive W))) := by rw [hXrel s (u : Additive W)]
        _ = ρ (ν s) ((π₁ (X (u : Additive W)) : ↥U₁) : Additive W) :=
            hπ₁_nat (ρ (ν s)) (hU₁ρ (ν s)) (hU₂ρ (ν s)) (X (u : Additive W))
        _ = ρ (ν s) (((Xe.trans πe) u : ↥U₁) : Additive W) := rfl
        _ = (ρ₁ (ν s) ((Xe.trans πe) u) : Additive W) :=
            (ρ₁_apply (ν s) ((Xe.trans πe) u).1 ((Xe.trans πe) u).2).symm
    ·
      have hU₂N : U₂ ≤ N := by rw [← hcase]; exact inf_le_left
      have hNU₂ : N = U₂ := by
        refine (Submodule.eq_of_le_of_finrank_eq hU₂N ?_).symm
        rw [hNdim, hfin12]
      let Φ : ↥U₁ →ₗ[ZMod 2] ↥U₁ :=
        ((Cc.symm.toLinearMap.comp X.toLinearMap).comp U₁.subtype).codRestrict U₁
          (fun u => hCinv _ (hNU₂ ▸ hxN u))
      have hinj : Function.Injective Φ := by
        intro u v huv
        have h1 : Φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have h2 : Cc.symm (X ((u - v : ↥U₁) : Additive W)) = 0 :=
          show Cc.symm (X ((u - v : ↥U₁) : Additive W)) = 0 from congrArg Subtype.val h1
        have h3 : X ((u - v : ↥U₁) : Additive W) = 0 :=
          Cc.symm.injective (by rw [h2, map_zero])
        have h4 : ((u - v : ↥U₁) : Additive W) = 0 := X.injective (by rw [h3, map_zero])
        exact Subtype.ext (sub_eq_zero.mp h4)
      let b : ↥U₁ ≃ₗ[ZMod 2] ↥U₁ := LinearEquiv.ofBijective Φ
        ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ) rfl).mp hinj⟩
      refine ⟨b, ?_⟩
      intro s u
      apply Subtype.ext
      calc (b (ρ₁ s u) : Additive W) = Cc.symm (X (ρ₁ s u : Additive W)) := rfl
        _ = Cc.symm (X (ρ s (u : Additive W))) := by rw [ρ₁_apply s u.1 u.2]
        _ = Cc.symm (ρ (ν s) (X (u : Additive W))) := by rw [hXrel s (u : Additive W)]
        _ = ρ (ν s) (Cc.symm (X (u : Additive W))) := by
            show Cc.symm ((lin ((α (ν s) : ↥L) : MulAut W)) (X (u : Additive W))) =
              (lin ((α (ν s) : ↥L) : MulAut W)) (Cc.symm (X (u : Additive W)))
            exact hcomm (ν s) (X (u : Additive W))
        _ = ρ (ν s) ((b u : ↥U₁) : Additive W) := rfl
        _ = (ρ₁ (ν s) (b u) : Additive W) := (ρ₁_apply (ν s) (b u).1 (b u).2).symm
  obtain ⟨b, hb⟩ := b_exists
  have hptr : ∀ g : SL(3, K), X7a.tauSL K g = CatalogueBGraphForm.slGraphAut 3 K g := by
    intro g
    apply Subtype.ext
    rw [X7a.tauSL_coe, CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
    rfl
  rcases key with ⟨E, hE⟩ | ⟨E, hE⟩
  · let φ : (Fin 3 → K) ≃ (Fin 3 → K) :=
      Equiv.trans (Equiv.symm E.toEquiv) (Equiv.trans b.toEquiv E.toEquiv)
    have hφ : ∀ (g : SL(3, K)) (v : Fin 3 → K),
        φ (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          ((ν g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v := by
      intro g v
      have h1 : E.symm (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          ρ₁ g (E.symm v) := by
        apply E.injective
        rw [hE g (E.symm v), AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      show E (b (E.symm (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v))) =
        ((ν g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ E (b (E.symm v))
      rw [h1, hb g (E.symm v), hE (ν g) (b (E.symm v))]
    exact L34Out.not_exists_equivariant hgraph ⟨φ, φ.bijective, hφ⟩
  · let φ : (Fin 3 → K) ≃ (Fin 3 → K) :=
      Equiv.trans (Equiv.symm E.toEquiv) (Equiv.trans b.toEquiv E.toEquiv)
    have hφ : ∀ (g : SL(3, K)) (v : Fin 3 → K),
        φ (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          (((CatalogueBGraphForm.slGraphAut 3 K * ν *
            CatalogueBGraphForm.slGraphAut 3 K) g : SL(3, K)) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ φ v := by
      intro g v
      have h1 : E.symm (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          ρ₁ (X7a.tauSL K g) (E.symm v) := by
        apply E.injective
        rw [hE (X7a.tauSL K g) (E.symm v), AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          X7a.tauSL_tauSL]
      show E (b (E.symm (((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v))) =
        (((CatalogueBGraphForm.slGraphAut 3 K * ν *
          CatalogueBGraphForm.slGraphAut 3 K) g : SL(3, K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ E (b (E.symm v))
      rw [h1, hb (X7a.tauSL K g) (E.symm v), hE (ν (X7a.tauSL K g)) (b (E.symm v))]
      simp only [MulAut.mul_apply]
      rw [hptr (ν (X7a.tauSL K g)), hptr g]
    exact L34Out.not_exists_equivariant (isGraphType_graph_conj hgraph) ⟨φ, φ.bijective, hφ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
