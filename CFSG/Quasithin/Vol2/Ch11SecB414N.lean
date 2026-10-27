module

public import CFSG.Quasithin.Vol2.Ch11SecB414H
public import CFSG.Quasithin.Vol2.Ch11SecB414F
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open Subgroup CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups Matrix

section Adj

variable {F : Type} [Field F] [CharP F 2]

theorem twistMat_zero (g : SL(3, F)) : twistMat F 0 g = (g : Matrix (Fin 3) (Fin 3) F) := by
  ext a b
  rw [twistMat_apply, frK_apply]
  simp

theorem adjRep_mulVec_eq (s : SL(3, F)) (c : Fin 8 → F) :
    adjRep F 0 s *ᵥ c = adG (Matrix.SpecialLinearGroup.toGL s) c := by
  have h := Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (adjEnd F 0 s)
  have h2 : adjRep F 0 s *ᵥ c = Matrix.toLinAlgEquiv' (adjRep F 0 s) c := rfl
  rw [h2]
  change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (adjEnd F 0 s)) c = _
  rw [h, adjEnd_apply, adjAd_apply, conjMat, twistMat_zero, twistMat_zero]
  rfl

end Adj

section Section

variable {G : Type} [Group G] [Finite G] {Γ V Z L X : Subgroup G} {F : Type} [Field F]
  [Fintype F] {α : ↥Γ →* GL (Fin 3) F ⧸ center (GL (Fin 3) F)}
  {P : Subgroup (GL (Fin 3) F ⧸ center (GL (Fin 3) F))}

omit [Finite G] in
theorem Hyp.isTwAdjointSection (hyp : Hyp Γ V Z L X F α P) [Fact (IsElem V Z)] {k : ℕ}
    (Φ : (Fin 8 → F) ≃+ SecU V Z)
    (hΦ : ∀ (g : GL (Fin 3) F) (v : Fin 8 → F),
      glRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker g (Φ v) =
        Φ (((g : Matrix (Fin 3) (Fin 3) F).det) ^ k • adG g v)) :
    IsTwAdjointSection k Γ V Z α.ker F := by
  have := hyp.charP
  let β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F) :=
    { toFun := fun v => Multiplicative.ofAdd (Xm (Φ.symm (secπ V Z v)))
      map_one' := by
        rw [secπ_one, map_zero, ← XmL_apply, map_zero]
        rfl
      map_mul' := fun v w => by
        rw [secπ_mul, map_add, ← XmL_apply, map_add]
        rfl }
  have hβ : ∀ v, Multiplicative.toAdd (β v) = Xm (Φ.symm (secπ V Z v)) := fun _ => rfl
  refine ⟨hyp.le_normalizer_V, hyp.lt.le, α, hyp.surj, rfl, β, fun v => ?_, fun M hM => ?_, ?_,
    fun γ u v huv g hg => ?_⟩
  · rw [hβ]
    exact trace_Xm F _
  · obtain ⟨v, hv⟩ := secπ_surjective V Z (Φ (co M))
    refine ⟨v, ?_⟩
    rw [hβ, hv, AddEquiv.symm_apply_apply]
    exact Xm_co F hM
  · ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← secπ_eq_zero_iff]
    constructor
    · intro h
      have h1 : Xm (Φ.symm (secπ V Z v)) = 0 := congrArg Multiplicative.toAdd h
      have h2 : Φ.symm (secπ V Z v) = 0 := by
        rw [← co_Xm (Φ.symm (secπ V Z v)), h1]
        funext i
        fin_cases i <;> rfl
      rw [← Φ.apply_symm_apply (secπ V Z v), h2, map_zero]
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hβ, h, map_zero, ← XmL_apply, map_zero]
      rfl
  · have hvu : v = conjV V γ (hyp.le_normalizer_V γ.2) u := Subtype.ext huv
    have h1 : secπ V Z v = Φ (((g : Matrix (Fin 3) (Fin 3) F).det) ^ k •
        adG g (Φ.symm (secπ V Z u))) := by
      rw [← hΦ, Φ.apply_symm_apply,
        glRep_eq hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hg, secRep_secπ, hvu]
    rw [hβ, hβ, h1, AddEquiv.symm_apply_apply, ← XmL_apply, map_smul, XmL_apply, adG,
      adjAd_apply, Xm_co F (by rw [trace_conj_eq F _ _ _ (by rw [← Units.val_mul,
        inv_mul_cancel, Units.val_one]), trace_Xm])]
    rfl

end Section

section Embedding

variable {G : Type} [Group G] [Finite G] {Γ V Z L X : Subgroup G} {F : Type} [Field F]
  [Fintype F] {α : ↥Γ →* GL (Fin 3) F ⧸ center (GL (Fin 3) F)}
  {P : Subgroup (GL (Fin 3) F ⧸ center (GL (Fin 3) F))}

theorem Hyp.exists_adj_embedding (hyp : Hyp Γ V Z L X F α P) [Fact (IsElem V Z)] :
    ∃ Φ₀ : (Fin 8 → F) →+ SecU V Z, Function.Injective Φ₀ ∧
      ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 → ∀ v,
        Φ₀ (adG g v) =
          glRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker g (Φ₀ v) := by
  have := hyp.charP
  have hF := hyp.card
  set ρG := glRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker with hρG
  set ρ := slRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker with hρ
  have hirrG : ρG.IsIrreducible :=
    glRep_isIrreducible hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hyp.lt hyp.irred
  have : Nontrivial (SecU V Z) :=
    ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρG).mp hirrG).1
  obtain ⟨ω₀, h0, h1⟩ := exists_ne_zero_ne_one hF
  set ω : Fˣ := Units.mk0 ω₀ h0 with hωdef
  have hω3 : ω ^ 3 = 1 := Units.ext (by simp [ω, pow_three_eq_one hF h0 h1])
  have hω : orderOf ω = 3 := orderOf_eq_prime hω3 fun h => h1 (by
    have := congrArg Units.val h
    simpa [ω] using this)
  obtain ⟨U₀, hU₀⟩ := exists_minimal_of_wellFoundedLT
    (fun W : Submodule (ZMod 2) (SecU V Z) => W ≠ ⊥ ∧ ∀ s : SL(3, F), ∀ u ∈ W, ρ s u ∈ W)
    ⟨⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  let W₀ : Subrepresentation ρ := ⟨U₀, fun s _ hu => hU₀.prop.2 s _ hu⟩
  set ρ₀ := W₀.toRepresentation with hρ₀
  have hirr₀ : ρ₀.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hU₀.prop.1, fun N hN => ?_⟩
    have hN'le : N.map U₀.subtype ≤ U₀ := by
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    have hN'st : ∀ s : SL(3, F), ∀ u ∈ N.map U₀.subtype, ρ s u ∈ N.map U₀.subtype := by
      rintro s _ ⟨u, hu, rfl⟩
      exact ⟨ρ₀ s u, hN s u hu, rfl⟩
    by_cases h0 : N.map U₀.subtype = ⊥
    · left
      rw [eq_bot_iff]
      intro u hu
      have : (u : SecU V Z) ∈ N.map U₀.subtype := ⟨u, hu, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot _).mpr (Subtype.ext this)
    · right
      have h := hU₀.eq_of_le ⟨h0, hN'st⟩ hN'le
      apply Submodule.map_injective_of_injective U₀.injective_subtype
      rw [Submodule.map_subtype_top]
      exact h
  have hnt₀ : ∃ x, ρ₀ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    let Fx : Submodule (ZMod 2) (SecU V Z) :=
      { carrier := {u | ∀ s : SL(3, F), ρ s u = u}
        add_mem' := fun ha hb s => by rw [map_add, ha s, hb s]
        zero_mem' := fun s => map_zero _
        smul_mem' := fun c u hu s => by rw [map_smul, hu s] }
    have hFx : ∀ g, ∀ u ∈ Fx, ρG g u ∈ Fx := by
      intro g u hu s
      have hs' : ((g⁻¹ * Matrix.SpecialLinearGroup.toGL s * g : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).det = 1 := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          Matrix.SpecialLinearGroup.coe_GL_coe_matrix, s.2, mul_one, ← Matrix.det_mul,
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      let s' : SL(3, F) := ⟨_, hs'⟩
      have hss : Matrix.SpecialLinearGroup.toGL s * g = g * Matrix.SpecialLinearGroup.toGL s' := by
        rw [show Matrix.SpecialLinearGroup.toGL s' = g⁻¹ * Matrix.SpecialLinearGroup.toGL s * g
          from Units.ext rfl]
        group
      show ρG (Matrix.SpecialLinearGroup.toGL s) (ρG g u) = ρG g u
      rw [← Module.End.mul_apply, ← map_mul, hss, map_mul, Module.End.mul_apply]
      exact congrArg _ (hu s')
    have hU₀Fx : U₀ ≤ Fx := fun u hu s => by
      have h := congrArg (fun f => (f ⟨u, hu⟩ : SecU V Z)) (hcon s)
      exact h
    rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρG).mp hirrG).2 Fx hFx with h | h
    · exact hU₀.prop.1 (eq_bot_iff.mpr (h ▸ hU₀Fx))
    · obtain ⟨γ, hγ⟩ := hyp.surj
        (QuotientGroup.mk' (center (GL (Fin 3) F)) (Matrix.SpecialLinearGroup.toGL (dT 1 ω)))
      have hσ : secRep V Z Γ hyp.le_normalizer_V hyp.le_normalizer_Z γ = 1 := by
        rw [← glRep_eq hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hγ.symm]
        refine LinearMap.ext fun u => ?_
        have hu : u ∈ Fx := by
          rw [h]
          exact Submodule.mem_top
        exact hu (dT 1 ω)
      have hα1 : α γ = 1 := (hyp.ker_iff γ).mpr
        ((secRep_eq_one_iff V Z Γ hyp.le_normalizer_V hyp.le_normalizer_Z γ).mp hσ)
      rw [hα1, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Matrix.GeneralLinearGroup.center_eq_range_scalar] at hγ
      obtain ⟨c, hc⟩ := hγ
      have e0 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) hc
      have e1 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        dT_coe, dTMat] at e0 e1
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e0 e1
      apply h1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_one] at e0 e1
      have e2 : (ω : F) = ω₀ := rfl
      rw [← e2, ← e1, e0]
  have hcen₀ : ρ₀ (dT ω ω) = 1 := by
    have h := slRep_dT_omega hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hω3
    refine LinearMap.ext fun u => Subtype.ext ?_
    show ρ (dT ω ω) u = u
    rw [h]
    rfl
  have hdiv₀ : ∃ m, Nat.card W₀.toSubmodule =
      Nat.card {u : W₀.toSubmodule // ρ₀ (dT 1 ω) u = u} * 16 ^ m := by
    obtain ⟨m, hm⟩ := hyp.exists_card_eq_fix hω3 U₀ hU₀.prop.2
    refine ⟨m, ?_⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun u => Subtype.ext_iff)]
    exact hm
  obtain ⟨H, hH⟩ := exists_adjEquiv hF ρ₀ hirr₀ hnt₀ hω hcen₀ hdiv₀
  refine ⟨U₀.subtype.toAddMonoidHom.comp H.toAddMonoidHom,
    Subtype.val_injective.comp H.injective, fun g hg v => ?_⟩
  let s : SL(3, F) := ⟨g, hg⟩
  have hgs : g = Matrix.SpecialLinearGroup.toGL s := Units.ext rfl
  rw [hgs, ← adjRep_mulVec_eq]
  show ((H (adjRep F 0 s *ᵥ v) : W₀.toSubmodule) : SecU V Z) = ρ s (H v)
  rw [hH]
  rfl

end Embedding

theorem lemmaB414Class_holds : LemmaB414Class := by
  intro G _ _ Γ V Z L X F _ _ α P hyp
  have : Fact (IsElem V Z) := ⟨hyp.isElem⟩
  have := hyp.charP
  obtain ⟨Φ₀, hinj, hΦ₀⟩ := hyp.exists_adj_embedding
  obtain ⟨k, hk, Φ, hΦ⟩ := exists_twAdj_equiv hyp.card
    (glRep hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker)
    (glRep_isIrreducible hyp.le_normalizer_V hyp.le_normalizer_Z hyp.surj hyp.hker hyp.lt
      hyp.irred) Φ₀ hinj hΦ₀
  exact ⟨k, hk, hyp.isTwAdjointSection Φ hΦ⟩

end CFSG.Quasithin.H13.Ch4.B414
