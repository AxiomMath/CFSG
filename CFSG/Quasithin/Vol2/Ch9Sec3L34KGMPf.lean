module

public import CFSG.Quasithin.Vol2.Ch9L34BinClass
public import CFSG.Quasithin.Background.L34BinMult
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGM

public section

namespace CFSG.Quasithin.H13.Ch9.L34B

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.L34Bin
open CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups

theorem zSL_mem_center : zSL ∈ Subgroup.center (SL(3, F4)) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨omegaU, by rw [Fintype.card_fin]; exact (omega_pow_eq_one_iff 3).mpr rfl, ?_⟩
  have h := coe_toGL_zSL
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
  rw [h]
  rfl

theorem uSL_not_mem_center : uSL (f4c 1) 0 0 ∉ Subgroup.center (SL(3, F4)) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrFun (congrFun hr 0) 1
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at h
  exact absurd (congrArg F4.code h) (by decide)

theorem exists_hom_of_isPSL {L : Type} [Group L] (h : IsPSL 3 2 2 L) :
    ∃ ψ : SL(3, F4) →* L, Function.Surjective ψ ∧ ψ zSL = 1 ∧
      ψ (uSL (f4c 1) 0 0) ≠ 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : Nat.card F4 = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card, F4.card]
    norm_num
  let eK : K ≃+* F4 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 2 (by norm_num) hK).trans
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F4 2 2 (by norm_num) hF4).symm
  let E : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4 :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eK (Fin 3)))
  refine ⟨E.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_, ?_⟩
  · exact E.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr zSL_mem_center, map_one]
  · intro h1
    apply uSL_not_mem_center
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
      ← map_one E.symm] at h1
    exact (QuotientGroup.eq_one_iff _).mp (E.symm.injective h1)

theorem exists_model {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] (σ : Representation (ZMod 2) SL(3, F4) M)
    (hirr : ∀ N : Submodule (ZMod 2) M, (∀ g, ∀ v ∈ N, σ g v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hZ : σ zSL = 1) (hnt : ∃ g, σ g ≠ 1) :
    (∃ e : M ≃ₗ[ZMod 2] (Fin 9 → ZMod 2), ∀ g v, e (σ g v) = (R9 g).mulVec (e v)) ∨
      (∃ e : M ≃ₗ[ZMod 2] (Fin 9 → ZMod 2), ∀ g v, e (σ g v) = (R9g g).mulVec (e v)) ∨
      (∃ e : M ≃ₗ[ZMod 2] (Fin 16 → ZMod 2), ∀ g v, e (σ g v) = (R16 g).mulVec (e v)) ∨
      (∃ e : M ≃ₗ[ZMod 2] (Fin 64 → ZMod 2), ∀ g v, e (σ g v) = (R64 g).mulVec (e v)) := by
  classical
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) M
  let ρ₀ : SL(3, F4) →* Matrix (Fin (Module.finrank (ZMod 2) M))
      (Fin (Module.finrank (ZMod 2) M)) (ZMod 2) :=
    { toFun := fun g => LinearMap.toMatrix b b (σ g)
      map_one' := by rw [map_one, Module.End.one_eq_id, LinearMap.toMatrix_id]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }
  have hρ₀ : ∀ g v, b.equivFun (σ g v) = (ρ₀ g).mulVec (b.equivFun v) := fun g v => by
    simp only [Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b (σ g) v).symm
  obtain ⟨g₀, hg₀⟩ := hnt
  have hM : Nontrivial M := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hg₀ (LinearMap.ext fun v => Subsingleton.elim _ _)
  have hn : 0 < Module.finrank (ZMod 2) M := Module.finrank_pos
  have hirr₀ : ∀ N : Submodule (ZMod 2) (Fin (Module.finrank (ZMod 2) M) → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    rcases hirr (N.comap b.equivFun.toLinearMap) (fun g v hv => by
      show b.equivFun (σ g v) ∈ N
      rw [hρ₀]
      exact hN g _ hv) with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have : b.equivFun.symm y ∈ N.comap b.equivFun.toLinearMap := by
        show b.equivFun (b.equivFun.symm y) ∈ N
        rwa [LinearEquiv.apply_symm_apply]
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← b.equivFun.apply_symm_apply y, this, map_zero]
    · right
      rw [eq_top_iff]
      intro y _
      have : b.equivFun.symm y ∈ N.comap b.equivFun.toLinearMap := by
        rw [h]
        exact Submodule.mem_top
      have h2 : b.equivFun (b.equivFun.symm y) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at h2
  have hZ₀ : ρ₀ zSL = 1 := by
    show LinearMap.toMatrix b b (σ zSL) = 1
    rw [hZ, Module.End.one_eq_id, LinearMap.toMatrix_id]
  have hnt₀ : ∃ g, ρ₀ g ≠ 1 := ⟨g₀, fun h => hg₀ (by
    have h1 : LinearMap.toMatrix b b (σ g₀) = LinearMap.toMatrix b b LinearMap.id := by
      rw [LinearMap.toMatrix_id]
      exact h
    rw [(LinearMap.toMatrix b b).injective h1, Module.End.one_eq_id])⟩
  have key : ∀ {m : ℕ} (R : SL(3, F4) →* Matrix (Fin m) (Fin m) (ZMod 2)),
      (∃ M₀ : Matrix (Fin m) (Fin (Module.finrank (ZMod 2) M)) (ZMod 2),
        Function.Bijective M₀.mulVec ∧ ∀ g, M₀ * ρ₀ g = R g * M₀) →
      ∃ e : M ≃ₗ[ZMod 2] (Fin m → ZMod 2), ∀ g v, e (σ g v) = (R g).mulVec (e v) := by
    rintro m R ⟨M₀, hbij, hcomm⟩
    refine ⟨b.equivFun.trans (LinearEquiv.ofBijective M₀.mulVecLin hbij), fun g v => ?_⟩
    show M₀.mulVec (b.equivFun (σ g v)) = (R g).mulVec (M₀.mulVec (b.equivFun v))
    rw [hρ₀, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  rcases classify ρ₀ hn hirr₀ hZ₀ hnt₀ with h | h | h | h
  · exact Or.inl (key R9 h)
  · exact Or.inr (Or.inl (key R9g h))
  · exact Or.inr (Or.inr (Or.inl (key R16 h)))
  · exact Or.inr (Or.inr (Or.inr (key R64 h)))

section Models

variable {G E : Type} [Group G] [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def IsModelOf (ρ : G →* Module.End (ZMod 2) E) {m : ℕ}
    (R : G →* Matrix (Fin m) (Fin m) (ZMod 2)) (W : Submodule (ZMod 2) E) : Prop :=
  ∃ (hW : IsInvSub ρ W) (e : W ≃ₗ[ZMod 2] (Fin m → ZMod 2)),
    ∀ g (w : W), e ⟨ρ g w, hW g w w.2⟩ = (R g).mulVec (e w)

theorem card_of_isModelOf {ρ : G →* Module.End (ZMod 2) E} {m : ℕ}
    {R : G →* Matrix (Fin m) (Fin m) (ZMod 2)} {W : Submodule (ZMod 2) E}
    (h : IsModelOf ρ R W) : Nat.card W = 2 ^ m := by
  obtain ⟨-, e, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem false_of_isModelOf [Finite E] {ρ : G →* Module.End (ZMod 2) E} {m : ℕ}
    (R : G →* Matrix (Fin m) (Fin m) (ZMod 2)) {U : Set G}
    (hR : ∀ v v' : Fin m → ZMod 2, v ≠ 0 → v' ≠ 0 → (∀ u ∈ U, (R u).mulVec v = v) →
      (∀ u ∈ U, (R u).mulVec v' = v') →
      ∃ S : Matrix (Fin m) (Fin m) (ZMod 2), (∀ g, S * R g = R g * S) ∧ S.mulVec v = v')
    {c : E} (hc : ∀ u ∈ U, ρ u c = c) (hgen : ∀ N, IsInvSub ρ N → c ∈ N → N = ⊤)
    (𝒲 : Set (Submodule (ZMod 2) E))
    (h𝒲 : ∀ W ∈ 𝒲, IsInvSub ρ W ∧ ∀ M, IsInvSub ρ M → M ≤ W → M = ⊥ ∨ M = W)
    (htop : sSup 𝒲 = ⊤) {W₁ W₂ : Submodule (ZMod 2) E} (h₁ : W₁ ∈ 𝒲) (h₂ : W₂ ∈ 𝒲)
    (hne : W₁ ≠ W₂) (hW₂0 : W₂ ≠ ⊥) (hm₁ : IsModelOf ρ R W₁) (hm₂ : IsModelOf ρ R W₂) :
    False := by
  obtain ⟨hW₁, hirr₁⟩ := h𝒲 W₁ h₁
  obtain ⟨hW₂, hirr₂⟩ := h𝒲 W₂ h₂
  have hcard : Nat.card W₁ = Nat.card W₂ := by
    rw [card_of_isModelOf hm₁, card_of_isModelOf hm₂]
  have hinf : IsInvSub ρ (W₁ ⊓ W₂) := fun g v hv => ⟨hW₁ g v hv.1, hW₂ g v hv.2⟩
  have h₁₂ : W₁ ⊓ W₂ = ⊥ := by
    rcases hirr₁ _ hinf inf_le_left with h | h
    · exact h
    · exfalso
      have hle : W₁ ≤ W₂ := h ▸ inf_le_right
      rcases hirr₂ _ hW₁ hle with h' | h'
      · apply hW₂0
        rw [h'] at hcard
        have h1 : Nat.card (⊥ : Submodule (ZMod 2) E) = 1 := by
          rw [Nat.card_eq_one_iff_unique]
          exact ⟨inferInstance, inferInstance⟩
        rw [h1] at hcard
        have : Subsingleton W₂ := (Nat.card_eq_one_iff_unique.mp hcard.symm).1
        exact (Submodule.subsingleton_iff_eq_bot).mp this
      · exact hne h'
  have hsup : IsInvSub ρ (W₁ ⊔ W₂) := by
    intro g v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hW₁ g a ha) (hW₂ g b hb)
  obtain ⟨C, hC, hcompl⟩ := exists_isCompl_of_sSup ρ 𝒲 h𝒲 htop hsup
  obtain ⟨hW₁', e₁, he₁⟩ := hm₁
  obtain ⟨hW₂', e₂, he₂⟩ := hm₂
  refine false_of_two_copies hc hgen hW₁ hW₂ hC h₁₂ hcompl hW₂0 (e₁.trans e₂.symm)
    (fun g w => ?_) (fun w w' hw hw' hfw hfw' => ?_)
  ·
    have h1 : e₂ ((e₁.trans e₂.symm) ⟨ρ g w, hW₁ g w w.2⟩) =
        e₂ ⟨ρ g ((e₁.trans e₂.symm) w), hW₂ g _ ((e₁.trans e₂.symm) w).2⟩ := by
      rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he₂, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, he₁]
    exact congrArg Subtype.val (e₂.injective h1)
  ·
    have hfix : ∀ y : W₂, (∀ u ∈ U, ρ u y = y) → ∀ u ∈ U, (R u).mulVec (e₂ y) = e₂ y :=
      fun y hy u hu => by
        rw [← he₂]
        congr 1
        exact Subtype.ext (hy u hu)
    have hne0 : ∀ y : W₂, y ≠ 0 → e₂ y ≠ 0 := fun y hy h => hy (by
      have := congrArg e₂.symm h
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this)
    obtain ⟨S, hS, hSv⟩ := hR _ _ (hne0 w hw) (hne0 w' hw') (hfix w hfw) (hfix w' hfw')
    refine ⟨e₂.symm.toLinearMap ∘ₗ S.mulVecLin ∘ₗ e₂.toLinearMap, fun g y => ?_, ?_⟩
    · have h1 : e₂ ((e₂.symm.toLinearMap ∘ₗ S.mulVecLin ∘ₗ e₂.toLinearMap)
          ⟨ρ g y, hW₂ g y y.2⟩) = e₂ ⟨ρ g ((e₂.symm.toLinearMap ∘ₗ S.mulVecLin ∘ₗ
            e₂.toLinearMap) y), hW₂ g _ ((e₂.symm.toLinearMap ∘ₗ S.mulVecLin ∘ₗ
              e₂.toLinearMap) y).2⟩ := by
        rw [he₂]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
          Matrix.mulVecLin_apply]
        rw [he₂, Matrix.mulVec_mulVec, hS, ← Matrix.mulVec_mulVec]
      exact congrArg Subtype.val (e₂.injective h1)
    · apply e₂.injective
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        Matrix.mulVecLin_apply, hSv]

end Models

@[expose, instance_reducible] noncomputable def modV {V : Type} [CommGroup V]
    (h : ∀ v : V, v ^ 2 = 1) : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule fun x => by
    show Additive.ofMul (Additive.toMul x ^ 2) = 0
    rw [h]
    rfl

section Lin

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] def linV : MulAut V →* Module.End (ZMod 2) (Additive V) where
  toFun a :=
    { toFun := fun m => Additive.ofMul (a (Additive.toMul m))
      map_add' := fun m m' => by rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun c m => by
        rw [RingHom.id_apply, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul,
          Nat.cast_smul_eq_nsmul, toMul_nsmul, map_pow, ofMul_pow] }
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem linV_injective : Function.Injective (linV (V := V)) := fun _ _ h =>
  MulEquiv.ext fun v => Additive.ofMul.injective (LinearMap.congr_fun h (Additive.ofMul v))

theorem eq_bot_or_top_of_irr {X : Subgroup (MulAut V)}
    (hirr : XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤) {N : Submodule (ZMod 2) (Additive V)}
    (hN : ∀ x ∈ X, ∀ m ∈ N, linV x m ∈ N) : N = ⊥ ∨ N = ⊤ := by
  let J : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ N}
      mul_mem' := fun {v w} hv hw => by
        show Additive.ofMul (v * w) ∈ N
        rw [ofMul_mul]
        exact N.add_mem hv hw
      one_mem' := by
        show Additive.ofMul (1 : V) ∈ N
        rw [ofMul_one]
        exact N.zero_mem
      inv_mem' := fun {v} hv => by
        show Additive.ofMul v⁻¹ ∈ N
        rw [ofMul_inv]
        exact N.neg_mem hv }
  have hJ : XMod.IsInv ↥X J := fun a v hv => hN a a.2 (Additive.ofMul v) hv
  rcases hirr.2 J hJ bot_le le_top with h | h
  · left
    rw [eq_bot_iff]
    intro m hm
    have h1 : Additive.toMul m ∈ J := hm
    rw [h, Subgroup.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact Additive.toMul.injective h1
  · right
    rw [eq_top_iff]
    intro m _
    have h1 : Additive.toMul m ∈ J := h ▸ Subgroup.mem_top _
    exact h1

theorem exists_mulEquiv_of_isModelOf {k : ℕ} {φ : SL(3, F4) →* MulAut V}
    (σ : SL(3, F4) →* MulAut (H.Mathieu.Wn k)) (h : IsModelOf (linV.comp φ) (autMat.comp σ) ⊤) :
    ∃ e : V ≃* H.Mathieu.Wn k, ∀ g, MulAut.congr e (φ g) = σ g := by
  obtain ⟨hW, E, hE⟩ := h
  let E' : Additive V ≃ₗ[ZMod 2] (Fin k → ZMod 2) := Submodule.topEquiv.symm.trans E
  have hE' : ∀ g (m : Additive V), E' (linV (φ g) m) = (autMat (σ g)).mulVec (E' m) :=
    fun g m => hE g ⟨m, Submodule.mem_top⟩
  let e : V ≃* H.Mathieu.Wn k :=
    { toFun := fun v => Multiplicative.ofAdd (E' (Additive.ofMul v))
      invFun := fun w => Additive.toMul (E'.symm (Multiplicative.toAdd w))
      left_inv := fun v => by simp
      right_inv := fun w => by simp
      map_mul' := fun v w => by simp [ofMul_mul, map_add, ofAdd_add] }
  refine ⟨e, fun g => MulEquiv.ext fun w => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective w
  show e (φ g (e.symm (e v))) = σ g (e v)
  rw [MulEquiv.symm_apply_apply]
  have h1 := hE' g (Additive.ofMul v)
  rw [autMat_mulVec] at h1
  show Multiplicative.ofAdd (E' (Additive.ofMul (φ g v))) = σ g (Multiplicative.ofAdd (E'
    (Additive.ofMul v)))
  have h2 : linV (φ g) (Additive.ofMul v) = Additive.ofMul (φ g v) := rfl
  rw [← h2, h1, ofAdd_toAdd]

theorem exists_mulEquiv18 {φ : SL(3, F4) →* MulAut V} {A B : Submodule (ZMod 2) (Additive V)}
    (hAB : IsCompl A B) (hA : IsModelOf (linV.comp φ) R9 A)
    (hB : IsModelOf (linV.comp φ) R9g B) :
    ∃ e : V ≃* W18, ∀ g, MulAut.congr e (φ g) = slRep rho18GL g := by
  obtain ⟨hAi, eA, heA⟩ := hA
  obtain ⟨hBi, eB, heB⟩ := hB
  let E' : Additive V ≃ₗ[ZMod 2] (Fin 9 → ZMod 2) × (Fin 9 → ZMod 2) :=
    (Submodule.prodEquivOfIsCompl A B hAB).symm.trans (eA.prodCongr eB)
  have hE' : ∀ g (m : Additive V), E' (linV (φ g) m) =
      ((R9 g).mulVec (E' m).1, (R9g g).mulVec (E' m).2) := by
    intro g m
    have hpA : A.projectionOnto B hAB (linV (φ g) m) =
        ⟨linV (φ g) (A.projectionOnto B hAB m), hAi g _ (A.projectionOnto B hAB m).2⟩ :=
      Subtype.ext (projectionOnto_comm hAi hBi hAB g m)
    have hpB : B.projectionOnto A hAB.symm (linV (φ g) m) =
        ⟨linV (φ g) (B.projectionOnto A hAB.symm m), hBi g _ (B.projectionOnto A hAB.symm m).2⟩ :=
      Subtype.ext (projectionOnto_comm hBi hAi hAB.symm g m)
    show (eA ((Submodule.prodEquivOfIsCompl A B hAB).symm (linV (φ g) m)).1,
        eB ((Submodule.prodEquivOfIsCompl A B hAB).symm (linV (φ g) m)).2) =
      ((R9 g).mulVec (eA ((Submodule.prodEquivOfIsCompl A B hAB).symm m).1),
        (R9g g).mulVec (eB ((Submodule.prodEquivOfIsCompl A B hAB).symm m).2))
    rw [Submodule.prodEquivOfIsCompl_symm_apply, Submodule.prodEquivOfIsCompl_symm_apply, hpA, hpB]
    exact Prod.ext (heA g _) (heB g _)
  let e : V ≃* W18 :=
    { toFun := fun v => (Multiplicative.ofAdd (E' (Additive.ofMul v)).1,
        Multiplicative.ofAdd (E' (Additive.ofMul v)).2)
      invFun := fun w => Additive.toMul (E'.symm (Multiplicative.toAdd w.1,
        Multiplicative.toAdd w.2))
      left_inv := fun v => by simp
      right_inv := fun w => by simp
      map_mul' := fun v w => by simp [ofMul_mul, map_add, ofAdd_add] }
  refine ⟨e, fun g => MulEquiv.ext fun w => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective w
  show e (φ g (e.symm (e v))) = rho18GL (Matrix.SpecialLinearGroup.toGL g) (e v)
  rw [MulEquiv.symm_apply_apply, rho18GL_apply]
  have h1 := hE' g (Additive.ofMul v)
  have h2 : linV (φ g) (Additive.ofMul v) = Additive.ofMul (φ g v) := rfl
  rw [h2] at h1
  have hc1 : (E' (Additive.ofMul (φ g v))).1 = Multiplicative.toAdd
      (rho9 (Matrix.SpecialLinearGroup.toGL g)
        (Multiplicative.ofAdd (E' (Additive.ofMul v)).1)) := by
    rw [h1]
    show (autMat (slRep rho9 g)).mulVec _ = _
    rw [autMat_mulVec]
    rfl
  have hc2 : (E' (Additive.ofMul (φ g v))).2 = Multiplicative.toAdd
      (rho9 (grGL (Matrix.SpecialLinearGroup.toGL g))
        (Multiplicative.ofAdd (E' (Additive.ofMul v)).2)) := by
    rw [h1]
    show (autMat (slRep rho9 (gamSL g))).mulVec _ = _
    rw [autMat_mulVec, slRep, MonoidHom.comp_apply, toGL_gamSL]
  refine Prod.ext ?_ ?_
  · show Multiplicative.ofAdd (E' (Additive.ofMul (φ g v))).1 = _
    rw [hc1, ofAdd_toAdd]
    rfl
  · show Multiplicative.ofAdd (E' (Additive.ofMul (φ g v))).2 = _
    rw [hc2, ofAdd_toAdd]
    rfl

end Lin

section Clifford

theorem exists_fixed_ne_zero {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    [Nontrivial E] {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (ρ : P →* Module.End (ZMod 2) E) : ∃ w : E, w ≠ 0 ∧ ∀ p, ρ p w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : P →* Equiv.Perm E :=
    { toFun := fun p =>
        { toFun := ρ p
          invFun := ρ p⁻¹
          left_inv := fun x => by
            show ρ p⁻¹ (ρ p x) = x
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
          right_inv := fun x => by
            show ρ p (ρ p⁻¹ x) = x
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
      map_one' := Equiv.ext fun x => by
        show ρ 1 x = x
        rw [map_one, Module.End.one_apply]
      map_mul' := fun p q => Equiv.ext fun x => by
        show ρ (p * q) x = ρ p (ρ q x)
        rw [map_mul, Module.End.mul_apply] }
  let _ : MulAction P E := MulAction.compHom E φ
  obtain ⟨v, hv0⟩ := exists_ne (0 : E)
  have h2 : 2 ∣ Nat.card E := by
    have hord : addOrderOf v = 2 := by
      refine addOrderOf_eq_prime ?_ hv0
      rw [two_nsmul, ← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    have := addOrderOf_dvd_natCard v
    rwa [hord] at this
  have hfix0 : (0 : E) ∈ MulAction.fixedPoints P E := fun p => map_zero (ρ p)
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point E h2 hfix0
  exact ⟨b, fun h => hb0 h.symm, fun p => hb p⟩

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

omit [Module (ZMod 2) (Additive V)] in
theorem exists_comm {X L : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    {φ : SL(3, F4) →* MulAut V} (hφ : φ.range = L) {x : MulAut V} (hx : x ∈ X) (g : SL(3, F4)) :
    ∃ g', φ g * x = x * φ g' := by
  have h1 : φ g ∈ L := hφ ▸ ⟨g, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem hx)) (φ g)).mp h1
  rw [← hφ, inv_inv] at h2
  obtain ⟨g', hg'⟩ := h2
  refine ⟨g', ?_⟩
  rw [hg']
  group

theorem isInvSub_map {X L : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V))) {φ : SL(3, F4) →* MulAut V}
    (hφ : φ.range = L) {x : MulAut V} (hx : x ∈ X) {W : Submodule (ZMod 2) (Additive V)}
    (hW : IsInvSub (linV.comp φ) W) : IsInvSub (linV.comp φ) (W.map (linV x)) := by
  rintro g _ ⟨w, hw, rfl⟩
  obtain ⟨g', hg'⟩ := exists_comm hXN hφ hx g
  refine ⟨(linV.comp φ) g' w, hW g' w hw, ?_⟩
  simp only [MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, ← hg', map_mul, Module.End.mul_apply]

theorem irr_map {X L : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V))) {φ : SL(3, F4) →* MulAut V}
    (hφ : φ.range = L) {x : MulAut V} (hx : x ∈ X) {W : Submodule (ZMod 2) (Additive V)}
    (hW : ∀ M, IsInvSub (linV.comp φ) M → M ≤ W → M = ⊥ ∨ M = W) :
    ∀ M, IsInvSub (linV.comp φ) M → M ≤ W.map (linV x) → M = ⊥ ∨ M = W.map (linV x) := by
  intro M hM hle
  have hback : (M.map (linV x⁻¹)).map (linV x) = M := by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_eq_id, Submodule.map_id]
  have hle' : M.map (linV x⁻¹) ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hle hv
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact hw
  rcases hW _ (isInvSub_map hXN hφ (X.inv_mem hx) hM) hle' with h | h
  · left
    rw [← hback, h, Submodule.map_bot]
  · right
    rw [← hback, h]

omit [Module (ZMod 2) (Additive V)] in
theorem exists_comm' {X L : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V))) {φ : SL(3, F4) →* MulAut V}
    (hφ : φ.range = L) {x : MulAut V} (hx : x ∈ X) (g : SL(3, F4)) :
    ∃ g', x * φ g = φ g' * x := by
  have h1 : φ g ∈ L := hφ ▸ ⟨g, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp (hXN hx) (φ g)).mp h1
  rw [← hφ] at h2
  obtain ⟨g', hg'⟩ := h2
  refine ⟨g', ?_⟩
  rw [hg']
  group

omit [Module (ZMod 2) (Additive V)] in
theorem map_eq_range {L : Subgroup (MulAut V)} {φ : SL(3, F4) →* MulAut V} (hφ : φ.range = L)
    {W : Type} [Group W] {e : V ≃* W} {σ : SL(3, F4) →* MulAut W}
    (he : ∀ g, MulAut.congr e (φ g) = σ g) : L.map (MulAut.congr e).toMonoidHom = σ.range := by
  rw [← hφ, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext he

end Clifford

theorem sup_sylow_eq_top {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (h2 : ∀ x : G, ∃ m : ℕ, x ^ 2 ^ m ∈ L) (S : Sylow 2 G) : L ⊔ (S : Subgroup G) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : IsPGroup 2 (G ⧸ L) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm⟩ := h2 x
    exact ⟨m, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hm⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hq2
  have hL : L.index = 2 ^ k := hk
  rw [← Subgroup.index_eq_one]
  have h1 : (L ⊔ (S : Subgroup G)).index ∣ 2 ^ k :=
    hL ▸ Subgroup.index_dvd_of_le (le_sup_left : L ≤ L ⊔ S)
  have h2' : ¬ 2 ∣ (L ⊔ (S : Subgroup G)).index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_right))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · simpa using hj
  · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) h2'

theorem exists_irr_sub {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] [Nontrivial E]
    {G : Type} [Group G] (ρ : G →* Module.End (ZMod 2) E) :
    ∃ W : Submodule (ZMod 2) E, IsInvSub ρ W ∧ W ≠ ⊥ ∧
      ∀ M, IsInvSub ρ M → M ≤ W → M = ⊥ ∨ M = W := by
  classical
  have : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun S : Submodule (ZMod 2) E => (S : Set E)) SetLike.coe_injective
  let P : Set (Submodule (ZMod 2) E) := {N | IsInvSub ρ N ∧ N ≠ ⊥}
  have hP : (Set.toFinite P).toFinset.Nonempty :=
    ⟨⊤, (Set.toFinite P).mem_toFinset.mpr ⟨fun _ _ _ => Submodule.mem_top, top_ne_bot⟩⟩
  obtain ⟨W, hWP, hWmin⟩ := (Set.toFinite P).toFinset.exists_min_image (fun N => Nat.card N) hP
  obtain ⟨hWi, hW0⟩ := (Set.toFinite P).mem_toFinset.mp hWP
  refine ⟨W, hWi, hW0, fun M hM hle => ?_⟩
  by_cases hM0 : M = ⊥
  · exact Or.inl hM0
  · right
    have hcard := hWmin M ((Set.toFinite P).mem_toFinset.mpr ⟨hM, hM0⟩)
    have h1 : (M : Set E) = W := Set.eq_of_subset_of_ncard_le hle (by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcard) (Set.toFinite _)
    exact SetLike.coe_injective h1

section MainArg

variable {V : Type} [CommGroup V] [Finite V]
  [Module (ZMod 2) (Additive V)]

theorem model_of_irr {φ : SL(3, F4) →* MulAut V} (hZ : φ zSL = 1)
    {W : Submodule (ZMod 2) (Additive V)} (hW : IsInvSub (linV.comp φ) W)
    (hirr : ∀ M, IsInvSub (linV.comp φ) M → M ≤ W → M = ⊥ ∨ M = W)
    (hnt : ∃ g, ∃ w ∈ W, linV (φ g) w ≠ w) :
    IsModelOf (linV.comp φ) R9 W ∨ IsModelOf (linV.comp φ) R9g W ∨
      IsModelOf (linV.comp φ) R16 W ∨ IsModelOf (linV.comp φ) R64 W := by
  let σ : Representation (ZMod 2) SL(3, F4) W :=
    { toFun := fun g => (linV (φ g)).restrict (hW g)
      map_one' := LinearMap.ext fun w => Subtype.ext (by
        show linV (φ 1) (w : Additive V) = w
        rw [map_one, map_one, Module.End.one_apply])
      map_mul' := fun g h => LinearMap.ext fun w => Subtype.ext (by
        show linV (φ (g * h)) (w : Additive V) = linV (φ g) (linV (φ h) w)
        rw [map_mul, map_mul, Module.End.mul_apply]) }
  have hσ : ∀ g (w : W), σ g w = ⟨linV (φ g) w, hW g w w.2⟩ := fun _ _ => rfl
  have hirrσ : ∀ N : Submodule (ZMod 2) W, (∀ g, ∀ v ∈ N, σ g v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    rcases hirr (N.map W.subtype) (by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨σ g v, hN g v hv, rfl⟩) (by
      rintro _ ⟨v, -, rfl⟩
      exact v.2) with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have : (v : Additive V) ∈ N.map W.subtype := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact (Submodule.mem_bot _).mpr (Subtype.ext this)
    · right
      rw [eq_top_iff]
      intro v _
      have : (v : Additive V) ∈ N.map W.subtype := by
        rw [h]
        exact v.2
      obtain ⟨u, hu, hu'⟩ := this
      rwa [show u = v from Subtype.ext hu'] at hu
  have hZσ : σ zSL = 1 := LinearMap.ext fun w => Subtype.ext (by
    show linV (φ zSL) (w : Additive V) = w
    rw [hZ, map_one, Module.End.one_apply])
  have hntσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨g, w, hw, hne⟩ := hnt
    refine ⟨g, fun h => hne ?_⟩
    have := congrArg Subtype.val (LinearMap.congr_fun h ⟨w, hw⟩)
    exact this
  have : Finite W := Subtype.finite
  rcases exists_model σ hirrσ hZσ hntσ with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨hW, e, fun g w => (congrArg e (hσ g w).symm).trans (he g w)⟩
  · exact Or.inr (Or.inl ⟨hW, e, fun g w => (congrArg e (hσ g w).symm).trans (he g w)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hW, e, fun g w => (congrArg e (hσ g w).symm).trans (he g w)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hW, e, fun g w => (congrArg e (hσ g w).symm).trans (he g w)⟩))

end MainArg

theorem factL34Modules_holds : FactL34Modules := by
  intro V _ _ hV2 X hirr L hLX hXN hPSL hC hX2
  classical
  let _ : Module (ZMod 2) (Additive V) := modV hV2
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) fun f g h => MulEquiv.ext (congrFun h)
  obtain ⟨ψ, hψs, hψZ, hψu⟩ := exists_hom_of_isPSL hPSL
  set φ : SL(3, F4) →* MulAut V := L.subtype.comp ψ with hφdef
  have hφ : φ.range = L := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψs, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hφZ : φ zSL = 1 := by
    show ((ψ zSL : L) : MulAut V) = 1
    rw [hψZ]
    rfl
  have hφu : φ (uSL (f4c 1) 0 0) ≠ 1 := fun h => hψu (Subtype.ext h)
  set ρ : SL(3, F4) →* Module.End (ZMod 2) (Additive V) := linV.comp φ with hρdef
  have : Nontrivial (Additive V) := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hirr.1
    refine ⟨⟨Additive.ofMul v, 0, fun h => hv ?_⟩⟩
    rw [Subgroup.mem_bot]
    exact Additive.ofMul.injective h
  have hXirr : ∀ N : Submodule (ZMod 2) (Additive V),
      (∀ x ∈ X, ∀ m ∈ N, linV x m ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    eq_bot_or_top_of_irr hirr hN
  have hlinV : ∀ (z : MulAut V) m, linV z⁻¹ (linV z m) = m := fun z m => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨W₀, hW₀i, hW₀0, hW₀irr⟩ := exists_irr_sub ρ
  let Wf : ↥X → Submodule (ZMod 2) (Additive V) := fun x => W₀.map (linV (x : MulAut V))
  have hWfi : ∀ x, IsInvSub ρ (Wf x) := fun x => isInvSub_map hXN hφ x.2 hW₀i
  have hWfirr : ∀ x, ∀ M, IsInvSub ρ M → M ≤ Wf x → M = ⊥ ∨ M = Wf x := fun x =>
    irr_map hXN hφ x.2 hW₀irr
  have hWfcard : ∀ x, Nat.card (Wf x) = Nat.card W₀ := fun x =>
    (Nat.card_congr (Submodule.equivMapOfInjective _ (fun a b h => by
      rw [← hlinV x a, ← hlinV x b, h]) W₀).toEquiv).symm
  have hWf0 : ∀ x, Wf x ≠ ⊥ := fun x h => hW₀0 (by
    rw [eq_bot_iff]
    intro w hw
    have h1 : linV (x : MulAut V) w ∈ Wf x := ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← hlinV x w, h1, map_zero])
  have htop : (⨆ x, Wf x) = ⊤ := by
    have hinv : ∀ z ∈ X, ∀ m ∈ ⨆ x, Wf x, linV z m ∈ ⨆ x, Wf x := by
      intro z hz m hm
      have hle : (⨆ x, Wf x).map (linV z) ≤ ⨆ x, Wf x := by
        rw [Submodule.map_iSup]
        refine iSup_le fun x => ?_
        refine le_trans (le_of_eq ?_) (le_iSup Wf ⟨z * x, X.mul_mem hz x.2⟩)
        show (W₀.map (linV (x : MulAut V))).map (linV z) = W₀.map (linV (z * (x : MulAut V)))
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]
      exact hle ⟨m, hm, rfl⟩
    rcases hXirr _ hinv with h | h
    · exact absurd (eq_bot_iff.mpr ((le_iSup Wf 1).trans h.le)) (hWf0 1)
    · exact h
  have hntx : ∀ x, ∃ g, ∃ w ∈ Wf x, linV (φ g) w ≠ w := by
    intro x
    by_contra h
    push Not at h
    let F : Submodule (ZMod 2) (Additive V) :=
      { carrier := {v | ∀ g, linV (φ g) v = v}
        add_mem' := fun {a b} ha hb g => by rw [map_add, ha g, hb g]
        zero_mem' := fun g => map_zero _
        smul_mem' := fun c v hv g => by rw [map_smul, hv g] }
    have hFinv : ∀ z ∈ X, ∀ v ∈ F, linV z v ∈ F := fun z hz v hv g => by
      obtain ⟨g', hg'⟩ := exists_comm hXN hφ hz g
      show linV (φ g) (linV z v) = linV z v
      rw [← Module.End.mul_apply, ← map_mul, hg', map_mul, Module.End.mul_apply, hv g']
    have hF : F = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun y => ?_
      rintro _ ⟨w, hw, rfl⟩
      have e : linV (y : MulAut V) w = linV ((y : MulAut V) * (x : MulAut V)⁻¹)
          (linV (x : MulAut V) w) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      rw [e]
      exact hFinv _ (X.mul_mem y.2 (X.inv_mem x.2)) _ (fun g => h g _ ⟨w, hw, rfl⟩)
    apply hφu
    apply linV_injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ F := by
      rw [hF]
      exact Submodule.mem_top
    rw [map_one, Module.End.one_apply]
    exact hv _
  have hmodel : ∀ x, IsModelOf ρ R9 (Wf x) ∨ IsModelOf ρ R9g (Wf x) ∨
      IsModelOf ρ R16 (Wf x) ∨ IsModelOf ρ R64 (Wf x) := fun x =>
    model_of_irr hφZ (hWfi x) (hWfirr x) (hntx x)
  have hLn : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN
  let φX : SL(3, F4) →* ↥X := (Subgroup.inclusion hLX).comp ψ
  obtain ⟨S, hQS⟩ := (isPGroup_U.map φX).exists_le_sylow
  obtain ⟨c, hc0, hcS⟩ := exists_fixed_ne_zero S.isPGroup'
    (linV.comp (X.subtype.comp (S : Subgroup ↥X).subtype))
  have hcs : ∀ s ∈ (S : Subgroup ↥X), linV ((s : ↥X) : MulAut V) c = c := fun s hs =>
    hcS ⟨s, hs⟩
  have hcU : ∀ u ∈ (upperUni F4 : Set SL(3, F4)), ρ u c = c := fun u hu =>
    hcs _ (hQS ⟨u, hu, rfl⟩)
  have hT : L.subgroupOf X ⊔ (S : Subgroup ↥X) = ⊤ := sup_sylow_eq_top (fun x => by
    obtain ⟨m, hm⟩ := hX2 x x.2
    exact ⟨m, Subgroup.mem_subgroupOf.mpr (by simpa using hm)⟩) S
  have hgen : ∀ N, IsInvSub ρ N → c ∈ N → N = ⊤ := by
    intro N hN hcN
    set N₀ := Submodule.span (ZMod 2) (Set.range fun g => ρ g c) with hN₀
    have hstep : ∀ z : MulAut V, (∀ g, ∃ g', linV z (ρ g c) = ρ g' c) →
        ∀ m ∈ N₀, linV z m ∈ N₀ := by
      intro z hz m hm
      have hle : N₀ ≤ N₀.comap (linV z) := Submodule.span_le.mpr (by
        rintro _ ⟨g, rfl⟩
        obtain ⟨g', hg'⟩ := hz g
        show linV z (ρ g c) ∈ N₀
        rw [hg']
        exact Submodule.subset_span ⟨g', rfl⟩)
      exact hle hm
    let Stab : Subgroup ↥X :=
      { carrier := {x | (∀ g, ∃ g', linV (x : MulAut V) (ρ g c) = ρ g' c) ∧
          ∀ g, ∃ g', linV (x : MulAut V)⁻¹ (ρ g c) = ρ g' c}
        mul_mem' := fun {x y} hx hy => ⟨fun g => by
            obtain ⟨g₁, h₁⟩ := hy.1 g
            obtain ⟨g₂, h₂⟩ := hx.1 g₁
            exact ⟨g₂, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, h₁, h₂]⟩,
          fun g => by
            obtain ⟨g₁, h₁⟩ := hx.2 g
            obtain ⟨g₂, h₂⟩ := hy.2 g₁
            exact ⟨g₂, by
              rw [Subgroup.coe_mul, _root_.mul_inv_rev, map_mul, Module.End.mul_apply, h₁, h₂]⟩⟩
        one_mem' := ⟨fun g => ⟨g, by rw [Subgroup.coe_one, map_one, Module.End.one_apply]⟩,
          fun g => ⟨g, by rw [Subgroup.coe_one, inv_one, map_one, Module.End.one_apply]⟩⟩
        inv_mem' := fun {x} hx => ⟨fun g => by
            obtain ⟨g', h'⟩ := hx.2 g
            exact ⟨g', by rw [Subgroup.coe_inv]; exact h'⟩,
          fun g => by
            obtain ⟨g', h'⟩ := hx.1 g
            exact ⟨g', by rw [Subgroup.coe_inv, inv_inv]; exact h'⟩⟩ }
    have hLStab : L.subgroupOf X ≤ Stab := by
      intro x hx
      obtain ⟨g₀, hg₀⟩ : (x : MulAut V) ∈ φ.range := hφ ▸ Subgroup.mem_subgroupOf.mp hx
      refine ⟨fun g => ⟨g₀ * g, ?_⟩, fun g => ⟨g₀⁻¹ * g, ?_⟩⟩
      · rw [← hg₀, map_mul ρ, Module.End.mul_apply]
        rfl
      · rw [← hg₀, ← map_inv φ g₀, map_mul ρ, Module.End.mul_apply]
        rfl
    have hSStab : (S : Subgroup ↥X) ≤ Stab := by
      intro s hs
      have key : ∀ t ∈ (S : Subgroup ↥X), ∀ g, ∃ g', linV (t : MulAut V) (ρ g c) = ρ g' c := by
        intro t ht g
        obtain ⟨g', hg'⟩ := exists_comm' hXN hφ t.2 g
        refine ⟨g', ?_⟩
        show linV (t : MulAut V) (linV (φ g) c) = linV (φ g') c
        rw [← Module.End.mul_apply, ← map_mul, hg', map_mul, Module.End.mul_apply, hcs t ht]
      exact ⟨key s hs, fun g => by
        obtain ⟨g', h'⟩ := key s⁻¹ (S.inv_mem hs) g
        exact ⟨g', by rw [← Subgroup.coe_inv]; exact h'⟩⟩
    have hall : ∀ x : ↥X, x ∈ Stab := fun x => by
      have : x ∈ L.subgroupOf X ⊔ (S : Subgroup ↥X) := hT ▸ Subgroup.mem_top x
      exact sup_le hLStab hSStab this
    have hN₀ : N₀ = ⊤ := by
      rcases hXirr N₀ (fun z hz m hm => hstep z (hall ⟨z, hz⟩).1 m hm) with h | h
      · exfalso
        have : c ∈ N₀ := Submodule.subset_span ⟨1, by
          show ρ 1 c = c
          rw [map_one, Module.End.one_apply]⟩
        rw [h, Submodule.mem_bot] at this
        exact hc0 this
      · exact h
    rw [eq_top_iff, ← hN₀]
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hN g c hcN)
  have h𝒲 : ∀ W ∈ Set.range Wf, IsInvSub ρ W ∧ ∀ M, IsInvSub ρ M → M ≤ W → M = ⊥ ∨ M = W := by
    rintro _ ⟨x, rfl⟩
    exact ⟨hWfi x, hWfirr x⟩
  have hfalse : ∀ {m : ℕ} (R : SL(3, F4) →* Matrix (Fin m) (Fin m) (ZMod 2)),
      (∀ v v' : Fin m → ZMod 2, v ≠ 0 → v' ≠ 0 →
        (∀ u ∈ (upperUni F4 : Set SL(3, F4)), (R u).mulVec v = v) →
        (∀ u ∈ (upperUni F4 : Set SL(3, F4)), (R u).mulVec v' = v') →
        ∃ S : Matrix (Fin m) (Fin m) (ZMod 2), (∀ g, S * R g = R g * S) ∧ S.mulVec v = v') →
      ∀ x y, Wf x ≠ Wf y → IsModelOf ρ R (Wf x) → IsModelOf ρ R (Wf y) → False :=
    fun R hR x y hne hx hy => false_of_isModelOf R (U := (upperUni F4 : Set SL(3, F4))) hR hcU
      hgen (Set.range Wf) h𝒲 htop ⟨x, rfl⟩ ⟨y, rfl⟩ hne (hWf0 y) hx hy
  have hR9 := fun v v' (hv : v ≠ 0) (hv' : v' ≠ 0) hfv hfv' => exists_scal9 hv hv' hfv hfv'
  have hR9g := fun v v' (hv : v ≠ 0) (hv' : v' ≠ 0) hfv hfv' => exists_scal9g hv hv' hfv hfv'
  have hR16 := fun v v' (hv : v ≠ 0) (hv' : v' ≠ 0) hfv hfv' => exists_scal16 hv hv' hfv hfv'
  have hR64 := fun v v' (hv : v ≠ 0) (hv' : v' ≠ 0) hfv hfv' => exists_scal64 hv hv' hfv hfv'
  have hcard : ∀ x, Nat.card (Wf x) = Nat.card (Wf 1) := fun x => by rw [hWfcard, hWfcard]
  have htop1 : (∀ x, Wf x = Wf 1) → Wf 1 = ⊤ := fun hall => by
    rw [← htop]
    exact le_antisymm (le_iSup Wf 1) (iSup_le fun x => (hall x).le)
  have hpair : ∀ x, Wf x ≠ Wf 1 → Wf 1 ⊓ Wf x = ⊥ := fun x hne => by
    rcases hWfirr 1 _ (fun g v hv => Submodule.mem_inf.mpr ⟨hWfi 1 g v (Submodule.mem_inf.mp hv).1,
        hWfi x g v (Submodule.mem_inf.mp hv).2⟩) inf_le_left with h | h
    · exact h
    · exfalso
      rcases hWfirr x _ (hWfi 1) (h ▸ inf_le_right) with h' | h'
      · exact hWf0 1 h'
      · exact hne h'.symm
  have hcompl : ∀ x, Wf x ≠ Wf 1 → (∀ y, Wf y = Wf 1 ∨ Wf y = Wf x) →
      IsCompl (Wf 1) (Wf x) := fun x hne hy => by
    refine ⟨disjoint_iff.mpr (hpair x hne), codisjoint_iff.mpr ?_⟩
    rw [← htop]
    refine le_antisymm (sup_le (le_iSup Wf 1) (le_iSup Wf x)) (iSup_le fun y => ?_)
    rcases hy y with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  have h9ne16 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R9 W → Nat.card W ≠ 2 ^ 16 :=
    fun h => by rw [card_of_isModelOf h]; norm_num
  have h9gne16 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R9g W →
      Nat.card W ≠ 2 ^ 16 := fun h => by rw [card_of_isModelOf h]; norm_num
  have h9ne64 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R9 W → Nat.card W ≠ 2 ^ 64 :=
    fun h => by rw [card_of_isModelOf h]; norm_num
  have h9gne64 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R9g W →
      Nat.card W ≠ 2 ^ 64 := fun h => by rw [card_of_isModelOf h]; norm_num
  have h16ne64 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R16 W →
      Nat.card W ≠ 2 ^ 64 := fun h => by rw [card_of_isModelOf h]; norm_num
  have h16ne9 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R16 W →
      Nat.card W ≠ 2 ^ 9 := fun h => by rw [card_of_isModelOf h]; norm_num
  have h64ne9 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R64 W →
      Nat.card W ≠ 2 ^ 9 := fun h => by rw [card_of_isModelOf h]; norm_num
  have h64ne16 : ∀ {W : Submodule (ZMod 2) (Additive V)}, IsModelOf ρ R64 W →
      Nat.card W ≠ 2 ^ 16 := fun h => by rw [card_of_isModelOf h]; norm_num
  have hrange9g : ((slRep rho9).comp gamSL).range = (slRep rho9).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr gamSL_surjective,
      ← MonoidHom.range_eq_map]
  rcases hmodel 1 with h9 | h9g | h16 | h64
  ·
    by_cases hall : ∀ x, Wf x = Wf 1
    · have h9' : IsModelOf ρ (autMat.comp (slRep rho9)) ⊤ := by
        rw [← htop1 hall]
        exact h9
      obtain ⟨e, he⟩ := exists_mulEquiv_of_isModelOf (slRep rho9) h9'
      exact Or.inl ⟨e, map_eq_range hφ he⟩
    · push Not at hall
      obtain ⟨x₁, hx₁⟩ := hall
      have hm₁ : IsModelOf ρ R9g (Wf x₁) := by
        rcases hmodel x₁ with h | h | h | h
        · exact (hfalse R9 hR9 x₁ 1 hx₁ h h9).elim
        · exact h
        · exact absurd ((hcard x₁).trans (card_of_isModelOf h9)) (h16ne9 h)
        · exact absurd ((hcard x₁).trans (card_of_isModelOf h9)) (h64ne9 h)
      have hy : ∀ y, Wf y = Wf 1 ∨ Wf y = Wf x₁ := by
        intro y
        by_contra hne
        push Not at hne
        rcases hmodel y with h | h | h | h
        · exact hfalse R9 hR9 y 1 hne.1 h h9
        · exact hfalse R9g hR9g y x₁ hne.2 h hm₁
        · exact h16ne9 h ((hcard y).trans (card_of_isModelOf h9))
        · exact h64ne9 h ((hcard y).trans (card_of_isModelOf h9))
      obtain ⟨e, he⟩ := exists_mulEquiv18 (hcompl x₁ hx₁ hy) h9 hm₁
      exact Or.inr (Or.inl ⟨e, map_eq_range hφ he⟩)
  ·
    by_cases hall : ∀ x, Wf x = Wf 1
    · have h9' : IsModelOf ρ (autMat.comp ((slRep rho9).comp gamSL)) ⊤ := by
        rw [← htop1 hall]
        exact h9g
      obtain ⟨e, he⟩ := exists_mulEquiv_of_isModelOf ((slRep rho9).comp gamSL) h9'
      exact Or.inl ⟨e, (map_eq_range hφ he).trans hrange9g⟩
    · push Not at hall
      obtain ⟨x₁, hx₁⟩ := hall
      have hm₁ : IsModelOf ρ R9 (Wf x₁) := by
        rcases hmodel x₁ with h | h | h | h
        · exact h
        · exact (hfalse R9g hR9g x₁ 1 hx₁ h h9g).elim
        · exact absurd ((hcard x₁).trans (card_of_isModelOf h9g)) (h16ne9 h)
        · exact absurd ((hcard x₁).trans (card_of_isModelOf h9g)) (h64ne9 h)
      have hy : ∀ y, Wf y = Wf 1 ∨ Wf y = Wf x₁ := by
        intro y
        by_contra hne
        push Not at hne
        rcases hmodel y with h | h | h | h
        · exact hfalse R9 hR9 y x₁ hne.2 h hm₁
        · exact hfalse R9g hR9g y 1 hne.1 h h9g
        · exact h16ne9 h ((hcard y).trans (card_of_isModelOf h9g))
        · exact h64ne9 h ((hcard y).trans (card_of_isModelOf h9g))
      obtain ⟨e, he⟩ := exists_mulEquiv18 (hcompl x₁ hx₁ hy).symm hm₁ h9g
      exact Or.inr (Or.inl ⟨e, map_eq_range hφ he⟩)
  ·
    have hall : ∀ x, Wf x = Wf 1 := by
      intro x
      by_contra hne
      rcases hmodel x with h | h | h | h
      · exact h9ne16 h ((hcard x).trans (card_of_isModelOf h16))
      · exact h9gne16 h ((hcard x).trans (card_of_isModelOf h16))
      · exact hfalse R16 hR16 x 1 hne h h16
      · exact h64ne16 h ((hcard x).trans (card_of_isModelOf h16))
    have h16' : IsModelOf ρ (autMat.comp (slRep rho16GL)) ⊤ := by
      rw [← htop1 hall]
      exact h16
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isModelOf (slRep rho16GL) h16'
    exact Or.inr (Or.inr (Or.inl ⟨e, map_eq_range hφ he⟩))
  ·
    have hall : ∀ x, Wf x = Wf 1 := by
      intro x
      by_contra hne
      rcases hmodel x with h | h | h | h
      · exact h9ne64 h ((hcard x).trans (card_of_isModelOf h64))
      · exact h9gne64 h ((hcard x).trans (card_of_isModelOf h64))
      · exact h16ne64 h ((hcard x).trans (card_of_isModelOf h64))
      · exact hfalse R64 hR64 x 1 hne h h64
    have h64' : IsModelOf ρ (autMat.comp (slRep rho64GL)) ⊤ := by
      rw [← htop1 hall]
      exact h64
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isModelOf (slRep rho64GL) h64'
    exact Or.inr (Or.inr (Or.inr ⟨e, map_eq_range hφ he⟩))

end CFSG.Quasithin.H13.Ch9.L34B
