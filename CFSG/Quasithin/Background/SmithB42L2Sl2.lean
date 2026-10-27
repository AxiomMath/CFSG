module

public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport

public section

namespace CFSG.Quasithin

namespace B42L2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Lift CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization

section Transport

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem toAdd_binPsi (φ : MulAut V) (v : V) :
    binPsi θ φ (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ (φ v)) := by
  rw [binPsi_apply]
  simp

theorem irr_map {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (U : Submodule (ZMod 2) W) (hU : ∀ x ∈ L.map (binPsi θ).toMonoidHom, ∀ u ∈ U, x u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  let J : Subgroup V :=
    { carrier := {v | Multiplicative.toAdd (θ v) ∈ U}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul] at ha hb ⊢
        exact U.add_mem ha hb
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_inv, toAdd_inv] at ha ⊢
        exact U.neg_mem ha }
  have hJ : ∀ l ∈ L, ∀ v ∈ J, l v ∈ J := by
    intro l hl v hv
    show Multiplicative.toAdd (θ (l v)) ∈ U
    rw [← toAdd_binPsi]
    exact hU _ ⟨l, hl, rfl⟩ _ hv
  rcases hirr J hJ with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have hv : θ.symm (Multiplicative.ofAdd u) ∈ J := by
      show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd u))) ∈ U
      simpa using hu
    rw [h, Subgroup.mem_bot] at hv
    have := congrArg θ hv
    simp only [MulEquiv.apply_symm_apply, map_one] at this
    rw [Submodule.mem_bot]
    exact Multiplicative.ofAdd.injective this
  · right
    rw [eq_top_iff]
    intro u _
    have hv : θ.symm (Multiplicative.ofAdd u) ∈ J := by rw [h]; trivial
    have h2 : Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd u))) ∈ U := hv
    simpa using h2

theorem quad_map {Q : Subgroup (MulAut V)} (hQ : IsQuadratic Q) :
    ∀ a ∈ Q.map (binPsi θ).toMonoidHom, ∀ b ∈ Q.map (binPsi θ).toMonoidHom, ∀ w : W,
      b (a w - w) = a w - w := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  set v := θ.symm (Multiplicative.ofAdd w) with hv
  have hw : w = Multiplicative.toAdd (θ v) := by simp [hv]
  have hu : a v * v⁻¹ ∈ fixV Q :=
    hQ (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
  have h1 : (binPsi θ).toMonoidHom a w - w = Multiplicative.toAdd (θ (a v * v⁻¹)) := by
    show binPsi θ a w - w = _
    rw [hw, toAdd_binPsi, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  rw [h1]
  show binPsi θ b _ = _
  rw [toAdd_binPsi, hu b hb]

end Transport

section Alt

variable {V : Type} [CommGroup V] [Finite V]

theorem sl2_raw
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    (θL : ↥L ≃* SL(2, F)) {Q : Subgroup (MulAut V)} (hQ : IsFFStarOffender G Q)
    (hQq : IsQuadratic Q) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (θ : V ≃* Multiplicative W) :
    Nat.card Q * Nat.card (fixV Q) = Nat.card V ∧
      ∃ θ₀ : ↥(L.map (binPsi θ).toMonoidHom) ≃* SL(2, F),
        (∀ l : ↥L, θ₀ (L.equivMapOfInjective _ (binPsi θ).injective l) = θL l) ∧
        (NaturalAlt (L.map (binPsi θ).toMonoidHom) (Q.map (binPsi θ).toMonoidHom) θ₀ ∨
          DeletedAlt n (L.map (binPsi θ).toMonoidHom) (Q.map (binPsi θ).toMonoidHom) θ₀) := by
  classical
  obtain ⟨-, -, -, hq⟩ := FFC.b4hyp_data hHyp
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  set ψ := binPsi θ with hψ
  set L₀ := L.map ψ.toMonoidHom with hL₀
  set A₀ := Q.map ψ.toMonoidHom with hA₀
  let eL : ↥L ≃* ↥L₀ := L.equivMapOfInjective ψ.toMonoidHom ψ.injective
  have hZ₀ : Subgroup.center ↥L₀ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : eL.symm x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply eL.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx (eL g)
    rw [hZ, Subgroup.mem_bot] at hx'
    have := congrArg eL hx'
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  let α₀ : (↥L₀ ⧸ Subgroup.center ↥L₀) ≃* SL(2, F) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ₀).trans QuotientGroup.quotientBot).trans
      (eL.symm.trans θL)
  have hα : ∀ x : ↥L₀, α₀ (QuotientGroup.mk x) = θL (eL.symm x) := fun x => rfl
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have : CFSG.IsElementaryAbelian 2 ↥A₀ := (isElemAbelian2_iff_map θ Q).1 hQ.2.2.1
  have hA1 : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff_of_injective Q ψ.injective]
    exact hQ.2.1
  have hAN : A₀ ≤ Subgroup.normalizer (L₀ : Set (W ≃ₗ[ZMod 2] W)) := by
    rw [hA₀, hL₀, ← Subgroup.map_equiv_normalizer_eq L ψ]
    exact Subgroup.map_mono (hQ.1.trans (le_normalizer_of_b4Hyp hHyp))
  have hoff : Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) A₀ := by
    rw [hA₀, weight_map θ Q, ← natCard_eq θ]
    exact card_le_of_offender hQ
  obtain ⟨-, θ₀, hθ₀, halt, hw⟩ := central_quotient_SL2_alternatives_GL hn hF L₀ A₀
    ⟨hntW, fun U hU => irr_map θ hirrV U hU⟩ (isPerfect_of_equiv eL hq.1) α₀ hA1 hAN
    (quad_map θ hQq) hoff
  refine ⟨?_, θ₀, fun l => ?_, halt⟩
  · rw [hA₀, weight_map θ Q, ← natCard_eq θ] at hw
    exact hw
  · rw [hθ₀, hα]
    exact congrArg θL (eL.symm_apply_apply l)

omit [Finite V] in
theorem nat_of_naturalAlt {L Q : Subgroup (MulAut V)} {F : Type} [Field F]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (θ : V ≃* Multiplicative W)
    (θL : ↥L ≃* SL(2, F)) (θ₀ : ↥(L.map (binPsi θ).toMonoidHom) ≃* SL(2, F))
    (hθ : ∀ l : ↥L, θ₀ (L.equivMapOfInjective _ (binPsi θ).injective l) = θL l)
    (h : NaturalAlt (L.map (binPsi θ).toMonoidHom) (Q.map (binPsi θ).toMonoidHom) θ₀) :
    Q ≤ L ∧ ∃ e : V ≃* Multiplicative (Fin 2 → F), ∀ (l : ↥L) (v : V),
      e ((l : MulAut V) v) = Multiplicative.ofAdd
        ((θL l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (e v))) := by
  obtain ⟨hAL, β, hβ, -⟩ := h
  refine ⟨(Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 hAL,
    θ.trans (AddEquiv.toMultiplicative β), fun l v => ?_⟩
  have h1 := hβ (L.equivMapOfInjective _ (binPsi θ).injective l) (Multiplicative.toAdd (θ v))
  have h2 : ((L.equivMapOfInjective _ (binPsi θ).injective l :
      ↥(L.map (binPsi θ).toMonoidHom)) : W ≃ₗ[ZMod 2] W) = binPsi θ l := rfl
  rw [hθ, h2] at h1
  show Multiplicative.ofAdd (β (Multiplicative.toAdd (θ ((l : MulAut V) v)))) =
    Multiplicative.ofAdd ((θL l : Matrix (Fin 2) (Fin 2) F).mulVec
      (β (Multiplicative.toAdd (θ v))))
  rw [← h1, ← toAdd_binPsi]

@[expose] noncomputable def coreEquiv {Ω : Type} [Fintype Ω] {n : ℕ} (ι : Ω ≃ Fin n) :
    Multiplicative ↥(evenWeight Ω) ≃* ↥(G6.coreMod n) where
  toFun x := ⟨Multiplicative.ofAdd fun i =>
      ((Multiplicative.toAdd x : ↥(evenWeight Ω)) : Ω → ZMod 2) (ι.symm i), by
    rw [G6.mem_coreMod, toAdd_ofAdd]
    have h := (Multiplicative.toAdd x).2
    change ∑ p, ((Multiplicative.toAdd x : ↥(evenWeight Ω)) : Ω → ZMod 2) p = 0 at h
    rw [← h]
    exact Equiv.sum_comp ι.symm _⟩
  invFun y := Multiplicative.ofAdd ⟨fun p => Multiplicative.toAdd (y : G6.PermMod n) (ι p), by
    change ∑ p, Multiplicative.toAdd (y : G6.PermMod n) (ι p) = 0
    rw [Equiv.sum_comp ι (fun i => Multiplicative.toAdd (y : G6.PermMod n) i)]
    exact y.2⟩
  left_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext p
    simp
  right_inv y := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    simp

omit [Finite V] in
theorem del_of_deletedAlt {L Q : Subgroup (MulAut V)} {F : Type} [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] {n : ℕ}
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (θ : V ≃* Multiplicative W)
    (θ₀ : ↥(L.map (binPsi θ).toMonoidHom) ≃* SL(2, F))
    (h : DeletedAlt n (L.map (binPsi θ).toMonoidHom) (Q.map (binPsi θ).toMonoidHom) θ₀) :
    n = 2 ∧ ¬ Q ≤ L ∧ ∃ (σ : ↥(L ⊔ Q) ≃* Equiv.Perm (Fin 5)) (e : V ≃* ↥(G6.coreMod 5)),
      (∀ (y : ↥(L ⊔ Q)) (v : V), e ((y : MulAut V) v) = G6.coreAct 5 (σ y) (e v)) ∧
      ∀ y : ↥(L ⊔ Q), (y : MulAut V) ∈ L ↔ σ y ∈ alternatingGroup (Fin 5) := by
  classical
  obtain ⟨hnAL, hn2, hΩ5, ψ', β, -, hψ2, hψ3, -⟩ := h
  refine ⟨hn2, fun hQL => hnAL (Subgroup.map_mono hQL), ?_⟩
  let ι : ℙ F (Fin 2 → F) ≃ Fin 5 := Fintype.equivFinOfCardEq hΩ5
  have hsup : (L ⊔ Q).map (binPsi θ).toMonoidHom =
      L.map (binPsi θ).toMonoidHom ⊔ Q.map (binPsi θ).toMonoidHom := Subgroup.map_sup L Q _
  let eLQ : ↥(L ⊔ Q) ≃* ↥(L.map (binPsi θ).toMonoidHom ⊔ Q.map (binPsi θ).toMonoidHom) :=
    ((L ⊔ Q).equivMapOfInjective _ (binPsi θ).injective).trans (MulEquiv.subgroupCongr hsup)
  have heLQ : ∀ y : ↥(L ⊔ Q), ((eLQ y : ↥(L.map (binPsi θ).toMonoidHom ⊔
      Q.map (binPsi θ).toMonoidHom)) : W ≃ₗ[ZMod 2] W) = binPsi θ y := fun y => rfl
  refine ⟨(eLQ.trans ψ').trans (Equiv.permCongrHom ι),
    θ.trans ((AddEquiv.toMultiplicative β.toAddEquiv).trans (coreEquiv ι)), fun y v => ?_,
    fun y => ?_⟩
  · apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have h1 := hψ2 (eLQ y) (Multiplicative.toAdd (θ v))
    rw [heLQ, toAdd_binPsi] at h1
    have h3 : Multiplicative.toAdd (((θ.trans ((AddEquiv.toMultiplicative β.toAddEquiv).trans
        (coreEquiv ι))) ((y : MulAut V) v) : ↥(G6.coreMod 5)) : G6.PermMod 5) i =
        (β (Multiplicative.toAdd (θ ((y : MulAut V) v))) : ℙ F (Fin 2 → F) → ZMod 2)
          (ι.symm i) := rfl
    rw [h3, h1, G6.coreAct_coe, G6.permAct_apply]
    set p := ψ' (eLQ y) with hp
    have hσ : ((eLQ.trans ψ').trans (Equiv.permCongrHom ι)) y = ι.permCongr p := rfl
    rw [hσ]
    have hj : ι.symm ((ι.permCongr p)⁻¹ i) = p.symm (ι.symm i) := by
      set j := (ι.permCongr p)⁻¹ i with hjdef
      have h5 : ι.permCongr p j = i := by
        rw [hjdef, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
      rw [Equiv.permCongr_apply] at h5
      rw [Equiv.eq_symm_apply, ← h5, Equiv.symm_apply_apply]
    show (β (Multiplicative.toAdd (θ v)) : ℙ F (Fin 2 → F) → ZMod 2) (p.symm (ι.symm i)) =
      (β (Multiplicative.toAdd (θ v)) : ℙ F (Fin 2 → F) → ZMod 2)
        (ι.symm ((ι.permCongr p)⁻¹ i))
    rw [hj]
  · rw [← Subgroup.mem_map_iff_mem (f := (binPsi θ).toMonoidHom) (binPsi θ).injective (K := L)
      (x := (y : MulAut V)), Equiv.Perm.mem_alternatingGroup]
    show binPsi θ y ∈ L.map (binPsi θ).toMonoidHom ↔ _
    rw [← heLQ, ← Subgroup.mem_subgroupOf,
      ← Subgroup.mem_map_iff_mem (f := ψ'.toMonoidHom) ψ'.injective
        (K := Subgroup.subgroupOf _ _) (x := eLQ y)]
    change ψ' (eLQ y) ∈ ((L.map (binPsi θ).toMonoidHom).subgroupOf _).map ψ'.toMonoidHom ↔ _
    rw [hψ3, Equiv.Perm.mem_alternatingGroup]
    change _ ↔ Equiv.Perm.sign (ι.permCongr (ψ' (eLQ y))) = 1
    rw [Equiv.Perm.sign_permCongr]

theorem sl2_alt
    (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (θL : ↥L ≃* SL(2, F)) {Q : Subgroup (MulAut V)} (hQ : IsFFStarOffender G Q)
    (hQq : IsQuadratic Q) :
    Nat.card Q * Nat.card (fixV Q) = Nat.card V ∧
      ((Q ≤ L ∧ ∃ e : V ≃* Multiplicative (Fin 2 → F), ∀ (l : ↥L) (v : V),
          e ((l : MulAut V) v) = Multiplicative.ofAdd
            ((θL l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (e v)))) ∨
        (n = 2 ∧ ¬ Q ≤ L ∧ ∃ (σ : ↥(L ⊔ Q) ≃* Equiv.Perm (Fin 5)) (e : V ≃* ↥(G6.coreMod 5)),
          (∀ (y : ↥(L ⊔ Q)) (v : V), e ((y : MulAut V) v) = G6.coreAct 5 (σ y) (e v)) ∧
          ∀ y : ↥(L ⊔ Q), (y : MulAut V) ∈ L ↔ σ y ∈ alternatingGroup (Fin 5))) := by
  classical
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  obtain ⟨hw, θ₀, hθ₀, halt⟩ := sl2_raw hHyp hZ hn hF θL hQ hQq θ
  refine ⟨hw, ?_⟩
  rcases halt with h | h
  · exact Or.inl (nat_of_naturalAlt θ θL θ₀ hθ₀ h)
  · exact Or.inr (del_of_deletedAlt θ θ₀ h)

theorem weight_eq_sl2
    (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (θL : ↥L ≃* SL(2, F)) {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) :
    Nat.card B * Nat.card (fixV B) = Nat.card V :=
  weight_eq_of_quadratic hV (fun _ hQ hQq => (sl2_alt hV hHyp hZ hn hF θL hQ hQq).1) hB

end Alt

end B42L2

end CFSG.Quasithin
