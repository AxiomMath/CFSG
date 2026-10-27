module

public import CFSG.Quasithin.Background.G2Omega4Plus
public import CFSG.Quasithin.Background.G2Omega4PlusFiveData

public section

namespace CFSG.Quasithin.Om4Model

theorem polarDet_add_left : ∀ X X' Y : Mt,
    polarDet (X + X') Y = polarDet X Y + polarDet X' Y := by
  decide +kernel

theorem polarDet_self : ∀ X : Mt, polarDet X X = 0 := by
  decide +kernel

theorem polarDet_zero_left : ∀ X : Mt, polarDet 0 X = 0 := by
  decide +kernel

theorem exists_perp_decomp {X₁ X₂ : Mt} (h : polarDet X₁ X₂ ≠ 0) (Y : Mt) :
    ∃ a b : Mt, polarDet a X₁ = 0 ∧ polarDet b X₂ = 0 ∧ Y = a + b := by
  by_cases hY : polarDet Y X₁ = 0
  · exact ⟨Y, 0, hY, polarDet_zero_left X₂, by simp⟩
  · refine ⟨Y + X₂, X₂, ?_, polarDet_self X₂, ?_⟩
    · rw [polarDet_add_left]
      have h1 : polarDet X₂ X₁ ≠ 0 := by rw [polarDet_comm]; exact h
      have : ∀ z w : ZMod 2, z ≠ 0 → w ≠ 0 → z + w = 0 := by decide
      exact this _ _ hY h1
    · rw [add_assoc, add_self_mt, add_zero]

end CFSG.Quasithin.Om4Model

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups commutatorElement
open Om4Model

variable {G : Type*} [Group G]

theorem abel_sq_of_prod {S S₂ W W' : Subgroup G} (hN : ∀ x ∈ S, ∀ y ∈ S₂, x * y * x⁻¹ ∈ S₂)
    (hWS : W ≤ S) (hW'S : W' ≤ S) (hSW : (S : Set G) = (W : Set G) * (W' : Set G))
    (hWW : ∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ S₂)
    (hW'W' : ∀ x ∈ W', ∀ y ∈ W', x * y * x⁻¹ * y⁻¹ ∈ S₂)
    (hWW' : ∀ x ∈ W, ∀ y ∈ W', x * y * x⁻¹ * y⁻¹ ∈ S₂)
    (hW2 : ∀ x ∈ W, x * x ∈ S₂) (hW'2 : ∀ x ∈ W', x * x ∈ S₂) :
    (∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ S₂) ∧ ∀ a ∈ S, a * a ∈ S₂ := by
  have hNor : (S₂.subgroupOf S).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (fun _ hx => (le_normalizer_of_conj_mem hN : S ≤ Subgroup.normalizer (S₂ : Set G)) hx)
  have key : ∀ x y : ↥S, (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ S₂ →
      Commute (secMk S S₂ x) (secMk S S₂ y) := by
    intro x y h
    have h1 : secMk S S₂ (x * y * x⁻¹ * y⁻¹) = 1 := secMk_eq_one_iff.2 (by simpa using h)
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hsplit : ∀ a ∈ S, ∃ w ∈ W, ∃ x ∈ W', a = w * x := fun a ha => by
    have h : a ∈ (S : Set G) := ha
    rw [hSW] at h
    obtain ⟨w, hw, x, hx, rfl⟩ := h
    exact ⟨w, hw, x, hx, rfl⟩
  have hsq : ∀ (x : G) (hx : x ∈ S), x * x ∈ S₂ →
      secMk S S₂ ⟨x, hx⟩ * secMk S S₂ ⟨x, hx⟩ = 1 := by
    intro x hx h
    rw [← map_mul]
    exact secMk_eq_one_iff.2 h
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨w₁, hw₁, x₁, hx₁, rfl⟩ := hsplit a ha
    obtain ⟨w₂, hw₂, x₂, hx₂, rfl⟩ := hsplit b hb
    have c11 : Commute (secMk S S₂ ⟨w₁, hWS hw₁⟩) (secMk S S₂ ⟨w₂, hWS hw₂⟩) :=
      key _ _ (hWW _ hw₁ _ hw₂)
    have c12 : Commute (secMk S S₂ ⟨w₁, hWS hw₁⟩) (secMk S S₂ ⟨x₂, hW'S hx₂⟩) :=
      key _ _ (hWW' _ hw₁ _ hx₂)
    have c21 : Commute (secMk S S₂ ⟨x₁, hW'S hx₁⟩) (secMk S S₂ ⟨w₂, hWS hw₂⟩) :=
      (key _ _ (hWW' _ hw₂ _ hx₁)).symm
    have c22 : Commute (secMk S S₂ ⟨x₁, hW'S hx₁⟩) (secMk S S₂ ⟨x₂, hW'S hx₂⟩) :=
      key _ _ (hW'W' _ hx₁ _ hx₂)
    have hc := (Commute.mul_right c11 c12).mul_left (Commute.mul_right c21 c22)
    have e1 : (⟨w₁ * x₁, ha⟩ : ↥S) = ⟨w₁, hWS hw₁⟩ * ⟨x₁, hW'S hx₁⟩ := rfl
    have e2 : (⟨w₂ * x₂, hb⟩ : ↥S) = ⟨w₂, hWS hw₂⟩ * ⟨x₂, hW'S hx₂⟩ := rfl
    exact commutator_mem_of_secMk_commute (x := ⟨w₁ * x₁, ha⟩) (y := ⟨w₂ * x₂, hb⟩)
      (by rw [e1, e2, map_mul, map_mul]; exact hc)
  · obtain ⟨w₁, hw₁, x₁, hx₁, rfl⟩ := hsplit a ha
    have c : Commute (secMk S S₂ ⟨x₁, hW'S hx₁⟩) (secMk S S₂ ⟨w₁, hWS hw₁⟩) :=
      (key _ _ (hWW' _ hw₁ _ hx₁)).symm
    have e1 : (⟨w₁ * x₁, ha⟩ : ↥S) = ⟨w₁, hWS hw₁⟩ * ⟨x₁, hW'S hx₁⟩ := rfl
    have h1 := hsq w₁ (hWS hw₁) (hW2 _ hw₁)
    have h2 := hsq x₁ (hW'S hx₁) (hW'2 _ hx₁)
    have h3 : secMk S S₂ ⟨w₁ * x₁, ha⟩ * secMk S S₂ ⟨w₁ * x₁, ha⟩ = 1 := by
      rw [e1, map_mul, c.mul_mul_mul_comm, h1, h2, one_mul]
    rw [← map_mul] at h3
    simpa using secMk_eq_one_iff.1 h3


theorem rconj_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) : rconj X g ≤ rconj Y g :=
  fun _ hy => mem_rconj.2 (h (mem_rconj.1 hy))

namespace Om4Setting

variable {V V₁ L T H : Subgroup G} (S : Om4Setting V V₁ L T H)

include S

theorem VL_decomp {g : G} (hg : g ∈ L) (hgV : ¬ rconj V₁ g ≤ V) :
    ∀ y ∈ conjClosure V₁ L, ∃ v ∈ V, ∃ v' ∈ rconj V g, y = v * v' := by
  obtain ⟨X₁, hX₁, hdet₁, -, hperp, hpolar⟩ := S.core hg hgV
  intro y hy
  have hgLU : g ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hg
  have hginvLU : g⁻¹ ∈ L ⊔ conjClosure V H :=
    (le_sup_left : L ≤ L ⊔ conjClosure V H) (L.inv_mem hg)
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_perp_decomp hpolar (Multiplicative.toAdd (S.D.ψ ⟨y, hy⟩))
  obtain ⟨v₀, hv₀⟩ : ∃ v : ↥(conjClosure V₁ L), S.D.ψ v = Multiplicative.ofAdd a :=
    ⟨S.D.ψ.symm _, MulEquiv.apply_symm_apply _ _⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v : ↥(conjClosure V₁ L), S.D.ψ v = Multiplicative.ofAdd b :=
    ⟨S.D.ψ.symm _, MulEquiv.apply_symm_apply _ _⟩
  have hv₀V : (v₀ : G) ∈ V := (hperp v₀).2 (by rw [hv₀, toAdd_ofAdd]; exact ha)
  have hψ : Multiplicative.toAdd (S.D.ψ (conjAct (conjClosure V₁ L) ⟨g, S.D.hnorm hgLU⟩ v₁)) =
      omSmul (S.D.α ⟨g, hgLU⟩) (Multiplicative.toAdd (S.D.ψ v₁)) := S.D.equiv ⟨g, hgLU⟩ v₁
  rw [hv₁, toAdd_ofAdd] at hψ
  have hγinv : S.D.α ⟨g⁻¹, hginvLU⟩ = (S.D.α ⟨g, hgLU⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hX₁eq : omSmul (S.D.α ⟨g, hgLU⟩) (omSmul (S.D.α ⟨g⁻¹, hginvLU⟩) X₁) = X₁ := by
    rw [hγinv, ← omSmul_mul, mul_inv_cancel, omSmul_one]
  have hv₁V : (conjAct (conjClosure V₁ L) ⟨g, S.D.hnorm hgLU⟩ v₁ : G) ∈ V := by
    refine (hperp _).2 ?_
    rw [hψ]
    calc polarDet (omSmul (S.D.α ⟨g, hgLU⟩) b) X₁
        = polarDet (omSmul (S.D.α ⟨g, hgLU⟩) b)
            (omSmul (S.D.α ⟨g, hgLU⟩) (omSmul (S.D.α ⟨g⁻¹, hginvLU⟩) X₁)) := by rw [hX₁eq]
      _ = polarDet b (omSmul (S.D.α ⟨g⁻¹, hginvLU⟩) X₁) := polarDet_omSmul _ _ _
      _ = 0 := hb
  rw [conjAct_coe_apply] at hv₁V
  have hyv : (⟨y, hy⟩ : ↥(conjClosure V₁ L)) = v₀ * v₁ := by
    apply S.D.ψ.injective
    rw [map_mul, hv₀, hv₁]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
    exact hab
  exact ⟨v₀, hv₀V, v₁, mem_rconj.2 hv₁V, congrArg Subtype.val hyv⟩

end Om4Setting

namespace AlmostSpecialOm4Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialOm4Hyp V V₁ L T H)

include hyp

theorem G26_five {U I S S₂ : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgV : ¬ rconj V₁ g ≤ V) (hI : I = U ⊔ rconj U g) (hS : S = pCoreOf 2 I)
    (hS₂ : S₂ = conjClosure V₁ L ⊔ (U ⊓ rconj U g)) :
    ∃ M₁ M₂ Sa Sb : Subgroup G,
      S ≤ M₁ ∧ S ≤ M₂ ∧ M₁ ≤ I ∧ M₂ ≤ I ∧ M₁ ⊔ M₂ = I ∧ M₁ ⊓ M₂ = S ∧ ⁅M₁, M₂⁆ ≤ S ∧
      S₂ ≤ Sa ∧ Sa ≤ S ∧ S₂ ≤ Sb ∧ Sb ≤ S ∧ Sa ⊔ Sb = S ∧ Sa ⊓ Sb = S₂ ∧ ⁅Sa, Sb⁆ ≤ S₂ ∧
      Sa = ⁅S, M₁⁆ ⊔ S₂ ∧ Sb = ⁅S, M₂⁆ ⊔ S₂ ∧
      (∀ s ∈ S, s ∈ Sa ↔ ∀ m ∈ M₂, ⁅m, s⁆ ∈ S₂) ∧
      (∀ s ∈ S, s ∈ Sb ↔ ∀ m ∈ M₁, ⁅m, s⁆ ∈ S₂) ∧
      IsSumOfNaturalSL2Modules M₁ Sa S S₂ ∧ IsSumOfNaturalSL2Modules M₂ Sb S S₂ := by
  subst hS hS₂
  obtain ⟨D, hperp⟩ := hyp.module
  let St : Om4Setting V V₁ L T H := ⟨hyp, D, hperp⟩
  have hI' : I = L ⊔ U := St.I_eq_LU' hU hg hgV hI
  have hUI : U ≤ I := by rw [hI]; exact le_sup_left
  have hLI : L ≤ I := by rw [hI']; exact le_sup_left
  have hgI : g ∈ I := hLI hg
  have hUT : U ≤ T := St.U_le_T' hU
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := by rw [hU]; exact St.T_le_normU
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ :=
    sx_facts_gen hI' hUT hTU hyp.base.T_le_normL hyp.base.sylow_LT
  obtain ⟨h31, h32, h33, h34, h35, h36⟩ := hyp.G26_three hU hg hgV hI
  obtain ⟨hSeq, hSset⟩ := hyp.G26_two (U := U) (I := I) (S := pCoreOf 2 I)
    (W := U ⊓ pCoreOf 2 I) hU hg hgV hI rfl rfl
  have hIle' : I ≤ L ⊔ conjClosure V H := by rw [hI', hU]
  have hV₁VL : V₁ ≤ conjClosure V₁ L := le_conjClosure V₁ L
  have hV₁S₂ : V₁ ≤ conjClosure V₁ L ⊔ (U ⊓ rconj U g) := hV₁VL.trans le_sup_left
  have hS₂N : ∀ x ∈ I, ∀ y ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g),
      x * y * x⁻¹ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
    fun x hx y hy => (Subgroup.mem_normalizer_iff.1 (h35 hx) y).1 hy
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁ := fun x hx y hy =>
    G22Conclusion.commutator_mem hyp.base hyp.g22 (hU ▸ hx) (hU ▸ hy)
  have hsq : ∀ x ∈ U, x * x ∈ V₁ := fun x hx => by
    have := G22Conclusion.sq_mem hyp.base hyp.g22 (hU ▸ hx)
    rwa [pow_two] at this
  have hW'S : rconj (U ⊓ pCoreOf 2 I) g ≤ pCoreOf 2 I := rconj_inf_le_Sx hgI hINorm
  have hWW : ∀ x ∈ U ⊓ pCoreOf 2 I, ∀ y ∈ U ⊓ pCoreOf 2 I,
      x * y * x⁻¹ * y⁻¹ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
    fun x hx y hy => hV₁S₂ (hcomm x hx.1 y hy.1)
  have hW'W' : ∀ x ∈ rconj (U ⊓ pCoreOf 2 I) g, ∀ y ∈ rconj (U ⊓ pCoreOf 2 I) g,
      x * y * x⁻¹ * y⁻¹ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) := by
    intro x hx y hy
    have hc := hcomm _ (mem_rconj.1 hx).1 _ (mem_rconj.1 hy).1
    have := hS₂N g⁻¹ (I.inv_mem hgI) _ (hV₁S₂ hc)
    have e : g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) * g⁻¹⁻¹ =
        x * y * x⁻¹ * y⁻¹ := by group
    rwa [e] at this
  have hWW' : ∀ x ∈ U ⊓ pCoreOf 2 I, ∀ y ∈ rconj (U ⊓ pCoreOf 2 I) g,
      x * y * x⁻¹ * y⁻¹ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ U ⊓ pCoreOf 2 I :=
      comm_mem_inf_of_normalizes hx.1 (hW'S hy) (fun a ha b hb => hINorm a (hUI ha) b hb) hSxU
    have hyU : y ∈ rconj U g := mem_rconj.2 (mem_rconj.1 hy).1
    have h2 : y * x * y⁻¹ * x⁻¹ ∈ rconj (U ⊓ pCoreOf 2 I) g :=
      comm_mem_rconj_inf hgI hINorm hUI hSxU hyU hx.2
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ rconj U g := by
      have := (rconj (U ⊓ pCoreOf 2 I) g).inv_mem h2
      have e : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
      rw [e] at this
      exact rconj_mono inf_le_left g this
    exact (le_sup_right : U ⊓ rconj U g ≤ _) ⟨h1.1, h3⟩
  have hW2 : ∀ x ∈ U ⊓ pCoreOf 2 I, x * x ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
    fun x hx => hV₁S₂ (hsq x hx.1)
  have hW'2 : ∀ x ∈ rconj (U ⊓ pCoreOf 2 I) g, x * x ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) := by
    intro x hx
    have hc := hsq _ (mem_rconj.1 hx).1
    have := hS₂N g⁻¹ (I.inv_mem hgI) _ (hV₁S₂ hc)
    have e : g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g⁻¹⁻¹ = x * x := by group
    rwa [e] at this
  obtain ⟨habel, hsq'⟩ := abel_sq_of_prod (S := pCoreOf 2 I)
    (S₂ := conjClosure V₁ L ⊔ (U ⊓ rconj U g)) (W := U ⊓ pCoreOf 2 I)
    (W' := rconj (U ⊓ pCoreOf 2 I) g)
    (fun x hx y hy => hS₂N x (pCoreOf_le 2 I hx) y hy) inf_le_right hW'S hSset hWW hW'W' hWW'
    hW2 hW'2
  have hQ : QuotSetting I (pCoreOf 2 I) (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) :=
    { S₂_le := h32
      Sx_le := pCoreOf_le 2 I
      nS := hINorm
      nS₂ := hS₂N
      abel := habel
      sq := hsq' }
  obtain ⟨α, hαdef⟩ : ∃ α : ↥I →* OmG, ∀ x : ↥I, α x = St.D.α ⟨x, hIle' x.2⟩ :=
    ⟨St.D.α.comp (Subgroup.inclusion hIle'), fun x => rfl⟩
  have hαsurj : Function.Surjective α := by
    intro y
    obtain ⟨x, rfl⟩ := St.D.surj y
    have hxI : (x : G) ∈ I := by rw [hI', hU]; exact x.2
    exact ⟨⟨x, hxI⟩, by rw [hαdef]⟩
  have hker : ∀ x : ↥I, α x = 1 ↔ (x : G) ∈ pCoreOf 2 I := by
    intro x
    rw [hαdef x, St.alpha_eq_one_iff]
    exact ⟨fun h => mem_pCoreOf_of_mem_pCoreOf_of_le hIle x.2 h, fun h => hSxO h⟩
  have hUc : ∀ u ∈ U, ∀ s ∈ pCoreOf 2 I, u * s * u⁻¹ * s⁻¹ ∈ U ⊓ pCoreOf 2 I :=
    fun u hu s hs => comm_mem_inf_of_normalizes hu hs
      (fun x hx y hy => hINorm x (hUI hx) y hy) hSxU
  have hUW : ∀ u ∈ U, ∀ w ∈ U ⊓ pCoreOf 2 I,
      u * w * u⁻¹ * w⁻¹ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
    fun u hu w hw => hV₁S₂ (hcomm u hu w hw.1)
  have hSx : ∀ s ∈ pCoreOf 2 I, ∃ w ∈ U ⊓ pCoreOf 2 I, ∃ v ∈ U ⊓ pCoreOf 2 I,
      s = w * (g⁻¹ * v * g) := by
    intro s hs
    have h : s ∈ ((pCoreOf 2 I : Subgroup G) : Set G) := hs
    rw [hSset] at h
    obtain ⟨w, hw, y, hy, rfl⟩ := h
    refine ⟨w, hw, g * y * g⁻¹, mem_rconj.1 hy, ?_⟩
    group
  have hVW : V ≤ U ⊓ pCoreOf 2 I := by
    refine le_inf ?_ ?_
    · rw [hU]; exact le_conjClosure V H
    · exact (hyp.V_le_VL.trans (le_sup_left : conjClosure V₁ L ≤ _)).trans h32
  have hCN : U ⊓ rconj U g ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) :=
    inf_le_left.trans (hUI.trans h34)
  have hS₂mul : ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) =
      (conjClosure V₁ L : Set G) * ((U ⊓ rconj U g : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN
  have hcap : ∀ v ∈ U ⊓ pCoreOf 2 I, ∀ w ∈ U ⊓ pCoreOf 2 I,
      w⁻¹ * (g⁻¹ * v * g) ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) →
        g⁻¹ * v * g ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) := by
    intro v hv w hw hmem
    have hx : g⁻¹ * v * g ∈ rconj (U ⊓ pCoreOf 2 I) g := inv_mul_mul_mem_rconj hv
    have hmem' : w⁻¹ * (g⁻¹ * v * g) ∈
        ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) := hmem
    rw [hS₂mul] at hmem'
    obtain ⟨y, hy, a, ha, hya⟩ := hmem'
    obtain ⟨v₀, hv₀, v', hv', rfl⟩ := St.VL_decomp hg hgV y hy
    have hv'VL : v' ∈ conjClosure V₁ L := by
      have := (conjClosure V₁ L).mul_mem ((conjClosure V₁ L).inv_mem (hyp.V_le_VL hv₀)) hy
      simpa using this
    have haS : a ∈ pCoreOf 2 I := h32 ((le_sup_right : U ⊓ rconj U g ≤ _) ha)
    have hc : v' * a = a * v' :=
      ((Subgroup.mem_centralizer_iff.1 (h33 hv'VL).2) a haS).symm
    have hx' : g⁻¹ * v * g = w * (v₀ * v' * a) := by
      calc g⁻¹ * v * g = w * (w⁻¹ * (g⁻¹ * v * g)) := by group
        _ = w * (v₀ * v' * a) := by rw [← hya]
    have ht : g⁻¹ * v * g * v'⁻¹ = w * v₀ * a := by
      rw [hx']
      calc w * (v₀ * v' * a) * v'⁻¹ = w * v₀ * (v' * a) * v'⁻¹ := by group
        _ = w * v₀ * (a * v') * v'⁻¹ := by rw [hc]
        _ = w * v₀ * a := by group
    have htW : w * v₀ * a ∈ U ⊓ pCoreOf 2 I :=
      (U ⊓ pCoreOf 2 I).mul_mem ((U ⊓ pCoreOf 2 I).mul_mem hw (hVW hv₀)) ⟨ha.1, haS⟩
    have htW' : g⁻¹ * v * g * v'⁻¹ ∈ rconj (U ⊓ pCoreOf 2 I) g :=
      (rconj (U ⊓ pCoreOf 2 I) g).mul_mem hx
        ((rconj (U ⊓ pCoreOf 2 I) g).inv_mem (rconj_mono hVW g hv'))
    have htS₂ : g⁻¹ * v * g * v'⁻¹ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
      (le_sup_right : U ⊓ rconj U g ≤ _)
        ⟨by rw [ht]; exact htW.1, rconj_mono inf_le_left g htW'⟩
    have e : g⁻¹ * v * g = (g⁻¹ * v * g * v'⁻¹) * v' := by group
    rw [e]
    exact (conjClosure V₁ L ⊔ (U ⊓ rconj U g)).mul_mem htS₂
      ((le_sup_left : conjClosure V₁ L ≤ _) hv'VL)
  obtain ⟨X₁, hX₁, hdet₁, hstab, -, hpolar⟩ := St.core hg hgV
  obtain ⟨a, b, ha, hb, hX⟩ := exists_vecMulVec X₁ hX₁ hdet₁
  obtain ⟨τ₁, hτ₁, hτ₁', hτ₁a⟩ : ∃ τ : SL(2, ZMod 2), τ * τ = 1 ∧ τ ≠ 1 ∧ τ • a = a := by
    rcases sl2_exists_invol_fix a with h | h
    · exact absurd h ha
    · exact h
  obtain ⟨τ₂, hτ₂, hτ₂', hτ₂b⟩ : ∃ τ : SL(2, ZMod 2), τ * τ = 1 ∧ τ ≠ 1 ∧ τ • b = b := by
    rcases sl2_exists_invol_fix b with h | h
    · exact absurd h hb
    · exact h
  have hfix₁ : omSmul ((τ₁, 1) : OmG) X₁ = X₁ := by
    rw [hX, omSmul_vecMulVec, hτ₁a, one_smul]
  have hfix₂ : omSmul ((1, τ₂) : OmG) X₁ = X₁ := by
    rw [hX, omSmul_vecMulVec, hτ₂b, one_smul]
  obtain ⟨u₁, hu₁U, hu₁α⟩ := hstab _ hfix₁
  obtain ⟨u₂, hu₂U, hu₂α⟩ := hstab _ hfix₂
  have hu₁I : (u₁ : G) ∈ I := hUI (hU ▸ hu₁U)
  have hu₂I : (u₂ : G) ∈ I := hUI (hU ▸ hu₂U)
  have hgLU : g ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hg
  have hginvLU : g⁻¹ ∈ L ⊔ conjClosure V H :=
    (le_sup_left : L ≤ L ⊔ conjClosure V H) (L.inv_mem hg)
  have hγinv : St.D.α ⟨g⁻¹, hginvLU⟩ = (St.D.α ⟨g, hgLU⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hγ3 : (St.D.α ⟨g, hgLU⟩) ^ 3 = 1 := St.alpha_cube_eq_one hg
  have hγ₁ : (St.D.α ⟨g, hgLU⟩).1 ^ 3 = 1 := by simpa using congrArg Prod.fst hγ3
  have hγ₂ : (St.D.α ⟨g, hgLU⟩).2 ^ 3 = 1 := by simpa using congrArg Prod.snd hγ3
  have hpolar' : polarDet (Matrix.vecMulVec a b)
      (Matrix.vecMulVec (((St.D.α ⟨g, hgLU⟩)⁻¹).1 • a) (((St.D.α ⟨g, hgLU⟩)⁻¹).2 • b)) ≠ 0 := by
    have h := hpolar
    rw [hγinv, hX,
      show omSmul (St.D.α ⟨g, hgLU⟩)⁻¹ (Matrix.vecMulVec a b) =
        Matrix.vecMulVec (((St.D.α ⟨g, hgLU⟩)⁻¹).1 • a) (((St.D.α ⟨g, hgLU⟩)⁻¹).2 • b) from
        omSmul_vecMulVec ((St.D.α ⟨g, hgLU⟩)⁻¹).1 ((St.D.α ⟨g, hgLU⟩)⁻¹).2 a b] at h
    exact h
  have hγ₁' : (St.D.α ⟨g, hgLU⟩).1 ≠ 1 := by
    intro h1
    apply hpolar'
    rw [Prod.fst_inv, h1, inv_one, one_smul]
    exact polarDet_vecMulVec_eq_zero _ _ _ _ (Or.inl rfl)
  have hγ₂' : (St.D.α ⟨g, hgLU⟩).2 ≠ 1 := by
    intro h1
    apply hpolar'
    rw [Prod.snd_inv, h1, inv_one, one_smul]
    exact polarDet_vecMulVec_eq_zero _ _ _ _ (Or.inr rfl)
  exact five_of_data hQ α hαsurj hker (inf_le_right : U ⊓ pCoreOf 2 I ≤ pCoreOf 2 I) hgI
    hUc hUW hSx hcap hτ₁ hτ₁' hτ₂ hτ₂' hγ₁ hγ₁' hγ₂ hγ₂'
    (u₁ := ⟨u₁, hu₁I⟩) (u₂ := ⟨u₂, hu₂I⟩) (hU ▸ hu₁U) (by rw [hαdef]; exact hu₁α)
    (hU ▸ hu₂U) (by rw [hαdef]; exact hu₂α) (by rw [hαdef])

end AlmostSpecialOm4Hyp

end CFSG.Quasithin
