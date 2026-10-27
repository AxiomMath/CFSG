module

public import CFSG.Quasithin.Background.SmithB45J2Desc
public import CFSG.Quasithin.Background.SmithB45J2Small
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42DichProof

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Model CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.H CFSG.Open

section Realize

variable {V : Type} [CommGroup V]

theorem realizes_of_equiv {L : Subgroup (MulAut V)} (π : ↥j2Γ₀ →* ↥L)
    (hπ : Function.Surjective π) (e : V ≃* W6)
    (he : ∀ (γ : ↥j2Γ₀) (v : V), e (((π γ : ↥L) : MulAut V) v) = matHom (qHomJ γ) (e v)) :
    (FFModel.zornQ j2Γ₀).Realizes L ⊤ ⊥ := by
  let q : ↥(FFModel.zornQ j2Γ₀).sec ⧸ (FFModel.zornQ j2Γ₀).ker.subgroupOf
      (FFModel.zornQ j2Γ₀).sec ≃* W6 :=
    MulEquiv.ofBijective qQuot qQuot_bijective
  let β : ↥(⊤ : Subgroup V) →* ↥(FFModel.zornQ j2Γ₀).sec ⧸ (FFModel.zornQ j2Γ₀).ker.subgroupOf
      (FFModel.zornQ j2Γ₀).sec :=
    q.symm.toMonoidHom.comp (e.toMonoidHom.comp (⊤ : Subgroup V).subtype)
  have hqβ : ∀ u : ↥(⊤ : Subgroup V), q (β u) = e u := fun u => q.apply_symm_apply _
  refine ⟨π, hπ, bot_le, zornR_le_zornO0, fun _ _ _ => Subgroup.mem_top _, ?_,
    fun γ m hm => zornAct_mem_O0 _ j2Γ₀_le_quasithinG2 γ hm,
    fun γ m hm => zornAct_mem_R _ j2Γ₀_le_quasithinG2 γ hm, β, ?_, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨v, hv⟩ := e.surjective (q y)
    refine ⟨⟨v, Subgroup.mem_top v⟩, q.injective ?_⟩
    rw [hqβ]
    exact hv
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h1 := hqβ u
      rw [h, map_one] at h1
      exact e.injective (h1.symm.trans (map_one e).symm)
    · intro h
      apply q.injective
      rw [hqβ, h, map_one, map_one]
  · intro (γ : ↥j2Γ₀) u m hu hm h
    apply q.injective
    have hu' : q (QuotientGroup.mk m) = e u := by
      rw [← h]
      exact hqβ u
    refine (hqβ ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩).trans ((he γ u).trans ?_)
    rw [← hu']
    change matHom (qHomJ γ) (Multiplicative.ofAdd (qProj (Multiplicative.toAdd
      (m.1 : Multiplicative (quasithinZorn FieldFour))))) =
      Multiplicative.ofAdd (qProj (Multiplicative.toAdd ((FFModel.zornQ j2Γ₀).act γ m.1)))
    apply Multiplicative.toAdd.injective
    rw [toAdd_matHom, toAdd_ofAdd, toAdd_ofAdd, qHomJ, MonoidHom.comp_apply, qHom_mulVec]
    have htr : (Multiplicative.toAdd m.1).1 + (Multiplicative.toAdd m.1).2.2.2 = 0 := m.2
    exact (qProj_apply (j2Γ₀_le_quasithinG2 γ.2) htr).symm

end Realize

end CFSG.Quasithin.J2Row

namespace CFSG.Quasithin.J2Mod

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.J2Row
  CFSG.Quasithin.J2Model CFSG.Quasithin.H FieldFour Matrix Module

section Module

variable {W : Type} [CommGroup W] (hV : ∀ w : W, w ^ 2 = 1)

@[expose] def autLinJ (a : MulAut W) : F2Vec W hV →ₗ[ZMod 2] F2Vec W hV :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v => F2Vec.ofV hV (a (F2Vec.toV hV v))
      map_zero' := by
        rw [F2Vec.toV_zero, map_one, F2Vec.ofV_one]
      map_add' := fun u v => by
        rw [F2Vec.toV_add, map_mul, F2Vec.ofV_mul] }

@[expose] def autRepJ : MulAut W →* (F2Vec W hV →ₗ[ZMod 2] F2Vec W hV) where
  toFun := autLinJ hV
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

variable {L : Subgroup (MulAut W)} {H : Type*} [Group H]

@[expose] def autRepOfJ (θ : ↥L ≃* H) : Representation (ZMod 2) H (F2Vec W hV) :=
  (autRepJ hV).comp (L.subtype.comp θ.symm.toMonoidHom)

theorem autRepOfJ_apply (θ : ↥L ≃* H) (g : H) (v : F2Vec W hV) :
    autRepOfJ hV θ g v = F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v)) :=
  rfl

theorem isIrreducible_autRepOfJ [Nontrivial W] (θ : ↥L ≃* H)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    (autRepOfJ hV θ).IsIrreducible := by
  have : Nontrivial (F2Vec W hV) := inferInstanceAs (Nontrivial (Additive W))
  have hbt : (⊥ : Subrepresentation (autRepOfJ hV θ)) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : F2Vec W hV)
    have hvt : v ∈ (⊤ : Subrepresentation (autRepOfJ hV θ)).toSubmodule := Submodule.mem_top
    rw [← h] at hvt
    exact hv ((Submodule.mem_bot _).mp hvt)
  have : Nontrivial (Subrepresentation (autRepOfJ hV θ)) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subgroup W :=
    { carrier := {w | F2Vec.ofV hV w ∈ U.toSubmodule}
      mul_mem' := fun {a b} ha hb => by
        change F2Vec.ofV hV (a * b) ∈ U.toSubmodule
        rw [F2Vec.ofV_mul]
        exact U.toSubmodule.add_mem ha hb
      one_mem' := by
        change F2Vec.ofV hV 1 ∈ U.toSubmodule
        rw [F2Vec.ofV_one]
        exact U.toSubmodule.zero_mem
      inv_mem' := fun {w} hw => by
        have hinv : w⁻¹ = w := by
          rw [inv_eq_iff_mul_eq_one, ← sq]
          exact hV w
        change F2Vec.ofV hV w⁻¹ ∈ U.toSubmodule
        rw [hinv]
        exact hw }
  have hU' : ∀ g ∈ L, ∀ u ∈ U', g u ∈ U' := by
    intro g hg u hu
    have h1 := U.apply_mem_toSubmodule (θ ⟨g, hg⟩) hu
    change F2Vec.ofV hV ((θ.symm (θ ⟨g, hg⟩) : MulAut W) (F2Vec.toV hV (F2Vec.ofV hV u))) ∈
      U.toSubmodule at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1
  rcases hirr U' hU' with h0 | h0
  · left
    ext v
    constructor
    · intro hv
      have hv' : F2Vec.toV hV v ∈ U' := hv
      rw [h0, Subgroup.mem_bot] at hv'
      have hv0 : v = 0 := by
        rw [← F2Vec.ofV_toV hV v, hv', F2Vec.ofV_one]
      rw [hv0]
      exact Submodule.zero_mem _
    · intro hv
      have hv0 : v = 0 := (Submodule.mem_bot _).mp hv
      rw [hv0]
      exact U.toSubmodule.zero_mem
  · right
    ext v
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      have hv' : F2Vec.toV hV v ∈ U' := by
        rw [h0]
        exact Subgroup.mem_top _
      exact hv'

theorem finrank_lt_of_card_lt [Finite W] (hcard : Nat.card W < 2 ^ 24) :
    finrank (ZMod 2) (F2Vec W hV) < 24 := by
  have h1 : Nat.card (F2Vec W hV) = 2 ^ finrank (ZMod 2) (F2Vec W hV) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (F2Vec W hV) = Nat.card W := rfl
  have h3 : 2 ^ finrank (ZMod 2) (F2Vec W hV) < 2 ^ 24 := by
    rw [← h1, h2]
    exact hcard
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3

end Module

theorem j2SmallModules_holds :
    J2SmallModules := by
  intro V _ _ hV L hL hirr hcard
  obtain ⟨θ0⟩ := hL
  let θ : ↥L ≃* G6 := θ0.trans gammaEquiv
  obtain ⟨hntV, hirrU⟩ := CFSG.QuasithinUnique.Bridge.Dichotomy.isIrrOn_of_isIrrSec hirr
  have hfin : FiniteDimensional (ZMod 2) (F2Vec V hV) := Module.Finite.of_finite
  rcases j2_binary_small (F2Vec V hV) (autRepOfJ hV θ) (isIrreducible_autRepOfJ hV θ hirrU)
      (finrank_lt_of_card_lt hV hcard) with he | he
  · obtain ⟨e⟩ := he
    exfalso
    have htriv : ∀ g : G6, g = 1 := by
      intro g
      have h1 : ∀ w : V, (θ.symm g : MulAut V) w = w := by
        intro w
        have h2 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g
          (F2Vec.ofV hV w)
        have h3 : rep1 g = 1 := rfl
        rw [matrixBaseChange_apply, h3, RingHom.coe_id, Matrix.map_id, Matrix.one_mulVec,
          Representation.Equiv.coe_toIntertwiningMap] at h2
        exact Additive.ofMul.injective (e.injective h2)
      have h5 : θ.symm g = 1 := Subtype.ext (MulEquiv.ext h1)
      exact θ.symm.injective (h5.trans (map_one θ.symm).symm)
    obtain ⟨x, y, hxy⟩ := exists_pair_ne G6
    exact hxy ((htriv x).trans (htriv y).symm)
  · obtain ⟨e⟩ := he
    let E : V ≃* W6 :=
      { toFun := fun v => Multiplicative.ofAdd (e (F2Vec.ofV hV v))
        invFun := fun x => F2Vec.toV hV (e.symm (Multiplicative.toAdd x))
        left_inv := fun v => by
          change F2Vec.toV hV (e.symm (e (F2Vec.ofV hV v))) = v
          rw [Representation.Equiv.symm_apply_apply]
          rfl
        right_inv := fun x => by
          change Multiplicative.ofAdd (e (F2Vec.ofV hV (F2Vec.toV hV
            (e.symm (Multiplicative.toAdd x))))) = x
          rw [F2Vec.ofV_toV, Representation.Equiv.apply_symm_apply]
          rfl
        map_mul' := fun a b => by
          simp only [F2Vec.ofV_mul, map_add, ofAdd_add] }
    refine realizes_of_equiv (θ.symm.toMonoidHom.comp qHomΓ)
      (θ.symm.surjective.comp qHomΓ_surjective) E fun γ v => ?_
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (qHomΓ γ)
      (F2Vec.ofV hV v)
    rw [Representation.Equiv.coe_toIntertwiningMap, restrictF4_apply,
      autRepOfJ_apply] at h1
    apply Multiplicative.toAdd.injective
    rw [toAdd_matHom]
    exact h1

end CFSG.Quasithin.J2Mod
