module

public import CFSG.Quasithin.MS93.ML3Split
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix

section Conj

variable {G : Type*} [Group G] {L V : Subgroup G}

@[expose] def conjOn (h : L ≤ Subgroup.normalizer (V : Set G)) : ↥L →* MulAut ↥V where
  toFun l :=
    { toFun := fun v => ⟨(l : G) * v * (l : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (h l.2) v).mp v.2⟩
      invFun := fun v => ⟨(l : G)⁻¹ * v * (l : G), by
        have := (Subgroup.mem_normalizer_iff.mp (h (L.inv_mem l.2)) v).mp v.2
        simpa using this⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun v w => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun v => Subtype.ext (by simp)
  map_mul' l k := MulEquiv.ext fun v => Subtype.ext (by simp [mul_assoc])

theorem coe_conjOn_apply (h : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) (v : ↥V) :
    ((conjOn h l v : ↥V) : G) = (l : G) * v * (l : G)⁻¹ :=
  rfl

end Conj

section Act

variable {G : Type*} [Group G] {L V : Subgroup G} {F : Type} [Field F]

@[expose] noncomputable def toSL3 (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
    ↥L →* SL3 F :=
  (specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α

theorem coe_toSL3 (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (l : ↥L) :
    ((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      (((α l : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
  rw [← specialLinearGroupEquivStatedSL_coe 3 F (toSL3 α l)]
  simp [toSL3]

theorem toSL3_surjective {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hα : Function.Surjective α) : Function.Surjective (toSL3 α) :=
  (specialLinearGroupEquivStatedSL 3 F).symm.surjective.comp hα

@[expose] noncomputable def actSL3 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hker : ∀ l : ↥L, α l = 1 → ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ = v) : SL3 F →* MulAut ↥V :=
  (QuotientGroup.lift (toSL3 α).ker (conjOn hLV) (by
      intro l hl
      rw [MonoidHom.mem_ker] at hl ⊢
      have hl' : α l = 1 := by
        have := congrArg (specialLinearGroupEquivStatedSL 3 F) hl
        simpa [toSL3] using this
      exact MulEquiv.ext fun v => Subtype.ext (hker l hl' v v.2))).comp
    (QuotientGroup.quotientKerEquivOfSurjective (toSL3 α) (toSL3_surjective hα)).symm.toMonoidHom

theorem actSL3_toSL3 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hker : ∀ l : ↥L, α l = 1 → ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ = v) (l : ↥L) :
    actSL3 hLV hα hker (toSL3 α l) = conjOn hLV l := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (toSL3 α) (toSL3_surjective hα)).symm
      (toSL3 α l) = (l : ↥L ⧸ (toSL3 α).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [actSL3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]

end Act

section Bridge

variable {G : Type} [Group G] [Finite G] {L U V : Subgroup G} {F : Type} [Field F] [Fintype F]

theorem isSumOfNaturalModulesVia_two_of_ext
    (h14 : MS14AS) {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hker : ∀ l : ↥L, α l = 1 → ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ = v)
    (hsq : SQTKGroup (SL3 F))
    (hU : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hVU : IsSumOfNaturalModulesVia L V U α false 1) :
    IsSumOfNaturalModulesVia L V ⊥ α false 2 := by
  obtain ⟨hLU, -, βU, hβUs, hβUk, hβUeq⟩ := hU
  obtain ⟨hLV, hUV, βV, hβVs, hβVk, hβVeq⟩ := hVU
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hF'
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with
      mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  set ρ := actSL3 hLV hα hker with hρ
  let e1 : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))
  have he1 : ∀ m : Multiplicative (Fin 1 → Fin 3 → F),
      Multiplicative.toAdd (e1 m) = Multiplicative.toAdd m 0 := fun m => rfl
  have he1s : ∀ x : Fin 3 → F, Multiplicative.toAdd (e1.symm (Multiplicative.ofAdd x)) 0 = x :=
    fun x => rfl
  have hβUi : Function.Injective βU := by
    rw [← MonoidHom.ker_eq_bot_iff, hβUk, Subgroup.bot_subgroupOf]
  let eU : ↥U ≃* Multiplicative (Fin 1 → Fin 3 → F) := MulEquiv.ofBijective βU ⟨hβUi, hβUs⟩
  let ι : Multiplicative (Fin 3 → F) →* ↥V :=
    (Subgroup.inclusion hUV).comp (eU.symm.toMonoidHom.comp e1.symm.toMonoidHom)
  let β : ↥V →* Multiplicative (Fin 3 → F) := e1.toMonoidHom.comp βV
  have hρl : ∀ l : ↥L, ρ (toSL3 α l) = conjOn hLV l := actSL3_toSL3 hLV hα hker
  have hmat : ∀ l : ↥L, moduleAct false (α l : GL (Fin 3) F) =
      ((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) := fun l => by
    rw [coe_toSL3]
    rfl
  let E : NatNatExt ρ :=
    { ι := ι
      β := β
      ι_injective := (Subgroup.inclusion_injective hUV).comp
        (eU.symm.injective.comp e1.symm.injective)
      β_surjective := e1.surjective.comp hβVs
      ker_β := by
        ext v
        rw [MonoidHom.mem_ker, MonoidHom.mem_range]
        constructor
        · intro hv
          have hv' : βV v = 1 := e1.injective (by simpa [β] using hv)
          have hvU : v ∈ U.subgroupOf V := hβVk ▸ hv'
          rw [Subgroup.mem_subgroupOf] at hvU
          refine ⟨e1 (βU ⟨v, hvU⟩), ?_⟩
          apply Subtype.ext
          show ((eU.symm (e1.symm (e1 (βU ⟨v, hvU⟩))) : ↥U) : G) = v
          rw [MulEquiv.symm_apply_apply]
          exact congrArg Subtype.val (eU.symm_apply_apply ⟨v, hvU⟩)
        · rintro ⟨x, rfl⟩
          have hmem : (ι x : ↥V) ∈ U.subgroupOf V := by
            rw [Subgroup.mem_subgroupOf]
            exact (eU.symm (e1.symm x)).2
          rw [← hβVk, MonoidHom.mem_ker] at hmem
          simp [β, hmem]
      ι_equiv := fun g x => by
        obtain ⟨l, rfl⟩ := toSL3_surjective hα g
        rw [hρl]
        set u := eU.symm (e1.symm (Multiplicative.ofAdd x)) with hu
        have hu' : ((l : G) * u * (l : G)⁻¹) ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hLU l.2) u).mp u.2
        have heq := hβUeq l u ⟨_, hu'⟩ rfl 0
        have hβu : βU u = e1.symm (Multiplicative.ofAdd x) := eU.apply_symm_apply _
        rw [hβu, he1s, hmat] at heq
        have hβu' : βU ⟨_, hu'⟩ = e1.symm (Multiplicative.ofAdd
            (((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) := by
          apply e1.injective
          apply Multiplicative.toAdd.injective
          rw [he1, MulEquiv.apply_symm_apply, toAdd_ofAdd]
          exact heq
        have hu'eq : (⟨_, hu'⟩ : ↥U) = eU.symm (e1.symm (Multiplicative.ofAdd
            (((toSL3 α l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x))) := by
          rw [MulEquiv.eq_symm_apply]
          exact hβu'
        apply Subtype.ext
        change (l : G) * (u : G) * (l : G)⁻¹ = _
        rw [show ((l : G) * (u : G) * (l : G)⁻¹) = ((⟨_, hu'⟩ : ↥U) : G) from rfl, hu'eq]
        rfl
      β_equiv := fun g v => by
        obtain ⟨l, rfl⟩ := toSL3_surjective hα g
        rw [hρl]
        have heq := hβVeq l v (conjOn hLV l v) rfl 0
        rw [hmat] at heq
        simp only [β, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply, he1]
        exact heq }
  have hV2' : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV2 v v.2)
  have hsqρ : SQTKGroup ↥ρ.range :=
    InternalSec.sqtkGroup_of_surjective E.rangeEquiv.toMonoidHom E.rangeEquiv.surjective
      (by
        rw [show (E.rangeEquiv.toMonoidHom).ker = ⊥ from
          (MonoidHom.ker_eq_bot_iff _).mpr E.rangeEquiv.injective]
        exact IsPGroup.of_bot)
      hsq
  obtain ⟨γ, hγb, hγeq⟩ := E.exists_equiv_two hV2' h14 hF' hsqρ
  refine ⟨hLV, bot_le, γ, hγb.2, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff γ).mpr hγb.1
  · intro a u v huv i
    have hv : v = ρ (toSL3 α a) u := by
      rw [hρl]
      exact Subtype.ext huv
    rw [hv, hγeq, hmat]

end Bridge

end CFSG.Quasithin.MS93
