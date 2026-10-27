module

public import CFSG.Quasithin.Vol2.Ch11SecO5F

public section

namespace CFSG.Quasithin.Vol2.Ch11.O5

theorem eq_one_of_mul_inv_mem_center {S : Type*} [Group S] [Group.IsPerfect S] (β : MulAut S)
    (h : ∀ x, β x * x⁻¹ ∈ Subgroup.center S) : β = 1 := by
  let f : S →* Subgroup.center S :=
    { toFun := fun x => ⟨β x * x⁻¹, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.mp (h y) x⁻¹
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc β x * β y * (y⁻¹ * x⁻¹) = β x * ((β y * y⁻¹) * x⁻¹) := by group
          _ = β x * (x⁻¹ * (β y * y⁻¹)) := by rw [hc]
          _ = β x * x⁻¹ * (β y * y⁻¹) := by group }
  have hker : commutator S ≤ f.ker := Abelianization.commutator_subset_ker f
  ext x
  have hx : f x = 1 := (MonoidHom.mem_ker).mp (hker Group.IsPerfect.mem_commutator)
  have h1 : β x * x⁻¹ = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

end CFSG.Quasithin.Vol2.Ch11.O5

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.GorensteinWalter Ch11.O5

theorem sl2pSignalizerFact_holds : SL2pSignalizerFact := by
  intro G _ _ K L₁ R p hp hp5 ⟨φ, hφs, hφk⟩ hL₁K hperf ⟨F₄, _, _, hF₄, ⟨eL⟩⟩ hRK hRL hRL₁
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp5' : 5 ≤ p := by rcases hp5 with h | h <;> omega
  have hZp : Nat.card (ZMod p) = p := Nat.card_zmod p
  set Q := oTwoTwoPrime K with hQdef
  let ρ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* PSL2 (ZMod p) := QuotientGroup.mk' _
  let ψ : ↥L₁ →* PSL2 (ZMod p) := ρ.comp (φ.comp (Subgroup.inclusion hL₁K))
  have hψ : ∀ l : ↥L₁, ψ l = ρ (φ ⟨l, hL₁K l.2⟩) := fun _ => rfl
  have hL₁p : Group.IsPerfect L₁ := Subgroup.isPerfect_iff.mpr hperf
  have hSL : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F₄) :=
    ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => by
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F₄ =>
        (A : Matrix (Fin 2) (Fin 2) F₄) 0 1) h
      simp at this⟩⟩
  have : Nontrivial (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := eL.toEquiv.nontrivial
  have : Nontrivial ↥L₁ := (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L₁)).nontrivial
  have hBperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    have : Group.IsPerfect ψ.range := Group.IsPerfect.ofSurjective ψ.rangeRestrict_surjective
    exact Subgroup.isPerfect_iff.mp this
  have hBne : ψ.range ≠ ⊥ := by
    intro h
    have hc : ∀ l : ↥L₁, φ ⟨l, hL₁K l.2⟩ ∈ Subgroup.center _ := fun l => by
      have : ψ l ∈ ψ.range := ⟨l, rfl⟩
      rw [h, Subgroup.mem_bot, hψ] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    let f := (φ.comp (Subgroup.inclusion hL₁K)).codRestrict (Subgroup.center _) hc
    have hf : ∀ l : ↥L₁, f l = 1 := fun l =>
      (MonoidHom.mem_ker).mp (Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator)
    have hLQ : L₁ ≤ Q := fun l hl => by
      have h1 : φ ⟨l, hL₁K hl⟩ = 1 := congrArg Subtype.val (hf ⟨l, hl⟩)
      have h2 : (⟨l, hL₁K hl⟩ : ↥K) ∈ φ.ker := h1
      rw [hφk, Subgroup.mem_subgroupOf] at h2
      exact h2
    have : Group.IsSolvable ↥Q := SecD.isSolvable_oTwoTwoPrime K
    have : Group.IsSolvable ↥L₁ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLQ)
    exact Group.IsPerfect.not_isSolvable (↥L₁) this
  have hB := perfect_cases hp (by omega) hZp hBperf hBne
  have hBs : IsSimpleGroup ψ.range := isSimpleGroup_of_cases hp5' hZp hB
  have hBns : ¬ Group.IsSolvable ψ.range := by
    have : Group.IsPerfect ψ.range := Subgroup.isPerfect_iff.mpr hBperf
    have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hBne
    exact Group.IsPerfect.not_isSolvable _
  have hO : ∀ c (hc : c ∈ pCoreOf 2 L₁), ψ ⟨c, Subgroup.map_subtype_le _ hc⟩ = 1 := by
    intro c hc
    have hcO : (⟨c, Subgroup.map_subtype_le _ hc⟩ : ↥L₁) ∈ CFSG.pCore 2 ↥L₁ :=
      (Subgroup.mem_map_iff_mem L₁.subtype_injective).1 hc
    have hN := eq_bot_of_isPGroup_two hBns
      (Subgroup.Normal.map CFSG.pCore_normal ψ.rangeRestrict ψ.rangeRestrict_surjective)
      (CFSG.pCore_isPGroup.map ψ.rangeRestrict)
    have h1 : ψ.rangeRestrict ⟨c, Subgroup.map_subtype_le _ hc⟩ = 1 := by
      have : ψ.rangeRestrict ⟨c, Subgroup.map_subtype_le _ hc⟩ ∈
          (CFSG.pCore 2 ↥L₁).map ψ.rangeRestrict := ⟨_, hcO, rfl⟩
      rwa [hN, Subgroup.mem_bot] at this
    exact congrArg Subtype.val h1
  have hNn : (Q.subgroupOf K).Normal := hφk ▸ φ.normal_ker
  let eφ : (↥K ⧸ Q.subgroupOf K) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have heφ : ∀ k : ↥K, eφ (QuotientGroup.mk k) = φ k := fun _ => rfl
  have hS : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (ZMod p) (by omega)
  have hR : ∀ (r : G) (hr : r ∈ R), ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ Q := by
    intro r hr
    have hrK := hRK hr
    have hrQ : r ∈ Subgroup.normalizer (Q : Set G) :=
      SecD.normalizer_le_normalizer_oTwoTwoPrime K hrK
    let c := conjAct K ⟨r, hrK⟩
    have hc : ∀ k : ↥K, ((c k : ↥K) : G) = r * k * r⁻¹ := fun k =>
      Subgroup.normalizerMonoidHom_apply_apply_coe K (Subgroup.inclusion le_rfl ⟨r, hrK⟩) k
    have hcN : (Q.subgroupOf K).map (c : ↥K →* ↥K) = Q.subgroupOf K := by
      ext k
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨k', hk', hkk'⟩
        rw [Subgroup.mem_subgroupOf] at hk' ⊢
        rw [← hkk']
        change ((c k' : ↥K) : G) ∈ Q
        rw [hc]
        exact (Subgroup.mem_normalizer_iff.mp hrQ _).mp hk'
      · intro hk
        refine ⟨c.symm k, ?_, by change c (c.symm k) = k; rw [MulEquiv.apply_symm_apply]⟩
        rw [Subgroup.mem_subgroupOf] at hk ⊢
        have h1 : ((c (c.symm k) : ↥K) : G) = r * (c.symm k : G) * r⁻¹ := hc _
        rw [MulEquiv.apply_symm_apply] at h1
        have h2 : ((c.symm k : ↥K) : G) = r⁻¹ * k * r := by rw [h1]; group
        rw [h2]
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrQ) _).mp hk
        simpa using this
    let β : MulAut (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      MulAut.congr eφ (QuotientGroup.congr _ _ c hcN)
    have hβ : ∀ k : ↥K, β (φ k) = φ (c k) := fun k => by
      change eφ (QuotientGroup.congr _ _ c hcN (eφ.symm (φ k))) = φ (c k)
      rw [← heφ k, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk, heφ]
    let βb : MulAut (PSL2 (ZMod p)) :=
      QuotientGroup.congr _ _ β (Subgroup.map_center_eq β)
    have hβb : βb = 1 := by
      refine eq_one_of_fix hp hp5' hZp hB ?_
      rintro _ ⟨l, rfl⟩
      rw [hψ]
      change QuotientGroup.congr _ _ β (Subgroup.map_center_eq β) (QuotientGroup.mk _) = _
      rw [QuotientGroup.congr_mk, hβ]
      have hcl := hRL₁ (Subgroup.commutator_mem_commutator hr l.2)
      rw [commutatorElement_def] at hcl
      have hclL : r * (l : G) * r⁻¹ * (l : G)⁻¹ ∈ L₁ := Subgroup.map_subtype_le _ hcl
      have e1 : c ⟨l, hL₁K l.2⟩ =
          (⟨r * (l : G) * r⁻¹ * (l : G)⁻¹, hL₁K hclL⟩ : ↥K) * ⟨l, hL₁K l.2⟩ := by
        apply Subtype.ext
        rw [hc]
        simp
      rw [e1, map_mul, QuotientGroup.mk_mul]
      have h1 : (QuotientGroup.mk (φ ⟨r * (l : G) * r⁻¹ * (l : G)⁻¹, hL₁K hclL⟩) :
          PSL2 (ZMod p)) = 1 := hO _ hcl
      rw [h1, one_mul]
      rfl
    have hβ1 : β = 1 := by
      refine eq_one_of_mul_inv_mem_center β fun x => ?_
      have h1 : βb (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [hβb]; rfl
      change QuotientGroup.congr _ _ β (Subgroup.map_center_eq β) (QuotientGroup.mk x) = _ at h1
      rw [QuotientGroup.congr_mk, QuotientGroup.eq] at h1
      have h3 : x⁻¹ * β x ∈ Subgroup.center _ := by
        have := (Subgroup.center _).inv_mem h1
        simpa using this
      have h4 := Subgroup.mem_center_iff.mp h3 x
      have e3 : β x * x⁻¹ = x⁻¹ * β x := by
        calc β x * x⁻¹ = x * (x⁻¹ * β x) * x⁻¹ := by group
          _ = (x⁻¹ * β x) * x * x⁻¹ := by rw [h4]
          _ = x⁻¹ * β x := by group
      rw [e3]
      exact h3
    intro k hk
    have h1 : φ (c ⟨k, hk⟩) = φ ⟨k, hk⟩ := by rw [← hβ, hβ1, MulAut.one_apply]
    have h2 : c ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [hφk, Subgroup.mem_subgroupOf] at h2
    simpa [hc] using h2
  rw [Subgroup.commutator_le]
  intro r hr k hk
  rw [commutatorElement_def]
  exact hR r hr k hk

end CFSG.Quasithin.Vol2.Ch11.SecE
