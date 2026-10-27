module

public import CFSG.Quasithin.MS93.ML3Rec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix ML3
open scoped commutatorElement

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]

namespace ML3

theorem exists_quotient_action
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V)
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z)
    (hker : ∀ l : ↥K, α l = 1 → ∀ v ∈ V, v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z) :
    ∃ (Q : Type) (_ : CommGroup Q) (π : ↥V →* Q) (ρ : SL3 F →* MulAut Q),
      Function.Surjective π ∧ (∀ v : ↥V, π v = 1 ↔ (v : G) ∈ Z) ∧
      ∀ (l : ↥K) (v : ↥V), ρ (toSL3 α l) (π v) = π (conjOn hKV l v) := by
  have hN : (Z.subgroupOf V).Normal := ⟨fun z hz v => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have h := hVc v v.2 z (hZV hz)
    have he : ((v * z * v⁻¹ : ↥V) : G) = ⁅(v : G), (z : G)⁆ * z := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [he]
    exact Z.mul_mem h hz⟩
  let Q := ↥V ⧸ Z.subgroupOf V
  let _ : CommGroup Q :=
    { (QuotientGroup.Quotient.group (Z.subgroupOf V)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h := hVc _ (V.inv_mem b.2) _ (V.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥V) : G) =
                ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [he]
            exact h }
  have hmap : ∀ l : ↥K, (Z.subgroupOf V).map (conjOn hKV l : ↥V →* ↥V) = Z.subgroupOf V := by
    intro l
    have hle : ∀ l : ↥K, (Z.subgroupOf V).map (conjOn hKV l : ↥V →* ↥V) ≤ Z.subgroupOf V := by
      rintro l _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_subgroupOf]
      show ((conjOn hKV l z : ↥V) : G) ∈ Z
      rw [coe_conjOn_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hKZ l.2) z).mp hz
    refine le_antisymm (hle l) fun z hz => ?_
    refine ⟨conjOn hKV l⁻¹ z, ?_, ?_⟩
    · exact hle l⁻¹ ⟨z, hz, rfl⟩
    · change conjOn hKV l (conjOn hKV l⁻¹ z) = z
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  let act : ↥K →* MulAut Q :=
    { toFun := fun l => QuotientGroup.congr (Z.subgroupOf V) (Z.subgroupOf V) (conjOn hKV l)
        (hmap l)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H v =>
          simp only [QuotientGroup.congr_mk, map_one, MulAut.one_apply]
      map_mul' := fun l l' => by
        ext q
        induction q using QuotientGroup.induction_on with
        | H v =>
          simp only [QuotientGroup.congr_mk, map_mul, MulAut.mul_apply] }
  have hact : ∀ (l : ↥K) (v : ↥V), act l (QuotientGroup.mk v) =
      QuotientGroup.mk (conjOn hKV l v) := fun l v => rfl
  have hkerle : (toSL3 α).ker ≤ act.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have hl' : α l = 1 := by
      have := congrArg (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F) hl
      simpa [toSL3] using this
    ext q
    induction q using QuotientGroup.induction_on with
    | H v =>
      rw [hact, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h := hker l hl' v v.2
      have he : (((conjOn hKV l v)⁻¹ * v : ↥V) : G) =
          ((v : G)⁻¹ * ((l : G) * v * (l : G)⁻¹))⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply]
        group
      rw [he]
      exact Z.inv_mem h
  let ρ : SL3 F →* MulAut Q :=
    (QuotientGroup.lift (toSL3 α).ker act hkerle).comp
      (QuotientGroup.quotientKerEquivOfSurjective (toSL3 α) (toSL3_surjective hα)).symm.toMonoidHom
  have hρ : ∀ l : ↥K, ρ (toSL3 α l) = act l := by
    intro l
    have h : (QuotientGroup.quotientKerEquivOfSurjective (toSL3 α) (toSL3_surjective hα)).symm
        (toSL3 α l) = (l : ↥K ⧸ (toSL3 α).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
  refine ⟨Q, inferInstance, QuotientGroup.mk' (Z.subgroupOf V), ρ,
    QuotientGroup.mk'_surjective _, fun v => ?_, fun l v => ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hact]

end ML3

section Bridge

variable [Finite F] [CharP F 2] {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

namespace ML3

theorem isSumOfNaturalModulesVia_of_vecStab_aux (σ : SL3 F →* SL3 F) (hσ : ∀ g, σ (σ g) = g)
    (dual : Bool) (hmat : ∀ g, ((σ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) = natAct dual g)
    (hα : Function.Surjective α)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V)
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z)
    (hker : ∀ l : ↥K, α l = 1 → ∀ v ∈ V, v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z)
    {w : G} (hwV : w ∈ V) (hwZ : w ∉ Z)
    (hw : ∀ l : ↥K, σ (toSL3 α l) ∈ (ptLevi : Subgroup (SL3 F)) →
      w⁻¹ * ((l : G) * w * (l : G)⁻¹) ∈ Z)
    (hquad : ∀ l l' : ↥K, σ (toSL3 α l) ∈ rootGroup 0 1 → σ (toSL3 α l') ∈ rootGroup 0 1 →
      ∀ v ∈ V, ((l : G) * v * (l : G)⁻¹ * v⁻¹)⁻¹ *
        ((l' : G) * ((l : G) * v * (l : G)⁻¹ * v⁻¹) * (l' : G)⁻¹) ∈ Z)
    (hfix : ∀ v ∈ V, (∀ l : ↥K, σ (toSL3 α l) ∈ (lnLevi : Subgroup (SL3 F)) →
      v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z) → v ∈ Z)
    (hgen : V = Subgroup.closure {u | ∃ l : ↥K, (l : G) * w * (l : G)⁻¹ = u} ⊔ Z) :
    IsSumOfNaturalModulesVia K V Z α dual 1 := by
  obtain ⟨Q, _, π, ρ, hπs, hπk, hπρ⟩ := exists_quotient_action hα hKV hZV hKZ hVc hker
  have hπeq : ∀ v v' : ↥V, π v = π v' ↔ ((v : G))⁻¹ * v' ∈ Z := fun v v' => by
    have := hπk (v⁻¹ * v')
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    simpa using this
  have hsurjσ : ∀ g : SL3 F, ∃ l : ↥K, σ (toSL3 α l) = g := fun g => by
    obtain ⟨l, hl⟩ := toSL3_surjective hα (σ g)
    exact ⟨l, by rw [hl, hσ]⟩
  have hconj : ∀ (l : ↥K) (v : ↥V), ρ (σ (σ (toSL3 α l))) (π v) = π (conjOn hKV l v) :=
    fun l v => by rw [hσ, hπρ]
  set wb := π ⟨w, hwV⟩ with hwb
  have hw1 : wb ≠ 1 := fun h => hwZ ((hπk ⟨w, hwV⟩).mp h)
  have hw' : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), (ρ.comp σ) g wb = wb := by
    intro g hg
    obtain ⟨l, rfl⟩ := hsurjσ g
    rw [MonoidHom.comp_apply, hconj, hwb, hπeq]
    have h := Z.inv_mem (hw l hg)
    rw [coe_conjOn_apply]
    convert h using 1
    group
  have hquad' : ∀ a ∈ rootGroup 0 1, ∀ a' ∈ rootGroup 0 1, ∀ q : Q,
      (ρ.comp σ) a' ((ρ.comp σ) a q * q⁻¹) = (ρ.comp σ) a q * q⁻¹ := by
    intro a ha a' ha' q
    obtain ⟨l, rfl⟩ := hsurjσ a
    obtain ⟨l', rfl⟩ := hsurjσ a'
    obtain ⟨v, rfl⟩ := hπs q
    simp only [MonoidHom.comp_apply]
    rw [hconj, ← map_inv, ← map_mul, hconj, hπeq]
    have hc : (((conjOn hKV l v * v⁻¹ : ↥V)) : G) = (l : G) * v * (l : G)⁻¹ * (v : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOn_apply]
    have hc' : ((conjOn hKV l' (conjOn hKV l v * v⁻¹) : ↥V) : G) =
        (l' : G) * ((l : G) * v * (l : G)⁻¹ * (v : G)⁻¹) * (l' : G)⁻¹ := by
      rw [coe_conjOn_apply, hc]
    rw [hc, hc']
    have := Z.inv_mem (hquad l l' ha ha' v v.2)
    rwa [_root_.mul_inv_rev, inv_inv] at this
  have hfix' : ∀ q : Q, (∀ g ∈ (lnLevi : Subgroup (SL3 F)), (ρ.comp σ) g q = q) → q = 1 := by
    intro q hq
    obtain ⟨v, rfl⟩ := hπs q
    rw [hπk]
    apply hfix v v.2
    intro l hl
    have h := hq _ hl
    rw [MonoidHom.comp_apply, hconj, hπeq, coe_conjOn_apply] at h
    have := Z.inv_mem h
    convert this using 1
    group
  have hgen' : Subgroup.closure (Set.range fun g : SL3 F => (ρ.comp σ) g wb) = ⊤ := by
    set H := (Subgroup.closure (Set.range fun g : SL3 F => (ρ.comp σ) g wb)).comap π with hH
    have hHV : ∀ x ∈ V, x ∈ H.map V.subtype := by
      intro x hx
      rw [hgen] at hx
      refine (sup_le ?_ ?_ : Subgroup.closure {u | ∃ l : ↥K, (l : G) * w * (l : G)⁻¹ = u} ⊔ Z ≤
        H.map V.subtype) hx
      · rw [Subgroup.closure_le]
        rintro _ ⟨l, rfl⟩
        have hmem : (l : G) * w * (l : G)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hKV l.2) w).mp hwV
        refine ⟨⟨_, hmem⟩, ?_, rfl⟩
        rw [hH, SetLike.mem_coe, Subgroup.mem_comap]
        apply Subgroup.subset_closure
        refine ⟨σ (toSL3 α l), ?_⟩
        simp only [MonoidHom.comp_apply]
        rw [hconj]
        rfl
      · intro z hz
        refine ⟨⟨z, hZV hz⟩, ?_, rfl⟩
        rw [hH, SetLike.mem_coe, Subgroup.mem_comap, (hπk _).mpr hz]
        exact Subgroup.one_mem _
    rw [eq_top_iff]
    intro q _
    obtain ⟨v, rfl⟩ := hπs q
    obtain ⟨v', hv', hvv'⟩ := hHV v v.2
    have : v' = v := Subtype.ext hvv'
    rw [← this]
    exact hv'
  obtain ⟨β, hβ, -⟩ := exists_natEquiv_of_vecStab (ρ.comp σ) wb hw1 hw' hquad' hfix' hgen'
  let e1 : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))
  refine ⟨hKV, hZV, e1.symm.toMonoidHom.comp (β.toMonoidHom.comp π),
    e1.symm.surjective.comp (β.surjective.comp hπs), ?_, ?_⟩
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hπk]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · intro a u v huv i
    have hv : v = conjOn hKV a u := Subtype.ext (by rw [coe_conjOn_apply]; exact huv)
    have h := hβ (σ (toSL3 α a)) (π u)
    rw [MonoidHom.comp_apply, hconj, ← hv, hmat] at h
    rw [moduleAct_eq_natAct]
    change Multiplicative.toAdd (β (π v)) = natAct dual (toSL3 α a) *ᵥ
      Multiplicative.toAdd (β (π u))
    exact h

end ML3

theorem isSumOfNaturalModulesVia_dual_of_vecStab (hα : Function.Surjective α)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ V)
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (hVc : ∀ v ∈ V, ∀ w ∈ V, ⁅v, w⁆ ∈ Z)
    (hker : ∀ l : ↥K, α l = 1 → ∀ v ∈ V, v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z)
    {w : G} (hwV : w ∈ V) (hwZ : w ∉ Z)
    (hw : ∀ l : ↥K, transposeInv (toSL3 α l) ∈ (ptLevi : Subgroup (SL3 F)) →
      w⁻¹ * ((l : G) * w * (l : G)⁻¹) ∈ Z)
    (hquad : ∀ l l' : ↥K, transposeInv (toSL3 α l) ∈ rootGroup 0 1 →
      transposeInv (toSL3 α l') ∈ rootGroup 0 1 →
      ∀ v ∈ V, ((l : G) * v * (l : G)⁻¹ * v⁻¹)⁻¹ *
        ((l' : G) * ((l : G) * v * (l : G)⁻¹ * v⁻¹) * (l' : G)⁻¹) ∈ Z)
    (hfix : ∀ v ∈ V, (∀ l : ↥K, transposeInv (toSL3 α l) ∈ (lnLevi : Subgroup (SL3 F)) →
      v⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ Z) → v ∈ Z)
    (hgen : V = Subgroup.closure {u | ∃ l : ↥K, (l : G) * w * (l : G)⁻¹ = u} ⊔ Z) :
    IsSumOfNaturalModulesVia K V Z α true 1 :=
  isSumOfNaturalModulesVia_of_vecStab_aux transposeInv transposeInv_transposeInv true
    (fun g => by rw [coe_transposeInv, natAct_true]) hα hKV hZV hKZ hVc hker hwV hwZ hw hquad
    hfix hgen

end Bridge

end CFSG.Quasithin.MS93
