module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.KFacts.KP2KleinOffender

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP2

open Equiv

variable {G : Type*} [Group G]

private noncomputable def conjM {R₁ R₂ : Subgroup G} [(R₂.subgroupOf R₁).Normal]
    (g : ↥(Subgroup.normalizer (R₁ : Set G) ⊓ Subgroup.normalizer (R₂ : Set G))) :
    MulAut (↥R₁ ⧸ R₂.subgroupOf R₁) :=
  QuotientGroup.congr (R₂.subgroupOf R₁) (R₂.subgroupOf R₁)
    (Subgroup.normalizerMonoidHom R₁ ⟨g.1, (Submonoid.mem_inf.mp g.2).1⟩) (by
      have hg₂ : (g : G) ∈ Subgroup.normalizer (R₂ : Set G) := (Submonoid.mem_inf.mp g.2).2
      have hg₁ : (g : G) ∈ Subgroup.normalizer (R₁ : Set G) := (Submonoid.mem_inf.mp g.2).1
      have hg₁' : (g : G)⁻¹ ∈ Subgroup.normalizer (R₁ : Set G) := inv_mem hg₁
      have hg₂' : (g : G)⁻¹ ∈ Subgroup.normalizer (R₂ : Set G) := inv_mem hg₂
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        change ((Subgroup.normalizerMonoidHom R₁ ⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩) y :
          G) ∈ R₂
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe R₁]
        exact (Subgroup.mem_normalizer_iff.mp hg₂ (y : G)).mp hy
      · intro hx
        let y : ↥R₁ := ⟨(g : G)⁻¹ * (x : G) * (g : G),
          by simpa only [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp hg₁' (x : G)).mp x.2⟩
        have hy : Subgroup.normalizerMonoidHom R₁ ⟨g.1, (Submonoid.mem_inf.mp g.2).1⟩ y = x := by
          apply Subtype.ext
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe R₁]
          simp only [y]
          group
        have hy₂ : y ∈ R₂.subgroupOf R₁ := by
          rw [Subgroup.mem_subgroupOf]
          simpa only [y, inv_inv] using
            (Subgroup.mem_normalizer_iff.mp hg₂' (x : G)).mp hx
        exact ⟨y, hy₂, hy⟩)

private lemma conjM_mk {R₁ R₂ : Subgroup G} [(R₂.subgroupOf R₁).Normal]
    (g : ↥(Subgroup.normalizer (R₁ : Set G) ⊓ Subgroup.normalizer (R₂ : Set G)))
    (r : ↥R₁) :
    conjM g (QuotientGroup.mk r) =
      QuotientGroup.mk (Subgroup.normalizerMonoidHom R₁ ⟨g.1, (Submonoid.mem_inf.mp g.2).1⟩ r) := by
  simp only [conjM, QuotientGroup.congr_mk]

private lemma conjM_mk_eq_mk_iff {R₁ R₂ : Subgroup G} [(R₂.subgroupOf R₁).Normal]
    (g : ↥(Subgroup.normalizer (R₁ : Set G) ⊓ Subgroup.normalizer (R₂ : Set G)))
    (r : ↥R₁) :
    conjM g (QuotientGroup.mk r) = QuotientGroup.mk r ↔
      (g : G) * (r : G) * (g : G)⁻¹ * (r : G)⁻¹ ∈ R₂ := by
  rw [conjM_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf,
    Subgroup.coe_div, Subgroup.normalizerMonoidHom_apply_apply_coe R₁, div_eq_mul_inv]

private noncomputable def conjMHom (R₁ R₂ : Subgroup G) [(R₂.subgroupOf R₁).Normal] :
    ↥(Subgroup.normalizer (R₁ : Set G) ⊓ Subgroup.normalizer (R₂ : Set G)) →*
      MulAut (↥R₁ ⧸ R₂.subgroupOf R₁) where
  toFun := conjM
  map_one' := by
    apply MulEquiv.ext
    intro m
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective m
    rw [conjM_mk, MulAut.one_apply]
    have h1 : (⟨((1 : ↥(Subgroup.normalizer (R₁ : Set G) ⊓
        Subgroup.normalizer (R₂ : Set G))) : G), (Subgroup.mem_inf.mp
        (1 : ↥(Subgroup.normalizer (R₁ : Set G) ⊓
          Subgroup.normalizer (R₂ : Set G))).2).1⟩ :
        ↥(Subgroup.normalizer (R₁ : Set G))) = 1 := by
      apply Subtype.ext
      rfl
    rw [h1, map_one, MulAut.one_apply]
  map_mul' := by
    intro g h
    apply MulEquiv.ext
    intro m
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective m
    rw [MulAut.mul_apply, conjM_mk, conjM_mk, conjM_mk]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.normalizerMonoidHom_apply_apply_coe R₁]
    group

theorem card_mul_card_lt_of_section [Finite G] {J R₁ R₂ F X : Subgroup G}
    (θ : ↥J →* alternatingGroup (Fin 7)) (hθ : Function.Surjective θ)
    (hR₁ : IsPGroup 2 R₁) (hR : R₂ < R₁) (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G))
    (hJ₁ : J ≤ Subgroup.normalizer (R₁ : Set G)) (hJ₂ : J ≤ Subgroup.normalizer (R₂ : Set G))
    (hker : ∀ j : ↥J, θ j = 1 → ∀ r ∈ R₁, (j : G) * r * (j : G)⁻¹ * r⁻¹ ∈ R₂)
    (hfix : ∀ r ∈ R₁, (∀ j ∈ J, j * r * j⁻¹ * r⁻¹ ∈ R₂) → r ∈ R₂)
    {t : G} (ht₁ : t ∈ Subgroup.normalizer (R₁ : Set G))
    (ht₂ : t ∈ Subgroup.normalizer (R₂ : Set G)) (htJ : t ∈ Subgroup.normalizer (J : Set G))
    {π : Equiv.Perm (Fin 7)} (hπ : π ∉ alternatingGroup (Fin 7))
    (htθ : ∀ j : ↥J, ((θ ⟨t * j * t⁻¹, (Subgroup.mem_normalizer_iff.mp htJ j).mp j.2⟩ :
        alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      π * (θ j : Equiv.Perm (Fin 7)) * π⁻¹)
    (hFJ : F ≤ J) (g : Equiv.Perm (Fin 7))
    (hFV : ∀ f (hf : f ∈ F), ((θ ⟨f, hFJ hf⟩ : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)) ∈ vTwo.map (MulAut.conj g).toMonoidHom)
    (hF : ∃ f, ∃ hf : f ∈ F, θ ⟨f, hFJ hf⟩ ≠ 1)
    (hX₂ : R₂ ≤ X) (hX₁ : X ≤ R₁) (hFX : ∀ x ∈ X, ∀ f ∈ F, f * x * f⁻¹ * x⁻¹ ∈ R₂) :
    Nat.card ((F.subgroupOf J).map θ) * Nat.card X < Nat.card R₁ := by
  letI hN : (R₂.subgroupOf R₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR.le).mpr hR₁₂
  haveI hNX : (R₂.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₂).mpr (hX₁.trans hR₁₂)
  let M := ↥R₁ ⧸ R₂.subgroupOf R₁
  haveI : Finite ↥R₁ := Subtype.finite
  haveI : Finite M := Quotient.finite _
  haveI : Finite ↥R₂ := Subtype.finite
  have hM : IsPGroup 2 M := hR₁.to_quotient (R₂.subgroupOf R₁)
  haveI hMnontriv : Nontrivial M := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    have hR₂eq : R₂ = R₁ := by
      ext r
      constructor
      · exact fun hr => hR.le hr
      · intro hr
        have : (⟨r, hr⟩ : ↥R₁) ∈ R₂.subgroupOf R₁ := by
          rw [htop]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
    exact (ne_of_lt hR) hR₂eq
  let e : ↥J →* ↥(Subgroup.normalizer (R₁ : Set G) ⊓
      Subgroup.normalizer (R₂ : Set G)) := Subgroup.inclusion (le_inf hJ₁ hJ₂)
  let κ : ↥J →* MulAut M := (conjMHom R₁ R₂).comp e
  let σ : MulAut M := conjMHom R₁ R₂ ⟨t, Submonoid.mem_inf.mpr ⟨ht₁, ht₂⟩⟩
  let ψ : ↥J →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp θ
  let FJ : Subgroup ↥J := F.subgroupOf J
  have hψ : ψ.range = alternatingGroup (Fin 7) := by
    rw [show ψ = (alternatingGroup (Fin 7)).subtype.comp θ from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hθ, Subgroup.map_top,
      Subgroup.range_subtype]
  have hkerκ : ψ.ker ≤ κ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hθx : θ x = 1 := Subtype.ext (by simpa [ψ] using hx)
    apply MulEquiv.ext
    intro m
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective m
    change conjM (e x) (QuotientGroup.mk r) = QuotientGroup.mk r
    exact (conjM_mk_eq_mk_iff (g := e x) r).mpr (hker x hθx (r : G) r.2)
  have hfixκ : ∀ m : M, (∀ x : ↥J, κ x m = m) → m = 1 := by
    intro m hm
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective m
    have hr : (r : G) ∈ R₂ := by
      apply hfix (r : G) r.2
      intro j hj
      have h := hm ⟨j, hj⟩
      exact (conjM_mk_eq_mk_iff (g := e ⟨j, hj⟩) r).mp h
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hr
  have hσ : ∀ x : ↥J, ∃ x', ψ x' = π * ψ x * π⁻¹ ∧ σ * κ x * σ⁻¹ = κ x' := by
    intro x
    refine ⟨⟨t * (x : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htJ x).mp x.2⟩, ?_, ?_⟩
    · simpa [ψ] using htθ x
    · have helem : (⟨t, Submonoid.mem_inf.mpr ⟨ht₁, ht₂⟩⟩ :
          ↥(Subgroup.normalizer (R₁ : Set G) ⊓ Subgroup.normalizer (R₂ : Set G))) * e x *
          (⟨t, Submonoid.mem_inf.mpr ⟨ht₁, ht₂⟩⟩ :
            ↥(Subgroup.normalizer (R₁ : Set G) ⊓ Subgroup.normalizer (R₂ : Set G)))⁻¹ =
          e ⟨t * (x : G) * t⁻¹,
            (Subgroup.mem_normalizer_iff.mp htJ x).mp x.2⟩ := by
        apply Subtype.ext
        simp only [e, Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv]
      change conjMHom R₁ R₂ ⟨t, Submonoid.mem_inf.mpr ⟨ht₁, ht₂⟩⟩ * conjMHom R₁ R₂ (e x) *
          (conjMHom R₁ R₂ ⟨t, Submonoid.mem_inf.mpr ⟨ht₁, ht₂⟩⟩)⁻¹ =
        conjMHom R₁ R₂ (e ⟨t * (x : G) * t⁻¹,
          (Subgroup.mem_normalizer_iff.mp htJ x).mp x.2⟩)
      rw [← map_mul, ← map_inv, ← map_mul, helem]
  have hFJne : FJ.map ψ ≠ ⊥ := by
    obtain ⟨f, hf, hfne⟩ := hF
    intro hbot
    have hmemFJ : (⟨f, hFJ hf⟩ : ↥J) ∈ FJ := by
      rw [Subgroup.mem_subgroupOf]
      exact hf
    have hmem : ψ ⟨f, hFJ hf⟩ ∈ FJ.map ψ :=
      Subgroup.mem_map_of_mem ψ hmemFJ
    rw [hbot] at hmem
    apply hfne
    have h1 : ψ ⟨f, hFJ hf⟩ = 1 := by simpa using hmem
    exact Subtype.ext (by simpa [ψ] using h1)
  have hFV' : FJ.map ψ ≤ vTwo.map (MulAut.conj g).toMonoidHom := by
    rintro y ⟨x, hx, rfl⟩
    exact hFV x.1 (Subgroup.mem_subgroupOf.mp hx)
  have hmain : Nat.card (FJ.map ψ) *
      Nat.card {m : M // ∀ x ∈ FJ, κ x m = m} < Nat.card M :=
    card_map_mul_card_fixed_lt hM κ ψ hψ hkerκ hfixκ σ hπ hσ hFJne g hFV'
  let φ : ↥X →* M := (QuotientGroup.mk' (R₂.subgroupOf R₁)).comp (Subgroup.inclusion hX₁)
  let Xbar : Subgroup M := φ.range
  have hkerφ : φ.ker = R₂.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker]
    change ((Subgroup.inclusion hX₁ x : ↥R₁) : ↥R₁ ⧸ R₂.subgroupOf R₁) = 1 ↔
      (x : G) ∈ R₂
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hcardX : Nat.card X = Nat.card Xbar * Nat.card R₂ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (R₂.subgroupOf X)]
    have hq : Nat.card (X ⧸ R₂.subgroupOf X) = Nat.card Xbar := by
      calc
        Nat.card (X ⧸ R₂.subgroupOf X) = Nat.card (X ⧸ φ.ker) := by rw [hkerφ]
        _ = Nat.card Xbar := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂).toEquiv]
  have hXbar_le : Nat.card Xbar ≤
      Nat.card {m : M // ∀ x ∈ FJ, κ x m = m} := by
    let f : Xbar → {m : M // ∀ x ∈ FJ, κ x m = m} := fun m =>
      ⟨m.1, by
        intro x hx
        obtain ⟨y, hy⟩ := m.2
        rw [← hy]
        change conjM (e x) (QuotientGroup.mk (Subgroup.inclusion hX₁ y)) =
          QuotientGroup.mk (Subgroup.inclusion hX₁ y)
        exact (conjM_mk_eq_mk_iff (g := e x) ⟨(y : G), hX₁ y.2⟩).mpr
          (hFX (y : G) y.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))⟩
    exact Nat.card_le_card_of_injective f
      (fun a b h => Subtype.ext (by
        show (a : M) = (b : M)
        simpa only [f] using congrArg Subtype.val h))
  have hcardF : Nat.card (FJ.map ψ) = Nat.card (FJ.map θ) := by
    rw [show FJ.map ψ = (FJ.map θ).map (alternatingGroup (Fin 7)).subtype from by
      rw [Subgroup.map_map]]
    exact Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective
  have hcardR₁ : Nat.card R₁ = Nat.card M * Nat.card R₂ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (R₂.subgroupOf R₁)]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.le).toEquiv
  have hmain' : Nat.card (FJ.map θ) *
      Nat.card {m : M // ∀ x ∈ FJ, κ x m = m} < Nat.card M := by
    simpa only [hcardF] using hmain
  calc
    Nat.card (FJ.map θ) * Nat.card X
        = Nat.card (FJ.map θ) * (Nat.card Xbar * Nat.card R₂) := by rw [hcardX]
    _ = (Nat.card (FJ.map θ) * Nat.card Xbar) * Nat.card R₂ := by ring
    _ ≤ (Nat.card (FJ.map θ) *
          Nat.card {m : M // ∀ x ∈ FJ, κ x m = m}) * Nat.card R₂ := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hXbar_le)
    _ < Nat.card M * Nat.card R₂ := by
        exact Nat.mul_lt_mul_of_pos_right hmain' (Nat.card_pos (α := R₂))
    _ = Nat.card R₁ := hcardR₁.symm

end CFSG.RankThree.PartTwo.KFacts.KP2
