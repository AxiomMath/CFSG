module

public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBT

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
@[expose] def subfieldImage (k : Subfield K) : Subgroup (ModGL τ K) :=
  (adjointGroup τ k).map (baseChangeGL k.subtype)

theorem subfieldImage_le (k : Subfield K) : subfieldImage τ k ≤ adjointGroup τ K := by
  rintro _ ⟨g, hg, rfl⟩
  exact baseChangeGL_mem_adjointGroup k.subtype hg

theorem xUnit_mem_subfieldImage (k : Subfield K) (i : Fin τ.rank) {c : K} (hc : c ∈ k) :
    xUnit τ K i c ∈ subfieldImage τ k :=
  ⟨xUnit τ k i ⟨c, hc⟩, xUnit_mem_adjointGroup i _, baseChangeGL_xUnit _ i _⟩

theorem units_map_entrywiseHom_of_mem_subfieldImage {k : Subfield K} {β : K ≃+* K}
    (hβ : ∀ c ∈ k, β c = c) {g : ModGL τ K} (hg : g ∈ subfieldImage τ k) :
    Units.map (entrywiseHom β.toRingHom) g = g := by
  obtain ⟨g', -, rfl⟩ := hg
  have hcomp : β.toRingHom.comp k.subtype = k.subtype := RingHom.ext fun x => hβ x x.2
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]

@[expose] def fixingSubgroupEquivAlgEquiv (k : Subfield K) :
    fixingSubgroup (K ≃+* K) (k : Set K) ≃ (K ≃ₐ[k] K) where
  toFun β := AlgEquiv.ofRingEquiv (f := (β : K ≃+* K)) fun x => by
    have h := (mem_fixingSubgroup_iff _).1 β.2 x x.2
    rwa [RingAut.smul_def] at h
  invFun e := ⟨e.toRingEquiv, (mem_fixingSubgroup_iff _).2 fun y hy => by
    rw [RingAut.smul_def]
    exact e.commutes ⟨y, hy⟩⟩
  left_inv β := Subtype.ext (RingEquiv.ext fun _ => rfl)
  right_inv e := AlgEquiv.ext fun _ => rfl

theorem odd_F4_subfield_pointwise_automorphism_centralizer {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (k : Subfield K) :
    subfieldImage .F4 k ≤ adjointGroup .F4 K ∧
      fixingSubgroup (MulAut (adjointGroup .F4 K))
          (((subfieldImage .F4 k).subgroupOf (adjointGroup .F4 K) :
            Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
        (fixingSubgroup (K ≃+* K) (k : Set K)).map
          (entrywiseAdjointAutHom (τ := .F4)) ∧
      Function.Injective (entrywiseAdjointAutHom (τ := .F4) (K := K)) ∧
      IsCyclic (fixingSubgroup (K ≃+* K) (k : Set K)) ∧
      Nonempty (fixingSubgroup (K ≃+* K) (k : Set K) ≃ (K ≃ₐ[k] K)) ∧
      Nat.card (fixingSubgroup (K ≃+* K) (k : Set K)) = Module.finrank k K := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hrank : 0 < Tag.F4.rank := by decide
  set C := adjointGroup Tag.F4 K
  set J := subfieldImage Tag.F4 k
  have hJC : J ≤ C := subfieldImage_le k
  set ι : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  set ιk : ZMod ℓ →+* k := ZMod.castHom (dvd_refl ℓ) k
  have hιk : ι = k.subtype.comp ιk := RingHom.ext_zmod _ _
  have hHJ : ∀ g0 ∈ adjointGroup Tag.F4 (ZMod ℓ), baseChangeGL ι g0 ∈ J := fun g0 hg0 =>
    ⟨baseChangeGL ιk g0, baseChangeGL_mem_adjointGroup ιk hg0, by
      rw [baseChangeGL_baseChangeGL, ← hιk]⟩
  have hodd : Odd (Nat.card (ZMod ℓ)) := by
    rw [Nat.card_zmod]
    exact hℓ.odd_of_ne_two hℓ2
  have hfaith := (exceptional_Lang_finite_root_centralizer_faithfulness Tag.F4 (ZMod ℓ) hodd K
    ι).2.2.1
  obtain ⟨hNF, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK
    Tag.F4 (Or.inl rfl)
  obtain ⟨fr, -, -, htop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf
      hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, htop⟩
  refine ⟨hJC, le_antisymm (fun α hα => ?_) ?_, entrywiseAdjointAutHom_injective hrank,
    inferInstance, ⟨fixingSubgroupEquivAlgEquiv k⟩, ?_⟩
  ·
    have hfix : ∀ j : C, (j : ModGL Tag.F4 K) ∈ J → α j = j := fun j hj => by
      have h := (mem_fixingSubgroup_iff _).1 hα j (Subgroup.mem_subgroupOf.2 hj)
      rwa [MulAut.smul_def] at h
    obtain ⟨⟨g, β⟩, hgβ, -⟩ := hNF α
    simp only at hgβ
    have hg1 : g = 1 := by
      refine Subtype.ext (hfaith g g.2 fun h hh => ?_)
      obtain ⟨g0, hg0, rfl⟩ := hh
      have hhJ := hHJ g0 hg0
      have h1 := hfix ⟨_, hJC hhJ⟩ hhJ
      have h2 := hgβ ⟨_, hJC hhJ⟩
      rw [h1] at h2
      change baseChangeGL ι g0 = (g : ModGL Tag.F4 K) *
        Units.map (entrywiseHom β.toRingHom) (baseChangeGL ι g0) * (g : ModGL Tag.F4 K)⁻¹ at h2
      rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
        RingHom.ext_zmod (β.toRingHom.comp ι) ι] at h2
      rw [← mul_inv_eq_iff_eq_mul.1 h2.symm]
    subst hg1
    have hαβ : α = entrywiseAdjointAut Tag.F4 β :=
      MulEquiv.ext fun h => Subtype.ext (by
        rw [hgβ h, coe_entrywiseAdjointAut]
        simp)
    have hβk : β ∈ fixingSubgroup (K ≃+* K) (k : Set K) :=
      (mem_fixingSubgroup_iff _).2 fun c hc => by
        rw [RingAut.smul_def]
        have h1 := hfix (adjX Tag.F4 K ⟨0, hrank⟩ c) (xUnit_mem_subfieldImage k _ hc)
        rw [hαβ, FieldGraphFieldPointwise.entrywiseAdjointAut_adjX] at h1
        exact adjX_injective _ h1
    exact ⟨β, hβk, hαβ.symm⟩
  ·
    rintro _ ⟨β, hβ, rfl⟩
    refine (mem_fixingSubgroup_iff _).2 fun j hj => Subtype.ext ?_
    rw [MulAut.smul_def]
    change Units.map (entrywiseHom β.toRingHom) (j : ModGL Tag.F4 K) = j
    exact units_map_entrywiseHom_of_mem_subfieldImage (fun c hc => by
      have h := (mem_fixingSubgroup_iff _).1 hβ c hc
      rwa [RingAut.smul_def] at h) (Subgroup.mem_subgroupOf.1 hj)
  ·
    rw [Nat.card_congr (fixingSubgroupEquivAlgEquiv k), IsGalois.card_aut_eq_finrank]

end CFSG.RankThree.Chevalley
