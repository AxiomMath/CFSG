module

public import CFSG.Quasithin.Vol2.Ch11SecA13Line

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

noncomputable def conjOn (V U : Subgroup G) (hUV : U ≤ V) (k : G)
    (hk : k ∈ Subgroup.normalizer (U : Set G)) (w : ↥V) : ↥V := by
  classical
  exact if hw : (w : G) ∈ U then ⟨k * w * k⁻¹, hUV ((Subgroup.mem_normalizer_iff.mp hk _).mp hw)⟩
    else w

omit [Finite G] in
theorem conjOn_coe {V U : Subgroup G} (hUV : U ≤ V) {k : G}
    (hk : k ∈ Subgroup.normalizer (U : Set G)) {w : ↥V} (hw : (w : G) ∈ U) :
    ((conjOn V U hUV k hk w : ↥V) : G) = k * w * k⁻¹ := by
  simp [conjOn, hw]

theorem centralizer_commS_of_perfect (hL3 : FactLineSL3) (hLp : FactLineSp4)
    (hLg : FactLineG2) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {U₂ : Subgroup G}
    (hU₂ : IsVi T L I n 2 U₂) {K : Subgroup G} (hKK : ⁅K, K⁆ = K)
    (hKN : K ≤ Subgroup.normalizer (U₂ : Set G))
    (hcomm : ∀ k ∈ K, ∀ l ∈ LOf L U₂, ∀ v ∈ U₂,
      k * (l * v * l⁻¹) * k⁻¹ = l * (k * v * k⁻¹) * l⁻¹) :
    ∀ k ∈ K, ∀ y : ↥(fsuV T I),
      y ∈ commS (perfectCore (autOn L (fsuV T I) ⊓ stabW (U₂.subgroupOf (fsuV T I))))
        (U₂.subgroupOf (fsuV T I)) → k * (y : G) * k⁻¹ = y := by
  have hUV := IsVi.le_fsuV hU₂
  set S₂ := perfectCore (autOn L (fsuV T I) ⊓ stabW (U₂.subgroupOf (fsuV T I)))
  have he := (lineFacts hL3 hLp hLg h1102 h hU₂).2.2.2.2
  have hS₂ : S₂ = autOn (LOf L U₂) (fsuV T I) := perfectCore_eq_autOn_lOf h hUV
  have hmaps : ∀ k (hk : k ∈ K), (∀ u ∈ U₂.subgroupOf (fsuV T I),
      conjOn (fsuV T I) U₂ hUV k (hKN hk) u ∈ U₂.subgroupOf (fsuV T I)) ∧
      (∀ u ∈ U₂.subgroupOf (fsuV T I), ∀ v ∈ U₂.subgroupOf (fsuV T I),
        conjOn (fsuV T I) U₂ hUV k (hKN hk) (u * v) =
          conjOn (fsuV T I) U₂ hUV k (hKN hk) u * conjOn (fsuV T I) U₂ hUV k (hKN hk) v) ∧
      (∀ s ∈ S₂, ∀ u ∈ U₂.subgroupOf (fsuV T I),
        conjOn (fsuV T I) U₂ hUV k (hKN hk) (s u) =
          s (conjOn (fsuV T I) U₂ hUV k (hKN hk) u)) := by
    intro k hk
    have hkN := hKN hk
    refine ⟨fun u hu => ?_, fun u hu v hv => ?_, fun s hs u hu => ?_⟩
    · show ((conjOn _ _ hUV k _ u : ↥(fsuV T I)) : G) ∈ U₂
      rw [conjOn_coe hUV _ hu]
      exact (Subgroup.mem_normalizer_iff.mp hkN _).mp hu
    · apply Subtype.ext
      have huv : ((u * v : ↥(fsuV T I)) : G) ∈ U₂ := U₂.mul_mem hu hv
      rw [conjOn_coe hUV _ huv, Subgroup.coe_mul, Subgroup.coe_mul, conjOn_coe hUV _ hu,
        conjOn_coe hUV _ hv]
      group
    · rw [hS₂] at hs
      obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hs
      have hlU : l ∈ Subgroup.normalizer (U₂ : Set G) :=
        ((iInf_le (derivedSeriesOf _) 0).trans inf_le_right) hl
      have hsu : ((conjV (fsuV T I) l hlV u : ↥(fsuV T I)) : G) ∈ U₂ := by
        rw [conjV_apply_coe]
        exact (Subgroup.mem_normalizer_iff.mp hlU _).mp hu
      have hku : ((conjOn _ _ hUV k (hKN hk) u : ↥(fsuV T I)) : G) ∈ U₂ := by
        rw [conjOn_coe hUV _ hu]
        exact (Subgroup.mem_normalizer_iff.mp hkN _).mp hu
      apply Subtype.ext
      rw [conjOn_coe hUV _ hsu, conjV_apply_coe, conjV_apply_coe, conjOn_coe hUV _ hu]
      exact hcomm k hk l hl u hu
  set Y := (commS S₂ (U₂.subgroupOf (fsuV T I))).map (fsuV T I).subtype
  have hYU : ∀ y ∈ commS S₂ (U₂.subgroupOf (fsuV T I)), y ∈ U₂.subgroupOf (fsuV T I) := by
    intro y hy
    refine (Subgroup.closure_le _).mpr ?_ hy
    rintro _ ⟨s, hs, u, hu, rfl⟩
    have hs' : s ∈ stabW (U₂.subgroupOf (fsuV T I)) :=
      ((iInf_le (derivedSeriesOf _) 0).trans inf_le_right) hs
    exact Subgroup.mul_mem _ ((mem_stabW.mp hs' u).mp hu) (Subgroup.inv_mem _ hu)
  have hcK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ y ∈ commS S₂ (U₂.subgroupOf (fsuV T I)),
      k₁ * (k₂ * (y : G) * k₂⁻¹) * k₁⁻¹ = k₂ * (k₁ * (y : G) * k₁⁻¹) * k₂⁻¹ := by
    intro k₁ hk₁ k₂ hk₂ y hy
    obtain ⟨m₁, a₁, c₁⟩ := hmaps k₁ hk₁
    obtain ⟨m₂, a₂, c₂⟩ := hmaps k₂ hk₂
    have := he _ _ m₁ m₂ a₁ a₂ c₁ c₂ y hy
    have e := congrArg Subtype.val this
    have hyU : (y : G) ∈ U₂ := hYU y hy
    have hy₁ : ((conjOn _ _ hUV k₁ (hKN hk₁) y : ↥(fsuV T I)) : G) ∈ U₂ := m₁ y (hYU y hy)
    have hy₂ : ((conjOn _ _ hUV k₂ (hKN hk₂) y : ↥(fsuV T I)) : G) ∈ U₂ := m₂ y (hYU y hy)
    rw [conjOn_coe hUV _ hy₂, conjOn_coe hUV _ hy₁, conjOn_coe hUV _ hyU,
      conjOn_coe hUV _ hyU] at e
    exact e
  have hD : ⁅K, K⁆ ≤ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := hcK k₁⁻¹ (K.inv_mem hk₁) k₂⁻¹ (K.inv_mem hk₂) y hy
    simp only [inv_inv] at this
    simp only [Subgroup.coe_subtype, commutatorElement_def]
    calc (y : G) * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)
        = k₁ * k₂ * (k₂⁻¹ * k₁⁻¹ * (y : G) * k₁ * k₂) * k₁⁻¹ * k₂⁻¹ := by group
      _ = k₁ * k₂ * (k₁⁻¹ * k₂⁻¹ * (y : G) * k₂ * k₁) * k₁⁻¹ * k₂⁻¹ := by
          congr 3
          calc k₂⁻¹ * k₁⁻¹ * (y : G) * k₁ * k₂ = k₂⁻¹ * (k₁⁻¹ * (y : G) * k₁) * k₂ := by group
            _ = k₁⁻¹ * (k₂⁻¹ * (y : G) * k₂) * k₁ := this.symm
            _ = k₁⁻¹ * k₂⁻¹ * (y : G) * k₂ * k₁ := by group
      _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ * (y : G) := by group
  intro k hk y hy
  have hkY := Subgroup.mem_centralizer_iff.mp (hD (hKK.symm ▸ hk)) (y : G) ⟨y, hy, rfl⟩
  calc k * (y : G) * k⁻¹ = (y : G) * k * k⁻¹ := by rw [hkY]
    _ = y := by group

end CFSG.Quasithin.Vol2.Ch11.SecA
