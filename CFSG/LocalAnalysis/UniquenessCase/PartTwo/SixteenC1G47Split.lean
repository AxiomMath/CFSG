module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private lemma map_self_of_mapsTo {F : Type*} [Group F] [Finite F] (e : MulAut F)
    (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) : H.map (e : F →* F) = H := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact he y hy
  · exact (Subgroup.card_map_of_injective (f := (e : F →* F)) e.injective).ge

private noncomputable def restrictMulAut {F : Type*} [Group F] [Finite F] (e : MulAut F)
    (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) : MulAut H :=
  (e.subgroupMap H).trans (MulEquiv.subgroupCongr (map_self_of_mapsTo e H he))

@[simp]
private lemma restrictMulAut_apply {F : Type*} [Group F] [Finite F] (e : MulAut F)
    (H : Subgroup F) (he : ∀ x ∈ H, e x ∈ H) (x : H) :
    ((restrictMulAut e H he x : H) : F) = e x := by
  simp [restrictMulAut]

theorem s16c1_G47_split {Hs F : Type} [Group Hs] [Finite Hs] [Group F] [Finite F] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {S Z : Subgroup Hs} (hS : IsPGroup q S) (hZS : Z ≤ S)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Z)
    (hnc : ¬ ∃ s ∈ S, S ≤ Z ⊔ Subgroup.zpowers s) (hF : ∀ e : F, e * e = 1)
    (ρ : Hs →* MulAut F) (F₁ : Subgroup F) (hF₁ : ∀ s ∈ S, ∀ f ∈ F₁, ρ s f ∈ F₁)
    (hZ : ∀ c ∈ Z, ∀ f ∈ F₁, ρ c f = f)
    (hker : ∀ s ∈ S, (∀ f ∈ F₁, ρ s f = f) → s ∈ Z) :
    Subgroup.closure {f : F | f ∈ F₁ ∧ ∃ s ∈ S, s ∉ Z ∧ ρ s f = f} = F₁ := by
  classical
  let φ : ↥S →* MulAut ↥F₁ :=
    { toFun := fun s => restrictMulAut (ρ (s : Hs)) F₁ (hF₁ (s : Hs) s.2)
      map_one' := by
        ext x
        simp [restrictMulAut]
      map_mul' := by
        intro s t
        ext x
        simp [restrictMulAut, MulAut.mul_apply, map_mul] }
  let A : Subgroup (MulAut ↥F₁) := φ.range
  have hφ_apply : ∀ (s : ↥S) (x : ↥F₁), ((φ s) x : F) = ρ (s : Hs) x := by
    intro s x
    change ((restrictMulAut (ρ (s : Hs)) F₁ (hF₁ (s : Hs) s.2)) x : F) = ρ (s : Hs) x
    simp
  have hφZ : ∀ s : ↥S, (s : Hs) ∈ Z → φ s = 1 := by
    intro s hs
    ext x
    rw [hφ_apply s x]
    simpa using hZ (s : Hs) hs (x : F) x.2
  have hcommA : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← hs, ← ht, ← map_mul, ← map_mul]
    have hmemS : s.1 * t.1 * s.1⁻¹ * t.1⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem s.2 t.2) (S.inv_mem s.2)) (S.inv_mem t.2)
    have hz : φ ⟨s.1 * t.1 * s.1⁻¹ * t.1⁻¹, hmemS⟩ = 1 :=
      hφZ _ (hcomm s.1 s.2 t.1 t.2)
    have hst : s * t = ⟨s.1 * t.1 * s.1⁻¹ * t.1⁻¹, hmemS⟩ * (t * s) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    calc φ (s * t) = φ (⟨s.1 * t.1 * s.1⁻¹ * t.1⁻¹, hmemS⟩ * (t * s)) := by rw [hst]
      _ = φ ⟨s.1 * t.1 * s.1⁻¹ * t.1⁻¹, hmemS⟩ * φ (t * s) := map_mul φ _ _
      _ = φ (t * s) := by rw [hz, one_mul]
  haveI : IsMulCommutative ↥A := IsMulCommutative.of_comm hcommA
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  haveI : Fact (IsPGroup q ↥A) :=
    ⟨by simpa [A] using hS.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF₁two : IsPGroup 2 ↥F₁ := fun g => ⟨1, by
    have hg : g * g = 1 := Subtype.ext (hF (g : F))
    simpa [pow_two] using hg⟩
  have hcop : Nat.Coprime q (Nat.card ↥F₁) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hF₁two
    rw [hn]
    exact (Nat.coprime_primes hq Nat.prime_two).2 hq2 |>.pow_right n
  have hncycA : ¬ IsCyclic ↥A := by
    intro hcyc
    obtain ⟨a₀, ha₀⟩ := hcyc.exists_generator
    obtain ⟨s₀, hs₀⟩ := MonoidHom.mem_range.mp a₀.2
    refine hnc ⟨s₀.1, s₀.2, ?_⟩
    intro t ht
    have htA : φ ⟨t, ht⟩ ∈ A := ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha₀ ⟨φ ⟨t, ht⟩, htA⟩)
    have hpow : φ (s₀ ^ n) = φ ⟨t, ht⟩ := by
      have h1 : a₀.1 ^ n = (φ ⟨t, ht⟩ : MulAut ↥F₁) := by
        simpa using congrArg Subtype.val hn
      rw [← hs₀] at h1
      rwa [← map_zpow] at h1
    let u : ↥S := ⟨t, ht⟩ * s₀ ^ (-n)
    have hφu : φ u = 1 := by
      have h2 : φ (s₀ ^ (-n)) = (φ ⟨t, ht⟩)⁻¹ := by
        rw [map_zpow, zpow_neg, ← map_zpow, hpow]
      change φ (⟨t, ht⟩ * s₀ ^ (-n)) = 1
      rw [map_mul, h2, mul_inv_cancel]
    have hkeru : u.1 ∈ Z := by
      apply hker u.1 u.2
      intro f hf
      have hfix : (φ u) ⟨f, hf⟩ = ⟨f, hf⟩ := by rw [hφu]; rfl
      have hcoe : ((φ u) ⟨f, hf⟩ : F) = ρ (u : Hs) f := hφ_apply u ⟨f, hf⟩
      have := congrArg Subtype.val hfix
      rw [hcoe] at this
      simpa using this
    have ht_eq : t = u.1 * s₀.1 ^ n := by
      have hu : u.1 = t * s₀.1 ^ (-n) := rfl
      rw [hu]
      group
    rw [ht_eq]
    exact Subgroup.mul_mem_sup hkeru (Subgroup.zpow_mem_zpowers s₀.1 n)
  haveI : Fact q.Prime := ⟨hq⟩
  have htop := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := ↥F₁) (A := ↥A) q hcop hncycA
  let G₀ : Subgroup F := Subgroup.closure {f : F | f ∈ F₁ ∧ ∃ s ∈ S, s ∉ Z ∧ ρ s f = f}
  have hle : G₀ ≤ F₁ := (Subgroup.closure_le (K := F₁)).mpr fun f hf => hf.1
  have hge : F₁ ≤ G₀ := by
    have hsub :
        (⨆ (a : ↥A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥F₁) ≤
          G₀.comap F₁.subtype := by
      refine iSup₂_le fun a ha => ?_
      intro x hx
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp a.2
      have hsZ : s.1 ∉ Z := by
        intro hsZmem
        exact ha (Subtype.ext (hs.symm.trans (hφZ s hsZmem)))
      have hfix : ρ s.1 (x : F) = (x : F) := by
        have h1 : ((⟨a, Subgroup.mem_zpowers a⟩ : ↥(Subgroup.zpowers a)) • x : ↥F₁) = x :=
          (FixedPoints.mem_subgroup _ _ x).mp hx ⟨a, Subgroup.mem_zpowers a⟩
        have h3 : (a • x : ↥F₁) = x := by simpa only [Subgroup.smul_def] using h1
        have h2 : (a.1 x : F) = (x : F) := by
          simpa [Subgroup.smul_def, MulAut.smul_def] using congrArg Subtype.val h3
        rw [← hs] at h2
        rw [hφ_apply s x] at h2
        exact h2
      exact Subgroup.subset_closure ⟨x.2, ⟨s.1, s.2, hsZ, hfix⟩⟩
    intro g hg
    have hmem : (⟨g, hg⟩ : ↥F₁) ∈ G₀.comap F₁.subtype := by
      apply hsub
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  exact le_antisymm hle hge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
