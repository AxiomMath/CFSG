module

public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwGen
import CFSG.LieType.Chevalley.ProductInjectivity
import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section TwShort

private theorem ggRhoRho (γ : Fin (Tag.rank .E6) → ℤ) : rho (rho γ) = γ := by
  ext j
  fin_cases j <;> rfl

private theorem ggHeightRho (γ : Fin (Tag.rank .E6) → ℤ) : height (rho γ) = height γ := by
  rw [height, height, rho, permLattice]
  exact Equiv.sum_comp rhoPerm.symm γ

private theorem ggPinnedXListInjNeg
    {R : Type} [CommRing R]
    (L : List (Fin (Tag.rank .E6) → ℤ)) (hnd : L.Nodup)
    (hL : ∀ γ ∈ L, IsRoot .E6 γ ∧ height γ < 0)
    (c c' : (Fin (Tag.rank .E6) → ℤ) → R)
    (heq : (L.map fun γ => pinnedX .E6 R γ (c γ)).prod =
      (L.map fun γ => pinnedX .E6 R γ (c' γ)).prod) :
    ∀ γ ∈ L, c γ = c' γ := by
  have h := congrArg (fun g : (Module.End R (RootModule .E6 R))ˣ =>
    (g : Module.End R (RootModule .E6 R))) heq
  rw [coe_list_prod_pinnedX c L (fun γ hγ => (hL γ hγ).1),
    coe_list_prod_pinnedX c' L (fun γ hγ => (hL γ hγ).1)] at h
  have key := RootOperatorFamily.prod_eltOr_injective_of_ring (rootOperatorFamily .E6)
    (φ := AddMonoidHom.mk' (fun v : Fin (Tag.rank .E6) → ℤ => -height v)
      (fun u v => by simp only [height, Pi.add_apply, Finset.sum_add_distrib]; ring))
    L hnd (fun γ hγ => ⟨(hL γ hγ).1, by have := (hL γ hγ).2; show 0 < -height γ; omega⟩) _ _ h
  intro γ hγ
  have h1 := congrArg (((rootOperatorFamily .E6).pinnedFamilySign γ : R) * ·) (key γ hγ)
  simp only [← mul_assoc, (rootOperatorFamily .E6).pinnedFamilySign_mul_self, one_mul] at h1
  exact h1

private theorem ggPinnedXPairInjPos
    {R : Type} [CommRing R]
    {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α ≠ β)
    (hpα : 0 < height α) (hpβ : 0 < height β) {c₁ c₂ e₁ e₂ : R}
    (h : pinnedX .E6 R α c₁ * pinnedX .E6 R β c₂ =
      pinnedX .E6 R α e₁ * pinnedX .E6 R β e₂) : c₁ = e₁ ∧ c₂ = e₂ := by
  let L : List (Fin (Tag.rank .E6) → ℤ) := [α, β]
  have hnd : L.Nodup := by simp [L, hne]
  have hL : ∀ γ ∈ L, IsRoot .E6 γ ∧ 0 < height γ := by
    intro γ hγ
    simp only [L, List.mem_cons, List.mem_nil_iff, or_false] at hγ
    rcases hγ with rfl | rfl
    · exact ⟨hα, hpα⟩
    · exact ⟨hβ, hpβ⟩
  have hc : (L.map fun γ => pinnedX .E6 R γ (if γ = α then c₁ else c₂)).prod =
      pinnedX .E6 R α c₁ * pinnedX .E6 R β c₂ := by
    simp [L, Ne.symm hne]
  have he : (L.map fun γ => pinnedX .E6 R γ (if γ = α then e₁ else e₂)).prod =
      pinnedX .E6 R α e₁ * pinnedX .E6 R β e₂ := by
    simp [L, Ne.symm hne]
  have hmap : (L.map fun γ => pinnedX .E6 R γ (if γ = α then c₁ else c₂)).prod =
      (L.map fun γ => pinnedX .E6 R γ (if γ = α then e₁ else e₂)).prod := by
    rw [hc, he]; exact h
  have hkey := pinnedX_list_prod_injective L hnd hL
    (fun γ => if γ = α then c₁ else c₂) (fun γ => if γ = α then e₁ else e₂) hmap
  exact ⟨by simpa using hkey α (by simp [L]),
    by simpa only [if_neg (Ne.symm hne)] using hkey β (by simp [L])⟩

private theorem ggPinnedXPairInjNeg
    {R : Type} [CommRing R]
    {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α ≠ β)
    (hnα : height α < 0) (hnβ : height β < 0) {c₁ c₂ e₁ e₂ : R}
    (h : pinnedX .E6 R α c₁ * pinnedX .E6 R β c₂ =
      pinnedX .E6 R α e₁ * pinnedX .E6 R β e₂) : c₁ = e₁ ∧ c₂ = e₂ := by
  let L : List (Fin (Tag.rank .E6) → ℤ) := [α, β]
  have hnd : L.Nodup := by simp [L, hne]
  have hL : ∀ γ ∈ L, IsRoot .E6 γ ∧ height γ < 0 := by
    intro γ hγ
    simp only [L, List.mem_cons, List.mem_nil_iff, or_false] at hγ
    rcases hγ with rfl | rfl
    · exact ⟨hα, hnα⟩
    · exact ⟨hβ, hnβ⟩
  have hc : (L.map fun γ => pinnedX .E6 R γ (if γ = α then c₁ else c₂)).prod =
      pinnedX .E6 R α c₁ * pinnedX .E6 R β c₂ := by
    simp [L, Ne.symm hne]
  have he : (L.map fun γ => pinnedX .E6 R γ (if γ = α then e₁ else e₂)).prod =
      pinnedX .E6 R α e₁ * pinnedX .E6 R β e₂ := by
    simp [L, Ne.symm hne]
  have hmap : (L.map fun γ => pinnedX .E6 R γ (if γ = α then c₁ else c₂)).prod =
      (L.map fun γ => pinnedX .E6 R γ (if γ = α then e₁ else e₂)).prod := by
    rw [hc, he]; exact h
  have hkey := ggPinnedXListInjNeg L hnd hL
    (fun γ => if γ = α then c₁ else c₂) (fun γ => if γ = α then e₁ else e₂) hmap
  exact ⟨by simpa using hkey α (by simp [L]),
    by simpa only [if_neg (Ne.symm hne)] using hkey β (by simp [L])⟩

theorem ggPinnedXPairInj
    {R : Type} [CommRing R]
    {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α ≠ β)
    (hsign : (0 < height α ∧ 0 < height β) ∨ (height α < 0 ∧ height β < 0))
    {c₁ c₂ e₁ e₂ : R}
    (h : pinnedX .E6 R α c₁ * pinnedX .E6 R β c₂ =
      pinnedX .E6 R α e₁ * pinnedX .E6 R β e₂) : c₁ = e₁ ∧ c₂ = e₂ := by
  rcases hsign with ⟨hpα, hpβ⟩ | ⟨hnα, hnβ⟩
  · exact ggPinnedXPairInjPos hα hβ hne hpα hpβ h
  · exact ggPinnedXPairInjNeg hα hβ hne hnα hnβ h

theorem ggCommuteRoot
    {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hρ : rho a ≠ a) (hsum : ¬ IsRoot .E6 (a + rho a)) (hzero : a + rho a ≠ 0) :
    ∀ x ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a,
      ∀ z ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a),
        Commute x z := by
  have hne' : a ≠ -rho a := fun h => hzero (eq_neg_iff_add_eq_zero.mp h)
  exact (simply_laced_root_commutator_unit .E6 (Or.inr (Or.inl rfl)) ha (isRoot_rho ha)
    (Ne.symm hρ) hne').2 hsum GGL

private theorem ggDecompPair
    {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hρ : rho a ≠ a) (hsum : ¬ IsRoot .E6 (a + rho a)) (hzero : a + rho a ≠ 0)
    {y : ModGL (langTag .twistedE6) GGL}
    (hy : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a ⊔
      CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a)) :
    ∃ d₁ d₂ : GGL, y = pinnedX (langTag .twistedE6) GGL a d₁ *
      pinnedX (langTag .twistedE6) GGL (rho a) d₂ := by
  have hcommroot := ggCommuteRoot ha hρ hsum hzero
  let H : Subgroup (ModGL (langTag .twistedE6) GGL) :=
    CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a
  let K : Subgroup (ModGL (langTag .twistedE6) GGL) :=
    CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a)
  let P : Subgroup (ModGL (langTag .twistedE6) GGL) :=
    { carrier := {x | ∃ u ∈ H, ∃ v ∈ K, u * v = x}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro x x' ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
        refine ⟨u * u', H.mul_mem hu hu', v * v', K.mul_mem hv hv', ?_⟩
        have hvu : v * u' = u' * v := (hcommroot u' hu' v hv).eq.symm
        calc (u * u') * (v * v') = u * (u' * v) * v' := by group
          _ = u * (v * u') * v' := by rw [hvu]
          _ = (u * v) * (u' * v') := by group
      inv_mem' := by
        rintro x ⟨u, hu, v, hv, rfl⟩
        refine ⟨u⁻¹, H.inv_mem hu, v⁻¹, K.inv_mem hv, ?_⟩
        rw [mul_inv_rev]
        exact (hcommroot u hu v hv).inv_inv.eq }
  have hle : H ⊔ K ≤ P :=
    sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩)
  obtain ⟨u, hu, v, hv, huv⟩ := hle hy
  obtain ⟨d₁, hd₁⟩ := (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL)).1 hu
  obtain ⟨d₂, hd₂⟩ := (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL)).1 hv
  exact ⟨d₁, d₂, by rw [← huv, hd₁, hd₂]⟩

private theorem ggPermLatticeRho (γ : Fin (langTag .twistedE6).rank → ℤ) :
    permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) γ = rho γ := by
  ext j
  fin_cases j <;> rfl

private theorem ggPhiPinnedX_a
    (f : ℕ) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (d : GGL) :
    ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a d) =
      pinnedX (langTag .twistedE6) GGL (rho a) (d ^ 2 ^ f) := by
  rw [ggPhi_pinnedX_twistedE6 f (γ := a) ha, ggPermLatticeRho a]

private theorem ggPhiPinnedX_rho
    (f : ℕ) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (d : GGL) :
    ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL (rho a) d) =
      pinnedX (langTag .twistedE6) GGL a (d ^ 2 ^ f) := by
  rw [ggPhi_pinnedX_twistedE6 f (γ := rho a) (isRoot_rho ha), ggPermLatticeRho (rho a),
    ggRhoRho]

private theorem ggFrobPair
    (f : ℕ) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (d₁ d₂ : GGL) :
    ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a d₁ *
        pinnedX (langTag .twistedE6) GGL (rho a) d₂) =
      pinnedX (langTag .twistedE6) GGL (rho a) (d₁ ^ 2 ^ f) *
        pinnedX (langTag .twistedE6) GGL a (d₂ ^ 2 ^ f) := by
  rw [map_mul, ggPhiPinnedX_a f ha d₁, ggPhiPinnedX_rho f ha d₂]

theorem ggTwDescent_short_param
    (f : ℕ) (hf : 1 ≤ f) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hρ : rho a ≠ a) (hsum : ¬ IsRoot .E6 (a + rho a)) (hzero : a + rho a ≠ 0)
    {y : ModGL (langTag .twistedE6) GGL}
    (hy : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a ⊔
      CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a))
    (hfix : ggPhi .twistedE6 f y = y) :
    ∃ c : GaloisField 2 (2 * f),
      pinnedX (langTag .twistedE6) GGL a (ggRatEmb (2 * f) c) *
        pinnedX (langTag .twistedE6) GGL (rho a) (ggRatEmb (2 * f) (frobQ 2 f c)) = y := by
  classical
  have hheight : height (rho a) = height a := ggHeightRho a
  have hsign : (0 < height a ∧ 0 < height (rho a)) ∨
      (height a < 0 ∧ height (rho a) < 0) := by
    rcases IsRoot.height_pos_or_neg ha with hp | hn
    · exact Or.inl ⟨hp, by rw [hheight]; exact hp⟩
    · exact Or.inr ⟨hn, by rw [hheight]; exact hn⟩
  have hcommroot := ggCommuteRoot ha hρ hsum hzero
  obtain ⟨d₁, d₂, hydecomp⟩ := ggDecompPair ha hρ hsum hzero hy
  have hFrob : ggPhi .twistedE6 f y =
      pinnedX (langTag .twistedE6) GGL (rho a) (d₁ ^ 2 ^ f) *
        pinnedX (langTag .twistedE6) GGL a (d₂ ^ 2 ^ f) := by
    have h := ggFrobPair f ha d₁ d₂
    rwa [← hydecomp] at h
  have heq1 : pinnedX (langTag .twistedE6) GGL (rho a) (d₁ ^ 2 ^ f) *
      pinnedX (langTag .twistedE6) GGL a (d₂ ^ 2 ^ f) =
      pinnedX (langTag .twistedE6) GGL a d₁ *
        pinnedX (langTag .twistedE6) GGL (rho a) d₂ := by
    rw [← hFrob, hfix, hydecomp]
  have heq2 : pinnedX (langTag .twistedE6) GGL a (d₂ ^ 2 ^ f) *
      pinnedX (langTag .twistedE6) GGL (rho a) (d₁ ^ 2 ^ f) =
      pinnedX (langTag .twistedE6) GGL a d₁ *
        pinnedX (langTag .twistedE6) GGL (rho a) d₂ := by
    rw [← heq1]
    exact (hcommroot (pinnedX (langTag .twistedE6) GGL a (d₂ ^ 2 ^ f))
      (Subgroup.subset_closure ⟨d₂ ^ 2 ^ f, rfl⟩)
      (pinnedX (langTag .twistedE6) GGL (rho a) (d₁ ^ 2 ^ f))
      (Subgroup.subset_closure ⟨d₁ ^ 2 ^ f, rfl⟩)).eq
  have hinj := ggPinnedXPairInj ha (isRoot_rho ha) (Ne.symm hρ) hsign heq2
  have hd1' : d₂ ^ 2 ^ f = d₁ := hinj.1
  have hd2' : d₁ ^ 2 ^ f = d₂ := hinj.2
  have hff : 2 ^ f * 2 ^ f = 2 ^ (2 * f) := by
    rw [← pow_add, show f + f = 2 * f by omega]
  have hpow : d₁ ^ 2 ^ (2 * f) = d₁ := by
    have h1 : d₁ ^ (2 ^ f * 2 ^ f) = d₁ := by rw [pow_mul, hd2', hd1']
    simpa [hff] using h1
  have hmem : d₁ ∈ Set.range (ggRatEmb (2 * f)) := by
    rw [ggRatEmb_range (f := 2 * f) (by omega : 1 ≤ 2 * f)]
    exact hpow
  obtain ⟨c, hc⟩ := hmem
  have hθc : ggRatEmb (2 * f) (frobQ 2 f c) = d₂ := by
    rw [frobQ_apply, map_pow, hc, hd2']
  refine ⟨c, ?_⟩
  rw [hc, hθc]
  exact hydecomp.symm

theorem ggTwDescent_short
    (f : ℕ) (hf : 1 ≤ f) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hρ : rho a ≠ a) (hsum : ¬ IsRoot .E6 (a + rho a)) (hzero : a + rho a ≠ 0)
    {y : ModGL (langTag .twistedE6) GGL}
    (hy : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a ⊔
      CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL (rho a))
    (hfix : ggPhi .twistedE6 f y = y) :
    ∃ g : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f))),
      g ∈ e6Data_valid.rootGroup (GaloisField 2 (2 * f)) a ⊔
          e6Data_valid.rootGroup (GaloisField 2 (2 * f)) (rho a) ∧
        sigma (GaloisField 2 (2 * f)) (frobQ 2 f) g = g ∧ ggTwPsi f g = y := by
  obtain ⟨c, hcy⟩ := ggTwDescent_short_param f hf ha hρ hsum hzero hy hfix
  have hcxm : Commute (e6Data_valid.xm (GaloisField 2 (2 * f)) a c)
      (e6Data_valid.xm (GaloisField 2 (2 * f)) (rho a) (frobQ 2 f c)) :=
    commutatorElement_eq_one_iff_commute.1
      ((e6Data_valid.commutator_xm (GaloisField 2 (2 * f)) ha (isRoot_rho ha) hzero).2
        hsum c (frobQ 2 f c))
  refine ⟨e6Data_valid.xm (GaloisField 2 (2 * f)) a c *
      e6Data_valid.xm (GaloisField 2 (2 * f)) (rho a) (frobQ 2 f c), ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem_sup (e6Data_valid.xm_mem_rootGroup (GaloisField 2 (2 * f)) a c)
      (e6Data_valid.xm_mem_rootGroup (GaloisField 2 (2 * f)) (rho a) (frobQ 2 f c))
  · rw [map_mul, ggTwSigma_xm f ha c, ggTwSigma_xm f (isRoot_rho ha) (frobQ 2 f c),
      ggRhoRho, frobQ_frobQ 2 f hf]
    exact hcxm.eq.symm
  · rw [map_mul, ggTwPsi_xm f ha c, ggTwPsi_xm f (isRoot_rho ha) (frobQ 2 f c)]
    exact hcy

end TwShort

end CFSG.StandardType.GGFinModel
