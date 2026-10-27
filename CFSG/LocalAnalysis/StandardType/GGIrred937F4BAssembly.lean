module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BDescent
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BSplit
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BFrames
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BUnitary
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNF4Two

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Group

theorem isComponentOf_comap_of_normalized {H G : Type} [Group H] [Group G] (ψ : H →* G)
    (hψ : Function.Injective ψ) (C : Subgroup H) (P : Subgroup G) (hPC : P ≤ C.map ψ)
    (hnorm : ∀ c ∈ C, ∀ u ∈ P, ψ c * u * (ψ c)⁻¹ ∈ P) (hq : CFSG.IsQuasisimple ↥P) :
    CFSG.Assembly.IsComponentOf (P.comap ψ) C := by
  have hle : P.comap ψ ≤ C := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hPC hx
    have : c = x := hψ hcx
    exact this ▸ hc
  refine ⟨hle, ?_, ?_⟩
  · refine CFSG.Assembly.IsSubnormal.step hle ?_ (CFSG.Assembly.IsSubnormal.refl C)
    refine ⟨fun n hn g => ?_⟩
    have hn' : ψ n.1 ∈ P := hn
    change ψ (g.1 * n.1 * g.1⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hnorm g.1 g.2 _ hn'
  · let f : ↥(P.comap ψ) →* ↥P :=
      (ψ.comp (P.comap ψ).subtype).codRestrict P (fun x => x.2)
    have hbij : Function.Bijective f := by
      refine ⟨fun x y hxy => Subtype.ext (hψ (congrArg Subtype.val hxy)), fun y => ?_⟩
      obtain ⟨c, -, hc⟩ := hPC y.2
      exact ⟨⟨c, by rw [Subgroup.mem_comap, hc]; exact y.2⟩, Subtype.ext hc⟩
    exact ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1).1
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.ofBijective f hbij).symm hq)

theorem ne_of_isComponentOf_of_commute {G : Type} [Group G] {J₁ J₂ K : Subgroup G}
    (h : CFSG.Assembly.IsComponentOf J₁ K) (hc : ∀ x ∈ J₁, ∀ y ∈ J₂, x * y = y * x) :
    J₁ ≠ J₂ := by
  intro heq
  subst heq
  obtain ⟨-, -, -, hsimple⟩ := h
  have hcenter : Subgroup.center J₁ = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2 z.1 z.2)
  have hsub : Subsingleton (↥J₁ ⧸ Subgroup.center ↥J₁) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, hcenter]
    trivial
  haveI := hsimple.toNontrivial
  exact not_subsingleton _ hsub

theorem isElemAbelian_comap_of_le_range {H G : Type} [Group H] [Group G] (ψ : H →* G)
    (hψ : Function.Injective ψ) {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    (hEψ : E ≤ ψ.range) :
    IsElemAbelian p (E.comap ψ) ∧ Nat.card ↥(E.comap ψ) = Nat.card ↥E := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hψ
    have := hcomm.is_comm.comm (⟨ψ a, a.2⟩ : ↥E) ⟨ψ b, b.2⟩
    have h2 := congrArg Subtype.val this
    simpa using h2
  · apply hψ
    rw [map_pow, map_one]
    exact hexp (ψ x) hx
  · refine Nat.card_congr (Equiv.ofBijective (fun x : ↥(E.comap ψ) => (⟨ψ x, x.2⟩ : ↥E))
      ⟨fun x y hxy => Subtype.ext (hψ (congrArg Subtype.val hxy)), fun y => ?_⟩)
    obtain ⟨h, hh⟩ := hEψ y.2
    exact ⟨⟨h, by rw [Subgroup.mem_comap, hh]; exact y.2⟩, Subtype.ext hh⟩

end Group

section Factors

theorem f4_a2a2_two_unitary_factors
    {K : Type} [Field K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f)
    (h3q : 3 ∣ Nat.card K + 1) (hq2 : 2 < Nat.card K) (w₀ : WeylGroup Tag.F4)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ) (ha : ∀ i, a i ^ 3 = 1)
    (h12 : (rootCharKernel (τ := Tag.F4) a).ncard = 12)
    (Z : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)))
    (hZ : Z = toralCentralizer Tag.F4 (AlgebraicClosure K) a ⊓
      langFixed (AlgebraicClosure K) f w₀) :
    ∃ P₁ P₂ E₁ E₂ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)),
      P₁ ≤ Z ∧ P₂ ≤ Z ∧
      (∀ z ∈ Z, ∀ u ∈ P₁, z * u * z⁻¹ ∈ P₁) ∧ (∀ z ∈ Z, ∀ u ∈ P₂, z * u * z⁻¹ ∈ P₂) ∧
      CFSG.IsQuasisimple ↥P₁ ∧ CFSG.IsQuasisimple ↥P₂ ∧
      (∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) ∧
      E₁ ≤ P₁ ∧ E₂ ≤ P₂ ∧ IsElemAbelian 3 E₁ ∧ IsElemAbelian 3 E₂ ∧
      Nat.card ↥E₁ = 9 ∧ Nat.card ↥E₂ = 9 := by
  obtain ⟨α, β, α', β', h₁, h₂, horth, hker⟩ := f4_a2a2_kernel_split (AlgebraicClosure K) a ha h12
  obtain ⟨hM, hcomm, hN₁, hN₂⟩ := f4_a2a2_group_split (AlgebraicClosure K) a ha h₁ h₂ horth hker
  obtain ⟨-, hqs₁⟩ := a2FixedGroup_finite_quasisimple hq hq2 w₀ hw₀ h₁
  obtain ⟨-, hqs₂⟩ := a2FixedGroup_finite_quasisimple hq hq2 w₀ hw₀ h₂
  obtain ⟨E₁, hE₁, hab₁, hc₁⟩ := a2FixedGroup_contains_elemAbelian_nine hq h3q w₀ hw₀ h₁
  obtain ⟨E₂, hE₂, hab₂, hc₂⟩ := a2FixedGroup_contains_elemAbelian_nine hq h3q w₀ hw₀ h₂
  have hY₁M : rootSpan Tag.F4 (AlgebraicClosure K) (a2Roots α β) ≤
      toralCentralizer Tag.F4 (AlgebraicClosure K) a := by
    rw [hM]; exact le_sup_left.trans le_sup_right
  have hY₂M : rootSpan Tag.F4 (AlgebraicClosure K) (a2Roots α' β') ≤
      toralCentralizer Tag.F4 (AlgebraicClosure K) a := by
    rw [hM]; exact le_sup_right.trans le_sup_right
  refine ⟨a2FixedGroup (AlgebraicClosure K) f w₀ α β, a2FixedGroup (AlgebraicClosure K) f w₀ α' β',
    E₁, E₂, ?_, ?_, ?_, ?_, hqs₁, hqs₂, ?_, hE₁, hE₂, hab₁, hab₂, hc₁, hc₂⟩
  · rw [hZ]; exact inf_le_inf_right _ hY₁M
  · rw [hZ]; exact inf_le_inf_right _ hY₂M
  · intro z hz u hu
    rw [hZ] at hz
    exact ⟨hN₁ z hz.1 u hu.1, (langFixed (AlgebraicClosure K) f w₀).mul_mem
      ((langFixed (AlgebraicClosure K) f w₀).mul_mem hz.2 hu.2)
      ((langFixed (AlgebraicClosure K) f w₀).inv_mem hz.2)⟩
  · intro z hz u hu
    rw [hZ] at hz
    exact ⟨hN₂ z hz.1 u hu.1, (langFixed (AlgebraicClosure K) f w₀).mul_mem
      ((langFixed (AlgebraicClosure K) f w₀).mul_mem hz.2 hu.2)
      ((langFixed (AlgebraicClosure K) f w₀).inv_mem hz.2)⟩
  · intro x hx y hy
    exact hcomm x hx.1 y hy.1

end Factors

theorem f4ThreeA2A2TwoComponents_holds :
    F4ThreeA2A2TwoComponents:= by
  intro K _ _ _ h3 hq2 e g hg a ha h12 hga
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hf : 1 ≤ (n : ℕ) := n.pos
  obtain ⟨w₀, hw₀⟩ := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.exists_weyl_neg_F4
  obtain ⟨g', hg', hdesc⟩ := exists_map_ggFix_langEmbedding hf hq h3 w₀ hw₀ e hg a ha hga
  have hinj : Function.Injective (langEmbedding g') := langEmbedding_injective g'
  obtain ⟨P₁, P₂, E₁, E₂, hP₁Z, hP₂Z, hN₁, hN₂, hq₁, hq₂', hcomm, hE₁P, hE₂P, hE₁ab, hE₂ab,
    hE₁c, hE₂c⟩ :=
    f4_a2a2_two_unitary_factors hq h3 hq2 w₀ hw₀ a ha h12
      ((ggFix (MulAut.conj e)).map (langEmbedding g')) hdesc
  have hJ₁ := isComponentOf_comap_of_normalized (langEmbedding g') hinj
    (ggFix (MulAut.conj e)) P₁ hP₁Z
    (fun c hc u hu => hN₁ _ (Subgroup.mem_map_of_mem _ hc) u hu) hq₁
  have hJ₂ := isComponentOf_comap_of_normalized (langEmbedding g') hinj
    (ggFix (MulAut.conj e)) P₂ hP₂Z
    (fun c hc u hu => hN₂ _ (Subgroup.mem_map_of_mem _ hc) u hu) hq₂'
  have hZle : ((ggFix (MulAut.conj e)).map (langEmbedding g')) ≤ (langEmbedding g').range :=
    Subgroup.map_le_range _ _
  obtain ⟨hab₁, hc₁⟩ := isElemAbelian_comap_of_le_range (langEmbedding g') hinj hE₁ab
    (hE₁P.trans (hP₁Z.trans hZle))
  obtain ⟨hab₂, hc₂⟩ := isElemAbelian_comap_of_le_range (langEmbedding g') hinj hE₂ab
    (hE₂P.trans (hP₂Z.trans hZle))
  refine ⟨P₁.comap (langEmbedding g'), P₂.comap (langEmbedding g'), E₁.comap (langEmbedding g'),
    E₂.comap (langEmbedding g'), hJ₁, hJ₂, ?_, Subgroup.comap_mono hE₁P, Subgroup.comap_mono hE₂P,
    hab₁, hab₂, hc₁.trans hE₁c, hc₂.trans hE₂c⟩
  refine ne_of_isComponentOf_of_commute hJ₁ ?_
  intro x hx y hy
  apply hinj
  rw [map_mul, map_mul]
  exact hcomm _ hx _ hy

end Irred937

end CFSG.StandardType

end
