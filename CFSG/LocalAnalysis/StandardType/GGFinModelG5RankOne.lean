module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LieType.Chevalley.E6GraphInvolutionForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsFour

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section RankOne

private noncomputable def g5_fixField (f : ℕ) : Subfield GGL :=
  RingHom.eqLocusField (ggFrobT f) (RingHom.id GGL)

private theorem g5_mem_fixField {f : ℕ} {x : GGL} :
    x ∈ g5_fixField f ↔ x ^ 2 ^ f = x := by
  simp [g5_fixField, RingHom.mem_eqLocusField, ggFrobT_apply]

private theorem g5_phi_pinnedX_fixed
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ)
    {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) (hfix : ggGraphLat t γ = γ)
    (c : GGL) :
    ggPhi t f (pinnedX (langTag t) GGL γ c) =
      pinnedX (langTag t) GGL γ (c ^ 2 ^ f) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ggPhi_pinnedX_untw (Or.inl rfl) f hγ c
  · exact ggPhi_pinnedX_untw (Or.inr (Or.inl rfl)) f hγ c
  · exact ggPhi_pinnedX_untw (Or.inr (Or.inr (Or.inl rfl))) f hγ c
  · exact ggPhi_pinnedX_untw (Or.inr (Or.inr (Or.inr rfl))) f hγ c
  · rw [ggPhi_pinnedX_twistedE6 f hγ c]
    exact congrArg (fun v : Fin (langTag .twistedE6).rank → ℤ =>
      pinnedX (langTag .twistedE6) GGL v (c ^ 2 ^ f)) hfix

private theorem g5_graphLat_neg (t : StatedLieTag) (γ : Fin (langTag t).rank → ℤ) :
    ggGraphLat t (-γ) = -(ggGraphLat t γ) := by
  cases t <;> rfl

private theorem g5_pinnedX_mem_fixGp
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ)
    {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) (hfix : ggGraphLat t γ = γ)
    (c : GGL) (hc : c ^ 2 ^ f = c) :
    pinnedX (langTag t) GGL γ c ∈ ggFixGp t f ⊓ rootSubgroup (langTag t) GGL γ := by
  refine ⟨⟨pinnedX_mem_adjointGroup γ c, ?_⟩, mem_rootSubgroup.mpr ⟨c, rfl⟩⟩
  show ggPhi t f (pinnedX (langTag t) GGL γ c) = pinnedX (langTag t) GGL γ c
  rw [g5_phi_pinnedX_fixed ht f hγ hfix c, hc]

private theorem g5_map_sl2Upper {L K : Type} [Field L] [Field K] (f : L →+* K) (c : L) :
    Matrix.SpecialLinearGroup.map f (CFSG.LocalAnalysis.ComponentInitial.sl2Upper L c) =
      uSL (f c) := by
  rw [show CFSG.LocalAnalysis.ComponentInitial.sl2Upper L c = uSL c from rfl]
  exact map_uSL f c

private theorem g5_map_sl2Lower {L K : Type} [Field L] [Field K] (f : L →+* K) (c : L) :
    Matrix.SpecialLinearGroup.map f (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      vSL (f c) := by
  rw [show CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c = vSL c from rfl]
  exact map_vSL f c

private theorem g5_ratSL2_le_range (f : ℕ) :
    ratSL2 f ≤
      (Matrix.SpecialLinearGroup.map (g5_fixField f).subtype).range := by
  intro A hA
  have hA' : Matrix.SpecialLinearGroup.map (ggFrobT f) A = A := hA
  have hentry : ∀ i j, ggFrobT f (A i j) = A i j := by
    intro i j
    have h := congrArg (fun B : SL2 GGL => (B : Matrix (Fin 2) (Fin 2) GGL) i j) hA'
    simpa using h
  set M : Matrix (Fin 2) (Fin 2) (g5_fixField f) :=
    fun i j => ⟨A i j, (g5_mem_fixField).mpr (hentry i j)⟩ with hM
  have hdet : M.det = 1 := by
    apply (g5_fixField f).subtype.injective
    rw [RingHom.map_det]
    have hmap : (g5_fixField f).subtype.mapMatrix M = (A : Matrix (Fin 2) (Fin 2) GGL) := by
      ext i j
      rfl
    rw [hmap, A.2]
    rfl
  refine MonoidHom.mem_range.mpr ⟨⟨M, hdet⟩, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

private theorem g5_range_map_le
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) (hfix : ggGraphLat t β = β) :
    (Matrix.SpecialLinearGroup.map (g5_fixField f).subtype).range ≤
      (ratRankOne t f β).comap (rootSL2 (langTag t) GGL β) := by
  have h2 : (2 : GGL) = 0 := CharTwo.two_eq_zero
  intro B hB
  obtain ⟨C, rfl⟩ := MonoidHom.mem_range.mp hB
  have hgen : Subgroup.closure
      (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (g5_fixField f)) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (g5_fixField f))) = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
  have hfixβ : ggGraphLat t (-β) = -β := by rw [g5_graphLat_neg, hfix]
  have hle : Subgroup.closure
      (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (g5_fixField f)) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (g5_fixField f))) ≤
      (ratRankOne t f β).comap
        ((rootSL2 (langTag t) GGL β).comp
          (Matrix.SpecialLinearGroup.map (g5_fixField f).subtype)) := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show rootSL2 (langTag t) GGL β
        (Matrix.SpecialLinearGroup.map (g5_fixField f).subtype
          (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (g5_fixField f) c)) ∈ ratRankOne t f β
      rw [g5_map_sl2Upper,
        CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2 β ((g5_fixField f).subtype c)]
      exact Subgroup.mem_sup_left (g5_pinnedX_mem_fixGp ht f hβ hfix ((g5_fixField f).subtype c)
        ((g5_mem_fixField).mp c.2))
    · show rootSL2 (langTag t) GGL β
        (Matrix.SpecialLinearGroup.map (g5_fixField f).subtype
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (g5_fixField f) c)) ∈ ratRankOne t f β
      rw [g5_map_sl2Lower,
        CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two h2 hβ ((g5_fixField f).subtype c)]
      exact Subgroup.mem_sup_right (g5_pinnedX_mem_fixGp ht f (IsRoot.neg hβ) hfixβ
        ((g5_fixField f).subtype c) ((g5_mem_fixField).mp c.2))
  exact hle (by rw [hgen]; exact Subgroup.mem_top C)

theorem ggG5_ratRankOne_eq
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) (hfix : ggGraphLat t β = β) :
    ratRankOne t f β = (ratSL2 f).map (rootSL2 (langTag t) GGL β) := by
  have h2 : (2 : GGL) = 0 := CharTwo.two_eq_zero
  have hfixβ : ggGraphLat t (-β) = -β := by rw [g5_graphLat_neg, hfix]
  refine le_antisymm ?_ ?_
  · rw [ratRankOne]
    refine sup_le ?_ ?_
    · rintro g ⟨hgFix, hgRoot⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hgRoot
      have hc : c ^ 2 ^ f = c := by
        have h : ggPhi t f (pinnedX (langTag t) GGL β c) = pinnedX (langTag t) GGL β c :=
          (Subgroup.mem_inf.mp hgFix).2
        rw [g5_phi_pinnedX_fixed ht f hβ hfix c] at h
        exact pinnedX_injective (langTag t) GGL β h
      exact Subgroup.mem_map.mpr ⟨uSL c, by
        show Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL c) = uSL c
        rw [map_uSL, ggFrobT_apply, hc],
        CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2 β c⟩
    · rintro g ⟨hgFix, hgRoot⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hgRoot
      have hc : c ^ 2 ^ f = c := by
        have h : ggPhi t f (pinnedX (langTag t) GGL (-β) c) =
            pinnedX (langTag t) GGL (-β) c := (Subgroup.mem_inf.mp hgFix).2
        rw [g5_phi_pinnedX_fixed ht f (IsRoot.neg hβ) hfixβ c] at h
        exact pinnedX_injective (langTag t) GGL (-β) h
      exact Subgroup.mem_map.mpr ⟨vSL c, by
        show Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL c) = vSL c
        rw [map_vSL, ggFrobT_apply, hc],
        CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two h2 hβ c⟩
  · calc (ratSL2 f).map (rootSL2 (langTag t) GGL β)
        ≤ ((Matrix.SpecialLinearGroup.map (g5_fixField f).subtype).range).map
            (rootSL2 (langTag t) GGL β) :=
          Subgroup.map_mono (g5_ratSL2_le_range f)
      _ ≤ ratRankOne t f β :=
          Subgroup.map_le_iff_le_comap.mpr (g5_range_map_le ht f hβ hfix)

private theorem g5_map_conj_fixGp {t : StatedLieTag} (f : ℕ)
    {n : ModGL (langTag t) GGL} (hn : n ∈ adjointGroup (langTag t) GGL)
    (hnΦ : ggPhi t f n = n) :
    (ggFixGp t f).map (MulAut.conj n).toMonoidHom = ggFixGp t f := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxA : x ∈ adjointGroup (langTag t) GGL := (Subgroup.mem_inf.mp hx).1
    have hxΦ : ggPhi t f x = x := (Subgroup.mem_inf.mp hx).2
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hn hxA) (inv_mem hn), ?_⟩
    show ggPhi t f (n * x * n⁻¹) = n * x * n⁻¹
    rw [map_mul, map_mul, map_inv, hnΦ, hxΦ]
  · intro y hy
    have hyA : y ∈ adjointGroup (langTag t) GGL := (Subgroup.mem_inf.mp hy).1
    have hyΦ : ggPhi t f y = y := (Subgroup.mem_inf.mp hy).2
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * y * n, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hn) hyA) hn, ?_⟩
      show ggPhi t f (n⁻¹ * y * n) = n⁻¹ * y * n
      rw [map_mul, map_mul, map_inv, hnΦ, hyΦ]
    · show n * (n⁻¹ * y * n) * n⁻¹ = y
      group

private theorem g5_map_conj_rootSubgroup
    {t : StatedLieTag} (f : ℕ)
    (u : WeylGroup (langTag t))
    (hu : ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
      canonicalRep (coxeterSystem (langTag t)) GGL u)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) :
    (rootSubgroup (langTag t) GGL β).map
        (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom =
      rootSubgroup (langTag t) GGL (u • β) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hx
    refine mem_rootSubgroup.mpr ⟨c, ?_⟩
    show pinnedX (langTag t) GGL (u • β) c =
      (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom
        (pinnedX (langTag t) GGL β c)
    exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.canonicalRep_conj_pinnedX_charTwo
      u hβ c).symm
  · intro y hy
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hy
    refine Subgroup.mem_map.mpr ⟨pinnedX (langTag t) GGL β c,
      mem_rootSubgroup.mpr ⟨c, rfl⟩, ?_⟩
    show (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom
        (pinnedX (langTag t) GGL β c) = pinnedX (langTag t) GGL (u • β) c
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.canonicalRep_conj_pinnedX_charTwo
      u hβ c

theorem ggG5_ratRankOne_conj
    {t : StatedLieTag} (ht : GGExcFive t) (f : ℕ)
    (u : WeylGroup (langTag t))
    (hu : ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
      canonicalRep (coxeterSystem (langTag t)) GGL u)
    {β : Fin (langTag t).rank → ℤ} (hβ : IsRoot (langTag t) β) :
    (ratRankOne t f β).map
        (MulAut.conj (canonicalRep (coxeterSystem (langTag t)) GGL u)).toMonoidHom =
      ratRankOne t f (u • β) := by
  rw [ratRankOne, ratRankOne, Subgroup.map_sup,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj
      (canonicalRep (coxeterSystem (langTag t)) GGL u)).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj
      (canonicalRep (coxeterSystem (langTag t)) GGL u)).injective,
    g5_map_conj_fixGp f (canonicalRep_mem_adjointGroup _ GGL u) hu,
    g5_map_conj_rootSubgroup f u hu hβ,
    g5_map_conj_rootSubgroup f u hu (IsRoot.neg hβ), smul_neg]

end RankOne

end CFSG.StandardType.GGFinModel.G5
