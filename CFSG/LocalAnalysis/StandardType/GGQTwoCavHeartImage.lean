module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBLemmas

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
  {Bs L : Subgroup G} {x : G}

omit [Fact p.Prime] in
theorem beta_image_inner_of_le_sup_zpowers
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : Bs ≤ L ⊔ Subgroup.zpowers x)
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) :
    (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range := by
  let H := ((MulAut.conj : R →* MulAut R).range.comap (ggLAut L θ)).map
    (Subgroup.normalizer (L : Set G)).subtype
  have hLH : L ≤ H := by
    intro l hl
    refine ⟨⟨l, Subgroup.le_normalizer hl⟩, ?_, rfl⟩
    exact ⟨θ ((⟨l, hl⟩ : L) : L ⧸ Subgroup.center L),
      (ggLAut_of_mem_conj θ ⟨l, hl⟩ _).symm⟩
  have hxH : x ∈ H := by
    refine ⟨⟨x, Subgroup.centralizer_le_normalizer (L : Set G) hxC⟩, ?_, rfl⟩
    change ggLAut L θ _ ∈ (MulAut.conj : R →* MulAut R).range
    rw [ggLAut_eq_one_of_mem_centralizer L θ hxC]
    exact Subgroup.one_mem _
  have hBsH : Bs ≤ H := hBs.trans (sup_le hLH (Subgroup.zpowers_le.mpr hxH))
  rintro _ ⟨b, rfl⟩
  obtain ⟨n, hn, heq⟩ := hBsH b.property
  have hn' : n = ⟨b, hN b.property⟩ := Subtype.ext heq
  change ggLAut L θ n ∈ (MulAut.conj : R →* MulAut R).range at hn
  simpa only [hn', ggBeta_eq] using hn

theorem GGQ2LDatum.coroot_mem (M : GGQ2LDatum p Bs L x) (hp2 : p ≠ 2)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (i : M.Λ) :
    ((Additive.toMul (M.model.symm (M.coroot i)) : Bs) : G) ∈ L := by
  apply ggCoroot_mem hp2 hN M.model (M.simple_apply i)
  · simp only [M.pairing, M.isCartan.1 i, Int.cast_ofNat]
  · rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩

theorem GGQ2LDatum.coSpan_le_ggLinImage (M : GGQ2LDatum p Bs L x) (hp2 : p ≠ 2)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    M.coSpan ≤ ggLinImage (p := p) M.model L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (mem_ggLinImage (p := p) M.model L _).mpr (M.coroot_mem hp2 hN i)

theorem GGQ2LDatum.bstar_le_sup_zpowers_of_heartShape (M : GGQ2LDatum p Bs L x)
    (hp2 : p ≠ 2) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h : M.HeartShape) :
    Bs ≤ L ⊔ Subgroup.zpowers x := by
  have hco := M.coSpan_le_ggLinImage hp2 hN
  have htop : M.coSpan ⊔ Submodule.span (ZMod p) {M.xV} = ⊤ := by
    rcases h with hB | hD
    · exact hB.2.2.2
    · rw [hD.2.2, top_sup_eq]
  have hco' : M.coSpan ≤ ggLinImage (p := p) M.model (L ⊔ Subgroup.zpowers x) :=
    hco.trans (ggLinImage_mono (p := p) M.model le_sup_left)
  have hx' : Submodule.span (ZMod p) {M.xV} ≤
      ggLinImage (p := p) M.model (L ⊔ Subgroup.zpowers x) := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact (ofMul_mem_ggLinImage (p := p) M.model _ ⟨x, M.hx⟩).mpr
      ((le_sup_right : Subgroup.zpowers x ≤ L ⊔ Subgroup.zpowers x)
        (Subgroup.mem_zpowers x))
  intro b hb
  apply (ofMul_mem_ggLinImage (p := p) M.model _ ⟨b, hb⟩).mp
  exact (htop ▸ (sup_le hco' hx')) Submodule.mem_top

theorem GGQ2LDatum.beta_image_inner_of_heartShape (M : GGQ2LDatum p Bs L x)
    (hp2 : p ≠ 2) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h : M.HeartShape)
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) :
    (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range :=
  beta_image_inner_of_le_sup_zpowers hN
    (M.bstar_le_sup_zpowers_of_heartShape hp2 hN h) hxC θ

end CFSG.StandardType

end
