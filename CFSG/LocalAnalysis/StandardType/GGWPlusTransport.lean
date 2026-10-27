module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem mulAut_conj_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem mulAut_congr_trans {A B C : Type*} [Group A] [Group B] [Group C]
    (θ : A ≃* B) (e : B ≃* C) (φ : MulAut A) :
    MulAut.congr (θ.trans e) φ = MulAut.congr e (MulAut.congr θ φ) := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]

private theorem range_conj_map_congr {R R' : Type*} [Group R] [Group R'] (e : R ≃* R') :
    (MulAut.conj : R →* MulAut R).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : R' →* MulAut R').range := by
  apply le_antisymm
  · rintro y ⟨z, ⟨r, rfl⟩, rfl⟩
    exact ⟨e r, (mulAut_conj_congr e r).symm⟩
  · rintro y ⟨r, rfl⟩
    exact ⟨MulAut.conj (e.symm r), ⟨e.symm r, rfl⟩, by
      simpa using mulAut_conj_congr e (e.symm r)⟩

private theorem map_centralizer_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (f : G ≃* G') (S : Subgroup G) :
    (Subgroup.centralizer (S : Set G)).map f.toMonoidHom =
      Subgroup.centralizer ((S.map f.toMonoidHom : Subgroup G') : Set G') := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro h ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hz s hs]
  · intro y hy
    rw [show y = f.toMonoidHom (f.symm y) from (f.apply_symm_apply y).symm,
      Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro s hs
    apply f.injective
    rw [map_mul, map_mul, f.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hy (f.toMonoidHom s) ⟨s, hs, rfl⟩

theorem ggWPlusTableB_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGWPlusTableB p R' I') : GGWPlusTableB p R I := by
  intro M _ _ L' E θ hE hpos hZ A M₁ E₁ h₀ hX hAN hpel hM₁E₁ hE₁A hAM₁ hAM₁N hAE₁N hEp
    hh₀ hhp hAE₁h
  let f : MulAut R ≃* MulAut R' := MulAut.congr e
  have hgg : ggLAut L' (θ.trans e) = f.toMonoidHom.comp (ggLAut L' θ) := by
    ext g x
    exact DFunLike.congr_fun
      (mulAut_congr_trans θ e (centerQuotAut L' (L'.normalizerMonoidHom g))) x
  have hInn : (MulAut.conj : R' →* MulAut R').range =
      ((MulAut.conj : R →* MulAut R).range).map f.toMonoidHom :=
    (range_conj_map_congr e).symm
  have himg : ggLAutImage L' (θ.trans e) E = (ggLAutImage L' θ E).map f.toMonoidHom := by
    simp only [ggLAutImage]
    rw [Subgroup.map_map, ← hgg]
  have hpos' : GGTableBPosition p L' E I' (θ.trans e) hE := by
    refine ⟨hpos.1, hpos.2.1, hpos.2.2.1, ?_,
      hpos.2.2.2.2.1, hpos.2.2.2.2.2.1, hpos.2.2.2.2.2.2⟩
    intro x
    rw [hgg]
    exact hI _ (hpos.2.2.2.1 x)
  have hX' : (MulAut.conj : R' →* MulAut R').range ⊓
      Subgroup.normalizer (ggLAutImage L' (θ.trans e) E) ≤ A.map f.toMonoidHom := by
    rw [hInn, himg, ← Subgroup.map_equiv_normalizer_eq (ggLAutImage L' θ E) f,
      ← Subgroup.map_inf ((MulAut.conj : R →* MulAut R).range)
        (Subgroup.normalizer (ggLAutImage L' θ E)) f.toMonoidHom f.injective]
    exact Subgroup.map_mono hX
  have hAN' : A.map f.toMonoidHom ≤
      Subgroup.normalizer (ggLAutImage L' (θ.trans e) E) := by
    rw [himg, ← Subgroup.map_equiv_normalizer_eq (ggLAutImage L' θ E) f]
    exact Subgroup.map_mono hAN
  have hmap : (MulAut.conj : R' →* MulAut R').range ⊔
      Subgroup.centralizer (ggLAutImage L' (θ.trans e) E) =
      ((MulAut.conj : R →* MulAut R).range ⊔
        Subgroup.centralizer (ggLAutImage L' θ E)).map f.toMonoidHom := by
    rw [Subgroup.map_sup, hInn, himg, map_centralizer_eq_of_mulEquiv f (ggLAutImage L' θ E)]
  have hpel' : ∀ a ∈ A.map f.toMonoidHom, (∃ k : ℕ, a ^ p ^ k = 1) →
      a ∈ (MulAut.conj : R' →* MulAut R').range ⊔
        Subgroup.centralizer (ggLAutImage L' (θ.trans e) E) := by
    rintro a' ⟨a, ha, rfl⟩ ⟨k, hk⟩
    have ha1 : a ^ p ^ k = 1 := f.injective (by simpa using hk)
    rw [hmap]
    exact (Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective).mpr (hpel a ha ⟨k, ha1⟩)
  have hM₁E₁' : M₁.map f.toMonoidHom ≤ E₁.map f.toMonoidHom := Subgroup.map_mono hM₁E₁
  have hE₁A' : E₁.map f.toMonoidHom ≤ A.map f.toMonoidHom := Subgroup.map_mono hE₁A
  have hAM₁' : A.map f.toMonoidHom ⊓
      Subgroup.centralizer (ggLAutImage L' (θ.trans e) E) ≤ M₁.map f.toMonoidHom := by
    rw [himg, ← map_centralizer_eq_of_mulEquiv f (ggLAutImage L' θ E),
      ← Subgroup.map_inf A (Subgroup.centralizer (ggLAutImage L' θ E)) f.toMonoidHom
        f.injective]
    exact Subgroup.map_mono hAM₁
  have hAM₁N' : A.map f.toMonoidHom ≤ Subgroup.normalizer (M₁.map f.toMonoidHom) := by
    rw [← Subgroup.map_equiv_normalizer_eq M₁ f]
    exact Subgroup.map_mono hAM₁N
  have hAE₁N' : A.map f.toMonoidHom ≤ Subgroup.normalizer (E₁.map f.toMonoidHom) := by
    rw [← Subgroup.map_equiv_normalizer_eq E₁ f]
    exact Subgroup.map_mono hAE₁N
  have hEp' : ∀ e' ∈ E₁.map f.toMonoidHom, ∃ k : ℕ, e' ^ p ^ k ∈ M₁.map f.toMonoidHom := by
    rintro e' ⟨e, he, rfl⟩
    obtain ⟨k, hk⟩ := hEp e he
    refine ⟨k, ?_⟩
    have : f (e ^ p ^ k) ∈ M₁.map f.toMonoidHom :=
      (Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective).mpr hk
    simpa using this
  have hh₀' : f h₀ ∈ A.map f.toMonoidHom :=
    (Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective).mpr hh₀
  have hhp' : (orderOf (f h₀)).Coprime p := by
    rw [MulEquiv.orderOf_eq]
    exact hhp
  have hAE₁h' : A.map f.toMonoidHom ≤ E₁.map f.toMonoidHom ⊔ Subgroup.zpowers (f h₀) := by
    change A.map f.toMonoidHom ≤ E₁.map f.toMonoidHom ⊔
      Subgroup.zpowers (f.toMonoidHom h₀)
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup]
    exact Subgroup.map_mono hAE₁h
  have key := h M L' E (θ.trans e) hE hpos' hZ (A.map f.toMonoidHom) (M₁.map f.toMonoidHom)
    (E₁.map f.toMonoidHom) (f h₀) hX' hAN' hpel' hM₁E₁' hE₁A' hAM₁' hAM₁N' hAE₁N' hEp' hh₀'
    hhp' hAE₁h'
  exact (Subgroup.map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp key

end CFSG.StandardType
