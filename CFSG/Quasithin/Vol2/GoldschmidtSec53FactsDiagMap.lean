module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiag
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMap
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.Sec53F.BA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Y Y' C : Type} [Group Y] [Group Y'] [Group C]

theorem BorelBase.map {U H : Subgroup Y} (D : BorelBase U H) (e : Y ≃* Y') :
    BorelBase (U.map e.toMonoidHom) (H.map e.toMonoidHom) where
  center y' hy' := by
    have h1 : e.symm y' = 1 := D.center _ fun x => by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy' _
    calc y' = e (e.symm y') := (e.apply_symm_apply y').symm
      _ = 1 := by rw [h1, map_one]
  sylow := isSylowTwoOf_top_map D.sylow e
  H_comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, D.H_comm a ha b hb]
  H_le := by
    rw [← Subgroup.map_equiv_normalizer_eq U e]
    exact Subgroup.map_mono D.H_le
  U_inf_H := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have : y = x := e.injective hyx
    rw [D.U_inf_H x hx (this ▸ hy), map_one]
  B_eq := by
    intro g' hg'
    rw [← Subgroup.map_equiv_normalizer_eq U e] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    obtain ⟨u, hu, h, hh, hgh⟩ := D.B_eq g hg
    exact ⟨e u, ⟨u, hu, rfl⟩, e h, ⟨h, hh, rfl⟩, by rw [hgh]; exact map_mul e.toMonoidHom u h⟩

namespace BorelAutDiag

variable {U H : Subgroup Y} {F E : Subgroup (MulAut Y)}

theorem congr_apply (e : Y ≃* Y') (α : MulAut Y) (x : Y) :
    (MulAut.congr e α) (e x) = e (α x) := by
  change e (α (e.symm (e x))) = e (α x)
  rw [e.symm_apply_apply]

theorem stab_map (e : Y ≃* Y') {S : MulAut Y} (h : ∀ x, S x ∈ U ↔ x ∈ U) (x' : Y') :
    (MulAut.congr e S) x' ∈ U.map e.toMonoidHom ↔ x' ∈ U.map e.toMonoidHom := by
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [congr_apply, mem_map_equiv_iff', mem_map_equiv_iff', h]

theorem map (D : BorelAutDiag U H F E) (e : Y ≃* Y') :
    BorelAutDiag (U.map e.toMonoidHom) (H.map e.toMonoidHom) (F.map (MulAut.congr e).toMonoidHom)
      (E.map (MulAut.congr e).toMonoidHom) where
  toBorelBase := D.toBorelBase.map e
  F_U := by
    rintro _ ⟨σ, hσ, rfl⟩ x'
    exact stab_map e (D.F_U σ hσ) x'
  F_H := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨h, hh, rfl⟩
    show (MulAut.congr e σ) (e h) ∈ H.map e.toMonoidHom
    rw [congr_apply]
    exact ⟨σ h, D.F_H σ hσ h hh, rfl⟩
  F_solv := by
    have := D.F_solv
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective F
      (MulAut.congr e).toMonoidHom (MulAut.congr e).injective).toMonoidHom)
      (Subgroup.equivMapOfInjective F _ (MulAut.congr e).injective).surjective
  F_faithful := by
    rintro _ ⟨σ, hσ, rfl⟩ hfix
    have : σ = 1 := by
      apply D.F_faithful σ hσ
      intro h hh
      have := hfix (e h) ⟨h, hh, rfl⟩
      change (MulAut.congr e σ) (e h) = e h at this
      rw [congr_apply] at this
      exact e.injective this
    rw [this, map_one]
  E_U := by
    rintro _ ⟨ε, hε, rfl⟩ x'
    exact stab_map e (D.E_U ε hε) x'
  E_solv := by
    have := D.E_solv
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective E
      (MulAut.congr e).toMonoidHom (MulAut.congr e).injective).toMonoidHom)
      (Subgroup.equivMapOfInjective E _ (MulAut.congr e).injective).surjective
  E_triv := by
    rintro _ ⟨ε, hε, rfl⟩ b' hb'
    rw [← Subgroup.map_equiv_normalizer_eq U e] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    change (e b)⁻¹ * (MulAut.congr e ε) (e b) ∈ U.map e.toMonoidHom
    rw [congr_apply, ← map_inv, ← map_mul]
    exact ⟨_, D.E_triv ε hε b hb, rfl⟩
  E_two := by
    rintro _ ⟨ε, hε, rfl⟩ k hk
    have h1 : ε ^ 2 ^ k = 1 := by
      apply (MulAut.congr e).injective
      rw [map_pow, map_one]
      exact hk
    obtain ⟨u, hu, rfl⟩ := D.E_two ε hε k h1
    refine ⟨e u, ⟨u, hu, rfl⟩, ?_⟩
    refine MulEquiv.ext fun x => ?_
    show e (MulAut.conj u (e.symm x)) = MulAut.conj (e u) x
    simp [MulAut.conj_apply]
  F_E := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨ε, hε, rfl⟩
    exact ⟨σ * ε * σ⁻¹, D.F_E σ hσ ε hε, by simp [map_mul, map_inv]⟩
  normal_form := by
    intro α' hα'
    set α : MulAut Y := (MulAut.congr e).symm α' with hα
    have hstab : ∀ x, α x ∈ U ↔ x ∈ U := by
      intro x
      have h1 := hα' (e x)
      have h2 : α' (e x) = e (α x) := by
        have := congr_apply e α x
        rwa [hα, MulEquiv.apply_symm_apply] at this
      rw [h2, mem_map_equiv_iff', mem_map_equiv_iff'] at h1
      exact h1
    obtain ⟨ε, hε, σ, hσ, hασ⟩ := D.normal_form α hstab
    refine ⟨(MulAut.congr e) ε, ⟨ε, hε, rfl⟩, (MulAut.congr e) σ, ⟨σ, hσ, rfl⟩, ?_⟩
    have h1 : (MulAut.congr e) α = α' := (MulAut.congr e).apply_symm_apply α'
    rw [← h1, hασ, map_mul]

theorem exists_of_equiv [Finite C] {U₀ H₀ : Subgroup C} {F₀ E₀ : Subgroup (MulAut C)}
    (D₀ : BorelAutDiag U₀ H₀ F₀ E₀) (e : Y ≃* C) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ (H : Subgroup Y) (F E : Subgroup (MulAut Y)), BorelAutDiag U H F E := by
  have hU' := isSylowTwoOf_top_map hU e
  obtain ⟨k, -, hk⟩ := D₀.sylow.exists_conj hU'
  let e' : C ≃* Y := (MulAut.conj k).trans e.symm
  have hUe : U₀.map e'.toMonoidHom = U := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h1 : MulAut.conj k c ∈ U₀.map (MulAut.conj k).toMonoidHom := ⟨c, hc, rfl⟩
      rw [← hk] at h1
      obtain ⟨y', hy', hy'c⟩ := h1
      show e.symm (MulAut.conj k c) ∈ U
      rw [← hy'c]
      simpa using hy'
    · intro hy
      have h1 : e y ∈ U.map e.toMonoidHom := ⟨y, hy, rfl⟩
      rw [hk] at h1
      obtain ⟨c, hc, hce⟩ := h1
      exact ⟨c, hc, by
        show e.symm (MulAut.conj k c) = y
        have : MulAut.conj k c = e y := hce
        rw [this]
        simp⟩
  have := D₀.map e'
  rw [hUe] at this
  exact ⟨_, _, _, this⟩

end BorelAutDiag

end CFSG.Quasithin.H13.Sec53F.BA
