module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.Sec53F.BA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Y Y' C : Type} [Group Y] [Group Y'] [Group C]

theorem mem_map_equiv_iff' (e : Y ≃* Y') (K : Subgroup Y) (x : Y) :
    e x ∈ K.map e.toMonoidHom ↔ x ∈ K :=
  Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective

theorem isSylowTwoOf_top_map {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) (e : Y ≃* Y') :
    IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hU.2.1.of_equiv (Subgroup.equivMapOfInjective U e.toMonoidHom e.injective)
  · have h := hU.2.2
    have e1 : ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.subgroupOf ⊤).index := by
      show (U.map e.toMonoidHom).relIndex ⊤ = U.relIndex ⊤
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right]
      exact Subgroup.index_map_equiv U e
    rwa [e1]

namespace BorelAutData

variable {U H : Subgroup Y} {F : Subgroup (MulAut Y)}

theorem map (D : BorelAutData U H F) (e : Y ≃* Y') :
    BorelAutData (U.map e.toMonoidHom) (H.map e.toMonoidHom)
      (F.map (MulAut.congr e).toMonoidHom) where
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
  F_U := by
    rintro _ ⟨σ, hσ, rfl⟩ x'
    show e (σ (e.symm x')) ∈ U.map e.toMonoidHom ↔ x' ∈ U.map e.toMonoidHom
    rw [mem_map_equiv_iff', D.F_U σ hσ]
    conv_rhs => rw [← e.apply_symm_apply x', mem_map_equiv_iff']
  F_H := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨h, hh, rfl⟩
    show e (σ (e.symm (e h))) ∈ H.map e.toMonoidHom
    rw [e.symm_apply_apply]
    exact ⟨σ h, D.F_H σ hσ h hh, rfl⟩
  F_comm := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [← map_mul, ← map_mul, D.F_comm σ hσ τ hτ]
  F_faithful := by
    rintro _ ⟨σ, hσ, rfl⟩ hfix
    have : σ = 1 := by
      apply D.F_faithful σ hσ
      intro h hh
      have := hfix (e h) ⟨h, hh, rfl⟩
      change e (σ (e.symm (e h))) = e h at this
      rw [e.symm_apply_apply] at this
      exact e.injective this
    rw [this, map_one]
  normal_form := by
    intro α' hα'
    set α : MulAut Y := (MulAut.congr e).symm α' with hα
    have hαapp : ∀ x, α x = e.symm (α' (e x)) := fun x => rfl
    have hstab : ∀ x, α x ∈ U ↔ x ∈ U := by
      intro x
      rw [hαapp, ← mem_map_equiv_iff' e, e.apply_symm_apply, hα', mem_map_equiv_iff']
    obtain ⟨g, hg, σ, hσ, hασ⟩ := D.normal_form α hstab
    refine ⟨e g, ?_, (MulAut.congr e) σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · rw [← Subgroup.map_equiv_normalizer_eq U e]
      exact ⟨g, hg, rfl⟩
    · have h1 : (MulAut.congr e) α = α' := (MulAut.congr e).apply_symm_apply α'
      rw [← h1, hασ, map_mul]
      congr 1
      refine MulEquiv.ext fun x => ?_
      show e (MulAut.conj g (e.symm x)) = MulAut.conj (e g) x
      simp [MulAut.conj_apply]


theorem exists_of_equiv [Finite C] {U₀ H₀ : Subgroup C} {F₀ : Subgroup (MulAut C)}
    (D₀ : BorelAutData U₀ H₀ F₀) (e : Y ≃* C) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ (H : Subgroup Y) (F : Subgroup (MulAut Y)), BorelAutData U H F := by
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
  exact ⟨_, _, this⟩

end BorelAutData

end CFSG.Quasithin.H13.Sec53F.BA
