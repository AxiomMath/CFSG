module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G]

private theorem mul_conj_mem_of_modEq {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    {d x t y w : Γ} (hxw : x⁻¹ * w ∈ N) (hty : y⁻¹ * t ∈ N)
    (h : d * x * d⁻¹ * (t * x * t⁻¹)⁻¹ ∈ N) : (y⁻¹ * d) * w * (y⁻¹ * d)⁻¹ * w⁻¹ ∈ N := by
  obtain ⟨π, hπ⟩ : ∃ π : Γ →* Γ ⧸ N, ∀ g, g ∈ N ↔ π g = 1 :=
    ⟨QuotientGroup.mk' N, fun g => (QuotientGroup.eq_one_iff g).symm⟩
  rw [hπ] at hxw hty h ⊢
  simp only [map_mul, map_inv] at hxw hty h ⊢
  have hX : π x = π w := inv_mul_eq_one.mp hxw
  have hT : π t = π y := (inv_mul_eq_one.mp hty).symm
  have hD : π d * π x * (π d)⁻¹ = π t * π x * (π t)⁻¹ := mul_inv_eq_one.mp h
  rw [hX, hT] at hD
  calc (π y)⁻¹ * π d * π w * ((π y)⁻¹ * π d)⁻¹ * (π w)⁻¹
      = (π y)⁻¹ * (π d * π w * (π d)⁻¹) * π y * (π w)⁻¹ := by group
    _ = 1 := by rw [hD]; group

theorem exists_inner_of_forall {A M W H : Subgroup G} [(ker148 A M).Normal]
    (hWM : W ≤ M) (hHM : H ≤ M) (hφ : Nonempty (↥(img148 A M W) ≃* alternatingGroup (Fin 5)))
    (hWH : img148 A M W ≤ img148 A M H) {d : G} (hdM : d ∈ M)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hdH : d ∈ Subgroup.normalizer (H : Set G))
    (hinner : ∀ (T : Subgroup G) (f : ↥T →* alternatingGroup (Fin 5)), T ≤ H →
      Function.Surjective f → f.ker = (T ⊓ pPrimeCoreOf 3 M).subgroupOf T →
      (∀ x ∈ T, d * x * d⁻¹ ∈ T) →
      ∃ t ∈ T, ∀ x ∈ T, (d * x * d⁻¹) * (t * x * t⁻¹)⁻¹ ∈ pPrimeCoreOf 3 M) :
    ∃ y ∈ W, ∀ w ∈ W, (y⁻¹ * d) * w * (y⁻¹ * d)⁻¹ * w⁻¹ ∈ pPrimeCoreOf 3 M := by
  obtain ⟨e⟩ := hφ
  have hMK : M ≤ Subgroup.normalizer (pPrimeCoreOf 3 M : Set G) := le_normalizer_pPrimeCoreOf 3 M
  have hWK : W ≤ Subgroup.normalizer (pPrimeCoreOf 3 M : Set G) := hWM.trans hMK
  have hWMA : W ≤ M ⊔ A := hWM.trans le_sup_left
  have hdec : ∀ x ∈ W ⊔ pPrimeCoreOf 3 M, ∃ y ∈ W, ∃ k ∈ pPrimeCoreOf 3 M, y * k = x := by
    intro x hx
    have hx' : x ∈ ((W ⊔ pPrimeCoreOf 3 M : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right W _ hWK] at hx'
    exact hx'
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = H ⊓ (W ⊔ pPrimeCoreOf 3 M) := ⟨_, rfl⟩
  have hTmem : ∀ x, x ∈ T ↔ x ∈ H ∧ x ∈ W ⊔ pPrimeCoreOf 3 M := fun x => by
    rw [hT]
    exact Subgroup.mem_inf
  have hTH : T ≤ H := fun x hx => ((hTmem x).mp hx).1
  have hTMA : T ≤ M ⊔ A := fun x hx => Subgroup.mem_sup_left (hHM (hTH hx))
  have hdT : ∀ x ∈ T, d * x * d⁻¹ ∈ T := by
    intro x hx
    obtain ⟨hxH, hxWK⟩ := (hTmem x).mp hx
    refine (hTmem _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hdH x).mp hxH, ?_⟩
    obtain ⟨y, hy, k, hk, rfl⟩ := hdec x hxWK
    have h1 : d * y * d⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hdW y).mp hy
    have h2 : d * k * d⁻¹ ∈ pPrimeCoreOf 3 M := (Subgroup.mem_normalizer_iff.mp (hMK hdM) k).mp hk
    have h3 := Subgroup.mul_mem_sup h1 h2
    rwa [show d * y * d⁻¹ * (d * k * d⁻¹) = d * (y * k) * d⁻¹ by group] at h3
  have hlift : ∀ w ∈ W, ∃ x ∈ T, x⁻¹ * w ∈ pPrimeCoreOf 3 M := by
    intro w hw
    have hwMA : w ∈ M ⊔ A := hWMA hw
    obtain ⟨g, hgH, hg⟩ : QuotientGroup.mk' (ker148 A M) ⟨w, hwMA⟩ ∈ img148 A M H :=
      hWH ⟨⟨w, hwMA⟩, hw, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hg
    have hk : (g : G)⁻¹ * w ∈ pPrimeCoreOf 3 M := Subgroup.mem_subgroupOf.mp hg
    have hk' : w⁻¹ * (g : G) ∈ pPrimeCoreOf 3 M := by
      simpa using (pPrimeCoreOf 3 M).inv_mem hk
    refine ⟨g, (hTmem _).mpr ⟨Subgroup.mem_subgroupOf.mp hgH, ?_⟩, hk⟩
    simpa using Subgroup.mul_mem_sup hw hk'
  let ψ : ↥T →* ↥(M ⊔ A) ⧸ ker148 A M :=
    (QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion hTMA)
  have hψ : ∀ (t : ↥T) (u : ↥(M ⊔ A)), ψ t = QuotientGroup.mk' (ker148 A M) u ↔
      (t : G)⁻¹ * (u : G) ∈ pPrimeCoreOf 3 M := by
    intro t u
    change QuotientGroup.mk' (ker148 A M) (Subgroup.inclusion hTMA t) = _ ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf
  have hψW : ∀ t : ↥T, ψ t ∈ img148 A M W := by
    intro t
    obtain ⟨y, hy, k, hk, hyk⟩ := hdec t ((hTmem t).mp t.2).2
    refine ⟨⟨y, hWMA hy⟩, hy, ?_⟩
    refine ((hψ t ⟨y, hWMA hy⟩).mpr ?_).symm
    show (t : G)⁻¹ * y ∈ pPrimeCoreOf 3 M
    rw [← hyk, show (y * k)⁻¹ * y = k⁻¹ by group]
    exact (pPrimeCoreOf 3 M).inv_mem hk
  let g : ↥T →* ↥(img148 A M W) := ψ.codRestrict (img148 A M W) hψW
  let f : ↥T →* alternatingGroup (Fin 5) := e.toMonoidHom.comp g
  have hfker : ∀ t : ↥T, f t = 1 ↔ (t : G) ∈ pPrimeCoreOf 3 M := by
    intro t
    have h1 : f t = 1 ↔ ψ t = 1 := by
      change e (g t) = 1 ↔ _
      rw [e.map_eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have h2 : ψ t = 1 ↔ (t : G) ∈ pPrimeCoreOf 3 M := by
      change QuotientGroup.mk' (ker148 A M) (Subgroup.inclusion hTMA t) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf
    exact h1.trans h2
  have hfsurj : Function.Surjective f := by
    intro a
    obtain ⟨z, rfl⟩ := e.surjective a
    obtain ⟨m, hm, hmz⟩ := z.2
    obtain ⟨x, hxT, hx⟩ := hlift (m : G) (Subgroup.mem_subgroupOf.mp hm)
    refine ⟨⟨x, hxT⟩, congrArg e (Subtype.ext ?_)⟩
    change ψ ⟨x, hxT⟩ = (z : ↥(M ⊔ A) ⧸ ker148 A M)
    rw [← hmz]
    exact (hψ ⟨x, hxT⟩ m).mpr hx
  have hker : f.ker = (T ⊓ pPrimeCoreOf 3 M).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
  obtain ⟨t, htT, ht⟩ := hinner T f hTH hfsurj hker hdT
  obtain ⟨y, hy, k, hk, hyk⟩ := hdec t ((hTmem t).mp htT).2
  refine ⟨y, hy, fun w hw => ?_⟩
  obtain ⟨x, hxT, hxw⟩ := hlift w hw
  have hty : y⁻¹ * t ∈ pPrimeCoreOf 3 M := by
    rw [← hyk, inv_mul_cancel_left]
    exact hk
  exact Subgroup.mem_subgroupOf.mp (mul_conj_mem_of_modEq (ker148 A M)
    (d := ⟨d, Subgroup.mem_sup_left hdM⟩) (x := ⟨x, hTMA hxT⟩) (t := ⟨t, hTMA htT⟩)
    (y := ⟨y, hWMA hy⟩) (w := ⟨w, hWMA hw⟩) (Subgroup.mem_subgroupOf.mpr hxw)
    (Subgroup.mem_subgroupOf.mpr hty) (Subgroup.mem_subgroupOf.mpr (ht x hxT)))

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
