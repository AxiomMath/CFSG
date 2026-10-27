module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem K105In.map_mulEquiv {X' : Type} [Group X'] (f : X ≃* X') {H T : Subgroup X}
    (h : K105In H T) :
    K105In (H.map f.toMonoidHom) (T.map f.toMonoidHom) := by
  intro Y hTY hYH hYs hY3
  let Z : Subgroup X := Y.comap f.toMonoidHom
  have hYrange : Y ≤ f.toMonoidHom.range :=
    hYH.trans (Subgroup.map_le_range f.toMonoidHom H)
  have hTZ : T ≤ Z := Subgroup.map_le_iff_le_comap.mp hTY
  have hZH : Z ≤ H := fun x hx =>
    (Subgroup.mem_map_iff_mem f.injective).1 (hYH hx)
  have hmap : Z.map f.toMonoidHom = Y := by
    change (Y.comap f.toMonoidHom).map f.toMonoidHom = Y
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hYrange]
  have hZsolv : Group.IsSolvable ↥Z := by
    have e := Subgroup.equivMapOfInjective Z f.toMonoidHom f.injective
    rw [hmap] at e
    exact @Group.isSolvable_of_surjective ↥Y ↥Z _ _ e.symm.toMonoidHom
      e.symm.surjective hYs
  have hZ3 : ¬ 3 ∣ Nat.card ↥Z := by
    intro h3
    apply hY3
    have e := Subgroup.equivMapOfInjective Z f.toMonoidHom f.injective
    rw [hmap] at e
    rw [← Nat.card_congr e.toEquiv]
    exact h3
  have hZT : Z ≤ T := h Z hTZ hZH hZsolv hZ3
  rw [← hmap]
  exact Subgroup.map_mono hZT

theorem K105In.of_isSylowTwoOf {H T T' : Subgroup X} (h : K105In H T) (hTH : T ≤ H)
    (hT'H : T' ≤ H) (hT : IsSylowTwoOf T ⊤) (hT' : IsSylowTwoOf T' ⊤) :
    K105In H T' := by
  have hiSH : ¬ 2 ∣ (T.subgroupOf H).index := by
    have h := hT.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rw [Subgroup.relIndex_top_right] at h
    exact fun h2 => h (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))
  have hiSH' : ¬ 2 ∣ (T'.subgroupOf H).index := by
    have h := hT'.2.2
    change ¬ 2 ∣ T'.relIndex ⊤ at h
    rw [Subgroup.relIndex_top_right] at h
    exact fun h2 => h (h2.trans (Subgroup.relIndex_dvd_index_of_le hT'H))
  have hSylH : IsSylowTwoOf T H := ⟨hTH, hT.2.1, hiSH⟩
  have hSylH' : IsSylowTwoOf T' H := ⟨hT'H, hT'.2.1, hiSH'⟩
  obtain ⟨g, hgH, hconjX⟩ := IsSylowTwoOf.exists_conj hSylH hSylH'
  have hHmap : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgH)
  have hmap := h.map_mulEquiv (MulAut.conj g)
  rw [hHmap, ← hconjX] at hmap
  exact hmap

omit [Finite X] in
theorem centralizer_conj (g x : X) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set X) =
      (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
