module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem ggKGRootDatumAt_of_componentCover
    {R : Type} [Group R] [Finite R]
    (hS : IsSimpleGroup R) (hnc : ∃ a b : R, a * b ≠ b * a) (hchev : IsChevSimple 2 R)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup R} (hE : IsElemAbelian p E)
    {ι : Type} (m : ι → R) (J : ι → Subgroup R)
    (hmJ : ∀ i, m i ∈ J i)
    (hJcomp : ∀ i, CFSG.Assembly.IsComponentOf (J i)
      (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({m i} : Set R) : Subgroup R) : Set R)))
    (hdvd : ∀ i, p ∣ Nat.card (J i))
    (hcover : ∀ w₀ : R, GGKGIsReflAt p E w₀ →
      ∃ i, ∃ u ∈ Subgroup.normalizer (E : Set R),
        ∀ e ∈ E, w₀ * e * w₀⁻¹ =
          (u * m i * u⁻¹) * e * (u * m i * u⁻¹)⁻¹) :
    GGKGRootDatumAt p E := by
  classical
  intro w₀ hrefl
  obtain ⟨i, u, huN, hwu⟩ := hcover w₀ hrefl
  set w : R := u * m i * u⁻¹ with hwdef
  set c : R ≃* R := MulAut.conj u with hcdef
  have hw_eq : w = c (m i) := by
    simp [hwdef, hcdef, MulAut.conj_apply]
  have hEN : E.map c.toMonoidHom = E := by
    simpa [hcdef] using Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
  have hA_map : (E ⊓ Subgroup.centralizer ({m i} : Set R)).map c.toMonoidHom =
      E ⊓ Subgroup.centralizer ({w} : Set R) := by
    rw [CFSG.centralizer_inter_map c E (m i), hEN, ← hw_eq]
  have hcent_map :
      (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({m i} : Set R) : Subgroup R) : Set R)).map c.toMonoidHom =
      Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R) := by
    rw [CFSG.Glauberman.map_centralizer_eq_of_equiv c
      (E ⊓ Subgroup.centralizer ({m i} : Set R)), hA_map]
  have hJcomp' : CFSG.Assembly.IsComponentOf ((J i).map c.toMonoidHom)
      (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) := by
    have h := isComponentOf_map_of_injective c.toMonoidHom c.injective (hJcomp i)
    rwa [hcent_map] at h
  refine ⟨w, ?_, (J i).map c.toMonoidHom, ?_, hJcomp', ?_, ?_⟩
  · intro e he
    simpa [hwdef] using (hwu e he).symm
  · rw [hw_eq]
    exact Subgroup.mem_map_of_mem c.toMonoidHom (hmJ i)
  · rw [Subgroup.card_map_of_injective c.injective]
    exact hdvd i
  · intro a ha haw
    have huinv : u⁻¹ ∈ Subgroup.normalizer (E : Set R) := Subgroup.inv_mem _ huN
    have ha'E : u⁻¹ * a * u ∈ E :=
      by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp huinv a).mp ha
    have ha'p : (u⁻¹ * a * u) ^ p = 1 := by
      rw [show u⁻¹ * a * u = u⁻¹ * a * (u⁻¹)⁻¹ by rw [inv_inv]]
      rw [conj_pow, hE.2 a ha, mul_one, mul_inv_cancel]
    have hcomm' : (u⁻¹ * a * u) * m i = m i * (u⁻¹ * a * u) := by
      have h := congrArg (fun x => u⁻¹ * x * u) haw
      rw [hwdef] at h
      calc
        (u⁻¹ * a * u) * m i = u⁻¹ * (a * (u * m i * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * m i * u⁻¹) * a) * u := h.symm
        _ = m i * (u⁻¹ * a * u) := by group
    have ha'cent : u⁻¹ * a * u ∈ Subgroup.centralizer ({m i} : Set R) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm'
    have hJcent : J i ≤ Subgroup.centralizer ({u⁻¹ * a * u} : Set R) := by
      intro x hx
      have hx' := (hJcomp i).1 hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx') (u⁻¹ * a * u) ⟨ha'E, ha'cent⟩).symm
    have hlayer := ggKG_layer_of_chevSimple hS hnc hchev hp hp2 ha'p
      (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top
        (hJcomp i).2.2.1) hJcent
    calc
      (J i).map c.toMonoidHom
          ≤ (LargeEvenLayer (Subgroup.centralizer ({u⁻¹ * a * u} : Set R))).map
              c.toMonoidHom :=
            Subgroup.map_mono hlayer
      _ = LargeEvenLayer
            ((Subgroup.centralizer ({u⁻¹ * a * u} : Set R)).map c.toMonoidHom) :=
            (largeEvenLayer_map_of_injective c.toMonoidHom c.injective _).symm
      _ = LargeEvenLayer (Subgroup.centralizer ({a} : Set R)) := by
            rw [CFSG.centralizer_singleton_map c (u⁻¹ * a * u)]
            rw [show c (u⁻¹ * a * u) = a by
              rw [hcdef, MulAut.conj_apply]
              group]

end CFSG.StandardType

end
