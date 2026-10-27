module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

namespace P22w

section Transport

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {N : Subgroup X}

theorem commOn_restrict (K : Subgroup ↥N) (U : Submodule (ZMod 2) V) :
    commOn (ρ.comp N.subtype) K U = commOn ρ (K.map N.subtype) U := by
  unfold commOn
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, u, hu, rfl⟩
    exact ⟨a, ⟨a, ha, rfl⟩, u, hu, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
    exact ⟨a, ha, u, hu, rfl⟩

theorem isInvariant_map {H : Subgroup ↥N} {A : Submodule (ZMod 2) V} (h : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (ρ.comp N.subtype) H A) :
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (H.map N.subtype) A := by
  rintro _ ⟨a, ha, rfl⟩ u hu
  exact h a ha u hu

theorem coe_symm_equivMap {H : Subgroup ↥N} (hh : ↥(H.map N.subtype)) :
    ((((H.equivMapOfInjective N.subtype N.subtype_injective).symm hh : ↥H) : ↥N) : X) = (hh : X) := by
  have h5 := Subgroup.coe_equivMapOfInjective_apply H N.subtype N.subtype_injective
    ((H.equivMapOfInjective N.subtype N.subtype_injective).symm hh)
  rw [MulEquiv.apply_symm_apply] at h5
  exact h5.symm

theorem secNat_map {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup ↥N}
    {A B : Submodule (ZMod 2) V} {H' : Subgroup (GL ι K)} (h : SecNat (ρ.comp N.subtype) H A B H') :
    SecNat ρ (H.map N.subtype) A B H' := by
  obtain ⟨hA, hB, hBA, φ, ψ, h0, h1, h2, h3⟩ := h
  refine ⟨isInvariant_map hA, isInvariant_map hB, hBA,
    (H.equivMapOfInjective N.subtype N.subtype_injective).symm.trans φ, ψ, h0, h1, h2, fun hh x hx => ?_⟩
  have h4 := h3 ((H.equivMapOfInjective N.subtype N.subtype_injective).symm hh) x hx
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_symm_equivMap] at h4
  exact h4

theorem secNatS5_map {H : Subgroup ↥N} {A B : Submodule (ZMod 2) V} (h : SecNatS5 (ρ.comp N.subtype) H A B) :
    SecNatS5 ρ (H.map N.subtype) A B := by
  obtain ⟨hA, hB, hBA, φ, ψ, h0, h1, h2, h3, h4⟩ := h
  refine ⟨isInvariant_map hA, isInvariant_map hB, hBA,
    (H.equivMapOfInjective N.subtype N.subtype_injective).symm.trans φ, ψ, h0, h1, h2, h3, fun hh x hx => ?_⟩
  have h5 := h4 ((H.equivMapOfInjective N.subtype N.subtype_injective).symm hh) x hx
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_symm_equivMap] at h5
  exact h5

theorem shape148_map {H : Subgroup ↥N} {U C : Submodule (ZMod 2) V} (h : Shape148 (ρ.comp N.subtype) H U C) :
    Shape148 ρ (H.map N.subtype) U C := by
  rcases h with ⟨n, hn, F, i1, i2, hF, hs⟩ | hs | ⟨Ai, hAi, hsup, hind⟩ | hs
  · exact Or.inl ⟨n, hn, F, i1, i2, hF, secNat_map hs⟩
  · exact Or.inr (Or.inl (secNat_map hs))
  · exact Or.inr (Or.inr (Or.inl ⟨Ai, fun i => ⟨(hAi i).1, (hAi i).2.1, secNat_map (hAi i).2.2⟩, hsup, hind⟩))
  · exact Or.inr (Or.inr (Or.inr (secNatS5_map hs)))

end Transport

theorem factorShape22_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : FactorShape22 A) :
    FactorShape22 B := by
  rcases h with ⟨n, F, i1, i2, hF, ⟨φ⟩⟩ | h | h
  · exact Or.inl ⟨n, F, i1, i2, hF, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h))
  · obtain ⟨φ⟩ := h
    exact Or.inr (Or.inr ⟨e.symm.trans φ⟩)

theorem isInternalDirect_map {X : Type} [Group X] {N : Subgroup X} {m : ℕ} {Hs : Fin m → Subgroup ↥N}
    (hd : IsInternalDirect (⊤ : Subgroup ↥N) Hs) : IsInternalDirect N (fun i => (Hs i).map N.subtype) := by
  obtain ⟨h1, h2, h3⟩ := hd
  refine ⟨?_, ?_, fun i => ?_⟩
  · rw [← Subgroup.map_iSup, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := h2 i j hij x hx y hy
    exact congrArg Subtype.val this
  · have hmap : (⨆ j ∈ {j | j ≠ i}, (Hs j).map N.subtype) = (⨆ j ∈ {j | j ≠ i}, Hs j).map N.subtype := by
      rw [Subgroup.map_iSup]
      congr 1
      ext j
      rw [Subgroup.map_iSup]
    change (Hs i).map N.subtype ⊓ (⨆ j ∈ {j | j ≠ i}, (Hs j).map N.subtype) = ⊥
    rw [hmap, ← Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, h3 i, Subgroup.map_bot]

end P22w

end CFSG.LocalAnalysis.UniquenessCase.UC22
