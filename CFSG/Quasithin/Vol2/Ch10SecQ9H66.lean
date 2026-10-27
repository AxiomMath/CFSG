module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H62
public import CFSG.Quasithin.Vol2.Ch10SecQ9H65

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin (perfectCore IsMaxParabolic2 IsParabolic2 IsG2)

namespace G2Core

theorem not_two_dvd_index_of_residual {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup X} (hres : ResidualOvergroupsAt X U P)
    (hcore : ∀ j, U ≤ perfectCore (P j)) {Pa : Subgroup X}
    (hPa : IsMaxParabolic2 (⊤ : Subgroup X) Pa) : ¬ 2 ∣ (perfectCore Pa).index := by
  obtain ⟨⟨-, S₁, hS₁, hN⟩, hne, hmax⟩ := hPa
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hU hS₁
  set c : X ≃* X := MulAut.conj g with hc
  have hres' := hres.map c
  rw [hg] at hres'
  have hcore' : ∀ j, S₁ ≤ perfectCore ((P j).map c.toMonoidHom) := fun j => by
    rw [← hg, ← CFSG.Quasithin.map_perfectCore]
    exact Subgroup.map_mono (hcore j)
  have hS₁N : S₁ ≤ Pa := fun x hx => hN ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
  obtain ⟨M, hM, hPaM⟩ := (eq_top_or_exists_le_coatom Pa).resolve_left hne
  obtain ⟨j, hj⟩ := (hres'.2.2.1 M (hS₁N.trans hPaM)).1 hM.covBy_top
  have hpar : IsParabolic2 (⊤ : Subgroup X) M := ⟨le_top, S₁, hS₁, fun x hx => hPaM (hN hx)⟩
  have heq : M = Pa := hmax M hpar hM.1 hPaM
  have hS₁i : ¬ 2 ∣ S₁.index := by
    have h := hS₁.2.2
    rwa [show (S₁.subgroupOf ⊤).index = S₁.index from Subgroup.relIndex_top_right S₁] at h
  rw [← heq, hj]
  exact fun h2 => hS₁i (h2.trans (Subgroup.index_dvd_of_le (hcore' j)))

theorem isSylowTwoOf_top_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {U : Subgroup A}
    (hU : IsSylowTwoOf U ⊤) : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hU.2.1.map _, ?_⟩
  have h := hU.2.2
  rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
  rwa [show ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective e.bijective]

end G2Core

theorem factG2CoreOddIndex_holds :
    FactG2CoreOddIndex := by
  intro Y _ _ f hf hY P hP
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hY
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  have hcore : ∀ j, (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤
      perfectCore
        ((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf (adjointGroup Tag.G2 K)) := by
    intro j
    rw [Rank2.perfectCore_subgroupOf (parabolicSubgroup_le_adjointGroup _ _ _)]
    intro x hx
    exact Subgroup.mem_subgroupOf.2
      (G2Core.posUnipotent_le_perfectCore hK4 _ (Subgroup.mem_subgroupOf.1 hx))
  refine G2Core.not_two_dvd_index_of_residual (G2Core.isSylowTwoOf_top_map e.symm hU₀)
    ((G2_residualOvergroupsAt (K := K)).map e.symm) (fun j => ?_) hP
  rw [← CFSG.Quasithin.map_perfectCore]
  exact Subgroup.map_mono (hcore j)

end CFSG.Quasithin.Vol2.Ch10.SecB
