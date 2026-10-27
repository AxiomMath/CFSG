module

public import CFSG.Milestones.ASVolI.F411.aSwCore
public import CFSG.Quasithin.Vol2.F134LieSp4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv tauAut tauAut_proj)

section Tau

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem burnsideF411a_map_tauEquiv_stabilizer :
    (stabilizer 2 K (flag 2 K 1)).map (tauEquiv (F := K)).toMonoidHom =
        stabilizer 2 K (flag 2 K 2) ∧
      (stabilizer 2 K (flag 2 K 2)).map (tauEquiv (F := K)).toMonoidHom =
        stabilizer 2 K (flag 2 K 1) := by
  have h12 : (stabilizer 2 K (flag 2 K 1)).map (tauEquiv (F := K)).toMonoidHom ≤
      stabilizer 2 K (flag 2 K 2) := by
    rintro _ ⟨g, hg, rfl⟩
    exact CFSG.Quasithin.F134.Sp4.tauSp_mem_stabilizer_two hg
  have h21 : (stabilizer 2 K (flag 2 K 2)).map (tauEquiv (F := K)).toMonoidHom ≤
      stabilizer 2 K (flag 2 K 1) := by
    rintro _ ⟨g, hg, rfl⟩
    exact CFSG.Quasithin.F134.Sp4.tauSp_mem_stabilizer_one hg
  have hc : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K),
      Nat.card ((stabilizer 2 K W).map (tauEquiv (F := K)).toMonoidHom) =
        Nat.card (stabilizer 2 K W) := fun W =>
    Subgroup.card_map_of_injective (f := (tauEquiv (F := K)).toMonoidHom)
      (tauEquiv (F := K)).injective
  have c1 := Subgroup.card_le_of_le h12
  have c2 := Subgroup.card_le_of_le h21
  rw [hc] at c1 c2
  exact ⟨Subgroup.eq_of_le_of_card_ge h12 (by rw [hc]; exact c2),
    Subgroup.eq_of_le_of_card_ge h21 (by rw [hc]; exact c1)⟩

theorem burnsideF411a_map_tauAut_projStabilizer {a b : ℕ}
    (h : (stabilizer 2 K (flag 2 K a)).map (tauEquiv (F := K)).toMonoidHom =
      stabilizer 2 K (flag 2 K b)) :
    (projStabilizer 2 K (flag 2 K a)).map (tauAut (F := K)).toMonoidHom =
      projStabilizer 2 K (flag 2 K b) := by
  rw [projStabilizer, projStabilizer, Subgroup.map_map, ← h, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => tauAut_proj g

end Tau

private theorem burnsideF411a_sp4_marking_parabolic {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .Sp4 2 f H) (b : Bool) :
    marking.parabolic b =
      (projStabilizer 2 marking.field (flag 2 marking.field (if b then 2 else 1))).map
        (marking.identification : StatedProj (StatedSp 2 marking.field) ≃* H).toMonoidHom := by
  set K := marking.field
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have keym : ∀ (b : Bool) (x : StatedSp 2 K),
      x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (2 ^ f) K marking.basis b ↔
        x ∈ stabilizer 2 K (flag 2 K (if b then 2 else 1)) := by
    intro b x
    rw [hbasis]
    have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (2 ^ f) K 1 b ↔
        (x : GL (ChF.ClassicalRoots.Coord .Sp4) K) ∈ ChF.ClassicalRoots.rawStabilizer
          ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .Sp4) K) :
            Matrix (ChF.ClassicalRoots.Coord .Sp4) (ChF.ClassicalRoots.Coord .Sp4) K).mulVec
              vector) ''
            ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .Sp4
              else ChF.ClassicalRoots.flagOne .Sp4)) :=
      Iff.rfl
    rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
      burnsideF4h_cl_map_eq_iff _
        (C := (((x⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        (by rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one])
        (by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one])]
    simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
    cases b
    · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sp_coordinateSpace _).1, (burnsideF4h_cl_sp_coordinateSpace _).1]
    · simp only [if_true, ChF.ClassicalRoots.flagTwo]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sp_coordinateSpace _).2, (burnsideF4h_cl_sp_coordinateSpace _).2]
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨proj 2 K x, ⟨x, (keym b x).1 hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, (keym b x).2 hx, rfl⟩

theorem burnsideF411a_swap_Sp4_two {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨chart, hB, hP1, hP2⟩ := hyp.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  rotate_left
  iterate 5 exact absurd hk (by decide)
  have hc : c = .Sp4 := by cases c <;> first | rfl | exact absurd hk (by decide)
  subst hc
  set K := marking.field
  have hK : Nat.card K = 2 ^ f := by simpa using marking.field_card
  haveI : CharP K 2 := burnsideF4h_cl_charP hK
  let e : StatedProj (StatedSp 2 K) ≃* ↥Gp := marking.identification
  have hcl := (burnsideF4h_cl_Sp4 2 f ↥Gp marking).1
  have hmap := burnsideF4h_isLieParabolics_map Gp.subtype Gp.subtype_injective hcl
  rw [burnsideF4h_map_subtype_top, ← h1, ← h2, ← h3, ← hB, ← hP1, ← hP2] at hmap
  have hQ1 : (Gp ⊓ M₁).subgroupOf Gp = marking.parabolic false := by
    rw [hP1, h2]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hQ2 : (Gp ⊓ M₂).subgroupOf Gp = marking.parabolic true := by
    rw [hP2, h3]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  obtain ⟨τ₀, hτ₀⟩ := CFSG.Quasithin.F134.Sp4.exists_forall_eq_conj_mul_pow e.symm
  have hζ : ∀ a b : ℕ, (stabilizer 2 K (flag 2 K a)).map (tauEquiv (F := K)).toMonoidHom =
      stabilizer 2 K (flag 2 K b) →
      ((projStabilizer 2 K (flag 2 K a)).map e.toMonoidHom).map
          (MulAut.congr e (tauAut (F := K))).toMonoidHom =
        (projStabilizer 2 K (flag 2 K b)).map e.toMonoidHom := by
    intro a b hab
    rw [← burnsideF411a_map_tauAut_projStabilizer hab, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => by simp [MulAut.congr_apply]
  have hpar := burnsideF411a_sp4_marking_parabolic marking
  refine burnsideF411a_swap_of_graph hyp.normal hyp.centralizer_trivial hyp.split hmap τ₀ hτ₀
    (MulAut.congr e (tauAut (F := K))) ?_ ?_
  · rw [hQ1, hQ2, hpar false, hpar true]
    exact hζ 1 2 (burnsideF411a_map_tauEquiv_stabilizer (K := K)).1
  · rw [hQ1, hQ2, hpar false, hpar true]
    exact hζ 2 1 (burnsideF411a_map_tauEquiv_stabilizer (K := K)).2

end CFSG.ASVolI
