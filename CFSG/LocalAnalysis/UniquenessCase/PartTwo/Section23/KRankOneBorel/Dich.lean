module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup

@[expose] def RankOneOver (X : Type) [Group X] : Prop :=
  ∀ (S : Sylow 2 X) (H : Subgroup X), (S : Subgroup X) ≤ H →
    H ≤ normalizer ((S : Subgroup X) : Set X) ∨ H = ⊤

theorem RankOneOver.of_surjective {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (h : RankOneOver A) : RankOneOver B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S' H' hS'H'
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf 2 S'
  have hSH : (S : Subgroup A) ≤ H'.comap f := by
    rw [← Subgroup.map_le_iff_le_comap, ← Sylow.coe_mapSurjective hf S]
    exact hS'H'
  rcases h S (H'.comap f) hSH with hN | htop
  · left
    calc H' = (H'.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf H').symm
      _ ≤ (normalizer ((S : Subgroup A) : Set A)).map f := Subgroup.map_mono hN
      _ ≤ normalizer (((S : Subgroup A).map f) : Set B) := Subgroup.le_normalizer_map f
      _ = normalizer ((S.mapSurjective hf : Sylow 2 B) : Set B) := by
          exact congrArg (fun K : Subgroup B => normalizer (K : Set B))
            (Sylow.coe_mapSurjective hf S).symm
  · right
    calc H' = (H'.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf H').symm
      _ = (⊤ : Subgroup A).map f := by rw [htop]
      _ = ⊤ := Subgroup.map_top_of_surjective f hf

theorem RankOneOver.of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] (e : A ≃* B)
    (h : RankOneOver A) : RankOneOver B :=
  RankOneOver.of_surjective e.toMonoidHom e.surjective h

private theorem eq_top_of_map_mk'_eq_top_of_perfect {Y : Type} [Group Y]
    (hperf : _root_.commutator Y = ⊤) (Z : Subgroup Y) [Z.Normal]
    (hZ : Z ≤ center Y) (H : Subgroup Y)
    (hH : H.map (QuotientGroup.mk' Z) = ⊤) : H = ⊤ := by
  have hsup : Z ⊔ H = ⊤ := by
    have h1 : (H.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = Z ⊔ H :=
      QuotientGroup.comap_map_mk' Z H
    rw [hH, Subgroup.comap_top] at h1
    exact h1.symm
  have hHnorm : H.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le (hZ.trans (Subgroup.center_le_normalizer (H : Set Y)))
      Subgroup.le_normalizer
  have hZcomm : IsMulCommutative Z :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (hZ.trans (Subgroup.center_le_centralizer (Z : Set Y)))
  have hcomm : _root_.commutator Y ≤ H := by
    letI : H.Normal := hHnorm
    exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (N := H) (H := Z) (by rw [sup_comm]; exact hsup) hZcomm
  rw [eq_top_iff, ← hperf]
  exact hcomm

theorem normalizer_le_normalizer_of_le_normalizer {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (S : Sylow p Y) {W : Subgroup Y} (hSW : (S : Subgroup Y) ≤ W)
    (hWN : W ≤ normalizer ((S : Subgroup Y) : Set Y)) :
    normalizer (W : Set Y) ≤ normalizer ((S : Subgroup Y) : Set Y) := by
  intro g hg
  set S' : Subgroup Y := (S : Subgroup Y).map (MulAut.conj g).toMonoidHom with hS'
  have hSW' : S' ≤ W := by
    rw [hS']
    calc (S : Subgroup Y).map (MulAut.conj g).toMonoidHom
        ≤ W.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hSW
      _ = W := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hS'N : S' ≤ normalizer ((S : Subgroup Y) : Set Y) := hSW'.trans hWN
  have hP2 : IsPGroup p S' := by
    rw [hS']
    exact S.isPGroup'.map (MulAut.conj g).toMonoidHom
  have hsup2 : IsPGroup p (((S : Subgroup Y) ⊔ S' : Subgroup Y)) :=
    IsPGroup.to_sup_of_normal_left' S.isPGroup' hP2 hS'N
  have heq : ((S : Subgroup Y) ⊔ S') = (S : Subgroup Y) := S.is_maximal' hsup2 le_sup_left
  have hle : S' ≤ (S : Subgroup Y) :=
    calc S' ≤ (S : Subgroup Y) ⊔ S' := le_sup_right
      _ = (S : Subgroup Y) := heq
  have heq2 : S' = (S : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hS']
      exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).symm)
  have hmap : (S : Subgroup Y).map (MulAut.conj g).toMonoidHom = (S : Subgroup Y) := by
    rwa [hS'] at heq2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem dich_of_map_center {Y : Type} [Group Y] [Finite Y] (hperf : _root_.commutator Y = ⊤)
    (Z : Subgroup Y) [Z.Normal] (hZ : Z ≤ center Y) (S : Sylow 2 Y) (H : Subgroup Y)
    (hSH : (S : Subgroup Y) ≤ H)
    (h : H.map (QuotientGroup.mk' Z) ≤
        normalizer (((S : Subgroup Y).map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z)) ∨
      H.map (QuotientGroup.mk' Z) = ⊤) :
    H ≤ normalizer ((S : Subgroup Y) : Set Y) ∨ H = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  rcases h with hnorm | htop
  · left
    have hN : H ≤ normalizer (((S : Subgroup Y) ⊔ Z : Subgroup Y) : Set Y) := by
      intro y hy
      have hm : QuotientGroup.mk' Z y ∈ normalizer
          ((((S : Subgroup Y).map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z))) :=
        hnorm (Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hy)
      have hm' : y ∈ (normalizer (((S : Subgroup Y).map (QuotientGroup.mk' Z) :
          Subgroup (Y ⧸ Z)))).comap (QuotientGroup.mk' Z) := hm
      rwa [Subgroup.comap_normalizer_eq_of_surjective _ hq,
        QuotientGroup.comap_map_mk' Z (S : Subgroup Y), sup_comm] at hm'
    have hWN : ((S : Subgroup Y) ⊔ Z : Subgroup Y) ≤
        normalizer ((S : Subgroup Y) : Set Y) :=
      sup_le Subgroup.le_normalizer
        (hZ.trans (Subgroup.center_le_normalizer ((S : Subgroup Y) : Set Y)))
    exact hN.trans (normalizer_le_normalizer_of_le_normalizer S le_sup_left hWN)
  · right
    exact eq_top_of_map_mk'_eq_top_of_perfect hperf Z hZ H htop

theorem RankOneOver.of_quotient_center {Y : Type} [Group Y] [Finite Y]
    (hperf : _root_.commutator Y = ⊤) (h : RankOneOver (Y ⧸ center Y)) : RankOneOver Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S H hSH
  have hSH' : ((S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center Y)) :
      Sylow 2 (Y ⧸ center Y)) : Subgroup (Y ⧸ center Y)) ≤
      H.map (QuotientGroup.mk' (Subgroup.center Y)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSH
  have hdich := h (S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center Y)))
    (H.map (QuotientGroup.mk' (Subgroup.center Y))) hSH'
  simp only [Sylow.coe_mapSurjective] at hdich
  exact dich_of_map_center hperf (Subgroup.center Y) le_rfl S H hSH hdich

theorem RankOneOver.of_bender {X : Type} [Group X] [Finite X]
    (hB : CFSG.Open.fusionIsBenderGroup X) : RankOneOver X := by
  intro S H hSH
  haveI : IsSimpleGroup X :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  by_cases hH : H = ⊤
  · exact Or.inr hH
  · exact Or.inl (CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB S hSH hH)

theorem rankOneOver_of_shape {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSz X n ∨ IsL2 X n ∨ IsSU3 X n) : RankOneOver X := by
  rcases h with h | h | h
  · exact RankOneOver.of_bender (uc22p2214_bor_bender_Sz h)
  · exact RankOneOver.of_bender (uc22p2214_bor_bender_L2 h)
  · exact RankOneOver.of_quotient_center h.1.1
      (RankOneOver.of_bender (uc22p2214_bor_bender_U3 h.2))

theorem dich_of_residual {X : Type} [Group X] [Finite X] {U : Subgroup X}
    {P : Fin 2 → Subgroup X} (hR : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt X U P)
    (hinf : P 0 ⊓ P 1 ≤ normalizer (U : Set X)) (θ : MulAut X) (hθU : U.map θ.toMonoidHom = U)
    (hθP : (P 0).map θ.toMonoidHom ≠ P 0) (H : Subgroup X) (hUH : U ≤ H)
    (hθH : H.map θ.toMonoidHom = H) :
    H ≤ normalizer (U : Set X) ∨ H = ⊤ := by
  obtain ⟨hne, hUP, hmax, -, -, -⟩ := hR
  by_cases hH : H = ⊤
  · exact Or.inr hH
  · left
    obtain ⟨M, hHM, hM⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hH)
    obtain ⟨j, hj⟩ := (hmax M (hUH.trans hHM)).1 hM
    have hHj : H ≤ P j := hj ▸ hHM
    have hcov0 : (P 0).map θ.toMonoidHom ⋖ ⊤ := by
      have h := (apply_covBy_apply_iff (MulEquiv.mapSubgroup θ)).2
        ((hmax (P 0) (hUP 0)).2 ⟨0, rfl⟩)
      rwa [show (MulEquiv.mapSubgroup θ) (⊤ : Subgroup X) = ⊤ from
        Subgroup.map_top_of_surjective _ θ.surjective] at h
    have hU0 : U ≤ (P 0).map θ.toMonoidHom := by
      rw [← hθU]
      exact Subgroup.map_mono (hUP 0)
    obtain ⟨k, hk⟩ := (hmax ((P 0).map θ.toMonoidHom) hU0).1 hcov0
    have hP0θ : (P 0).map θ.toMonoidHom = P 1 := by
      fin_cases k
      · exact absurd hk hθP
      · exact hk
    have hcov1 : (P 1).map θ.toMonoidHom ⋖ ⊤ := by
      have h := (apply_covBy_apply_iff (MulEquiv.mapSubgroup θ)).2
        ((hmax (P 1) (hUP 1)).2 ⟨1, rfl⟩)
      rwa [show (MulEquiv.mapSubgroup θ) (⊤ : Subgroup X) = ⊤ from
        Subgroup.map_top_of_surjective _ θ.surjective] at h
    have hU1 : U ≤ (P 1).map θ.toMonoidHom := by
      rw [← hθU]
      exact Subgroup.map_mono (hUP 1)
    obtain ⟨k, hk1⟩ := (hmax ((P 1).map θ.toMonoidHom) hU1).1 hcov1
    have hP1θ : (P 1).map θ.toMonoidHom = P 0 := by
      fin_cases k
      · exact hk1
      · exact absurd (Subgroup.map_injective θ.injective (hP0θ.trans hk1.symm)) hne
    have hHP : H ≤ P 0 ⊓ P 1 := by
      fin_cases j
      · refine le_inf hHj ?_
        rw [← hP0θ, ← hθH]
        exact Subgroup.map_mono hHj
      · refine le_inf ?_ hHj
        rw [← hP1θ, ← hθH]
        exact Subgroup.map_mono hHj
    exact hHP.trans hinf

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel
