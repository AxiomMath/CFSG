module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem uc22p22u_le_inf_sup_of_perfect_map {Q B : Type*} [Group Q] [Group B] (φ : Q →* B)
    (N : Subgroup Q) [N.Normal] (hN : φ.ker = N) (C : Subgroup Q)
    (hC : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ C ⊔ N) (U : Subgroup Q) (hNU : N ≤ U)
    (hperf : ⁅U.map φ, U.map φ⁆ = U.map φ) : U ≤ (U ⊓ C) ⊔ N := by
  have h1 : U ≤ ⁅U, U⁆ ⊔ N := by
    calc U ≤ (U.map φ).comap φ := le_comap_map φ U
      _ = ((⁅U, U⁆).map φ).comap φ := by rw [map_commutator, hperf]
      _ = ⁅U, U⁆ ⊔ φ.ker := comap_map_eq φ _
      _ = ⁅U, U⁆ ⊔ N := by rw [hN]
  have h2 : ⁅U, U⁆ ≤ C ⊔ N := (commutator_mono le_top le_top).trans hC
  intro u hu
  obtain ⟨c, hc, n, hn, rfl⟩ := mem_sup_of_normal_right.mp ((sup_le h2 le_sup_right) (h1 hu))
  have hcU : c ∈ U := by
    simpa using mul_mem hu (inv_mem (hNU hn))
  exact mul_mem_sup (mem_inf.mpr ⟨hcU, hc⟩) hn

theorem uc22p22u_split_of_perfect {Q B : Type*} [Group Q] [Finite Q] [Group B] (φ : Q →* B)
    (N : Subgroup Q) [N.Normal] (hN : φ.ker = N)
    (h118 : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤
      centralizer ((((CFSG.fittingSubgroup ↥N).map N.subtype) ⊔ ((CFSG.layer ↥N).map N.subtype) :
        Subgroup Q) : Set Q) ⊔ (CFSG.layer ↥N).map N.subtype)
    (U : Subgroup Q) (hNU : N ≤ U) (hperf : ⁅U.map φ, U.map φ⁆ = U.map φ) :
    U ≤ (U ⊓ centralizer ((((CFSG.fittingSubgroup ↥N).map N.subtype) ⊔ ((CFSG.layer ↥N).map N.subtype) :
      Subgroup Q) : Set Q)) ⊔ N :=
  uc22p22u_le_inf_sup_of_perfect_map φ N hN _
    (h118.trans (sup_le_sup_left (map_subtype_le _) _)) U hNU hperf

theorem uc22p22u_layer_quotient_eq_top {Y : Type*} [Group Y] [Finite Y] (K P : Subgroup Y) [K.Normal]
    [P.Normal] (hY : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤) (hKP : ⁅(⊤ : Subgroup Y), K⁆ ≤ P)
    (hlayer : CFSG.layer (Y ⧸ K) = ⊤) : CFSG.layer (Y ⧸ P) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' P) := QuotientGroup.mk'_surjective P
  let g : Y ⧸ K →* Y ⧸ (K ⊔ P) :=
    QuotientGroup.map K (K ⊔ P) (MonoidHom.id Y) fun x hx => mem_sup_left hx
  have hg : Function.Surjective g := fun x => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(y : Y ⧸ K), rfl⟩
  have hA : CFSG.layer (Y ⧸ (K ⊔ P)) = ⊤ := CFSG.LocalCores.layer_eq_top_of_surjective hlayer g hg
  let f : Y ⧸ P →* Y ⧸ (K ⊔ P) :=
    QuotientGroup.map P (K ⊔ P) (MonoidHom.id Y) fun x hx => mem_sup_right hx
  have hf : Function.Surjective f := fun x => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(y : Y ⧸ P), rfl⟩
  have hKc : K.map (QuotientGroup.mk' P) ≤ center (Y ⧸ P) := by
    refine commutator_top_left_eq_bot_iff_le_center.mp ?_
    rw [← map_top_of_surjective _ hπ, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hKP
  have hker' : f.ker ≤ K.map (QuotientGroup.mk' P) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hπ x
    obtain ⟨k, hk, p, hp, rfl⟩ := mem_sup_of_normal_right.mp
      ((QuotientGroup.eq_one_iff y).mp (MonoidHom.mem_ker.mp hx))
    have hp1 : QuotientGroup.mk' P p = 1 := (QuotientGroup.eq_one_iff p).mpr hp
    refine ⟨k, hk, ?_⟩
    rw [map_mul, hp1, mul_one]
  have hperf : ⁅(⊤ : Subgroup (Y ⧸ P)), (⊤ : Subgroup (Y ⧸ P))⁆ = ⊤ := by
    have h := map_commutator (⊤ : Subgroup Y) ⊤ (QuotientGroup.mk' P)
    rw [hY, map_top_of_surjective _ hπ] at h
    exact h.symm
  exact uc22p22u_layer_eq_top_of_central_ext f hf (hker'.trans hKc) hperf hA

theorem uc22p22u_layer_bar_eq_top {Y : Type*} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal]
    (hY : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤)
    (hKY : ⁅(⊤ : Subgroup Y), K⁆ ≤ CFSG.pCore 2 Y) (hlayer : CFSG.layer (Y ⧸ K) = ⊤) :
    CFSG.layer (Y ⧸ CFSG.pCore 2 Y) = ⊤ :=
  uc22p22u_layer_quotient_eq_top K (CFSG.pCore 2 Y) hY hKY hlayer

end CFSG.LocalAnalysis.UniquenessCase.UC22
