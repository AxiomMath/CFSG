module

public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec14.Concrete

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

@[expose] def KS152J2Gen : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ z : Γ, z ≠ 1 →
      (∃ S : Sylow 3 Γ, z ∈ (S : Subgroup Γ) ∧
        (S : Subgroup Γ) ≤ Subgroup.centralizer ({z} : Set Γ)) →
      ∀ Q F : Subgroup Γ, IsPGroup 2 Q → 64 ∣ Nat.card Q →
        F ≤ Subgroup.centralizer ({z} : Set Γ) → Group.IsPerfect F → Nat.card F = 60 →
          Q ⊔ F = ⊤

@[expose] def Step152GenTheta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Y M X : Subgroup G, Ctx152 A (lB A) Y M X →
    ∀ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A (lB A) X c L d p P T K S →
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∈
        scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2) →
      (aschbacherSolvableCore 3 ↥L).map L.subtype ≤
        (S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔ X

@[expose] def Step152GenS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Y M X : Subgroup G, Ctx152 A (lB A) Y M X →
    ∀ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A (lB A) X c L d p P T K S →
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∈
        scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2) →
      ∃ Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
        Q ≤ ((((S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔ X).subgroupOf L).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) ∧
        IsPGroup 2 Q ∧ 64 ∣ Nat.card Q

@[expose] def Step152GenX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Y M X : Subgroup G, Ctx152 A (lB A) Y M X →
    ∀ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A (lB A) X c L d p P T K S →
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∈
        scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2) →
      ∃ F : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
        F ≤ (X.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ∧
        Group.IsPerfect F ∧ Nat.card F = 60 ∧
        F ≤ Subgroup.centralizer ((((Subgroup.zpowers d).subgroupOf L).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) : Subgroup _) : Set _)

theorem kS152HJGen_of (hθ : Step152GenTheta) (hS : Step152GenS) (hX : Step152GenX)
    (hJ2 : KS152J2Gen) : KS152HJGen := by
  intro G _ _ A c L h Y M X hctx d p P T K S hD hSH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set J := (S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔ X with hJ
  obtain ⟨Q, hQJ, hQ2, hQ64⟩ := hS G A c L h Y M X hctx d p P T K S hD hSH
  obtain ⟨F, hFX, hFp, hF60, hFd⟩ := hX G A c L h Y M X hctx d p P T K S hD hSH
  have hθL := hθ G A c L h Y M X hctx d p P T K S hD hSH
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := hD.central_d
  set z : ↥L ⧸ θ := ρ ⟨d, hdL⟩ with hz
  have hd3 : d ^ 3 = 1 := h.isE27.1.2 d hD.mem_d
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hD.ne_d
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine ⟨S3.mapSurjective (QuotientGroup.mk'_surjective θ), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  have hFz : F ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine hFd.trans (Subgroup.centralizer_le ?_)
    rw [Set.singleton_subset_iff]
    exact ⟨⟨d, hdL⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers d), rfl⟩
  have htop := hJ2 (↥L ⧸ θ) hD.hj z hz1 hzc Q F hQ2 hQ64 hFz hFp hF60
  have hJbar : (J.subgroupOf L).map ρ = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine sup_le hQJ (hFX.trans (Subgroup.map_mono fun x hx => ?_))
    exact Subgroup.mem_subgroupOf.mpr ((le_sup_right : X ≤ J) (Subgroup.mem_subgroupOf.mp hx))
  intro l hl
  obtain ⟨j, hj, hjl⟩ : ρ ⟨l, hl⟩ ∈ (J.subgroupOf L).map ρ := hJbar ▸ Subgroup.mem_top _
  have hjθ : j⁻¹ * ⟨l, hl⟩ ∈ θ := by
    rw [← QuotientGroup.eq]
    exact hjl
  have h1 : ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ J := hθL ⟨_, hjθ, rfl⟩
  have h2 : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have h3 : l = (j : G) * ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h3]
  exact J.mul_mem h2 h1

end CFSG.RankThree.PartTwo.Sec15
