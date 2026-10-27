module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

private theorem s7FixedCoset_normalAction {G : Type*} [Group G] {A P B : Subgroup G}
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    ∃ σ : ↥A →* MulAut ↥P,
      (∀ (a : ↥A) (x : ↥P), (((σ a) x : ↥P) : G) = (a : G) * (x : G) * (a : G)⁻¹) ∧
      ∀ a : ↥A, (B.subgroupOf P).map (σ a).toMonoidHom = B.subgroupOf P := by
  let σ : ↥A →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP)
  have hcoe (a : ↥A) (x : ↥P) :
      (((σ a) x : ↥P) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    rw [show σ a = P.normalizerMonoidHom (Subgroup.inclusion hAP a) from rfl,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  refine ⟨σ, hcoe, ?_⟩
  intro a
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : G) ∈ B at hy
    change (((σ a) y : ↥P) : G) ∈ B
    rw [hcoe a y]
    exact (Subgroup.mem_normalizer_iff.mp (hAB a.2) (y : G)).mp hy
  · intro hx
    change (x : G) ∈ B at hx
    refine ⟨(σ a)⁻¹ x, ?_, (σ a).apply_symm_apply x⟩
    change ((((σ a)⁻¹ x : ↥P)) : G) ∈ B
    have hcoe' : ((((σ a)⁻¹ x : ↥P)) : G) = (a : G)⁻¹ * (x : G) * (a : G) := by
      rw [show (σ a)⁻¹ = σ (a⁻¹) from (map_inv σ a).symm]
      rw [hcoe (a⁻¹) x]
      simp
    rw [hcoe']
    simpa using (Subgroup.mem_normalizer_iff.mp (hAB (A.inv_mem a.2)) (x : G)).mp hx

private theorem s7FixedCoset_quotientAction {G : Type*} [Group G] {A P B : Subgroup G}
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    [hN : (B.subgroupOf P).Normal] :
    ∃ (σ : ↥A →* MulAut ↥P) (τ : ↥A →* MulAut (↥P ⧸ B.subgroupOf P)),
      (∀ (a : ↥A) (x : ↥P), (((σ a) x : ↥P) : G) = (a : G) * (x : G) * (a : G)⁻¹) ∧
      ∀ (a : ↥A) (y : ↥P),
        τ a (QuotientGroup.mk y) = QuotientGroup.mk ((σ a) y) := by
  classical
  let N : Subgroup ↥P := B.subgroupOf P
  have hNnormal : N.Normal := hN
  obtain ⟨σ, hcoe, hmap⟩ := s7FixedCoset_normalAction hAP hAB
  let τ : ↥A →* MulAut (↥P ⧸ N) :=
    { toFun := fun a => QuotientGroup.congr N N (σ a) (by simpa using hmap a)
      map_one' := by
        ext x
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N x
        change QuotientGroup.mk' N ((σ 1) t) = QuotientGroup.mk' N t
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        ext x
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N x
        change QuotientGroup.mk' N ((σ (a * b)) t) =
          QuotientGroup.mk' N ((σ a) ((σ b) t))
        rw [map_mul]
        rfl }
  exact ⟨σ, τ, hcoe, fun a y => rfl⟩

theorem exists_fixed_coset_of_pGroup {G : Type} [Group G] [Finite G] {A P B : Subgroup G}
    (hA : IsPGroup 3 A) (hP : IsPGroup 3 P) (hBP : B ≤ P) (hBn : (B.subgroupOf P).Normal)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hne : B ≠ P) :
    ∃ x ∈ P, x ∉ B ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ B := by
  classical
  let N : Subgroup ↥P := B.subgroupOf P
  have hNnormal : (B.subgroupOf P).Normal := hBn
  obtain ⟨σ, τ, hcoe, hτ⟩ := s7FixedCoset_quotientAction hAP hAB
  let mulActionInst : MulAction ↥A (↥P ⧸ N) := MulAction.compHom _ τ
  have hsmul : ∀ (a : ↥A) (x : ↥P ⧸ N), a • x = τ a x := fun _ _ => rfl
  have hcardΩ : Nat.card (↥P ⧸ N) ≠ 1 := by
    intro h1
    have hidx : N.index = 1 := (Subgroup.index_eq_card (H := N)).trans h1
    have htop : N = ⊤ := Subgroup.index_eq_one.mp hidx
    have hle : P ≤ B := Subgroup.subgroupOf_eq_top.mp htop
    exact hne (le_antisymm hBP hle)
  have hdvd : 3 ∣ Nat.card (↥P ⧸ N) := by
    rcases (hP.to_quotient N).card_eq_or_dvd with h | h
    · exact absurd h hcardΩ
    · exact h
  have h1fix : (1 : ↥P ⧸ N) ∈ MulAction.fixedPoints ↥A (↥P ⧸ N) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    rw [hsmul]
    exact map_one (τ a)
  obtain ⟨b, hb, hbne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hA (↥P ⧸ N) hdvd h1fix
  rw [MulAction.mem_fixedPoints] at hb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · intro hyB
    exact hbne ((QuotientGroup.eq_one_iff (N := N) y).mpr
      (Subgroup.mem_subgroupOf.mpr hyB)).symm
  · intro a ha
    have hfixa : τ ⟨a, ha⟩ (QuotientGroup.mk y) = QuotientGroup.mk y := by
      have h := hb ⟨a, ha⟩
      rwa [hsmul] at h
    rw [hτ] at hfixa
    have hmemN : ((σ ⟨a, ha⟩) y)⁻¹ * y ∈ N := (QuotientGroup.eq (s := N)).mp hfixa
    have hconjN : (σ ⟨a, ha⟩) y * y⁻¹ ∈ N := by
      have h := hNnormal.conj_mem (((σ ⟨a, ha⟩) y)⁻¹ * y)⁻¹ (N.inv_mem hmemN) y
      convert h using 1
      group
    convert Subgroup.mem_subgroupOf.mp hconjN using 1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe ⟨a, ha⟩ y]

end CFSG.StandardType.FrameRoute.FS81

end
