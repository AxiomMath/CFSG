module

public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup
open scoped Pointwise

variable {A H S : Type*} [Group A] [Group H] [Group S] [MulDistribMulAction A H]
  [MulDistribMulAction A S]

theorem smul_mem_commutator_of_invariant {K : Subgroup H} (hK : ∀ a : A, ∀ x ∈ K, a • x ∈ K)
    (a : A) {x : H} (hx : x ∈ ⁅K, K⁆) : a • x ∈ ⁅K, K⁆ := by
  have hmap : K.map (MulDistribMulAction.toMonoidHom H a) ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hK a y hy
  have hmem : a • x ∈ (⁅K, K⁆ : Subgroup H).map (MulDistribMulAction.toMonoidHom H a) :=
    ⟨x, hx, rfl⟩
  rw [map_commutator] at hmem
  exact commutator_mono hmap hmap hmem

theorem coprime_invariant_minimal_perfect_cover [Finite A] [Finite H] [Finite S] {p : ℕ}
    (hp : p.Prime) (hA : IsPGroup p A) (π : H →* S) (hπA : ∀ (a : A) (h : H), π (a • h) = a • π h)
    (hpH : ¬ p ∣ Nat.card H) (hS : Group.IsPerfect S)
    (K : Subgroup H) (hKinv : ∀ a : A, ∀ x ∈ K, a • x ∈ K) (hKS : K.map π = ⊤)
    (hKmin : ∀ K' : Subgroup H, K' ≤ K → (∀ a : A, ∀ x ∈ K', a • x ∈ K') → K'.map π = ⊤ →
      K' = K) :
    ⁅K, K⁆ = K ∧ (∀ a : A, ∀ x ∈ K ⊓ π.ker, a • x ∈ K ⊓ π.ker) ∧
      ((K ⊓ π.ker).subgroupOf K).Normal ∧ Group.IsNilpotent (K ⊓ π.ker : Subgroup H) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card (K ⊓ π.ker : Subgroup H) →
        ∀ R : Sylow r (K ⊓ π.ker : Subgroup H),
          (∀ R' : Sylow r (K ⊓ π.ker : Subgroup H), R' = R) ∧
          (((R : Subgroup (K ⊓ π.ker : Subgroup H)).map (K ⊓ π.ker).subtype).subgroupOf K).Normal ∧
          ∀ a : A, ∀ x ∈ (R : Subgroup (K ⊓ π.ker : Subgroup H)).map (K ⊓ π.ker).subtype,
            a • x ∈ (R : Subgroup (K ⊓ π.ker : Subgroup H)).map (K ⊓ π.ker).subtype := by
  set C : Subgroup H := K ⊓ π.ker with hCdef
  have hperf : ⁅K, K⁆ = K := by
    refine hKmin _ (commutator_le_of_le le_rfl le_rfl)
      (fun a x hx => smul_mem_commutator_of_invariant hKinv a hx) ?_
    rw [map_commutator, hKS]
    exact (Group.isPerfect_def.mp hS)
  have hCinv : ∀ a : A, ∀ x ∈ C, a • x ∈ C := fun a x hx =>
    ⟨hKinv a x hx.1, π.mem_ker.mpr (by rw [hπA, π.mem_ker.mp hx.2, smul_one])⟩
  have hKC : K ≤ normalizer (C : Set H) := by
    refine le_normalizer_of_forall_conj_mem fun k hk x hx => ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk)
    · exact π.normal_ker.conj_mem x hx.2 k
  have hCn : (C.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hKC
  have hpC : Nat.Coprime p (Nat.card C) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpH (h.trans (card_subgroup_dvd_card C))
  have : IsInvariant A H C := ⟨fun a g => ⟨fun hg => hCinv a g hg, fun hg => by
    have := hCinv a⁻¹ _ hg
    rwa [inv_smul_smul] at this⟩⟩
  have key : ∀ r : ℕ, r.Prime → ∃ R₀ : Sylow r C,
      K ≤ normalizer ((((R₀ : Subgroup C).map C.subtype : Subgroup H)) : Set H) ∧
      ∀ a : A, ∀ x ∈ (R₀ : Subgroup C).map C.subtype, a • x ∈ (R₀ : Subgroup C).map C.subtype := by
    intro r hr
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨R₀, -, hR₀⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p r hp hr hA
      hpC ⊥ IsPGroup.of_bot fun a x hx => by
        rw [mem_bot] at hx ⊢
        rw [hx, smul_one]
    have hR₀inv : ∀ a : A, ∀ x ∈ (R₀ : Subgroup C).map C.subtype,
        a • x ∈ (R₀ : Subgroup C).map C.subtype := by
      rintro a _ ⟨c, hc, rfl⟩
      have heq : a • (R₀ : Subgroup C) = (R₀ : Subgroup C) := by
        rw [← Sylow.pointwise_smul_def, hR₀ a]
      have hac : a • c ∈ (R₀ : Subgroup C) := by
        rw [← heq]
        exact Subgroup.smul_mem_pointwise_smul c a _ hc
      exact ⟨a • c, hac, rfl⟩
    refine ⟨R₀, ?_, hR₀inv⟩
    set M := K ⊓ normalizer ((((R₀ : Subgroup C).map C.subtype : Subgroup H)) : Set H) with hM
    have hMinv : ∀ a : A, ∀ x ∈ M, a • x ∈ M := fun a x hx =>
      ⟨hKinv a x hx.1, CFSG.SignalizerFunctor.Helpers.normalizer_invariant_of_invariant _ hR₀inv
        a x hx.2⟩
    have hMS : M.map π = ⊤ := by
      rw [eq_top_iff]
      intro s _
      obtain ⟨k, hk, rfl⟩ : s ∈ K.map π := hKS ▸ mem_top s
      obtain ⟨c, hc, hck⟩ := exists_mul_mem_normalizer_sylow R₀ (hKC hk)
      refine ⟨c * k, ⟨K.mul_mem hc.1 hk, hck⟩, ?_⟩
      rw [map_mul, π.mem_ker.mp hc.2, one_mul]
    rw [← hKmin M inf_le_left hMinv hMS]
    exact inf_le_right
  have hnormal : ∀ r : ℕ, r.Prime → ∀ R₀ : Sylow r C,
      K ≤ normalizer ((((R₀ : Subgroup C).map C.subtype : Subgroup H)) : Set H) →
        (R₀ : Subgroup C).Normal := by
    intro r hr R₀ hK
    refine ⟨fun x hx c => ?_⟩
    have hmem : ((c : H) * x * (c : H)⁻¹) ∈ (R₀ : Subgroup C).map C.subtype :=
      (mem_normalizer_iff.mp (hK c.2.1) x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = c * x * c⁻¹ := Subtype.ext hyx
    rw [← this]
    exact hy
  have huniq : ∀ r : ℕ, r.Prime → ∀ R R' : Sylow r C, R' = R := by
    intro r hr R R'
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨R₀, hR₀K, -⟩ := key r hr
    have := Sylow.unique_of_normal R₀ (hnormal r hr R₀ hR₀K)
    exact Subsingleton.elim R' R
  have hnil : Group.IsNilpotent C := by
    refine (Group.isNilpotent_of_finite_tfae (G := C)).out 4 1 |>.mp ?_
    intro r hr P
    obtain ⟨R₀, hR₀K, -⟩ := key r hr.out
    rw [huniq r hr.out R₀ P]
    exact hnormal r hr.out R₀ hR₀K
  refine ⟨hperf, hCinv, hCn, hnil, fun r hr _ R => ?_⟩
  obtain ⟨R₀, hR₀K, hR₀inv⟩ := key r hr
  rw [huniq r hr R₀ R]
  refine ⟨fun R' => huniq r hr R₀ R', ?_, hR₀inv⟩
  exact (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans inf_le_left)).mpr hR₀K

omit [MulDistribMulAction A S] in
theorem exists_minimal_invariant_cover [Finite H] (π : H →* S) (hπ : Function.Surjective π) :
    ∃ K : Subgroup H, (∀ a : A, ∀ x ∈ K, a • x ∈ K) ∧ K.map π = ⊤ ∧
      ∀ K' : Subgroup H, K' ≤ K → (∀ a : A, ∀ x ∈ K', a • x ∈ K') → K'.map π = ⊤ → K' = K := by
  set T : Set (Subgroup H) := {K | (∀ a : A, ∀ x ∈ K, a • x ∈ K) ∧ K.map π = ⊤} with hT
  have hTtop : (⊤ : Subgroup H) ∈ T :=
    ⟨fun _ _ _ => mem_top _, by rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ]⟩
  obtain ⟨K, hK, hmin⟩ :=
    (measure fun K : Subgroup H => Nat.card K).wf.has_min T ⟨⊤, hTtop⟩
  refine ⟨K, hK.1, hK.2, fun K' hK'K hK'inv hK'S => ?_⟩
  have hnot := hmin K' ⟨hK'inv, hK'S⟩
  exact eq_of_le_of_card_ge hK'K (not_lt.mp hnot)

end CFSG.RankThree.GroupTheory.SteinbergBM
