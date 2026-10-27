module

public import CFSG.Quasithin.H13.L32AC47f
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

section Induced

variable {G X : Type*} [Group G] [Group X] {K N : Subgroup G} (π : ↥K →* X)
  (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ N)

include hker in
theorem map_conjK_eq_one {h : G} (hK : h ∈ Subgroup.normalizer (K : Set G))
    (hN : h ∈ Subgroup.normalizer (N : Set G)) (k : ↥K) (hk : π k = 1) : π (conjK hK k) = 1 := by
  rw [hker] at hk ⊢
  rw [conjK_apply]
  exact (Subgroup.mem_normalizer_iff.mp hN k).mp hk

noncomputable def indEndo {h : G} (hK : h ∈ Subgroup.normalizer (K : Set G))
    (hN : h ∈ Subgroup.normalizer (N : Set G)) : X →* X :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨π.comp (conjK hK), fun k hk => map_conjK_eq_one π hker hK hN k hk⟩

theorem indEndo_apply {h : G} (hK : h ∈ Subgroup.normalizer (K : Set G))
    (hN : h ∈ Subgroup.normalizer (N : Set G)) (k : ↥K) :
    indEndo π hπ hker hK hN (π k) = π (conjK hK k) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k

theorem indEndo_injective {h : G} (hK : h ∈ Subgroup.normalizer (K : Set G))
    (hN : h ∈ Subgroup.normalizer (N : Set G)) : Function.Injective (indEndo π hπ hker hK hN) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro a ha
  obtain ⟨k, rfl⟩ := hπ a
  rw [MonoidHom.mem_ker, indEndo_apply, hker, conjK_apply] at ha
  rw [hker]
  have := (Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normalizer (N : Set G)).inv_mem hN) _).mp ha
  simpa [mul_assoc] using this

variable [Finite X]

noncomputable def indAut {h : G} (hK : h ∈ Subgroup.normalizer (K : Set G))
    (hN : h ∈ Subgroup.normalizer (N : Set G)) : MulAut X :=
  MulEquiv.ofBijective (indEndo π hπ hker hK hN)
    (Finite.injective_iff_bijective.mp (indEndo_injective π hπ hker hK hN))

theorem indAut_apply {h : G} (hK : h ∈ Subgroup.normalizer (K : Set G))
    (hN : h ∈ Subgroup.normalizer (N : Set G)) (k : ↥K) :
    indAut π hπ hker hK hN (π k) = π (conjK hK k) :=
  indEndo_apply π hπ hker hK hN k

noncomputable def indHom {Y : Subgroup G} (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) : ↥Y →* MulAut X where
  toFun y := indAut π hπ hker (hYK y.2) (hYN y.2)
  map_one' := by
    apply MulEquiv.ext
    intro a
    obtain ⟨k, rfl⟩ := hπ a
    rw [indAut_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show ((1 : ↥Y) : G) * k * ((1 : ↥Y) : G)⁻¹ = k
    simp
  map_mul' y y' := by
    apply MulEquiv.ext
    intro a
    obtain ⟨k, rfl⟩ := hπ a
    rw [MulAut.mul_apply, indAut_apply, indAut_apply, indAut_apply]
    congr 1
    exact Subtype.ext (by simp only [conjK_apply, Subgroup.coe_mul]; group)

theorem indHom_apply {Y : Subgroup G} (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (y : ↥Y) (k : ↥K) :
    indHom π hπ hker hYK hYN y (π k) = π (conjK (hYK y.2) k) :=
  indAut_apply π hπ hker _ _ k

end Induced

theorem mem_inner_of_odd_orderOf {X : Type*} [Group X] (hout : IsPGroup 2 (Outer X))
    {α : MulAut X} (hα : Odd (orderOf α)) : α ∈ inner X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hout (QuotientGroup.mk α)
  have h1 : orderOf (QuotientGroup.mk α : Outer X) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (QuotientGroup.mk α : Outer X) ∣ orderOf α :=
    orderOf_map_dvd (QuotientGroup.mk' (inner X)) α
  have h3 : orderOf (QuotientGroup.mk α : Outer X) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hα))) h1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end CFSG.Quasithin.H13.L32A.C
