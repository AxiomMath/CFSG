module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne.K1214

open Subgroup

@[expose] def SylowShape (p r e : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ S : Subgroup X, IsPGroup p ↥S → ¬ p ∣ S.index →
    Nonempty (↥S ≃* (Fin r → Multiplicative (ZMod (p ^ e))))

theorem SylowShape.of_mulEquiv {p r e : ℕ} {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (h : SylowShape p r e Y) : SylowShape p r e X := by
  intro S hS hidx
  have hS' : IsPGroup p ↥(S.map (φ : X →* Y)) :=
    hS.of_equiv (Subgroup.equivMapOfInjective S (φ : X →* Y) φ.injective)
  have hidx' : ¬ p ∣ (S.map (φ : X →* Y)).index := by
    rwa [Subgroup.index_map_equiv S φ]
  obtain ⟨e⟩ := h _ hS' hidx'
  exact ⟨(Subgroup.equivMapOfInjective S (φ : X →* Y) φ.injective).trans e⟩

theorem SylowShape.of_witness {p r e : ℕ} {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    {T : Subgroup X} (hT : IsPGroup p ↥T) (hidx : ¬ p ∣ T.index)
    (φ : ↥T ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) : SylowShape p r e X := by
  intro S hS hSidx
  have : Fact p.Prime := ⟨hp⟩
  let S' : Sylow p X := hS.toSylow hSidx
  let T' : Sylow p X := hT.toSylow hidx
  exact ⟨(Sylow.equiv S' T').trans φ⟩

theorem SylowShape.quotient {p r e : ℕ} {Γ : Type*} [Group Γ] [Finite Γ] (hp : p.Prime)
    (N : Subgroup Γ) [N.Normal] (hN : ¬ p ∣ Nat.card N) (h : SylowShape p r e Γ) :
    SylowShape p r e (Γ ⧸ N) := by
  have : Fact p.Prime := ⟨hp⟩
  intro Sb hSb hidx
  set π : Γ →* Γ ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  let S₀ : Sylow p Γ := Classical.arbitrary _
  set S : Subgroup Γ := (S₀ : Subgroup Γ) with hS
  obtain ⟨φ⟩ := h S S₀.isPGroup' S₀.not_dvd_index
  have hŜp : IsPGroup p ↥(S.map π) := S₀.isPGroup'.map π
  have hŜidx : ¬ p ∣ (S.map π).index := fun hd =>
    S₀.not_dvd_index (hd.trans (Subgroup.index_map_dvd S hsurj))
  have hNS : N ⊓ S = ⊥ := by
    have hp' : IsPGroup p ↥(N ⊓ S) := S₀.isPGroup'.to_inf_right
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hp'
    have hdvd : Nat.card ↥(N ⊓ S) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    rw [hj] at hdvd
    by_cases hj0 : j = 0
    · subst hj0
      exact Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
    · exact absurd ((dvd_pow_self p hj0).trans hdvd) hN
  have hinj : Function.Injective (π.subgroupMap S) := by
    intro x y hxy
    have h1 : π (x : Γ) = π (y : Γ) := congrArg Subtype.val hxy
    have h2 : (x : Γ)⁻¹ * (y : Γ) ∈ N := QuotientGroup.eq.mp h1
    have h3 : (x : Γ)⁻¹ * (y : Γ) ∈ S := S.mul_mem (S.inv_mem x.2) y.2
    have h4 : (x : Γ)⁻¹ * (y : Γ) ∈ N ⊓ S := ⟨h2, h3⟩
    rw [hNS, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  let ψ : ↥S ≃* ↥(S.map π) := MulEquiv.ofBijective (π.subgroupMap S)
    ⟨hinj, MonoidHom.subgroupMap_surjective π S⟩
  let Ŝ' : Sylow p (Γ ⧸ N) := hŜp.toSylow hŜidx
  let S' : Sylow p (Γ ⧸ N) := hSb.toSylow hidx
  exact ⟨(Sylow.equiv Ŝ' S').symm.trans (ψ.symm.trans φ)⟩

end CFSG.RankThree.PartOne.K1214
