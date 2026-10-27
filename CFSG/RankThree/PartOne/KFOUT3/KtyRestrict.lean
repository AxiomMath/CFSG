module

public import CFSG.RankThree.PartOne.S12.Sec12Restrict
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne

section Restrict

variable {G : Type} [Group G] [Finite G] {c : G} {L E F : Subgroup G}

omit [Finite G] in
theorem pow_conjAut_eq_one_iff (E : Subgroup G) {x : G} (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (n : ℕ) : (E.normalizerMonoidHom ⟨x, hxE⟩) ^ n = 1 ↔ ∀ e ∈ E, x ^ n * e * (x ^ n)⁻¹ = e := by
  rw [← map_pow]
  constructor
  · intro h e he
    have := congrArg (fun φ : MulAut E => ((φ ⟨e, he⟩ : E) : G)) h
    simpa using this
  · intro h
    ext e
    exact h e e.2

omit [Finite G] in
theorem pow_centralizes_iff (R : Sec12Three.Restr c L E F) {x : G} (hxL : x ∈ L) (n : ℕ) :
    (∀ e ∈ E, x ^ n * e * (x ^ n)⁻¹ = e) ↔ ∀ f ∈ F, x ^ n * f * (x ^ n)⁻¹ = f := by
  constructor
  · intro h f hf
    exact h f (R.F_le_E hf)
  · intro h e he
    obtain ⟨f, hf, i, rfl⟩ := R.exists_mul_zpow he
    have h1 : x ^ n * (f * c ^ i) * (x ^ n)⁻¹ =
        (x ^ n * f * (x ^ n)⁻¹) * (x ^ n * c ^ i * (x ^ n)⁻¹) := by group
    rw [h1, R.conj_zpow (L.pow_mem hxL n) i, h f hf]

omit [Finite G] in
theorem orderOf_conjAut_eq (R : Sec12Three.Restr c L E F) {x : G} (hxL : x ∈ L)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxF : x ∈ Subgroup.normalizer (F : Set G)) :
    orderOf (E.normalizerMonoidHom ⟨x, hxE⟩) = orderOf (F.normalizerMonoidHom ⟨x, hxF⟩) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [pow_conjAut_eq_one_iff E hxE n, pow_conjAut_eq_one_iff F hxF n, pow_centralizes_iff R hxL n]

omit [Finite G] in
theorem isAutReflection_restrict {p : ℕ} (R : Sec12Three.Restr c L E F) {x : G} (hxL : x ∈ L)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxF : x ∈ Subgroup.normalizer (F : Set G)) :
    IsAutReflection p E (E.normalizerMonoidHom ⟨x, hxE⟩) ↔
      IsAutReflection p F (F.normalizerMonoidHom ⟨x, hxF⟩) := by
  have hmoved := R.autMovedInG_eq (R.comm x hxL).symm hxE hxF
  have hcard : Nat.card (autMoved E (E.normalizerMonoidHom ⟨x, hxE⟩)) =
      Nat.card (autMoved F (F.normalizerMonoidHom ⟨x, hxF⟩)) := by
    rw [← Sec12Three.natCard_autMovedInG, ← Sec12Three.natCard_autMovedInG, hmoved]
  unfold IsAutReflection
  rw [orderOf_conjAut_eq R hxL hxE hxF, hcard]

omit [Finite G] in
theorem eq_of_F_actions (R : Sec12Three.Restr c L E F) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (hxF : x ∈ Subgroup.normalizer (F : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (h : F.normalizerMonoidHom ⟨x, hxF⟩ = F.normalizerMonoidHom ⟨y, hyF⟩) :
    E.normalizerMonoidHom ⟨x, hxE⟩ = E.normalizerMonoidHom ⟨y, hyE⟩ := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  obtain ⟨f, hf, i, hfi⟩ := R.exists_mul_zpow e.2
  show x * (e : G) * x⁻¹ = y * (e : G) * y⁻¹
  have hfxy : x * f * x⁻¹ = y * f * y⁻¹ := by
    have := congrArg (fun φ : MulAut F => ((φ ⟨f, hf⟩ : F) : G)) h
    simpa using this
  rw [hfi]
  have h1 : ∀ u : G, u ∈ L → u * (f * c ^ i) * u⁻¹ = (u * f * u⁻¹) * c ^ i := by
    intro u hu
    calc u * (f * c ^ i) * u⁻¹ = (u * f * u⁻¹) * (u * c ^ i * u⁻¹) := by group
      _ = (u * f * u⁻¹) * c ^ i := by rw [R.conj_zpow hu i]
  rw [h1 x hxL, h1 y hyL, hfxy]

end Restrict

end CFSG.RankThree.PartOne.KFOUT3
