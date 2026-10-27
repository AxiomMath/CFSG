module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.EmptyFaithful.S151bW3Five

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

private theorem card_mul_dvd_of_commute_of_inf_eq_bot {Γ : Type*} [Group Γ] {L R K : Subgroup Γ}
    (hL : L ≤ K) (hR : R ≤ K) (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) (hLR : L ⊓ R = ⊥) :
    Nat.card L * Nat.card R ∣ Nat.card K := by
  have hcomm : ∀ (x : L) (y : R), Commute (L.subtype x) (R.subtype y) := fun x y => hc x x.2 y y.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod L.subtype R.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨L.subtype_injective, R.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hLR
  calc Nat.card L * Nat.card R = Nat.card (L × R) := (Nat.card_prod _ _).symm
    _ = Nat.card (MonoidHom.noncommCoprod L.subtype R.subtype hcomm).range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ = Nat.card (L ⊔ R : Subgroup Γ) := by
        rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    _ ∣ Nat.card K := Subgroup.card_dvd_of_le (sup_le hL hR)

namespace SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

omit [Finite W] in
private theorem card_A₀_eq_hundred : Nat.card (S.A₁ ⊔ S.A₂ : Subgroup (MulAut W)) = 100 := by
  rw [← S.range_ι, ← Nat.card_congr (MonoidHom.ofInjective S.ι_injective).toEquiv, Nat.card_prod,
    Nat.card_eq_fintype_card, DihedralGroup.card]

omit [Finite W] in
private theorem orderOf_conj_a₂ : orderOf (S.τ * S.a₂ * S.τ⁻¹) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [conj_pow, S.a₂_pow (Or.inr rfl), mul_one, mul_inv_cancel]
  · intro h
    refine S.a₂_ne_one (Or.inr rfl) ?_
    have h' : S.τ⁻¹ * (S.τ * S.a₂ * S.τ⁻¹) * S.τ = S.a₂ := by group
    rw [← h', h]
    group

omit [Finite W] in
private theorem four_dvd_card_sylowTwo {P : Subgroup (MulAut W)}
    (hS2 : IsSylowTwoOf P (S.A₁ ⊔ S.A₂)) : 4 ∣ Nat.card P := by
  obtain ⟨hle, -, hodd⟩ := hS2
  have h1 := Subgroup.card_mul_index (P.subgroupOf (S.A₁ ⊔ S.A₂))
  rw [S.card_A₀_eq_hundred, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  have hcop : Nat.Coprime 4 (P.subgroupOf (S.A₁ ⊔ S.A₂)).index := by
    have := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    simpa using this
  exact hcop.dvd_of_dvd_mul_right (by rw [h1]; norm_num)

theorem A₀_eq_closure {Tb : Subgroup (MulAut W)}
    (hS2 : IsSylowTwoOf (Tb ⊓ (S.A₁ ⊔ S.A₂)) (S.A₁ ⊔ S.A₂)) :
    S.A₁ ⊔ S.A₂ = Subgroup.closure
      ({S.a₂, S.τ * S.a₂ * S.τ⁻¹} ∪
        ((Tb ⊓ (S.A₁ ⊔ S.A₂) : Subgroup (MulAut W)) : Set (MulAut W))) := by
  set K : Subgroup (MulAut W) := Subgroup.closure
    ({S.a₂, S.τ * S.a₂ * S.τ⁻¹} ∪
      ((Tb ⊓ (S.A₁ ⊔ S.A₂) : Subgroup (MulAut W)) : Set (MulAut W)))
  have hb₂ : S.a₂ ∈ K := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hb₁ : S.τ * S.a₂ * S.τ⁻¹ ∈ K := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hPK : Tb ⊓ (S.A₁ ⊔ S.A₂) ≤ K := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hb₁A : S.τ * S.a₂ * S.τ⁻¹ ∈ S.A₁ := S.τ₂₁ _ S.a₂_mem
  have hKle : K ≤ S.A₁ ⊔ S.A₂ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ((rfl | rfl) | hx)
    · exact Subgroup.mem_sup_right S.a₂_mem
    · exact Subgroup.mem_sup_left hb₁A
    · exact hx.2
  have h25 : 25 ∣ Nat.card K := by
    have hL : Subgroup.zpowers (S.τ * S.a₂ * S.τ⁻¹) ≤ S.A₁ := Subgroup.zpowers_le.mpr hb₁A
    have hR : Subgroup.zpowers S.a₂ ≤ S.A₂ := Subgroup.zpowers_le.mpr S.a₂_mem
    have h := card_mul_dvd_of_commute_of_inf_eq_bot (K := K)
      (Subgroup.zpowers_le.mpr hb₁) (Subgroup.zpowers_le.mpr hb₂)
      (fun x hx y hy => S.comm x (hL hx) y (hR hy))
      (le_bot_iff.mp ((inf_le_inf hL hR).trans S.inf.le))
    rwa [Nat.card_zpowers, Nat.card_zpowers, S.orderOf_conj_a₂, S.orderOf_a₂_five] at h
  have h4 : 4 ∣ Nat.card K := (S.four_dvd_card_sylowTwo hS2).trans (Subgroup.card_dvd_of_le hPK)
  have h100 : 100 ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h25 h4)
  have hfin : Finite (S.A₁ ⊔ S.A₂ : Subgroup (MulAut W)) :=
    Nat.finite_of_card_ne_zero (by rw [S.card_A₀_eq_hundred]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hKle (by rw [S.card_A₀_eq_hundred]; exact h100)).symm

end SixData151b

end CFSG.Quasithin
