module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcAssembly
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld.ExceptionalOrders

namespace TwE6Toral

theorem not_dvd_mul_geomSums_twistedE6 {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) :
    ¬ p ∣ q ^ 36 * (geomSum 2 2 q * geomSum 3 2 q *
      (geomSum 2 5 q * geomSum 2 3 q * geomSum 2 1 q) *
        (geomSum 2 9 q * geomSum 2 6 q * geomSum 2 4 q * geomSum 3 1 q)) := by
  have hq1 := TableBExc.cast_eq_one_of_dvd_sub_one hq hpq
  have h1152 : ¬ p ∣ 1152 := by
    intro h
    have h' : p ∣ 2 ^ 7 * 3 ^ 2 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
      omega
  rw [← ZMod.natCast_eq_zero_iff] at h1152 ⊢
  intro h
  apply h1152
  rw [← h]
  push_cast
  simp only [TableBExc.geomSum_cast hq1, hq1, one_pow]
  norm_num

section Index

variable {K : Type} [Field K] [Finite K] {σ : K →+* K}

theorem index_graphFixedRootTorus_E6 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).index =
      (2 ^ f) ^ 36 * (geomSum 2 2 (2 ^ f) * geomSum 3 2 (2 ^ f) *
        (geomSum 2 5 (2 ^ f) * geomSum 2 3 (2 ^ f) * geomSum 2 1 (2 ^ f)) *
          (geomSum 2 9 (2 ^ f) * geomSum 2 6 (2 ^ f) * geomSum 2 4 (2 ^ f) *
            geomSum 3 1 (2 ^ f))) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := card_orbitField (t := TwistTag.E6) Nat.prime_two hf hK hσ
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6,
    ← graphFixedRootTorus_eq_compatTorus hsurj] at hC
  have hcard := Subgroup.card_mul_index ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (graphFixedRootTorus_le TwistTag.E6 K σ)).toEquiv, hC, mul_assoc] at hcard
  have : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard

theorem not_dvd_index_graphFixedRootTorus_E6 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1) :
    ¬ p ∣ ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).index := by
  rw [index_graphFixedRootTorus_E6 hf hK hσ]
  exact not_dvd_mul_geomSums_twistedE6 hp hp5 Nat.one_le_two_pow hpq

end Index

section Toral

@[expose] def twTorusPow (K : Type) [Field K] (σ : K →+* K) (p : ℕ) :
    Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) where
  carrier := {g | (g : ModGL TwistTag.E6.tag K) ∈ torusGroup TwistTag.E6.tag K ∧ g ^ p = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    have hc : Commute a b := Subtype.ext
      (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha.1)
        (torusGroup_le_diagonalGroup hb.1))
    rw [hc.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem isElemAbelian_twTorusPow (K : Type) [Field K] (σ : K →+* K) (p : ℕ) :
    IsElemAbelian p (twTorusPow K σ p) :=
  ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (mul_comm_of_mem_diagonalGroup
    (torusGroup_le_diagonalGroup a.2.1) (torusGroup_le_diagonalGroup b.2.1)))⟩⟩,
    fun _ hx => hx.2⟩

variable {K : Type} [Field K] [Finite K] {σ : K →+* K}

theorem exists_conj_le_twTorusPow {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((graphFixedRootTorus TwistTag.E6 K σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).index)
    {E : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)} (hE : IsElemAbelian p E) :
    ∃ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      E.map (MulAut.conj g).toMonoidHom ≤ twTorusPow K σ p := by
  have : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx
    (TableB.isPGroup_of_isElemAbelian hE)
  refine ⟨g, fun x hx => ⟨?_, ?_⟩⟩
  · have hx' : (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootTorus TwistTag.E6 K σ :=
      Subgroup.mem_subgroupOf.mp (hg hx)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx').1).1
  · obtain ⟨e, he, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 e he, map_one]

theorem ggOrdPToralMax_graphFixedRootGroup_E6 {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1) :
    GGOrdPToralMax ↥(graphFixedRootGroup TwistTag.E6 K σ) p := by
  have : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  exact OrdPInnerExc.ggOrdPToralMax_of_conj_le (isElemAbelian_twTorusPow K σ p) fun A hA =>
    exists_conj_le_twTorusPow hp (not_dvd_index_graphFixedRootTorus_E6 hf hK hσ hp hp5 hpq) hA

end Toral

section Univ

theorem ggOrdPToralMax_twistedE6_split {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f - 1) : GGOrdPToralMax (twistedE6Group 2 f) p := by
  obtain ⟨π, hπ, hkerπ, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  have hC := ggOrdPToralMax_graphFixedRootGroup_E6 hf (card_galoisField_two_mul f hf)
    (frobQ_apply 2 f) hp hp5 hpq
  have : Finite (Module.End (GaloisField 2 (2 * f))
    (RootModule TwistTag.E6.tag (GaloisField 2 (2 * f)))) :=
    Module.finite_of_finite (GaloisField 2 (2 * f))
  refine OrdPInnerExc.ggOrdPToralMax_of_surjective hp hπ hkerπ.le ?_ hC
  rw [hkerπ]
  exact OrdPInnerExc.coprime_card_center_twistedE6 ggTwE6CenterTrivialInput_holds hf hp
    fun h => absurd h.1 (by omega)

end Univ

end TwE6Toral

section Inputs

@[expose] def GGOrdPToralTwE6Rest : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1) → ¬ (5 ≤ p ∧ p ∣ 2 ^ f - 1) →
    (∃ A : Subgroup (twistedE6Group 2 f), IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (twistedE6Group 2 f) p

theorem ggOrdPToralTwE6Input_of_rest (h : GGOrdPToralTwE6Rest) : GGOrdPToralTwE6Input := by
  intro f p hf hp hp2 h3 hA
  by_cases hs : 5 ≤ p ∧ p ∣ 2 ^ f - 1
  · exact TwE6Toral.ggOrdPToralMax_twistedE6_split hf hp hs.1 hs.2
  · exact h f p hf hp hp2 h3 hs hA

end Inputs

end CFSG.StandardType
