module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCases
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem r5b_isElementaryAbelian_of_isElemAbelian {p : ℕ} {K : Type*} [Group K] {E : Subgroup K}
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.IsElementaryAbelian p E := by
  unfold CFSG.Open.IsElemAbelian at hE
  obtain ⟨hc, hexp⟩ := hE
  exact
    { toIsMulCommutative := hc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hexp x x.2) }

theorem r5b_isElemAbelian_of_isElementaryAbelian {p : ℕ} {K : Type*} [Group K] {E : Subgroup K}
    [CFSG.IsElementaryAbelian p E] : CFSG.Open.IsElemAbelian p E := by
  unfold CFSG.Open.IsElemAbelian
  exact ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩

theorem r5b_map_normalizer_mem {K G : Type*} [Group K] [Group G] {f : K →* G}
    (hf : Function.Injective f) {T : Subgroup K} {a : K}
    (ha : a ∈ Subgroup.normalizer (T : Set K)) :
    f a ∈ Subgroup.normalizer ((T.map f : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at ha ⊢
  intro h
  by_cases hh : h ∈ f.range
  · obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hh
    have e : f a * f k * (f a)⁻¹ = f (a * k * a⁻¹) := by simp only [map_mul, map_inv]
    rw [e, Subgroup.mem_map_iff_mem hf, Subgroup.mem_map_iff_mem hf]
    exact ha k
  · constructor
    · intro hm
      obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp hm
      exact absurd (MonoidHom.mem_range.mpr ⟨k, hk⟩) hh
    · intro hm
      obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp hm
      exfalso
      apply hh
      refine MonoidHom.mem_range.mpr ⟨a⁻¹ * k * a, ?_⟩
      rw [map_mul, map_mul, map_inv, hk]
      group

theorem false_of_elemAbelian_cube {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hlr : CFSG.Assembly.RankThreeEven.localRank p G < 3)
    {A T : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A) (hA3 : Nat.card A = p ^ 3)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) : False := by
  have hel : CFSG.IsElementaryAbelian p A := r5b_isElementaryAbelian_of_isElemAbelian hA
  have h1 : CFSG.pRank p A ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
    CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ.pRank_le_localRank_of_le_normalizer hp hT hT2 hAT
  have h2 : CFSG.pRank p A = 3 := CFSG.pRank_eq_of_card_eq_pow hp.one_lt hA3
  omega

theorem hno_of_localRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hlr : CFSG.Assembly.RankThreeEven.localRank p G < 3) (M : Subgroup G) :
    ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M) := by
  intro A T hA hA3 hT hT2 hAT
  haveI : Fact p.Prime := ⟨hp⟩
  have hAel : CFSG.IsElementaryAbelian p A := r5b_isElementaryAbelian_of_isElemAbelian hA
  have hAm : CFSG.IsElementaryAbelian p (A.map M.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine false_of_elemAbelian_cube hp hlr (A := A.map M.subtype) (T := T.map M.subtype)
    r5b_isElemAbelian_of_isElementaryAbelian ?_ ?_ ?_ ?_
  · rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hA3
  · exact fun h => hT ((Subgroup.map_eq_bot_iff_of_injective T M.subtype_injective).mp h)
  · exact hT2.map M.subtype
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact r5b_map_normalizer_mem M.subtype_injective (hAT ha)

end CFSG.RankThree.PartTwo.Sec13.F135Last
