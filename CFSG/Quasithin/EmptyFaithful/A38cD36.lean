module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.Background.F918H0
public import CFSG.Quasithin.H13.VolIA38SLThree
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.EmptyFaithful.A38cOrders

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI

section Realizes

variable {V : Type*} [CommGroup V]

theorem FFModel.RealizesVia.injective_of_faithful_section {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

theorem realizes_nat_equiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : (FFModel.nat Γ).Realizes H U Z) : Nonempty (↥Γ ≃* ↥H) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨MulEquiv.ofBijective π ⟨hπ.injective_of_faithful_section (FFModel.nat_faithful _), hπ.1⟩⟩

theorem realizes_card_of_isSimpleGroup {D : FFModel} [IsSimpleGroup D.Gam]
    {H : Subgroup (MulAut V)} [Nontrivial ↥H] {U Z : Subgroup V} (h : D.Realizes H U Z) :
    Nat.card D.Gam = Nat.card ↥H := by
  obtain ⟨π, hπ⟩ := h
  exact card_eq_of_surjective_hom_of_simple π hπ.1

end Realizes

theorem nonempty_statedSL_three_zmod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (↥(StatedSL 3 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  exact ⟨(specialLinearGroupEquivStatedSL 3 K).symm.trans (slMulEquivOfRingEquiv ε 3)⟩

theorem d36A38_holds : D36A38 := by
  intro W _ L V hA h5
  have hS : IsSimpleGroup ↥L := isSimpleGroup_of_a38Types hA
  have hnt : Nontrivial ↥L := hS.toNontrivial
  have hcard : A38Order (Nat.card ↥L) := a38Order_card hA
  rcases h5 with ⟨n, K, _, _, hK, hreal⟩ | ⟨n, K, _, _, hK, hreal⟩ | hreal | ⟨K, _, _, hK, hreal⟩ |
    ⟨K, _, _, hK, hreal⟩ | ⟨α, hreal⟩
  ·
    obtain ⟨e⟩ := realizes_nat_equiv hreal
    have hn : n = 1 := a38TypesSLThree_holds ↥L K n hK ⟨e.symm⟩ hA
    subst hn
    have hK2 : Nat.card K = 2 := by simpa using hK
    obtain ⟨e'⟩ := nonempty_statedSL_three_zmod_two hK2
    exact ⟨isPSL_three_two_iff.mpr ⟨e.symm.trans e'⟩, K, inferInstance, inferInstance, hK, hreal⟩
  ·
    obtain ⟨e⟩ := realizes_nat_equiv hreal
    have hn : 1 ≤ n := by
      by_contra h0
      have h1 := Finite.one_lt_card (α := K)
      rw [hK, show n = 0 by omega] at h1
      simp at h1
    refine (a38Order_not_rankTwoOrder hcard ?_).elim
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ?_⟩)))
    rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow hK, ordBC_two_two_pow hn,
      ← pow_mul, ← pow_mul, mul_comm n 4, mul_comm n 2]
  ·
    have hs6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      Vol2.Ch10.SecA.isSimpleGroup_alt (by norm_num)
    have : IsSimpleGroup (FFModel.altDn 6).Gam := hs6
    have h360 := realizes_card_of_isSimpleGroup hreal
    have h360' : Nat.card ↥L = 360 := by
      rw [← h360]
      show Nat.card ↥(alternatingGroup (Fin 6)) = 360
      rw [Vol2.Ch10.SecA.card_alt 6 (by norm_num)]
      decide
    exact (not_a38Order_360 (h360' ▸ hcard)).elim
  ·
    obtain ⟨e⟩ := realizes_nat_equiv hreal
    have hK' : Nat.card K = 2 := by simpa using hK
    exact (not_a38Order_20160 (by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_four_of_two hK'] at hcard
      exact hcard)).elim
  ·
    obtain ⟨e⟩ := realizes_nat_equiv hreal
    have hK' : Nat.card K = 2 := by simpa using hK
    exact (not_a38Order_9999360 (by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_five_of_two hK'] at hcard
      exact hcard)).elim
  ·
    have hs7 : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      Vol2.Ch10.SecA.isSimpleGroup_alt (by norm_num)
    have : IsSimpleGroup (FFModel.a7Four α).Gam := hs7
    have h2520 := realizes_card_of_isSimpleGroup hreal
    have h2520' : Nat.card ↥L = 2520 := by
      rw [← h2520]
      show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
      rw [Vol2.Ch10.SecA.card_alt 7 (by norm_num)]
      decide
    exact (not_a38Order_2520 (h2520' ▸ hcard)).elim

end CFSG.Quasithin
