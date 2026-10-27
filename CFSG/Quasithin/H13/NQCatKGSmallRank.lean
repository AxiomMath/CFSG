module

public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.RankThree.PartOne.KLC.TriTorus
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Quasithin

theorem isElemAbelianOfRank_of_card_prime {V : Type} [Group V] [Finite V] {p n : ℕ}
    [hp : Fact p.Prime] (hc : ∀ x y : V, x * y = y * x) (hpow : ∀ x : V, x ^ p = 1)
    (hcard : Nat.card V = p ^ n) : IsElemAbelianOfRank p n V := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have h2 : ∀ x : Additive V, (p : ℕ) • x = 0 := by
    intro x
    change Additive.ofMul (Additive.toMul x ^ p) = 0
    rw [hpow]
    rfl
  let hM : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule h2
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have hF : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
  have hd : Module.finrank (ZMod p) (Additive V) = n := by
    have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive V) _ _ hM hF
    have hcard' : Nat.card (Additive V) = p ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  have hFree : Module.Free (ZMod p) (Additive V) := Module.Free.of_divisionRing _ _
  let b := @Module.finBasis (ZMod p) (Additive V) _ _ hM hFree _ hF
  let e : Additive V ≃ₗ[ZMod p] (Fin n → ZMod p) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

theorem exists_isElemAbelianOfRank_two {X : Type} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    ∃ E : Subgroup X, IsElemAbelianOfRank p 2 ↥E := by
  obtain ⟨A, -, ⟨hAc, hAp⟩, hcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (⊤ : Subgroup X)
  have hdvd : p ^ 2 ∣ Nat.card A := hcard ▸ pow_dvd_pow p h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨K.map A.subtype,
    IsElemAbelianOfRank.of_mulEquiv (K.equivMapOfInjective A.subtype A.subtype_injective)
      (isElemAbelianOfRank_of_card_prime (fun x y => ?_) (fun x => ?_) hK)⟩
  · exact Subtype.ext (hAc.is_comm.comm x.1 y.1)
  · apply Subtype.ext
    apply Subtype.ext
    simpa using hAp _ x.1.2

theorem j2_exists_isElemAbelianOfRank_three_two
    (S : Type) [Group S] (h : IsSporadic .J2 S) :
    ∃ E : Subgroup S, IsElemAbelianOfRank 3 2 ↥E := by
  obtain ⟨e⟩ := h
  have : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  obtain ⟨E, hE⟩ := exists_isElemAbelianOfRank_two
    (CFSG.RankThree.ThinCatalog.two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy)
  exact ⟨E.map e.symm.toMonoidHom, IsElemAbelianOfRank.of_mulEquiv (e.symm.subgroupMap E) hE⟩

theorem trialityD4_two_exists_isElemAbelianOfRank_seven_two
    (S : Type) [Group S] (h : Is3D4 2 1 S) : ∃ E : Subgroup S, IsElemAbelianOfRank 7 2 ↥E := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two le_rfl h.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 3 := hK
  have h2 := CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi36 (ℓ := 2) le_rfl hK' σ hσ
    (ε := 1) (Or.inl rfl) (p := 7) (by norm_num) (by norm_num)
  have : Finite (CFSG.Blueprint.Chevalley.ModGL
      CFSG.Blueprint.Chevalley.TwistTag.D4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  obtain ⟨E, hE⟩ := exists_isElemAbelianOfRank_two h2
  exact ⟨E.map e.symm.toMonoidHom, IsElemAbelianOfRank.of_mulEquiv (e.symm.subgroupMap E) hE⟩

end CFSG.Quasithin.H13.NQCat
