module

public import CFSG.LocalAnalysis.StandardType.GGE6OppCentre
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompQuasi
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMInput
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrders
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafComponent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinAbs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Helpers


private theorem e6_marking_conj {H : Type} [Group H] [Group.IsPerfect H] {f : ℕ} (hf : 1 ≤ f)
    {z : H}
    (hraw : LargeEvenRawDatum (⟨.E6, 0, f⟩ : LargeEvenLabel) fun R _ _ _ =>
      Nonempty (H ⧸ Subgroup.center H ≃* R)) :
    LargeEvenMarking H (fun lab _ _ I _ θ => lab = ⟨.E6, 0, f⟩ ∧
      ggInducedAut θ (MulAut.conj z) ∈ I) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, hQ⟩ := by
    simpa only [LargeEvenRawDatum, LargeEvenRecipeChevalley] using hraw
  let : Field K := hKfield
  let : Finite K := hKfin
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) .E6 2 f :=
    ⟨⟨Nat.prime_two, hf, rfl⟩, untwistedChevalleyModel_largeEven .E6 hKcard⟩
  have hsimple : IsSimpleGroup
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
    CFSG.Timmesfeld.isSimpleGroup_of_lieModel (Or.inr (Or.inl ⟨rfl, by decide, hchev⟩))
  obtain ⟨e⟩ := hQ
  have hntH : Nontrivial (H ⧸ Subgroup.center H) :=
    @Equiv.nontrivial (H ⧸ Subgroup.center H)
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) e.toEquiv
      hsimple.toNontrivial
  obtain ⟨a, b, hab⟩ :=
    exists_mul_ne_mul_centerQuot_of_perfect (Group.IsPerfect.commutator_eq_top) hntH
  refine ⟨Group.IsPerfect.commutator_eq_top, ⟨.E6, 0, f⟩, ⟨hf, rfl⟩, ?_⟩
  refine ⟨K, hKfield, hKfin, hKcard, ?_⟩
  refine ⟨hsimple,
    ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩, ?_⟩
  refine ⟨e, rfl, ?_⟩
  rw [tpq_ggInducedAut_conj]
  exact conj_mem_largeEvenChevIDImage (LargeEvenCartanE 6) K _ (e (QuotientGroup.mk z))

private theorem twE6_marking_conj {H : Type} [Group H] [Group.IsPerfect H] {f : ℕ} (hf : 1 ≤ f)
    {z : H}
    (hraw : LargeEvenRawDatum (⟨.twE6, 0, f⟩ : LargeEvenLabel) fun R _ _ _ =>
      Nonempty (H ⧸ Subgroup.center H ≃* R)) :
    LargeEvenMarking H (fun lab _ _ I _ θ => lab = ⟨.twE6, 0, f⟩ ∧
      ggInducedAut θ (MulAut.conj z) ∈ I) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, hQ⟩ := by
    simpa only [LargeEvenRawDatum, LargeEvenRecipeTwisted] using hraw
  let : Field K := hKfield
  let : Finite K := hKfin
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 f))
      .twistedE6 2 f :=
    ⟨⟨Nat.prime_two, hf, rfl⟩, twistedChevalleyModel_largeEven .E6 hKcard⟩
  have hsimple : IsSimpleGroup
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 f)) :=
    CFSG.Timmesfeld.isSimpleGroup_of_lieModel (Or.inr (Or.inl ⟨rfl, by decide, hchev⟩))
  obtain ⟨e⟩ := hQ
  have hntH : Nontrivial (H ⧸ Subgroup.center H) :=
    @Equiv.nontrivial (H ⧸ Subgroup.center H)
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 f)) e.toEquiv
      hsimple.toNontrivial
  obtain ⟨a, b, hab⟩ :=
    exists_mul_ne_mul_centerQuot_of_perfect (Group.IsPerfect.commutator_eq_top) hntH
  refine ⟨Group.IsPerfect.commutator_eq_top, ⟨.twE6, 0, f⟩, ⟨hf, rfl⟩, ?_⟩
  refine ⟨K, hKfield, hKfin, hKcard, ?_⟩
  refine ⟨hsimple,
    ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩, ?_⟩
  refine ⟨e, rfl, ?_⟩
  rw [tpq_ggInducedAut_conj]
  exact conj_mem_largeEvenChevIDImage (LargeEvenCartanE 6) K _ (e (QuotientGroup.mk z))

end Helpers

theorem ggTorsionDatum_conj_of_e6Opp
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H] {f : ℕ} (hf : 1 ≤ f)
    (hH : (GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1))
    {z : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H))) :
    GGTorsionDatum (fun lab => (lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
      (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1)) 3 (MulAut.conj z) J := by
  have hperf : commutator H = ⊤ := Group.IsPerfect.commutator_eq_top
  have hz_center : z ∉ Subgroup.center H := by
    intro hz
    apply not_three_dvd_card_center_of_e6Opp (H := H) hf hH
    have hle : Subgroup.zpowers z ≤ Subgroup.center H := Subgroup.zpowers_le.mpr hz
    have hdvd : orderOf z ∣ Nat.card (Subgroup.center H) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers] at h1
    have hord : orderOf z = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hz3 hz1
    rwa [hord] at hdvd
  have hconj1 : MulAut.conj z ≠ 1 := by
    intro h
    apply hz_center
    rw [Subgroup.mem_center_iff]
    intro y
    have h' := congrArg (fun f : MulAut H => f y) h
    rw [MulAut.one_apply, MulAut.conj_apply] at h'
    have hzy : z * y = y * z := by
      have := congrArg (fun t => t * z) h'
      simpa [mul_assoc] using this
    exact hzy.symm
  have hconj3 : (MulAut.conj z) ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  have hcomp : IsComponentOf J (ggAutFixedSubgroup (MulAut.conj z)) := by
    rw [D4Inner.ggAutFixedSubgroup_conj_eq_centralizer]
    exact hJc
  unfold GGTorsionDatum
  refine ⟨Nat.prime_three, by norm_num, hconj3, hconj1, hcomp, ?_⟩
  rcases hH with ⟨hE6, h3⟩ | ⟨htwE6, h3⟩
  · refine largeEvenMarking_mono
      (P := fun lab _ _ I _ θ => lab = ⟨.E6, 0, f⟩ ∧
        ggInducedAut θ (MulAut.conj z) ∈ I) ?_ (e6_marking_conj hf hE6)
    intro lab R _ I F θ h
    exact ⟨Or.inl ⟨h.1, h3⟩, h.2⟩
  · refine largeEvenMarking_mono
      (P := fun lab _ _ I _ θ => lab = ⟨.twE6, 0, f⟩ ∧
        ggInducedAut θ (MulAut.conj z) ∈ I) ?_ (twE6_marking_conj hf htwE6)
    intro lab R _ I F θ h
    exact ⟨Or.inr ⟨h.1, h3⟩, h.2⟩

theorem ggE6OppOrderThree_label_two
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (hH : GGHasLabel ⟨.E6, 0, 1⟩ (H ⧸ Subgroup.center H)) {z : H} (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) {J : Subgroup H}
    (hJ : J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
    (hJc : IsComponentOf J (Subgroup.centralizer ({z} : Set H))) :
    GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J) := by
  have hperf : commutator H = ⊤ := Group.IsPerfect.commutator_eq_top
  have hrawGuard : LargeEvenRawDatum (⟨.E6, 0, 1⟩ : LargeEvenLabel) fun R _ I F =>
      Nonempty (H ⧸ Subgroup.center H ≃* R) ∧
        LargeEvenSimpleGuard GGInndiagCommEq R I F :=
    largeEvenLabelAll_inndiagComm_E6 (lab := ⟨.E6, 0, 1⟩) rfl
      (fun R _ _ _ => Nonempty (H ⧸ Subgroup.center H ≃* R)) hH
  obtain ⟨K, hKfield, hKfin, hKcard, hQ, hGuard⟩ := by
    simpa only [LargeEvenRawDatum, LargeEvenRecipeChevalley, pow_one] using hrawGuard
  let : Field K := hKfield
  let : Finite K := hKfin
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) .E6 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl⟩, untwistedChevalleyModel_largeEven .E6 hKcard⟩
  have hsimple : IsSimpleGroup
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
    CFSG.Timmesfeld.isSimpleGroup_of_lieModel (Or.inr (Or.inl ⟨rfl, by decide, hchev⟩))
  obtain ⟨θ⟩ := hQ
  have hntH : Nontrivial (H ⧸ Subgroup.center H) :=
    @Equiv.nontrivial (H ⧸ Subgroup.center H)
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) θ.toEquiv
      hsimple.toNontrivial
  obtain ⟨a, b, hab⟩ :=
    exists_mul_ne_mul_centerQuot_of_perfect hperf hntH
  have hna : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false),
      a * b ≠ b * a :=
    ⟨θ a, θ b, fun h => hab (θ.injective (by simpa only [map_mul] using h))⟩
  have hEq : GGInndiagCommEq (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
    hGuard hsimple hna
  have hlab : LargeEvenInLambda2 (⟨.E6, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl⟩
  have hm : MarkedModel (⟨.E6, 0, 1⟩ : LargeEvenLabel) (H ⧸ Subgroup.center H) :=
    l05nL4h_markedModel hperf hntH hlab hH
  have hlie : CFSG.Blueprint.LieModel (H ⧸ Subgroup.center H) .E6 0 2 1 := hm
  have hchevH : CFSG.Blueprint.ChevalleyExceptionalModel (H ⧸ Subgroup.center H) .E6 2 1 :=
    hlie.chevalleyExceptionalModel (by decide)
  obtain ⟨d, hdchar, hdfield, hd, ⟨e'⟩⟩ := TablePThreeKG.e6TwoLeaf_index_E6 hchevH
  have hcomp : IsComponentOf J (ggAutFixedSubgroup (MulAut.conj z)) := by
    rw [D4Inner.ggAutFixedSubgroup_conj_eq_centralizer]
    exact hJc
  have huniq : ∀ Q : Subgroup H,
      IsComponentOf Q (ggAutFixedSubgroup (MulAut.conj z)) → Q = J := by
    intro Q hQ
    have hQ' : IsComponentOf Q (Subgroup.centralizer ({z} : Set H)) := by
      rwa [D4Inner.ggAutFixedSubgroup_conj_eq_centralizer] at hQ
    have hE : IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({z} : Set H)))
        (Subgroup.centralizer ({z} : Set H)) := by
      rw [← hJ]; exact hJc
    exact (SpFin.layer_eq_of_isComponentOf hQ' hE).symm.trans hJ.symm
  have hδI : ggInducedAut θ (MulAut.conj z) ∈
      LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false) := by
    rw [tpq_ggInducedAut_conj]
    exact conj_mem_largeEvenChevIDImage (LargeEvenCartanE 6) K _ (θ (QuotientGroup.mk z))
  have hconj3 : (MulAut.conj z) ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  have hconj1 : MulAut.conj z ≠ 1 := by
    intro h
    have hz_center : z ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h' := congrArg (fun f : MulAut H => f y) h
      rw [MulAut.one_apply, MulAut.conj_apply] at h'
      have hzy : z * y = y * z := by
        have := congrArg (fun t => t * z) h'
        simpa [mul_assoc] using this
      exact hzy.symm
    have hle : Subgroup.zpowers z ≤ Subgroup.center H := Subgroup.zpowers_le.mpr hz_center
    have hdvd : orderOf z ∣ Nat.card (Subgroup.center H) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers] at h1
    have hord : orderOf z = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hz3 hz1
    rw [hord] at hdvd
    exact not_three_dvd_card_center_of_e6Opp (H := H) le_rfl (Or.inl ⟨hH, by norm_num⟩) hdvd
  obtain ⟨lab', hlab', hhas', hcomp_pair⟩ :=
    TablePThreeKG.e6TwoLeaf_component θ hperf hconj3 hconj1 hcomp huniq hδI hEq d hdchar
      (by simpa using hdfield) (Or.inl hd) (θ.symm.trans e')
  obtain ⟨hW, -⟩ := hcomp_pair.1 hd
  unfold TablePThreeKG.E6TwoCompLabelW at hW
  rcases hW with h1 | h2 | h3
  · exact Or.inl (h1 ▸ hhas')
  · exact Or.inr (Or.inl (h2 ▸ hhas'))
  · exact Or.inr (Or.inr (h3 ▸ hhas'))

end CFSG.StandardType

end
