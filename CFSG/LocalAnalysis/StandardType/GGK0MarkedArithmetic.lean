module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVacMoreNine

public section

namespace CFSG.StandardType.GGK0MarkedArithmetic

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

theorem compType_mem (D : K0Diag) (nodes : List ℕ) :
    (k0CompType D nodes).1 ∈
      ([.A, .C, .D, .G2, .F4, .E6, .E7, .E8] : List LargeEvenLieTag) := by
  unfold k0CompType
  dsimp only
  split
  · split <;> (try split_ifs) <;> simp
  · (try split_ifs) <;> simp

theorem markedModel_of_label
    {X : Type} [Group X] {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hX : ∃ a b : X, a * b ≠ b * a)
    (hlab : GGHasLabel lab X) : MarkedModel lab X := by
  apply largeEvenRawDatum_elim_const
  refine largeEvenRawDatum_imp hΛ ?_ ?_ hlab
  · rintro R _ I F ⟨e⟩
    obtain ⟨a, b, hab⟩ := hX
    refine ⟨e a, e b, ?_⟩
    intro h
    apply hab
    apply e.injective
    simpa only [map_mul] using h
  · rintro R _ I F ⟨e⟩ hM
    exact MarkedModel.of_mulEquiv e.symm hM


theorem orbit_descriptor_tag
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) (j : Fin M.row.D.orbits.length) :
    (M.row.D.orbits[j].lab.tag = .B2der ∧ M.row.D.orbits[j].lab.n = 1) ∨
      (markChar M.row.D.orbits[j].lab = 2 ∧
       M.row.D.orbits[j].lab.tag ≠ .twB2 ∧ M.row.D.orbits[j].lab.tag ≠ .twF4 ∧
       M.row.D.orbits[j].lab.tag ≠ .twF4der ∧ M.row.D.orbits[j].lab.n ∣
         markDeg M.row.D.orbits[j].lab) := by
  rw [M.orbit_descriptor]
  unfold KacRow.orbitDescriptor orbitDescriptorOf
  dsimp only
  have h := compType_mem M.row.diagram ((M.orbitNodes j).headD [])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  all_goals rw [h]
  all_goals simp only [k0LabelOf]
  all_goals (try split_ifs) <;> simp [markChar, markDeg, dvd_refl]
  all_goals split_ifs <;> simp


theorem dvd_card_component_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {K : Subgroup R} (hK : IsComponentOf K (ggFixSub phi)) : p ∣ Nat.card K := by
  have hτ : M.tau ≠ .G2 := by
    rw [← M.tau_eq]
    cases M.row.T <;> simp [absTag]
  obtain ⟨j, hj, hKeq⟩ :=
    GGK0MarkedComponents.exists_component_position_of_realization
      hpair.1 hpair.2.1 M hτ hK
  subst K
  obtain ⟨hΛ, hlabel⟩ := M.label j hj
  have hqs := (GGK0MarkedComponents.component_of_realization M j hj).1.2.2
  have hmodel : MarkedModel M.row.D.orbits[j].lab
      (coreFactor M.setup M.iota M.a (M.repr j) ⧸
        Subgroup.center (coreFactor M.setup M.iota M.a (M.repr j))) :=
    markedModel_of_label hΛ (ggQuasisimple_centerQuot hqs).2 hlabel
  rcases orbit_descriptor_tag M j with ⟨htag, hn⟩ | ⟨hc, hB2, hF4, hF4d, hnd⟩
  · have hdiv : lab.n ∣ 1 := by
      rw [← hn, M.field_exp]
      exact dvd_mul_left lab.n (M.orbitNodes j).length
    have hn1 : lab.n = 1 := Nat.eq_one_of_dvd_one hdiv
    have hp3 : p = 3 := by
      rcases hpair.2.2.1 with hd | hd
      · have hp1 : p ∣ 1 := by simpa only [hn1, pow_one, Nat.reduceSub] using hd
        exact (hpair.1.ne_one (Nat.eq_one_of_dvd_one hp1)).elim
      · exact (Nat.prime_dvd_prime_iff_eq hpair.1 Nat.prime_three).mp
          (by simpa only [hn1, pow_one, Nat.reduceAdd] using hd)
    have hcard := ggMarkedModel_card_b2der htag hmodel
    have hthree : 3 ∣ Nat.card (coreFactor M.setup M.iota M.a (M.repr j) ⧸
      Subgroup.center (coreFactor M.setup M.iota M.a (M.repr j))) := by
        rw [hcard]; norm_num
    exact (hp3.symm ▸ hthree).trans (Subgroup.card_quotient_dvd_card _)
  · have hfield : GGCompFieldAt (2 ^ markDeg M.row.D.orbits[j].lab)
        (coreFactor M.setup M.iota M.a (M.repr j)) :=
      ⟨M.row.D.orbits[j].lab, hΛ, hc, rfl, hB2, hF4, hF4d, hlabel,
        _, inferInstance, hmodel, ⟨MulEquiv.refl _⟩⟩
    have hnDiv : lab.n ∣ M.row.D.orbits[j].lab.n := by
      rw [M.field_exp]
      exact dvd_mul_left lab.n (M.orbitNodes j).length
    have hd : lab.n ∣ markDeg M.row.D.orbits[j].lab := hnDiv.trans hnd
    obtain ⟨k, hk⟩ := hd
    have hpSq : p ∣ (2 ^ lab.n) ^ 2 - 1 :=
      CorFourTwoVacMore.dvd_sq_sub_one_of_dvd (hpair.2.2.1.elim Or.inr Or.inl)
    have hdSq : (2 ^ lab.n) ^ 2 - 1 ∣ (2 ^ markDeg M.row.D.orbits[j].lab) ^ 2 - 1 := by
      rw [hk, pow_mul]
      exact sq_sub_one_dvd_pow_sq_sub_one (2 ^ lab.n) k
    exact hpSq.trans (hdSq.trans (ggCompFieldAt_dvd hfield))


theorem cover_dvd_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {L : Type} [Group L] [Finite L] (psi : L →* R)
    (hpsi : Function.Surjective psi) (hker : psi.ker ≤ Subgroup.center L)
    (e : MulAut L) (hInd : ∀ l, phi (psi l) = psi (e l)) :
    ∀ K : Subgroup L, IsComponentOf K (ggFixSub e) → p ∣ Nat.card K :=
  ggK1_cover_dvd psi hpsi hker e phi hInd (fun _ hK => dvd_card_component_of_realization hpair M hK)

end CFSG.StandardType.GGK0MarkedArithmetic


