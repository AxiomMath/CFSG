module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1119StepsProof

theorem center_quotient_center_eq_bot_of_isPerfect {M : Type*} [Group M]
    (hP : Group.IsPerfect (M ⧸ Subgroup.center M)) :
    Subgroup.center (M ⧸ Subgroup.center M) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center M) q
  have hc : ∀ g : M, z * g * z⁻¹ * g⁻¹ ∈ Subgroup.center M := by
    intro g
    have h1 := Subgroup.mem_center_iff.mp hq (QuotientGroup.mk' (Subgroup.center M) g)
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center M)]
    simp only [QuotientGroup.mk'_apply] at h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← h1]
    group
  have hcomm : ∀ g h : M, g * (z * h * z⁻¹ * h⁻¹) = (z * h * z⁻¹ * h⁻¹) * g := fun g h =>
    Subgroup.mem_center_iff.mp (hc h) g
  let f : M →* Subgroup.center M :=
    { toFun := fun g => ⟨z * g * z⁻¹ * g⁻¹, hc g⟩
      map_one' := by ext; simp
      map_mul' := fun g h => by
        ext
        simp only [Subgroup.coe_mul]
        calc z * (g * h) * z⁻¹ * (g * h)⁻¹
            = (z * g * z⁻¹ * g⁻¹) * (g * (z * h * z⁻¹ * h⁻¹)) * g⁻¹ := by group
          _ = (z * g * z⁻¹ * g⁻¹) * (z * h * z⁻¹ * h⁻¹) := by
              rw [hcomm g h]
              group }
  have hker1 : commutator M ≤ f.ker := Abelianization.commutator_subset_ker f
  have hker2 : Subgroup.center M ≤ f.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    ext
    change z * w * z⁻¹ * w⁻¹ = 1
    rw [Subgroup.mem_center_iff.mp hw z]
    group
  have htop : ∀ g : M, f g = 1 := by
    intro g
    have hg : (QuotientGroup.mk' (Subgroup.center M) g) ∈
        (commutator M).map (QuotientGroup.mk' (Subgroup.center M)) := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _), ← _root_.commutator_def, hP.commutator_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hhg⟩ := hg
    have hw : h⁻¹ * g ∈ Subgroup.center M := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center M)]
      simp only [QuotientGroup.mk'_apply] at hhg
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hhg, inv_mul_cancel]
    have e : g = h * (h⁻¹ * g) := by group
    rw [e, map_mul, hker1 hh, hker2 hw, one_mul]
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg Subtype.val (htop g)
  change z * g * z⁻¹ * g⁻¹ = 1 at h1
  calc g * z = (z * g * z⁻¹ * g⁻¹)⁻¹ * (z * g) := by group
    _ = z * g := by rw [h1, inv_one, one_mul]

section Centre


theorem center_eq_bot_of_isoGTwo {X : Type} [Group X] (hX : Group.IsPerfect X)
    {q : TauCeti.PrimePower} (h : Sec4.IsoGTwo X q) : Subgroup.center X = ⊥ := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    (GaloisField q.p q.exponent) hK
  have e' := e.trans b.symm
  have hP := Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
    (center_quotient_center_eq_bot_of_isPerfect hP)

theorem center_eq_bot_of_isoTrialityD4 {X : Type} [Group X] (hX : Group.IsPerfect X)
    {n : ℕ} (h : Sec8.IsoTrialityD4 X n) : Subgroup.center X = ⊥ := by
  obtain ⟨q, hv, -, -, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (3 * q.exponent)) =
      q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [GaloisField.card q.p _ (by have := q.exponent_pos; omega), TauCeti.PrimePower.card_def]
    change q.p ^ (3 * q.exponent) = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv
    (GaloisField q.p (3 * q.exponent)) hK
    (iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent)
    (fun x => by rw [TauCeti.PrimePower.card_def]; rfl)
  have e' := e.trans b.symm
  have hP := Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
    (center_quotient_center_eq_bot_of_isPerfect hP)

end Centre

theorem center_eq_bot_of_isLThreePi {X : Type} [Group X] (hX : IsQuasisimple X)
    (h : Sec13.IsLThreePi X) : Subgroup.center X = ⊥ := by
  obtain ⟨p, e, hp, he, hiso⟩ := h
  rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot φ
      (Sec13.isPerfect_center_projSL p e he hq).2
  · by_cases h2 : p ^ e = 2
    · exfalso
      obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
      have hsolU := Sec13.isSolvable_projSU_two
      have hsol : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have : Group.IsPerfect X := hX.1
      have : Nontrivial X := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        obtain ⟨u, v, huv⟩ := hX.2.2
        exact huv (Subsingleton.elim _ _)
      exact Group.IsPerfect.not_isSolvable X hsol
    · have hq2 : 2 < p ^ e := by
        have h1 : 2 ≤ p ^ e := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
        omega
      exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot φ
        (Sec13.isPerfect_center_projSU p e he hq hq2).2

end Item1119StepsProof

section Big


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem Sec11Big.center_eq_bot (hbig : Sec11Big G A c L a R Y d x s r g) :
    Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
  have hq := Sec12.isQuasisimple_thetaQuot_of_mem hbig.mem_thetaComponentsAt_Y
  rcases hbig.isList with ⟨q, hq'⟩ | ⟨n, hn⟩ | hL
  · exact Item1119StepsProof.center_eq_bot_of_isoGTwo hq.1 hq'
  · exact Item1119StepsProof.center_eq_bot_of_isoTrialityD4 hq.1 hn
  · exact Item1119StepsProof.center_eq_bot_of_isLThreePi hq hL

theorem Sec11Big.a_not_mem_Y (hbig : Sec11Big G A c L a R Y d x s r g) : a ∉ Y := by
  intro haY
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt hbig.mem_thetaComponentsAt_Y
  set y : Y := ⟨a, haY⟩ with hy
  have hcen : (y : Y ⧸ aschbacherSolvableCore 3 Y) ∈
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [Subgroup.mem_center_iff]
    intro w
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hy]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYC w.2)
  rw [hbig.center_eq_bot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have h3 := (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.2.1
  apply h3
  have ha3 : a ^ 3 = 1 := hbig.mem_partTwoF.1.2 a hbig.a_mem
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 hbig.a_ne_one
  have h1 := orderOf_dvd_natCard (⟨y, hcen⟩ : aschbacherSolvableCore 3 Y)
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord] at h1

end Big

end CFSG.RankThree.PartTwo.Sec11
