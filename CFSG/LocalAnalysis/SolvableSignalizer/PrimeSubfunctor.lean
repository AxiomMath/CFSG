module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.Adapter
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
import CFSG.LocalAnalysis.SolvableSignalizer.Quotient
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorRestriction

public section

namespace CFSG.SolvableSignalizer

section Helpers

variable {A G : Type*} [Group A] [Group G]

private theorem primeSupported_of_le {π : Set ℕ} {H K : Subgroup G} (h : H ≤ K)
    (hK : primeSupported π (Nat.card K)) : primeSupported π (Nat.card H) :=
  fun q hq hqdvd => hK q hq (hqdvd.trans (Subgroup.card_dvd_of_le h))

private theorem le_normalizer_inf {C H K : Subgroup G}
    (hH : C ≤ Subgroup.normalizer (H : Set G)) (hK : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem map_subtype_le_normalizer_iff (H : Subgroup G) (C U : Subgroup H) :
    C.map H.subtype ≤ Subgroup.normalizer (U.map H.subtype : Set G) ↔
      C ≤ Subgroup.normalizer (U : Set H) := by
  rw [Subgroup.map_le_iff_le_comap,
    Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range H.subtype U),
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

private theorem primeSupported_map_subtype_iff (π : Set ℕ) (H : Subgroup G) (U : Subgroup H) :
    primeSupported π (Nat.card (U.map H.subtype)) ↔
      CFSG.IsPiSubgroup {q : Nat.Primes | q.val ∈ π} U := by
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact ⟨fun h q hq => h q.val q.property hq, fun h q hq hd => h ⟨q, hq⟩ hd⟩

private theorem le_normalizer_completion (θ : A → Subgroup G) {C : Subgroup G}
    (h : ∀ a : A, a ≠ 1 → C ≤ Subgroup.normalizer (θ a : Set G)) :
    C ≤ Subgroup.normalizer (completion θ : Set G) := fun c hc => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, completion]
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun a => iSup_congr fun ha =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h a ha hc)

private theorem isComplete_congr {p : ℕ} {α : A →* MulAut G} {β γ : A → Subgroup G}
    (h : ∀ a : A, a ≠ 1 → β a = γ a) : IsComplete p α β ↔ IsComplete p α γ := by
  have hc : completion β = completion γ := iSup_congr fun a => iSup_congr fun ha => h a ha
  rw [IsComplete, IsComplete, hc, Compatible, Compatible]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun a ha => ?_
  rw [h a ha]

theorem primeSubfunctor_diff_singleton_eq {α : A →* MulAut G} {θ : A → Subgroup G} {q : ℕ}
    {a : A} (ha : a ≠ 1) {π : Set ℕ} (hπ : spectrum θ ⊆ π) :
    primeSubfunctor α θ (π \ {q}) a = primeSubfunctor α θ (spectrum θ \ {q}) a := by
  have hs (U : Subgroup G) (hU : U ≤ θ a) : primeSupported (π \ {q}) (Nat.card U) ↔
      primeSupported (spectrum θ \ {q}) (Nat.card U) :=
    ⟨fun h r hr hd => ⟨⟨hr, a, ha, hd.trans (Subgroup.card_dvd_of_le hU)⟩, (h r hr hd).2⟩,
      fun h r hr hd => ⟨hπ (h r hr hd).1, (h r hr hd).2⟩⟩
  unfold primeSubfunctor
  refine iSup_congr fun U => iSup_congr fun hU => ?_
  simp only [hs U hU]

end Helpers

universe u v
variable {A : Type u} {G : Type v} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

theorem Datum.primeSubfunctor_spec (d : Datum p α θ)
    (π : Set ℕ) (hpπ : p ∉ π) (a : A) (ha : a ≠ 1) :
    primeSubfunctor α θ π a ≤ θ a ∧
    IsInvariant α (primeSubfunctor α θ π a) ∧
    primeSupported π (Nat.card (primeSubfunctor α θ π a)) ∧
    commonSignalizerWhole θ ≤ Subgroup.normalizer (primeSubfunctor α θ π a : Set G) ∧
    primeSubfunctor α θ π a =
      ⨅ (U : Subgroup (θ a))
        (_ : IsInvariant α (U.map (θ a).subtype))
        (_ : CFSG.IsHallSubgroup {q : Nat.Primes | q.val ∈ π} U),
        U.map (θ a).subtype ∧
    (∀ U : Subgroup G, U ≤ θ a → IsInvariant α U →
      primeSupported π (Nat.card U) →
      commonSignalizerWhole θ ≤ Subgroup.normalizer (U : Set G) →
      U ≤ primeSubfunctor α θ π a) := by
  classical
  let H := θ a
  have hH : IsInvariant α H := d.invariant a ha
  let β := restrictAction α H hH
  let PiSet : Set Nat.Primes := {q | q.val ∈ π}
  let R : Subgroup H := ⨅ (U : Subgroup H)
    (_ : CFSG.IsHallSubgroup PiSet U) (_ : IsInvariant β U), U
  let S : Subgroup G := R.map H.subtype
  have hA : IsPGroup p A :=
    have := d.isElementaryAbelian
    CFSG.IsElementaryAbelian.isPGroup p A
  have hcop : ¬ p ∣ Nat.card H := d.prime.coprime_iff_not_dvd.mp (d.coprime a ha)
  obtain ⟨hRi, hRπ, hRn, hRmax⟩ := iInf_invariant_isHallSubgroup_largest
    p d.prime hA β hcop (d.solvable a ha) PiSet hpπ
  change IsInvariant β R at hRi
  change CFSG.IsPiSubgroup PiSet R at hRπ
  change actionFixedAll β ≤ Subgroup.normalizer (R : Set H) at hRn
  change ∀ U : Subgroup H, IsInvariant β U → CFSG.IsPiSubgroup PiSet U →
    actionFixedAll β ≤ Subgroup.normalizer (U : Set H) → U ≤ R at hRmax
  have hC : (actionFixedAll β).map H.subtype = commonSignalizerWhole θ := by
    rw [fixedBySubgroup_restrictAction_map_subtype]
    exact (compatible_values_and_commonSignalizer d).2.2 a ha
  have hSle : S ≤ H := Subgroup.map_subtype_le R
  have hSi : IsInvariant α S := (isInvariant_restrictAction_iff hH R).mp hRi
  have hSπ : primeSupported π (Nat.card S) := (primeSupported_map_subtype_iff π H R).mpr hRπ
  have hSn : commonSignalizerWhole θ ≤ Subgroup.normalizer (S : Set G) := by
    rw [← hC]
    exact (map_subtype_le_normalizer_iff H _ R).mpr hRn
  have hmax (U : Subgroup G) (hUH : U ≤ H) (hUi : IsInvariant α U)
      (hUπ : primeSupported π (Nat.card U))
      (hUn : commonSignalizerWhole θ ≤ Subgroup.normalizer (U : Set G)) : U ≤ S := by
    have hm : (U.subgroupOf H).map H.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUH
    rw [← hm] at hUi hUπ hUn ⊢
    rw [← hC, map_subtype_le_normalizer_iff] at hUn
    exact Subgroup.map_mono (hRmax _ ((isInvariant_restrictAction_iff hH _).mpr hUi)
      ((primeSupported_map_subtype_iff π H _).mp hUπ) hUn)
  have heq : primeSubfunctor α θ π a = S :=
    le_antisymm (iSup_le fun U => iSup_le fun hUH => iSup_le fun hUi => iSup_le fun hUπ =>
        iSup_le fun hUn => hmax U hUH hUi hUπ hUn)
      (le_primeSubfunctor hSle hSi hSπ hSn)
  rw [heq]
  refine ⟨hSle, hSi, hSπ, hSn, ?_, hmax⟩
  let T : Subgroup G := ⨅ (U : Subgroup H)
    (_ : IsInvariant α (U.map H.subtype)) (_ : CFSG.IsHallSubgroup PiSet U),
    U.map H.subtype
  have hTle (U : Subgroup H) (hUh : CFSG.IsHallSubgroup PiSet U)
      (hUi : IsInvariant β U) : T ≤ U.map H.subtype :=
    iInf₂_le_of_le U ((isInvariant_restrictAction_iff hH U).mp hUi) (iInf_le _ hUh)
  change S = T
  refine le_antisymm (le_iInf₂ fun U hUi => le_iInf fun hUh => Subgroup.map_mono
    (iInf₂_le_of_le U hUh (iInf_le _ ((isInvariant_restrictAction_iff hH U).mpr hUi)))) ?_
  obtain ⟨P, hPh, hPi, -⟩ := exists_isHallSubgroup_isInvariant_le
    p d.prime hA β hcop (d.solvable a ha) PiSet hpπ R hRi hRπ
  intro x hx
  obtain ⟨y, -, rfl⟩ := hTle P hPh hPi hx
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_iInf.mpr fun U => Subgroup.mem_iInf.mpr
    fun hUh => Subgroup.mem_iInf.mpr fun hUi => ?_)
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp (hTle U hUh hUi hx)

omit [Finite A] [Finite G] in
private theorem isInvariant_fixedSubgroup (α : A →* MulAut G) (b : A) :
    IsInvariant α (fixedSubgroup α b) := by
  have hcomm (a b : A) (x : G) : α b (α a x) = α a (α b x) := by
    rw [← MulAut.mul_apply, ← map_mul, mul_comm, map_mul, MulAut.mul_apply]
  intro a
  ext g
  simp only [Subgroup.mem_map, mem_fixedSubgroup, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hcomm a b x, hx]
  · intro hg
    exact ⟨α a⁻¹ g, by rw [hcomm a⁻¹ b g, hg], by simp⟩

private theorem le_normalizer_fixedIn (d : Datum p α θ) {a : A} (ha : a ≠ 1)
    {H : Subgroup G} (hH : commonSignalizerWhole θ ≤ Subgroup.normalizer (H : Set G)) :
    commonSignalizerWhole θ ≤ Subgroup.normalizer (fixedIn α H a : Set G) :=
  le_normalizer_inf hH ((((commonSignalizerWhole_le θ ha).trans (d.central a ha)).trans
    (fixedSubgroup α a).le_normalizer))

theorem Datum.primeSubfunctor (d : Datum p α θ)
    (π : Set ℕ) (hpπ : p ∉ π) :
    Datum p α (primeSubfunctor α θ π) ∧
    spectrum (primeSubfunctor α θ π) ⊆ π ∩ spectrum θ ∧
    (∀ H : Subgroup G, CompatibleAt p α θ π H →
      commonSignalizerWhole θ ≤ Subgroup.normalizer (H : Set G) →
      Compatible p α (primeSubfunctor α θ π) H) := by
  have hval := Datum.primeSubfunctor_spec d π hpπ
  refine ⟨⟨d.prime, d.exponent, d.rank_two, fun a ha => (hval a ha).2.1, fun a ha => ?_,
    fun a ha => ?_, fun a ha => (hval a ha).1.trans (d.central a ha), fun a b ha hb => ?_⟩,
    ?_, fun H hH hnorm => ⟨hH.1.1, hH.1.2.1, hH.1.2.2.1, fun a ha => ?_⟩⟩
  · have := d.solvable a ha
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hval a ha).1)
  · exact d.prime.coprime_iff_not_dvd.mpr fun hpdvd => hpπ ((hval a ha).2.2.1 p d.prime hpdvd)
  · obtain ⟨hle, hi, hπ, hn, -, -⟩ := hval a ha
    exact (hval b hb).2.2.2.2.2 _ ((inf_le_inf_right _ hle).trans (d.balance a b ha hb))
      (hi.inf (isInvariant_fixedSubgroup α b)) (primeSupported_of_le inf_le_left hπ)
      (le_normalizer_fixedIn d hb hn)
  · rintro q ⟨hq, a, ha, hqdiv⟩
    exact ⟨(hval a ha).2.2.1 q hq hqdiv,
      hq, a, ha, hqdiv.trans (Subgroup.card_dvd_of_le (hval a ha).1)⟩
  · exact (hval a ha).2.2.2.2.2 _ (hH.1.2.2.2 a ha)
      (hH.1.1.inf (isInvariant_fixedSubgroup α a))
      (primeSupported_of_le inf_le_left hH.2) (le_normalizer_fixedIn d ha hnorm)

private theorem map_commonSignalizerWhole_restrictTheta (d : Datum p α θ)
    (H : Subgroup G) :
    (commonSignalizerWhole (restrictTheta θ H)).map H.subtype =
      commonSignalizerWhole (fun a => θ a ⊓ H) := by
  obtain ⟨a, ha⟩ := Datum.exists_ne_one d
  ext x
  simp only [commonSignalizerWhole, commonSignalizer, Subgroup.mem_map, Subgroup.mem_iInf,
    Subgroup.mem_top, forall_const, mem_restrictTheta, Subgroup.mem_inf, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩ b hb
    exact ⟨hy b hb, y.property⟩
  · intro hx
    exact ⟨⟨x, (hx a ha).2⟩, fun b hb => (hx b hb).1, rfl⟩

private theorem map_primeSubfunctor_restrictTheta (d : Datum p α θ)
    (H : Subgroup G) (hH : IsInvariant α H) (π : Set ℕ) (a : A) :
    (primeSubfunctor (restrictAction α H hH) (restrictTheta θ H) π a).map H.subtype =
      primeSubfunctor α (fun b => θ b ⊓ H) π a := by
  have hnormal (U : Subgroup H) :
      commonSignalizerWhole (restrictTheta θ H) ≤ Subgroup.normalizer (U : Set H) ↔
      commonSignalizerWhole (fun b => θ b ⊓ H) ≤
        Subgroup.normalizer (U.map H.subtype : Set G) := by
    rw [← map_commonSignalizerWhole_restrictTheta d H, map_subtype_le_normalizer_iff]
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr (iSup_le fun U => iSup_le fun hU =>
      iSup_le fun hi => iSup_le fun hp => iSup_le fun hn => Subgroup.map_le_iff_le_comap.mp ?_)
    have hU' : U.map H.subtype ≤ θ a ⊓ H := by
      rw [← Subgroup.subgroupOf_map_subtype (θ a) H]
      exact Subgroup.map_mono hU
    have hp' : primeSupported π (Nat.card (U.map H.subtype)) := by
      rwa [Subgroup.card_map_of_injective H.subtype_injective]
    exact le_primeSubfunctor (θ := fun b => θ b ⊓ H) hU'
      ((isInvariant_restrictAction_iff hH U).mp hi) hp' ((hnormal U).mp hn)
  · refine iSup_le fun U => iSup_le fun hU => iSup_le fun hi => iSup_le fun hp =>
      iSup_le fun hn => ?_
    have heq : (U.subgroupOf H).map H.subtype = U :=
      Subgroup.map_subgroupOf_eq_of_le (hU.trans inf_le_right)
    rw [← heq] at hi hp hn ⊢
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hp
    exact Subgroup.map_mono (le_primeSubfunctor (Subgroup.subgroupOf_mono H (hU.trans inf_le_left))
      ((isInvariant_restrictAction_iff hH _).mpr hi) hp ((hnormal _).mpr hn))

private theorem solvableSignalizer_inf (d : Datum p α θ)
    (H : Subgroup G) (hH : IsInvariant α H) :
    Datum p α (fun a => θ a ⊓ H) := by
  refine ⟨d.prime, d.exponent, d.rank_two, fun a ha => (d.invariant a ha).inf hH,
    fun a ha => ?_, fun a ha => (d.coprime a ha).of_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left), fun a ha => inf_le_left.trans (d.central a ha),
    fun a b ha hb => ?_⟩
  · have := d.solvable a ha
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  · exact le_inf ((inf_le_inf_right _ inf_le_left).trans (d.balance a b ha hb))
      (inf_le_left.trans inf_le_right)

theorem map_primeSubfunctor_restrict (d : Datum p α θ)
    (H : Subgroup G) (hH : IsInvariant α H)
    (normalized : commonSignalizerWhole θ ≤ Subgroup.normalizer (H : Set G))
    (π : Set ℕ) (_hpπ : p ∉ π) (a : A) (ha : a ≠ 1) :
    (primeSubfunctor (restrictAction α H hH) (restrictTheta θ H) π a).map H.subtype =
      primeSubfunctor α θ π a ⊓ H := by
  let δ : A → Subgroup G := fun b => θ b ⊓ H
  have dδ : Datum p α δ := solvableSignalizer_inf d H hH
  have hv : Internal.values α δ = CFSG.SignalizerFunctor.Helpers.signalizerRestriction
      (Internal.values α θ) (Internal.lift α H) :=
    funext fun S => Internal.lift_inf α (θ (Internal.index α S)) H
  have hn : CFSG.SignalizerFunctor.Helpers.signalizerCommonFixed
      p 1 (Internal.actor α) (Internal.values α θ) ≤
      Subgroup.normalizer (Internal.lift α H : Set (Internal.Ambient α)) := by
    rw [Internal.signalizerCommonFixed_values d]
    exact (Internal.lift_le_normalizer_lift _ _).mpr normalized
  have hS : Internal.cyclicActor α a ∈
      CFSG.Open.signalizerFunctorEk p 1 (Internal.actor α) :=
    ⟨Internal.cyclicActor_le α a, by simpa using Internal.card_cyclicActor d ha⟩
  have hr := CFSG.SignalizerFunctor.Helpers.signalizer_prime_subfunctor_restriction
    p 1 d.prime (Internal.actor α) (Internal.lift α H) (Internal.isElemAbelian_actor d)
    (Internal.values α θ) (Internal.solvableSignalizerConditions_values d)
    ((Internal.isInvariant_iff_actor_le_normalizer α H).mp hH) hn π (Internal.cyclicActor α a) hS
  have hprime {β : A → Subgroup G} (dβ : Datum p α β) :
      primeSubfunctor α β π (Internal.index α (Internal.cyclicActor α a)) =
        primeSubfunctor α β π a := by
    unfold primeSubfunctor
    rw [Internal.lift_injective α (Internal.values_cyclicActor dβ ha)]
  rw [← hv, Internal.signalizerPrimeValue_values dδ π hS,
    Internal.signalizerPrimeValue_values d π hS, hprime d, hprime dδ, ← Internal.lift_inf] at hr
  rw [map_primeSubfunctor_restrictTheta d H hH π a]
  exact Internal.lift_injective α hr

theorem LocallyComplete.restrict (d : Datum p α θ)
    (local_complete : LocallyComplete p α θ) (H : Subgroup G)
    (hH : IsInvariant α H)
    (normalized : commonSignalizerWhole θ ≤ Subgroup.normalizer (H : Set G)) :
    LocallyComplete p (restrictAction α H hH) (restrictTheta θ H) := by
  let β := restrictAction α H hH
  let δ := restrictTheta θ H
  refine ⟨fun U hU hne => ?_, fun q hq => ?_⟩
  · have hUG := (compatible_restrict_iff hH U).mp hU
    have hneG : U.map H.subtype ≠ ⊥ := fun h =>
      hne (Subgroup.map_injective H.subtype_injective (h.trans (Subgroup.map_bot _).symm))
    apply (compatible_restrict_iff hH _).mpr
    refine Compatible.of_le_of_isInvariant d (local_complete.1 _ hUG hneG) ?_ ?_
    · simp only [completionIn, Subgroup.map_iSup]
      refine iSup₂_le fun a ha => le_iSup₂_of_le a ha ?_
      rw [Subgroup.map_inf _ _ _ H.subtype_injective]
      exact inf_le_inf ((Subgroup.subgroupOf_map_subtype (θ a) H).le.trans inf_le_left)
        (Subgroup.le_normalizer_map H.subtype)
    · refine (isInvariant_restrictAction_iff hH _).mp fun b => ?_
      have hN := hU.1.normalizer
      simp only [completionIn, Subgroup.map_iSup]
      exact iSup_congr fun a => iSup_congr fun ha => by
        rw [Subgroup.map_inf _ _ _ (β b).injective, hN b,
          (Datum.restrict d H hH).1.invariant a ha b]
  · have hpπ : p ∉ spectrum θ \ {q} := fun hp => d.notMem_spectrum hp.1
    have hc := (IsComplete.restrict (Datum.primeSubfunctor d _ hpπ).1
      (local_complete.2 q (spectrum_restrictTheta_subset θ H hq)) H hH).1
    have heq (a : A) (ha : a ≠ 1) : restrictTheta (primeSubfunctor α θ (spectrum θ \ {q})) H a =
        primeSubfunctor β δ (spectrum θ \ {q}) a := by
      apply Subgroup.map_injective H.subtype_injective
      rw [restrictTheta, Subgroup.subgroupOf_map_subtype]
      exact (map_primeSubfunctor_restrict d H hH normalized _ hpπ a ha).symm
    exact (isComplete_congr fun a ha => (heq a ha).trans
      (primeSubfunctor_diff_singleton_eq ha (spectrum_restrictTheta_subset θ H))).mp hc

theorem LocallyComplete.completion_primeSubfunctor_spec (d : Datum p α θ)
    (local_complete : LocallyComplete p α θ) (q : ℕ) (hq : q ∈ spectrum θ) :
    let πq := spectrum θ \ {q}
    let Kq := completion (primeSubfunctor α θ πq)
    CompatibleAt p α θ πq Kq ∧
    commonSignalizerWhole θ ≤ Subgroup.normalizer (Kq : Set G) ∧
    (∀ H : Subgroup G, CompatibleAt p α θ πq H →
      commonSignalizerWhole θ ≤ Subgroup.normalizer (H : Set G) → H ≤ Kq) ∧
    (∀ a : A, a ≠ 1 → (pPrimeCore q (θ a)).map (θ a).subtype ≤ Kq) := by

  intro πq Kq
  have hpπ : p ∉ πq := fun h => d.notMem_spectrum h.1
  obtain ⟨dsf, hspec, hdom⟩ := Datum.primeSubfunctor d πq hpπ
  have hc : Compatible p α (primeSubfunctor α θ πq) Kq := local_complete.2 q hq
  refine ⟨⟨⟨hc.1, hc.2.1, hc.2.2.1,
      fun a ha => (hc.2.2.2 a ha).trans (Datum.primeSubfunctor_spec d πq hpπ a ha).1⟩,
    fun r hr hd => (hspec (primeSupported_spectrum_of_compatible dsf hc r hr hd)).1⟩,
    le_normalizer_completion _ fun a ha => (Datum.primeSubfunctor_spec d πq hpπ a ha).2.2.2.1,
    fun H hH hnorm => (eq_completionIn_and_le_completion dsf (hdom H hH hnorm)).2,
    fun a ha => ?_⟩
  have : Fact q.Prime := ⟨hq.1⟩
  set V := (pPrimeCore q (θ a)).map (θ a).subtype
  have hVinv : IsInvariant α V := (d.invariant a ha).map_subtype_of_characteristic inferInstance
  have hVle : V ≤ θ a := Subgroup.map_subtype_le _
  have hVcomp : Compatible p α θ V := Compatible.of_le_of_isInvariant d
    ((compatible_values_and_commonSignalizer d).1 a ha) hVle hVinv
  have hVπ : primeSupported πq (Nat.card V) := by
    intro r hr hd
    refine ⟨primeSupported_spectrum_of_compatible d hVcomp r hr hd, ?_⟩
    rw [Subgroup.card_map_of_injective (θ a).subtype_injective] at hd
    intro hrq
    rw [Set.mem_singleton_iff] at hrq
    subst hrq
    exact hr.coprime_iff_not_dvd.mp pPrimeCore_coprime_card hd
  have hVnorm : commonSignalizerWhole θ ≤ Subgroup.normalizer (V : Set G) := by
    have hmap := Subgroup.le_normalizer_map (H := pPrimeCore q (θ a)) (f := (θ a).subtype)
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact (commonSignalizerWhole_le θ ha).trans hmap
  exact ((Datum.primeSubfunctor_spec d πq hpπ a ha).2.2.2.2.2 V hVle hVinv hVπ hVnorm).trans
    (le_iSup₂_of_le a ha le_rfl)

end CFSG.SolvableSignalizer
