module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.RFAux

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem bot_mem_dset
    (h : Counterexample p A θ) : (⊥ : Subgroup G) ∈ dset p A θ := by
  rw [h.dset_eq_singleton]
  exact Set.mem_singleton _

theorem ne_dsub_of_mem_dset
    (h : Counterexample p A θ) {Y : Subgroup G} (hY : Y ∈ dset p A θ) :
    Y ≠ dsub A θ := fun heq => not_dsub_le_of_mem_dset h.hyp.nearFunctor hY heq.ge

theorem mem_cset_bot_iff
    (h : Counterexample p A θ) {X : Subgroup G} :
    X ∈ cset p A θ ⊥ ↔ X ∈ mtil p A θ ∧ ¬ Group.IsSolvable X := by
  have hθ := h.hyp.nearFunctor
  constructor
  · rintro ⟨hX, P, hP⟩
    refine ⟨hX, fun hsol => ?_⟩
    have hP' : P ∈ iPairs A X := by
      have : P ∈ iPairsY A X ⊥ := by
        rw [← pairsYX_eq_iPairsY hθ hX]
        exact hP
      exact this.1
    have hP1 : Group.IsSolvable ↥P.1 :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hP.2)
    obtain ⟨n, hn⟩ := hP1.solvable
    exact Thm33a.not_isSolvableSection_of_mem_iPairs hP' ⟨n, (le_of_eq hn).trans bot_le⟩
  · rintro ⟨hX, hns⟩
    refine ⟨hX, ?_⟩
    set U : Subgroup G := perfRes X with hU
    have hUX : U ≤ X := Subgroup.map_subtype_le _
    have hNX : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (U : Set G) :=
      Nonsolvable.normalizer_le_normalizer_perfectResidual_map X
    have hDX : dsub A θ ≤ X := hX.2
    have hUadm : Admits (dsub A θ ⊔ A) U :=
      sup_le (hDX.trans (Subgroup.le_normalizer.trans hNX))
        ((show Admits A X from hX.1.1).trans (hNX))
    have hUp : Group.IsPerfect U := Nonsolvable.isPerfect_perfectResidual_map X
    have hUne : ⊥ < U := by
      refine bot_lt_iff_ne_bot.mpr fun hbot => hns ?_
      have h1 : CFSG.perfectResidual ↥X = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hbot
      exact (CFSG.perfect_residual_characterization (G := ↥X)).2.2.2.2.2.mp h1
    have hbotN : (⊥ : Subgroup G).Normal := inferInstance
    have hbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hbotN
    obtain ⟨P, hP, -, hPX⟩ := RFAux.exists_pair_above_perfect hθ hX hUX hUadm hUp hUne
      ⟨bot_le, le_top.trans hbot.ge⟩ (le_top.trans hbot.ge)
    have hmem : dsub A θ ⊓ P.2 ∈ dset p A θ := ⟨P, hP, rfl⟩
    rw [h.dset_eq_singleton, Set.mem_singleton_iff] at hmem
    exact ⟨P, ⟨hP, by rw [inf_comm]; exact hmem⟩, hPX⟩

theorem cset_bot_eq
    (h : Counterexample p A θ) :
    cset p A θ ⊥ = {X | X ∈ mtil p A θ ∧ ¬ Group.IsSolvable X} :=
  Set.ext fun _ => h.mem_cset_bot_iff

theorem mem_rSet_iff
    (h : Counterexample p A θ) {B : Subgroup G} :
    B ∈ rSet p A θ ↔ B ≠ ⊥ ∧ B ≤ A ∧ ¬ Group.IsSolvable (thetaOf θ B) := by
  constructor
  · rintro ⟨hB1, hBA, hc⟩
    exact ⟨hB1, hBA, (h.mem_cset_bot_iff.mp hc).2⟩
  · rintro ⟨hB1, hBA, hns⟩
    exact ⟨hB1, hBA, h.mem_cset_bot_iff.mpr ⟨thetaOf_mem_mtil h.hyp.nearFunctor hBA hB1, hns⟩⟩

theorem mem_rSetN_iff
    (h : Counterexample p A θ) {B : Subgroup G} {i : ℕ} :
    B ∈ rSetN p A θ i ↔
      B ≠ ⊥ ∧ B ≤ A ∧ ¬ Group.IsSolvable (thetaOf θ B) ∧ Nat.card B = p ^ i := by
  constructor
  · rintro ⟨hB, hc⟩
    obtain ⟨h1, h2, h3⟩ := h.mem_rSet_iff.mp hB
    exact ⟨h1, h2, h3, hc⟩
  · rintro ⟨h1, h2, h3, hc⟩
    exact ⟨h.mem_rSet_iff.mpr ⟨h1, h2, h3⟩, hc⟩

theorem rSet_mono
    (h : Counterexample p A θ) {B B' : Subgroup G} (hB : B ∈ rSet p A θ)
    (hB' : B' ≤ B) (hB'1 : B' ≠ ⊥) : B' ∈ rSet p A θ := by
  obtain ⟨-, hBA, hns⟩ := h.mem_rSet_iff.mp hB
  refine h.mem_rSet_iff.mpr ⟨hB'1, hB'.trans hBA, fun hsol => hns ?_⟩
  have := hsol
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (thetaOf_anti hB' : thetaOf θ B ≤ thetaOf θ B'))

theorem card_of_mem_rSet
    (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ) :
    Nat.card B = p ∨ Nat.card B = p ^ 2 := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨hB1, hBA, hns⟩ := h.mem_rSet_iff.mp hB
  have hdvd : Nat.card B ∣ p ^ 3 := h.hyp.card ▸ Subgroup.card_dvd_of_le hBA
  obtain ⟨i, hi, hBi⟩ := (Nat.dvd_prime_pow h.hyp.prime).mp hdvd
  interval_cases i
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hBi)) hB1
  · exact Or.inl (by simpa using hBi)
  · exact Or.inr hBi
  · exfalso
    have hBA' : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hBi, h.hyp.card])
    subst hBA'
    exact hns (isSolvable_dsub hθ)

theorem isGreatest_ssol
    (h : Counterexample p A θ) :
    IsGreatest (signalizers p A (thetaSolFun p A θ) (NearASolvable p A)) (ssol p A θ) := by
  obtain ⟨S, hSmem, hSmax, -⟩ := thetaSolFun_complete h.hyp.nearFunctor h.hyp.card.ge
  have heq : ssol p A θ = S :=
    le_antisymm (iSup₂_le fun X hX => hSmax X hX) (le_iSup₂ (f := fun X (_ : X ∈ signalizers p A
      (thetaSolFun p A θ) (NearASolvable p A)) => X) S hSmem)
  rw [heq]
  exact ⟨hSmem, hSmax⟩

theorem isSolvable_ssol
    (h : Counterexample p A θ) : Group.IsSolvable (ssol p A θ) := by
  obtain ⟨S, hSmem, hSmax, hS⟩ := thetaSolFun_complete h.hyp.nearFunctor h.hyp.card.ge
  have heq : ssol p A θ = S :=
    le_antisymm (iSup₂_le fun X hX => hSmax X hX) (le_iSup₂ (f := fun X (_ : X ∈ signalizers p A
      (thetaSolFun p A θ) (NearASolvable p A)) => X) S hSmem)
  rw [heq]
  exact hS

theorem ssol_mem_assoc
    (h : Counterexample p A θ) : ssol p A θ ∈ assoc p A θ := by
  obtain ⟨hA, hcop, hcen, hnear⟩ := h.isGreatest_ssol.1
  exact ⟨hA, hcop, fun a ha ha1 => (hcen a ha ha1).trans (thetaSol_le (θ a)), hnear⟩

omit [Finite G] in
theorem le_thetaSol_of_mem_mhat {Z : Subgroup G} (hZ : Z ∈ mhat p A θ) {a : G}
    (hZa : Z ≤ θ a) (hs : Group.IsSolvable Z) : Z ≤ thetaSol p A θ (θ a) :=
  le_iSup₂ (f := fun Z (_ : Z ∈ {Z | Z ∈ mhat p A θ ∧ Z ≤ θ a ∧ Group.IsSolvable Z}) => Z)
    Z ⟨hZ, hZa, hs⟩

theorem dsub_le_ssol
    (h : Counterexample p A θ) : dsub A θ ≤ ssol p A θ := by
  have hθ := h.hyp.nearFunctor
  refine h.isGreatest_ssol.2 ?_
  refine ⟨admits_dsub hθ, ?_, fun a ha ha1 => ?_, ?_⟩
  · obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hθ
    exact (hθ.isFunctor.coprime a ha ha1).coprime_dvd_right
      (Subgroup.card_dvd_of_le (dsub_le_apply ha ha1))
  · exact inf_le_left.trans (le_thetaSol_of_mem_mhat (mtil_subset_mhat (dsub_mem_mtil hθ))
      (dsub_le_apply ha ha1) (isSolvable_dsub hθ))
  · obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hθ
    exact nearASolvable_of_isSolvable (isSolvable_dsub hθ)
      ((hθ.isFunctor.coprime a ha ha1).coprime_dvd_right
        (Subgroup.card_dvd_of_le (dsub_le_apply ha ha1)))

theorem ssol_mem_mtil
    (h : Counterexample p A θ) : ssol p A θ ∈ mtil p A θ :=
  ⟨h.ssol_mem_assoc, h.dsub_le_ssol⟩

theorem le_ssol_of_isSolvable
    (h : Counterexample p A θ) {Z : Subgroup G}
    (hZ : Z ∈ mhat p A θ) (hs : Group.IsSolvable Z) : Z ≤ ssol p A θ := by
  have hθ := h.hyp.nearFunctor
  refine h.isGreatest_ssol.2 ?_
  have hZ' := hZ
  obtain ⟨⟨hAZ, hcop, hcen, hnear⟩, hDZ⟩ := hZ'
  refine ⟨hAZ, hcop, fun a ha ha1 => ?_, hnear⟩
  have hDa : dsub A θ ≤ Subgroup.centralizer {a} :=
    (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAa : A ≤ Subgroup.centralizer {a} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg ha)
  have hadmZ : Admits (dsub A θ ⊔ A) Z := sup_le hDZ hAZ
  have hadm : Admits (dsub A θ ⊔ A) (Z ⊓ Subgroup.centralizer {a}) :=
    hadmZ.inf (admits_centralizer_singleton (sup_le hDa hAa))
  have hmem : Z ⊓ Subgroup.centralizer {a} ∈ mhat p A θ :=
    ⟨mem_assoc_of_le hθ.prime hZ.1 inf_le_left (hadm.mono_left le_sup_right),
      hadm.mono_left le_sup_left⟩
  exact le_thetaSol_of_mem_mhat hmem (hcen a ha ha1)
    (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : Z ⊓ Subgroup.centralizer {a} ≤ Z)))

theorem ssol_inf_eq_thetaSol
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ mhat p A θ) : ssol p A θ ⊓ X = thetaSol p A θ X := by
  have hθ := h.hyp.nearFunctor
  refine le_antisymm ?_ (le_inf (iSup₂_le fun Z hZ => h.le_ssol_of_isSolvable hZ.1 hZ.2.2)
    (thetaSol_le X))
  have hAS : Admits A (ssol p A θ) := h.ssol_mem_assoc.1
  have hAX : Admits A X := hX.1.1
  have hadm : Admits A (ssol p A θ ⊓ X) := hAS.inf hAX
  have hadmD : Admits (dsub A θ) (ssol p A θ ⊓ X) :=
    (admits_dsub_of_le h.dsub_le_ssol).inf hX.2
  have := h.isSolvable_ssol
  exact le_iSup₂ (f := fun Z (_ : Z ∈ {Z | Z ∈ mhat p A θ ∧ Z ≤ X ∧ Group.IsSolvable Z}) => Z)
    (ssol p A θ ⊓ X) ⟨⟨mem_assoc_of_le hθ.prime h.ssol_mem_assoc inf_le_left hadm, hadmD⟩,
      inf_le_right, Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left : ssol p A θ ⊓ X ≤ ssol p A θ))⟩

theorem isGreatest_ssol_inf
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ mtil p A θ) :
    IsGreatest {Z : Subgroup G | Z ≤ X ∧ Admits (cenIn X (A : Set G) ⊔ A) Z ∧
      Group.IsSolvable Z} (ssol p A θ ⊓ X) := by
  have hθ := h.hyp.nearFunctor
  have hD : cenIn X (A : Set G) = dsub A θ := cenIn_eq_dsub hθ hX
  have hAS : Admits A (ssol p A θ) := h.ssol_mem_assoc.1
  have hAX : Admits A X := hX.1.1
  have hDS : Admits (dsub A θ) (ssol p A θ) := admits_dsub_of_le h.dsub_le_ssol
  have hDX : Admits (dsub A θ) X := admits_dsub_of_le hX.2
  have := h.isSolvable_ssol
  refine ⟨⟨inf_le_right, ?_, Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (inf_le_left : ssol p A θ ⊓ X ≤ ssol p A θ))⟩, ?_⟩
  · rw [hD]
    exact sup_le (hDS.inf hDX) (hAS.inf hAX)
  · rintro Z ⟨hZX, hZadm, hZs⟩
    rw [hD] at hZadm
    exact le_inf (h.le_ssol_of_isSolvable (mem_mhat_of_le_mtil hθ.prime hX hZX hZadm) hZs) hZX

theorem ssol_inf_thetaOf_eq
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) : ssol p A θ ⊓ thetaOf θ B = thetaSol p A θ (thetaOf θ B) :=
  h.ssol_inf_eq_thetaSol (mtil_subset_mhat (thetaOf_mem_mtil h.hyp.nearFunctor hBA hB))

theorem thetaOf_le_ssol_of_isSolvable
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    (hB : B ≠ ⊥) (hs : Group.IsSolvable (thetaOf θ B)) : thetaOf θ B ≤ ssol p A θ :=
  h.le_ssol_of_isSolvable (mtil_subset_mhat (thetaOf_mem_mtil h.hyp.nearFunctor hBA hB)) hs

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
