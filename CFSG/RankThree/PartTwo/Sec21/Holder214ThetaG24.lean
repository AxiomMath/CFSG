module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24Unique
public import Certificates.Certificate799103

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.Sporadic.Co1Block (twoBD xBar yBar card_twoBD)
open Equiv Hering214Even
open scoped commutatorElement

noncomputable def g24C1 : Perm (Fin 1365) := permOfArr 1365 g24ThC1

noncomputable def g24C2 : Perm (Fin 1365) := permOfArr 1365 g24ThC2

noncomputable def g24Tau : Perm (Fin 1365) := permOfArr 1365 g24ThTau

noncomputable def g24E0 : Subgroup (Perm (Fin 1365)) := Subgroup.closure {g24C1, g24C2}

noncomputable def g24R : Subgroup (Perm (Fin 1365)) := Subgroup.closure {xBar, yBar, g24Tau}

theorem permOfArr_xa : permOfArr 1365 CFSG.EvenSporadicStandard.G24Aut.xa = xBar :=
  CFSG.Sporadic.Co1Block.strong0_eq

theorem permOfArr_ya : permOfArr 1365 CFSG.EvenSporadicStandard.G24Aut.ya = yBar :=
  CFSG.Sporadic.Co1Block.strong1_eq

theorem g24_basic :
    g24Tau * xBar * g24Tau⁻¹ ∈ twoBD ∧ g24Tau * yBar * g24Tau⁻¹ ∈ twoBD ∧ g24C1 ^ 3 = 1 ∧
      g24C2 ^ 3 = 1 ∧ g24C1 * g24C2 = g24C2 * g24C1 ∧ g24C1 ≠ 1 ∧ g24C2 ≠ 1 ∧
      g24C2 ≠ g24C1 ∧ g24C2 ≠ g24C1 ^ 2 := by
  have h := Certificates.certificate799103.1
  rw [permOfArr_xa, permOfArr_ya] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, hx, hy, -⟩ := h
  exact ⟨hx, hy, h1, h2, h3, h4, h5, h6, h7⟩

theorem g24Tau_not_mem : g24Tau ∉ twoBD := by
  have h := Certificates.certificate799103.1
  rw [permOfArr_xa, permOfArr_ya] at h
  exact h.2.2.2.2.2.2.2.2.2.2.1

theorem g24E0_le_DT : g24E0 ≤ ⁅twoBD ⊓ Subgroup.centralizer {g24Tau},
    twoBD ⊓ Subgroup.centralizer {g24Tau}⁆ := by
  have h := Certificates.certificate799103.1
  rw [permOfArr_xa, permOfArr_ya] at h
  rw [g24E0, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem g24Tau_mem_normalizer : g24Tau ∈ Subgroup.normalizer (twoBD : Set (Perm (Fin 1365))) :=
  CFSG.EvenSporadicStandard.G24Aut.mem_normalizer_of_gens g24_basic.1 g24_basic.2.1

theorem twoBD_le_g24R : twoBD ≤ g24R :=
  Subgroup.closure_mono (Set.insert_subset_insert (by simp))

theorem card_g24R_ge : 503193600 ≤ Nat.card g24R := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le twoBD_le_g24R
  have hτR : g24Tau ∈ g24R :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Nat.mul_one] at hc
    have e := Subgroup.eq_of_le_of_card_ge twoBD_le_g24R hc.le
    rw [← e] at hτR
    exact g24Tau_not_mem hτR
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hc
    exact Nat.card_pos.ne' hc
  rw [hc, card_twoBD]
  omega

theorem g24E0_le_twoBD : g24E0 ≤ twoBD := g24E0_le_DT.trans ((commutator_self_le _).trans inf_le_left)

noncomputable def g24Basis : Asc83Table.E9Basis ↥twoBD :=
  have h := g24_basic
  { a := ⟨g24C1, g24E0_le_twoBD (Subgroup.subset_closure (Set.mem_insert _ _))⟩
    b := ⟨g24C2, g24E0_le_twoBD (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩
    ha := Subtype.ext h.2.2.1
    hb := Subtype.ext h.2.2.2.1
    hab := Subtype.ext h.2.2.2.2.1
    card := Asc83Table.card_closure_pair_eq_nine (Subtype.ext h.2.2.1) (Subtype.ext h.2.2.2.1)
      (Subtype.ext h.2.2.2.2.1) (fun e => h.2.2.2.2.2.1 (congrArg Subtype.val e))
      (Asc83Table.not_mem_zpowers_of_ne (Subtype.ext h.2.2.1)
        (fun e => h.2.2.2.2.2.2.1 (congrArg Subtype.val e))
        (fun e => h.2.2.2.2.2.2.2.1 (congrArg Subtype.val e))
        (fun e => h.2.2.2.2.2.2.2.2 (congrArg Subtype.val e))) }

theorem eq_tau_of_centralizes {u : Perm (Fin 1365)} (huR : u ∈ g24R) (hu2 : u ^ 2 = 1)
    (hu1 : u * g24C1 = g24C1 * u) (hu2' : u * g24C2 = g24C2 * u) : u = 1 ∨ u = g24Tau := by
  have h := Certificates.certificate799103.2.1
  rw [permOfArr_xa, permOfArr_ya] at h
  exact h u huR hu2 hu1 hu2'

theorem f3At_g24_e0 {U : Subgroup (Perm (Fin 1365))} (hUR : U ≤ g24R)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU1 : U ≠ ⊥)
    (hcomm : ∀ u ∈ U, u * g24C1 = g24C1 * u ∧ u * g24C2 = g24C2 * u) :
    F3At twoBD g24E0 (Subgroup.centralizer (U : Set (Perm (Fin 1365)))) := by
  have hUV : ∀ u ∈ U, u = 1 ∨ u = g24Tau := fun u hu =>
    eq_tau_of_centralizes (hUR hu) (hU2 u hu) (hcomm u hu).1 (hcomm u hu).2
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hτU : g24Tau ∈ U := by
    rcases hUV u hu with h | h
    · exact absurd h hu1'
    · exact h ▸ hu
  have hC : Subgroup.centralizer (U : Set (Perm (Fin 1365))) =
      Subgroup.centralizer {g24Tau} := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun h => (h _ hτU).symm, fun h v hv => ?_⟩
    rcases hUV v hv with rfl | rfl
    · rw [one_mul, mul_one]
    · exact h.symm
  have h := Certificates.certificate799103.2.2.1
  rw [permOfArr_xa, permOfArr_ya] at h
  rw [F3At, hC]
  exact ⟨g24E0_le_DT, h⟩

theorem exists_conj_eq_g24E0 {E : Subgroup (Perm (Fin 1365))} (hED : E ≤ twoBD)
    (hE9 : Nat.card E = 9) : ∃ g ∈ twoBD, g24E0.map (MulAut.conj g).toMonoidHom = E := by
  have h := Certificates.certificate799103.2.2.2
  rw [permOfArr_xa, permOfArr_ya] at h
  exact h E hED hE9

theorem f3At_g24 {E U : Subgroup (Perm (Fin 1365))} (hED : E ≤ twoBD) (hE : Nat.card E = 9)
    (hUR : U ≤ g24R) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hU1 : U ≠ ⊥)
    (hcomm : ∀ u ∈ U, ∀ e ∈ E, u * e = e * u) :
    F3At twoBD E (Subgroup.centralizer (U : Set (Perm (Fin 1365)))) := by
  obtain ⟨g, hgD, hg⟩ := exists_conj_eq_g24E0 hED hE
  have hU'm : (U.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective U
  have hgc : ∀ c ∈ g24E0, MulAut.conj g c ∈ E := fun c hc => hg ▸ ⟨c, hc, rfl⟩
  have hF := (f3At_g24_e0 (U := U.comap (MulAut.conj g).toMonoidHom) ?_ ?_ ?_ ?_).map
    (MulAut.conj g)
  · rwa [map_conj_eq_self_of_mem hgD, hg, map_centralizer_equiv, hU'm] at hF
  · intro x hx
    have hxR : MulAut.conj g x ∈ g24R := hUR hx
    have hgR := twoBD_le_g24R hgD
    have e : x = g⁻¹ * MulAut.conj g x * g := by
      rw [MulAut.conj_apply]
      group
    rw [e]
    exact g24R.mul_mem (g24R.mul_mem (g24R.inv_mem hgR) hxR) hgR
  · intro x hx
    exact (MulAut.conj g).injective (by rw [map_pow, map_one]; exact hU2 _ hx)
  · intro h
    exact hU1 (by rw [← hU'm, h, Subgroup.map_bot])
  · intro x hx
    have hc1 := hgc _ (Subgroup.subset_closure (Set.mem_insert _ _))
    have hc2 := hgc _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    exact ⟨(MulAut.conj g).injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hc1),
      (MulAut.conj g).injective (by rw [map_mul, map_mul]; exact hcomm _ hx _ hc2)⟩

theorem g24R_eq_N : g24R = Subgroup.normalizer (twoBD : Set (Perm (Fin 1365))) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [g24R, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact Subgroup.le_normalizer (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact Subgroup.le_normalizer (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · exact g24Tau_mem_normalizer
  · rw [CFSG.EvenSporadicStandard.G24Aut.g24_card_normalizer]
    exact card_g24R_ge

theorem evenThetaFacts_twoBD : EvenThetaFacts ↥twoBD := by
  obtain ⟨-, -, -, -, hC, -⟩ := CFSG.EvenSporadicStandard.G24Aut.g24_outer_basic
  have hAut : Nat.card (MulAut ↥twoBD) ≤ 2 * Nat.card ↥twoBD :=
    CFSG.EvenSporadicStandard.G24Aut.g24_aut_card_le
  have hcard : Nat.card (MulAut ↥twoBD) ≤
      Nat.card ↥(Subgroup.normalizer (twoBD : Set (Perm (Fin 1365)))) := by
    rw [CFSG.EvenSporadicStandard.G24Aut.g24_card_normalizer]
    rw [card_twoBD] at hAut
    omega
  have hZ : Subgroup.center ↥twoBD = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hC z fun x hx => ?_)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)).symm
  set ψ := MulEquiv.ofBijective twoBD.normalizerMonoidHom
    (CFSG.EvenSporadicStandard.Induction.AutBound.normalizerMonoidHom_bijective twoBD hC hcard)
    with hψ
  set ι : MulAut ↥twoBD →* Perm (Fin 1365) :=
    (Subgroup.normalizer (twoBD : Set (Perm (Fin 1365)))).subtype.comp ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp ψ.symm.injective
  have hψc : ∀ p : ↥twoBD, ψ ⟨p, Subgroup.le_normalizer p.2⟩ = MulAut.conj p := fun p =>
    MulEquiv.ext fun q => Subtype.ext rfl
  have hιc : ∀ p : ↥twoBD, ι (MulAut.conj p) = p := fun p => by
    rw [hι, MonoidHom.comp_apply, ← hψc p]
    simp
  have hInn : (MulAut.conj : ↥twoBD →* MulAut ↥twoBD).range.map ι = twoBD := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hσ
      rw [hιc]
      exact p.2
    · intro hx
      exact ⟨MulAut.conj ⟨x, hx⟩, MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩, hιc ⟨x, hx⟩⟩
  have hrange : ι.range = g24R := by
    rw [g24R_eq_N]
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨σ, rfl⟩
      exact (ψ.symm σ).2
    · intro hx
      exact ⟨ψ ⟨x, hx⟩, by simp [hι]⟩
  refine ⟨hZ, fun σ hσ => ?_, exists_e9_of_e9Basis g24Basis (MulEquiv.refl _), ?_⟩
  · obtain ⟨y, rfl⟩ := KS14.exists_conj_of_card_mulAut_le hZ hAut σ
      ⟨1, by rw [pow_one]; exact hσ⟩
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  · intro Ē Ū hĒ _ hĒ9 hŪ hŪ1 _ hcomm
    have hF := f3At_g24 (E := Ē.map ι) (U := Ū.map ι) ((Subgroup.map_mono hĒ).trans hInn.le)
      (by rw [Subgroup.card_map_of_injective hιinj, hĒ9])
      ((Subgroup.map_le_range ι Ū).trans hrange.le)
      (by
        rintro _ ⟨u, hu, rfl⟩
        rw [← map_pow, hŪ.2 u hu, map_one])
      (fun h => hŪ1 ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).mp h))
      (by
        rintro _ ⟨u, hu, rfl⟩ _ ⟨e, he, rfl⟩
        rw [← map_mul, ← map_mul, hcomm u hu e he])
    have hF' : F3At ((MulAut.conj : ↥twoBD →* MulAut ↥twoBD).range.map ι) (Ē.map ι)
        ((Subgroup.centralizer (Ū : Set (MulAut ↥twoBD))).map ι) := by
      rw [hInn, map_centralizer_of_injective hιinj, hrange]
      refine (F3At.congr_inf ?_).mpr hF
      rw [inf_comm _ g24R, ← inf_assoc, inf_of_le_left twoBD_le_g24R]
    exact F3At.of_map_injective hιinj hF'

theorem evenThetaFacts_of_g24 {X : Type} [Group X] (h : ChevalleyExceptionalModel X .G2 2 2) :
    EvenThetaFacts X := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Induction.lieModel_g24_equiv
    (Or.inr (Or.inl ⟨rfl, by decide, h⟩)) CFSG.EvenSporadicStandard.G24Model.g24Model_proved
  exact evenThetaFacts_of_mulEquiv e evenThetaFacts_twoBD

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
