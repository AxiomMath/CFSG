module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a
import CFSG.GroupTheory.PElementSubgroup
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

variable {G : Type} [Group G] [Finite G]

private theorem r95c_map_subgroupOf_I9_eq_bot (H : Subgroup G) :
    ((I9 H).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).1 (Subgroup.mem_subgroupOf.1 hx)

private theorem r95c_img9_le_of_le_sup {H K L : Subgroup G} (hLH : L ≤ H)
    (hKL : K ≤ L ⊔ I9 H) : img9 H K ≤ img9 H L := by
  have hIH : I9 H ≤ H := Subgroup.map_subtype_le _
  calc img9 H K ≤ img9 H (L ⊔ I9 H) := by
        unfold img9
        exact Subgroup.map_mono fun x hx =>
          Subgroup.mem_subgroupOf.2 (hKL (Subgroup.mem_subgroupOf.1 hx))
    _ = img9 H L := by
        unfold img9
        rw [Subgroup.subgroupOf_sup hLH hIH, Subgroup.map_sup,
          r95c_map_subgroupOf_I9_eq_bot H, sup_bot_eq]

private theorem r95c_mem_I9_of_mk_eq {H : Subgroup G} {a b : ↥H}
    (h : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) a =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) b) :
    ((a : G)⁻¹ * (b : G)) ∈ I9 H := by
  obtain ⟨z, hz, hzy⟩ := (QuotientGroup.mk'_eq_mk' (CFSG.pPrimeCore 3 ↥H)).1 h
  have hz' : (z : G) ∈ I9 H :=
    (Subgroup.mem_map_iff_mem H.subtype_injective).2 hz
  have hzy' : (b : G) = (a : G) * (z : G) := by
    rw [← hzy]; rfl
  have hza : (a : G)⁻¹ * (b : G) = (z : G) := by
    rw [hzy']; group
  rw [hza]; exact hz'

private theorem r95c_pRank_le_one {D : Data G} {Y H D₃ S : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hSL : S ≤ L9 Y H ⊔ I9 H) :
    CFSG.Open.pRank 3 S ≤ 1 := by
  have hLH : L9 Y H ≤ H := L9_le_of_le hyp.2.1.1
  have hSH : S ≤ H := hSL.trans (sup_le hLH (Subgroup.map_subtype_le _))
  have hle : img9 H S ≤ img9 H (L9 Y H) := r95c_img9_le_of_le_sup hLH hSL
  calc CFSG.Open.pRank 3 S = CFSG.Open.pRank 3 (⊤ : Subgroup ↥S) :=
        CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) S
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img9 H S)) :=
        CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
          (toImg9 hSH) (toImg9_surjective hSH) (coprime_card_ker_toImg9 hSH)
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(img9 H (L9 Y H))) :=
        CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_le_of_injective 3 (by norm_num)
          (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(L9 Y H)) :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
          (toImg9 hLH) (toImg9_surjective hLH) (coprime_card_ker_toImg9 hLH)).symm
    _ = CFSG.Open.pRank 3 (L9 Y H) :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num)
          (L9 Y H)).symm
    _ = 1 := hyp.2.1.2.2

private theorem r95c_not_hasE9 {D : Data G} {Y H D₃ S : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hSL : S ≤ L9 Y H ⊔ I9 H) :
    ¬ CFSG.GroupTheory.ThreeTranspositions.HasE9 ↥S := by
  intro h
  have h2 := CFSG.GroupTheory.ThreeTranspositions.two_le_pRank_of_hasE9_subgroup S h
  have h1 := r95c_pRank_le_one hyp hSL
  omega

private theorem r95c_mem_uniqueSet {D : Data G} {Y H D₃ T A : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hTM : T ≤ D.M) (hTL : T ≤ L9 Y H ⊔ I9 H)
    (hDT : D₃ ≤ T) (hAT : A ≤ T) (hA3 : Nat.card A = 3) :
    A ∈ uniqueSet D.M := by
  have hDU : D₃ ∈ uniqueSet D.M :=
    hyp.1.2.2 D₃ (hyp.2.2.1.trans (opp_le_self 3 Y)) hyp.2.2.2
  obtain ⟨l, hl, hAl⟩ :=
    exists_map_conj_eq_of_card_eq_three (r95c_not_hasE9 hyp hTL) hAT hDT hA3 hyp.2.2.2
  have key : D₃.map (MulAut.conj l⁻¹).toMonoidHom = A := by
    rw [← hAl, Subgroup.map_map]
    have hcomp : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  rw [← key]
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.conj_mem_uniqueSet hDU (hTM (T.inv_mem hl))

private theorem r95c_calNOf_ne {D : Data G} {H S : Subgroup G} (hH : H ≠ ⊤)
    (hHM : ¬ H ≤ D.M) (hSH : S ≤ H) : calNOf S ≠ {D.M} := by
  obtain ⟨N, hN, hHN⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  intro h
  have : N ∈ calNOf S := ⟨hN, hSH.trans hHN⟩
  rw [h, Set.mem_singleton_iff] at this
  exact hHM (this ▸ hHN)

private theorem r95c_L9_le_sup {Y H S : Subgroup G} (hYH : Y ≤ H)
    (hSL : S ≤ L9 Y H ⊔ I9 H) : L9 S H ≤ L9 Y H ⊔ I9 H := by
  have hn : H ≤ normalizer ((L9 Y H ⊔ I9 H : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_L9 Y H)
      (CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  refine iSup_le fun h => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxS : x ∈ L9 Y H ⊔ I9 H := hSL (opp_le_self 3 S hx)
  change (h : G) * x * (h : G)⁻¹ ∈ L9 Y H ⊔ I9 H
  exact (Subgroup.mem_normalizer_iff.1 (hn h.2) x).mp hxS

private theorem r95c_hyp91_of_le {D : Data G} {Y H D₃ T : Subgroup G} (hyp : Hyp91 D Y H D₃)
    (hH : H ≠ ⊤) (hTH : T ≤ H) (hTM : T ≤ D.M) (hTL : T ≤ L9 Y H ⊔ I9 H)
    (hDT : D₃ ≤ T) : Hyp91 D T H D₃ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : Nat.card D₃ = 3 := hyp.2.2.2
  have hHM : ¬ H ≤ D.M := hyp.2.1.2.1
  have hD3' : IsPGroup 3 D₃ := IsPGroup.of_card (n := 1) (by rw [hD3, pow_one])
  have hDO : D₃ ≤ Opp 3 T :=
    CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_three hD3' hDT
  refine ⟨⟨hTM, r95c_calNOf_ne hH hHM hTH,
    fun A hAT hA3 => r95c_mem_uniqueSet hyp hTM hTL hDT hAT hA3⟩,
    ⟨hTH, hHM, ?_⟩, hDO, hD3⟩
  apply le_antisymm
  · exact r95c_pRank_le_one hyp (r95c_L9_le_sup hyp.2.1.1 hTL)
  · exact CFSG.SectionRank.le_pRank (by norm_num) (hDO.trans (opp_le_L9 T H))
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hD3) (k := 1) (by rw [hD3, pow_one])

private theorem r95c_img9_le_T {D : Data G} {Y H : Subgroup G}
    (hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) :
    img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M ⊓ (L9 Y H ⊔ I9 H)) := by
  intro z hz
  obtain ⟨l, hl, hlz⟩ := Subgroup.mem_map.1 hz
  obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 (hLM hz)
  have hli : ((l : G)⁻¹ * (m : G)) ∈ I9 H :=
    r95c_mem_I9_of_mk_eq (hlz.trans hmz.symm)
  have hlL : (l : G) ∈ L9 Y H := Subgroup.mem_subgroupOf.1 hl
  have hmHM : (m : G) ∈ H ⊓ D.M := Subgroup.mem_subgroupOf.1 hm
  have hmLI : (m : G) ∈ L9 Y H ⊔ I9 H := by
    have h := Subgroup.mul_mem_sup hlL hli
    rw [mul_inv_cancel_left] at h
    exact h
  exact Subgroup.mem_map.2 ⟨m, Subgroup.mem_subgroupOf.2 ⟨hmHM, hmLI⟩, hmz⟩

private theorem r95c_exists_hom {Y H T : Subgroup G} (hYH : Y ≤ H) (hTH : T ≤ H)
    (hTL : T ≤ L9 Y H ⊔ I9 H) (hLT : img9 H (L9 Y H) ≤ img9 H T) :
    ∃ ρ : ↥T →* Lbar9 Y H, Function.Surjective ρ ∧
      ∀ t : ↥T, ρ t = 1 → (t : G) ∈ I9 H := by
  have hLH : L9 Y H ≤ H := L9_le_of_le hYH
  have hle : img9 H T ≤ img9 H (L9 Y H) := r95c_img9_le_of_le_sup hLH hTL
  let ρ : ↥T →* Lbar9 Y H := (Subgroup.inclusion hle).comp (toImg9 hTH)
  have hsurj : Function.Surjective ρ := by
    intro z
    obtain ⟨t, ht⟩ := toImg9_surjective hTH ⟨z.1, hLT z.2⟩
    exact ⟨t, Subtype.ext
      (congrArg (fun x : ↥(img9 H T) => (x : Hbar9 H)) ht)⟩
  have hker : ∀ t : ↥T, ρ t = 1 → (t : G) ∈ I9 H := by
    intro t ht
    have h1 : toImg9 hTH t = 1 := by
      apply Subgroup.inclusion_injective hle
      rw [map_one]
      simpa [ρ] using ht
    exact (mem_ker_toImg9 hTH).1 (MonoidHom.mem_ker.2 h1)
  exact ⟨ρ, hsurj, hker⟩

private theorem r95c_map_eq_top_of_normal {A B : Type*} [Group A] [Group B] [IsSimpleGroup B]
    (ρ : A →* B) (hρ : Function.Surjective ρ) {N : Subgroup A} [N.Normal] {d : A}
    (hd : d ∈ N) (hd1 : ρ d ≠ 1) : N.map ρ = ⊤ := by
  haveI : (N.map ρ).Normal := (inferInstance : N.Normal).map ρ hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ρ) with h | h
  · exfalso
    have : ρ d ∈ N.map ρ := ⟨d, hd, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hd1 this
  · exact h

private theorem r95c_quot_pPrimeCore_equiv {X Λ : Type*} [Group X] [Finite X] [Group Λ]
    [IsSimpleGroup Λ] (φ : X →* Λ) (hφ : Function.Surjective φ)
    (hker : Nat.Coprime 3 (Nat.card φ.ker)) (h3 : 3 ∣ Nat.card Λ) :
    Nonempty ((X ⧸ CFSG.pPrimeCore 3 X) ≃* Λ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : φ.ker ≤ CFSG.pPrimeCore 3 X :=
    CFSG.le_pPrimeCore_of_normal_coprime (MonoidHom.normal_ker φ) hker
  have h2 : CFSG.pPrimeCore 3 X ≤ φ.ker := by
    haveI : ((CFSG.pPrimeCore 3 X).map φ).Normal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := X)).map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pPrimeCore 3 X).map φ) with h | h
    · rw [Subgroup.map_eq_bot_iff] at h
      exact h
    · exfalso
      have hdiv : Nat.card Λ ∣ Nat.card (CFSG.pPrimeCore 3 X) := by
        rw [← Subgroup.card_top (G := Λ), ← h]
        exact Subgroup.card_map_dvd _ _
      have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 X)) :=
        CFSG.pPrimeCore_coprime_card
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime 3)).1 hcop (h3.trans hdiv)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm h2 h1)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

private theorem r95c_equiv_of_hom {T D₃ I : Subgroup G} {Λ : Type} [Group Λ] [IsSimpleGroup Λ]
    (hD3 : Nat.card D₃ = 3) (hDT : D₃ ≤ T) (hI : Nat.Coprime 3 (Nat.card I))
    (ρ : ↥T →* Λ) (hρ : Function.Surjective ρ)
    (hker : ∀ t : ↥T, ρ t = 1 → (t : G) ∈ I) :
    Nonempty (BarO3 (Opp 3 T) ≃* Λ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXT : Opp 3 T ≤ T := opp_le_self 3 T
  have hD3' : IsPGroup 3 D₃ := IsPGroup.of_card (n := 1) (by rw [hD3, pow_one])
  have hD3P : D₃ ≤ Opp 3 T :=
    CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_three hD3' hDT
  have h3dvd : 3 ∣ Nat.card D₃ := by rw [hD3]
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  let dT : ↥T := ⟨d, hDT d.2⟩
  have hdG : orderOf (dT : G) = 3 := by
    change orderOf ((d : ↥D₃) : G) = 3
    rw [Subgroup.orderOf_coe, hd]
  have hd1 : ρ dT ≠ 1 := by
    intro h1
    have hmemI : (dT : G) ∈ I := hker dT h1
    have h3dvdI : 3 ∣ Nat.card I := by
      have h := Subgroup.orderOf_dvd_natCard I hmemI
      rwa [hdG] at h
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime 3)).1 hI h3dvdI
  let φ : ↥(Opp 3 T) →* Λ := ρ.comp (Subgroup.inclusion hXT)
  have hdTmem : dT ∈ (Opp 3 T).subgroupOf T := Subgroup.mem_subgroupOf.2 (hD3P d.2)
  haveI : ((Opp 3 T).subgroupOf T).Normal := normal_opp_subgroupOf 3 T
  have hrange : φ.range = ⊤ := by
    change (ρ.comp (Subgroup.inclusion hXT)).range = ⊤
    rw [← MonoidHom.map_range ρ (Subgroup.inclusion hXT), Subgroup.inclusion_range]
    exact r95c_map_eq_top_of_normal ρ hρ (N := (Opp 3 T).subgroupOf T) (d := dT) hdTmem hd1
  have hφ : Function.Surjective φ := MonoidHom.range_eq_top.1 hrange
  have h3 : 3 ∣ Nat.card Λ := by
    have ho : orderOf (ρ dT) = 3 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have : dT ^ 3 = 1 := by
          have hoT : orderOf dT = 3 := by rw [← Subgroup.orderOf_coe (a := dT), hdG]
          simpa [hoT] using pow_orderOf_eq_one dT
        rw [this, map_one]
      · exact hd1
    simpa [ho] using orderOf_dvd_natCard (ρ dT)
  have hker' : Nat.Coprime 3 (Nat.card φ.ker) := by
    have hmaple : φ.ker.map (Opp 3 T).subtype ≤ I := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker (Subgroup.inclusion hXT x) hx
    have hdiv : Nat.card φ.ker ∣ Nat.card I := by
      rw [← Subgroup.card_map_of_injective (Opp 3 T).subtype_injective]
      exact Subgroup.card_dvd_of_le hmaple
    exact Nat.Coprime.coprime_dvd_right hdiv hI
  exact r95c_quot_pPrimeCore_equiv φ hφ hker' h3

theorem r95_exists_core {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃)
    (hH : H ≠ ⊤) (hS : IsSimpleGroup (Lbar9 Y H))
    (hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) :
    ∃ K : Subgroup G, Hyp91 D K H D₃ ∧ Nonempty (BarO3 (Opp 3 K) ≃* Lbar9 Y H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hS
  have hYH : Y ≤ H := hyp.2.1.1
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hTH : H ⊓ D.M ⊓ (L9 Y H ⊔ I9 H) ≤ H := inf_le_left.trans inf_le_left
  have hTM : H ⊓ D.M ⊓ (L9 Y H ⊔ I9 H) ≤ D.M := inf_le_left.trans inf_le_right
  have hTL : H ⊓ D.M ⊓ (L9 Y H ⊔ I9 H) ≤ L9 Y H ⊔ I9 H := inf_le_right
  have hDT : D₃ ≤ H ⊓ D.M ⊓ (L9 Y H ⊔ I9 H) :=
    le_inf (le_inf (hyp.2.2.1.trans (hXY.trans hYH)) (hyp.2.2.1.trans (hXY.trans hyp.1.1)))
      ((hyp.2.2.1.trans (opp_le_L9 Y H)).trans le_sup_left)
  have hI : Nat.Coprime 3 (Nat.card (I9 H)) := by
    rw [I9, Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  refine ⟨H ⊓ D.M ⊓ (L9 Y H ⊔ I9 H),
    r95c_hyp91_of_le hyp hH hTH hTM hTL hDT, ?_⟩
  obtain ⟨ρ, hρ, hker⟩ := r95c_exists_hom hYH hTH hTL (r95c_img9_le_T hLM)
  exact r95c_equiv_of_hom hyp.2.2.2 hDT hI ρ hρ hker

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
