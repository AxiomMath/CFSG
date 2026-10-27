module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOvergroupDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxStruct
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieve
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiE7
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiE8
import CFSG.LocalAnalysis.StandardType.GGTorusMaxAssemblyLemmas
import CFSG.LocalAnalysis.StandardType.GGTorusMaxIndexLemma
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R16ExcLabel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremA

theorem tmAsm_card_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G) :
    Nat.card G = orderE7 2 := by
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hsimple hEm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  have e' : G ≃* adjointGroup .E7 (GaloisField 2 1) := Subgroup.topEquiv.symm.trans e
  rw [Nat.card_congr e'.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hGF]
  rfl

theorem tmAsm_card_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G) :
    Nat.card G = orderE8 2 := by
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hsimple hEm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E8 := by rcases hmt with ⟨h, -⟩ | ⟨-, h⟩ <;> [omega; exact h]
  obtain ⟨e⟩ := Y10F.exists_mulEquiv_adjointGroup_of_isLabel_E8 (lab := ⟨t, r, 1⟩) hlab ht hZ
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  have e' : G ≃* adjointGroup .E8 (GaloisField 2 1) := Subgroup.topEquiv.symm.trans e
  rw [Nat.card_congr e'.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hGF]
  rfl


theorem tmAsm_primePower_card_two (q : TauCeti.PrimePower) (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have h1 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact h
  have hp : q.p ∣ 2 := h1 ▸ dvd_pow_self _ q.exponent_pos.ne'
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hp
  refine ⟨hp2, ?_⟩
  rw [hp2] at h1
  exact Nat.pow_right_injective (le_refl 2) (by simpa using h1)

theorem tmAsm_primePower_card_three (q : TauCeti.PrimePower) (h : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have h1 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact h
  have hp : q.p ∣ 3 := h1 ▸ dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hp
  refine ⟨hp3, ?_⟩
  rw [hp3] at h1
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h1)

theorem tmAsm_cast_statedSU (n : ℕ) {p f : ℕ} [Fact p.Prime] (hp : p = 2) (hf : f = 1) {J : Type}
    [Group J] (e : J ≃* StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f)))) :
    Nonempty (J ≃* StatedProj (StatedSU n (2 ^ 1) (GaloisField 2 2))) := by
  subst hp hf
  exact ⟨e⟩

theorem tmAsm_twistedA_two (r : ℕ) (q : TauCeti.PrimePower) (hq : q.card = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) {J : Type} [Group J]
    (e : J ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    Nonempty (J ≃* StatedProj (StatedSU (r + 1) (2 ^ 1) (GaloisField 2 2))) := by
  obtain ⟨hp, hf⟩ := tmAsm_primePower_card_two q hq
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 :=
    (TauCeti.LieTypeIndex.characteristic_twistedA r q).trans hp
  have hf' : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA r q).trans hf
  exact tmAsm_cast_statedSU (r + 1) hc hf'
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv))

theorem tmAsm_E7
    (hOver : LSS92MaxOvergroupInput) (hLie : TmLieOutAll) (hSpor : TmSporadicOutInput)
    (hLieOrd : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hSporOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (hK : KProper InCatalog G) (E : Subgroup G) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 7) : IsCoatom (Subgroup.normalizer (E : Set G)) := by
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7'
  have hMcard : Nat.card (Subgroup.normalizer (E : Set G)) = 3 ^ 7 * 2903040 := by
    rw [tmStruct_card_E7 G hEm hsimple E hE hcard, hW]
  have hcent := tmStruct_cent_E7 G hEm hsimple E hE hcard
  have hirr := tmStruct_irred_E7 G hEm hsimple E hE hcard
  have hG := tmAsm_card_E7 G hEm hsimple
  have hE3p : IsPGroup 3 E := IsPGroup.of_card (n := 7) hcard
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE0 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hsyl : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ Subgroup.normalizer (E : Set G) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine tmAsm_exists_sylow_le 3 _ ?_
    rw [hMcard, hG]
    have hk : orderE7 2 = 3 ^ 7 * 2903040 * 1259653636703600996790650798080 := by
      norm_num [orderE7]
    have hfac := Nat.factorization_mul (show (3 ^ 7 * 2903040 : ℕ) ≠ 0 by norm_num)
      (show (1259653636703600996790650798080 : ℕ) ≠ 0 by norm_num)
    have h3 : (1259653636703600996790650798080 : ℕ).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [hk, hfac, Finsupp.add_apply, h3, add_zero]
  refine tmAsm_isCoatom_of_coatom_overgroups _
    (tmAsm_normalizer_ne_top E hEcomm (by norm_num) hcard) ?_
  intro H hHc hMH
  haveI := hsimple
  rcases hOver G 7 hEm hsimple hK E hE hcard H hHc hMH with
    ⟨P, hPH, hPn, hP2, -, hv⟩ | ⟨hrow, hsurv⟩ | ⟨J, hJH, hJn, hJs, hJna, hJC⟩
  · exact tmAsm_case_parabolic E P H 8 hE.2 hMH.le hPH hPn hP2 hcent
      (by rw [hMcard]; norm_num) (by simpa using hv)
  · have hdvd : Nat.card (Subgroup.normalizer (E : Set G)) ∣ Nat.card H :=
      Subgroup.card_dvd_of_le hMH.le
    have hrows : ∀ n ∈ tmRowOrders 7, 3 ^ 7 * 2903040 ∣ n →
        n = 3 ^ 7 * 2903040 ∨ n = tmSurvivorOrder 7 := by decide +kernel
    rcases hrows _ hrow (hMcard ▸ hdvd) with h | h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hMH.le (by rw [h, hMcard])) hMH.ne
    · obtain ⟨Q, hQH, hQn, hQ3⟩ := hsurv h
      exact tmAsm_case_normal_three E H Q hE3p hE0 hEcomm hcent hirr hsyl hMH hQH hQn hQ3
  · have hJne : J ≠ ⊤ := by
      intro h
      apply hHc.1
      rw [eq_top_iff]
      exact h ▸ hJH
    haveI := hJs
    have hcat : InCatalog J := tmAsm_inCatalog_of_kProper hK J hJne hJna
    have hdvdJ : Nat.card J ∣ orderE7 2 := hG ▸ Subgroup.card_subgroup_dvd_card J
    have hltJ : Nat.card J < orderE7 2 := by
      rw [← hG]
      exact lt_of_le_of_ne (Subgroup.card_le_card_group J)
        (fun h => hJne ((Subgroup.card_eq_iff_eq_top J).1 h))
    have hMdvd : Nat.card (Subgroup.normalizer (E : Set G)) ∣ Nat.card (MulAut J) :=
      tmAsm_card_dvd_aut _ H J hMH.le hJH hJn hJC
    obtain ⟨d, q, hd, hq, ⟨eJ⟩⟩ :=
      tmSieve_E7 hLie hSpor hLieOrd hSporOrd J hcat hJna hdvdJ hltJ (hMcard ▸ hMdvd)
    obtain ⟨d1, hv1⟩ := d
    simp only at hd
    subst hd
    obtain ⟨e2⟩ := tmAsm_twistedA_two 8 q hq hv1 eJ
    obtain ⟨π, φ, hπs, hπk, -⟩ := tmStruct_E7 G hEm hsimple E hE hcard
    let ψ0 : ↥(Subgroup.normalizer (E : Set G)) →* MulAut J :=
      (tmAsm_conj H J hJH hJn).comp (Subgroup.inclusion hMH.le)
    have hψ0 : Function.Injective ψ0 :=
      (tmAsm_conj_injective H J hJH hJn hJC).comp (Subgroup.inclusion_injective hMH.le)
    let ψ : ↥(Subgroup.normalizer (E : Set G)) →*
        MulAut (StatedProj (StatedSU 9 (2 ^ 1) (GaloisField 2 2))) :=
      (MulAut.congr e2).toMonoidHom.comp ψ0
    have hψ : Function.Injective ψ := (MulAut.congr e2).injective.comp hψ0
    have hK4 : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by omega)]; norm_num
    exact tmSemi_E7 E hE hcard π hπs hπk hcent hirr (GaloisField 2 2) hK4 ψ hψ


theorem tmAsm_E8
    (hOver : LSS92MaxOvergroupInput) (hLie : TmLieOutAll) (hSpor : TmSporadicOutInput)
    (hLieOrd : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hSporOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (hK : KProper InCatalog G) (E : Subgroup G) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 8) : IsCoatom (Subgroup.normalizer (E : Set G)) := by
  have hW : Nat.card (WeylGroup Tag.E8) = 696729600 :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E8'
  have hMcard : Nat.card (Subgroup.normalizer (E : Set G)) = 3 ^ 8 * 696729600 := by
    rw [tmStruct_card_E8 G hEm hsimple E hE hcard, hW]
  have hcent := tmStruct_cent_E8 G hEm hsimple E hE hcard
  have hirr := tmStruct_irred_E8 G hEm hsimple E hE hcard
  have hG := tmAsm_card_E8 G hEm hsimple
  have hE3p : IsPGroup 3 E := IsPGroup.of_card (n := 8) hcard
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE0 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hsyl : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ Subgroup.normalizer (E : Set G) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine tmAsm_exists_sylow_le 3 _ ?_
    rw [hMcard, hG]
    have hk : orderE8 2 = 3 ^ 8 * 696729600 *
        73897791064615528590603056885624799443602704935739140866048000 := by
      norm_num [orderE8]
    have hfac := Nat.factorization_mul (show (3 ^ 8 * 696729600 : ℕ) ≠ 0 by norm_num)
      (show (73897791064615528590603056885624799443602704935739140866048000 : ℕ) ≠ 0 by norm_num)
    have h3 : (73897791064615528590603056885624799443602704935739140866048000 : ℕ).factorization 3
        = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [hk, hfac, Finsupp.add_apply, h3, add_zero]
  refine tmAsm_isCoatom_of_coatom_overgroups _
    (tmAsm_normalizer_ne_top E hEcomm (by norm_num) hcard) ?_
  intro H hHc hMH
  haveI := hsimple
  rcases hOver G 8 hEm hsimple hK E hE hcard H hHc hMH with
    ⟨P, hPH, hPn, hP2, -, hv⟩ | ⟨hrow, hsurv⟩ | ⟨J, hJH, hJn, hJs, hJna, hJC⟩
  · exact tmAsm_case_parabolic E P H 11 hE.2 hMH.le hPH hPn hP2 hcent
      (by rw [hMcard]; norm_num) (by simpa using hv)
  · have hdvd : Nat.card (Subgroup.normalizer (E : Set G)) ∣ Nat.card H :=
      Subgroup.card_dvd_of_le hMH.le
    have hrows : ∀ n ∈ tmRowOrders 8, 3 ^ 8 * 696729600 ∣ n →
        n = 3 ^ 8 * 696729600 ∨ n = tmSurvivorOrder 8 := by decide +kernel
    rcases hrows _ hrow (hMcard ▸ hdvd) with h | h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hMH.le (by rw [h, hMcard])) hMH.ne
    · obtain ⟨Q, hQH, hQn, hQ3⟩ := hsurv h
      exact tmAsm_case_normal_three E H Q hE3p hE0 hEcomm hcent hirr hsyl hMH hQH hQn hQ3
  · have hJne : J ≠ ⊤ := by
      intro h
      apply hHc.1
      rw [eq_top_iff]
      exact h ▸ hJH
    haveI := hJs
    have hcat : InCatalog J := tmAsm_inCatalog_of_kProper hK J hJne hJna
    have hdvdJ : Nat.card J ∣ orderE8 2 := hG ▸ Subgroup.card_subgroup_dvd_card J
    have hltJ : Nat.card J < orderE8 2 := by
      rw [← hG]
      exact lt_of_le_of_ne (Subgroup.card_le_card_group J)
        (fun h => hJne ((Subgroup.card_eq_iff_eq_top J).1 h))
    have hMdvd : Nat.card (Subgroup.normalizer (E : Set G)) ∣ Nat.card (MulAut J) :=
      tmAsm_card_dvd_aut _ H J hMH.le hJH hJn hJC
    let ψ0 : ↥(Subgroup.normalizer (E : Set G)) →* MulAut J :=
      (tmAsm_conj H J hJH hJn).comp (Subgroup.inclusion hMH.le)
    have hψ0 : Function.Injective ψ0 :=
      (tmAsm_conj_injective H J hJH hJn hJC).comp (Subgroup.inclusion_injective hMH.le)
    rcases tmSieve_E8 hLie hSpor hLieOrd hSporOrd J hcat hJna hdvdJ hltJ (hMcard ▸ hMdvd) with
      ⟨d, q, hd, hq, ⟨eJ⟩⟩ | ⟨d, q, hd, hq, ⟨eJ⟩⟩
    · obtain ⟨d1, hv1⟩ := d
      simp only at hd
      subst hd
      obtain ⟨e2⟩ := tmAsm_twistedA_two 9 q hq hv1 eJ
      obtain ⟨π, φ, hπs, hπk, -⟩ := tmStruct_E8 G hEm hsimple E hE hcard
      let ψ : ↥(Subgroup.normalizer (E : Set G)) →*
          MulAut (StatedProj (StatedSU 10 (2 ^ 1) (GaloisField 2 2))) :=
        (MulAut.congr e2).toMonoidHom.comp ψ0
      have hψ : Function.Injective ψ := (MulAut.congr e2).injective.comp hψ0
      have hK4 : Nat.card (GaloisField 2 2) = 4 := by
        rw [GaloisField.card 2 2 (by omega)]; norm_num
      exact tmSemi_E8 E hE hcard π hπs hπk hcent hirr (GaloisField 2 2) hK4 ψ hψ
    · obtain ⟨hp3, hf1⟩ := tmAsm_primePower_card_three q hq
      have hJcard : Nat.card J = 2 ^ 12 * 3 ^ 12 * 5 ^ 2 * 7 * 13 := by
        rw [hLieOrd d J ⟨eJ⟩, hd]
        show CFSG.Open.orderD 4 q.card = _
        rw [hq]
        decide +kernel
      have hAut : Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := hLie d J ⟨eJ⟩
      have hout : tmLieOut d.1 = 24 := by
        rw [hd]
        simp only [tmLieOut]
        rw [hq, hf1]
        norm_num
      have hHA : Nat.card H ∣ Nat.card (MulAut J) :=
        Subgroup.card_dvd_of_injective _ (tmAsm_conj_injective H J hJH hJn hJC)
      have hHle : Nat.card H ≤ 26 * Nat.card (Subgroup.normalizer (E : Set G)) := by
        have h1 : Nat.card H ≤ Nat.card J * 24 :=
          Nat.le_of_dvd (by rw [hJcard]; norm_num) (hHA.trans (hout ▸ hAut))
        rw [hMcard]
        rw [hJcard] at h1
        omega
      have hMcard' : Nat.card ↥((Subgroup.normalizer (E : Set G)).subgroupOf H) =
          Nat.card (Subgroup.normalizer (E : Set G)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH.le).toEquiv
      have hidx : ((Subgroup.normalizer (E : Set G)).subgroupOf H).index ≤ 26 :=
        tmIdx_index_le_of_card_le _ (by rw [hMcard']; exact hHle)
      haveI : IsSimpleGroup (J.subgroupOf H) :=
        (Subgroup.subgroupOfEquivOfLe hJH).isSimpleGroup
      exact tmIdx_omega8plus3_excluded ((Subgroup.normalizer (E : Set G)).subgroupOf H)
        (J.subgroupOf H)
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv, hJcard])
        (by rw [hMcard', hMcard]; norm_num) hidx


theorem tmAsm_lss92TorusMaxInput
    (hOver : LSS92MaxOvergroupInput) (hLie : TmLieOutAll) (hSpor : TmSporadicOutInput)
    (hLieOrd : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hSporOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable) :
    LSS92TorusMaxInput := by
  intro G _ _ m hEm hsimple hK E hE hcard
  have hm : m = 7 ∨ m = 8 := by
    obtain ⟨-, ⟨t, r, n⟩, ⟨hmt, -, -⟩, -⟩ := exists_label_of_marking hsimple hEm
    rcases hmt with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hm with rfl | rfl
  · exact tmAsm_E7 hOver hLie hSpor hLieOrd hSporOrd G hEm hsimple hK E hE hcard
  · exact tmAsm_E8 hOver hLie hSpor hLieOrd hSporOrd G hEm hsimple hK E hE hcard

end CFSG.StandardType.FrameRoute

end
