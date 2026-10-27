module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKeySetup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddKF7
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentA
import CFSG.GroupTheory.PrimeOrderSubgroups
import CFSG.Walter.Bender1970.S3.Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private lemma altOff_eq_altCent (s : Finset (Fin 10)) :
    A10Perm.altOff s =
      CFSG.ComponentClassification.CatFactsL4U4.AltCent.altOff s := by
  ext x
  rw [A10Perm.mem_altOff_iff]
  constructor
  · rintro ⟨hxalt, hxfix⟩
    exact CFSG.ComponentClassification.CatFactsL4U4.AltCent.mem_altOff hxfix
      (Equiv.Perm.mem_alternatingGroup.mp hxalt)
  · intro hx
    exact ⟨Equiv.Perm.mem_alternatingGroup.mpr
        (CFSG.ComponentClassification.CatFactsL4U4.AltCent.sign_of_mem_altOff hx),
      fun a ha => CFSG.ComponentClassification.CatFactsL4U4.AltCent.apply_eq_of_mem_altOff
        hx ha⟩

private lemma card_altOff_of_card_eq_three (s : Finset (Fin 10)) (hs : s.card = 3) :
    Nat.card ↥(A10Perm.altOff s) = 2520 := by
  rw [altOff_eq_altCent,
    CFSG.ComponentClassification.CatFactsL4U4.AltCent.card_altOff s (by rw [hs]; norm_num),
    hs]
  norm_num [Nat.factorial]

private lemma isSimpleGroup_altOff_of_card_eq_three (s : Finset (Fin 10)) (hs : s.card = 3) :
    IsSimpleGroup ↥(A10Perm.altOff s) := by
  rw [altOff_eq_altCent]
  exact CFSG.ComponentClassification.CatFactsL4U4.AltCent.isSimpleGroup_altOff s
    (by rw [hs]; norm_num)

private lemma isPerfect_altOff_of_card_eq_three (s : Finset (Fin 10)) (hs : s.card = 3) :
    Group.IsPerfect ↥(A10Perm.altOff s) := by
  haveI hsimple : IsSimpleGroup ↥(A10Perm.altOff s) :=
    isSimpleGroup_altOff_of_card_eq_three s hs
  refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative ?_
  intro hcomm
  haveI := hcomm
  have hp := (Group.is_simple_iff_prime_card (α := ↥(A10Perm.altOff s))).mp hsimple
  rw [card_altOff_of_card_eq_three s hs] at hp
  norm_num at hp

private lemma altOff_le_centralizer_singleton {s : Finset (Fin 10)} {b : Equiv.Perm (Fin 10)}
    (hb : b.support = s) :
    A10Perm.altOff s ≤ Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin 10))) := by
  intro σ hσ
  rw [Subgroup.mem_centralizer_iff]
  intro τ hτ
  rw [Set.mem_singleton_iff] at hτ
  subst τ
  rw [A10Perm.mem_altOff_iff] at hσ
  have hdisj : Equiv.Perm.Disjoint σ b := by
    intro x
    by_cases hx : σ x = x
    · exact Or.inl hx
    · refine Or.inr ?_
      by_contra hbne
      exact hx (hσ.2 x (hb ▸ (Equiv.Perm.mem_support.mpr hbne)))
  exact (hdisj.commute.symm).eq

private lemma exists_altOff_le_map_inf (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hdeg : F.deg B = 3) :
    ∃ s : Finset (Fin 10), s.card = 3 ∧
      A10Perm.altOff s ≤ ((c.L.subgroupOf D.M) ⊓
        Subgroup.centralizer ((B.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)).map F.phiA := by
  classical
  have hBM : B ≤ D.M := hBA.trans F.A_le_M
  have hBL : B ≤ c.L := hBA.trans (F.A_le.trans F.P_le_L)
  obtain ⟨b, hbB, _, hBz⟩ :=
    CFSG.GroupTheory.exists_generator_of_card_prime (p := 3) (by norm_num) hB3
  let bM : ↥D.M := ⟨b, hBM hbB⟩
  let s : Finset (Fin 10) := (F.phiA bM).support
  have hs : s.card = 3 := by
    have hdeg' : F.deg (Subgroup.zpowers b) = 3 := by rw [← hBz]; exact hdeg
    rw [F.deg_zpowers_eq (hBL hbB)] at hdeg'
    simpa [s, bM] using hdeg'
  have hzpow : (Subgroup.zpowers b).subgroupOf D.M = Subgroup.zpowers bM := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa [bM] using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [bM] using congrArg Subtype.val hn⟩
  have hBmap : (B.subgroupOf D.M).map F.phiA = Subgroup.zpowers (F.phiA bM) := by
    calc (B.subgroupOf D.M).map F.phiA
        = ((Subgroup.zpowers b).subgroupOf D.M).map F.phiA := by rw [hBz]
      _ = (Subgroup.zpowers bM).map F.phiA := by rw [hzpow]
      _ = Subgroup.zpowers (F.phiA bM) := MonoidHom.map_zpowers F.phiA bM
  have hleL : A10Perm.altOff s ≤ (c.L.subgroupOf D.M).map F.phiA := by
    rw [map_L_phiA]
    exact fun σ hσ => (A10Perm.mem_altOff_iff.mp hσ).1
  have hleCent : A10Perm.altOff s ≤
      Subgroup.centralizer (((B.subgroupOf D.M).map F.phiA :
        Subgroup (Equiv.Perm (Fin 10))) : Set (Equiv.Perm (Fin 10))) := by
    rw [hBmap, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact altOff_le_centralizer_singleton rfl
  have hBgroup : IsPGroup 3 (B.subgroupOf D.M) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hB3]
    norm_num
  have hBsub : B.subgroupOf D.M ≤ c.L.subgroupOf D.M :=
    Subgroup.subgroupOf_mono D.M hBL
  have hmap := CoprimeImage.map_inf_centralizer_of_coprime_ker (p := 3) (by norm_num)
    F.phiA F.coprime_card_ker_phiA hBgroup hBsub
  refine ⟨s, hs, ?_⟩
  rw [hmap]
  exact le_inf hleL hleCent

private lemma normalizer_ne_top_of_card_eq_three (F : A10Frame c) {B : Subgroup G}
    (hB3 : Nat.card B = 3) :
    Subgroup.normalizer (B : Set G) ≠ ⊤ := by
  intro htop
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB3
    norm_num at hB3
  haveI hBnormal : B.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
  haveI hGsimple : IsSimpleGroup G := D.standing.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with hbot | htopB
  · exact hBne hbot
  · rw [htopB] at hB3
    have hGcard : Nat.card G = 3 := by simpa using hB3
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsCyclic G := isCyclic_of_prime_card hGcard
    have hcomm : IsMulCommutative G := IsCyclic.isMulCommutative
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    exact hab (hcomm.is_comm.comm a b)

private lemma bar_kernel_le {A : Type} [Group A] [Finite A] {H : Subgroup G}
    {S : Subgroup (Equiv.Perm (Fin 10))}
    (K5 : Subgroup ↥H) [K5.Normal] (eY : A →* ↥H) (gY : A →* (↥H ⧸ K5))
    (hK5 : K5 = CFSG.pPrimeCore 5 ↥H)
    (hgY : gY = (QuotientGroup.mk' K5).comp eY)
    (heY : Function.Injective eY) (hSsimple : IsSimpleGroup ↥S)
    (hScard : Nat.card ↥S = 2520) (f0 : A →* ↥S) (hf0 : Function.Surjective f0) :
    gY.ker ≤ f0.ker := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hker_dvd : Nat.card gY.ker ∣ Nat.card K5 := by
    rw [hgY, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact Subgroup.card_comap_dvd_of_injective K5 eY heY
  have hker_cop : Nat.Coprime (Nat.card gY.ker) 5 :=
    Nat.Coprime.of_dvd_left (hK5 ▸ hker_dvd)
      (CFSG.pPrimeCore_coprime_card (p := 5) (G := ↥H)).symm
  haveI hker_normal : gY.ker.Normal := MonoidHom.normal_ker gY
  haveI himage_normal : (gY.ker.map f0).Normal := hker_normal.map f0 hf0
  have himage_cop : Nat.Coprime (Nat.card (gY.ker.map f0)) 5 :=
    Nat.Coprime.of_dvd_left (Subgroup.card_map_dvd gY.ker f0) hker_cop
  haveI : IsSimpleGroup ↥S := hSsimple
  have himage_bot : gY.ker.map f0 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (gY.ker.map f0) with h | h
    · exact h
    · exfalso
      have h5 : 5 ∣ Nat.card (gY.ker.map f0) := by
        rw [h]
        simpa using (show 5 ∣ Nat.card ↥S from by rw [hScard]; norm_num)
      exact (Nat.prime_five.coprime_iff_not_dvd).mp
        (Nat.coprime_comm.mp himage_cop) h5
  intro y hy
  rw [MonoidHom.mem_ker]
  have hy' : f0 y ∈ gY.ker.map f0 := Subgroup.mem_map_of_mem f0 hy
  rw [himage_bot] at hy'
  exact Subgroup.mem_bot.mp hy'

private lemma bar_surjection_of_perfect {H X : Subgroup G} {S : Subgroup (Equiv.Perm (Fin 10))}
    (hXH : X ≤ H) (hXM : X ≤ D.M) (f : ↥X →* ↥S)
    (hSsimple : IsSimpleGroup ↥S)
    (hScard : Nat.card ↥S = 2520) (Y0 : Subgroup ↥X) (hY0 : ⁅Y0, Y0⁆ = Y0)
    (hY0map : Y0.map f = ⊤) :
    ∃ (Ybar : Subgroup (UC22.F07.QuotK7 5 H)) (fbar : ↥Ybar →* ↥S),
      Function.Surjective fbar ∧
      Ybar ≤ ((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)) ∧
      ⁅Ybar, Ybar⁆ = Ybar := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let K5 : Subgroup ↥H := CFSG.pPrimeCore 5 ↥H
  let eY : ↥Y0 →* ↥H := (Subgroup.inclusion hXH).comp Y0.subtype
  let gY : ↥Y0 →* UC22.F07.QuotK7 5 H := (QuotientGroup.mk' K5).comp eY
  have heY : Function.Injective eY :=
    (Subgroup.inclusion_injective hXH).comp Y0.subtype_injective
  let Ybar : Subgroup (UC22.F07.QuotK7 5 H) := gY.range
  let psi : ↥Y0 →* ↥Ybar := gY.codRestrict Ybar (fun y => MonoidHom.mem_range.mpr ⟨y, rfl⟩)
  have hpsi : Function.Surjective psi := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hz
    exact ⟨y, Subtype.ext hy⟩
  let f0 : ↥Y0 →* ↥S := f.comp Y0.subtype
  have hf0 : Function.Surjective f0 := by
    intro s
    have hs : s ∈ Y0.map f := by rw [hY0map]; exact Subgroup.mem_top s
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨y, hy⟩, hyf⟩
  have hker_le : gY.ker ≤ f0.ker :=
    bar_kernel_le K5 eY gY rfl rfl heY hSsimple hScard f0 hf0
  have hpsi_ker : psi.ker ≤ f0.ker := by
    have hker_eq : psi.ker = gY.ker := by
      ext y
      simp [psi, MonoidHom.mem_ker]
    rw [hker_eq]
    exact hker_le
  obtain ⟨fbar, hfbar⟩ : ∃ fbar : ↥Ybar →* ↥S, Function.Surjective fbar :=
    ⟨psi.liftOfRightInverse (Function.surjInv hpsi) (Function.rightInverse_surjInv hpsi)
        ⟨f0, hpsi_ker⟩, by
      intro s
      obtain ⟨y, rfl⟩ := hf0 s
      exact ⟨psi y, MonoidHom.liftOfRightInverse_comp_apply psi (Function.surjInv hpsi)
        (Function.rightInverse_surjInv hpsi) ⟨f0, hpsi_ker⟩ y⟩⟩
  have hYbar_le : Ybar ≤ ((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)) := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_map.mpr ⟨eY y, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ⟨(eY y).2, ?_⟩
    have hyX : ((y : X) : G) ∈ D.M := hXM (y : X).2
    simpa [eY] using hyX
  have hcomm_top : commutator ↥Y0 = ⊤ := by
    apply Subgroup.map_injective (f := Y0.subtype) Y0.subtype_injective
    rw [Subgroup.map_subtype_commutator, hY0, Subgroup.map_top, Subgroup.range_subtype]
  have hYbar_perf : ⁅Ybar, Ybar⁆ = Ybar := by
    rw [← map_commutator_eq (f := gY), hcomm_top, Subgroup.map_top]
  exact ⟨Ybar, fbar, hfbar, hYbar_le, hYbar_perf⟩

private lemma exists_perfect_surjection_of_deg_three (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hdeg : F.deg B = 3) :
    ∃ (S : Subgroup (Equiv.Perm (Fin 10))) (X : Subgroup G),
      IsSimpleGroup ↥S ∧ Group.IsPerfect ↥S ∧ Nat.card ↥S = 2520 ∧
      X ≤ Subgroup.normalizer (B : Set G) ∧ X ≤ D.M ∧
      ∃ f : ↥X →* ↥S, Function.Surjective f := by
  classical
  obtain ⟨s, hs, hs_le⟩ := exists_altOff_le_map_inf F hBA hB3 hdeg
  let K : Subgroup ↥D.M := Subgroup.comap F.phiA (A10Perm.altOff s)
  let CM : Subgroup ↥D.M :=
    Subgroup.centralizer ((B.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)
  let X : Subgroup G := (c.L ⊓ CM.map D.M.subtype) ⊓ K.map D.M.subtype
  have hBM : B ≤ D.M := hBA.trans F.A_le_M
  have hCM : CM.map D.M.subtype = D.M ⊓ Subgroup.centralizer (B : Set G) :=
    CFSG.Walter.map_subtype_centralizer_subgroupOf hBM
  have hCM_le : CM.map D.M.subtype ≤ Subgroup.normalizer (B : Set G) := by
    rw [hCM]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hXM : X ≤ D.M := fun x hx => c.hyp81.1 hx.1.1
  have hXH : X ≤ Subgroup.normalizer (B : Set G) := fun x hx => hCM_le hx.1.2
  have hXphi : ∀ x : X, F.phiA ⟨(x : G), hXM x.2⟩ ∈ A10Perm.altOff s := by
    intro x
    obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp x.2.2
    rw [← (Subtype.ext hyx : y = ⟨(x : G), hXM x.2⟩)]
    exact Subgroup.mem_comap.mp hyK
  let fPerm : ↥X →* Equiv.Perm (Fin 10) :=
    { toFun := fun x => F.phiA ⟨(x : G), hXM x.2⟩
      map_one' := by
        rw [show (⟨((1 : ↥X) : G), hXM (1 : ↥X).2⟩ : ↥D.M) = 1 from Subtype.ext rfl, map_one]
      map_mul' := fun x y => by
        rw [show (⟨(((x * y : ↥X)) : G), hXM (x * y).2⟩ : ↥D.M) =
            ⟨(x : G), hXM x.2⟩ * ⟨(y : G), hXM y.2⟩ from Subtype.ext rfl, map_mul] }
  let f : ↥X →* ↥(A10Perm.altOff s) := fPerm.codRestrict (A10Perm.altOff s) hXphi
  have hf : Function.Surjective f := by
    intro σ
    obtain ⟨y, hy, hyσ⟩ := Subgroup.mem_map.mp (hs_le σ.2)
    have hxL : (y : G) ∈ c.L := Subgroup.mem_subgroupOf.mp hy.1
    have hyCM : (y : G) ∈ CM.map D.M.subtype :=
      Subgroup.mem_map_of_mem D.M.subtype hy.2
    have hxM : (y : G) ∈ D.M := c.hyp81.1 hxL
    have hxK : (y : G) ∈ K.map D.M.subtype :=
      Subgroup.mem_map.mpr ⟨y, Subgroup.mem_comap.mpr (hyσ ▸ σ.2), rfl⟩
    refine ⟨⟨(y : G), ⟨⟨hxL, hyCM⟩, hxK⟩⟩, ?_⟩
    apply Subtype.ext
    have hcoe : (⟨(y : G), hxM⟩ : ↥D.M) = y := Subtype.ext rfl
    simpa [f, fPerm, hcoe] using hyσ
  exact ⟨A10Perm.altOff s, X, isSimpleGroup_altOff_of_card_eq_three s hs,
    isPerfect_altOff_of_card_eq_three s hs, card_altOff_of_card_eq_three s hs,
    hXH, hXM, f, hf⟩

private lemma exists_bar_surjection_of_deg_three (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hdeg : F.deg B = 3) :
    ∃ (S : Subgroup (Equiv.Perm (Fin 10)))
      (Ybar : Subgroup (UC22.F07.QuotK7 5 (Subgroup.normalizer (B : Set G))))
      (fbar : ↥Ybar →* ↥S),
      IsSimpleGroup ↥S ∧ Group.IsPerfect ↥S ∧ Nat.card ↥S = 2520 ∧
      Function.Surjective fbar ∧
      Ybar ≤ ((Subgroup.normalizer (B : Set G) ⊓ D.M).subgroupOf
        (Subgroup.normalizer (B : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥(Subgroup.normalizer (B : Set G)))) ∧
      ⁅Ybar, Ybar⁆ = Ybar := by
  obtain ⟨S, X, hSsimple, hSperf, hScard, hXH, hXM, f, hf⟩ :=
    exists_perfect_surjection_of_deg_three F hBA hB3 hdeg
  haveI : Group.IsPerfect ↥S := hSperf
  obtain ⟨Y0, hY0, hY0map⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.exists_perfect_map_eq_top f hf
  obtain ⟨Ybar, fbar, hfbar, hYbar_le, hYbar_perf⟩ :=
    bar_surjection_of_perfect hXH hXM f hSsimple hScard Y0 hY0 hY0map
  exact ⟨S, Ybar, fbar, hSsimple, hSperf, hScard, hfbar, hYbar_le, hYbar_perf⟩

theorem normalizer_le_of_deg_three (F : A10Frame c) (hKF7 : UC22.KF7Use D) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hdeg : F.deg B = 3) :
    Subgroup.normalizer (B : Set G) ≤ D.M := by
  classical
  let H : Subgroup G := Subgroup.normalizer (B : Set G)
  change H ≤ D.M
  by_contra hHM
  obtain ⟨S, Ybar, fbar, hSsimple, hSperf, hScard, hfbar, hYbar_le, hYbar_perf⟩ :=
    exists_bar_surjection_of_deg_three F hBA hB3 hdeg
  haveI : IsSimpleGroup ↥S := hSsimple
  haveI : Group.IsPerfect ↥S := hSperf
  have hrank : 1 < CFSG.Open.pRank 5 (H ⊓ D.M) := by
    refine lt_of_lt_of_le (one_lt_pRank_five_centralizer_inf F hBA hB3 hdeg) ?_
    exact CFSG.SectionRank.pRank_mono (p := 5) (by norm_num)
      (le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer (B : Set G))) inf_le_right)
  have hsec : UC22.F07.Sec7Hyp D 5 H :=
    ⟨by norm_num, by norm_num,
      c.isStronglyPEmbedded_of_mem_sigma (by rw [F.sig]; simp),
      normalizer_ne_top_of_card_eq_three F hB3, hHM, hrank⟩
  rcases hKF7 5 (by rw [F.sig]; simp) H hsec with hsol | ⟨-, hquot⟩
  · haveI : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H))) := hsol
    haveI : Group.IsSolvable ↥Ybar :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYbar_le)
        (Subgroup.inclusion_injective hYbar_le)
    haveI : Group.IsSolvable ↥S := solvable_of_surjective hfbar
    exact hSperf.not_isSolvable ↥S inferInstance
  · obtain ⟨e⟩ := hquot Ybar hYbar_le hYbar_perf ↥S hSsimple fbar hfbar
    have hcard : Nat.card ↥S = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hScard] at hcard
    norm_num at hcard

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
