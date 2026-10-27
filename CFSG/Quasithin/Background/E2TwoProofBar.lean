module

public import CFSG.Quasithin.Background.E2TwoProofComp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.E2TwoProofFactor

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

structure Setting (H T M : Subgroup Γ) (L : Subgroup (E2.StarQuot M H)) (K : Subgroup Γ) :
    Prop where
  minPar : MinParabolic H T M
  sqtk : SQTKGroup ↥H
  ns : ¬ Group.IsSolvable ↥H
  factor : Factor (E2.star M H T) (E2.star M H M) L
  cComp : K ∈ cComp H
  le : K ≤ H
  star_eq : E2.star M H K = L

theorem exists_setting (h : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hns : ¬ Group.IsSolvable ↥H) : ∃ L K, Setting H T M L K := by
  have : Finite (E2.StarQuot M H) := finite_starQuot M H
  obtain ⟨L, hF⟩ := exists_factor (minParabolic_star h) (kerIn_star M H)
    (not_isSolvable_star h hns)
  obtain ⟨K, hK, hKH, hKL⟩ := exists_cComp_star h hF.mem_cComp
  exact ⟨L, K, ⟨h, hsq, hns, hF, hK, hKH, hKL⟩⟩

noncomputable abbrev barMap (H : Subgroup Γ) : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥H)

@[expose] noncomputable def kbar (H K : Subgroup Γ) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  (K.subgroupOf H).map (barMap H)

@[expose] noncomputable def jbar (M H : Subgroup Γ) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  ((kerIn M H).subgroupOf H).map (barMap H)

theorem sqtkHypCat_bar (hsq : SQTKGroup ↥H) : SQTKHypCat (↥H ⧸ CFSG.pCore 2 ↥H) :=
  have h := SQTKHyp.of_sqtkGroup ↥H hsq
  have := h.finite
  { finite := h.finite
    sqt := CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.sqt
    kgroup := h.kgroup
    o2 := h.o2 }

theorem pCore_eq (X : Type) [Group X] : CFSG.pCore 2 X = CFSG.Open.pCore 2 X :=
  CFSG.pCore_eq_open X 2

theorem isSolvable_ker_barMap (H : Subgroup Γ) : Group.IsSolvable (barMap H).ker := by
  rw [QuotientGroup.ker_mk']
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥H) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have := hp.isNilpotent
  infer_instance

theorem eq_bot_of_isPGroup_two_of_dvd {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup 2 P) (hPQ : P ≤ Q) (hQ : ¬ 2 ∣ Nat.card Q) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card Q := Subgroup.card_dvd_of_le hPQ
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq P hn
  · exfalso
    apply hQ
    rw [hn, pow_succ] at hdvd
    exact (Dvd.intro_left _ rfl).trans hdvd

theorem not_isPGroup_two_of_isQuasisimple {G : Type*} [Group G] [Finite G]
    (hG : CFSG.IsQuasisimple G) : ¬ IsPGroup 2 G := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil := hp.isNilpotent
  obtain ⟨hperf, hs, -⟩ := hG
  have hnt : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (G ⧸ Subgroup.center G) := Quotient.instSubsingletonQuotient _
    exact hs.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hab => hab
      (Subsingleton.elim a b)
  exact Group.IsPerfect.not_isNilpotent G hnil

omit [Finite Γ] in
theorem open_pCore_bar (H : Subgroup Γ) : CFSG.Open.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ := by
  exact pCore_two_quotient_pCore_two ↥H

namespace Setting

variable {L : Subgroup (E2.StarQuot M H)} {K : Subgroup Γ} (S : Setting H T M L K)
include S

theorem sup_eq : H = K ⊔ T := by
  have := finite_starQuot M H
  exact sup_eq_of_star S.minPar S.le (by rw [S.star_eq]; exact S.factor.sup_eq_top)

theorem pCore_le_ker : CFSG.pCore 2 ↥H ≤ (starMap M H).ker := by
  have h1 := S.minPar.subgroupOf.pCore_le_kerIn
  rw [kerIn_subgroupOf_top, ← ker_starMap] at h1
  exact h1

noncomputable def psi : ↥H ⧸ CFSG.pCore 2 ↥H →* E2.StarQuot M H :=
  QuotientGroup.lift (CFSG.pCore 2 ↥H) (starMap M H) S.pCore_le_ker

theorem psi_barMap (x : ↥H) : S.psi (barMap H x) = starMap M H x :=
  QuotientGroup.lift_mk _ _ _

theorem pCore_le_M : (barMap H).ker ≤ M.subgroupOf H := by
  rw [QuotientGroup.ker_mk']
  exact S.pCore_le_ker.trans (ker_starMap_le_subgroupOf M H)

theorem minPar_bar :
    MinParabolic (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ((T.subgroupOf H).map (barMap H))
      ((M.subgroupOf H).map (barMap H)) :=
  S.minPar.subgroupOf.map_of_surjective (QuotientGroup.mk'_surjective _) S.pCore_le_M

theorem kerIn_bar : kerIn ((M.subgroupOf H).map (barMap H)) ⊤ = jbar M H := by
  rw [kerIn_map_top (QuotientGroup.mk'_surjective _) S.pCore_le_M, kerIn_subgroupOf_top]
  rfl

theorem card_jbar_odd : ¬ 2 ∣ Nat.card (jbar M H) := by
  have := S.minPar_bar.card_kerIn_odd (open_pCore_bar H)
  rwa [S.kerIn_bar] at this

theorem ker_psi : S.psi.ker = jbar M H := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) y
  constructor
  · intro hy
    rw [MonoidHom.mem_ker, S.psi_barMap] at hy
    exact ⟨x, by rw [← ker_starMap]; exact hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    rw [MonoidHom.mem_ker]
    have : barMap H z = barMap H x := hzx
    rw [← this, S.psi_barMap, ← MonoidHom.mem_ker, ker_starMap]
    exact hz

theorem kbar_mem_cComp :
    kbar H K ∈ CFSG.Quasithin.cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  map_mem_cComp_top (barMap H) (QuotientGroup.mk'_surjective _) (isSolvable_ker_barMap H)
    (subgroupOf_mem_cComp S.cComp)

theorem map_psi_kbar' : (kbar H K).map S.psi = E2.star M H K := by
  rw [kbar, Subgroup.map_map, star_def]
  congr 1

theorem map_psi_kbar : (kbar H K).map S.psi = L :=
  S.map_psi_kbar'.trans S.star_eq

theorem odd_card_solvableRadical_kbar :
    ¬ 2 ∣ Nat.card (CFSG.solvableRadical ↥(kbar H K)) := by
  set Kb := kbar H K
  set R := CFSG.solvableRadical ↥Kb
  have hmapsto : ∀ k : ↥Kb, S.psi k ∈ L := fun k => by
    have h1 : S.psi k ∈ Kb.map S.psi := ⟨k, k.2, rfl⟩
    rwa [S.map_psi_kbar] at h1
  let f : ↥Kb →* ↥L := (S.psi.comp Kb.subtype).codRestrict L hmapsto
  have hfs : Function.Surjective f := by
    intro l
    have hl : (l : E2.StarQuot M H) ∈ Kb.map S.psi := by
      have h1 : Kb.map S.psi = L := S.map_psi_kbar
      exact h1.ge l.2
    obtain ⟨k, hk, hkl⟩ := hl
    exact ⟨⟨k, hk⟩, Subtype.ext hkl⟩
  have hRn : R.Normal := by
    unfold R CFSG.solvableRadical
    exact Subgroup.sSup_normal _ fun N hN => hN.1
  have hRs : Group.IsSolvable R := A3.solvableRadical_isSolvable
  have hRf : R.map f = ⊥ := by
    have hL := S.factor.simple
    have hnorm : (R.map f).Normal := hRn.map f hfs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map f) with h | h
    · exact h
    · exfalso
      have hsolv : Group.IsSolvable (R.map f) := by
        have := hRs
        exact Group.isSolvable_of_surjective (f.subgroupMap_surjective R)
      rw [h] at hsolv
      have e : ↥(⊤ : Subgroup ↥L) ≃* ↥L := Subgroup.topEquiv
      have : Group.IsSolvable ↥L := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
      exact S.factor.nonab
        (IsMulCommutative.of_comm ((IsSimpleGroup.comm_iff_isSolvable).mpr this))
  have hRJ : R.map Kb.subtype ≤ jbar M H := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← S.ker_psi, MonoidHom.mem_ker]
    have : f r = 1 := by
      have : f r ∈ R.map f := ⟨r, hr, rfl⟩
      rwa [hRf, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcard : Nat.card (R.map Kb.subtype) = Nat.card R :=
    Subgroup.card_map_of_injective Kb.subtype_injective
  intro h2
  apply S.card_jbar_odd
  rw [← hcard] at h2
  exact h2.trans (Subgroup.card_dvd_of_le hRJ)

theorem kbar_facts (h36 : A36CoreForSQTKCat) :
    CFSG.IsQuasisimple ↥(kbar H K) ∧
      Subgroup.center ↥(kbar H K) = CFSG.solvableRadical ↥(kbar H K) := by
  obtain ⟨-, hcom, -⟩ := h36 _ (sqtkHypCat_bar S.sqtk) _ S.kbar_mem_cComp
  obtain ⟨-, -, hcase, -, hq⟩ := hcom
  have hodd := S.odd_card_solvableRadical_kbar
  rcases hcase with ⟨-, hidx⟩ | ⟨hFZ, hFR, -⟩
  · exfalso
    apply hodd
    have h2 := Subgroup.relIndex_dvd_card (CFSG.fittingSubgroup ↥(kbar H K))
      (CFSG.solvableRadical ↥(kbar H K))
    rw [hidx] at h2
    exact h2
  · have hZR : Subgroup.center ↥(kbar H K) = CFSG.solvableRadical ↥(kbar H K) := by
      rw [← hFZ, hFR]
    refine ⟨?_, hZR⟩
    have hcomm : ⁅CFSG.solvableRadical ↥(kbar H K), CFSG.solvableRadical ↥(kbar H K)⁆ = ⊥ := by
      rw [← hZR, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w _
      exact (Subgroup.mem_center_iff.mp hz w)
    have e := (QuotientGroup.quotientMulEquivOfEq hcomm).trans (QuotientGroup.quotientBot)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

theorem kbar_isQuasisimple (h36 : A36CoreForSQTKCat) : CFSG.IsQuasisimple ↥(kbar H K) :=
  (S.kbar_facts h36).1

theorem odd_card_center_kbar (h36 : A36CoreForSQTKCat) :
    ¬ 2 ∣ Nat.card (Subgroup.center ↥(kbar H K)) := by
  rw [(S.kbar_facts h36).2]
  exact S.odd_card_solvableRadical_kbar

theorem isQuasisimple_quotient_pCore (h36 : A36CoreForSQTKCat) :
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := S.kbar_isQuasisimple h36
  have hmem : ∀ k : ↥K, barMap H (Subgroup.inclusion S.le k) ∈ kbar H K := fun k =>
    ⟨Subgroup.inclusion S.le k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  let f : ↥K →* ↥(kbar H K) := ((barMap H).comp (Subgroup.inclusion S.le)).codRestrict _ hmem
  have hfs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : CFSG.Open.pCore 2 ↥K = f.ker := by
    apply le_antisymm
    · set P := CFSG.Open.pCore 2 ↥K
      have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
      have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup 2
      have hPf : (P.map f).Normal := hPn.map f hfs
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPf with htop | hcen
      · exfalso
        apply not_isPGroup_two_of_isQuasisimple hq
        have h2 : IsPGroup 2 (P.map f) := hP2.map f
        rw [htop] at h2
        exact h2.of_equiv Subgroup.topEquiv
      · have hbot := eq_bot_of_isPGroup_two_of_dvd (hP2.map f) hcen (S.odd_card_center_kbar h36)
        rw [Subgroup.map_eq_bot_iff] at hbot
        exact hbot
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker f) ?_
      intro k
      have hk : f k = 1 := k.2
      have hk' : Subgroup.inclusion S.le (k : ↥K) ∈ CFSG.pCore 2 ↥H := by
        have h1 : barMap H (Subgroup.inclusion S.le (k : ↥K)) = 1 := congrArg Subtype.val hk
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hp2 : IsPGroup 2 (CFSG.pCore 2 ↥H) := by
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      obtain ⟨n, hn⟩ := hp2 ⟨_, hk'⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : Γ)) hn
      simpa using this
  have e : ↥K ⧸ CFSG.Open.pCore 2 ↥K ≃* ↥(kbar H K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  exact A3.isQuasisimple_iff_open.mp (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq)

end Setting

end E2P

end CFSG.Quasithin
