module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

theorem card_le_three_of_isPGroup_mulAut {T : Type*} [Group T] [Finite T] (hT : Nat.card T = 9)
    {Q : Subgroup (MulAut T)} (hQ : IsPGroup 3 Q) : Nat.card Q ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card T = 3 ^ 2 := by rw [hT]; norm_num
  by_cases hcyc : IsCyclic T
  · haveI : IsCyclic T := hcyc
    have hdvd : Nat.card Q ∣ 6 := by
      have h : Nat.card Q ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card Q
      rwa [IsCyclic.card_mulAut T, hT, show Nat.totient 9 = 6 by decide] at h
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [hn] at hdvd ⊢
    have hnle : n ≤ 1 := by
      by_contra h
      have hn2 : 2 ≤ n := by omega
      have h9dvd : 9 ∣ 3 ^ n := by
        rw [show 9 = 3 ^ 2 by norm_num]
        exact Nat.pow_dvd_pow 3 hn2
      have h96 : 9 ∣ 6 := h9dvd.trans hdvd
      norm_num at h96
    calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
      _ = 3 := by norm_num
  · haveI : Nontrivial T := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      have h1 : Nat.card T ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      omega
    have hexp : ∀ x : T, x ^ 3 = 1 := by
      have hexp3 : Monoid.exponent T = 3 :=
        (not_isCyclic_iff_exponent_eq_prime Nat.prime_three hcard).mp hcyc
      intro x
      by_cases hx : x = 1
      · simp [hx]
      · have hx3 : orderOf x = 3 :=
          (Monoid.exponent_eq_prime_iff Nat.prime_three).mp hexp3 x hx
        rw [← hx3]
        exact pow_orderOf_eq_one x
    exact CFSG.RankThree.Coprime.card_le_of_isPGroup_mulAut hexp hcard Q hQ

namespace A10Gen

variable {X : Type} [Group X] [Finite X]

private lemma isSylowOf_inf_of_normal {L : Subgroup X} (hLn : L.Normal) (R : Sylow 3 X) :
    CFSG.ABGLocalTools.IsSylowOf 3 ((R : Subgroup X) ⊓ L) L ∧
      (R : Subgroup X) ≤
        Subgroup.normalizer (((R : Subgroup X) ⊓ L : Subgroup X) : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 3 (R : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, R.isPGroup', by simpa using R.not_dvd_index⟩
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((R : Subgroup X) ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hRsyl le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  refine ⟨hTsyl, ?_⟩
  have hTleR : ((R : Subgroup X) ⊓ L) ≤ (R : Subgroup X) := inf_le_left
  have hsub : ((R : Subgroup X) ⊓ L).subgroupOf (R : Subgroup X) =
      L.subgroupOf (R : Subgroup X) := by
    ext x
    simp [Subgroup.mem_inf, and_comm]
  have hN : (((R : Subgroup X) ⊓ L).subgroupOf (R : Subgroup X)).Normal := by
    rw [hsub]
    exact hLn.subgroupOf (R : Subgroup X)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTleR).mp hN

private lemma card_eq_nine_of_isSylowOf {L : Subgroup X} {T : Subgroup X}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L)
    (h9 : 9 ∣ Nat.card L) (h27 : ¬ 27 ∣ Nat.card L) : Nat.card T = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : Nat.card ↥T = 3 ^ (Nat.card ↥L).factorization 3 := hTsyl.card_eq
  have h9' : 3 ^ 2 ∣ Nat.card ↥L := by
    rw [show 3 ^ 2 = 9 by norm_num]
    exact h9
  have hge2 : 2 ≤ (Nat.card ↥L).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos (α := ↥L)).ne').mp h9'
  have hle2 : (Nat.card ↥L).factorization 3 ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ (Nat.card ↥L).factorization 3 := by omega
    apply h27
    have h27' : 3 ^ 3 ∣ Nat.card ↥L :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Nat.card_pos (α := ↥L)).ne').mpr h3
    rwa [show 3 ^ 3 = 27 by norm_num] at h27'
  rw [hfac, le_antisymm hle2 hge2]
  norm_num

private lemma exists_sylow_ne_bot_isMulCommutative {L : Subgroup X} {T : Subgroup X}
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L) (hTcard : Nat.card T = 9) :
    ∃ P : Sylow 3 ↥L, (P : Subgroup ↥L) = T.subgroupOf L ∧
      (P : Subgroup ↥L) ≠ ⊥ ∧ IsMulCommutative (P : Subgroup ↥L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hPcard : Nat.card ↥(P : Subgroup ↥L) = 9 := by
    rw [hP]
    calc Nat.card ↥(T.subgroupOf L) = Nat.card ↥T :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTsyl.le).toEquiv
      _ = 9 := hTcard
  have hPcomm : IsMulCommutative (P : Subgroup ↥L) := by
    refine IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) ?_
    rw [hPcard]
    norm_num
  have hPne : (P : Subgroup ↥L) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(P : Subgroup ↥L) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [hPcard] at h1
    norm_num at h1
  exact ⟨P, hP, hPne, hPcomm⟩

private lemma conjNormal_pow_three_and_commute {L : Subgroup X} (hLn : L.Normal)
    {T : Subgroup X} {P : Sylow 3 ↥L} (hP : (P : Subgroup ↥L) = T.subgroupOf L)
    {R : Sylow 3 X} {r : X} (hrR : r ∈ (R : Subgroup X))
    (hrC : ∀ t ∈ T, r * t = t * r) :
    (∃ n : ℕ, (MulAut.conjNormal (H := L) r) ^ (3 ^ n) = 1) ∧
      ∀ g ∈ (P : Subgroup ↥L), MulAut.conjNormal (H := L) r * MulAut.conj g =
        MulAut.conj g * MulAut.conjNormal (H := L) r := by
  haveI : L.Normal := hLn
  constructor
  · obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hrR⟩
    refine ⟨n, ?_⟩
    have hrpow : r ^ (3 ^ n) = 1 := by simpa using hn
    rw [← map_pow, hrpow, map_one]
  · intro g hg
    have hgT : (g : X) ∈ T := by
      have hg' : g ∈ T.subgroupOf L := by rw [← hP]; exact hg
      exact Subgroup.mem_subgroupOf.mp hg'
    have hrg : r * (g : X) = (g : X) * r := hrC _ hgT
    calc MulAut.conjNormal (H := L) r * MulAut.conj g
        = MulAut.conjNormal (H := L) r * MulAut.conjNormal (H := L) (g : X) := by
          rw [← MulAut.conjNormal_val]
      _ = MulAut.conjNormal (H := L) (r * (g : X)) := by rw [map_mul]
      _ = MulAut.conjNormal (H := L) ((g : X) * r) := by rw [hrg]
      _ = MulAut.conjNormal (H := L) (g : X) * MulAut.conjNormal (H := L) r := by
          rw [map_mul]
      _ = MulAut.conj g * MulAut.conjNormal (H := L) r := by
          rw [← MulAut.conjNormal_val]

private lemma inv_mul_mem_centralizer_of_conjNormal_eq {L : Subgroup X} (hLn : L.Normal)
    {r : X} {g₀ : ↥L}
    (hφg : MulAut.conjNormal (H := L) r = MulAut.conj g₀) :
    (g₀ : X)⁻¹ * r ∈ Subgroup.centralizer (L : Set X) := by
  haveI : L.Normal := hLn
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hφy : MulAut.conjNormal (H := L) r ⟨y, hy⟩ = MulAut.conj g₀ ⟨y, hy⟩ := by
    rw [hφg]
  have hval : r * y * r⁻¹ = (g₀ : X) * y * (g₀ : X)⁻¹ := by
    have := congrArg Subtype.val hφy
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
  calc y * ((g₀ : X)⁻¹ * r) = (g₀ : X)⁻¹ * ((g₀ : X) * y * (g₀ : X)⁻¹) * r := by group
    _ = (g₀ : X)⁻¹ * (r * y * r⁻¹) * r := by rw [hval]
    _ = ((g₀ : X)⁻¹ * r) * y := by group

private lemma mem_of_commute (hIA : RankThreeTheoremC.KFactInnerAction)
    {L : Subgroup X} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup ↥L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥)
    {T : Subgroup X} (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L) (hTcard : Nat.card T = 9)
    {R : Sylow 3 X} {r : X} (hrR : r ∈ (R : Subgroup X))
    (hrC : ∀ t ∈ T, r * t = t * r) : r ∈ T := by
  haveI : L.Normal := hLn
  obtain ⟨P, hP, hPne, hPcomm⟩ :=
    exists_sylow_ne_bot_isMulCommutative hTsyl hTcard
  obtain ⟨hφ, hcomm⟩ := conjNormal_pow_three_and_commute hLn hP hrR hrC
  obtain ⟨g₀, hg₀P, hφg⟩ :=
    hIA 3 Nat.prime_three (by norm_num) ↥L hLs hnab hcat P hPne hPcomm
      (MulAut.conjNormal (H := L) r) hφ hcomm
  have hg₀T : (g₀ : X) ∈ T := by
    have hg' : g₀ ∈ T.subgroupOf L := by rw [← hP]; exact hg₀P
    exact Subgroup.mem_subgroupOf.mp hg'
  have hcen := inv_mul_mem_centralizer_of_conjNormal_eq hLn hφg
  have h1 : (g₀ : X)⁻¹ * r = 1 := by
    rw [hC, Subgroup.mem_bot] at hcen
    exact hcen
  have hr : r = (g₀ : X) := by
    calc r = (g₀ : X) * ((g₀ : X)⁻¹ * r) := by group
      _ = (g₀ : X) := by rw [h1, mul_one]
  rwa [hr]

private def conjAction (R : Sylow 3 X) (T : Subgroup X)
    (hTN : (R : Subgroup X) ≤ Subgroup.normalizer (T : Set X)) : ↥R →* MulAut ↥T :=
  (Subgroup.normalizerMonoidHom T).comp
    (MonoidHom.codRestrict (Subgroup.subtype R) (Subgroup.normalizer (T : Set X))
      (fun r => hTN r.2))

private lemma conjAction_ker (hIA : RankThreeTheoremC.KFactInnerAction)
    {L : Subgroup X} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup ↥L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥)
    {T : Subgroup X} (hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T L)
    (hTcard : Nat.card T = 9) (R : Sylow 3 X)
    (hTN : (R : Subgroup X) ≤ Subgroup.normalizer (T : Set X)) :
    (conjAction R T hTN).ker = T.subgroupOf (R : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTcomm : ∀ a b : ↥T, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hTcard]; norm_num)
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hr
    have hrC : ∀ t ∈ T, (r : X) * t = t * (r : X) := by
      intro t ht
      have h1 : conjAction R T hTN r ⟨t, ht⟩ = ⟨t, ht⟩ := by
        simpa using congrArg (fun e : MulAut ↥T => e ⟨t, ht⟩) hr
      have hcoe : (conjAction R T hTN r ⟨t, ht⟩ : X) = (r : X) * t * (r : X)⁻¹ := rfl
      have h2 : (r : X) * t * (r : X)⁻¹ = t := by
        have := congrArg Subtype.val h1
        simpa [hcoe] using this
      calc (r : X) * t = ((r : X) * t * (r : X)⁻¹) * (r : X) := by group
        _ = t * (r : X) := by rw [h2]
    exact mem_of_commute hIA hLn hLs hnab hcat hC hTsyl hTcard r.2 hrC
  · intro hrT
    ext t
    have hcoe : (conjAction R T hTN r t : X) = (r : X) * (t : X) * (r : X)⁻¹ := rfl
    rw [hcoe, MulAut.one_apply]
    have hc : (r : X) * (t : X) = (t : X) * (r : X) :=
      congrArg Subtype.val (hTcomm ⟨(r : X), hrT⟩ t)
    calc (r : X) * (t : X) * (r : X)⁻¹ =
          (t : X) * ((r : X) * (r : X)⁻¹) := by rw [hc]; group
      _ = (t : X) := by group

private lemma card_le_twentyseven_of_conjAction {T : Subgroup X} (hTcard : Nat.card T = 9)
    (R : Sylow 3 X) (hTN : (R : Subgroup X) ≤ Subgroup.normalizer (T : Set X))
    (hker : Nat.card ↥(conjAction R T hTN).ker = 9) : Nat.card ↥R ≤ 27 := by
  have hrange : IsPGroup 3 (conjAction R T hTN).range := by
    have htop : IsPGroup 3 (⊤ : Subgroup ↥R) := R.isPGroup'.to_subgroup ⊤
    have hmap := IsPGroup.map htop (conjAction R T hTN)
    rwa [Subgroup.map_top] at hmap
  have hle3 : Nat.card ↥(conjAction R T hTN).range ≤ 3 :=
    card_le_three_of_isPGroup_mulAut hTcard hrange
  have h := Subgroup.card_ker_mul_card_range (conjAction R T hTN)
  rw [hker] at h
  calc Nat.card ↥R = 9 * Nat.card ↥(conjAction R T hTN).range := h.symm
    _ ≤ 9 * 3 := Nat.mul_le_mul_left 9 hle3
    _ = 27 := by norm_num

private lemma not_eightyone_dvd_card_of_card_le {R : Sylow 3 X}
    (hRle : Nat.card ↥R ≤ 27) : ¬ 81 ∣ Nat.card X := by
  intro h81
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRcard : Nat.card ↥R = 3 ^ (Nat.card X).factorization 3 :=
    Sylow.card_eq_multiplicity R
  have h81' : 3 ^ 4 ∣ Nat.card X := by
    rw [show 3 ^ 4 = 81 by norm_num]
    exact h81
  have h4 : 4 ≤ (Nat.card X).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.card_pos (α := X)).ne').mp h81'
  have hdvd : 3 ^ 4 ∣ Nat.card ↥R := by
    rw [hRcard]
    exact Nat.pow_dvd_pow 3 h4
  have h81R : 81 ≤ Nat.card ↥R := by
    have hle := Nat.le_of_dvd (Nat.card_pos (α := ↥R)) hdvd
    rwa [show 3 ^ 4 = 81 by norm_num] at hle
  omega

theorem not_eightyone_dvd_card_of_innerAction (hIA : RankThreeTheoremC.KFactInnerAction)
    {L : Subgroup X} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup ↥L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (h9 : 9 ∣ Nat.card L) (h27 : ¬ 27 ∣ Nat.card L) :
    ¬ 81 ∣ Nat.card X := by
  classical
  intro h81
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : L.Normal := hLn
  obtain ⟨R⟩ := Sylow.nonempty (p := 3) (G := X)
  obtain ⟨hTsyl, hTN⟩ := isSylowOf_inf_of_normal hLn R
  set T : Subgroup X := (R : Subgroup X) ⊓ L with hTdef
  have hTsyl' : CFSG.ABGLocalTools.IsSylowOf 3 T L := by
    rw [hTdef]
    exact hTsyl
  have hTN' : (R : Subgroup X) ≤ Subgroup.normalizer (T : Set X) := by
    rw [hTdef]
    exact hTN
  have hTcard : Nat.card T = 9 := by
    rw [hTdef]
    exact card_eq_nine_of_isSylowOf hTsyl h9 h27
  have hTleR : T ≤ (R : Subgroup X) := by
    rw [hTdef]
    exact inf_le_left
  have hfker : (conjAction R T hTN').ker = T.subgroupOf (R : Subgroup X) :=
    conjAction_ker hIA hLn hLs hnab hcat hC hTsyl' hTcard R hTN'
  have hkercard : Nat.card ↥(conjAction R T hTN').ker = 9 := by
    rw [hfker]
    calc Nat.card ↥(T.subgroupOf (R : Subgroup X)) = Nat.card ↥T :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleR).toEquiv
      _ = 9 := hTcard
  exact not_eightyone_dvd_card_of_card_le
    (card_le_twentyseven_of_conjAction hTcard R hTN' hkercard) h81

end A10Gen

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
