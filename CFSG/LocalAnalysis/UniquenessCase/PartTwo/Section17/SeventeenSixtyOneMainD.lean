module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneNonMainB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5QuotBasic
public import CFSG.GroupTheory.PElementSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem seven_not_dvd_pow_two_m (m : ℕ) : ¬ 7 ∣ 2 ^ m :=
  fun hd => absurd (Nat.prime_seven.dvd_of_dvd_pow hd) (by norm_num)


open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan in
theorem exists_sylow_seven_main
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    {K X : Subgroup G} (hKcalM : K ∈ calC D.M) (hKne : K ≠ L)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) (hmain : Opp 7 D.M = L ⊔ K)
    (hXK : X ≤ K) (hXcard : Nat.card X = 7) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 7 R D.M ∧ R ≤ D.M ∧ Nat.card R = 49 ∧
      X ≤ R ∧ Nat.card (R ⊓ L : Subgroup G) = 7 ∧ X ≠ R ⊓ L ∧ R = X ⊔ (R ⊓ L) := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hcentL : Subgroup.center (Bar2 L) = ⊥ := by
    have : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) ctx.shapeL
    exact center_eq_bot_of_isSimpleGroup_of_not_prime_card (by
      rw [card_bar_of_isL3 ctx.shapeL]; norm_num)
  have hcentK : Subgroup.center (Bar2 K) = ⊥ := by
    have : IsSimpleGroup (Bar2 K) := isSimpleGroup_bar_of_isL2_or_isSz hshape
    refine center_eq_bot_of_isSimpleGroup_of_not_prime_card ?_
    rcases hshape with h | h
    · rw [card_of_isL2 h]; norm_num
    · rw [show Nat.card (Bar2 K) = CFSG.Open.ordSuzuki 8 from
        CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]; norm_num
  have h7L : (Nat.card L).factorization 7 = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥(CFSG.pCore 2 ↥L) = 2 ^ m :=
      IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    have hzero : (2 ^ m).factorization 7 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (seven_not_dvd_pow_two_m m)
    have hnum : (2 ^ 6 * 3 ^ 2 * 5 * 7 : ℕ).factorization 7 = 1 := by decide +kernel
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), hm,
      card_bar_of_isL3 ctx.shapeL, Nat.factorization_mul (by positivity) (by positivity),
      Finsupp.add_apply, hzero, add_zero, hnum]
  have h7K : (Nat.card K).factorization 7 = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥(CFSG.pCore 2 ↥K) = 2 ^ m :=
      IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
    have hzero : (2 ^ m).factorization 7 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (seven_not_dvd_pow_two_m m)
    have hbar : Nat.card (Bar2 K) = 504 ∨ Nat.card (Bar2 K) = 29120 := by
      rcases hshape with h | h
      · exact Or.inl (by rw [card_of_isL2 h]; norm_num)
      · exact Or.inr (by
          rw [CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]; norm_num)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hm]
    rcases hbar with hb | hb <;>
      rw [hb, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply, hzero,
        add_zero] <;>
      decide +kernel
  have h7inf : (Nat.card (L ⊓ K : Subgroup G)).factorization 7 = 0 := by
    have hinfle : L ⊓ K ≤ CFSG.Open.pCoreOf 2 L :=
      (calC_inf_le_pCore_of_ne ctx.memC hKcalM hKne.symm hcentL hcentK).trans inf_le_left
    obtain ⟨m, hm⟩ := ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hinfle).exists_card_eq
    rw [hm]
    exact Nat.factorization_eq_zero_of_not_dvd (seven_not_dvd_pow_two_m m)
  have h7sup : (Nat.card (L ⊔ K : Subgroup G)).factorization 7 = 2 := by
    have hfac := congrArg (fun t : ℕ => t.factorization 7)
      (card_sup_mul_card_inf_of_le_normalizer (A := L) (C := K)
        (calC_le_normalizer_of_ne ctx.memC hKcalM hKne.symm))
    rw [show K ⊔ L = L ⊔ K by rw [sup_comm], Nat.factorization_mul (Nat.card_pos.ne')
      (Nat.card_pos.ne'), Finsupp.add_apply, Nat.factorization_mul (Nat.card_pos.ne')
      (Nat.card_pos.ne'), Finsupp.add_apply, h7L, h7K, h7inf] at hfac
    omega
  have hX7 : IsPGroup 7 X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  obtain ⟨R, hRsyl, hXR⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge (K := D.M) (hXK.trans hKM) hX7
  have hRM : R ≤ D.M := hRsyl.le
  have hRK : R ≤ L ⊔ K := by
    rw [← hmain]
    exact le_pElementSubgroup_of_isPGroup Nat.prime_seven hRsyl.isPGroup hRM
  have hRsylK : CFSG.ABGLocalTools.IsSylowOf 7 R (L ⊔ K) :=
    hRsyl.of_le hRK (sup_le hLM hKM)
  have hR49 : Nat.card R = 49 := by
    rw [hRsylK.card_eq, h7sup]; norm_num
  have hLnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (ctx.hyp54.2 L ctx.memC).1
  have hRsylL : CFSG.ABGLocalTools.IsSylowOf 7 (R ⊓ L) L :=
    hRsyl.inf_of_le_normalizer hLM hLnorm
  have hZLcard : Nat.card (R ⊓ L : Subgroup G) = 7 :=
    card_sylow_seven_eq_seven hRsylL
      (by rw [card_bar_of_isL3 ctx.shapeL]; norm_num)
      (by rw [card_bar_of_isL3 ctx.shapeL]; norm_num)
  have hXne : X ≠ R ⊓ L := by
    intro heq
    have hXleLK : X ≤ L ⊓ K := le_inf (by rw [heq]; exact inf_le_right) hXK
    have hinfle := calC_inf_le_pCore_of_ne ctx.memC hKcalM hKne.symm hcentL hcentK
    have hXleO : X ≤ CFSG.Open.pCoreOf 2 L := (hXleLK.trans hinfle).trans inf_le_left
    have hdvd : 7 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
      rw [← hXcard]; exact Subgroup.card_dvd_of_le hXleO
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
    rw [hm] at hdvd
    exact absurd (Nat.prime_seven.dvd_of_dvd_pow hdvd) (by norm_num)
  have hRcomm : ∀ a b : ↥R, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7)
      (by rw [hR49]; norm_num)).is_comm.comm
  have hXnormZ : X ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx z hz
    have hcomm : x * z = z * x :=
      congrArg Subtype.val (hRcomm ⟨x, hXR hx⟩ ⟨z, hz.1⟩)
    rw [show x * z * x⁻¹ = z by rw [hcomm]; group]
    exact hz
  have hcard1 : Nat.card ((R ⊓ L) ⊓ X : Subgroup G) = 1 := by
    have hdvd : Nat.card ((R ⊓ L) ⊓ X : Subgroup G) ∣ 7 := by
      rw [← hXcard]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
    · exact h1
    · exfalso
      have hEq : (R ⊓ L) ⊓ X = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      exact hXne (Subgroup.eq_of_le_of_card_ge (by rw [← hEq]; exact inf_le_left) (by omega))
  have hcard_sup : Nat.card (X ⊔ (R ⊓ L) : Subgroup G) = 49 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := R ⊓ L) (C := X) hXnormZ
    rw [hXcard, hZLcard, hcard1, mul_one] at h
    omega
  refine ⟨R, hRsyl, hRM, hR49, hXR, hZLcard, hXne, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hXR inf_le_left) (by omega)).symm

omit [Finite G] in
theorem map_conj_inf_eq_of_mem {M R L : Subgroup G} (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) {m : G} (hmM : m ∈ M)
    (hmR : m ∈ normalizer (R : Set G)) :
    (R ⊓ L).map (MulAut.conj m).toMonoidHom = R ⊓ L := by
  have : (L.subgroupOf M).Normal := hLn
  have hmL : m ∈ normalizer (L : Set G) :=
    (Subgroup.le_normalizer_of_normal_subgroupOf hLM) hmM
  have hRm : R.map (MulAut.conj m).toMonoidHom = R := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp hmR
  have hLm : L.map (MulAut.conj m).toMonoidHom = L := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp hmL
  calc (R ⊓ L).map (MulAut.conj m).toMonoidHom
      = R.map (MulAut.conj m).toMonoidHom ⊓ L.map (MulAut.conj m).toMonoidHom :=
        Subgroup.map_inf_eq R L ((MulAut.conj m).toMonoidHom) (MulAut.conj m).injective
    _ = R ⊓ L := by rw [hRm, hLm]

theorem mem_M_of_map_conj_eq (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (h59 : R17_59At D V₀ V) (h63 : UC6.R6_3 D)
    {K X Z : Subgroup G} {h : G}
    (hKcalM : K ∈ calC D.M) (hKne : K ≠ L) (hXK : X ≤ K) (hXcard : Nat.card X = 7)
    (hXZ : X.map (MulAut.conj h).toMonoidHom = Z)
    (hCZ : Subgroup.centralizer (Z : Set G) ≤ D.M) : h ∈ D.M := by
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hXM : X ≤ D.M := hXK.trans hKM
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  have hYeq : X = Z.map (MulAut.conj h⁻¹).toMonoidHom := by
    rw [← hXZ, Subgroup.map_map, hcomp, Subgroup.map_id]
  by_contra hh
  have hnot : ¬ barImage D.M X ≤
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) :=
    barImage_not_le_centralizer_of_conj (D := D) (V₀ := V₀) (V := V) (p := p) (L := L)
      ctx h59 h63 (X := Z) (Y := X) (g := h⁻¹) (r := 7) Nat.prime_seven (by norm_num)
      hXcard hXM hYeq (by simpa using hh) hCZ
  apply hnot
  refine (nonMain_barImage_mono hXK).trans ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact uc22p22l_barImage_commute ctx.memC hKcalM hKne.symm b hb a ha
theorem surjective_bar2_inf_centralizer (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K Z : Subgroup G} (hKcalM : K ∈ calC D.M) (hKne : K ≠ L)
    (hZL : Z ≤ L) (hZcard : Nat.card Z = 7) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp
      (Subgroup.inclusion (inf_le_left : K ⊓ centralizer (Z : Set G) ≤ K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcommZ : ∀ z ∈ Z, CentralizesBar z K := by
    intro z hz
    refine ⟨(calC_le_normalizer_of_ne hKcalM ctx.memC hKne) (hZL hz), fun k hk => ?_⟩
    exact (calC_commutator_le_of_ne ctx.memC hKcalM hKne.symm
      (Subgroup.commutator_mem_commutator (hZL hz) hk)).2
  have hsup : (K ⊓ Subgroup.centralizer (Z : Set G)) ⊔ CFSG.Open.pCoreOf 2 K = K :=
    uc22p21d_sup_pCore_eq (L := K) (A := Z) (r := 7) Nat.prime_seven (by norm_num)
      hZcard hcommZ
  intro y
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
  have hleN : K ⊓ Subgroup.centralizer (Z : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right
    (K ⊓ Subgroup.centralizer (Z : Set G)) (CFSG.Open.pCoreOf 2 K) hleN
  rw [hsup] at hset
  have hmem : (k : G) ∈ (↑(K ⊓ Subgroup.centralizer (Z : Set G)) : Set G) *
      (↑(CFSG.Open.pCoreOf 2 K) : Set G) := by
    rw [← hset]; exact k.2
  obtain ⟨a, ha, n, hn, han⟩ := hmem
  have hn' : n ∈ (CFSG.pCore 2 ↥K).map K.subtype := hn
  obtain ⟨n', hn'mem, hval⟩ := Subgroup.mem_map.mp hn'
  let a' : ↥K := ⟨a, ha.1⟩
  have hmul : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) k =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) a' := by
    have hk_eq : k = a' * n' := by
      ext
      change (k : G) = a * (n' : G)
      rw [show (n' : G) = n from hval]
      exact han.symm
    rw [hk_eq, map_mul]
    have hn1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) n' = 1 :=
      (QuotientGroup.eq_one_iff n').mpr hn'mem
    rw [hn1, mul_one]
  refine ⟨⟨a, ha⟩, ?_⟩
  change (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨a, ha.1⟩ = y
  rw [← hmul, hk]
theorem pRank_normalizer_barImage_le (D : Data G) {Z : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZM : Z ≤ D.M) (hZ7 : IsPGroup 7 Z) :
    CFSG.Open.pRank p (normalizer (barImage D.M Z : Set (Bar2 D.M))) ≤
      CFSG.Open.pRank p (normalizer (Z : Set G) ⊓ D.M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have h7N : ¬ 7 ∣ Nat.card (CFSG.pCore 2 ↥D.M) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    rw [hm]; exact seven_not_dvd_pow_two_m m
  have hA : IsPGroup 7 (Z.subgroupOf D.M) := hZ7.comap_subtype (K := D.M)
  have hle : Subgroup.normalizer (barImage D.M Z : Set (Bar2 D.M)) ≤
      (Subgroup.normalizer (Z.subgroupOf D.M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    simpa only [barImage] using
      normalizer_map_mk'_le_of_coprime (p := 7) (B := ↥D.M) (N := CFSG.pCore 2 ↥D.M)
        (A := Z.subgroupOf D.M) hA h7N
  have hEq : (Subgroup.normalizer (Z.subgroupOf D.M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
      barImage D.M (Subgroup.normalizer (Z : Set G) ⊓ D.M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hZM]
    rw [← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (Z : Set G)) D.M]
    rfl
  calc CFSG.Open.pRank p (normalizer (barImage D.M Z : Set (Bar2 D.M)))
      ≤ CFSG.Open.pRank p ((Subgroup.normalizer (Z.subgroupOf D.M)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))) :=
        CFSG.SectionRank.pRank_mono hp.one_lt hle
    _ = CFSG.Open.pRank p (barImage D.M (Subgroup.normalizer (Z : Set G) ⊓ D.M)) := by
        rw [hEq]
    _ = CFSG.Open.pRank p (Subgroup.normalizer (Z : Set G) ⊓ D.M) :=
        s13_pRank_barImage hp hp2 inf_le_right
end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
