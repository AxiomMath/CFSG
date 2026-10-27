module

public import CFSG.Quasithin.EmptyFaithful.S1421QA19U
public import CFSG.Quasithin.EmptyFaithful.S1421QA19J4A
public import CFSG.Quasithin.EmptyFaithful.S1421Q9F
public import CFSG.Quasithin.EmptyFaithful.S1421QEx
public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace QA19

theorem eq_bot_of_perfect_of_isPGroup {X : Type*} [Group X] {R : Subgroup X}
    (hR : ⁅R, R⁆ = R) (hp : IsPGroup 2 R) [Finite R] : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  have : Group.IsNilpotent ↥R := hp.isNilpotent
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥R
  apply hlt.ne
  apply Subgroup.map_injective R.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hR]

theorem not_eleven_dvd_card_exactType {Y : Type} [Group Y]
    (h : IsPSL 3 2 2 Y ∨ IsSL3 (2 ^ 2) Y ∨ IsPSp4 2 2 Y) : ¬ 11 ∣ Nat.card Y := by
  rcases h with h | ⟨K, _, _, hK, ⟨e⟩⟩ | h
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    rw [this]
    decide
  · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hK]
    decide
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
    rw [this]
    decide

end QA19

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.exists_involution_gen (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hex : A318Exclusion (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ (z : G) (hz : z ∈ L), quasithinOmegaOneCenter T = Subgroup.zpowers z ∧
      H ≤ Subgroup.centralizer ({z} : Set G) ∧ orderOf (zbar L z hz) = 2 ∧
      ∃ P : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), IsSylowTwoOf P ⊤ ∧
        P ≤ Subgroup.centralizer ({zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 := c.eq_oPrimeResidualOf hF h36 h38 hq (MulEquiv.refl _) hex
  obtain ⟨z, hzZ, hz1, hz2, hzT, hZgen⟩ := exists_generator c.st
  have hzL : z ∈ L := c.omegaOneCenter_le_of_eq hL3 hzZ
  have hHz : H ≤ Subgroup.centralizer ({z} : Set G) :=
    (Q9.H_le_mcOf c.st).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ))
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hzz : (⟨z, hzL⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  have hne : π ⟨z, hzL⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨z, hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have hcen := normal_isPGroup_le_center_of_isQuasisimple hq _
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) hmem
    apply c.not_le_mc
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hZgen] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : Commute z l := by
      have := Subgroup.mem_center_iff.mp hcen ⟨l, hl⟩
      exact congrArg Subtype.val this.symm
    exact ((hcomm.zpow_left k).eq)
  have hord : orderOf (π ⟨z, hzL⟩) = 2 := by
    apply orderOf_eq_prime _ hne
    rw [← map_pow, hzz, map_one]
  refine ⟨z, hzL, hZgen, hHz, hord, ?_⟩
  have hSyl : IsSylowTwoOf (sOf T K1) (g0Of T M H K1) := isSylowTwoOf_g0 c.inM c.sylow
  have hSL : IsSylowTwoOf (sOf T K1 ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hSyl c.le_g0Of c.g0Of_le_normalizer
  have hP := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSL) π
    (QuotientGroup.mk'_surjective _)
  refine ⟨_, hP, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hxS : (x : G) ∈ sOf T K1 ⊓ L := Subgroup.mem_subgroupOf.mp hx
  have hxT : (x : G) ∈ T := hxS.1.1
  exact hzT _ hxT

end S1421

namespace QA19

abbrev centQuot {G : Type} [Group G] (L : Subgroup G) (z : G) (hz : z ∈ L) : Type :=
  ↥(Subgroup.centralizer ({S1421.zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L))) ⧸
    CFSG.pCore 2 ↥(Subgroup.centralizer ({S1421.zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L)))

open CFSG.Quasithin.H13.J4 in
theorem core3J4ShapeThree_of_inputs
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hd : Core3SmallData) (h128Four : Lemma128Four)
    (hL34 : Q9.L34Maximal) : Core3J4ShapeThree := by
  intro G _ _ T M H K1 L M₁ c hq hJ4 hKL hKc hK1lt hL hPSL
  have hsm : Core3IsSmall (↥L ⧸ CFSG.pCore 2 ↥L) := Or.inr ⟨.J4, Or.inr (Or.inl rfl), hJ4⟩
  obtain ⟨hex, -⟩ := hd _ hsm
  obtain ⟨z, hz, hZgen, hHz, hord, P, hP, hPle⟩ := c.exists_involution_gen hF h36 h38 hq hex
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    c.st.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hBl : oTwoUpper H ∈ lFamily T := by
    show oTwoUpper H ∈ cComp (oTwoUpper H ⊔ T)
    rw [S1421.sup_oTwoUpper_eq c.st]
    exact hKc
  have hmax : quasithinIsMaximalLocal T (oTwoUpper H) :=
    Q9.isMaximalLocal_oTwoUpper h128Four hL34 c.st hKc hL
  obtain ⟨Kc, hKc', hKKc⟩ :=
    Q9.exists_cComp_mcOf h37 h39 c.st hBl (hKH.trans (Q9.H_le_mcOf c.st))
  have hKcK : Kc = oTwoUpper H := hmax.2 Kc (Q9.isLocal_of_cComp_mcOf c.st hKc') hKKc
  have hKM : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    have hnorm := lemma_1_2_4_normal c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian h37 h38
      (Q9.pCoreOf_mcOf_ne_bot c.st) (Q9.isSylowTwoOf_mcOf c.st) hBl hKKc hKc' hTN
    rw [hKcK] at hnorm
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hKH.trans (Q9.H_le_mcOf c.st))).mp hnorm
  obtain ⟨e⟩ := hJ4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ P.index := by
    have h := hP.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at h
  have hP2 : IsPGroup 2 P := hP.2.1
  let S : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) := hP2.toSylow hodd
  have hSP : (S : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = P := IsPGroup.toSylow_coe hP2 hodd
  have hzb : S1421.zbar L z hz ∈ P := by
    have hz2 : IsPGroup 2 (Subgroup.zpowers (S1421.zbar L z hz)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hle : (S : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ≤
        Subgroup.normalizer ((Subgroup.zpowers (S1421.zbar L z hz) : Subgroup _) : Set _) := by
      intro s hs
      rw [hSP] at hs
      have h1 : s ∈ Subgroup.centralizer ((Subgroup.zpowers (S1421.zbar L z hz) :
          Subgroup _) : Set _) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact hPle hs
      exact Subgroup.centralizer_le_normalizer _ h1
    have hmax := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' hz2 hle) le_sup_left
    rw [hSP] at hmax
    have : S1421.zbar L z hz ∈ (S : Subgroup _) ⊔ Subgroup.zpowers (S1421.zbar L z hz) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [hSP, hmax] at this
    exact this
  have hcent : S1421.zbar L z hz ∈
      (Subgroup.center ↥(S : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))).map
        (S : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)).subtype := by
    refine H13.J4.mem_center_map_iff.2 ⟨by rw [hSP]; exact hzb, fun y hy => ?_⟩
    rw [hSP] at hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPle hy)
  obtain ⟨hord', S', hS'⟩ := H13.J4.twoCentral_of_mulEquiv hcent e rfl
  have hT0 := ((H13.J4.concreteJ4_typeJ4).2.2.2.2 (e (S1421.zbar L z hz)) (hord'.trans hord)
    ⟨S', hS'⟩)
  have hT4 : IsTypeJ4Centralizer (↥L ⧸ CFSG.pCore 2 ↥L) (S1421.zbar L z hz) :=
    IsTypeJ4Centralizer.of_mulEquiv hT0 e.symm (e.symm_apply_apply _)
  obtain ⟨-, -, -, hAut, -⟩ := hT4
  obtain ⟨Z, hZn, hZ3, hZidx, hDperf, hDcenter, -, ψ, θ, hψsurj, hψker, -⟩ := hAut
  have hDD : ⁅Subgroup.centralizer (Z : Set (centQuot L z hz)),
      Subgroup.centralizer (Z : Set (centQuot L z hz))⁆ =
        Subgroup.centralizer (Z : Set (centQuot L z hz)) := by
    have h1 := congrArg (Subgroup.map (Subgroup.centralizer (Z : Set (centQuot L z hz))).subtype)
      hDperf.commutator_eq_top
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  have hZD : Z ≤ Subgroup.centralizer (Z : Set (centQuot L z hz)) := by
    intro x hx
    rw [← hDcenter] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hψk : (Nat.card ψ.ker).Prime := by
    rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, hZ3]
    exact Nat.prime_three
  have : IsSimpleGroup H13.J4.M22 := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := perfect_of_mem_cComp hKc
  have hK'perf : ⁅(oTwoUpper H).subgroupOf L, (oTwoUpper H).subgroupOf L⁆ =
      (oTwoUpper H).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKL, hKperf]
  have hK'z : (oTwoUpper H).subgroupOf L ≤
      Subgroup.centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKH.trans hHz (Subgroup.mem_subgroupOf.mp hk))
  have hK'norm : ∀ q ∈ Subgroup.centralizer ({(⟨z, hz⟩ : ↥L)} : Set ↥L),
      ∀ k ∈ (oTwoUpper H).subgroupOf L, q * k * q⁻¹ ∈ (oTwoUpper H).subgroupOf L := by
    intro q hq' k hk
    have hqM : (q : G) ∈ mcOf T := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [hZgen] at hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hcomm : Commute z (q : G) :=
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hq')).symm
      exact (hcomm.zpow_left n).eq
    have := (Subgroup.mem_normalizer_iff.mp (hKM hqM) (k : G)).mp (Subgroup.mem_subgroupOf.mp hk)
    exact this
  have hK'O : ∃ k ∈ (oTwoUpper H).subgroupOf L,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) k ∉
        (CFSG.pCore 2 ↥(Subgroup.centralizer ({S1421.zbar L z hz} : Set _))).map
          (Subgroup.centralizer ({S1421.zbar L z hz} : Set _)).subtype := by
    by_contra hcon
    push Not at hcon
    set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    set Cs : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      Subgroup.centralizer ({S1421.zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L)) with hCs
    have hOp : IsPGroup 2 ((CFSG.pCore 2 ↥Cs).map Cs.subtype) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Cs)).map Cs.subtype
    have hRle : ((oTwoUpper H).subgroupOf L).map π ≤ (CFSG.pCore 2 ↥Cs).map Cs.subtype := by
      rintro _ ⟨k, hk, rfl⟩
      exact hcon k hk
    have hRperf : ⁅((oTwoUpper H).subgroupOf L).map π, ((oTwoUpper H).subgroupOf L).map π⁆ =
        ((oTwoUpper H).subgroupOf L).map π := by
      rw [← Subgroup.map_commutator, hK'perf]
    have hRbot := eq_bot_of_perfect_of_isPGroup hRperf (hOp.to_le hRle)
    have hKle : (oTwoUpper H).subgroupOf L ≤ CFSG.pCore 2 ↥L := by
      intro k hk
      have : π k ∈ ((oTwoUpper H).subgroupOf L).map π := Subgroup.mem_map_of_mem π hk
      rw [hRbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have hK2 : IsPGroup 2 ((oTwoUpper H).subgroupOf L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hKle
    have hK2' : IsPGroup 2 (oTwoUpper H) :=
      hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKL)
    have : Group.IsNilpotent ↥(oTwoUpper H) := hK2'.isNilpotent
    exact not_isSolvable_of_mem_cComp hKc inferInstance
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ Subgroup.center ↥L := by
    rw [QuotientGroup.ker_mk']
    exact S1421.normal_isPGroup_le_center_of_isQuasisimple hq _
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have hdvd := card_dvd_of_perfect_normalized (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) hker (⟨z, hz⟩ : ↥L)
    (Subgroup.centralizer ({S1421.zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L))) rfl
    (CFSG.pCore 2 ↥(Subgroup.centralizer ({S1421.zbar L z hz} : Set (↥L ⧸ CFSG.pCore 2 ↥L))))
    (Subgroup.centralizer (Z : Set (centQuot L z hz))) hDD hZidx ψ hψsurj hψk
    ((oTwoUpper H).subgroupOf L) hK'perf hK'z hK'norm hK'O
  have h11 : 11 ∣ Nat.card (oTwoUpper H) := by
    have h1 : Nat.card H13.J4.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at hdvd
    exact (by norm_num : 11 ∣ 443520).trans hdvd
  have h11' : 11 ∣ Nat.card (OTwoQuot (oTwoUpper H)) :=
    dvd_card_oTwoQuot_of_dvd_card (by decide) h11
  exact not_eleven_dvd_card_exactType (exactType_oTwoQuot hKperf (by norm_num) (Or.inl hPSL)) h11'

end QA19

end CFSG.Quasithin
