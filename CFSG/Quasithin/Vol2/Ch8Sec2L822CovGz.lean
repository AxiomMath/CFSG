module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovGz4
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovList
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovE9
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQB
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQPhi
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQSyl
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQCentral
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQOver
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQJ4
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP6
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBRank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem cov_gz_false
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h36 : A36ForSQTK)
    (h312 : CFSG.QuasithinUnique.Vol2Native.A312ForSQTKCat)
    (hov24 : OverSylow2M24Cov) (hovHe : OverSylow2HeCov) (hJ4 : J4CoverFacts)
    (hM23 : Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960)
    (hcardJ4 : Nat.card CFSG.Blueprint.NativeSporadic.J4 = 86775571046077562880)
    (hcardM22 : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520)
    {G : Type} [Group G] [Finite G] (hqtke : quasithinIsQTKECat G) (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a)
    {T H M Lz : Subgroup G} {z y : G}
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hHz : H ≤ Subgroup.centralizer ({z} : Set G))
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) (hTH : T ≤ H) (hTM : T ≤ M)
    (hTsyl : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)))
    (hLzG : Lz ≤ Subgroup.centralizer ({z} : Set G)) (hTLz : T ≤ Subgroup.normalizer (Lz : Set G))
    (hLzF : Lz ∈ lFamily T) (hLzperf : ⁅Lz, Lz⁆ = Lz)
    (hLzq : IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)))
    (hyH : y ∈ H) (hyM : y ∈ M) (hyL : y ∈ Lz) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hcomm : ∀ l ∈ Lz, y⁻¹ * l⁻¹ * y * l ∈ pCoreOf 2 Lz)
    (hmp : MinParabolic H T (H ⊓ M)) (θ : ↥H →* Equiv.Perm (Fin 5)) (hθs : Function.Surjective θ)
    (hθJ : ∀ g : ↥H, (g : G) ∈ kerIn (H ⊓ M) H → θ g = 1)
    (hθy : θ ⟨y, hyH⟩ ≠ 1) (hH9 : ¬ 9 ∣ Nat.card H) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hsimple
  set Gz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hGz
  have hpC : CFSG.Open.pCoreOf 2 Gz ≠ ⊥ := kzPCoreCentralizerNeBot_kz3 hz1 hz2
  have hloc : LocalSQTK G := (qtkeCore_of_cat hnab hqtke).1
  have hSQ : SQTKGroup ↥Gz := sqtkGroup_of_pCoreOf_ne_bot hqtke hsimple hnab hpC
  obtain ⟨Kz, hKz, hLK⟩ := lemma_1_2_4_exists hqtke hsimple hnab h37 h39 hpC hTsyl hLzG hLzF
  have hKG : Kz ≤ Gz := le_of_mem_cComp hKz
  have hKn : Gz ≤ Subgroup.normalizer (Kz : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp
      (lemma_1_2_4_normal hqtke hsimple hnab h37 h38 hpC hTsyl hLzF hLK hKz hTLz)
  have hTK : T ≤ Subgroup.normalizer (Kz : Set G) := fun t ht => hKn (hTsyl.1 ht)
  obtain ⟨a, b, haL, hbL, hab, ha3, hb3, ha1, hba⟩ := exists_commuting_three_cv hLzq
  have hKq : CFSG.IsQuasisimple (↥Kz ⧸ CFSG.pCore 2 ↥Kz) :=
    CFSG.Quasithin.H13.Ch9.FFB.isQuasisimple_o2q h36 hSQ hKz hKn (hLK haL) (hLK hbL) hab ha3 hb3
      ha1 hba
  set K : Subgroup G := twoResidual H with hKdef
  have hKH : K ≤ H := twoResidual_le H
  have hKperf : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.1 (isPerfect_twoResidual_of_perm5_surj_cv hmp θ hθs)
  have hθK : (K.subgroupOf H).map θ = alternatingGroup (Fin 5) := map_twoResidual_perm5_cv H θ hθs
  have hy3ord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyK : y ∈ K := by
    rw [hKdef, F6.twoResidual_eq_oTwoUpper H]
    exact Subgroup.subset_closure ⟨hyH, by rw [hy3ord]; decide⟩
  have hyJ : y ∉ kerIn (H ⊓ M) H := fun h => hθy (hθJ ⟨y, hyH⟩ h)
  have hKKz : K ≤ Kz := by
    have hYn : H ≤ Subgroup.normalizer ((H ⊓ Kz : Subgroup G) : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh),
          (Subgroup.mem_normalizer_iff.mp (hKn (hHz hh)) x).mp hx.2⟩
      · intro hx
        have hh' : h⁻¹ ∈ H := H.inv_mem hh
        have h1 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ H ⊓ Kz := by
          refine ⟨H.mul_mem (H.mul_mem hh' hx.1) (H.inv_mem hh'), ?_⟩
          exact (Subgroup.mem_normalizer_iff.mp (hKn (hHz hh')) _).mp hx.2
        have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
        rwa [e] at h1
    rcases hmp.le_kerIn_or_twoResidual_le (inf_le_left : H ⊓ Kz ≤ H) hYn with h | h
    · exact absurd (h ⟨hyH, hLK hyL⟩) hyJ
    · exact h.trans inf_le_right
  by_cases heq : modO2Image Gz Lz = modO2Image Gz Kz
  ·
    exfalso
    have hconj := cov_Lbar_ne_Kbar hTsyl hTM hHz hLzG hLzq hLK hKz hKn hyM hyL hy3 hy1 hcomm heq
    apply hyJ
    rw [mem_kerIn]
    intro b hb
    exact ⟨H.mul_mem (H.mul_mem hb hyH) (H.inv_mem hb), hconj b hb⟩
  ·
    have hsix := cov_list_match hloc h312 hTsyl hpC hLzG hLzF hLzq hKz hLK heq hKq hM23
    have hS := cov_Q_sylow hTsyl hKG hTK
    have hθy' : θ ⟨y, hKH hyK⟩ ≠ 1 := hθy
    obtain ⟨hmemK, φ, hφs, hφy⟩ := cov_Q_phi hKH hKKz θ hθK hyK hθy'
    obtain ⟨hBperf, hSB, hBhat, hmemB, hytc⟩ := cov_Q_B hTLz hLK hLzperf hLzq hyL hy3 hcomm
    have hyt3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) ⟨y, hLK hyL⟩ : ↥Kz ⧸ CFSG.pCore 2 ↥Kz) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨y, hLK hyL⟩ : ↥Kz) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have hd : CoverQData (↥Kz ⧸ CFSG.pCore 2 ↥Kz) (modO2Image Kz (T ⊓ Kz)) (modO2Image Kz (H ⊓ Kz))
        (modO2Image Kz K) (modO2Image Kz Lz)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) ⟨y, hLK hyL⟩) :=
      { S2 := hS.1
        Sodd := hS.2
        SP := cov_modO2Image_mono (inf_le_inf_right Kz hTH)
        KP := cov_modO2Image_mono (le_inf hKH hKKz)
        P9 := cov_Q_P9 hH9
        Kperf := kzBq_commutator_kz3 hKKz hKperf
        ytK := hmemK
        Kphi := ⟨φ, hφs, hφy⟩
        Bperf := hBperf
        SB := hSB
        Bhat := hBhat
        ytB := hmemB
        yt3 := hyt3
        ytc := hytc }
    rcases hsix with h7 | h9 | h12 | h14 | h17 | h19
    · exact cover_Q_false_hat7 hd h7
    · exact cover_Q_false_su35 hd h9
    · exact cover_Q_false_hatM22 hcardM22 hd h12
    · exact cover_Q_false_M24 hov24 h14 hd
    · exact cover_Q_false_J4 hJ4 hcardJ4 hcardM22 h17 hd
    · exact cover_Q_false_He hovHe h19 hd

end CFSG.Quasithin.H13
