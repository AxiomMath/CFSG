module

public import CFSG.Quasithin.H13.U3Local
public import CFSG.Quasithin.H13.NQBlockOddResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem not_sq_dvd_two_pow_mul_three_pow_mul {p a b q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : q.Prime) : ¬ p ^ 2 ∣ 2 ^ a * 3 ^ b * q := by
  intro h
  have hc2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hc3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hc : Nat.Coprime (p ^ 2) (2 ^ a * 3 ^ b) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (hc2.pow_right a) (hc3.pow_right b))
  have h1 : p ^ 2 ∣ q := hc.dvd_of_dvd_mul_left h
  have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp ((dvd_pow_self p two_ne_zero).trans h1)
  have h4 : p ^ 2 ≤ q := Nat.le_of_dvd hq.pos h1
  rw [h3] at h4
  nlinarith [hq.two_le]

theorem card_eq_of_qt13Five (hord : U3.FiveQuotientExactOrders) {Q : Type} [Group Q] [Finite Q]
    (h : QT13Five Q) : Nat.card Q = 60 ∨ Nat.card Q = 168 ∨ Nat.card Q = 360 ∨
      Nat.card Q = 1080 ∨ Nat.card Q = 6048 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hord Q
  rcases h with h | h | h | ⟨hp, hc, he⟩ | h
  · exact Or.inl (h1 h)
  · exact Or.inr (Or.inl (h2 h))
  · exact Or.inr (Or.inr (Or.inl (h3 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h4 hp hc he))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h5 h))))

theorem not_sq_dvd_card_of_qt13Five (hord : U3.FiveQuotientExactOrders) {Q : Type} [Group Q]
    [Finite Q] (h : QT13Five Q) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card Q := by
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  rcases card_eq_of_qt13Five hord h with h | h | h | h | h <;> rw [h]
  · exact not_sq_dvd_two_pow_mul_three_pow_mul (a := 2) (b := 1) hp hp5 h5
  · exact not_sq_dvd_two_pow_mul_three_pow_mul (a := 3) (b := 1) hp hp5 h7
  · exact not_sq_dvd_two_pow_mul_three_pow_mul (a := 3) (b := 2) hp hp5 h5
  · exact not_sq_dvd_two_pow_mul_three_pow_mul (a := 3) (b := 3) hp hp5 h5
  · exact not_sq_dvd_two_pow_mul_three_pow_mul (a := 5) (b := 3) hp hp5 h7

theorem exists_prime_of_not_isQuasisimple {L : Type*} [Group L]
    [Finite L] (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ Nat.card (L ⧸ CFSG.pCore 2 L) ∧
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ CFSG.pCore 2 L)) := by
  classical
  obtain ⟨p, hp, hp5, D, -, -, hshape, hall⟩ :=
    NQBlock.nq_characteristic_radical_odd_residual_witness hSQT hLC hq
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hp5, ?_, ?_⟩
  · have hD : Nat.card D ∣ Nat.card (L ⧸ CFSG.pCore 2 L) := Subgroup.card_subgroup_dvd_card D
    rcases hshape with ⟨-, h2⟩ | ⟨-, h3, -⟩
    · rwa [h2] at hD
    · rw [h3] at hD
      exact (pow_dvd_pow p (by norm_num)).trans hD
  · set π := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
    set E : Subgroup L := D.comap π with hE
    set X : Subgroup L := closure {x | x ∈ E ∧ Odd (orderOf x)} with hX
    obtain ⟨-, -, -, -, -, hker, -, hrk, -⟩ := hall E X rfl rfl
    set f : X →* L ⧸ CFSG.pCore 2 L := π.comp X.subtype with hf
    have e : (X ⧸ CFSG.pCore 2 X) ≃* f.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange f)
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) = 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrk
    have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
    have h3 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt f.range.subtype
      f.range.subtype_injective
    omega

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_modO2_dvd_of_le {K L : Subgroup G} (hKL : K ≤ L) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥K →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hKL) with hf
  have hkerf : f.ker = (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hKL) := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hker : f.ker ≤ CFSG.pCore 2 ↥K := by
    have hp : IsPGroup 2 f.ker := by
      rw [hkerf]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective _
        (Subgroup.inclusion_injective hKL)
    exact le_sSup ⟨inferInstance, hp⟩
  have h1 : (CFSG.pCore 2 ↥K).index ∣ f.ker.index := Subgroup.index_dvd_of_le hker
  have h2 : f.ker.index = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.range ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.card_subgroup_dvd_card _
  exact h1.trans (h2 ▸ h3)

theorem exists_isMaximalLocal_ge {T K : Subgroup G} (hK : quasithinIsLocal T K) :
    ∃ L : Subgroup G, K ≤ L ∧ quasithinIsMaximalLocal T L := by
  obtain ⟨L, hL⟩ := (Set.toFinite {X : Subgroup G | quasithinIsLocal T X ∧ K ≤ X}).exists_maximal
    ⟨K, hK, le_rfl⟩
  exact ⟨L, hL.1.2, hL.1.1, fun X hX hLX => le_antisymm (hL.2 ⟨hX, hL.1.2.trans hLX⟩ hLX) hLX⟩

theorem isFaithfulLocal_of_le_of_le_normalizer (hQ : quasithinIsQTKECat G) {T K L : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsFaithfulLocal T K) (hL : quasithinIsLocal T L)
    (hKL : K ≤ L) (hTK : T ≤ normalizer (K : Set G)) : quasithinIsFaithfulLocal T L := by
  obtain ⟨-, hKX⟩ := isFaithfulLocal_iff_isXf.mp hK
  set R := T ⊓ normalizer (L : Set G) with hR
  have hRK : R ≤ normalizer (K : Set G) := inf_le_left.trans hTK
  have hLR : T ⊓ L ≤ R := le_inf inf_le_left (inf_le_right.trans le_normalizer)
  have hRsyl : IsSylowTwoOf R (L ⊔ R) := isSylowTwoOf_sup_of_isLocal hL inf_le_left inf_le_right hLR
  have hO2 : pCoreOf 2 (L ⊔ R) ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsyl
  have hA : A410Hyp K L R :=
    { xclass := hKX.1
      yclass := isXClass_of_isLocal hQ hT hL
      xy := hKL
      normalizes := inf_le_right
      sylowT := hRsyl
      o2le := le_inf hO2 (hO2.trans hRK)
      sylowNT := by
        rw [inf_eq_left.mpr hRK]
        exact A4.isSylowTwoOf_mono hRsyl (le_inf le_sup_right hRK) inf_le_left }
  exact isFaithfulLocal_iff_isXf.mpr ⟨hL, a4_10_3 hA hKX⟩

theorem le_normalizer_of_pRank_eq_two (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {T K : Subgroup G}
    (hKl : quasithinIsLocal T K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : CFSG.Open.pRank p K = 2) : T ≤ normalizer (K : Set G) := by
  have hn := Vol2Native.lemma_1_2_2_b hK h37 h38 Id2519.lemma122Rank hKl.2.2.2
    (cComp_of_isLocal hKl) hp hp2 hm
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)

theorem nonquasisimple_maximal_local_of_faithful
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1323 : Stmt13_1_2_three)
    (hord : U3.FiveQuotientExactOrders) [hs : IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : quasithinIsQTKECat G) (hX : ¬ QT13Excluded G) {T K : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hKf : quasithinIsFaithfulLocal T K)
    (hKq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ L : Subgroup G, K ≤ L ∧ quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L ∧
      T ≤ normalizer (L : Set G) ∧ ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : LocalSQTK G := (qtkeCore_of_cat hnab hQ).1
  have hKl := hKf.1
  have hO2K : pCoreOf 2 K ≠ ⊥ := U3.pCoreOf_ne_bot_of_isFaithfulLocal hKf
  have hsqt : CFSG.IsStronglyQuasithin ↥K := (hK K hO2K).1
  have hKc : K ∈ cComp (K ⊔ T) := cComp_of_isLocal hKl
  have hKtop : CFSG.IsCComponent (⊤ : Subgroup ↥K) := by
    have h3 := mem_cComp_top_iff_isCComponent.mp
      (subgroupOf_mem_cComp (cComp_mem_of_le hKc le_rfl le_sup_left))
    rwa [subgroupOf_self] at h3
  obtain ⟨p, hp, hp5, hdvd, hrk⟩ := exists_prime_of_not_isQuasisimple hsqt hKtop hKq
  have hp2 : p ≠ 2 := by omega
  have hmK : CFSG.Open.pRank p K = 2 := by
    have h1 := pRank_modO2_eq K hp hp2
    have h2 : CFSG.pRank p ↥K ≤ 2 := hsqt p hp hp2
    rw [Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp] at h2
    omega
  have hTK : T ≤ normalizer (K : Set G) := le_normalizer_of_pRank_eq_two hK h37 h38 hKl hp hp2 hmK
  obtain ⟨L, hKL, hLmax⟩ := exists_isMaximalLocal_ge hKl
  have hLf : quasithinIsFaithfulLocal T L :=
    isFaithfulLocal_of_le_of_le_normalizer hQ hT hKf hLmax.1 hKL hTK
  have hTL : T ≤ normalizer (L : Set G) := by
    have hS : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right
    have hn := Vol2Native.lemma_1_2_4_normal hK h37 h38 hLmax.1.2.2.2 hS
      (mem_lFamily_of_isLocal hKl) hKL (cComp_of_isLocal hLmax.1) hTK
    exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)
  refine ⟨L, hKL, hLmax, hLf, hTL, fun hLq => ?_⟩
  have h5 := h1323 G T L hs hnab hQ hT hX hLmax hLf hLq
  exact not_sq_dvd_card_of_qt13Five hord h5 hp hp5 (hdvd.trans (card_modO2_dvd_of_le hKL))

end CFSG.Quasithin.H13.NQCore
