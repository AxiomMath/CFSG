module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixLLift
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16_exists_perfect_centralizer_of_three_calC
    {M K₁ K₂ K₃ : Subgroup G}
    (h₁ : K₁ ∈ calC M) (h₂ : K₂ ∈ calC M) (h₃ : K₃ ∈ calC M)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hd₂ : p ∣ Nat.card K₂) (hd₃ : p ∣ Nat.card K₃)
    (hZ₂ : ¬ p ∣ Nat.card (Subgroup.center (Bar2 K₂)))
    (hZ₃ : ¬ p ∣ Nat.card (Subgroup.center (Bar2 K₃)))
    {b : G} (hbK : b ∈ K₁) (hbr : b ^ r = 1) :
    ∃ X : Subgroup G,
      X ≤ (K₂ ⊔ K₃) ⊓ Subgroup.centralizer ({b} : Set G) ∧
      ⁅X, X⁆ = X ∧ 2 ≤ CFSG.Open.pRank p X := by
  classical
  have hrFact : Fact r.Prime := ⟨hr⟩
  let S : Subgroup G := K₂ ⊔ K₃
  have hK₂S : K₂ ≤ S := le_sup_left
  have hK₃S : K₃ ≤ S := le_sup_right
  let T : Subgroup G := Subgroup.zpowers b ⊔ S
  have hK₂T : K₂ ≤ T := hK₂S.trans le_sup_right
  have hK₃T : K₃ ≤ T := hK₃S.trans le_sup_right
  have hST : S ≤ T := le_sup_right
  have hSNorm₂ : S ≤ Subgroup.normalizer (K₂ : Set G) :=
    sup_le Subgroup.le_normalizer (calC_le_normalizer_of_ne h₂ h₃ h23)
  have hSNorm₃ : S ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (calC_le_normalizer_of_ne h₃ h₂ h23.symm) Subgroup.le_normalizer
  have hsub₂ : CFSG.Open.IsSubnormal K₂ S :=
    CFSG.Quasithin.A4.subnormal_of_normal hK₂S
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₂S).2 hSNorm₂)
  have hsub₃ : CFSG.Open.IsSubnormal K₃ S :=
    CFSG.Quasithin.A4.subnormal_of_normal hK₃S
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₃S).2 hSNorm₃)
  have hbNS : b ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hb₂ : b ∈ Subgroup.normalizer (K₂ : Set G) :=
      (calC_le_normalizer_of_ne h₂ h₁ h12.symm) hbK
    have hb₃ : b ∈ Subgroup.normalizer (K₃ : Set G) :=
      (calC_le_normalizer_of_ne h₃ h₁ h13.symm) hbK
    change S.map (MulAut.conj b).toMonoidHom = S
    have hmap₂ : K₂.map (MulAut.conj b).toMonoidHom = K₂ :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 hb₂
    have hmap₃ : K₃.map (MulAut.conj b).toMonoidHom = K₃ :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 hb₃
    rw [show S = K₂ ⊔ K₃ from rfl, Subgroup.map_sup, hmap₂, hmap₃]
  have hTnorm : T ≤ Subgroup.normalizer (S : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hbNS) Subgroup.le_normalizer
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 S
  have hQS : Q ≤ S := CFSG.LieType.BorelTits.pCoreOf_le 2 S
  have hQT : Q ≤ T := hQS.trans hST
  have hQnorm : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 S)
  let N : Subgroup T := Q.subgroupOf T
  let R : Subgroup T := S.subgroupOf T
  have hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).2 hQnorm
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S
  have hN2 : IsPGroup 2 N := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQT).symm
  have hrN : ¬ r ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    exact hr2 (Nat.prime_eq_prime_of_dvd_pow hr Nat.prime_two h)
  have hpN : ¬ p ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h)
  let bT : T := ⟨b, Subgroup.mem_sup_left (Subgroup.mem_zpowers b)⟩
  have hbrT : bT ^ r = 1 := by
    apply Subtype.ext
    simpa [bT] using hbr
  have hXp : IsPGroup r (Subgroup.zpowers bT) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hbrT
  let X : Subgroup T := Subgroup.zpowers bT
  let π : T →* T ⧸ N := QuotientGroup.mk' N
  let Pb : Subgroup (T ⧸ N) := R.map π
  have hSperf : ⁅S, S⁆ = S := by
    have h := commutator_sup_sup (M := M) (L₁ := K₂) (L₂ := K₂) (L₃ := K₃) h₂ h₂ h₃
    simpa [S, sup_idem] using h
  have hRperf : ⁅R, R⁆ = R := by
    apply Subgroup.map_injective (f := T.subtype) T.subtype_injective
    rw [Subgroup.map_commutator (H₁ := R) (H₂ := R) T.subtype,
      Subgroup.map_subgroupOf_eq_of_le hST, hSperf]
  have hPb : ⁅Pb, Pb⁆ = Pb := by
    change ⁅R.map π, R.map π⁆ = R.map π
    rw [← Subgroup.map_commutator (H₁ := R) (H₂ := R) π, hRperf]
  have hcomm₂ : ∀ x (hx : x ∈ K₂),
      π bT * π (⟨x, hK₂T hx⟩ : T) = π (⟨x, hK₂T hx⟩ : T) * π bT := by
    intro x hx
    have hmemK : ⁅b, x⁆ ∈ CFSG.Open.pCoreOf 2 K₂ :=
      (calC_commutator_le_of_ne h₁ h₂ h12
        (Subgroup.commutator_mem_commutator hbK hx)).2
    have hmemQ : ⁅b, x⁆ ∈ Q :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub₂ hmemK
    have hmemN : (⁅bT, (⟨x, hK₂T hx⟩ : T)⁆ : T) ∈ N := by
      change (⁅bT, (⟨x, hK₂T hx⟩ : T)⁆ : T) ∈ Q.subgroupOf T
      rw [Subgroup.mem_subgroupOf]
      change T.subtype ⁅bT, (⟨x, hK₂T hx⟩ : T)⁆ ∈ Q
      rw [map_commutatorElement]
      simpa using hmemQ
    have h1 : π ⁅bT, (⟨x, hK₂T hx⟩ : T)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemN
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcomm₃ : ∀ x (hx : x ∈ K₃),
      π bT * π (⟨x, hK₃T hx⟩ : T) = π (⟨x, hK₃T hx⟩ : T) * π bT := by
    intro x hx
    have hmemK : ⁅b, x⁆ ∈ CFSG.Open.pCoreOf 2 K₃ :=
      (calC_commutator_le_of_ne h₁ h₃ h13
        (Subgroup.commutator_mem_commutator hbK hx)).2
    have hmemQ : ⁅b, x⁆ ∈ Q :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub₃ hmemK
    have hmemN : (⁅bT, (⟨x, hK₃T hx⟩ : T)⁆ : T) ∈ N := by
      change (⁅bT, (⟨x, hK₃T hx⟩ : T)⁆ : T) ∈ Q.subgroupOf T
      rw [Subgroup.mem_subgroupOf]
      change T.subtype ⁅bT, (⟨x, hK₃T hx⟩ : T)⁆ ∈ Q
      rw [map_commutatorElement]
      simpa using hmemQ
    have h1 : π ⁅bT, (⟨x, hK₃T hx⟩ : T)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemN
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hPbX : Pb ≤
      Subgroup.centralizer ((X.map π : Subgroup (T ⧸ N)) : Set (T ⧸ N)) := by
    have hXmap : X.map π = Subgroup.zpowers (π bT) := MonoidHom.map_zpowers π bT
    rw [hXmap]
    intro y hy
    change y ∈ R.map π at hy
    obtain ⟨k, hkR, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    have hkS : (k : G) ∈ S := Subgroup.mem_subgroupOf.mp hkR
    have hkS' : (k : G) ∈ (K₂ : Set G) * (K₃ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K₂ K₃
        (calC_le_normalizer_of_ne h₂ h₃ h23)]
      exact hkS
    obtain ⟨k₂, hk₂, k₃, hk₃, hk23⟩ := Set.mem_mul.mp hkS'
    let k₂T : T := ⟨k₂, hK₂T hk₂⟩
    let k₃T : T := ⟨k₃, hK₃T hk₃⟩
    have hk_eq : k = k₂T * k₃T := by
      apply Subtype.ext
      change (k : G) = k₂ * k₃
      exact hk23.symm
    calc π k * π bT
        = π (k₂T * k₃T) * π bT := by rw [hk_eq]
      _ = (π k₂T * π k₃T) * π bT := by rw [map_mul]
      _ = π k₂T * (π k₃T * π bT) := by group
      _ = π k₂T * (π bT * π k₃T) := by rw [← hcomm₃ k₃ hk₃]
      _ = (π k₂T * π bT) * π k₃T := by group
      _ = (π bT * π k₂T) * π k₃T := by rw [← hcomm₂ k₂ hk₂]
      _ = π bT * (π k₂T * π k₃T) := by group
      _ = π bT * π k := by rw [← map_mul, ← hk_eq]
  obtain ⟨P, hPC, hPperf, hPmap⟩ :=
    CFSG.SeitzReduction.LinearPilot.exists_perfect_le_centralizer_map_eq_of_coprime
      r N hrN hXp hPb hPbX
  have hNR : N ≤ R := by
    intro x hx
    change x ∈ Q.subgroupOf T at hx
    change x ∈ S.subgroupOf T
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hQS hx
  have hPleR : P ≤ R := by
    have hker : MonoidHom.ker π ≤ R := by
      change MonoidHom.ker (QuotientGroup.mk' N) ≤ R
      rw [QuotientGroup.ker_mk']
      exact hNR
    have hcomap : (R.map π).comap π = R := Subgroup.comap_map_eq_self hker
    have h1 : P ≤ (R.map π).comap π := by
      have h := Subgroup.le_comap_map (f := π) P
      rwa [show P.map π = R.map π from hPmap] at h
    rwa [hcomap] at h1
  have h2S : 2 ≤ CFSG.Open.pRank p S := by
    have hS : ∀ L ∈ ({K₂, K₃} : Finset (Subgroup G)), L ∈ calC S := by
      intro L hL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      · exact P22fin3.mem_calC_of_le_normalizer h₂ hK₂S hSNorm₂
      · exact P22fin3.mem_calC_of_le_normalizer h₃ hK₃S hSNorm₃
    have hZ : ∀ L ∈ ({K₂, K₃} : Finset (Subgroup G)),
        ¬ p ∣ Nat.card (Subgroup.center (Bar2 L)) := by
      intro L hL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      exacts [hZ₂, hZ₃]
    have hd : ∀ L ∈ ({K₂, K₃} : Finset (Subgroup G)), p ∣ Nat.card L := by
      intro L hL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      exacts [hd₂, hd₃]
    have h := P22fin3.card_le_pRank_of_finset (X := S)
      (S := ({K₂, K₃} : Finset (Subgroup G))) hp hp2 hS hZ hd
    rwa [Finset.card_pair h23] at h
  have hpker : ¬ p ∣ Nat.card ↥(MonoidHom.ker π) := by
    rwa [show MonoidHom.ker π = N from QuotientGroup.ker_mk' N]
  have hrankPR : CFSG.Open.pRank p P = CFSG.Open.pRank p R := by
    have hP := CFSG.pRank_map_eq_of_not_dvd_card_ker π
      (QuotientGroup.mk'_surjective N) hp hpker P
    have hR := CFSG.pRank_map_eq_of_not_dvd_card_ker π
      (QuotientGroup.mk'_surjective N) hp hpker R
    have hPmap' : P.map π = R.map π := hPmap
    have hP' : CFSG.Open.pRank p (R.map π) = CFSG.Open.pRank p P := by
      rw [← hPmap']
      exact hP
    exact hP'.symm.trans hR
  have hrankRS : CFSG.Open.pRank p R = CFSG.Open.pRank p S := by
    have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt
      (Subgroup.subgroupOfEquivOfLe hST)
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup R, h,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup S]
  have hXleS : P.map T.subtype ≤ S := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hST]
    exact Subgroup.map_mono hPleR
  have hXleC : P.map T.subtype ≤ Subgroup.centralizer ({b} : Set G) := by
    rintro x ⟨q, hqP, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqC : q ∈ Subgroup.centralizer (X : Set T) := hPC hqP
    have hcomm : bT * q = q * bT :=
      (Subgroup.mem_centralizer_iff.mp hqC) bT (Subgroup.mem_zpowers bT)
    simpa using (congrArg T.subtype hcomm).symm
  have hXperf : ⁅P.map T.subtype, P.map T.subtype⁆ = P.map T.subtype := by
    rw [← Subgroup.map_commutator (H₁ := P) (H₂ := P) T.subtype, hPperf]
  have h2P : 2 ≤ CFSG.Open.pRank p P := by
    rw [hrankPR, hrankRS]
    exact h2S
  have hXrank : 2 ≤ CFSG.Open.pRank p (P.map T.subtype) :=
    le_trans h2P (CFSG.SectionRank.pRank_le_map (p := p) hp.one_lt T.subtype
      T.subtype_injective P)
  exact ⟨P.map T.subtype, le_inf hXleS hXleC, hXperf, hXrank⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
