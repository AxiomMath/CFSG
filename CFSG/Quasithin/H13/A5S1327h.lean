module

public import CFSG.Quasithin.H13.A5S1327g

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

@[expose] def FactL2Three : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], p.Prime → (p % 24 = 11 ∨ p % 24 = 13) →
    F6.IsL2 p 1 K → CFSG.IsQuasisimple K ∧ (∀ b : ℕ, Nat.card K ≠ 60 * 2 ^ b) ∧
      ∀ P : Subgroup K, IsPGroup 2 ↥P → Nat.card ↥P ≤ 4

section Commuting

variable {D : Type*} [Group D] {K Zc : Subgroup D}

theorem exists_mul_of_mem_sup_comm (hcomm : ∀ k ∈ K, ∀ z ∈ Zc, k * z = z * k) {x : D}
    (hx : x ∈ K ⊔ Zc) : ∃ k ∈ K, ∃ z ∈ Zc, x = k * z := by
  have hZN : Zc ≤ Subgroup.normalizer (K : Set D) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K : Set D))
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => hcomm k hk z hz
  have hx' : x ∈ ((K ⊔ Zc : Subgroup D) : Set D) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K Zc hZN] at hx'
  obtain ⟨k, hk, z, hz, rfl⟩ := hx'
  exact ⟨k, hk, z, hz, rfl⟩

theorem sup_le_normalizer_of_comm (hcomm : ∀ k ∈ K, ∀ z ∈ Zc, k * z = z * k) :
    K ⊔ Zc ≤ Subgroup.normalizer (K : Set D) := by
  refine sup_le Subgroup.le_normalizer ?_
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K : Set D))
  intro z hz
  exact Subgroup.mem_centralizer_iff.mpr fun k hk => hcomm k hk z hz

theorem mem_of_mem_sup_of_two_pow [Finite D] (hcomm : ∀ k ∈ K, ∀ z ∈ Zc, k * z = z * k)
    (hZc : Nat.card ↥Zc = 3) (hKZ : K ⊓ Zc = ⊥) {x : D} (hx : x ∈ K ⊔ Zc) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1) : x ∈ K := by
  obtain ⟨k, hk, z, hz, rfl⟩ := exists_mul_of_mem_sup_comm hcomm hx
  have hc : Commute k z := hcomm k hk z hz
  rw [hc.mul_pow] at hxn
  have hzK : z ^ 2 ^ n ∈ K := by
    have : z ^ 2 ^ n = (k ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hxn
    rw [this]
    exact K.inv_mem (K.pow_mem hk _)
  have hz1 : z ^ 2 ^ n = 1 := by
    have h1 : z ^ 2 ^ n ∈ K ⊓ Zc := ⟨hzK, Zc.pow_mem hz _⟩
    rw [hKZ, Subgroup.mem_bot] at h1
    exact h1
  have hz3 : z ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥Zc) (x := ⟨z, hz⟩)
    rw [hZc] at h1
    simpa using congrArg Subtype.val h1
  have hz : z = 1 := eq_one_of_pow_coprime hz1 hz3 (Nat.Coprime.pow_left n (by norm_num))
  rw [hz, mul_one]
  exact hk

theorem comm_of_comm_ne_one (hZc : Nat.card ↥Zc = 3) {z : D} (hz : z ∈ Zc) (hz1 : z ≠ 1) {r : D}
    (hr : r * z * r⁻¹ = z) : ∀ y ∈ Zc, r * y * r⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : Subgroup.zpowers (⟨z, hz⟩ : ↥Zc) = ⊤ :=
    zpowers_eq_top_of_prime_card hZc (fun h => hz1 (by simpa using congrArg Subtype.val h))
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥Zc) ∈ Subgroup.zpowers (⟨z, hz⟩ : ↥Zc) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hy' : y = z ^ m := by
    have := congrArg Subtype.val hm
    simpa using this.symm
  rw [hy', ← conj_zpow, hr]

theorem comm_of_card_three (hZc : Nat.card ↥Zc = 3) {y z : D} (hy : y ∈ Zc) (hz : z ∈ Zc) :
    y * z = z * y := by
  by_cases hy1 : y = 1
  · rw [hy1, one_mul, mul_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : Subgroup.zpowers (⟨y, hy⟩ : ↥Zc) = ⊤ :=
    zpowers_eq_top_of_prime_card hZc (fun h => hy1 (by simpa using congrArg Subtype.val h))
  have hmem : (⟨z, hz⟩ : ↥Zc) ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Zc) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz' : z = y ^ m := by
    have := congrArg Subtype.val hm
    simpa using this.symm
  rw [hz']
  exact ((Commute.refl y).zpow_right m).eq

end Commuting

theorem InK4_mul_inv_of_not : ∀ σ τ : Equiv.Perm (Fin 5), InD σ → InD τ → ¬ InK4 σ → ¬ InK4 τ →
    InK4 (σ * τ⁻¹) := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure Case3 (S : Setting G T L V) (H : Subgroup G)
    (K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥K
  card_ne : ∀ b : ℕ, Nat.card ↥K ≠ 60 * 2 ^ b
  card_two_le : ∀ P : Subgroup ↥K, IsPGroup 2 ↥P → Nat.card ↥P ≤ 4
  card_Zc : Nat.card ↥Zc = 3
  sup_eq : K ⊔ Zc = twoResidual ⊤
  inf_eq : K ⊓ Zc = ⊥
  comm : ∀ k ∈ K, ∀ z ∈ Zc, k * z = z * k
  dihedral : Nonempty (↥(S.G1bar H ⊓ S.G2bar H) ≃* DihedralGroup 4)
  outer : ∀ t ∈ S.G1bar H ⊓ S.G2bar H, t ∉ K → F6.InducesOuterAut t K ∧ F6.InducesOuterAut t Zc

theorem case3_of (S : Setting G T L V) (hL2 : FactL2Three) {H : Subgroup G}
    (h : F6.IsF618CaseThree (S.G1bar H) (S.G2bar H) ∨ F6.IsF618CaseThree (S.G2bar H) (S.G1bar H)) :
    ∃ K Zc, S.Case3 H K Zc := by
  rcases h with ⟨p, K, Zc, hp, hp24, hL, hZc, hsup, hinf, hcomm, ⟨e⟩, -, -, hout⟩ |
      ⟨p, K, Zc, hp, hp24, hL, hZc, hsup, hinf, hcomm, ⟨e⟩, -, -, hout⟩
  · obtain ⟨hq, hc, h2⟩ := hL2 p ↥K hp hp24 hL
    exact ⟨K, Zc, hq, hc, h2, hZc, hsup, hinf, hcomm, ⟨e⟩, hout⟩
  · obtain ⟨hq, hc, h2⟩ := hL2 p ↥K hp hp24 hL
    rw [inf_comm] at e hout
    exact ⟨K, Zc, hq, hc, h2, hZc, hsup, hinf, hcomm, ⟨e⟩, hout⟩

variable (S : Setting G T L V)
include S

theorem map_mem_twoResidual {H : Subgroup G} {x : G} (hx : x ∈ S.H0 H) (hxo : Odd (orderOf x)) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) ⟨x, hx⟩ ∈ twoResidual ⊤ := by
  rw [twoResidual_eq_oTwoUpper']
  refine mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_
  have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat hxo h1

theorem map_oTwoUpper_le {H : Subgroup G} {x : G} (hx : x ∈ oTwoUpper H) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) ⟨x, Subgroup.mem_sup_right (oTwoUpper_le H hx)⟩
      ∈ twoResidual ⊤ := by
  have hle : oTwoUpper H ≤ ((twoResidual (⊤ : Subgroup (↥(S.H0 H) ⧸
      CFSG.pPrimeCore 3 ↥(S.H0 H)))).comap (QuotientGroup.mk' _)).map (S.H0 H).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyH, hyo⟩
    exact ⟨⟨y, Subgroup.mem_sup_right hyH⟩, S.map_mem_twoResidual _ hyo, rfl⟩
  obtain ⟨w, hw, hwx⟩ := hle hx
  have : w = ⟨x, Subgroup.mem_sup_right (oTwoUpper_le H hx)⟩ := Subtype.ext hwx
  rw [← this]
  exact hw

theorem map_L1_le {H : Subgroup G} {x : G} (hx : x ∈ S.L1) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) ⟨x, Subgroup.mem_sup_left (S.L1_le_borel_L hx)⟩
      ∈ twoResidual ⊤ := by
  have hle : S.L1 ≤ ((twoResidual (⊤ : Subgroup (↥(S.H0 H) ⧸
      CFSG.pPrimeCore 3 ↥(S.H0 H)))).comap (QuotientGroup.mk' _)).map (S.H0 H).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyL, m, hm, hym⟩
    have hyL1 : y ∈ S.L1 := Subgroup.subset_closure ⟨hyL, m, hm, hym⟩
    have hyo : Odd (orderOf y) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym)
    exact ⟨⟨y, Subgroup.mem_sup_left (S.L1_le_borel_L hyL1)⟩, S.map_mem_twoResidual _ hyo, rfl⟩
  obtain ⟨w, hw, hwx⟩ := hle hx
  have : w = ⟨x, Subgroup.mem_sup_left (S.L1_le_borel_L hx)⟩ := Subtype.ext hwx
  rw [← this]
  exact hw

theorem map_T_mem_inf {H : Subgroup G} (hTH : T ≤ H) {t : G} (ht : t ∈ T) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) ⟨t, Subgroup.mem_sup_right (hTH ht)⟩ ∈
      S.G1bar H ⊓ S.G2bar H :=
  ⟨⟨⟨t, Subgroup.mem_sup_right (hTH ht)⟩, show t ∈ S.L1 ⊔ T from Subgroup.mem_sup_right ht, rfl⟩,
    ⟨⟨t, Subgroup.mem_sup_right (hTH ht)⟩, show t ∈ H from hTH ht, rfl⟩⟩

theorem normal_K {H : Subgroup G} (hTH : T ≤ H)
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc) :
    K.Normal := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) with hπ
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have hKN : K ⊔ Zc ≤ Subgroup.normalizer (K : Set _) := sup_le_normalizer_of_comm hc.comm
  have hle : S.H0 H ≤ ((Subgroup.normalizer (K : Set (↥(S.H0 H) ⧸
      CFSG.pPrimeCore 3 ↥(S.H0 H)))).comap π).map (S.H0 H).subtype := by
    refine (le_of_eq (eq_oTwoUpper_sup_of_isSylowTwoOf'
      (isSylowTwoOf_of_le S.h13.sylow hTI))).trans ?_
    refine sup_le ?_ fun t ht => ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyI, hyo⟩
      refine ⟨⟨y, hyI⟩, hKN ?_, rfl⟩
      rw [hc.sup_eq]
      exact S.map_mem_twoResidual hyI hyo
    · refine ⟨⟨t, hTI ht⟩, ?_, rfl⟩
      by_cases htK : π ⟨t, hTI ht⟩ ∈ K
      · exact Subgroup.le_normalizer htK
      · exact (hc.outer _ (S.map_T_mem_inf hTH ht) htK).1.1
  refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => ?_)
  obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(S.H0 H)) g
  obtain ⟨w, hw, hwi⟩ := hle i.2
  have : w = i := Subtype.ext hwi
  rw [← this]
  exact hw

theorem normal_Zc {H : Subgroup G} (hTH : T ≤ H)
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc) :
    Zc.Normal := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) with hπ
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have hKZN : K ⊔ Zc ≤ Subgroup.normalizer
      (Zc : Set (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer
      (Zc : Set (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))))
    refine sup_le (fun k hk => ?_) (fun z hz => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun z hz => (hc.comm k hk z hz).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy => comm_of_card_three hc.card_Zc hy hz
  have hle : S.H0 H ≤ ((Subgroup.normalizer (Zc : Set (↥(S.H0 H) ⧸
      CFSG.pPrimeCore 3 ↥(S.H0 H)))).comap π).map (S.H0 H).subtype := by
    refine (le_of_eq (eq_oTwoUpper_sup_of_isSylowTwoOf'
      (isSylowTwoOf_of_le S.h13.sylow hTI))).trans ?_
    refine sup_le ?_ fun t ht => ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyI, hyo⟩
      refine ⟨⟨y, hyI⟩, hKZN ?_, rfl⟩
      rw [hc.sup_eq]
      exact S.map_mem_twoResidual hyI hyo
    · refine ⟨⟨t, hTI ht⟩, ?_, rfl⟩
      by_cases htK : π ⟨t, hTI ht⟩ ∈ K
      · exact hKZN (Subgroup.mem_sup_left htK)
      · exact (hc.outer _ (S.map_T_mem_inf hTH ht) htK).2.1
  refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => ?_)
  obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(S.H0 H)) g
  obtain ⟨w, hw, hwi⟩ := hle i.2
  have : w = i := Subtype.ext hwi
  rw [← this]
  exact hw

theorem exists_L0 {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥)
    (hN3s : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥(S.H0 H)))
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc) :
    ∃ L' : Subgroup ↥(S.H0 H), L' ∈ cComp (⊤ : Subgroup ↥(S.H0 H)) ∧
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) = K ∧ L'.Normal ∧
      ⁅quasithinOmegaOneCenter T, L'.map (S.H0 H).subtype⁆ = ⊥ := by
  set N3 := CFSG.pPrimeCore 3 ↥(S.H0 H) with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hKn := S.normal_K hH.1.1 hc
  have hKc : K ∈ cComp (⊤ : Subgroup (↥(S.H0 H) ⧸ N3)) :=
    mem_cComp_top_of_isComponent ⟨hc.quasisimple, hKn.isSubnormal⟩
  have hbij := cComp_quotient_bijOn N3 hN3s
  obtain ⟨L', hL', hL'K⟩ := hbij.2.2 hKc
  refine ⟨L', hL', hL'K, ⟨fun l hl h => ?_⟩, ?_⟩
  ·
    set e := MulAut.conj h with he
    have hL'' : L'.map e.toMonoidHom ∈ cComp (⊤ : Subgroup ↥(S.H0 H)) := by
      have := cComp_map_mulEquiv e hL'
      rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
    have himg : (L'.map e.toMonoidHom).map π = L'.map π := by
      rw [Subgroup.map_map, hL'K]
      have hcomp : π.comp e.toMonoidHom = (MulAut.conj (π h)).toMonoidHom.comp π := by
        ext x
        simp [he, MulAut.conj_apply, map_mul, map_inv]
      rw [hcomp, ← Subgroup.map_map, hL'K]
      apply le_antisymm
      · rintro _ ⟨k, hk, rfl⟩
        exact hKn.conj_mem k hk (π h)
      · intro k hk
        refine ⟨(π h)⁻¹ * k * (π h)⁻¹⁻¹, hKn.conj_mem k hk _, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    have heq : L'.map e.toMonoidHom = L' := hbij.2.1 hL'' hL' himg
    rw [← heq]
    exact ⟨l, hl, rfl⟩
  ·
    by_contra hne
    obtain ⟨b, hb⟩ := S.card_image_of_comm_ne hH hO2 hL' hne
    rw [hL'K] at hb
    exact hc.card_ne b hb

theorem mul_inv_mem_R1 {t p : G} (ht : t ∈ T) (hp : p ∈ T) (htR : t ∉ S.R1) (hpR : p ∉ S.R1) :
    t * p⁻¹ ∈ S.R1 := by
  have htp : t * p⁻¹ ∈ T := T.mul_mem ht (T.inv_mem hp)
  refine (S.mem_R1 htp).2 ?_
  have e : (⟨t * p⁻¹, S.frame.T_le htp⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨t, S.frame.T_le ht⟩ * (⟨p, S.frame.T_le hp⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv]
  exact InK4_mul_inv_of_not _ _ (S.frame.T_D _ ht) (S.frame.T_D _ hp)
    (fun h => htR ((S.mem_R1 ht).2 h)) (fun h => hpR ((S.mem_R1 hp).2 h))

theorem exists_R1_not_comm (h331 : Stmt3_3_1)
    (h311 : Theorem311Stmt) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc) :
    ∃ r : ↥(S.H0 H), (r : G) ∈ S.R1 ∧ ∃ z ∈ Zc,
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) r * z *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) r)⁻¹ ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N3 := CFSG.pPrimeCore 3 ↥(S.H0 H) with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hTH : T ≤ H := hH.1.1
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  by_contra hall
  push Not at hall
  by_cases hPR : pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1
  · exact S.false_of_P_le_R1 h331 h311 hH hHZ hsolv hS3 hPR
  obtain ⟨p, hpP, hpR⟩ := IsConcreteLE.not_le_iff_exists.1 hPR
  have hpT : p ∈ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH) hpP.1
  have hpZ : ∀ z ∈ Zc, π ⟨p, hTI hpT⟩ * z * (π ⟨p, hTI hpT⟩)⁻¹ = z := by
    have hmem : π ⟨p, hTI hpT⟩ ∈ K ⊔ Zc := by
      rw [hc.sup_eq]
      exact S.map_oTwoUpper_le hpP.2
    obtain ⟨k, hk, z', hz', he⟩ := exists_mul_of_mem_sup_comm hc.comm hmem
    intro z hz
    rw [he]
    have h1 : k * z = z * k := hc.comm k hk z hz
    have h2 : z' * z = z * z' := comm_of_card_three hc.card_Zc hz' hz
    calc k * z' * z * (k * z')⁻¹ = k * (z' * z) * z'⁻¹ * k⁻¹ := by group
      _ = k * (z * z') * z'⁻¹ * k⁻¹ := by rw [h2]
      _ = k * z * k⁻¹ := by group
      _ = z := by rw [h1]; group
  have hTZ : ∀ (t : G) (ht : t ∈ T), ∀ z ∈ Zc, π ⟨t, hTI ht⟩ * z * (π ⟨t, hTI ht⟩)⁻¹ = z := by
    intro t ht z hz
    by_cases htR : t ∈ S.R1
    · exact hall ⟨t, hTI ht⟩ htR z hz
    · have htp := S.mul_inv_mem_R1 ht hpT htR hpR
      have htpT : t * p⁻¹ ∈ T := T.mul_mem ht (T.inv_mem hpT)
      have e : (⟨t, hTI ht⟩ : ↥(S.H0 H)) = ⟨t * p⁻¹, hTI htpT⟩ * ⟨p, hTI hpT⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul]
      have ha := hall ⟨t * p⁻¹, hTI htpT⟩ htp z hz
      calc π ⟨t * p⁻¹, hTI htpT⟩ * π ⟨p, hTI hpT⟩ * z *
            (π ⟨t * p⁻¹, hTI htpT⟩ * π ⟨p, hTI hpT⟩)⁻¹ =
          π ⟨t * p⁻¹, hTI htpT⟩ * (π ⟨p, hTI hpT⟩ * z * (π ⟨p, hTI hpT⟩)⁻¹) *
            (π ⟨t * p⁻¹, hTI htpT⟩)⁻¹ := by group
        _ = z := by rw [hpZ z hz, ha]
  have hTK : ∀ (t : G) (ht : t ∈ T), π ⟨t, hTI ht⟩ ∈ K := by
    intro t ht
    by_contra htK
    obtain ⟨y, hy, hne⟩ := (hc.outer _ (S.map_T_mem_inf hTH ht) htK).2.2 1 (Subgroup.one_mem _)
    apply hne
    rw [hTZ t ht y hy]
    group
  set Tb := (T.subgroupOf (S.H0 H)).map π with hTb
  have hTbK : Tb ≤ K := by
    rintro _ ⟨⟨t, htI⟩, ht, rfl⟩
    exact hTK t ht
  have hinf8 : Nat.card ↥(S.G1bar H ⊓ S.G2bar H) = 8 := by
    obtain ⟨e⟩ := hc.dihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hinf2 : IsPGroup 2 ↥(S.G1bar H ⊓ S.G2bar H) :=
    IsPGroup.of_card (n := 3) (by rw [hinf8]; norm_num)
  have hTb_le : Tb ≤ S.G1bar H ⊓ S.G2bar H := by
    rintro _ ⟨⟨t, htI⟩, ht, rfl⟩
    exact S.map_T_mem_inf hTH ht
  have hTb_eq : S.G1bar H ⊓ S.G2bar H = Tb := by
    set P := A4.toSylow (isSylowTwoOf_of_le S.h13.sylow hTI) with hP
    set P' := P.mapSurjective (QuotientGroup.mk'_surjective N3) with hP'
    have hP'coe : (P' : Subgroup (↥(S.H0 H) ⧸ N3)) = Tb := by
      rw [hP', Sylow.coe_mapSurjective, hP, A4.toSylow_coe]
    rw [← hP'coe]
    exact P'.is_maximal' hinf2 (hP'coe ▸ hTb_le)
  have hTb8 : Nat.card ↥Tb = 8 := by rw [← hTb_eq, hinf8]
  have hTb2 : IsPGroup 2 ↥Tb := hTb_eq ▸ hinf2
  have h4 := hc.card_two_le (Tb.subgroupOf K) (A4.isPGroup_subgroupOf_of_le hTbK hTb2)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTbK).toEquiv, hTb8] at h4
  omega

theorem map_L1_le_K {H : Subgroup G} (hTH : T ≤ H)
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc)
    {r : ↥(S.H0 H)} (hr : (r : G) ∈ S.R1) {z₀ : ↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)}
    (hz₀ : z₀ ∈ Zc) (hrz : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) r * z₀ *
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) r)⁻¹ ≠ z₀) {l : G} (hl : l ∈ S.L1) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))
      ⟨l, Subgroup.mem_sup_left (S.L1_le_borel_L hl)⟩ ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) with hπ
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have hrT : (r : G) ∈ T := S.R1_le_T hr
  have hlI : l ∈ S.H0 H := Subgroup.mem_sup_left (S.L1_le_borel_L hl)
  have hrK : π r ∉ K := fun h => hrz (by rw [hc.comm _ h z₀ hz₀]; group)
  have hrinf : π r ∈ S.G1bar H ⊓ S.G2bar H := S.map_T_mem_inf hTH hrT
  obtain ⟨⟨hrNK, -⟩, ⟨hrNZ, -⟩⟩ := hc.outer _ hrinf hrK
  set o : G := (r : G) * l * (r : G)⁻¹ * l⁻¹ with ho
  have hoR : o ∈ S.R1 := by
    have h1 : l * (r : G)⁻¹ * l⁻¹ ∈ S.R1 :=
      (Subgroup.mem_normalizer_iff.mp (S.L1T_le_normalizer_R1 (Subgroup.mem_sup_left hl)) _).mp
        (S.R1.inv_mem hr)
    have e : o = (r : G) * (l * (r : G)⁻¹ * l⁻¹) := by rw [ho]; group
    rw [e]
    exact S.R1.mul_mem hr h1
  have hoL : o ∈ S.L1 := by
    have h1 : (r : G) * l * (r : G)⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hrT) l).mp hl
    exact S.L1.mul_mem h1 (S.L1.inv_mem hl)
  have hoT : o ∈ T := S.R1_le_T hoR
  have hoK : π ⟨o, hTI hoT⟩ ∈ K := by
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨o, hoT⟩
    have hb' : π ⟨o, hTI hoT⟩ ^ 2 ^ b = 1 := by
      rw [← map_pow]
      have : (⟨o, hTI hoT⟩ : ↥(S.H0 H)) ^ 2 ^ b = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hb)
      rw [this, map_one]
    have hmem : π ⟨o, hTI hoT⟩ ∈ K ⊔ Zc := by
      rw [hc.sup_eq]
      exact S.map_L1_le hoL
    exact mem_of_mem_sup_of_two_pow hc.comm hc.card_Zc hc.inf_eq hmem hb'
  have hconj : π r * π ⟨l, hlI⟩ * (π r)⁻¹ = π ⟨o, hTI hoT⟩ * π ⟨l, hlI⟩ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ho]
    group
  have hlmem : π ⟨l, hlI⟩ ∈ K ⊔ Zc := by
    rw [hc.sup_eq]
    exact S.map_L1_le hl
  obtain ⟨k, hk, z, hz, hkz⟩ := exists_mul_of_mem_sup_comm hc.comm hlmem
  rw [hkz] at hconj ⊢
  have hk1 : π r * k * (π r)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hrNK k).mp hk
  have hz1 : π r * z * (π r)⁻¹ ∈ Zc := (Subgroup.mem_normalizer_iff.mp hrNZ z).mp hz
  have hzz : π r * z * (π r)⁻¹ = z := by
    have e : (π r * z * (π r)⁻¹) * z⁻¹ = (π r * k * (π r)⁻¹)⁻¹ * (π ⟨o, hTI hoT⟩ * k) := by
      have h2 : (π r * k * (π r)⁻¹) * (π r * z * (π r)⁻¹) = π ⟨o, hTI hoT⟩ * k * z :=
        calc (π r * k * (π r)⁻¹) * (π r * z * (π r)⁻¹) = π r * (k * z) * (π r)⁻¹ := by group
          _ = π ⟨o, hTI hoT⟩ * (k * z) := hconj
          _ = π ⟨o, hTI hoT⟩ * k * z := by group
      calc (π r * z * (π r)⁻¹) * z⁻¹ = (π r * k * (π r)⁻¹)⁻¹ *
            ((π r * k * (π r)⁻¹) * (π r * z * (π r)⁻¹)) * z⁻¹ := by group
        _ = (π r * k * (π r)⁻¹)⁻¹ * (π ⟨o, hTI hoT⟩ * k * z) * z⁻¹ := by rw [h2]
        _ = (π r * k * (π r)⁻¹)⁻¹ * (π ⟨o, hTI hoT⟩ * k) := by group
    have hmK : (π r * z * (π r)⁻¹) * z⁻¹ ∈ K := by
      rw [e]
      exact K.mul_mem (K.inv_mem hk1) (K.mul_mem hoK hk)
    have hmZ : (π r * z * (π r)⁻¹) * z⁻¹ ∈ Zc := Zc.mul_mem hz1 (Zc.inv_mem hz)
    have h0 : (π r * z * (π r)⁻¹) * z⁻¹ ∈ K ⊓ Zc := ⟨hmK, hmZ⟩
    rw [hc.inf_eq, Subgroup.mem_bot] at h0
    exact mul_inv_eq_one.mp h0
  by_cases hz1' : z = 1
  · rw [hz1', mul_one]
    exact hk
  · exact absurd (comm_of_comm_ne_one hc.card_Zc hz hz1' hzz z₀ hz₀) hrz

theorem L1_le_of_map {H : Subgroup G} (hN3s : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥(S.H0 H)))
    {L' : Subgroup ↥(S.H0 H)} (hL' : L' ∈ cComp (⊤ : Subgroup ↥(S.H0 H)))
    (hmap : ∀ (l : G) (hl : l ∈ S.L1), QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))
      ⟨l, Subgroup.mem_sup_left (S.L1_le_borel_L hl)⟩ ∈
        L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) :
    S.L1 ≤ L'.map (S.H0 H).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyL, m, hm, hym⟩
  have hyL1 : y ∈ S.L1 := Subgroup.subset_closure ⟨hyL, m, hm, hym⟩
  have hyI : y ∈ S.H0 H := Subgroup.mem_sup_left (S.L1_le_borel_L hyL1)
  have hy3 : y ^ 3 = 1 := by
    set y' : ↥(S.L1 ⊔ T) := ⟨y, Subgroup.mem_sup_left hyL1⟩ with hy'
    have hσ : S.phiL1T y' ^ 3 = 1 := by
      refine eq_one_of_pow_coprime (m := 2) (n := m) (perm3_cube_sq _) ?_
        (Nat.coprime_two_left.mpr hm)
      rw [← pow_mul, mul_comm, pow_mul, ← map_pow]
      have : y' ^ m = 1 := Subtype.ext (by simpa using hym)
      rw [this, map_one, one_pow]
    have hT : ((y' ^ 3 : ↥(S.L1 ⊔ T)) : G) ∈ T :=
      S.mem_T_of_phiL1T_eq_one _ (by rw [map_pow]; exact hσ)
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨_, hT⟩
    have hb' : (y ^ 3) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    exact eq_one_of_pow_coprime hb' hm' (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hm))
  have hk : (⟨y, hyI⟩ : ↥(S.H0 H)) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hy3)
  exact ⟨⟨y, hyI⟩, mem_of_pow_three_of_mem_map hN3s hL' hk (hmap y hyL1), rfl⟩

theorem le_centralizer_UH_of_normal {H : Subgroup G} {L' : Subgroup ↥(S.H0 H)} (hn : L'.Normal)
    (hZ : ⁅quasithinOmegaOneCenter T, L'.map (S.H0 H).subtype⁆ = ⊥) :
    L'.map (S.H0 H).subtype ≤ Subgroup.centralizer (S.UH H : Set G) := by
  have hZC : quasithinOmegaOneCenter T ≤
      Subgroup.centralizer (L'.map (S.H0 H).subtype : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZ
  rintro _ ⟨l, hl, rfl⟩
  have hUl : S.UH H ≤ Subgroup.centralizer {((l : ↥(S.H0 H)) : G)} := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, z, hz, rfl⟩
    have hhI : h ∈ S.H0 H := Subgroup.mem_sup_right hh
    have hl' : (⟨h, hhI⟩ : ↥(S.H0 H))⁻¹ * l * ((⟨h, hhI⟩ : ↥(S.H0 H))⁻¹)⁻¹ ∈ L' :=
      hn.conj_mem l hl _
    have hc := Subgroup.mem_centralizer_iff.mp (hZC hz) _ ⟨_, hl', rfl⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc h * z * h⁻¹ * (l : G) = h * (z * (h⁻¹ * l * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * l * h) * z) * h⁻¹ := by rw [hc]
      _ = (l : G) * (h * z * h⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact Subgroup.mem_centralizer_singleton_iff.mp (hUl hu)

end Setting

end CFSG.Quasithin.H13.A5
