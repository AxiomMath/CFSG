module

public import CFSG.Quasithin.H13.U3L14B56
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.FaithfulSimple.SectionAction
public import CFSG.Quasithin.EmptyFaithful.S152UGen2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev kAct (K : Subgroup G) :
    ↥(normalizer (K : Set G)) →* MulAut (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
  CFSG.SignalizerFunctorTheorem.sectionAction le_rfl
    (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)

omit [Finite G] in
theorem kAct_eq_one_iff {K : Subgroup G} (g : ↥(normalizer (K : Set G))) :
    kAct K g = 1 ↔ ∀ k ∈ K, k⁻¹ * (g * k * (g : G)⁻¹) ∈ pCoreOf 2 K := by
  have key := CFSG.SignalizerFunctorTheorem.sectionAction_mk_eq_iff (L := pCoreOf 2 K) le_rfl
    (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K) g
  constructor
  · intro h k hk
    exact (key ⟨k, hk⟩).1 (by rw [h]; rfl)
  · intro h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.one_apply]
      exact (key k).2 (h k k.2)

omit [Finite G] in
theorem not_le_pCoreOf_of_isQuasisimple {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) : ¬ K ≤ pCoreOf 2 K := by
  intro h
  have hsub : Subsingleton (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H k =>
      induction b using QuotientGroup.induction_on with
      | H l =>
        rw [QuotientGroup.eq, ← coe_mem_pCoreOf_iff]
        exact h (mul_mem (inv_mem k.2) l.2)
  have h2 := hq.2.toNontrivial
  have hsub2 : Subsingleton ((↥K ⧸ CFSG.Open.pCore 2 ↥K) ⧸
      center (↥K ⧸ CFSG.Open.pCore 2 ↥K)) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => rw [Subsingleton.elim a b]
  exact (not_nontrivial_iff_subsingleton.mpr hsub2) h2

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem le_of_normal {N : Subgroup G} (hN : N ≤ Lp) (hLpN : Lp ≤ normalizer (N : Set G))
    (h : ¬ N ≤ pCoreOf 2 Lp) : Lp ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 Lp with hQ
  have hQLp : Q ≤ Lp := LieType.BorelTits.pCoreOf_le 2 Lp
  have hQN : Q ≤ normalizer (N : Set G) := hQLp.trans hLpN
  have hsup : Lp ≤ N ⊔ Q := by
    have h1 := relIndex_mul_relIndex Q (N ⊔ Q) Lp le_sup_right (sup_le hN hQLp)
    rw [S.Lp3] at h1
    have h2 : Q.relIndex (N ⊔ Q) ≠ 1 := fun h2 =>
      h (le_sup_left.trans (relIndex_eq_one.mp h2))
    have h3 : Q.relIndex (N ⊔ Q) ∣ 3 := Dvd.intro _ h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h4 | h4
    · exact absurd h4 h2
    · rw [h4] at h1
      exact relIndex_eq_one.mp (by omega)
  rw [S.Lp_eq]
  refine (closure_le _).2 fun y hy => ?_
  obtain ⟨m, hm⟩ := pow_two_mem_of_sup hQN (LieType.BorelTits.pCoreOf_isPGroup 2 Lp)
    (hsup hy.1)
  have hcop : (2 ^ m).gcd (orderOf y) = 1 :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hy.2)
  exact zpowers_le.2 hm (mem_zpowers_pow_iff.2 hcop)

theorem mem_pCoreOf_of_kAct_eq_one {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) {y : G}
    (hy : y ∈ Lp) (h1 : kAct K ⟨y, hD.Lp_K hy⟩ = 1) : y ∈ pCoreOf 2 Lp := by
  set N : Subgroup G := Lp ⊓ (kAct K).ker.map (normalizer (K : Set G)).subtype with hN
  have hNLp : N ≤ Lp := inf_le_left
  have hmemN : ∀ z (hz : z ∈ Lp), kAct K ⟨z, hD.Lp_K hz⟩ = 1 → z ∈ N := fun z hz h =>
    mem_inf.mpr ⟨hz, ⟨⟨z, hD.Lp_K hz⟩, h, rfl⟩⟩
  have hNmem : ∀ z ∈ N, ∃ hz : z ∈ normalizer (K : Set G), kAct K ⟨z, hz⟩ = 1 := by
    rintro z ⟨-, w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  have hLpN : Lp ≤ normalizer (N : Set G) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨hzK, hz1⟩ := hNmem z hz
      refine hmemN _ (mul_mem (mul_mem hl (hNLp hz)) (inv_mem hl)) ?_
      have : (⟨l * z * l⁻¹, hD.Lp_K (mul_mem (mul_mem hl (hNLp hz)) (inv_mem hl))⟩ :
          ↥(normalizer (K : Set G))) = ⟨l, hD.Lp_K hl⟩ * ⟨z, hzK⟩ * ⟨l, hD.Lp_K hl⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, hz1, mul_one, map_inv, mul_inv_cancel]
    · intro hz
      obtain ⟨hzK, hz1⟩ := hNmem _ hz
      have hzLp : z ∈ Lp := by
        have := mul_mem (mul_mem (inv_mem hl) (hNLp hz)) hl
        simpa [mul_assoc] using this
      refine hmemN z hzLp ?_
      have : (⟨z, hD.Lp_K hzLp⟩ : ↥(normalizer (K : Set G))) =
          ⟨l, hD.Lp_K hl⟩⁻¹ * ⟨l * z * l⁻¹, hzK⟩ * ⟨l, hD.Lp_K hl⟩ := by
        apply Subtype.ext
        simp only [coe_mul, coe_inv]
        group
      rw [this, map_mul, map_mul, hz1, mul_one, map_inv, inv_mul_cancel]
  by_contra hyQ
  have hLpN' : Lp ≤ N := S.le_of_normal hNLp hLpN fun hle => hyQ (hle (hmemN y hy h1))
  have hKle : ⁅K, Lp⁆ ≤ pCoreOf 2 K := by
    rw [commutator_le]
    intro k hk l hl
    obtain ⟨hlK, hl1⟩ := hNmem l (hLpN' hl)
    have h2 := (kAct_eq_one_iff ⟨l, hlK⟩).1 hl1 k⁻¹ (inv_mem hk)
    rw [commutatorElement_def]
    simpa [mul_assoc] using h2
  rw [hD.eqLp] at hKle
  exact not_le_pCoreOf_of_isQuasisimple hD.quasi hKle

theorem kAct_ne_one {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) {x : G} (hx : x ∈ Lp)
    (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) : kAct K ⟨x, hD.Lp_K hx⟩ ≠ 1 := by
  intro h
  have hQ := S.mem_pCoreOf_of_kAct_eq_one hD hx h
  obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 Lp ⟨x, hQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxo)
  exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd))

theorem R1_le_T : pCoreOf 2 (Lp ⊔ T) ≤ T :=
  pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ Lp ⊔ T)).2.1
    (S.syl (le_sup_right : T ≤ Lp ⊔ T)).2.2

theorem pCoreOf_Lp_le_R1 : pCoreOf 2 Lp ≤ pCoreOf 2 (Lp ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 Lp).trans le_sup_left)
    (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 Lp)
      (S.T_Lp.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lp)))
    (LieType.BorelTits.pCoreOf_isPGroup 2 Lp)

theorem comm_R1_mem {r y : G} (hr : r ∈ pCoreOf 2 (Lp ⊔ T)) (hy : y ∈ Lp) :
    r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 Lp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR1T : pCoreOf 2 (Lp ⊔ T) ≤ T := S.R1_le_T
  have h1 : r * y * r⁻¹ * y⁻¹ ∈ Lp :=
    mul_mem ((mem_normalizer_iff.mp (S.T_Lp (hR1T hr)) y).mp hy) (inv_mem hy)
  have h2 : r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 (Lp ⊔ T) := by
    have h3 : y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 (Lp ⊔ T) :=
      (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 (Lp ⊔ T)
        (mem_sup_left hy)) _).mp (inv_mem hr)
    have : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
    rw [this]
    exact mul_mem hr h3
  have hle : Lp ⊓ pCoreOf 2 (Lp ⊔ T) ≤ pCoreOf 2 Lp :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => mem_normalizer_inf (le_normalizer hl)
        (LieType.BorelTits.le_normalizer_pCoreOf 2 (Lp ⊔ T) (mem_sup_left hl)))
      ((LieType.BorelTits.pCoreOf_isPGroup 2 (Lp ⊔ T)).to_le inf_le_right)
  exact hle (mem_inf.mpr ⟨h1, h2⟩)

theorem mem_R1_of_comm {t : G} (ht : t ∈ T)
    (h : ∀ y ∈ Lp, t * y * t⁻¹ * y⁻¹ ∈ pCoreOf 2 (Lp ⊔ T)) : t ∈ pCoreOf 2 (Lp ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (Lp ⊔ T) with hR
  have hRT : R ≤ T := S.R1_le_T
  by_contra htR
  have hTsup : T ≤ R ⊔ zpowers t := by
    have h1 := relIndex_mul_relIndex R (R ⊔ zpowers t) T le_sup_left
      (sup_le hRT (zpowers_le.2 ht))
    rw [S.index2] at h1
    have h2 : R.relIndex (R ⊔ zpowers t) ≠ 1 := fun h2 =>
      htR ((relIndex_eq_one.mp h2) (mem_sup_right (mem_zpowers t)))
    have h3 : R.relIndex (R ⊔ zpowers t) ∣ 2 := Dvd.intro _ h1
    rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h4 | h4
    · exact absurd h4 h2
    · rw [h4] at h1
      exact relIndex_eq_one.mp (by omega)
  have hRn : Lp ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hLpT : Lp ≤ normalizer (T : Set G) := by
    intro y hy
    have key : ∀ y ∈ Lp, T ≤ T.comap (MulAut.conj y).toMonoidHom := by
      intro y hy s hs
      have hs' := hTsup hs
      have hsub : R ⊔ zpowers t ≤ T.comap (MulAut.conj y).toMonoidHom := by
        refine sup_le (fun r hr => ?_) (zpowers_le.2 ?_)
        · show y * r * y⁻¹ ∈ T
          exact hRT ((mem_normalizer_iff.mp (hRn (mem_sup_left hy)) r).mp hr)
        · show y * t * y⁻¹ ∈ T
          have h1 := h y hy
          have h2 : y * t * y⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ * t := by group
          rw [h2]
          exact mul_mem (inv_mem (hRT h1)) ht
      exact hsub hs'
    rw [mem_normalizer_iff]
    intro s
    refine ⟨fun hs => key y hy hs, fun hs => ?_⟩
    have := key y⁻¹ (inv_mem hy) hs
    simpa [mul_assoc] using this
  have hTR : T ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right (sup_le hLpT le_normalizer)
      S.isP_T
  exact htR (hTR ht)

theorem inf_le_R1 {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K) :
    T ⊓ K ≤ pCoreOf 2 (Lp ⊔ T) := by
  have hKLp : K ⊓ Lp ≤ pCoreOf 2 Lp := by
    by_contra h
    refine hg ((S.le_of_normal inf_le_right (fun l hl => mem_normalizer_inf (hD.Lp_K hl)
      (le_normalizer hl)) h).trans inf_le_left)
  intro t ht
  obtain ⟨htT, htK⟩ := mem_inf.mp ht
  refine S.mem_R1_of_comm htT fun y hy => S.pCoreOf_Lp_le_R1 (hKLp (mem_inf.mpr ⟨?_, ?_⟩))
  · have h1 : y * t⁻¹ * y⁻¹ ∈ K := (mem_normalizer_iff.mp (hD.Lp_K hy) _).mp (inv_mem htK)
    have : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
    rw [this]
    exact mul_mem htK h1
  · exact mul_mem ((mem_normalizer_iff.mp (S.T_Lp htT) y).mp hy) (inv_mem hy)

theorem mem_R1_of_kAct_eq_one {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) {t : G} (ht : t ∈ T)
    (h1 : kAct K ⟨t, hD.T_K ht⟩ = 1) : t ∈ pCoreOf 2 (Lp ⊔ T) := by
  refine S.mem_R1_of_comm ht fun y hy => S.pCoreOf_Lp_le_R1 ?_
  have hc : t * y * t⁻¹ * y⁻¹ ∈ Lp :=
    mul_mem ((mem_normalizer_iff.mp (S.T_Lp ht) y).mp hy) (inv_mem hy)
  refine S.mem_pCoreOf_of_kAct_eq_one hD hc ?_
  have : (⟨t * y * t⁻¹ * y⁻¹, hD.Lp_K hc⟩ : ↥(normalizer (K : Set G))) =
      ⟨t, hD.T_K ht⟩ * ⟨y, hD.Lp_K hy⟩ * ⟨t, hD.T_K ht⟩⁻¹ * ⟨y, hD.Lp_K hy⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
  group

theorem pCoreOf_KT_le_R1 {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) :
    pCoreOf 2 (K ⊔ T) ≤ pCoreOf 2 (Lp ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 (K ⊔ T) ≤ T :=
    pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ K ⊔ T)).2.1
      (S.syl (le_sup_right : T ≤ K ⊔ T)).2.2
  have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
  have hKO : K ⊓ pCoreOf 2 (K ⊔ T) ≤ pCoreOf 2 K :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => mem_normalizer_inf (le_normalizer hk)
        (LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T) (mem_sup_left hk)))
      ((LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)).to_le inf_le_right)
  intro t ht
  refine S.mem_R1_of_kAct_eq_one hD (hOT ht) ((kAct_eq_one_iff _).2 fun k hk => hKO ?_)
  refine mem_inf.mpr ⟨?_, ?_⟩
  · exact mul_mem (inv_mem hk) ((mem_normalizer_iff.mp (hD.T_K (hOT ht)) k).mp hk)
  · have h1 : k⁻¹ * t * k ∈ pCoreOf 2 (K ⊔ T) := by
      have := (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)
        (mem_sup_left (inv_mem hk))) t).mp ht
      simpa using this
    have : k⁻¹ * (t * k * t⁻¹) = (k⁻¹ * t * k) * t⁻¹ := by group
    rw [this]
    exact mul_mem h1 (inv_mem ht)

theorem mem_normalizer_pCoreOf_KT {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) {x : G}
    (hx : x ∈ Lp) : x ∈ normalizer (pCoreOf 2 (K ⊔ T) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (Lp ⊔ T) with hR
  have hRT : R ≤ T := S.R1_le_T
  have hOR := S.pCoreOf_KT_le_R1 hD
  have hRn : Lp ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hKTn : K ⊔ T ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    sup_le (fun k hk => le_normalizer (mem_sup_left hk))
      (fun t ht => inf_normalizer_le_normalizer_sup K R ⟨hD.T_K ht, hRn (mem_sup_right ht)⟩)
  have hKRT : K ⊔ R ≤ K ⊔ T := sup_le le_sup_left (hRT.trans le_sup_right)
  have h1 : pCoreOf 2 (K ⊔ T) ≤ pCoreOf 2 (K ⊔ R) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOR.trans le_sup_right)
      (hKRT.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T))
  have h2 : pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 (K ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 (K ⊔ R)).trans hKRT)
      (hKTn.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ R)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R))
  rw [← le_antisymm h2 h1]
  exact LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ R)
    (inf_normalizer_le_normalizer_sup K R ⟨hD.Lp_K hx, hRn (mem_sup_left hx)⟩)

theorem mem_normalizer_inf_K {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    {x : G} (hx : x ∈ Lp) : x ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := K ⊓ pCoreOf 2 Lp with hE
  have hTKR := S.inf_le_R1 hD hg
  have hTKE : T ⊓ K ≤ normalizer (E : Set G) := fun t ht => mem_normalizer_inf
    (hD.T_K (mem_inf.mp ht).1)
    (S.T_Lp.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lp) (mem_inf.mp ht).1)
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_of_le_normalizer (S.syl (le_sup_right : T ≤ K ⊔ T)) le_sup_left
      (sup_le le_normalizer hD.T_K)
  have hP2 : IsPGroup 2 ↥((T ⊓ K) ⊔ E) :=
    IsPGroup.to_sup_of_normal_right' (S.isP_T.to_le inf_le_left)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 Lp).to_le inf_le_right) hTKE
  have hPeq : T ⊓ K = (T ⊓ K) ⊔ E :=
    F1.eq_of_isSylowTwoOf_le hsyl (sup_le inf_le_right inf_le_left) hP2 le_sup_left
  have hEle : E ≤ T ⊓ K := hPeq ▸ le_sup_right
  have key : ∀ y ∈ Lp, ∀ t ∈ T ⊓ K, y * t * y⁻¹ ∈ T ⊓ K := by
    intro y hy t ht
    have htK : t⁻¹ ∈ K := inv_mem (mem_inf.mp ht).2
    have hc : t⁻¹ * y * t⁻¹⁻¹ * y⁻¹ ∈ E := by
      refine mem_inf.mpr ⟨?_, S.comm_R1_mem (hTKR (inv_mem ht)) hy⟩
      have h1 : y * t⁻¹⁻¹ * y⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (hD.Lp_K hy) _).mp (inv_mem htK)
      have : t⁻¹ * y * t⁻¹⁻¹ * y⁻¹ = t⁻¹ * (y * t⁻¹⁻¹ * y⁻¹) := by group
      rw [this]
      exact mul_mem htK h1
    have : y * t * y⁻¹ = t * (t⁻¹ * y * t⁻¹⁻¹ * y⁻¹) := by group
    rw [this]
    exact mul_mem ht (hEle hc)
  rw [mem_normalizer_iff]
  intro t
  refine ⟨fun ht => key x hx t ht, fun ht => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ ht
  simpa [mul_assoc] using this

end Set14

end CFSG.Quasithin.H13.U3
