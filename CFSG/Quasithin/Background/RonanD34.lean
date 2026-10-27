module

public import CFSG.Quasithin.Background.F918P1
public import CFSG.Quasithin.Background.PGroupIrrTrivial
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A1cModuleHomog

public section

namespace CFSG.Quasithin.RonanD34

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {W : Type} [CommGroup W]

structure Core (M Mp T : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  exp : ∀ w : W, w ^ 2 = 1
  sylow : IsSylowTwoOf T M
  Mp_le : Mp ≤ M
  Mp_normal : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))
  irr : V ∈ IrrPlus Mp (⊤ : Subgroup W)
  o2inv : ∀ g ∈ pCoreOf 2 (Mp ⊔ T), ∀ v ∈ V, g v ∈ V
  gen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤

@[expose] def CaseI (M Mp T L : Subgroup (MulAut W)) : Prop :=
  L ∈ cComp M ∧ CFSG.IsQuasisimple ↥L ∧ Mp = conjClosure L T

@[expose] def CaseII (Mp T : Subgroup (MulAut W)) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ IsPGroup p ↥Mp ∧ (frattini ↥Mp).map Mp.subtype < Mp ∧
    ∀ N : Subgroup (MulAut W), N ≤ Mp → (frattini ↥Mp).map Mp.subtype ≤ N →
      (∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N) → N = (frattini ↥Mp).map Mp.subtype ∨ N = Mp

section Basic

variable {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem leStab_of_inv {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : X ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hu => ?_, fun hu => h g hg u hu⟩
  have := h g⁻¹ (X.inv_mem hg) (g u) hu
  simpa using this

theorem Core.T_le (h : Core M Mp T V) : T ≤ M := h.sylow.1

theorem Core.T_le_normalizer (h : Core M Mp T V) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := h.T_le.trans h.Mp_normal

theorem Core.T_isPGroup (h : Core M Mp T V) : IsPGroup 2 ↥T := h.sylow.2.1

theorem Core.sup_le_M (h : Core M Mp T V) : Mp ⊔ T ≤ M := sup_le h.Mp_le h.T_le

theorem Core.sup_le_normalizer (h : Core M Mp T V) :
    Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
  sup_le Subgroup.le_normalizer h.T_le_normalizer

theorem Core.inv_V (h : Core M Mp T V) : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V :=
  (mem_irrPlus_top_iff.mp h.irr).1

theorem Core.Mp_le_stabSub (h : Core M Mp T V) : Mp ≤ stabSub V := leStab_of_inv h.inv_V

theorem Core.Mp_le_stabSub_orbSup (h : Core M Mp T V) : Mp ≤ stabSub (orbSup T V) := by
  have key : ∀ x ∈ Mp, ∀ u ∈ orbSup T V, x u ∈ orbSup T V := by
    intro x hx u hu
    have hle : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hx' : s⁻¹ * x * s ∈ Mp :=
        (Subgroup.mem_normalizer_iff''.mp (h.T_le_normalizer hs) x).mp hx
      show x (s v) ∈ orbSup T V
      have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
      rw [h1]
      exact map_le_orbSup hs ⟨_, h.inv_V _ hx' v hv, rfl⟩
    exact hle hu
  exact leStab_of_inv key

theorem Core.sup_le_stabSub_orbSup (h : Core M Mp T V) : Mp ⊔ T ≤ stabSub (orbSup T V) :=
  sup_le h.Mp_le_stabSub_orbSup (le_stabSub_orbSup T V)

end Basic

section Coprime

variable {G : Type*} [Group G]

theorem commute_of_isPGroup_two {Y K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hY : IsPGroup 2 ↥Y) (hK : IsPGroup p ↥K)
    (hYn : Y ≤ Subgroup.normalizer (K : Set G)) (hKn : K ≤ Subgroup.normalizer (Y : Set G)) :
    ∀ y ∈ Y, ∀ m ∈ K, y * m = m * y := by
  intro y hy m hm
  have hcK : y * m * y⁻¹ * m⁻¹ ∈ K := by
    have h1 : y * m * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hYn hy) m).mp hm
    exact K.mul_mem h1 (K.inv_mem hm)
  have hcY : y * m * y⁻¹ * m⁻¹ ∈ Y := by
    have h1 : m * y⁻¹ * m⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hKn hm) y⁻¹).mp (Y.inv_mem hy)
    have h2 : y * (m * y⁻¹ * m⁻¹) ∈ Y := Y.mul_mem hy h1
    simpa [mul_assoc] using h2
  obtain ⟨a, ha⟩ := hY ⟨_, hcY⟩
  obtain ⟨b, hb⟩ := hK ⟨_, hcK⟩
  have ha' : (y * m * y⁻¹ * m⁻¹) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : (y * m * y⁻¹ * m⁻¹) ^ p ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hord : orderOf (y * m * y⁻¹ * m⁻¹) ∣ Nat.gcd (2 ^ a) (p ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
  calc y * m = (y * m * y⁻¹ * m⁻¹) * (m * y) := by group
    _ = m * y := by rw [hord, one_mul]

end Coprime

section Clause1

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem eq_bot_of_normal_two_group (h : Core M Mp T V) {Y : Subgroup (MulAut W)} (hYM : Y ≤ M)
    (hYn : M ≤ Subgroup.normalizer (Y : Set (MulAut W))) (hY2 : IsPGroup 2 ↥Y)
    (hYMp : ∀ y ∈ Y, ∀ m ∈ Mp, y * m = m * y) : Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := h.T_le
  have hYT : Y ≤ T := by
    have hS2 : IsPGroup 2 (T.subgroupOf M) :=
      h.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
    let P : Sylow 2 M := hS2.toSylow h.sylow.2.2
    have hnormal : (Y.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hYn
    have hY' : IsPGroup 2 (Y.subgroupOf M) := hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYM).symm
    have hle : Y.subgroupOf M ≤ (P : Subgroup M) := hY'.le_sylow_of_normal P
    intro x hx
    exact hle (show (⟨x, hYM hx⟩ : M) ∈ Y.subgroupOf M from hx)
  have hYO : Y ≤ pCoreOf 2 (Mp ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right)
      (h.sup_le_M.trans hYn) hY2
  have hYV : ∀ y ∈ Y, ∀ v ∈ V, y v ∈ V := fun y hy v hv => h.o2inv y (hYO hy) v hv
  have hY1 : ∀ y ∈ Y, ∀ v ∈ V, y v = v :=
    trivial_on_of_isPGroup_commute h.exp h.irr hY2 hYV hYMp
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hgen : (⨆ g ∈ M, V.map g.toMonoidHom) ≤
      (y : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hconj : g⁻¹ * y * g ∈ Y := (Subgroup.mem_normalizer_iff''.mp (hYn hg) y).mp hy
    have h1 := hY1 _ hconj v hv
    simp only [MulAut.mul_apply] at h1
    show y (g v) = g v
    calc y (g v) = g (g⁻¹ (y (g v))) := by simp
      _ = g v := by rw [h1]
  ext w
  have hw : w ∈ (⨆ g ∈ M, V.map g.toMonoidHom) := by rw [h.gen]; trivial
  exact hgen hw

theorem pCoreOf_eq_bot_of_caseII (h : Core M Mp T V) {p : ℕ} (hII : CaseII Mp T p) :
    pCoreOf 2 M = ⊥ := by
  obtain ⟨hp, hp2, hMp, -⟩ := hII
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hYn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hYM := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  refine eq_bot_of_normal_two_group h hYM hYn hY2 ?_
  exact commute_of_isPGroup_two hp hp2 hY2 hMp (fun y hy => h.Mp_normal (hYM hy))
    (fun m hm => hYn (h.Mp_le hm))

end Clause1

section Clause2

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem inf_centSub_inv {A X : Subgroup (MulAut W)} {U : Subgroup W}
    (hXA : X ≤ Subgroup.normalizer (A : Set (MulAut W))) (hXU : X ≤ stabSub U) :
    ∀ x ∈ X, ∀ k ∈ A ⊓ centSub U, x * k * x⁻¹ ∈ A ⊓ centSub U := by
  intro x hx k hk
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hXA hx) k).mp hk.1, fun w hw => ?_⟩
  have hw' : x⁻¹ w ∈ U := (hXU (X.inv_mem hx) w).mpr hw
  have h1 : k (x⁻¹ w) = x⁻¹ w := hk.2 _ hw'
  show x (k (x⁻¹ w)) = w
  rw [h1]
  simp

theorem Core.not_Mp_le_centSub (h : Core M Mp T V) : ¬ Mp ≤ centSub (orbSup T V) := by
  intro hle
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp h.irr
  apply hlt.not_ge
  intro v hv
  exact ⟨hv, fun m hm => hle hm v (le_orbSup T V hv)⟩

theorem normal_inf_centSub (h : Core M Mp T V) :
    ((Mp ⊓ centSub (orbSup T V)).subgroupOf Mp).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := inf_centSub_inv h.sup_le_normalizer h.sup_le_stabSub_orbSup (g : MulAut W)
    (le_sup_left (a := Mp) (b := T) g.2) _ hn
  simpa using this

theorem mem_normalizer_of_inv_conj {G : Type*} [Group G] {K : Subgroup G} {x : G}
    (h1 : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (h2 : ∀ k ∈ K, x⁻¹ * k * x ∈ K) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h1 k hk, fun hk => ?_⟩
  have := h2 _ hk
  simpa [mul_assoc] using this

theorem le_frattini_of_caseII (h : Core M Mp T V) {p : ℕ} (hII : CaseII Mp T p) :
    Mp ⊓ centSub (orbSup T V) ≤ (frattini ↥Mp).map Mp.subtype := by
  obtain ⟨-, -, -, -, hirrT⟩ := hII
  set K := Mp ⊓ centSub (orbSup T V) with hK
  set Φ := (frattini ↥Mp).map Mp.subtype with hΦ
  have hKMp : K ≤ Mp := inf_le_left
  have hΦMp : Φ ≤ Mp := Subgroup.map_subtype_le _
  have hKinv := inf_centSub_inv (A := Mp) h.sup_le_normalizer h.sup_le_stabSub_orbSup
  have hΦn : Subgroup.normalizer (Mp : Set (MulAut W)) ≤ Subgroup.normalizer (Φ : Set (MulAut W)) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (frattini ↥Mp)
  have hNinv : ∀ t ∈ T, ∀ x ∈ K ⊔ Φ, t * x * t⁻¹ ∈ K ⊔ Φ := by
    intro t ht
    have htK : t ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
      mem_normalizer_of_inv_conj (hKinv t (le_sup_right (a := Mp) (b := T) ht))
        (fun k hk => by
          have h1 := hKinv t⁻¹ (le_sup_right (a := Mp) (b := T) (T.inv_mem ht)) k hk
          rwa [inv_inv] at h1)
    have htΦ : t ∈ Subgroup.normalizer (Φ : Set (MulAut W)) := hΦn (h.T_le_normalizer ht)
    have := Subgroup.inf_normalizer_le_normalizer_sup K Φ ⟨htK, htΦ⟩
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp this x).mp hx
  rcases hirrT (K ⊔ Φ) (sup_le hKMp hΦMp) le_sup_right hNinv with hN | hN
  · exact le_sup_left.trans hN.le
  · exfalso
    have hK' : K.subgroupOf Mp ⊔ frattini ↥Mp = ⊤ := by
      apply Subgroup.map_injective Mp.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKMp, Subgroup.map_top,
        Subgroup.range_subtype]
      exact hN
    have hKtop := frattini_nongenerating hK'
    apply h.not_Mp_le_centSub
    intro x hx
    have : (⟨x, hx⟩ : ↥Mp) ∈ K.subgroupOf Mp := by rw [hKtop]; trivial
    exact (Subgroup.mem_subgroupOf.mp this).2

theorem commutator_central_mul_left {G : Type*} [Group G] {k : G} (hk : ∀ g, g * k = k * g)
    (a b : G) : ⁅k * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅k, b⁆ = 1 := (show Commute k b from (hk b).symm).commutator_eq
  rw [h1, mul_one, (hk _).symm, mul_inv_cancel_right]

theorem commutator_central_mul_right {G : Type*} [Group G] {k : G} (hk : ∀ g, g * k = k * g)
    (a b : G) : ⁅a, k * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅a, k⁆ = 1 := (show Commute a k from hk a).commutator_eq
  rw [h1, one_mul, (hk _).symm, mul_inv_cancel_right]

theorem central_le_frattini {G : Type*} [Group G] [Finite G]
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    {K : Subgroup G} (hK : K ≤ Subgroup.center G) : K ≤ frattini G := by
  have hKn : K.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.mp (hK hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  unfold frattini Order.radical
  refine le_iInf₂ fun H hH => ?_
  by_contra hKH
  have hlt : H < K ⊔ H := lt_of_le_of_ne le_sup_right (fun h' => hKH (le_sup_left.trans h'.ge))
  have htop : K ⊔ H = ⊤ := hH.2 _ hlt
  have hcomm : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ H := by
    rw [← htop]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨k₁, hk₁, h₁, hh₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    obtain ⟨k₂, hk₂, h₂, hh₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    rw [commutator_central_mul_left (Subgroup.mem_center_iff.mp (hK hk₁)),
      commutator_central_mul_right (Subgroup.mem_center_iff.mp (hK hk₂)), commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  rw [hperf] at hcomm
  exact hH.1 (top_le_iff.mp hcomm)

theorem isComponent_conjAutSub {M L X : Subgroup (MulAut W)} {t : MulAut W}
    (hL : L ∈ cComp M) (hq : CFSG.IsQuasisimple ↥L) (htM : t ∈ M) (hLX : conjAutSub t L ≤ X)
    (hXM : X ≤ M) : CFSG.IsComponent ((conjAutSub t L).subgroupOf X) := by
  have hcM : M.map (MulAut.conj t).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htM)
  have hLt : conjAutSub t L ∈ cComp M := by
    have := cComp_map_mulEquiv (MulAut.conj t) hL
    rwa [hcM] at this
  have hLtX : conjAutSub t L ∈ cComp X := cComp_mem_of_le hLt hLX hXM
  refine ⟨?_, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hLtX))⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (Subgroup.subgroupOfEquivOfLe hLX).symm) hq

theorem le_frattini_of_caseI (h : Core M Mp T V) {L : Subgroup (MulAut W)} (hI : CaseI M Mp T L) :
    Mp ⊓ centSub (orbSup T V) ≤ (frattini ↥Mp).map Mp.subtype := by
  obtain ⟨hL, hq, hMp⟩ := hI
  set K := Mp ⊓ centSub (orbSup T V) with hK
  have hKMp : K ≤ Mp := inf_le_left
  have hKinv := inf_centSub_inv (A := Mp) h.sup_le_normalizer h.sup_le_stabSub_orbSup
  have hTM : T ≤ M := h.T_le
  have hconjle : ∀ t ∈ T, conjAutSub t L ≤ Mp := by
    intro t ht
    rintro _ ⟨l, hl, rfl⟩
    rw [hMp]
    exact mem_conjClosure ht hl
  have hcomp : ∀ t ∈ T, CFSG.IsComponent ((conjAutSub t L).subgroupOf Mp) := fun t ht =>
    isComponent_conjAutSub hL hq (hTM ht) (hconjle t ht) h.Mp_le
  have hdich : ∀ t ∈ T, conjAutSub t L ≤ K ∨
      ∀ x ∈ conjAutSub t L, ∀ k ∈ K, k * x = x * k := by
    intro t ht
    rcases CFSG.LocalCores.component_normal_subgroup (hcomp t ht) (normal_inf_centSub h) with
      h1 | h1
    · left
      exact CFSG.LocalCores.le_of_subgroupOf_le (hconjle t ht) h1
    · right
      intro x hx k hk
      have hc := Subgroup.commutator_mem_commutator
        (show (⟨x, hconjle t ht hx⟩ : ↥Mp) ∈ (conjAutSub t L).subgroupOf Mp from hx)
        (show (⟨k, hKMp hk⟩ : ↥Mp) ∈ K.subgroupOf Mp from hk)
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact (congrArg Subtype.val hc).symm
  by_cases hex : ∃ t ∈ T, conjAutSub t L ≤ K
  · exfalso
    obtain ⟨t, ht, htK⟩ := hex
    apply h.not_Mp_le_centSub
    have hMpK : Mp ≤ K := by
      rw [hMp]
      refine conjClosure_le fun s hs z hz => ?_
      have h1 : t * z * t⁻¹ ∈ K := htK ⟨z, hz, rfl⟩
      have h2 := hKinv (s * t⁻¹) (le_sup_right (a := Mp) (b := T) (T.mul_mem hs (T.inv_mem ht)))
        _ h1
      have e : s * t⁻¹ * (t * z * t⁻¹) * (s * t⁻¹)⁻¹ = s * z * s⁻¹ := by group
      rwa [e] at h2
    exact hMpK.trans inf_le_right
  · push Not at hex
    have hcentr : ∀ k ∈ K, ∀ x ∈ Mp, k * x = x * k := by
      intro k hk
      have hle : Mp ≤ Subgroup.centralizer ({k} : Set (MulAut W)) := by
        rw [hMp]
        refine conjClosure_le fun s hs z hz => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rcases hdich s hs with h1 | h1
        · exact absurd h1 (hex s hs)
        · exact h1 (s * z * s⁻¹) ⟨z, hz, rfl⟩ g hk
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp (hle hx) k rfl
    have hperf : ⁅(⊤ : Subgroup ↥Mp), (⊤ : Subgroup ↥Mp)⁆ = ⊤ := by
      apply Subgroup.map_injective Mp.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hMp]
      exact A3.conjClosure_perfect (perfect_of_mem_cComp hL)
    have hcenter : K.subgroupOf Mp ≤ Subgroup.center ↥Mp := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcentr x hx g g.2).symm
    have := central_le_frattini hperf hcenter
    calc K = (K.subgroupOf Mp).map Mp.subtype := (Subgroup.map_subgroupOf_eq_of_le hKMp).symm
      _ ≤ (frattini ↥Mp).map Mp.subtype := Subgroup.map_mono this

end Clause2

section Burnside

theorem eq_of_trivial_mod_frattini {K : Type*} [Group K] [Finite K]
    (hodd : Odd (Nat.card (frattini K))) (σ : K ≃* K) {n : ℕ}
    (hσ : ∀ y : K, (σ : K → K)^[2 ^ n] y = y)
    (htriv : ∀ y : K, σ y * y⁻¹ ∈ frattini K) (y : K) : σ y = y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let F : Subgroup K := MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id K)
  have hσN : ∀ z ∈ frattini K, σ z ∈ frattini K := by
    intro z hz
    have := Subgroup.characteristic_iff_map_eq.mp (inferInstance : (frattini K).Characteristic) σ
    rw [← this]
    exact Subgroup.mem_map_of_mem σ.toMonoidHom hz
  have hsup : F ⊔ frattini K = ⊤ := by
    rw [eq_top_iff]
    intro y _
    let S : Type _ := {z : K // y⁻¹ * z ∈ frattini K}
    have hSmem : ∀ z : S, y⁻¹ * σ z.1 ∈ frattini K := by
      intro z
      have h1 : y⁻¹ * σ z.1 = (y⁻¹ * (σ y * y⁻¹) * y) * σ (y⁻¹ * z.1) := by
        simp only [map_mul, map_inv]
        group
      rw [h1]
      refine (frattini K).mul_mem ?_ (hσN _ z.2)
      have := (inferInstance : (frattini K).Normal).conj_mem _ (htriv y) y⁻¹
      simpa using this
    let g : Function.End S := fun z => ⟨σ z.1, hSmem z⟩
    have hgit : ∀ (m : ℕ) (z : S), ((g ^ m) z).1 = (σ : K → K)^[m] z.1 := by
      intro m
      induction m with
      | zero => intro z; rfl
      | succ m ih =>
        intro z
        have h1 : (g ^ (m + 1)) z = (g ^ m) (g z) := rfl
        rw [h1, ih, Function.iterate_succ_apply]
    have hg : g ^ 2 ^ n = 1 := by
      funext z
      exact Subtype.ext (by rw [hgit]; exact hσ z.1)
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) hg
    let e : S ≃ frattini K :=
      { toFun := fun z => ⟨y⁻¹ * z.1, z.2⟩
        invFun := fun w => ⟨y * w.1, by simpa using w.2⟩
        left_inv := fun z => by ext; simp
        right_inv := fun w => by ext; simp }
    have hcard : Fintype.card S = Nat.card (frattini K) := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_congr e
    have hpos : 0 < Fintype.card (Function.fixedPoints g) := by
      have h1 : Fintype.card (Function.fixedPoints g) % 2 = 1 := by
        have h2 := hmod
        rw [hcard] at h2
        have h3 : Nat.card (frattini K) % 2 = 1 := Nat.odd_iff.mp hodd
        have h4 : Nat.card (frattini K) % 2 = Fintype.card (Function.fixedPoints g) % 2 := h2
        omega
      omega
    obtain ⟨⟨z, hz⟩⟩ := Fintype.card_pos_iff.mp hpos
    have hσz : σ z.1 = z.1 := by
      have := congrArg Subtype.val hz
      exact this
    have hzF : z.1 ∈ F := hσz
    have : y = z.1 * (y⁻¹ * z.1)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hzF ((frattini K).inv_mem z.2)
  have hF : F = ⊤ := frattini_nongenerating (K := F) (by rw [hsup])
  have hyF : y ∈ F := by rw [hF]; exact Subgroup.mem_top y
  exact hyF

theorem commute_of_comm_mod_frattini {G : Type*} [Group G] [Finite G] {Mp : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hMp : IsPGroup p ↥Mp) {y : G}
    (hyn : y ∈ Subgroup.normalizer (Mp : Set G)) {k : ℕ} (hyk : y ^ 2 ^ k = 1)
    (hy : ∀ g ∈ Mp, y * g * y⁻¹ * g⁻¹ ∈ (frattini ↥Mp).map Mp.subtype) :
    ∀ g ∈ Mp, y * g = g * y := by
  classical
  let σ : ↥Mp ≃* ↥Mp := Mp.normalizerMonoidHom ⟨y, hyn⟩
  have hσ : ∀ x : ↥Mp, ((σ x : ↥Mp) : G) = y * x * y⁻¹ := fun x =>
    Mp.normalizerMonoidHom_apply_apply_coe ⟨y, hyn⟩ x
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card (frattini ↥Mp)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hMp.to_subgroup (frattini ↥Mp))
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hit : ∀ (n : ℕ) (x : ↥Mp),
      (((σ : ↥Mp → ↥Mp)^[n] x : ↥Mp) : G) = y ^ n * x * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', hσ, ih]
      group
  have hσ1 : ∀ x : ↥Mp, (σ : ↥Mp → ↥Mp)^[2 ^ k] x = x := by
    intro x
    apply Subtype.ext
    rw [hit, hyk]
    simp
  have htriv : ∀ x : ↥Mp, σ x * x⁻¹ ∈ frattini ↥Mp := by
    intro x
    obtain ⟨z, hz, hzx⟩ := hy x x.2
    have : σ x * x⁻¹ = z := by
      apply Subtype.ext
      have h1 : ((σ x * x⁻¹ : ↥Mp) : G) = y * (x : G) * y⁻¹ * (x : G)⁻¹ := by
        simp [hσ]
      rw [h1]
      exact hzx.symm
    rw [this]
    exact hz
  intro g hg
  have := eq_of_trivial_mod_frattini hodd σ hσ1 htriv ⟨g, hg⟩
  have h2 := congrArg Subtype.val this
  simp only [hσ] at h2
  calc y * g = (y * g * y⁻¹) * y := by group
    _ = g * y := by rw [h2]

end Burnside

section Helpers

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {S Y : Subgroup G}
    (h : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) : S ≤ Subgroup.normalizer (Y : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h s hs y hy, fun hy => ?_⟩
  have h2 := h s⁻¹ (S.inv_mem hs) _ hy
  have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rwa [e] at h2

theorem eq_bot_of_perfect_of_isPGroup [Finite G] {Q : Subgroup G} (hq : ⁅Q, Q⁆ = Q)
    (hQ : IsPGroup 2 ↥Q) : Q = ⊥ := by
  by_contra hne
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  haveI : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hq
  exact Group.IsPerfect.not_isNilpotent _ hQ.isNilpotent

end Helpers

section PointwiseSmul

open scoped Pointwise

theorem smul_eq_map (t : MulAut W) (S : Subgroup W) : t • S = S.map t.toMonoidHom := by
  ext w
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro hw
    exact ⟨t⁻¹ • w, hw, by simp [MulAut.smul_def]⟩
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def] using hs

end PointwiseSmul

section AutSubLemmas

variable {Mp T : Subgroup (MulAut W)} {U : Subgroup W}

theorem mul_pow_mem_of_normalizes {G : Type*} [Group G] {K : Subgroup G} {k σ : G} (hk : k ∈ K)
    (hσ : σ ∈ Subgroup.normalizer (K : Set G)) (n : ℕ) : ∃ k' ∈ K, (k * σ) ^ n = k' * σ ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', hn⟩ := ih
    have hσn : σ ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hσ n
    have hc : σ ^ n * k * (σ ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hσn k).mp hk
    refine ⟨k' * (σ ^ n * k * (σ ^ n)⁻¹), K.mul_mem hk' hc, ?_⟩
    rw [pow_succ, hn]
    group

theorem autSub_conj_mem {Y L : Subgroup (MulAut W)}
    (hN : Y ⊓ stabSub U ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ x ∈ autSub Y U, ∀ k ∈ autSub L U, x * k * x⁻¹ ∈ autSub L U := by
  intro x hx k hk
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hk
  have hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hN ⟨hg, g.2⟩
  refine mem_autSub.mpr ⟨g * l * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hgN (l : MulAut W)).mp hl

theorem isPGroup_autSub {p : ℕ} {A : Subgroup (MulAut W)} (hA : A ≤ stabSub U)
    (hp : IsPGroup p ↥A) : IsPGroup p ↥(autSub A U) :=
  (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm).map (resHom U)

theorem autSub_normal (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W))) :
    ∀ x ∈ autSub (Mp ⊔ T) U, ∀ k ∈ autSub Mp U, x * k * x⁻¹ ∈ autSub Mp U :=
  autSub_conj_mem (Y := Mp ⊔ T) (L := Mp) (U := U)
    (fun g hg => (sup_le Subgroup.le_normalizer hTn) hg.1)

theorem normal_autSub_subgroupOf (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W))) :
    ((autSub Mp U).subgroupOf (autSub (Mp ⊔ T) U)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using autSub_normal hTn _ g.2 _ hn

theorem exists_pow_mem_autSub (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hT2 : IsPGroup 2 ↥T) (hMpU : Mp ≤ stabSub U) :
    ∀ y ∈ autSub (Mp ⊔ T) U, ∃ e : ℕ, y ^ 2 ^ e ∈ autSub Mp U := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
  have hg' : (g : MulAut W) ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hg'
  obtain ⟨m, hm, s, hs, hms⟩ := hg'
  have hmU : m ∈ stabSub U := hMpU hm
  have hsU : s ∈ stabSub U := by
    have h1 : s = m⁻¹ * (g : MulAut W) := by rw [← hms]; group
    rw [h1]
    exact (stabSub U).mul_mem ((stabSub U).inv_mem hmU) g.2
  have hsX : resHom U ⟨s, hsU⟩ ∈ autSub (Mp ⊔ T) U :=
    mem_autSub.mpr ⟨⟨s, hsU⟩, Subgroup.mem_sup_right hs, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, s ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hT2 ⟨s, hs⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hσe : (resHom U ⟨s, hsU⟩) ^ 2 ^ e = 1 := by
    rw [← map_pow, show (⟨s, hsU⟩ : ↥(stabSub U)) ^ 2 ^ e = 1 from Subtype.ext (by simpa using he),
      map_one]
  have hσN : resHom U ⟨s, hsU⟩ ∈ Subgroup.normalizer
      ((autSub Mp U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact autSub_normal hTn _ hsX k hk
    · intro hk
      have h2 := autSub_normal hTn _ ((autSub (Mp ⊔ T) U).inv_mem hsX) _ hk
      have e2 : (resHom U ⟨s, hsU⟩)⁻¹ * (resHom U ⟨s, hsU⟩ * k * (resHom U ⟨s, hsU⟩)⁻¹) *
          ((resHom U ⟨s, hsU⟩)⁻¹)⁻¹ = k := by group
      rw [e2] at h2
      exact h2
  have hκ : resHom U ⟨m, hmU⟩ ∈ autSub Mp U := mem_autSub.mpr ⟨⟨m, hmU⟩, hm, rfl⟩
  have hgms : g = ⟨m, hmU⟩ * ⟨s, hsU⟩ := Subtype.ext hms.symm
  obtain ⟨k', hk', hpow⟩ := mul_pow_mem_of_normalizes hκ hσN (2 ^ e)
  refine ⟨e, ?_⟩
  rw [hgms, map_mul, hpow, hσe, mul_one]
  exact hk'

end AutSubLemmas

section Clause1b

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem pCoreOf_autSub_orbSup_eq_bot_of_cent (h : Core M Mp T V)
    (hcent : ∀ (s : MulAut W) (hs : s ∈ T),
      resHom (orbSup T V) ⟨s, le_stabSub_orbSup T V hs⟩ ∈
        pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) → ∀ m ∈ Mp, s * m = m * s) :
    pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := h.T_le
  have hTX : T ≤ Mp ⊔ T := le_sup_right
  have hXM : Mp ⊔ T ≤ M := h.sup_le_M
  have hXs : Mp ⊔ T ≤ stabSub (orbSup T V) := h.sup_le_stabSub_orbSup
  let ρ : ↥(Mp ⊔ T) →* MulAut ↥(orbSup T V) :=
    (resHom (orbSup T V)).comp (Subgroup.inclusion hXs)
  have hrange : autSub (Mp ⊔ T) (orbSup T V) = ρ.range := by
    ext φ
    rw [mem_autSub, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXs x.2⟩, x.2, rfl⟩
  have hY2 : IsPGroup 2 (pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYn : autSub (Mp ⊔ T) (orbSup T V) ≤
      Subgroup.normalizer (pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) : Set (MulAut ↥(orbSup T V))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  let Yt : Subgroup ↥(Mp ⊔ T) := (pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V))).comap ρ
  have hYtn : Yt.Normal := by
    refine ⟨fun y hy g => ?_⟩
    have hg : ρ g ∈ autSub (Mp ⊔ T) (orbSup T V) := by rw [hrange]; exact ⟨g, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hYn hg) _).mp hy
  let P : Subgroup (MulAut W) := Yt.map (Mp ⊔ T).subtype ⊓ T
  have hPT : P ≤ T := inf_le_right
  have hPX : P ≤ Mp ⊔ T := hPT.trans hTX
  have hP2 : IsPGroup 2 P := h.sylow.2.1.to_le hPT
  have hPMp : ∀ p ∈ P, ∀ m ∈ Mp, p * m = m * p := by
    rintro _ ⟨⟨y, hy, rfl⟩, hyT⟩ m hm
    exact hcent y hyT hy m hm
  have hPn : Mp ⊔ T ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
    refine sup_le ?_ ?_
    · refine le_normalizer_of_forall_conj_mem fun m hm p hp => ?_
      rw [← hPMp p hp m hm, mul_inv_cancel_right]
      exact hp
    · refine le_normalizer_of_forall_conj_mem fun s hs p hp => ?_
      obtain ⟨hp1, hp2⟩ := Subgroup.mem_inf.mp hp
      obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.mp hp1
      have h1 : (⟨s, hTX hs⟩ * y * ⟨s, hTX hs⟩⁻¹ : ↥(Mp ⊔ T)) ∈ Yt := hYtn.conj_mem y hy _
      have h2 : (Mp ⊔ T).subtype (⟨s, hTX hs⟩ * y * ⟨s, hTX hs⟩⁻¹) = s * p * s⁻¹ := by
        rw [← hyp]
        rfl
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨_, h1, h2⟩,
        T.mul_mem (T.mul_mem hs hp2) (T.inv_mem hs)⟩
  have hPO : P ≤ pCoreOf 2 (Mp ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPX hPn hP2
  have hP1 : ∀ p ∈ P, ∀ v ∈ V, p v = v :=
    trivial_on_of_isPGroup_commute h.exp h.irr hP2 (fun p hp v hv => h.o2inv p (hPO hp) v hv)
      hPMp
  have hPT1 : ∀ p ∈ P, ∀ w ∈ orbSup T V, p w = w := by
    intro p hp w hw
    have hgen : orbSup T V ≤ (p : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
      refine orbSup_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hconj : s⁻¹ * p * s ∈ P :=
        (Subgroup.mem_normalizer_iff''.mp (hPn (hTX hs)) p).mp hp
      have h1 := hP1 _ hconj v hv
      simp only [MulAut.mul_apply] at h1
      show p (s v) = s v
      calc p (s v) = s (s⁻¹ (p (s v))) := by simp
        _ = s v := by rw [h1]
    exact hgen hw
  have hodd : ¬ 2 ∣ (T.subgroupOf (Mp ⊔ T)).index := fun hd => h.sylow.2.2 (by
    have e := Subgroup.relIndex_mul_relIndex T (Mp ⊔ T) M hTX hXM
    have h' : 2 ∣ T.relIndex M := e ▸ hd.mul_right _
    exact h')
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hQ2 : IsPGroup 2 ((T.subgroupOf (Mp ⊔ T)).map ρ.rangeRestrict) :=
    (h.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm).map ρ.rangeRestrict
  have hQi : ¬ 2 ∣ ((T.subgroupOf (Mp ⊔ T)).map ρ.rangeRestrict).index := fun hd =>
    hodd (hd.trans (Subgroup.index_map_dvd _ hsurj))
  have hNn : (Yt.map ρ.rangeRestrict).Normal := hYtn.map ρ.rangeRestrict hsurj
  have hN2 : IsPGroup 2 (Yt.map ρ.rangeRestrict) :=
    (hY2.comap_of_injective ρ.range.subtype ρ.range.subtype_injective).to_le (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx)
  have hNQ : Yt.map ρ.rangeRestrict ≤ (hQ2.toSylow hQi : Subgroup ↥ρ.range) :=
    hN2.le_sylow_of_normal (hQ2.toSylow hQi)
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  have hφG : φ ∈ ρ.range := hrange ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _ hφ
  obtain ⟨x, rfl⟩ := hφG
  have hx : x ∈ Yt := hφ
  have hmem : ρ.rangeRestrict x ∈ (T.subgroupOf (Mp ⊔ T)).map ρ.rangeRestrict :=
    hNQ ⟨x, hx, rfl⟩
  obtain ⟨s, hsT, hsx⟩ := hmem
  have hsx' : ρ s = ρ x := congrArg Subtype.val hsx
  have hsY : s ∈ Yt := by
    show ρ s ∈ pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V))
    rw [hsx']
    exact hφ
  have hsP : (s : MulAut W) ∈ P := ⟨⟨s, hsY, rfl⟩, hsT⟩
  rw [← hsx']
  ext u
  exact hPT1 _ hsP u u.2

end Clause1b

section SemisimpleHomog

open scoped Pointwise

section Abstract

variable {A : Type*} [Group A] {T : Type*} [Group T] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction A Q] [MulDistribMulAction T Q]

theorem isIrr_smul_of_normalizes (h : XMod.Normalizes A T Q) (t : T) {L : Subgroup Q}
    (hL : XMod.IsIrr A L) : XMod.IsIrr A (t • L) := by
  refine ⟨XMod.isInv_smul_of_normalizes h t hL.1, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    have h1 : L = ⊥ := by
      have := congrArg (fun J => t⁻¹ • J) h0
      simpa [smul_smul, Subgroup.smul_bot] using this
    exact hL.2.1.ne' h1
  · intro J hJ _ hJL
    have hJ' : XMod.IsInv A (t⁻¹ • J) := XMod.isInv_smul_of_normalizes h t⁻¹ hJ
    have hle : t⁻¹ • J ≤ L := by
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t⁻¹)).2 hJL
      simpa [inv_smul_smul] using this
    have hJeq : J = t • (t⁻¹ • J) := by rw [smul_inv_smul]
    rcases hL.2.2 (t⁻¹ • J) hJ' bot_le hle with h1 | h1
    · left
      rw [hJeq, h1, Subgroup.smul_bot]
    · right
      rw [hJeq, h1]

theorem smul_iSup_subgroup {ι : Sort*} (g : T) (R : ι → Subgroup Q) :
    g • (⨆ i, R i) = ⨆ i, g • R i := by
  have h : ∀ K : Subgroup Q, g • K = K.map (MulDistribMulAction.toMonoidHom Q g) := fun K => rfl
  rw [h, Subgroup.map_iSup]
  exact iSup_congr fun i => (h (R i)).symm

theorem smul_iSup_smul (r : T) (L : Subgroup Q) : r • (⨆ t : T, t • L) = ⨆ t : T, t • L := by
  rw [smul_iSup_subgroup]
  simp_rw [smul_smul]
  exact (Equiv.mulLeft r).iSup_comp (g := fun t : T => t • L)

theorem exists_iso_smul_of_le_orbit (h : XMod.Normalizes A T Q) {S J : Subgroup Q}
    (hS : XMod.IsIrr A S) (hJ : XMod.IsIrr A J) (hle : J ≤ ⨆ t : T, t • S) :
    ∃ t : T, XMod.Iso A J (t • S) := by
  have hinv : ∀ t : T, XMod.IsInv A (t • S) := fun t => XMod.isInv_smul_of_normalizes h t hS.1
  have hP : XMod.IsInv A (⨆ t : T, t • S) := XMod.isInv_iSup hinv
  have h1 : XMod.toSubmod hJ.1 ≤ ⨆ t : T, XMod.toSubmod (hinv t) := by
    rw [← XMod.toSubmod_iSup hinv]
    exact (XMod.toSubmod_le_iff (hL := hJ.1) (hL' := hP)).2 hle
  rw [← sSup_range] at h1
  have hsimple : ∀ m : ↥(Set.range fun t : T => XMod.toSubmod (hinv t)),
      IsSimpleModule ↥(XMod.opRing A Q) ↥(m : Submodule ↥(XMod.opRing A Q) (Additive Q)) := by
    rintro ⟨_, t, rfl⟩
    exact (XMod.isIrr_iff (hinv t)).1 (isIrr_smul_of_normalizes h t hS)
  have hVs : IsSimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod hJ.1) :=
    (XMod.isIrr_iff hJ.1).1 hJ
  obtain ⟨S', ⟨t, rfl⟩, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup (XMod.toSubmod hJ.1) _ h1
  exact ⟨t, (XMod.iso_iff hJ.1 (hinv t)).2 ⟨e⟩⟩

theorem exists_isCompl_iSup_smul (h : XMod.Normalizes A T Q) {L : Subgroup Q}
    (hL : XMod.IsIrr A L) {J : Subgroup Q} (hJ : XMod.IsInv A J) (hJle : J ≤ ⨆ t : T, t • L) :
    ∃ J' : Subgroup Q, J' ≤ ⨆ t : T, t • L ∧ XMod.IsInv A J' ∧ J ⊓ J' = ⊥ ∧
      J ⊔ J' = ⨆ t : T, t • L := by
  have hinv : ∀ t : T, XMod.IsInv A (t • L) := fun t => XMod.isInv_smul_of_normalizes h t hL.1
  have hM : XMod.IsInv A (⨆ t : T, t • L) := XMod.isInv_iSup hinv
  have hsimple : ∀ t : T, IsSimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod (hinv t)) :=
    fun t => (XMod.isIrr_iff (hinv t)).1 (isIrr_smul_of_normalizes h t hL)
  have hss : IsSemisimpleModule ↥(XMod.opRing A Q) ↥(⨆ t : T, XMod.toSubmod (hinv t)) := by
    have := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (s := Set.univ)
      (p := fun t : T => XMod.toSubmod (hinv t)) (fun t _ => haveI := hsimple t; inferInstance)
    rw [iSup_univ] at this
    exact this
  have hss' : IsSemisimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod hM) := by
    rw [XMod.toSubmod_iSup hinv]
    exact hss
  have hcompl : ComplementedLattice (Set.Iic (XMod.toSubmod hM)) :=
    (XMod.toSubmod hM).mapIic.complementedLattice_iff.1 inferInstance
  obtain ⟨c, hcN, hdisj, hsup⟩ := Set.Iic.complementedLattice_iff.1 hcompl (XMod.toSubmod hJ)
    ((XMod.toSubmod_le_iff (hL := hJ) (hL' := hM)).2 hJle)
  have hJ'le : XMod.ofSubmod c ≤ ⨆ t : T, t • L := fun q hq => hcN hq
  refine ⟨XMod.ofSubmod c, hJ'le, XMod.isInv_ofSubmod c, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro q hq
    have h1 : Additive.ofMul q ∈ XMod.toSubmod hJ ⊓ c := ⟨hq.1, hq.2⟩
    rw [hdisj, Submodule.mem_bot] at h1
    exact h1
  · refine le_antisymm (sup_le hJle hJ'le) fun q hq => ?_
    have h1 : Additive.ofMul q ∈ XMod.toSubmod hJ ⊔ c := by rw [hsup]; exact hq
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    have hq' : q = Additive.toMul x * Additive.toMul y := (congrArg Additive.toMul hxy).symm
    rw [hq']
    exact Subgroup.mul_mem_sup hx hy

@[expose] def isotypicSum (A : Type*) [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]
    (M L : Subgroup Q) : Subgroup Q :=
  ⨆ I' ∈ {I' : Subgroup Q | I' ≤ M ∧ XMod.IsIrr A I' ∧ XMod.Iso A I' L}, I'

theorem isotypicSum_congr {M L₁ L₂ : Subgroup Q} (hL₁ : XMod.IsInv A L₁) (h : XMod.Iso A L₁ L₂) :
    isotypicSum A M L₁ = isotypicSum A M L₂ := by
  have hset : {I' : Subgroup Q | I' ≤ M ∧ XMod.IsIrr A I' ∧ XMod.Iso A I' L₁} =
      {I' : Subgroup Q | I' ≤ M ∧ XMod.IsIrr A I' ∧ XMod.Iso A I' L₂} := by
    ext I'
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.trans h⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.trans (XMod.Iso.symm hL₁ h)⟩
  unfold isotypicSum
  rw [hset]

theorem smul_isotypicSum (h : XMod.Normalizes A T Q) (r : T) {M : Subgroup Q} (hM : r • M = M)
    (L : Subgroup Q) : r • isotypicSum A M L = isotypicSum A M (r • L) := by
  have hM' : r⁻¹ • M = M := (congrArg (fun K => r⁻¹ • K) hM).symm.trans (inv_smul_smul r M)
  unfold isotypicSum
  simp_rw [smul_iSup_subgroup]
  apply le_antisymm
  · refine iSup₂_le fun I' hI' => ?_
    refine le_iSup₂_of_le (r • I')
      ⟨?_, isIrr_smul_of_normalizes h r hI'.2.1, XMod.iso_smul h r hI'.2.2⟩ le_rfl
    have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := r)).2 hI'.1
    rwa [hM] at this
  · refine iSup₂_le fun I'' hI'' => ?_
    have hmem : r⁻¹ • I'' ∈ {I' : Subgroup Q | I' ≤ M ∧ XMod.IsIrr A I' ∧ XMod.Iso A I' L} := by
      refine ⟨?_, isIrr_smul_of_normalizes h r⁻¹ hI''.2.1, ?_⟩
      · have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := r⁻¹)).2 hI''.1
        rwa [hM'] at this
      · have := XMod.iso_smul h r⁻¹ hI''.2.2
        rwa [inv_smul_smul] at this
    exact le_iSup₂_of_le (r⁻¹ • I'') hmem (by rw [smul_inv_smul])

theorem exists_smul_isotypicSum_eq (h : XMod.Normalizes A T Q) {L L₁ L₂ : Subgroup Q}
    (hL : XMod.IsIrr A L) (hL₁ : XMod.IsIrr A L₁) (hL₂ : XMod.IsIrr A L₂)
    (h₁ : L₁ ≤ ⨆ t : T, t • L) (h₂ : L₂ ≤ ⨆ t : T, t • L) :
    ∃ r : T, r • isotypicSum A (⨆ t : T, t • L) L₁ = isotypicSum A (⨆ t : T, t • L) L₂ := by
  obtain ⟨t₁, ht₁⟩ := exists_iso_smul_of_le_orbit h hL hL₁ h₁
  obtain ⟨t₂, ht₂⟩ := exists_iso_smul_of_le_orbit h hL hL₂ h₂
  refine ⟨t₂ * t₁⁻¹, ?_⟩
  rw [isotypicSum_congr hL₁.1 ht₁, isotypicSum_congr hL₂.1 ht₂,
    smul_isotypicSum h _ (smul_iSup_smul _ L), smul_smul, inv_mul_cancel_right]

end Abstract

section Semisimple

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]
  {X T : Subgroup G} {S I : Subgroup V}

theorem tilde_eq_iSup_smul (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hS : ∀ t ∈ T, ∀ w ∈ S, t • w ∈ S) (hgen : S = ⨆ t ∈ T, t • I) :
    letI := quotAct hTX hS
    tilde X S S = ⨆ t : T, t • tilde X S I := by
  letI := quotAct hTX hS
  rw [← tilde_biSup_smul hTX hS I]
  exact congrArg (tilde X S) hgen

theorem semisimple_tilde_of_orbit (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hS : ∀ t ∈ T, ∀ w ∈ S, t • w ∈ S) (hI : I ∈ IrrPlus X S) (hgen : S = ⨆ t ∈ T, t • I) :
    ∀ J : Subgroup (V ⧸ modFix X S), J ≤ tilde X S S → XMod.IsInv ↥X J →
      ∃ J' : Subgroup (V ⧸ modFix X S), J' ≤ tilde X S S ∧ XMod.IsInv ↥X J' ∧ J ⊓ J' = ⊥ ∧
        J ⊔ J' = tilde X S S := by
  intro J hJle hJinv
  letI := quotAct hTX hS
  have hnorm := normalizes_quot hTX hS
  obtain ⟨hirr, -⟩ := isIrr_tilde hI
  have hM := tilde_eq_iSup_smul hTX hS hgen
  rw [hM] at hJle ⊢
  exact exists_isCompl_iSup_smul hnorm hirr hJinv hJle

theorem trans_tilde_of_orbit (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hS : ∀ t ∈ T, ∀ w ∈ S, t • w ∈ S) (hI : I ∈ IrrPlus X S) (hgen : S = ⨆ t ∈ T, t • I) :
    ∀ H₁ H₂ : Subgroup V, modFix X S ≤ H₁ → H₁ ≤ S → modFix X S ≤ H₂ → H₂ ≤ S →
      (∃ I₁ : Subgroup (V ⧸ modFix X S), I₁ ≤ tilde X S S ∧ XMod.IsIrr ↥X I₁ ∧
        tilde X S H₁ = ⨆ I' ∈ {I' : Subgroup (V ⧸ modFix X S) | I' ≤ tilde X S S ∧
          XMod.IsIrr ↥X I' ∧ XMod.Iso ↥X I' I₁}, I') →
      (∃ I₂ : Subgroup (V ⧸ modFix X S), I₂ ≤ tilde X S S ∧ XMod.IsIrr ↥X I₂ ∧
        tilde X S H₂ = ⨆ I' ∈ {I' : Subgroup (V ⧸ modFix X S) | I' ≤ tilde X S S ∧
          XMod.IsIrr ↥X I' ∧ XMod.Iso ↥X I' I₂}, I') →
      ∃ t ∈ T, t • H₁ = H₂ := by
  intro H₁ H₂ hc₁ _ hc₂ _ ⟨I₁, hI₁le, hI₁irr, hH₁⟩ ⟨I₂, hI₂le, hI₂irr, hH₂⟩
  letI := quotAct hTX hS
  have hnorm := normalizes_quot hTX hS
  obtain ⟨hirr, -⟩ := isIrr_tilde hI
  have hM := tilde_eq_iSup_smul hTX hS hgen
  rw [hM] at hI₁le hI₂le hH₁ hH₂
  obtain ⟨r, hr⟩ := exists_smul_isotypicSum_eq hnorm hirr hI₁irr hI₂irr hI₁le hI₂le
  have e : r • tilde X S H₁ = tilde X S H₂ := by
    rw [hH₁, hH₂]
    exact hr
  rw [tilde_smul hTX hS r H₁] at e
  have h1 := comap_tilde (X := X) (W := S) ((r : G) • H₁)
  have h2 := comap_tilde (X := X) (W := S) H₂
  rw [e] at h1
  have hsub : modFix X S ≤ (r : G) • H₁ := by
    intro c hc
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact hc₁ (smul_mem_modFix hTX hS (T.inv_mem r.2) hc)
  rw [sup_eq_left.2 hsub] at h1
  rw [sup_eq_left.2 hc₂] at h2
  exact ⟨r, r.2, h1.symm.trans h2⟩

end Semisimple


end SemisimpleHomog

section Clause4

variable [Finite W]

omit [Finite W] in
theorem map_mem_fixV_iff {H : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W))) (w : W) :
    g w ∈ fixV H ↔ w ∈ fixV H := by
  constructor
  · intro hw x hx
    have h1 := hw (g * x * g⁻¹) (conj_mem_of_mem_normalizer hg hx)
    have h3 : g (x w) = g w := by
      calc g (x w) = (g * x * g⁻¹) (g w) := by simp [MulAut.mul_apply]
        _ = g w := h1
    exact g.injective h3
  · intro hw x hx
    have h1 := hw (g⁻¹ * x * g) (inv_conj_mem_of_mem_normalizer hg hx)
    calc x (g w) = g ((g⁻¹ * x * g) w) := by simp [MulAut.mul_apply]
      _ = g w := by rw [h1]

omit [Finite W] in
theorem sup_inf_fixV_le {H : Subgroup (MulAut W)} {U I C : Subgroup W}
    (hU : ∀ x ∈ H, ∀ w ∈ U, x w ∈ U) (hI : I ∈ IrrPlus H (⊤ : Subgroup W))
    (hIC : I ⊓ fixV H ≤ C) (hCU : C ≤ U) (hUC : U ⊓ fixV H ≤ C) :
    (U ⊔ I) ⊓ fixV H ≤ C := by
  rw [mem_irrPlus_top_iff] at hI
  obtain ⟨invI, commI, ltI, irrI⟩ := hI
  rintro x ⟨hxUI, hxZ⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hxUI
  have hcU : ∀ g ∈ H, g w * w⁻¹ ∈ U ⊓ I := by
    intro g hg
    have hx : g (u * w) = u * w := mem_fixV.1 hxZ g hg
    rw [map_mul] at hx
    have e : g w * w⁻¹ = (g u)⁻¹ * u := by
      calc g w * w⁻¹ = (g u)⁻¹ * (g u * g w) * w⁻¹ := by group
        _ = (g u)⁻¹ * (u * w) * w⁻¹ := by rw [hx]
        _ = (g u)⁻¹ * u := by group
    refine ⟨?_, I.mul_mem (invI g hg w hw) (I.inv_mem hw)⟩
    rw [e]
    exact U.mul_mem (U.inv_mem (hU g hg u hu)) hu
  have hD1 : I ⊓ fixV H ≤ U ⊓ I := le_inf (hIC.trans hCU) inf_le_left
  rcases irrI (U ⊓ I) (isInv_inf hU invI) hD1 inf_le_right with hD | hD
  ·
    have hwcomm : ∀ g ∈ H, g w * w⁻¹ ∈ I ⊓ fixV H := fun g hg => by
      rw [← hD]
      exact hcU g hg
    let F : Subgroup W :=
      { carrier := {y | y ∈ I ∧ ∀ g ∈ H, g y * y⁻¹ ∈ fixV H}
        mul_mem' := by
          rintro a b ⟨ha, hag⟩ ⟨hb, hbg⟩
          refine ⟨I.mul_mem ha hb, fun g hg => ?_⟩
          have e : g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹) := by
            rw [map_mul, mul_inv]
            exact mul_mul_mul_comm _ _ _ _
          rw [e]
          exact (fixV H).mul_mem (hag g hg) (hbg g hg)
        one_mem' := ⟨I.one_mem, fun g _ => by simpa using (fixV H).one_mem⟩
        inv_mem' := by
          rintro a ⟨ha, hag⟩
          refine ⟨I.inv_mem ha, fun g hg => ?_⟩
          have e : g a⁻¹ * (a⁻¹)⁻¹ = (g a * a⁻¹)⁻¹ := by
            simp [mul_comm]
          rw [e]
          exact (fixV H).inv_mem (hag g hg) }
    have hmemF : ∀ y, y ∈ F ↔ y ∈ I ∧ ∀ g ∈ H, g y * y⁻¹ ∈ fixV H := fun y => Iff.rfl
    have invF : ∀ h ∈ H, ∀ y ∈ F, h y ∈ F := by
      intro h hh y hy
      obtain ⟨hyI, hyg⟩ := (hmemF y).1 hy
      refine (hmemF _).2 ⟨invI h hh y hyI, fun g hg => ?_⟩
      have hg' : h⁻¹ * g * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hg) hh
      have e : g (h y) * (h y)⁻¹ = h ((h⁻¹ * g * h) y * y⁻¹) := by
        simp [MulAut.mul_apply]
      rw [e]
      exact isInv_fixV H h hh _ (hyg _ hg')
    have hZF : I ⊓ fixV H ≤ F := fun z hz => (hmemF z).2 ⟨hz.1, fun g hg => by
      rw [mem_fixV.1 hz.2 g hg, mul_inv_cancel]
      exact (fixV H).one_mem⟩
    have hFI : F ≤ I := fun y hy => ((hmemF y).1 hy).1
    rcases irrI F invF hZF hFI with hF | hF
    · have hwF : w ∈ F := (hmemF w).2 ⟨hw, fun g hg => (hwcomm g hg).2⟩
      rw [hF] at hwF
      have huZ : u ∈ fixV H := by
        have := (fixV H).mul_mem hxZ ((fixV H).inv_mem hwF.2)
        rwa [mul_inv_cancel_right] at this
      exact C.mul_mem (hUC ⟨hu, huZ⟩) (hIC hwF)
    · exfalso
      have hle : commSub I H ≤ fixV H := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨g, hg, y, hy, rfl⟩
        have hyF : y ∈ F := by rw [hF]; exact hy
        exact ((hmemF y).1 hyF).2 g hg
      rw [commI] at hle
      have h1 : I ⊓ fixV H = I := inf_eq_left.2 hle
      rw [h1] at ltI
      exact lt_irrefl _ ltI
  ·
    have hIU : I ≤ U := inf_eq_right.1 hD
    exact hUC ⟨U.mul_mem hu (hIU hw), hxZ⟩

theorem fixV_eq_iSup_map {M Mp : Subgroup (MulAut W)} {V : Subgroup W}
    (hMn : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hirr : V ∈ IrrPlus Mp (⊤ : Subgroup W))
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤) :
    fixV Mp = ⨆ m ∈ M, (V ⊓ fixV Mp).map m.toMonoidHom := by
  set C : Subgroup W := ⨆ m ∈ M, (V ⊓ fixV Mp).map m.toMonoidHom
  have hCZ : C ≤ fixV Mp := by
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact (map_mem_fixV_iff (hMn hm) v).2 hv.2
  have hCinv : ∀ x ∈ Mp, ∀ w ∈ C, x w ∈ C := fun x hx w hw => by
    rw [mem_fixV.1 (hCZ hw) x hx]
    exact hw
  obtain ⟨U, hCU, hUmax⟩ := Finite.exists_le_maximal (a := C)
    (p := fun U : Subgroup W => C ≤ U ∧ (∀ x ∈ Mp, ∀ w ∈ U, x w ∈ U) ∧ U ⊓ fixV Mp ≤ C)
    ⟨le_rfl, hCinv, inf_le_left⟩
  obtain ⟨⟨-, hUinv, hUC⟩, hmax⟩ := hUmax
  have hconj : ∀ m ∈ M, V.map m.toMonoidHom ≤ U := by
    intro m hm
    have hVm : V.map m.toMonoidHom ∈ IrrPlus Mp (⊤ : Subgroup W) :=
      irrPlus_map (fun _ hx => conj_mem_of_mem_normalizer (hMn hm) hx)
        (fun _ hx => inv_conj_mem_of_mem_normalizer (hMn hm) hx) hirr
    have hVmC : V.map m.toMonoidHom ⊓ fixV Mp ≤ C := by
      rintro _ ⟨⟨v, hv, rfl⟩, hmv⟩
      have hvZ : v ∈ fixV Mp := (map_mem_fixV_iff (hMn hm) v).1 hmv
      have hle : (V ⊓ fixV Mp).map m.toMonoidHom ≤ C := le_iSup₂_of_le m hm le_rfl
      exact hle (Subgroup.mem_map_of_mem _ ⟨hv, hvZ⟩)
    have hP : C ≤ U ⊔ V.map m.toMonoidHom ∧
        (∀ x ∈ Mp, ∀ w ∈ U ⊔ V.map m.toMonoidHom, x w ∈ U ⊔ V.map m.toMonoidHom) ∧
        (U ⊔ V.map m.toMonoidHom) ⊓ fixV Mp ≤ C :=
      ⟨hCU.trans le_sup_left, isInv_sup hUinv ((mem_irrPlus_top_iff.1 hVm).1),
        sup_inf_fixV_le hUinv hVm hVmC hCU hUC⟩
    exact le_sup_right.trans (hmax hP le_sup_left)
  have hUtop : (⊤ : Subgroup W) ≤ U := by
    rw [← hgen]
    exact iSup₂_le hconj
  refine le_antisymm (fun w hw => hUC ⟨hUtop (Subgroup.mem_top w), hw⟩) hCZ


end Clause4

section FStar

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_pow_prime_pow_eq_one {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : X} {m n : ℕ} (hm : x ^ p ^ m = 1) (hn : x ^ 2 ^ n ∈ K) :
    x ∈ K := by
  have h2 : (x : X ⧸ K) ^ 2 ^ n = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have h1 : (x : X ⧸ K) ^ p ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, hm]
    exact QuotientGroup.mk_one K
  have hcop : Nat.Coprime (p ^ m) (2 ^ n) :=
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow m n
  have h := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2)
  rw [orderOf_eq_one_iff] at h
  exact (QuotientGroup.eq_one_iff x).mp h

theorem isPGroup_two_quotient {H Z : Subgroup G} (hZn : (Z.subgroupOf H).Normal)
    (hq : ∀ y ∈ H, ∃ n : ℕ, y ^ 2 ^ n ∈ Z) : IsPGroup 2 (↥H ⧸ Z.subgroupOf H) := by
  haveI := hZn
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨n, hn⟩ := hq y.1 y.2
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hn

theorem generalizedFitting_map_le_of_two_quotient {H Z : Subgroup G} (hZH : Z ≤ H)
    (hZn : (Z.subgroupOf H).Normal) (hq : ∀ y ∈ H, ∃ n : ℕ, y ^ 2 ^ n ∈ Z)
    (hO2 : pCoreOf 2 H = ⊥) : (CFSG.generalizedFitting ↥H).map H.subtype ≤ Z := by
  haveI := hZn
  haveI : Group.IsNilpotent (↥H ⧸ Z.subgroupOf H) := (isPGroup_two_quotient hZn hq).isNilpotent
  have hO2' : CFSG.pCore 2 ↥H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hO2
  have hF : CFSG.fittingSubgroup ↥H ≤ Z.subgroupOf H := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp, hO2']
      exact bot_le
    · intro x hx
      obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCore_isPGroup p.1.1 (G := ↥H) ⟨x, hx⟩
      obtain ⟨n, hn⟩ := hq x.1 x.2
      exact mem_of_pow_prime_pow_eq_one (Nat.prime_of_mem_primeFactors p.1.2) hp
        (by simpa using congrArg Subtype.val hm) hn
  have hL : CFSG.layer ↥H ≤ Z.subgroupOf H := by
    rw [← QuotientGroup.ker_mk' (Z.subgroupOf H), ← Subgroup.map_eq_bot_iff]
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect] at hlt
    exact lt_irrefl _ hlt
  calc (CFSG.generalizedFitting ↥H).map H.subtype
      ≤ (Z.subgroupOf H).map H.subtype := Subgroup.map_mono (sup_le hF hL)
    _ = Z := Subgroup.map_subgroupOf_eq_of_le hZH

theorem le_generalizedFitting_map_of_isPGroup {H Z : Subgroup G} (p : ℕ) [Fact p.Prime]
    (hZH : Z ≤ H) (hZn : (Z.subgroupOf H).Normal) (hZp : IsPGroup p ↥Z) :
    Z ≤ (CFSG.generalizedFitting ↥H).map H.subtype :=
  (CFSG.LieType.BorelTits.le_pCoreOf p hZH hZn hZp).trans
    (Subgroup.map_mono ((CFSG.pCore_le_fitting _ p).trans le_sup_left))

theorem isComponent_map_subtype_of_normal {A : Type*} [Group A] {W : Subgroup A} (hW : W.Normal)
    {K : Subgroup ↥W} (hK : CFSG.IsComponent K) : CFSG.IsComponent (K.map W.subtype) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective W.subtype W.subtype_injective) hK.1,
    hK.2.trans' hW.isSubnormal⟩

theorem map_layer_le_layer_of_normal {A : Type*} [Group A] {W : Subgroup A} (hW : W.Normal) :
    (CFSG.layer ↥W).map W.subtype ≤ CFSG.layer A := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact CFSG.LocalCores.component_le_layer (isComponent_map_subtype_of_normal hW hK)

theorem layer_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.layer A = ⊤) : CFSG.layer B = ⊤ := by
  have hle : (CFSG.layer A).map e.toMonoidHom ≤ CFSG.layer B := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact CFSG.LocalCores.component_le_layer (CFSG.LocalCores.isComponent_map_mulEquiv e hK)
  rw [h, Subgroup.map_top_of_surjective _ e.surjective] at hle
  exact top_le_iff.mp hle

theorem le_generalizedFitting_map_of_layer_eq_top {H Z : Subgroup G} (hZH : Z ≤ H)
    (hZn : (Z.subgroupOf H).Normal) (hZl : CFSG.layer ↥Z = ⊤) :
    Z ≤ (CFSG.generalizedFitting ↥H).map H.subtype := by
  have hl : CFSG.layer ↥(Z.subgroupOf H) = ⊤ :=
    layer_eq_top_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZH).symm hZl
  have hle : Z.subgroupOf H ≤ CFSG.layer ↥H := by
    intro x hx
    refine map_layer_le_layer_of_normal hZn ?_
    rw [hl]
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  calc Z = (Z.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hZH).symm
    _ ≤ (CFSG.generalizedFitting ↥H).map H.subtype := Subgroup.map_mono (hle.trans le_sup_right)

end FStar


section CommuteOn

variable [Finite W]

theorem trivial_on_of_isPGroup_commute_on {Mp : Subgroup (MulAut W)} {V : Subgroup W}
    (hexp : ∀ w : W, w ^ 2 = 1) (hirr : V ∈ IrrPlus Mp (⊤ : Subgroup W))
    {Y : Subgroup (MulAut W)} (hY : IsPGroup 2 Y) (hYV : ∀ y ∈ Y, ∀ v ∈ V, y v ∈ V)
    (hYMp : ∀ y ∈ Y, ∀ m ∈ Mp, ∀ v ∈ V, y (m v) = m (y v)) : ∀ y ∈ Y, ∀ v ∈ V, y v = v := by
  obtain ⟨hinv, hcomm, hlt, hirr'⟩ := mem_irrPlus_top_iff.mp hirr
  set C : Subgroup W := V ⊓ fixV Mp with hC
  have hYC : ∀ y ∈ Y, ∀ c ∈ C, y c ∈ C := by
    intro y hy c hc
    refine ⟨hYV y hy c hc.1, fun m hm => ?_⟩
    rw [← hYMp y hy m hm c hc.1, hc.2 m hm]
  let J : Subgroup W :=
    { carrier := {v | v ∈ V ∧ ∀ y ∈ Y, y v * v⁻¹ ∈ C}
      one_mem' := ⟨V.one_mem, fun y _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, fun y hy => by
        have e : y (a * b) * (a * b)⁻¹ = (y a * a⁻¹) * (y b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [e]
        exact C.mul_mem (ha.2 y hy) (hb.2 y hy)⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, fun y hy => by
        have e : y a⁻¹ * (a⁻¹)⁻¹ = (y a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
        rw [e]
        exact C.inv_mem (ha.2 y hy)⟩ }
  have hCJ : C ≤ J := fun c hc => ⟨hc.1, fun y hy => C.mul_mem (hYC y hy c hc) (C.inv_mem hc)⟩
  have hJV : J ≤ V := fun v hv => hv.1
  have hJinv : ∀ m ∈ Mp, ∀ w ∈ J, m w ∈ J := by
    intro m hm w hw
    refine ⟨hinv m hm w hw.1, fun y hy => ?_⟩
    have e : y (m w) * (m w)⁻¹ = m (y w * w⁻¹) := by
      rw [hYMp y hy m hm w hw.1, map_mul, map_inv]
    rw [e]
    have hc := hw.2 y hy
    rw [hc.2 m hm]
    exact hc
  have hJeq : J = V := by
    rcases hirr' J hJinv hCJ hJV with h | h
    · exfalso
      obtain ⟨v, hvV, hvC, hv⟩ :=
        exists_mem_diff_commutator_mem_of_isPGroup hY hexp hlt hYV hYC
      exact hvC (h ▸ ⟨hvV, hv⟩)
    · exact h
  have hall : ∀ v ∈ V, ∀ y ∈ Y, y v * v⁻¹ ∈ C := fun v hv y hy => by
    have hvJ : v ∈ J := by rw [hJeq]; exact hv
    exact hvJ.2 y hy
  intro y hy
  have hgen : commSub V Mp ≤ (y : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    show y (m v * v⁻¹) = m v * v⁻¹
    have hc := hall v hv y hy
    have h1 : m (y v * v⁻¹) = y v * v⁻¹ := hc.2 m hm
    have e : y v = (y v * v⁻¹) * v := by rw [inv_mul_cancel_right]
    calc y (m v * v⁻¹) = m (y v) * (y v)⁻¹ := by rw [map_mul, map_inv, hYMp y hy m hm v hv]
      _ = m ((y v * v⁻¹) * v) * (y v)⁻¹ := by rw [← e]
      _ = (y v * v⁻¹) * m v * (y v)⁻¹ := by rw [map_mul, h1]
      _ = (y v * (y v)⁻¹) * (m v * v⁻¹) := by ac_rfl
      _ = m v * v⁻¹ := by rw [mul_inv_cancel, one_mul]
  intro v hv
  have hv' : v ∈ commSub V Mp := hcomm.symm ▸ hv
  exact hgen hv'

end CommuteOn

section Clause1V

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem normal_comap_pCoreOf {A X : Subgroup (MulAut W)} {U : Subgroup W} (hXU : X ≤ stabSub U)
    (hXA : X ≤ A) :
    ((pCoreOf 2 (autSub A U)).comap ((resHom U).comp (Subgroup.inclusion hXU))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (autSub A U)
  refine ⟨fun y hy g => ?_⟩
  have hg : (resHom U).comp (Subgroup.inclusion hXU) g ∈ autSub A U :=
    mem_autSub.mpr ⟨⟨g, hXU g.2⟩, hXA g.2, rfl⟩
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hYn hg) _).mp hy

theorem pCoreOf_autSub_eq_bot_of_comm (h : Core M Mp T V)
    (hcomm : ∀ (y : MulAut W) (_ : y ∈ Mp ⊔ T) (hyV : y ∈ stabSub V),
      resHom V ⟨y, hyV⟩ ∈ pCoreOf 2 (autSub (Mp ⊔ T) V) →
        ∀ m ∈ Mp, ∀ v ∈ V, y (m v) = m (y v)) :
    pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup (MulAut W) := (Mp ⊔ T) ⊓ stabSub V with hX
  have hXV : X ≤ stabSub V := inf_le_right
  let ρ : ↥X →* MulAut ↥V := (resHom V).comp (Subgroup.inclusion hXV)
  have hrange : autSub (Mp ⊔ T) V = ρ.range := by
    ext φ
    rw [mem_autSub, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg, g.2⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hXV x.2⟩, x.2.1, rfl⟩
  have hY2 : IsPGroup 2 (pCoreOf 2 (autSub (Mp ⊔ T) V)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  let Yt : Subgroup ↥X := (pCoreOf 2 (autSub (Mp ⊔ T) V)).comap ρ
  have hYtn : Yt.Normal := normal_comap_pCoreOf hXV inf_le_left
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥X) := inferInstance
  have hS2 : IsPGroup 2 (S : Subgroup ↥X) := S.isPGroup'
  have hSi : ¬ 2 ∣ (S : Subgroup ↥X).index := S.not_dvd_index
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hQ2 : IsPGroup 2 ((S : Subgroup ↥X).map ρ.rangeRestrict) := hS2.map _
  have hQi : ¬ 2 ∣ ((S : Subgroup ↥X).map ρ.rangeRestrict).index := fun hd =>
    hSi (hd.trans (Subgroup.index_map_dvd _ hsurj))
  have hNn : (Yt.map ρ.rangeRestrict).Normal := hYtn.map ρ.rangeRestrict hsurj
  have hN2 : IsPGroup 2 (Yt.map ρ.rangeRestrict) :=
    (hY2.comap_of_injective ρ.range.subtype ρ.range.subtype_injective).to_le (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx)
  have hNQ : Yt.map ρ.rangeRestrict ≤ (hQ2.toSylow hQi : Subgroup ↥ρ.range) :=
    hN2.le_sylow_of_normal (hQ2.toSylow hQi)
  let P : Subgroup (MulAut W) := (Yt ⊓ (S : Subgroup ↥X)).map X.subtype
  have hP2 : IsPGroup 2 P := (hS2.to_le inf_le_right).map X.subtype
  have hPV : ∀ p ∈ P, ∀ v ∈ V, p v ∈ V := by
    rintro _ ⟨x, -, rfl⟩ v hv
    exact (hXV x.2 v).mpr hv
  have hPc : ∀ p ∈ P, ∀ m ∈ Mp, ∀ v ∈ V, p (m v) = m (p v) := by
    rintro _ ⟨x, ⟨hxY, -⟩, rfl⟩ m hm v hv
    exact hcomm (x : MulAut W) x.2.1 (hXV x.2) hxY m hm v hv
  have hP1 := trivial_on_of_isPGroup_commute_on h.exp h.irr hP2 hPV hPc
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  have hφG : φ ∈ ρ.range := hrange ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _ hφ
  obtain ⟨x, rfl⟩ := hφG
  have hx : x ∈ Yt := hφ
  have hmem : ρ.rangeRestrict x ∈ (S : Subgroup ↥X).map ρ.rangeRestrict := hNQ ⟨x, hx, rfl⟩
  obtain ⟨s, hsS, hsx⟩ := hmem
  have hsx' : ρ s = ρ x := congrArg Subtype.val hsx
  have hsY : s ∈ Yt := by
    show ρ s ∈ pCoreOf 2 (autSub (Mp ⊔ T) V)
    rw [hsx']
    exact hφ
  have hsP : (s : MulAut W) ∈ P := ⟨s, ⟨hsY, hsS⟩, rfl⟩
  rw [← hsx']
  ext u
  exact hP1 _ hsP u u.2

theorem commute_on_of_caseII (h : Core M Mp T V) {p : ℕ} (hII : CaseII Mp T p) {U : Subgroup W}
    (hMpU : Mp ≤ stabSub U) {y : MulAut W} (hyU : y ∈ stabSub U)
    (hρ : resHom U ⟨y, hyU⟩ ∈ pCoreOf 2 (autSub (Mp ⊔ T) U)) :
    ∀ m ∈ Mp, ∀ u ∈ U, y (m u) = m (y u) := by
  intro m hm u hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hII.1
  have hp2 := hII.2.1
  have hN2 : IsPGroup 2 (pCoreOf 2 (autSub (Mp ⊔ T) U)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hNn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (autSub (Mp ⊔ T) U)
  have hZp : IsPGroup p ↥(autSub Mp U) := isPGroup_autSub hMpU hII.2.2.1
  have hZn := autSub_normal (U := U) h.T_le_normalizer
  have hZH : autSub Mp U ≤ autSub (Mp ⊔ T) U := autSub_mono le_sup_left U
  have hcom := commute_of_isPGroup_two hp hp2 hN2 hZp
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (autSub (Mp ⊔ T) U)).trans
      (le_normalizer_of_forall_conj_mem hZn))
    (hZH.trans hNn)
  have hρm : resHom U ⟨m, hMpU hm⟩ ∈ autSub Mp U := mem_autSub.mpr ⟨_, hm, rfl⟩
  have h1 := hcom _ hρ _ hρm
  have h2 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : W)) h1
  simpa [MulAut.mul_apply, resHom_apply] using h2

theorem conjAutSub_le_Mp {Mp T L : Subgroup (MulAut W)} (hMp : Mp = conjClosure L T)
    {t : MulAut W} (ht : t ∈ T) : conjAutSub t L ≤ Mp := by
  rintro _ ⟨l, hl, rfl⟩
  rw [hMp]
  exact mem_conjClosure ht hl

theorem commute_on_of_caseI (h : Core M Mp T V) {L : Subgroup (MulAut W)} (hI : CaseI M Mp T L)
    {U : Subgroup W} (hMpU : Mp ≤ stabSub U) {y : MulAut W} (hyX : y ∈ Mp ⊔ T)
    (hyU : y ∈ stabSub U) (hρ : resHom U ⟨y, hyU⟩ ∈ pCoreOf 2 (autSub (Mp ⊔ T) U)) :
    ∀ m ∈ Mp, ∀ u ∈ U, y (m u) = m (y u) := by
  obtain ⟨hL, hq, hMp⟩ := hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup (MulAut W) := (Mp ⊔ T) ⊓ stabSub U with hX
  have hXU : X ≤ stabSub U := inf_le_right
  have hXM : X ≤ M := inf_le_left.trans h.sup_le_M
  have hMpX : Mp ≤ X := le_inf le_sup_left hMpU
  let ρ : ↥X →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hXU)
  have hN2 : IsPGroup 2 (pCoreOf 2 (autSub (Mp ⊔ T) U)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYt : ((pCoreOf 2 (autSub (Mp ⊔ T) U)).comap ρ).Normal :=
    normal_comap_pCoreOf hXU inf_le_left
  have hyN : (⟨y, hyX, hyU⟩ : ↥X) ∈ (pCoreOf 2 (autSub (Mp ⊔ T) U)).comap ρ := hρ
  have hgen : ∀ t ∈ T, ∀ l ∈ L, ∀ u ∈ U, y ((t * l * t⁻¹) u) = (t * l * t⁻¹) (y u) := by
    intro t ht l hl u hu
    have hconjX : conjAutSub t L ≤ X := (conjAutSub_le_Mp hMp ht).trans hMpX
    have hxX : t * l * t⁻¹ ∈ X := hconjX ⟨l, hl, rfl⟩
    have hcomp := isComponent_conjAutSub hL hq (h.T_le ht) hconjX hXM
    rcases CFSG.LocalCores.component_normal_subgroup hcomp hYt with h1 | h1
    ·
      have hQN : ((conjAutSub t L).subgroupOf X).map ρ ≤ pCoreOf 2 (autSub (Mp ⊔ T) U) :=
        Subgroup.map_le_iff_le_comap.mpr h1
      have hperf : ⁅((conjAutSub t L).subgroupOf X).map ρ, ((conjAutSub t L).subgroupOf X).map ρ⁆ =
          ((conjAutSub t L).subgroupOf X).map ρ := by
        rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hcomp.1.1]
      have hbot := eq_bot_of_perfect_of_isPGroup hperf (hN2.to_le hQN)
      have hmem : ρ ⟨t * l * t⁻¹, hxX⟩ ∈ ((conjAutSub t L).subgroupOf X).map ρ :=
        Subgroup.mem_map_of_mem ρ
          (show (⟨t * l * t⁻¹, hxX⟩ : ↥X) ∈ (conjAutSub t L).subgroupOf X from ⟨l, hl, rfl⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      have hfix : ∀ w ∈ U, (t * l * t⁻¹) w = w := by
        intro w hw
        have h0 := congrArg (fun φ : MulAut ↥U => ((φ ⟨w, hw⟩ : ↥U) : W)) hmem
        exact h0
      rw [hfix u hu, hfix (y u) ((hyU u).mpr hu)]
    ·
      have hc := Subgroup.commutator_mem_commutator
        (show (⟨t * l * t⁻¹, hxX⟩ : ↥X) ∈ (conjAutSub t L).subgroupOf X from ⟨l, hl, rfl⟩) hyN
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      have hc' : (t * l * t⁻¹) * y = y * (t * l * t⁻¹) := congrArg Subtype.val hc
      have := congrArg (fun φ : MulAut W => φ u) hc'
      simp only [MulAut.mul_apply] at this
      exact this.symm
  let Cy : Subgroup (MulAut W) :=
    { carrier := {m | m ∈ stabSub U ∧ ∀ u ∈ U, y (m u) = m (y u)}
      one_mem' := ⟨(stabSub U).one_mem, fun u _ => rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨(stabSub U).mul_mem ha.1 hb.1, fun u hu => by
        have hbu : b u ∈ U := (hb.1 u).mpr hu
        show y (a (b u)) = a (b (y u))
        rw [ha.2 _ hbu, hb.2 u hu]⟩
      inv_mem' := fun {a} ha => ⟨(stabSub U).inv_mem ha.1, fun u hu => by
        have hau : a⁻¹ u ∈ U := ((stabSub U).inv_mem ha.1 u).mpr hu
        have h1 := ha.2 _ hau
        have h2 : a (y (a⁻¹ u)) = y u := by
          rw [← h1]
          simp
        calc y (a⁻¹ u) = a⁻¹ (a (y (a⁻¹ u))) := by simp
          _ = a⁻¹ (y u) := by rw [h2]⟩ }
  have hMpC : Mp ≤ Cy := by
    refine hMp.le.trans (conjClosure_le fun t ht l hl => ⟨?_, hgen t ht l hl⟩)
    exact hMpU (conjAutSub_le_Mp hMp ht ⟨l, hl, rfl⟩)
  intro m hm u hu
  exact (hMpC hm).2 u hu

theorem pCoreOf_autSub_eq_bot_of_caseI (h : Core M Mp T V) {L : Subgroup (MulAut W)}
    (hI : CaseI M Mp T L) : pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥ :=
  pCoreOf_autSub_eq_bot_of_comm h fun _ hy hyV hρ =>
    commute_on_of_caseI h hI h.Mp_le_stabSub hy hyV hρ

theorem pCoreOf_autSub_eq_bot_of_caseII (h : Core M Mp T V) {p : ℕ} (hII : CaseII Mp T p) :
    pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥ :=
  pCoreOf_autSub_eq_bot_of_comm h fun _ _ hyV hρ =>
    commute_on_of_caseII h hII h.Mp_le_stabSub hyV hρ

theorem pCoreOf_autSub_orbSup_eq_bot_of_caseII (h : Core M Mp T V) {p : ℕ} (hII : CaseII Mp T p) :
    pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥ := by
  have hp := hII.1
  have hp2 := hII.2.1
  refine pCoreOf_autSub_orbSup_eq_bot_of_cent h fun s hs hρ => ?_
  have hsU : s ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V hs
  have hcomm := commute_on_of_caseII h hII h.Mp_le_stabSub_orbSup hsU hρ
  have hmod : ∀ m ∈ Mp, s * m * s⁻¹ * m⁻¹ ∈ (frattini ↥Mp).map Mp.subtype := by
    intro m hm
    apply le_frattini_of_caseII h hII
    refine ⟨?_, fun w hw => ?_⟩
    · have h1 : s * m * s⁻¹ ∈ Mp :=
        (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer hs) m).mp hm
      exact Mp.mul_mem h1 (Mp.inv_mem hm)
    · have hw1 : m⁻¹ w ∈ orbSup T V := ((h.Mp_le_stabSub_orbSup (Mp.inv_mem hm)) w).mpr hw
      have hw2 : s⁻¹ (m⁻¹ w) ∈ orbSup T V :=
        ((le_stabSub_orbSup T V (T.inv_mem hs)) _).mpr hw1
      have h3 := hcomm m hm _ hw2
      have e : (s * m * s⁻¹ * m⁻¹) w = s (m (s⁻¹ (m⁻¹ w))) := by simp [MulAut.mul_apply]
      rw [e, h3]
      simp
  obtain ⟨k, hk⟩ := h.T_isPGroup ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact fun m hm =>
    commute_of_comm_mod_frattini hp hp2 hII.2.2.1 (h.T_le_normalizer hs) hk' hmod m hm

end Clause1V

section Clause5

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem generalizedFitting_autSub_le (h : Core M Mp T V) {U : Subgroup W} (hMpU : Mp ≤ stabSub U)
    (hO2 : pCoreOf 2 (autSub (Mp ⊔ T) U) = ⊥) :
    (CFSG.generalizedFitting ↥(autSub (Mp ⊔ T) U)).map (autSub (Mp ⊔ T) U).subtype ≤
      autSub Mp U :=
  generalizedFitting_map_le_of_two_quotient (autSub_mono le_sup_left U)
    (normal_autSub_subgroupOf h.T_le_normalizer)
    (exists_pow_mem_autSub h.T_le_normalizer h.T_isPGroup hMpU) hO2

theorem autSub_le_generalizedFitting_of_pGroup (h : Core M Mp T V) {U : Subgroup W}
    (hMpU : Mp ≤ stabSub U) {p : ℕ} (hp : p.Prime) (hMp : IsPGroup p ↥Mp) :
    autSub Mp U ≤
      (CFSG.generalizedFitting ↥(autSub (Mp ⊔ T) U)).map (autSub (Mp ⊔ T) U).subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact le_generalizedFitting_map_of_isPGroup p (autSub_mono le_sup_left U)
    (normal_autSub_subgroupOf h.T_le_normalizer) (isPGroup_autSub hMpU hMp)

theorem autSub_le_generalizedFitting_of_layer (h : Core M Mp T V) {U : Subgroup W}
    (hl : CFSG.layer ↥(autSub Mp U) = ⊤) :
    autSub Mp U ≤
      (CFSG.generalizedFitting ↥(autSub (Mp ⊔ T) U)).map (autSub (Mp ⊔ T) U).subtype :=
  le_generalizedFitting_map_of_layer_eq_top (autSub_mono le_sup_left U)
    (normal_autSub_subgroupOf h.T_le_normalizer) hl

theorem layer_Mp_eq_top (h : Core M Mp T V) {L : Subgroup (MulAut W)} (hI : CaseI M Mp T L) :
    CFSG.layer ↥Mp = ⊤ := by
  obtain ⟨hL, hq, hMp⟩ := hI
  have hle : conjClosure L T ≤ (CFSG.layer ↥Mp).map Mp.subtype := by
    refine conjClosure_le fun t ht l hl => ?_
    have hcomp := isComponent_conjAutSub hL hq (h.T_le ht) (conjAutSub_le_Mp hMp ht) h.Mp_le
    have hlay := CFSG.LocalCores.component_le_layer hcomp
    exact ⟨⟨t * l * t⁻¹, conjAutSub_le_Mp hMp ht ⟨l, hl, rfl⟩⟩,
      hlay (show (⟨t * l * t⁻¹, conjAutSub_le_Mp hMp ht ⟨l, hl, rfl⟩⟩ : ↥Mp) ∈
        (conjAutSub t L).subgroupOf Mp from ⟨l, hl, rfl⟩), rfl⟩
  refine eq_top_iff.mpr fun x _ => ?_
  have hx' : (x : MulAut W) ∈ conjClosure L T := by
    rw [← hMp]
    exact x.2
  obtain ⟨z, hz, hzx⟩ := hle hx'
  have : z = x := Subtype.ext hzx
  rw [← this]
  exact hz

theorem layer_autSub_eq_top {Mp : Subgroup (MulAut W)} {U : Subgroup W} (hMpU : Mp ≤ stabSub U)
    (hl : CFSG.layer ↥Mp = ⊤) : CFSG.layer ↥(autSub Mp U) = ⊤ := by
  let f : ↥Mp →* ↥(autSub Mp U) :=
    ((resHom U).comp (Subgroup.inclusion hMpU)).codRestrict (autSub Mp U)
      (fun x => mem_autSub.mpr ⟨⟨x, hMpU x.2⟩, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact ⟨⟨g, hg⟩, rfl⟩
  exact CFSG.LocalCores.layer_eq_top_of_surjective hl f hf

end Clause5

section Clause36

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

theorem irrPlus_map_of_mem_normalizer (h : Core M Mp T V) {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (Mp : Set (MulAut W))) :
    V.map x.toMonoidHom ∈ IrrPlus Mp (⊤ : Subgroup W) :=
  irrPlus_map (fun _ hy => conj_mem_of_mem_normalizer hx hy)
    (fun _ hy => inv_conj_mem_of_mem_normalizer hx hy) h.irr

theorem Core.commSub_top (h : Core M Mp T V) : commSub (⊤ : Subgroup W) Mp = ⊤ := by
  refine eq_top_iff.mpr (h.gen.symm.le.trans (iSup₂_le fun m hm => ?_))
  have hVm := irrPlus_map_of_mem_normalizer h (h.Mp_normal hm)
  calc V.map m.toMonoidHom = commSub (V.map m.toMonoidHom) Mp :=
        (mem_irrPlus_top_iff.mp hVm).2.1.symm
    _ ≤ commSub ⊤ Mp := commSub_mono le_top le_rfl

theorem Core.commSub_orbSup (h : Core M Mp T V) : commSub (orbSup T V) Mp = orbSup T V := by
  refine le_antisymm (commSub_le_of_invariant fun x hx w hw => ?_) (orbSup_le fun t ht => ?_)
  · exact ((h.Mp_le_stabSub_orbSup hx) w).mpr hw
  · have hVt := irrPlus_map_of_mem_normalizer h (h.T_le_normalizer ht)
    calc V.map t.toMonoidHom = commSub (V.map t.toMonoidHom) Mp :=
          (mem_irrPlus_top_iff.mp hVt).2.1.symm
      _ ≤ commSub (orbSup T V) Mp := commSub_mono (map_le_orbSup ht) le_rfl

theorem Core.ti (h : Core M Mp T V) (hC : V ⊓ fixV Mp = ⊥) :
    ∀ x ∈ M, V ⊓ V.map x.toMonoidHom = ⊥ ∨ V.map x.toMonoidHom = V := by
  intro x hx
  have hVx := irrPlus_map_of_mem_normalizer h (h.Mp_normal hx)
  obtain ⟨invV, -, -, irrV⟩ := mem_irrPlus_top_iff.mp h.irr
  obtain ⟨invVx, -, -, irrVx⟩ := mem_irrPlus_top_iff.mp hVx
  have hCx : V.map x.toMonoidHom ⊓ fixV Mp = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨v, hv, rfl⟩, hmv⟩
    have hvZ : v ∈ fixV Mp := (map_mem_fixV_iff (h.Mp_normal hx) v).1 hmv
    have hv1 : v ∈ V ⊓ fixV Mp := ⟨hv, hvZ⟩
    rw [hC, Subgroup.mem_bot] at hv1
    rw [Subgroup.mem_bot]
    show x v = 1
    rw [hv1, map_one]
  by_cases hI : V ⊓ V.map x.toMonoidHom = ⊥
  · exact Or.inl hI
  · right
    have h1 : V ⊓ V.map x.toMonoidHom = V := by
      rcases irrV (V ⊓ V.map x.toMonoidHom) (isInv_inf invV invVx) (by rw [hC]; exact bot_le)
        inf_le_left with h' | h'
      · exact absurd (h'.trans hC) hI
      · exact h'
    have h2 : V ⊓ V.map x.toMonoidHom = V.map x.toMonoidHom := by
      rcases irrVx (V ⊓ V.map x.toMonoidHom) (isInv_inf invV invVx) (by rw [hCx]; exact bot_le)
        inf_le_right with h' | h'
      · exact absurd (h'.trans hCx) hI
      · exact h'
    rw [← h2, h1]

end Clause36

end CFSG.Quasithin.RonanD34
