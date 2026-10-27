module

public import CFSG.Quasithin.H13.A6S13813c
public import CFSG.Quasithin.H13.A6S13813b
public import CFSG.Quasithin.H13.A6S1385b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

namespace A6P

variable {G : Type} [Group G] [Finite G]

structure PData {M : Type} [Group M] (L1 T L H : Subgroup G) (φ : ↥H →* M) (A : Subgroup M)
    (p : ℕ) (P : Subgroup M) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  le_pCore : P ≤ pCoreOf p φ.range
  exp : ∀ x ∈ P, x ^ p = 1
  cls : ⁅⁅P, P⁆, P⁆ = ⊥
  normal : ∀ x ∈ φ.range, ∀ y ∈ P, x * y * x⁻¹ ∈ P
  not_cent : ¬ Cent P A
  minimal : ∀ R : Subgroup M, R ≤ P → (∀ y ∈ ((L1 ⊔ T).subgroupOf H).map φ, ∀ x ∈ R,
    y * x * y⁻¹ ∈ R) → ¬ Cent R A → R = P
  map_mem : ∀ x : ↥H, (x : G) ∈ oTwoRes ((P.comap φ).map H.subtype) → φ x ∈ P
  lift : ∀ y ∈ P, ∃ x : ↥H, (x : G) ∈ oTwoRes ((P.comap φ).map H.subtype) ∧ φ x = y
  not_le : ¬ oTwoRes ((P.comap φ).map H.subtype) ≤ Subgroup.normalizer (L : Set G)
  eq : H = (oTwoRes ((P.comap φ).map H.subtype) ⊔ L1) ⊔ T

end A6P

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem l1plus_le_L1 : l1plus T L V ≤ S.L1 := by
  refine (oTwoRes_le _).trans (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
  rw [commutatorElement_def]
  have h1 := (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hb.1) _).mp (S.L1.inv_mem ha)
  have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
  rw [e]
  exact S.L1.mul_mem ha h1

theorem exists_P (h139 : Stmt13_3_9) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hsol : Group.IsSolvable ↥H)
    (hmin : ∀ K ∈ S.Hz, K ≤ H → K = H)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
    (hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G))
    (hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G))
    {A : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))}
    (hA : A ≤ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hA2 : IsPGroup 2 A) (hA1 : A ≠ ⊥) :
    ∃ (p : ℕ) (P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))),
      A6P.PData S.L1 T L H (actH hV₁ hIH) A p P := by
  have hF := (hS.hF H hH).toHypF91
  set φ := actH hV₁ hIH with hφ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hsolX : Group.IsSolvable ↥φ.range :=
    Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hO2X : pCoreOf 2 φ.range = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact A6Tv.range_o2_eq_bot hF φ hker _ (pCoreOf_le 2 _) inferInstance
      (pCoreOf_isPGroup 2 _)
  have hAX : A ≤ φ.range := hA.trans (Subgroup.map_le_range _ _)
  obtain ⟨p, hp, hp2, hnt⟩ := A6P.exists_prime_not_centralizes hsolX hO2X hAX hA2 hA1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Sc, hScP, hScN, hScexp, hScl, hScA⟩ :=
    A6P.exists_supercritical_nontriv hp2 hAX hA2 hnt
  set Y := ((S.L1 ⊔ T).subgroupOf H).map φ with hY
  have hYX : Y ≤ φ.range := Subgroup.map_le_range _ _
  obtain ⟨P, hPS, hPY, hPA, hPmin⟩ :=
    A6P.exists_minimal_invariant (Y := Y) (fun y hy s hs => hScN y (hYX hy) s hs) hScA
  have hPexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => hScexp x (hPS hx)
  have hPcl : ⁅⁅P, P⁆, P⁆ = ⊥ := le_bot_iff.mp (hScl ▸
    Subgroup.commutator_mono (Subgroup.commutator_mono hPS hPS) hPS)
  have hPp : P ≤ pCoreOf p φ.range := hPS.trans hScP
  set Ph := oTwoRes ((P.comap φ).map H.subtype) with hPh
  have hPhH : Ph ≤ H := (oTwoRes_le _).trans (Subgroup.map_subtype_le _)
  have hφPh : ∀ x : ↥H, (x : G) ∈ Ph → φ x ∈ P := by
    intro x hx
    have h1 : (x : G) ∈ (P.comap φ).map H.subtype := oTwoRes_le _ hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hlift : ∀ y ∈ P, ∃ x : ↥H, (x : G) ∈ Ph ∧ φ x = y := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ((hPp.trans (pCoreOf_le p _)) hy)
    have hxK : (x : G) ∈ (P.comap φ).map H.subtype := ⟨x, hy, rfl⟩
    obtain ⟨x', hx', hx'φ⟩ := A6P.exists_odd_lift φ hxK hp2 (n := 1)
      (by rw [pow_one]; exact hPexp _ hy)
    exact ⟨x', hx', hx'φ⟩
  have hKF : (P.comap φ).map H.subtype ≤ oTwoFIn H := by
    rintro _ ⟨x, hx, rfl⟩
    exact A6P.mem_oTwoFIn_of_mem_pCoreOf φ hker (hPp hx)
  have hPhM : ¬ Ph ≤ Subgroup.normalizer (L : Set G) := by
    intro hle
    have hle2 : Ph ≤ oTwoRes (oTwoFIn H ⊓ Subgroup.normalizer (L : Set G)) := by
      rw [hPh, oTwoRes, Subgroup.closure_le]
      rintro y ⟨hy, m, hm, hym⟩
      exact Subgroup.subset_closure
        ⟨⟨hKF hy, hle (Subgroup.subset_closure ⟨hy, m, hm, hym⟩)⟩, m, hm, hym⟩
    have hL1 : Ph ≤ S.L1 := by
      rcases S.lem13812_two h139 hH with h | ⟨-, h⟩ | ⟨-, h⟩
      · exact hle2.trans (h ▸ bot_le)
      · exact hle2.trans h.le
      · exact hle2.trans (h.le.trans S.l1plus_le_L1)
    apply hPA
    intro y hy a ha
    obtain ⟨x, hxPh, rfl⟩ := hlift y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 (hA ha)
    rw [Subgroup.mem_subgroupOf] at hq
    have hxL : (x : G) ∈ S.L1 ⊔ T := Subgroup.mem_sup_left (hL1 hxPh)
    have hc2 : ((q * x * q⁻¹ * x⁻¹ : ↥H) : G) ∈ pCoreOf 2 (S.L1 ⊔ T) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hxL) _).mp
        ((pCoreOf 2 (S.L1 ⊔ T)).inv_mem hq)
      have e : ((q * x * q⁻¹ * x⁻¹ : ↥H) : G) = (q : G) * ((x : G) * (q : G)⁻¹ * (x : G)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hq h1
    have hcP : φ (q * x * q⁻¹ * x⁻¹) ∈ P := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have hqY : φ q ∈ Y := ⟨q, Subgroup.mem_subgroupOf.mpr (pCoreOf_le 2 _ hq), rfl⟩
      exact P.mul_mem (hPY _ hqY _ (hφPh x hxPh)) (P.inv_mem (hφPh x hxPh))
    have hc1 : φ (q * x * q⁻¹ * x⁻¹) = 1 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (S.L1 ⊔ T)) ⟨_, hc2⟩
      have hk' : (q * x * q⁻¹ * x⁻¹) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      have h2 : φ (q * x * q⁻¹ * x⁻¹) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
      have hcop : Nat.Coprime (2 ^ k) p :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
        (orderOf_dvd_of_pow_eq_one (hPexp _ hcP))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at hc1
    exact hc1
  have hPhH' : (Ph ⊔ S.L1) ⊔ T ≤ H :=
    sup_le (sup_le hPhH (le_sup_left.trans hH.1.1)) (le_sup_right.trans hH.1.1)
  have hHeq : H = (Ph ⊔ S.L1) ⊔ T := by
    refine (hmin _ (S.mem_Hz_of ?_ (hPhH'.trans hH.2.1) ?_) hPhH').symm
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    · exact fun h => hPhM (le_sup_left.trans (le_sup_left.trans h))
  have hnorm : ∀ x ∈ φ.range, ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
    set N : Subgroup G := ((Subgroup.normalizer (P : Set _)).comap φ).map H.subtype with hN
    have hmemN : ∀ h : ↥H, φ h ∈ Subgroup.normalizer (P : Set _) → (h : G) ∈ N :=
      fun h hh => ⟨h, hh, rfl⟩
    have hNmem : ∀ h : ↥H, (h : G) ∈ N → φ h ∈ Subgroup.normalizer (P : Set _) := by
      intro h hh
      obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.1 hh
      have : h' = h := Subtype.ext hh'eq
      rw [← this]
      exact hh'
    have hYN : ∀ h : ↥H, (h : G) ∈ S.L1 ⊔ T → φ h ∈ Subgroup.normalizer (P : Set _) := by
      intro h hh
      have hhY : φ h ∈ Y := ⟨h, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hPY (φ h) hhY y hy
      · intro hy
        have := hPY (φ h)⁻¹ (Y.inv_mem hhY) _ hy
        simpa [mul_assoc] using this
    have hPhN : ∀ h : ↥H, (h : G) ∈ Ph → φ h ∈ Subgroup.normalizer (P : Set _) := by
      intro h hh
      have hhP := hφPh h hh
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact P.mul_mem (P.mul_mem hhP hy) (P.inv_mem hhP)
      · intro hy
        have := P.mul_mem (P.mul_mem (P.inv_mem hhP) hy) hhP
        simpa [mul_assoc] using this
    have hle : (Ph ⊔ S.L1) ⊔ T ≤ N := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro g hg
        exact hmemN ⟨g, hPhH hg⟩ (hPhN ⟨g, hPhH hg⟩ hg)
      · intro g hg
        exact hmemN ⟨g, hH.1.1 (Subgroup.mem_sup_left hg)⟩
          (hYN _ (Subgroup.mem_sup_left hg))
      · intro g hg
        exact hmemN ⟨g, hH.1.1 (Subgroup.mem_sup_right hg)⟩
          (hYN _ (Subgroup.mem_sup_right hg))
    intro x hx y hy
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hx
    exact (Subgroup.mem_normalizer_iff.mp (hNmem h (hle (hHeq.le h.2))) y).mp hy
  exact ⟨p, P, hp, hp2, hPp, hPexp, hPcl, hnorm, hPA, hPmin, hφPh, hlift, hPhM, hHeq⟩

end Setting4

end CFSG.Quasithin.H13.A6

