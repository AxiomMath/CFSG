module

public import CFSG.Quasithin.H13.A6S13813a
public import CFSG.Quasithin.Background.D216Group
public import CFSG.Quasithin.Background.F9Geometry

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace A6P

section Gen

variable {M : Type} [Group M] [Finite M]

@[expose] def Cent (K A : Subgroup M) : Prop := ∀ x ∈ K, ∀ a ∈ A, a * x = x * a

theorem exists_supercritical_nontriv {X A : Subgroup M} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hAX : A ≤ X) (hA2 : IsPGroup 2 A) (hnt : ¬ Cent (pCoreOf p X) A) :
    ∃ S : Subgroup M, S ≤ pCoreOf p X ∧ (∀ x ∈ X, ∀ s ∈ S, x * s * x⁻¹ ∈ S) ∧
      (∀ s ∈ S, s ^ p = 1) ∧ ⁅⁅S, S⁆, S⁆ = ⊥ ∧ ¬ Cent S A := by
  set P0 := pCoreOf p X with hP0
  have hP0p : IsPGroup p ↥P0 := pCoreOf_isPGroup p X
  obtain ⟨S0, hS0, hfaith⟩ := exists_isSupercritical_faithful hp2 hP0p
  have hXN : X ≤ Subgroup.normalizer (P0 : Set M) := le_normalizer_pCoreOf p X
  let φ : ∀ x ∈ X, MulAut ↥P0 := fun x hx => P0.normalizerMonoidHom ⟨x, hXN hx⟩
  have hφ : ∀ x (hx : x ∈ X) (y : ↥P0), ((φ x hx y : ↥P0) : M) = x * y * x⁻¹ := fun x hx y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P0 ⟨x, hXN hx⟩ y
  refine ⟨S0.map P0.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  ·
    rintro x hx _ ⟨s, hs, rfl⟩
    have hmap := (Subgroup.characteristic_iff_map_eq.mp hS0.characteristic) (φ x hx)
    have h1 : φ x hx s ∈ S0 := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hs
    exact ⟨_, h1, hφ x hx s⟩
  · rintro _ ⟨s, hs, rfl⟩
    have := hS0.pow_eq_one s hs
    simpa using congrArg Subtype.val this
  ·
    have h1 : ⁅S0, S0⁆ ≤ centerOf S0 := (Subgroup.commutator_mono le_rfl le_top).trans
      hS0.commutator_le
    have h2 : ⁅⁅S0, S0⁆, S0⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have hc := (h1 ha).2
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hc b hb).symm
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, h2, Subgroup.map_bot]
  ·
    intro hcen
    apply hnt
    intro y hy a ha
    have haX : a ∈ X := hAX ha
    have hord : (orderOf (φ a haX)).Coprime p := by
      obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
      have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : (φ a haX) ^ 2 ^ k = 1 := by
        refine MulEquiv.ext fun z => Subtype.ext ?_
        have e : ∀ n : ℕ, (((φ a haX) ^ n) z : M) = a ^ n * z * (a ^ n)⁻¹ := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            rw [pow_succ', MulAut.mul_apply, hφ a haX, ih]
            group
        rw [e, hk']
        simp
      exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
        (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)))
    have htriv : ∀ x ∈ S0, x⁻¹ * (φ a haX) x ∈ frattiniIn S0 := by
      intro x hx
      have h1 : (φ a haX) x = x := by
        apply Subtype.ext
        rw [hφ a haX]
        have := hcen (x : M) ⟨x, hx, rfl⟩ a ha
        rw [this, mul_inv_cancel_right]
      rw [h1, inv_mul_cancel]
      exact Subgroup.one_mem _
    have h1 := hfaith _ hord htriv
    have h2 : (φ a haX) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [h1]; rfl
    have h3 : a * y * a⁻¹ = y := by
      have := congrArg Subtype.val h2
      rwa [hφ a haX] at this
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [h3]

theorem exists_prime_not_centralizes {V : Type} [CommGroup V] [Finite V]
    {X A : Subgroup (MulAut V)} (hsol : Group.IsSolvable ↥X) (hO2 : pCoreOf 2 X = ⊥)
    (hAX : A ≤ X) (hA2 : IsPGroup 2 A) (hA1 : A ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ Cent (pCoreOf p X) A := by
  by_contra hcon
  push Not at hcon
  have hF : fittingOf X ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
    refine (fittingOf_le_oddFitting hO2).trans (iSup_le fun p => iSup_le fun hp => iSup_le
      fun hp2 => ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcon p hp hp2 x hx a ha)
  have hAF : A ≤ fittingOf X := by
    refine (le_inf hAX ?_).trans (centralizer_fittingOf_le_of_solvable hsol)
    rw [Subgroup.le_centralizer_iff]
    exact hF
  have hodd := odd_card_fittingOf hO2
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hA2 ⟨a, haA⟩
  have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact ha1' (orderOf_eq_one_iff.1 (by simpa using hj))
  have h2 : 2 ∣ orderOf a := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  have h3 : orderOf a ∣ Nat.card (fittingOf X) := Subgroup.orderOf_dvd_natCard _ (hAF haA)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans h3))

theorem exists_minimal_invariant {S Y A : Subgroup M}
    (hSY : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hSA : ¬ Cent S A) :
    ∃ P : Subgroup M, P ≤ S ∧ (∀ y ∈ Y, ∀ x ∈ P, y * x * y⁻¹ ∈ P) ∧ ¬ Cent P A ∧
      ∀ R : Subgroup M, R ≤ P → (∀ y ∈ Y, ∀ x ∈ R, y * x * y⁻¹ ∈ R) → ¬ Cent R A → R = P := by
  obtain ⟨P, ⟨hPS, hPY, hPA⟩, -, hmin⟩ := A6Min.exists_minimal
    (P := fun R => R ≤ S ∧ (∀ y ∈ Y, ∀ x ∈ R, y * x * y⁻¹ ∈ R) ∧ ¬ Cent R A) ⟨le_rfl, hSY, hSA⟩
  exact ⟨P, hPS, hPY, hPA, fun R hRP hRY hRA => hmin R ⟨hRP.trans hPS, hRY, hRA⟩ hRP⟩

end Gen

section Rank

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem pRank_range_le_two_of_odd (hF : HypF91 T V L V₁ Vp H) (hK : quasithinIsQTKECat G)
    {M : Type*} [Group M] [Finite M] (φ : ↥H →* M)
    (hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p φ.range ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQne : pCoreOf 2 H ≠ ⊥ := fun h0 =>
    hF.V₁_ne_bot (le_bot_iff.1 (h0 ▸ hF.V₁_le_pCoreOf))
  have hkerEq : φ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  let e : ↥φ.range ≃* ↥H ⧸ (pCoreOf 2 H).subgroupOf H :=
    (QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerEq)
  have hN : ¬ p ∣ Nat.card ↥((pCoreOf 2 H).subgroupOf H) := by
    have h2 : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf H) :=
      (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).symm
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    exact hp2 this
  rw [← pRank_top_subtype φ.range, CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    CFSG.SectionRank.pRank_quotient_eq _ hN, pRank_top_subtype]
  exact pRank_le_two_of_pCoreOf_ne_bot hK hQne hp hp2

end Rank

section Beta

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}
  {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem exists_conj_Vγ_le (hF : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g) :
    ∃ h ∈ H, conjSub h (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := hF.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂, hd⟩⟩ :=
    exists_nbrs_of_geodesic hF.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have hVγ := (hF.F913_2 s).2 γ₂ hγ₂ hd
  have hγ₀ : F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) := adj_γ₀_γ₁.symm
  obtain ⟨x, hx, hxγ⟩ := stab_transitive_on_nbrs hγ₂ hγ₀
  have hxH : (x : G) ∈ H := by rwa [stab_γ₁ hF.amalgamHypV.le₂] at hx
  refine ⟨x, hxH, ?_⟩
  have h1 : conjSub (x : G) (stab (F8.γ₁ T L H) ⊓ stab γ₂) =
      stab (F8.γ₀ T L H) ⊓ stab (F8.γ₁ T L H) := by
    rw [conjSub_inf, ← stab_smul, ← stab_smul, hxγ, smul_eq_of_mem_stab hx, inf_comm]
  calc conjSub (x : G) (F8.Uγ V H (g : G))
      ≤ conjSub (x : G) (pCoreOf 2 (stab (F8.γ₁ T L H) ⊓ stab γ₂)) := conjSub_mono _ hVγ
    _ = pCoreOf 2 (conjSub (x : G) (stab (F8.γ₁ T L H) ⊓ stab γ₂)) := (pCoreOf_conjSub _ _).symm
    _ = pCoreOf 2 (L₁Of L V₁ ⊔ T) := by rw [h1, hF.F913_1]

end Beta

end A6P

end CFSG.Quasithin.H13.A6

