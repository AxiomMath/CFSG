module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34A126GL2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsOddAb
public import CFSG.Quasithin.Background.A1bLemma126
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
public import CFSG.RankThree.PartOne.S9.Extraction.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Quasithin
open CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem centralizes_pCoreOf_of_coprime_six [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {H X V : Subgroup G} (hXH : X ≤ H) (hVH : V ≤ H) (hV2 : IsPGroup 2 V) (hVX : ⁅V, X⁆ = V)
    (hX6 : Subgroup.closure {x | x ∈ X ∧ Nat.Coprime (orderOf x) 6} = X)
    (hr : CFSG.Open.pRank p (pCoreOf p H) ≤ 2) :
    V ≤ Subgroup.centralizer (pCoreOf p H : Set G) := by
  classical
  have hPp : IsPGroup p (pCoreOf p H) := pCoreOf_isPGroup p H
  have hHN : H ≤ Subgroup.normalizer (pCoreOf p H : Set G) := le_normalizer_pCoreOf p H
  let ρ : H →* MulAut (pCoreOf p H) := conjAut hHN
  obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_pCore_aut hp2 hPp
    (by rw [pRank_top_subtype]; exact hr)
  let θ : H →* GL (Fin 2) (ZMod p) := φ.comp ρ
  by_contra hV
  obtain ⟨v, hv, hvC⟩ := IsConcreteLE.not_le_iff_exists.1 hV
  have hvH : v ∈ H := hVH hv
  have hρne : ρ ⟨v, hvH⟩ ≠ 1 := by
    intro h1
    apply hvC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 : v * x * v⁻¹ = x := by
      have h3 : ((ρ ⟨v, hvH⟩ ⟨x, hx⟩ : pCoreOf p H) : G) = v * x * v⁻¹ := rfl
      have h4 : ((ρ ⟨v, hvH⟩ ⟨x, hx⟩ : pCoreOf p H) : G) = x := by rw [h1]; rfl
      exact h3.symm.trans h4
    calc x * v = (v * x * v⁻¹) * v := by rw [h2]
      _ = v * x := by group
  have hθne : θ ⟨v, hvH⟩ ≠ 1 := by
    intro h1
    have hker : ρ ⟨v, hvH⟩ ∈ φ.ker := h1
    rw [hφ] at hker
    have hpg : IsPGroup p (CFSG.Open.pCore p (MulAut (pCoreOf p H))) :=
      CFSG.LieType.BorelTits.pCore_isPGroup p
    obtain ⟨l, hl⟩ := hpg ⟨_, hker⟩
    obtain ⟨k, hk⟩ := hV2 ⟨v, hv⟩
    have h2 : (ρ ⟨v, hvH⟩) ^ (p ^ l) = 1 := by simpa using congrArg Subtype.val hl
    have h3 : (ρ ⟨v, hvH⟩) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      have : (⟨v, hvH⟩ : H) ^ (2 ^ k) = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hk
      rw [this, map_one]
    have hc : Nat.Coprime (p ^ l) (2 ^ k) :=
      Nat.Coprime.pow l k ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
    have := pow_gcd_eq_one.2 ⟨h2, h3⟩
    rw [hc.gcd_eq_one, pow_one] at this
    exact hρne this
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_commutator_eq_finite hVX
  let Vθ : Subgroup (GL (Fin 2) (ZMod p)) := (V.subgroupOf H).map θ
  have hVθ2 : IsPGroup 2 Vθ := by
    have h1 : IsPGroup 2 (V.subgroupOf H) :=
      hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
    exact h1.map θ
  have h2p : (2 : ZMod p) ≠ 0 := GL2.two_ne_zero_zmod hp2
  have hsix : ∀ (x : G) (hx : x ∈ X), (orderOf x).Coprime 6 → ∀ a ∈ Vθ,
      θ ⟨x, hXH hx⟩ * a = a * θ ⟨x, hXH hx⟩ := by
    intro x hx hx6 a ha
    have hxH : x ∈ H := hXH hx
    refine GL2Six.commute_of_normalizes_of_coprime_six h2p hVθ2 ?_ ?_ ha
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : (w : G) ∈ V := hw
      have hmem : x * (w : G) * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXN hx) _).1 hw'
      refine ⟨⟨x, hxH⟩ * w * ⟨x, hxH⟩⁻¹, hmem, ?_⟩
      simp [map_mul, map_inv]
    · have h1 : orderOf (θ ⟨x, hxH⟩) ∣ orderOf (⟨x, hxH⟩ : H) := orderOf_map_dvd θ _
      rw [Subgroup.orderOf_mk] at h1
      exact Nat.Coprime.coprime_dvd_left h1 hx6
  let K : Subgroup G :=
    ((Subgroup.centralizer (Vθ : Set (GL (Fin 2) (ZMod p)))).comap θ).map H.subtype
  have hXK : X ≤ K := by
    rw [← hX6, Subgroup.closure_le]
    rintro x ⟨hxX, hx6⟩
    refine ⟨⟨x, hXH hxX⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hsix x hxX hx6 a ha).symm
  have hVker : V ≤ θ.ker.map H.subtype := by
    calc V = ⁅V, X⁆ := hVX.symm
      _ ≤ θ.ker.map H.subtype := by
        refine Subgroup.commutator_le.2 fun w hw x hx => ?_
        have hwH : w ∈ H := hVH hw
        have hxH : x ∈ H := hXH hx
        refine ⟨⟨⁅w, x⁆, H.mul_mem (H.mul_mem (H.mul_mem hwH hxH) (H.inv_mem hwH))
          (H.inv_mem hxH)⟩, ?_, rfl⟩
        obtain ⟨y, hy, hyx⟩ := hXK hx
        have hyx' : y = ⟨x, hxH⟩ := Subtype.ext hyx
        rw [hyx', SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hy
        have hcomm := hy (θ ⟨w, hwH⟩) ⟨⟨w, hwH⟩, hw, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        have e : (⟨⁅w, x⁆, H.mul_mem (H.mul_mem (H.mul_mem hwH hxH) (H.inv_mem hwH))
          (H.inv_mem hxH)⟩ : H) = ⟨w, hwH⟩ * ⟨x, hxH⟩ * ⟨w, hwH⟩⁻¹ * ⟨x, hxH⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [hcomm]
        group
  obtain ⟨y, hy, hyv⟩ := hVker hv
  have hyv' : y = ⟨v, hvH⟩ := Subtype.ext hyv
  rw [hyv'] at hy
  exact hθne hy


theorem a126TwoFact_holds : A126TwoFact := by
  intro G _ _ H X V hXH hX hVH hV2 hVX hsolv hrank hX6
  have _ := hX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup ↥H := CFSG.pCore 2 ↥H with hQ
  set π : ↥H →* ↥H ⧸ Q := QuotientGroup.mk' Q with hπ
  set V₁ : Subgroup (↥H ⧸ Q) := (V.subgroupOf H).map π with hV₁
  set X₁ : Subgroup (↥H ⧸ Q) := (X.subgroupOf H).map π with hX₁
  have hV₁2 : IsPGroup 2 V₁ := (hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm).map π
  have hVX' : ⁅V.subgroupOf H, X.subgroupOf H⁆ = V.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVH,
      Subgroup.map_subgroupOf_eq_of_le hXH, hVX]
  have hV₁X₁ : ⁅V₁, X₁⁆ = V₁ := by
    rw [hV₁, hX₁, ← Subgroup.map_commutator, hVX']
  have hX' : X.subgroupOf H =
      Subgroup.closure {x : ↥H | (x : G) ∈ X ∧ Nat.Coprime (orderOf x) 6} := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hXH, MonoidHom.map_closure]
    conv_lhs => rw [← hX6]
    congr 1
    ext x
    constructor
    · rintro ⟨hxX, hx6⟩
      refine ⟨⟨x, hXH hxX⟩, ⟨hxX, ?_⟩, rfl⟩
      rwa [Subgroup.orderOf_mk]
    · rintro ⟨y, ⟨hyX, hy6⟩, rfl⟩
      refine ⟨hyX, ?_⟩
      rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  have hX₁6 : Subgroup.closure {x | x ∈ X₁ ∧ Nat.Coprime (orderOf x) 6} = X₁ := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
    · rw [hX₁, hX', MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨hyX, hy6⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rw [← MonoidHom.map_closure, ← hX']
        exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hyX)
      · exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd π y) hy6
  have hrΓ : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (pCoreOf p (⊤ : Subgroup (↥H ⧸ Q))) ≤ 2 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have hQp : ¬ p ∣ Nat.card Q := by
      intro hdvd
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
      rw [hn] at hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    calc CFSG.Open.pRank p (pCoreOf p (⊤ : Subgroup (↥H ⧸ Q)))
        ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ Q)) := CFSG.SectionRank.pRank_mono hp.one_lt le_top
      _ = CFSG.Open.pRank p (⊤ : Subgroup ↥H) := CFSG.SectionRank.pRank_quotient_eq Q hQp
      _ = CFSG.Open.pRank p H := pRank_top_subtype H
      _ ≤ 2 := hrank p hp hp2
  have hcent : ∀ p : ℕ, p.Prime → p ≠ 2 →
      V₁ ≤ Subgroup.centralizer (pCoreOf p (⊤ : Subgroup (↥H ⧸ Q)) : Set (↥H ⧸ Q)) := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    exact centralizes_pCoreOf_of_coprime_six hp2 le_top le_top hV₁2 hV₁X₁ hX₁6 (hrΓ p hp hp2)
  have hO2 : CFSG.pCore 2 (↥H ⧸ Q) = ⊥ := CFSG.RankThree.PartOne.Extract.pCore_two_quotient_eq_bot
  have : Group.IsSolvable ↥H := hsolv
  have hF : CFSG.fittingSubgroup (↥H ⧸ Q) ≤ Subgroup.centralizer (V₁ : Set (↥H ⧸ Q)) := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    have hqp : (q.1.1).Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : q.1.1 = 2
    · rw [hq2, hO2]
      exact bot_le
    · have h := hcent q.1.1 hqp hq2
      rw [pCoreOf_top] at h
      exact Subgroup.le_centralizer_iff.mp h
  have hVF : V₁ ≤ CFSG.fittingSubgroup (↥H ⧸ Q) :=
    (Subgroup.le_centralizer_iff.mpr hF).trans
      (CFSG.RankThree.PGroups.solvable_fitting_self_centralizing _)
  have hV₁bot : V₁ = ⊥ := by
    have h := CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore V₁
      (CFSG.fittingSubgroup (↥H ⧸ Q)) 2 Nat.prime_two hV₁2 inferInstance inferInstance
    rw [inf_eq_left.mpr hVF, hO2] at h
    exact le_bot_iff.mp h
  have hVQ : V.subgroupOf H ≤ Q := by
    intro v hv
    have h := Subgroup.mem_map_of_mem π hv
    rw [← hV₁, hV₁bot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h
    exact h
  intro v hv
  refine ⟨⟨v, hVH hv⟩, ?_, rfl⟩
  have h := hVQ (show (⟨v, hVH hv⟩ : ↥H) ∈ V.subgroupOf H from hv)
  rw [hQ] at h
  exact h

end CFSG.Quasithin.H13
