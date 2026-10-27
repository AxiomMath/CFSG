module

public import CFSG.Quasithin.Background.A1bGL2
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.Open.FusionDefs
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isElemAbelian_of_frattiniIn_eq_bot [Finite G] {p : ℕ} [Fact p.Prime] {V : Subgroup G}
    (hV : IsPGroup p V) (hΦ : frattiniIn V = ⊥) : IsElemAbelian p V := by
  have hfr : frattini V = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 hΦ
  obtain ⟨-, hcomm, hpow⟩ := frattini_quotient_elementary hV
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have h := hcomm (QuotientGroup.mk x) (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h
    have h2 := QuotientGroup.eq.1 h
    rw [hfr, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  · have h := hpow (QuotientGroup.mk (⟨x, hx⟩ : V))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hfr, Subgroup.mem_bot] at h
    simpa using congrArg Subtype.val h

theorem le_normalizer_of_commutator_eq_finite [Finite G] {V X : Subgroup G} (h : ⁅V, X⁆ = V) :
    X ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  refine mem_normalizer_of_conj_mem fun v hv => ?_
  have h1 : ⁅v⁻¹, x⁆ ∈ ⁅V, X⁆ := Subgroup.commutator_mem_commutator (V.inv_mem hv) hx
  rw [h] at h1
  have h2 := V.mul_mem hv h1
  simpa [commutatorElement_def, mul_assoc] using h2

theorem centralizes_pCoreOf [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {H X V : Subgroup G} (hXH : X ≤ H) (hX : opResidual 2 X = X) (hVH : V ≤ H)
    (hV2 : IsPGroup 2 V) (hVX : ⁅V, X⁆ = V) (hVel : IsElemAbelian 2 V)
    (hr : pRank p (pCoreOf p H) ≤ 2) : V ≤ Subgroup.centralizer (pCoreOf p H : Set G) := by
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
  have hA2 : ∀ a ∈ Vθ, a * a = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ V := hw
    have : w ^ 2 = 1 := Subtype.ext (by simpa using hVel.2 w hw')
    rw [← map_mul, ← pow_two, this, map_one]
  have hAc : ∀ a ∈ Vθ, ∀ b ∈ Vθ, a * b = b * a := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    have h1 : (w : G) ∈ V := hw
    have h2 : (w' : G) ∈ V := hw'
    have := hVel.1
    have h3 : w * w' = w' * w :=
      Subtype.ext (congrArg (fun z : V => (z : G)) (mul_comm' (⟨w, h1⟩ : V) ⟨w', h2⟩))
    rw [← map_mul, ← map_mul, h3]
  have hodd : ∀ (x : G) (hx : x ∈ X), (orderOf x).Coprime 2 → ∀ a ∈ Vθ,
      θ ⟨x, hXH hx⟩ * a = a * θ ⟨x, hXH hx⟩ := by
    intro x hx hx2 a ha
    have hxH : x ∈ H := hXH hx
    refine GL2.centralizes_of_odd_order hp2 hA2 hAc ?_ ?_ ha
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : (w : G) ∈ V := hw
      have hmem : x * (w : G) * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXN hx) _).1 hw'
      refine ⟨⟨x, hxH⟩ * w * ⟨x, hxH⟩⁻¹, hmem, ?_⟩
      simp [map_mul, map_inv]
    · have h1 : orderOf (θ ⟨x, hxH⟩) ∣ orderOf (⟨x, hxH⟩ : H) := orderOf_map_dvd θ _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat (Nat.coprime_two_right.1 hx2) h1
  let K : Subgroup G :=
    ((Subgroup.centralizer (Vθ : Set (GL (Fin 2) (ZMod p)))).comap θ).map H.subtype
  have hXK : X ≤ K := by
    calc X = opResidual 2 X := hX.symm
      _ ≤ K := by
        unfold opResidual
        rw [Subgroup.closure_le]
        rintro x ⟨hxX, hx2⟩
        refine ⟨⟨x, hXH hxX⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro a ha
        exact (hodd x hxX hx2 a ha).symm
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

theorem centralizes_of_normal_odd [Finite G] {H V N : Subgroup G} (hVH : V ≤ H)
    (hV2 : IsPGroup 2 V) (hq : ∀ q : ℕ, q.Prime → q ≠ 2 →
      V ≤ Subgroup.centralizer (pCoreOf q H : Set G))
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (hNodd : Odd (Nat.card N)) :
    V ≤ Subgroup.centralizer (N : Set G) := by
  classical
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hNn
  let ψ : H →* MulAut N := conjAut hHN
  have hsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard N hNodd
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hvH : v ∈ H := hVH hv
  obtain ⟨k, hk⟩ := hV2 ⟨v, hv⟩
  set φ : MulAut N := ψ ⟨v, hvH⟩ with hφ
  have hpow : φ ^ (2 ^ k) = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨v, hvH⟩ : H) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.fittingSubgroup N)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact Odd.of_dvd_nat hNodd (Subgroup.card_subgroup_dvd_card _)
  have hfix : ∀ x ∈ CFSG.fittingSubgroup N, φ x = x := by
    have hle : CFSG.fittingSubgroup N ≤ MonoidHom.eqLocus (φ : N →* N) (MonoidHom.id N) := by
      rw [CFSG.fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      have hqp : (q.1.1).Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hqd : q.1.1 ∣ Nat.card N := Nat.dvd_of_mem_primeFactors q.1.2
      have hq2 : q.1.1 ≠ 2 := by
        intro h2
        rw [h2] at hqd
        exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 hqd)
      have hqfact : Fact (q.1.1).Prime := ⟨hqp⟩
      have hK : (CFSG.pCore q.1.1 N).map N.subtype ≤ pCoreOf q.1.1 H := by
        have hQp : IsPGroup q.1.1 ((CFSG.pCore q.1.1 N).map N.subtype) :=
          (CFSG.pCore_isPGroup).map N.subtype
        refine le_pCoreOf_of_le_normalizer q.1.1 ((Subgroup.map_subtype_le _).trans hNH) ?_ hQp
        intro h hh
        refine mem_normalizer_of_conj_mem fun k hk => ?_
        obtain ⟨y, hy, rfl⟩ := hk
        have h1 : ψ ⟨h, hh⟩ y ∈ CFSG.pCore q.1.1 N := by
          have := CFSG.pCore_map_iso q.1.1 (ψ ⟨h, hh⟩)
          rw [← this]
          exact Subgroup.mem_map_of_mem _ hy
        exact ⟨ψ ⟨h, hh⟩ y, h1, rfl⟩
      intro x hx
      have hxK : (x : G) ∈ pCoreOf q.1.1 H := hK ⟨x, hx, rfl⟩
      have hvc := hq q.1.1 hqp hq2 hv
      rw [Subgroup.mem_centralizer_iff] at hvc
      have h3 := hvc _ hxK
      show φ x = x
      apply Subtype.ext
      show v * (x : G) * v⁻¹ = x
      rw [← h3]
      group
    intro x hx
    exact hle hx
  have hone : φ = 1 := CFSG.mulAut_eq_one_of_fixes_fittingSubgroup N hsolv φ (2 ^ k) hpow hcop hfix
  have h1 := congrArg (fun a : MulAut N => ((a ⟨n, hn⟩ : N) : G)) hone
  have h2 : v * n * v⁻¹ = n := h1
  calc n * v = (v * n * v⁻¹) * v := by rw [h2]
    _ = v * n := by group

theorem a126_one [Finite G] {H X V : Subgroup G} (hXH : X ≤ H) (hX : opResidual 2 X = X)
    (hVH : V ≤ H) (hV2 : IsPGroup 2 V) (hVX : ⁅V, X⁆ = V)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p (pCoreOf p H) ≤ 2)
    (hΦ : frattiniIn V = ⊥) : V ≤ Subgroup.centralizer (fusionOddCoreOf H : Set G) := by
  classical
  have hVel : IsElemAbelian 2 V := isElemAbelian_of_frattiniIn_eq_bot hV2 hΦ
  have hq : ∀ q : ℕ, q.Prime → q ≠ 2 →
      V ≤ Subgroup.centralizer (pCoreOf q H : Set G) := fun q hq hq2 => by
    have : Fact q.Prime := ⟨hq⟩
    exact centralizes_pCoreOf hq2 hXH hX hVH hV2 hVX hVel (hrank q hq hq2)
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hvH : v ∈ H := hVH hv
  have hle : fusionOddCore H ≤ Subgroup.centralizer ({(⟨v, hvH⟩ : H)} : Set H) := by
    refine sSup_le fun N hN x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hN'H : N.map H.subtype ≤ H := Subgroup.map_subtype_le N
    have hsub : (N.map H.subtype).subgroupOf H = N :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
    have hN'n : ((N.map H.subtype).subgroupOf H).Normal := by
      rw [hsub]
      exact hN.1
    have hN'odd : Odd (Nat.card (N.map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hN.2
    have hcent := centralizes_of_normal_odd hVH hV2 hq hN'H hN'n hN'odd
    have h1 := Subgroup.mem_centralizer_iff.1 (hcent hv) (x : G) ⟨x, hx, rfl⟩
    exact Subtype.ext h1.symm
  have := Subgroup.mem_centralizer_iff.1 (hle hy) ⟨v, hvH⟩ rfl
  exact (congrArg Subtype.val this).symm

end CFSG.Quasithin
