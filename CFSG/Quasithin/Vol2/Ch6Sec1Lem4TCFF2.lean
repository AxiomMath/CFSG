module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFF1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TB

public section

namespace CFSG.Quasithin.H13.T614.FFStep

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_self (S : Subgroup G) :
    Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_centralizer_iff.mp hg
  constructor
  · intro hx
    have e : g * x * g⁻¹ = x := by
      have := h1 x hx
      calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [this]
        _ = x := by group
    rw [e]
    exact hx
  · intro hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
      calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * ((g * x * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [h1 _ hx]
        _ = g * x * g⁻¹ := by group
    have h3 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have e : g * x * g⁻¹ = x := h2.symm.trans h3.symm
    rw [e] at hx
    exact hx

theorem conj_mem_centralizer {S : Subgroup G} {n c : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
    (hc : c ∈ Subgroup.centralizer (S : Set G)) : n * c * n⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : n⁻¹ * r * n ∈ S := by
    refine (Subgroup.mem_normalizer_iff.mp hn _).mpr ?_
    have e : n * (n⁻¹ * r * n) * n⁻¹ = r := by group
    rw [e]
    exact hr
  have hc1 := Subgroup.mem_centralizer_iff.mp hc _ hr'
  calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [hc1]
    _ = n * c * n⁻¹ * r := by group

noncomputable def xSet {R : Subgroup G} (hV : IsElemAbelian 2 R) (H : Subgroup G) : Subgroup G :=
  ((pCoreOf 2 (autI hV H)).comap (convI hV)).map (Subgroup.normalizer (R : Set G)).subtype ⊓ H

theorem mem_xSet {R H : Subgroup G} (hV : IsElemAbelian 2 R) {g : G} :
    g ∈ xSet hV H ↔ g ∈ H ∧ ∃ hg : g ∈ Subgroup.normalizer (R : Set G),
      convI hV ⟨g, hg⟩ ∈ pCoreOf 2 (autI hV H) := by
  unfold xSet
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨x, hx, hxg⟩, hgH⟩
    subst hxg
    exact ⟨hgH, x.2, hx⟩
  · rintro ⟨hgH, hgN, hP⟩
    exact ⟨⟨⟨g, hgN⟩, hP, rfl⟩, hgH⟩

end Basic

section Step3

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_autI_eq_bot {K T R : Subgroup G} (hV : IsElemAbelian 2 R)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hsyl : IsSylowTwoOf T (K ⊔ T)) (hperf : Group.IsPerfect ↥K)
    (hsimp : IsSimpleGroup (ModO2 K))
    (hHN : K ⊔ T ≤ Subgroup.normalizer (R : Set G))
    (hQC : pCoreOf 2 (K ⊔ T) ≤ Subgroup.centralizer (R : Set G))
    (hKC : K ⊓ Subgroup.centralizer (R : Set G) = pCoreOf 2 K) :
    pCoreOf 2 (autI hV (K ⊔ T)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hperf
  haveI : IsSimpleGroup (ModO2 K) := hsimp
  set H : Subgroup G := K ⊔ T with hH
  have hTH : T ≤ H := le_sup_right
  have hKH : K ≤ H := le_sup_left
  have hKCR : pCoreOf 2 K ≤ Subgroup.centralizer (R : Set G) := by
    rw [← hKC]
    exact inf_le_right
  have hPK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  set P : Subgroup (MulAut (IntMod R hV)) := pCoreOf 2 (autI hV H) with hP
  have hPn : ∀ φ ∈ autI hV H, ∀ x ∈ P, φ * x * φ⁻¹ ∈ P := fun φ hφ x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (autI hV H) hφ) x).mp hx
  have hPp : ∀ x ∈ P, ∃ n : ℕ, x ^ 2 ^ n = 1 := fun x hx => by
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autI hV H) ⟨x, hx⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  set X : Subgroup G := xSet hV H with hXdef
  have hCX : ∀ g ∈ H, g ∈ Subgroup.centralizer (R : Set G) → g ∈ X := by
    intro g hgH hgC
    have hgN : g ∈ Subgroup.normalizer (R : Set G) := centralizer_le_normalizer_self R hgC
    refine (mem_xSet hV).mpr ⟨hgH, hgN, ?_⟩
    rw [(convI_eq_one_iff hV ⟨g, hgN⟩).mpr hgC]
    exact P.one_mem
  have hXH : X ≤ H := fun g hg => ((mem_xSet hV).mp hg).1
  have hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    intro h hh x hx
    obtain ⟨hxH, hxN, hxP⟩ := (mem_xSet hV).mp hx
    have hhN : h ∈ Subgroup.normalizer (R : Set G) := hHN hh
    have hN' : h * x * h⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hxN) (Subgroup.inv_mem _ hhN)
    rw [mem_xSet hV]
    refine ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), hN', ?_⟩
    have e : (⟨h * x * h⁻¹, hN'⟩ : ↥(Subgroup.normalizer (R : Set G))) =
        ⟨h, hhN⟩ * ⟨x, hxN⟩ * (⟨h, hhN⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hPn _ (convI_mem_autI hV hh hhN) _ hxP
  have hX2 : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ Subgroup.centralizer (R : Set G) := by
    intro x hx
    obtain ⟨_, hxN, hxP⟩ := (mem_xSet hV).mp hx
    obtain ⟨n, hn⟩ := hPp _ hxP
    refine ⟨n, ?_⟩
    have h1 : convI hV ((⟨x, hxN⟩ : ↥(Subgroup.normalizer (R : Set G))) ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact hn
    have h2 := (convI_eq_one_iff hV _).mp h1
    simpa using h2
  have hX0n : ((X ⊓ K).subgroupOf K).Normal := by
    constructor
    intro c hc g
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    obtain ⟨hcX, hcK⟩ := Subgroup.mem_inf.mp hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.mpr ⟨hXn _ (hKH g.2) _ hcX,
      K.mul_mem (K.mul_mem g.2 hcK) (K.inv_mem g.2)⟩
  set π : ↥K →* ModO2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set M : Subgroup (ModO2 K) := ((X ⊓ K).subgroupOf K).map π with hM
  have hMn : M.Normal := Subgroup.Normal.map hX0n π (QuotientGroup.mk'_surjective _)
  have hXK : X ⊓ K ≤ pCoreOf 2 K := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := ModO2 K) M with hM0 | hM1
    · intro c hc
      obtain ⟨hcX, hcK⟩ := Subgroup.mem_inf.mp hc
      have h1 : π ⟨c, hcK⟩ ∈ M :=
        Subgroup.mem_map.mpr ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
      rw [hM0, Subgroup.mem_bot] at h1
      have h2 : (⟨c, hcK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h1
      exact Subgroup.mem_map.mpr ⟨⟨c, hcK⟩, h2, rfl⟩
    · exfalso
      have hKX : K ≤ X := by
        intro k hk
        have hk1 : π ⟨k, hk⟩ ∈ M := by
          rw [hM1]
          exact Subgroup.mem_top _
        obtain ⟨x, hx, hπx⟩ := Subgroup.mem_map.mp hk1
        have hxX : (x : G) ∈ X := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
        have ho : (x⁻¹ * ⟨k, hk⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
          have h3 : π (x⁻¹ * ⟨k, hk⟩) = 1 := by
            rw [map_mul, map_inv, hπx, inv_mul_cancel]
          exact (QuotientGroup.eq_one_iff _).mp h3
        have hoG : ((x⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K :=
          Subgroup.mem_map.mpr ⟨_, ho, rfl⟩
        have hoX : ((x⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ X :=
          hCX _ (hKH (hPK hoG)) (hKCR hoG)
        have e : k = (x : G) * ((x⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by
          simp
        rw [e]
        exact X.mul_mem hxX hoX
      have hpg : IsPGroup 2 (ModO2 K) := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H k =>
          obtain ⟨n, hn⟩ := hX2 k (hKX k.2)
          refine ⟨n, ?_⟩
          have hkK : ((k : G) ^ 2 ^ n) ∈ K := K.pow_mem k.2 _
          have hmem : ((k : G) ^ 2 ^ n) ∈ pCoreOf 2 K := by
            rw [← hKC]
            exact Subgroup.mem_inf.mpr ⟨hkK, hn⟩
          obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
          have hyk : y = k ^ 2 ^ n := Subtype.ext (by simpa using hyeq)
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← hyk]
          exact hy
      haveI : Group.IsPerfect (ModO2 K) :=
        Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective _)
      obtain ⟨q, hq⟩ := exists_ne (1 : ModO2 K)
      exact hq (eq_one_of_isPGroup_of_isPerfect hpg q)
  have hXK' : X ⊓ K = pCoreOf 2 K :=
    le_antisymm hXK (le_inf (fun g hg => hCX g (hKH (hPK hg)) (hKCR hg)) hPK)
  have hXp : IsPGroup 2 ↥X := by
    intro y
    have hxX : (y : G) ∈ X := y.2
    have hxH : (y : G) ∈ H := hXH hxX
    have hxKT : (y : G) ∈ ((K ⊔ T : Subgroup G) : Set G) := hxH
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hxKT
    obtain ⟨k, hk, t, ht, hkt⟩ := hxKT
    obtain ⟨a, ha⟩ := hsyl.2.1 ⟨t, ht⟩
    have ht' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨k', hk', e⟩ := exists_pow_mul_eq614 hTK hk ht (2 ^ a)
    have hx2a : (y : G) ^ 2 ^ a = k' := by
      rw [← hkt, e, ht', mul_one]
    have hmemX : (y : G) ^ 2 ^ a ∈ X ⊓ K :=
      Subgroup.mem_inf.mpr ⟨X.pow_mem hxX _, by rw [hx2a]; exact hk'⟩
    rw [hXK'] at hmemX
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hmemX⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((y : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact hb'
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hXn h hh x hx
    · intro hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      have := hXn h⁻¹ (H.inv_mem hh) _ hx
      rw [e] at this
      exact this
  have hXQ : X ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXH hHX hXp
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hφ)
  have hgX : (g : G) ∈ X := (mem_xSet hV).mpr ⟨hgH, g.2, hφ⟩
  have hgC : (g : G) ∈ Subgroup.centralizer (R : Set G) := hQC (hXQ hgX)
  rw [Subgroup.mem_bot]
  exact (convI_eq_one_iff hV g).mpr hgC

end Step3

section Step4

variable {G : Type} [Group G] [Finite G]

theorem exists_offender {K T R : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (hKC : K ⊓ Subgroup.centralizer (R : Set G) = pCoreOf 2 K)
    (hJ : ¬ thompsonJ T ≤ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (R : Set G) ∧
      ∃ a ∈ A, ∃ u ∈ K, a * u * a⁻¹ * u⁻¹ ∉ pCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hAnot⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K := by
    by_contra hcon
    push Not at hcon
    exact hJ (iSup₂_le fun A hA => hcon A hA)
  obtain ⟨a, haA, haCM⟩ := SetLike.not_le_iff_exists.mp hAnot
  have haT : a ∈ T := hA.1 haA
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hTK haT
  have hu : ∃ u ∈ K, a * u * a⁻¹ * u⁻¹ ∉ pCoreOf 2 K := by
    by_contra hcon
    push Not at hcon
    apply haCM
    exact ⟨haN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K haN,
      fun u hu => hcon u hu⟩
  obtain ⟨u, hu, huN⟩ := hu
  refine ⟨A, hA, ?_, a, haA, u, hu, huN⟩
  intro hAC
  apply haCM
  refine ⟨haN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K haN, ?_⟩
  intro u' hu'
  have h1 : u' * a⁻¹ * u'⁻¹ ∈ Subgroup.centralizer (R : Set G) :=
    conj_mem_centralizer (hKR hu') (Subgroup.inv_mem _ (hAC haA))
  have hcomm : a * u' * a⁻¹ * u'⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    have e : a * u' * a⁻¹ * u'⁻¹ = a * (u' * a⁻¹ * u'⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hAC haA) h1
  have hKmem : a * u' * a⁻¹ * u'⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp haN u').mp hu') (K.inv_mem hu')
  rw [← hKC]
  exact Subgroup.mem_inf.mpr ⟨hKmem, hcomm⟩

end Step4


end CFSG.Quasithin.H13.T614.FFStep
