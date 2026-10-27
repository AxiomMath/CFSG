module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCRank
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCLift
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCAct

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer614 (S : Subgroup G) :
    Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (S : Set G) := by
  have fwd : ∀ y ∈ Subgroup.centralizer (S : Set G), ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have hc := (Subgroup.mem_centralizer_iff.mp hy) s hs
    have e : y * s * y⁻¹ = s := by
      rw [← hc]
      group
    rw [e]
    exact hs
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    exact fwd g hg s hs
  · intro hs
    have := fwd g⁻¹ (Subgroup.inv_mem _ hg) _ hs
    have e : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
    rwa [e] at this

theorem zV_le_pCoreOf614 {T M L V : Subgroup G} (h : Hyp611 G T M L V 4)
    (hZV : Nat.card ↥(ZV614 T L V) = 4) :
    ZV614 T L V ≤ pCoreOf 2 (Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G)) := by
  have hp : IsPGroup 2 ↥(ZV614 T L V) := by
    rintro ⟨z, hz⟩
    refine ⟨1, ?_⟩
    have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
    have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
    apply Subtype.ext
    simpa using hz2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.le_normalizer)
    le_rfl hp

theorem pCoreOf_le_Aprime614 {K : Subgroup G} {E : Subgroup (ModO2 K)} (hE1 : (1 : ModO2 K) ∈ E) :
    pCoreOf 2 K ≤ Aprime614 K E := by
  intro n hn
  have hnK : n ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hn
  refine Subgroup.mem_map.mpr ⟨⟨n, hnK⟩, ?_, rfl⟩
  show mk614 K ⟨n, hnK⟩ ∈ E
  rw [mk614_eq_one_of_mem_pCoreOf hnK hn]
  exact hE1

theorem step7_false614 (hB : TitsBasicFact) {T M L V K : Subgroup G} {E : Subgroup (ModO2 K)}
    (h : Hyp611 G T M L V 4) (htits : IsTits (ModO2 K))
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 9)
    (hKZ : K ≤ Subgroup.centralizer ((ZV614 T L V : Subgroup G) : Set G))
    (hZV : Nat.card ↥(ZV614 T L V) = 4)
    {d : G} (hord : orderOf d = 3) (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hdTL : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hΦ : actModO2_614 K ⟨d, hdK⟩ = 1)
    (hdec : ∀ f ∈ Aprime614 K E ⊔ Subgroup.zpowers d,
      ∃ a ∈ Aprime614 K E, ∃ i : ℕ, i < 3 ∧ f = a * d ^ i)
    (hcardF : Nat.card ↥(Aprime614 K E ⊔ Subgroup.zpowers d) = 3 * Nat.card ↥(Aprime614 K E))
    (hcommF : ∀ f ∈ Aprime614 K E ⊔ Subgroup.zpowers d, ∀ g ∈ Aprime614 K E ⊔ Subgroup.zpowers d,
      f * g * (g * f)⁻¹ ∈ Aprime614 K E)
    (hexpF : ∀ f ∈ Aprime614 K E ⊔ Subgroup.zpowers d, f ^ 3 ∈ Aprime614 K E) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : d ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one d
  have hdK' : d ∉ K := by
    intro hdKm
    have h0 : actModO2_614 K ⟨d, hdK⟩ = MulAut.conj (mk614 K ⟨d, hdKm⟩) :=
      actModO2_614_of_mem K hdKm
    have h1 : MulAut.conj (mk614 K ⟨d, hdKm⟩) = MulAut.conj (1 : ModO2 K) := by
      rw [map_one, ← h0, hΦ]
    have hm : mk614 K ⟨d, hdKm⟩ = 1 := conj_inj614 (hB _ htits).2.2 h1
    have hpc := mem_pCoreOf_of_mk614_eq_one hdKm hm
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hpc⟩
    have hdk : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd := orderOf_dvd_of_pow_eq_one hdk
    rw [hord] at hdvd
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32
  have hA'K : Aprime614 K E ≤ K := aprime_le_K614 E
  have hFK : Aprime614 K E ⊔ Subgroup.zpowers d ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer (hA'K hx)) (Subgroup.zpowers_le.mpr hdK)
  have hPhi : ∀ f (hf : f ∈ Aprime614 K E ⊔ Subgroup.zpowers d), ∃ x ∈ E,
      actModO2_614 K ⟨f, hFK hf⟩ = MulAut.conj x := by
    intro f hf
    obtain ⟨a, ha, i, hi, rfl⟩ := hdec _ hf
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
    have haK : a ∈ K := hA'K ha
    refine ⟨mk614 K ⟨a, haK⟩, ?_, ?_⟩
    · have hay : (⟨a, haK⟩ : ↥K) = y := Subtype.ext hya.symm
      rw [hay]
      exact hy
    · have e : (⟨a * d ^ i, hFK hf⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨a, Subgroup.le_normalizer haK⟩ * ⟨d, hdK⟩ ^ i :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_pow, hΦ, one_pow, mul_one]
      exact actModO2_614_of_mem K haK
  have hcommN : ∀ f ∈ Aprime614 K E ⊔ Subgroup.zpowers d,
      ∀ g ∈ Aprime614 K E ⊔ Subgroup.zpowers d, f * g * (g * f)⁻¹ ∈ pCoreOf 2 K := by
    intro f hf g hg
    have hc := hcommF f hf g hg
    have hcK : f * g * (g * f)⁻¹ ∈ K := hA'K hc
    obtain ⟨x, hx, hfx⟩ := hPhi f hf
    obtain ⟨y, hy, hgy⟩ := hPhi g hg
    have hxy : x * y = y * x := by
      have := hEel.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩
      exact congrArg Subtype.val this
    have hel : (⟨f * g * (g * f)⁻¹, Subgroup.le_normalizer hcK⟩ :
        ↥(Subgroup.normalizer (K : Set G))) =
        ⟨f, hFK hf⟩ * ⟨g, hFK hg⟩ * (⟨g, hFK hg⟩ * ⟨f, hFK hf⟩)⁻¹ :=
      Subtype.ext (by simp)
    have hΦ1 : actModO2_614 K ⟨f * g * (g * f)⁻¹, Subgroup.le_normalizer hcK⟩ = 1 := by
      rw [hel, map_mul, map_mul, map_inv, map_mul, hfx, hgy]
      simp only [← map_mul, ← map_inv, hxy, mul_inv_cancel, map_one]
    have hm : mk614 K ⟨f * g * (g * f)⁻¹, hcK⟩ = 1 :=
      conj_inj614 (hB _ htits).2.2 (by
        rw [map_one]
        exact (actModO2_614_of_mem K hcK).symm.trans hΦ1)
    exact mem_pCoreOf_of_mk614_eq_one hcK hm
  have hexpN : ∀ f ∈ Aprime614 K E ⊔ Subgroup.zpowers d, f ^ 3 ∈ pCoreOf 2 K := by
    intro f hf
    have hcK : f ^ 3 ∈ K := hA'K (hexpF f hf)
    obtain ⟨x, hx, hfx⟩ := hPhi f hf
    have hx3 : x ^ 3 = 1 := hEel.2 x hx
    have hel : (⟨f ^ 3, Subgroup.le_normalizer hcK⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨f, hFK hf⟩ ^ 3 := Subtype.ext (by simp)
    have hΦ3 : actModO2_614 K ⟨f ^ 3, Subgroup.le_normalizer hcK⟩ = 1 := by
      rw [hel, map_pow, hfx, ← map_pow, hx3, map_one]
    have hm : mk614 K ⟨f ^ 3, hcK⟩ = 1 :=
      conj_inj614 (hB _ htits).2.2 (by
        rw [map_one]
        exact (actModO2_614_of_mem K hcK).symm.trans hΦ3)
    exact mem_pCoreOf_of_mk614_eq_one hcK hm
  have hNn : ((pCoreOf 2 K).subgroupOf (Aprime614 K E ⊔ Subgroup.zpowers d)).Normal := by
    constructor
    intro n hn f
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hfK : (f : G) ∈ Subgroup.normalizer (K : Set G) := hFK f.2
    have hnK : (n : G) ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hn
    have hfnK : (f : G) * (n : G) * (f : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hfK (n : G)).mp hnK
    have hmk1 : ((⟨(n : G), hnK⟩ : ↥K) : ModO2 K) = 1 := mk614_eq_one_of_mem_pCoreOf hnK hn
    have hmk2 : mk614 K ⟨(f : G) * (n : G) * (f : G)⁻¹, hfnK⟩ = 1 := by
      have := actModO2_614_mk K ⟨(f : G), hfK⟩ ⟨(n : G), hnK⟩
      rw [hmk1, map_one] at this
      exact this.symm
    have hfn := mem_pCoreOf_of_mk614_eq_one hfnK hmk2
    simpa using hfn
  have hNF : pCoreOf 2 K ≤ Aprime614 K E ⊔ Subgroup.zpowers d :=
    le_sup_of_le_left (pCoreOf_le_Aprime614 (E := E) (E.one_mem))
  have hcard27 : Nat.card ↥(Aprime614 K E ⊔ Subgroup.zpowers d) = 27 * Nat.card ↥(pCoreOf 2 K) := by
    rw [hcardF, card_Aprime614 hEcard]
    ring
  obtain ⟨S, hSF, hSab, hSexp, hScard⟩ :=
    CFSG.Quasithin.H13.T614.Lift.exists_elemAbelian27_of_mod2 hNF hNn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      (fun f hf g hg => by
        have e : f * g * f⁻¹ * g⁻¹ = f * g * (g * f)⁻¹ := by group
        rw [e]
        exact hcommN f hf g hg)
      (fun f hf => hexpN f hf) hcard27
  have hFH : Aprime614 K E ⊔ Subgroup.zpowers d ≤
      Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G) :=
    sup_le (fun x hx => centralizer_le_normalizer614 _ (hKZ (hA'K hx)))
      (Subgroup.zpowers_le.mpr (normalizer_ZV614 hdV hdTL))
  have hr3 : 3 ≤ CFSG.Open.pRank 3
      (Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G)) :=
    CFSG.Quasithin.le_pRank Nat.prime_three (hSF.trans hFH) ⟨hSab, hSexp⟩ (k := 3)
      (by rw [hScard]; norm_num)
  have hpH : pCoreOf 2 (Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G)) ≠ ⊥ := by
    intro h0
    have hle := zV_le_pCoreOf614 h hZV
    rw [h0, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hZV
    norm_num at hZV
  have hr2 := CFSG.Quasithin.EmptyFaithfulMultiple.pRank_le_two_of_pCoreOf_ne_bot_cat
    h.qtke hpH Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.H13.T614

end
