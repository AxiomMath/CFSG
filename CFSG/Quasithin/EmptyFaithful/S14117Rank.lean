module

public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Quasithin.EmptyFaithful.S14117Star
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise

section Abstract

variable {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]

theorem isCyclic_sylow_centralizer_of_faithful (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ 2) {r : Q} (hr1 : r ≠ 1)
    (hr2 : ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hfaith : Subgroup.zpowers r ⊓ Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q) = ⊥)
    {Cr : Subgroup Q} (hCr : Cr = Subgroup.centralizer ({r} : Set Q)) (P : Sylow p ↥Cr) :
    IsCyclic ↥(P : Subgroup ↥Cr) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set Qp : Subgroup Q := CFSG.Open.pCore p Q with hQp
  have hQpn : Qp.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hQpp : IsPGroup p Qp := CFSG.LieType.BorelTits.pCore_isPGroup p
  set P₀ : Subgroup Q := (P : Subgroup ↥Cr).map Cr.subtype with hP₀
  have hP₀p : IsPGroup p P₀ := P.isPGroup'.map Cr.subtype
  have hP₀r : ∀ x ∈ P₀, x * r = r * x := by
    rintro _ ⟨y, -, rfl⟩
    have hy : (y : Q) ∈ Subgroup.centralizer ({r} : Set Q) := hCr ▸ y.2
    exact (Subgroup.mem_centralizer_iff.mp hy r (Set.mem_singleton r)).symm
  set P' : Subgroup Q := Qp ⊔ P₀ with hP'
  have hQpN : Subgroup.normalizer (Qp : Set Q) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hQpn
  have hP'p : IsPGroup p P' :=
    IsPGroup.to_sup_of_normal_left' hQpp hP₀p (by rw [hQpN]; exact le_top)
  have hrN : r ∈ Subgroup.normalizer (P' : Set Q) :=
    Subgroup.inf_normalizer_le_normalizer_sup Qp P₀
      ⟨by rw [hQpN]; exact Subgroup.mem_top r,
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hP₀r)⟩
  set Gb : Subgroup Q := P' ⊔ Subgroup.zpowers r with hGb
  have hzN : Subgroup.zpowers r ≤ Subgroup.normalizer (P' : Set Q) := Subgroup.zpowers_le.mpr hrN
  have hGbmul : (Gb : Set Q) = (P' : Set Q) * (Subgroup.zpowers r : Set Q) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P' _ hzN
  have hGbN : Gb ≤ Subgroup.normalizer (P' : Set Q) := sup_le Subgroup.le_normalizer hzN
  have hP'Gb : P' ≤ Gb := le_sup_left
  have hrGb : r ∈ Gb := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  have hdec : ∀ g ∈ Gb, ∃ x ∈ P', ∃ c ∈ Subgroup.zpowers r, g = x * c := by
    intro g hg
    have : g ∈ (P' : Set Q) * (Subgroup.zpowers r : Set Q) := by rw [← hGbmul]; exact hg
    obtain ⟨x, hx, c, hc, rfl⟩ := this
    exact ⟨x, hx, c, hc, rfl⟩
  obtain ⟨m, hm⟩ := hr2
  have hcent : ∀ g ∈ Gb, (∀ a ∈ P', a * g = g * a) → g ∈ P' := by
    intro g hg hgc
    obtain ⟨x, hxP, c, hcz, rfl⟩ := hdec g hg
    have hxc : x * c = c * x := by
      have h1 := hgc x hxP
      have h2 : x * (x * c) = x * (c * x) := by rw [h1, mul_assoc]
      exact mul_left_cancel h2
    have hcm : c ^ 2 ^ m = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]
    have hgpow : (x * c) ^ 2 ^ m = x ^ 2 ^ m := by
      rw [(show Commute x c from hxc).mul_pow, hcm, mul_one]
    have hxpow : x ^ 2 ^ m ∈ Subgroup.centralizer (P' : Set Q) := by
      rw [← hgpow, Subgroup.mem_centralizer_iff]
      intro a ha
      exact ((show Commute a (x * c) from hgc a ha).pow_right (2 ^ m)).eq
    have hxcop : Nat.Coprime (2 ^ m) (orderOf x) := by
      obtain ⟨n, hn⟩ := hP'p ⟨x, hxP⟩
      have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxn)
        (Nat.Coprime.pow m n ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
          (Ne.symm hp2)))
    have hxcent : x ∈ Subgroup.centralizer (P' : Set Q) :=
      (Subgroup.zpowers_le.mpr hxpow) (A4.mem_zpowers_pow_of_coprime hxcop)
    have hccent : c ∈ Subgroup.centralizer (Qp : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haP' : a ∈ P' := Subgroup.mem_sup_left ha
      have h1 := hgc a haP'
      have h2 : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxcent a haP'
      calc a * c = x⁻¹ * (x * a) * c := by group
        _ = x⁻¹ * (a * x) * c := by rw [h2]
        _ = x⁻¹ * (a * (x * c)) := by group
        _ = x⁻¹ * ((x * c) * a) := by rw [h1]
        _ = c * a := by group
    have hc1 : c = 1 := by
      have : c ∈ Subgroup.zpowers r ⊓ Subgroup.centralizer (Qp : Set Q) := ⟨hcz, hccent⟩
      rw [hfaith, Subgroup.mem_bot] at this
      exact this
    rw [hc1, mul_one]
    exact hxP
  set Opb : Subgroup ↥Gb := CFSG.Open.pCore p ↥Gb with hOpb
  have hPn : (P'.subgroupOf Gb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP'Gb).mpr hGbN
  have hPp : IsPGroup p (P'.subgroupOf Gb) :=
    hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hP'Gb).symm
  have hPOpb : P'.subgroupOf Gb ≤ Opb := le_pCore p hPn hPp
  have hF : Subgroup.centralizer (Opb : Set ↥Gb) ≤ Opb := by
    intro g hg
    have hgP : (g : Q) ∈ P' := by
      refine hcent g g.2 fun a ha => ?_
      have h1 : (⟨a, hP'Gb ha⟩ : ↥Gb) ∈ Opb := hPOpb (Subgroup.mem_subgroupOf.mpr ha)
      have := Subgroup.mem_centralizer_iff.mp hg _ h1
      exact congrArg Subtype.val this
    exact hPOpb (Subgroup.mem_subgroupOf.mpr hgP)
  have hrankGb : CFSG.Open.pRank p (⊤ : Subgroup ↥Gb) ≤ 2 := by
    rw [pRank_top_subtype Gb]
    exact (CFSG.SectionRank.pRank_mono hp1 le_top).trans hrank
  have hA := A1c.A131Concl_of_surjective hp2 hF _ ↥Gb (MonoidHom.id ↥Gb)
    Function.surjective_id rfl hrankGb
  set rt : ↥Gb := ⟨r, hrGb⟩ with hrt
  have hrt2 : IsPGroup 2 (Subgroup.zpowers rt) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have e : ((r ^ k) ^ 2 ^ m : Q) = (r ^ 2 ^ m) ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have hk' : ((g : ↥Gb) : Q) = r ^ k := by rw [← hk]; rfl
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hk', e, hm, one_zpow]
  have hrtne : Subgroup.zpowers rt ≠ ⊥ := by
    intro hb
    apply hr1
    have : rt ∈ Subgroup.zpowers rt := Subgroup.mem_zpowers rt
    rw [hb, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcyc := hA.1 (Subgroup.zpowers rt) hrt2 hrtne
  have hP₀X : P₀ ≤
      (Opb ⊓ Subgroup.centralizer (Subgroup.zpowers rt : Set ↥Gb)).map Gb.subtype := by
    intro x hx
    have hxP' : x ∈ P' := Subgroup.mem_sup_right hx
    refine ⟨⟨x, hP'Gb hxP'⟩, ⟨hPOpb (Subgroup.mem_subgroupOf.mpr hxP'),
      Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    apply Subtype.ext
    show r ^ k * x = x * r ^ k
    exact (Commute.zpow_left (show Commute r x from (hP₀r x hx).symm) k).eq
  have hXc : IsCyclic ↥((Opb ⊓ Subgroup.centralizer (Subgroup.zpowers rt : Set ↥Gb)).map
      Gb.subtype) :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective
      (Opb ⊓ Subgroup.centralizer (Subgroup.zpowers rt : Set ↥Gb)) Gb.subtype
      Gb.subtype_injective) (MulEquiv.surjective _)
  have hP₀c : IsCyclic ↥P₀ := isCyclic_of_injective (Subgroup.inclusion hP₀X)
    (Subgroup.inclusion_injective hP₀X)
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (P : Subgroup ↥Cr) Cr.subtype Cr.subtype_injective).symm
    (MulEquiv.surjective _)

end Abstract

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ V : Subgroup G}

theorem lemma_14_1_17_four (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {r : OTwoQuot M}
    (hr : r ∈ imageOTwoQuot M (pCoreOf 2 (M₁ ⊓ M))) (hr1 : r ≠ 1)
    (hfaith : Subgroup.zpowers r ⊓
      Subgroup.centralizer (CFSG.Open.pCore p (OTwoQuot M) : Set (OTwoQuot M)) = ⊥) :
    (∀ P : Sylow p ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M))),
        IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M))))) ∧
      CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (V : Set G)) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set N : Subgroup ↥M := CFSG.Open.pCore 2 ↥M with hN
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (OTwoQuot M)) ≤ 2 := by
    have hnd : ¬ p ∣ Nat.card N := by
      intro hd
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).exists_card_eq
      rw [hk] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    have h1 := CFSG.SectionRank.pRank_quotient_eq (p := p) N hnd
    have h2 := pRank_top_subtype (p := p) M
    have h3 := pRank_le_two_of_isTwoLocal h.qtke hyp.inM.1.1 hp hp2
    calc CFSG.Open.pRank p (⊤ : Subgroup (OTwoQuot M)) = CFSG.Open.pRank p (⊤ : Subgroup ↥M) := h1
      _ = CFSG.Open.pRank p M := h2
      _ ≤ 2 := h3
  have hr2 : ∃ k : ℕ, r ^ 2 ^ k = 1 := by
    obtain ⟨ρ, hρM, hρR, rfl⟩ := mem_imageOTwoQuot_iff.mp hr
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (M₁ ⊓ M) ⟨ρ, hρR⟩
    refine ⟨k, ?_⟩
    have : (⟨ρ, hρM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hcyc : ∀ P : Sylow p ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M))),
      IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M)))) :=
    fun P => isCyclic_sylow_centralizer_of_faithful hp2 hrank hr1 hr2 hfaith rfl P
  refine ⟨hcyc, ?_⟩
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hC
  have hRM : pCoreOf 2 (M₁ ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hcomm : ⁅C, conjClosure (pCoreOf 2 (M₁ ⊓ M)) (⊥ ⊔ T)⁆ ≤ pCoreOf 2 M :=
    hyp.commutator_conjClosure_le h bot_le
  have hRW : pCoreOf 2 (M₁ ⊓ M) ≤ conjClosure (pCoreOf 2 (M₁ ⊓ M)) (⊥ ⊔ T) :=
    le_conjClosure _ _
  have hRC : imageOTwoQuot M (pCoreOf 2 (M₁ ⊓ M)) ≤
      Subgroup.centralizer (imageOTwoQuot M C : Set (OTwoQuot M)) := by
    refine imageOTwoQuot_le_centralizer fun x hx c hc => ?_
    have := Subgroup.commutator_mem_commutator (hRW hx) hc
    rw [Subgroup.commutator_comm] at this
    exact hcomm this
  have hCr : imageOTwoQuot M C ≤ Subgroup.centralizer ({r} : Set (OTwoQuot M)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact (Subgroup.mem_centralizer_iff.mp (hRC hr) v hv).symm
  refine CFSG.SectionRank.pRank_le hp1 fun E hEC hE => ?_
  have hEM : E ≤ M := hEC.trans inf_le_left
  set φ : ↥E →* OTwoQuot M := (QuotientGroup.mk' N).comp (Subgroup.inclusion hEM) with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : Subgroup.inclusion hEM x ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2) ⟨_, hxN⟩
    have h2 : (x : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥N => ((z : ↥M) : G)) hk
      simpa using this
    have h3 : (x : G) ^ p = 1 := hE.2 x x.2
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have h4 : orderOf (x : G) = 1 := by
      have d1 : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
      have d2 : orderOf (x : G) ∣ p := orderOf_dvd_of_pow_eq_one h3
      exact Nat.eq_one_of_dvd_coprimes hcop d1 d2
    exact Subtype.ext (orderOf_eq_one_iff.mp h4)
  have hφCr : ∀ x : ↥E, φ x ∈ Subgroup.centralizer ({r} : Set (OTwoQuot M)) := fun x =>
    hCr (mem_imageOTwoQuot_iff.mpr ⟨x, hEM x.2, hEC x.2, rfl⟩)
  have hXp : IsPGroup p ↥φ.range := (isPGroup_of_isElemAbelian hE).of_equiv
    (MonoidHom.ofInjective hφinj)
  have hXCr : φ.range ≤ Subgroup.centralizer ({r} : Set (OTwoQuot M)) := by
    rintro _ ⟨x, rfl⟩
    exact hφCr x
  have hXp' : IsPGroup p ↥(φ.range.subgroupOf (Subgroup.centralizer ({r} : Set (OTwoQuot M)))) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXCr).symm
  obtain ⟨P, hP⟩ := hXp'.exists_le_sylow
  set φ0 : ↥E →* ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M))) := φ.codRestrict _ hφCr
    with hφ0
  have hφP : ∀ x : ↥E, φ0 x ∈ (P : Subgroup ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M)))) :=
    fun x => hP (Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩)
  set φ1 : ↥E →* ↥(P : Subgroup ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M)))) :=
    φ0.codRestrict _ hφP with hφ1
  have := hcyc P
  have hEcyc : IsCyclic ↥E := isCyclic_of_injective φ1 fun a b hab =>
    hφinj (congrArg (fun z : ↥(P : Subgroup ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M)))) =>
      ((z : ↥(Subgroup.centralizer ({r} : Set (OTwoQuot M)))) : OTwoQuot M)) hab)
  obtain ⟨g, hg⟩ := hEcyc.exists_generator
  have hcard : Nat.card ↥E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 g g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rw [hcard, pow_one]
  exact Nat.le_of_dvd hp.pos hdvd

end Main

end CFSG.Quasithin
