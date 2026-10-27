module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A6
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E1
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D1
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

@[expose] def KMult3Ab : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    CFSG.Open.IsKGroup (J ⧸ center J) → IsPGroup 3 (center J) →
    CFSG.Open.pRank 3 (⊤ : Subgroup J) ≤ 3 →
    ∀ T : Subgroup J, CFSG.ABGLocalTools.IsSylowOf 3 T ⊤ →
      (∀ x ∈ T, x ^ 3 = 1 → ∀ y ∈ T, y ^ 3 = 1 → x * y = y * x) → center J = ⊥

end CFSG.LocalAnalysis.UniquenessCase.UCK

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588T

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

structure Hyp3 (G : Type) [Group G] [Finite G] (S Z : Subgroup G) : Prop where
  isKGroup : CFSG.Open.IsKGroup G
  sylow : IsSylowOf 3 S ⊤
  omega : ∀ x ∈ S, x ^ 3 = 1 → ∀ y ∈ S, y ^ 3 = 1 → x * y = y * x
  rank : CFSG.Open.pRank 3 S ≤ 3
  le : Z ≤ S
  card : Nat.card Z = 3
  wc : IsWeaklyClosedIn Z S

namespace Hyp3

variable {G : Type} [Group G] [Finite G] {S Z : Subgroup G}

theorem pow_eq_one (h : Hyp3 G S Z) {z : G} (hz : z ∈ Z) : z ^ 3 = 1 :=
  N588A.pow_eq_one_of_card h.card hz

theorem conjugate_eq_of_mem (h : Hyp3 G S Z) {s : G} (hs : s ∈ S) :
    CFSG.conjugate Z s = Z := by
  apply h.wc s
  intro x hx
  rw [N588A.mem_conjugate_iff] at hx
  have hxS : s * x * s⁻¹ ∈ S := h.le hx
  have e : x = s⁻¹ * (s * x * s⁻¹) * s := by group
  rw [e]
  exact S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs

theorem le_centralizer_of_normal_of_card (hSp : IsPGroup 3 S) (hZS : Z ≤ S)
    (hN : S ≤ Subgroup.normalizer (Z : Set G)) (hcard : Nat.card Z = 3) :
    Z ≤ Subgroup.centralizer (S : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent S := hSp.isNilpotent
  have hZcard : Nat.card (Z.subgroupOf S) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv, hcard]
  have hnormal : (Z.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hne : Z.subgroupOf S ≠ ⊥ := by
    intro hbot
    have h1 := hZcard
    rw [hbot, Subgroup.card_bot] at h1
    omega
  set H : Subgroup ↥S := Z.subgroupOf S ⊓ Subgroup.center ↥S with hH
  have hinter : H ≠ ⊥ := by
    rw [hH]
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hdvd : Nat.card H ∣ 3 := by
    rw [hH, ← hZcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne1 : Nat.card H ≠ 1 := fun h1 => hinter ((Subgroup.card_eq_one).mp h1)
  have hcardinf : Nat.card H = Nat.card (Z.subgroupOf S) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · rw [h, hZcard]
  have heq : H = Z.subgroupOf S := by
    rw [hH]
    exact Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcardinf.symm)
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hz' : (⟨z, hZS hz⟩ : S) ∈ Z.subgroupOf S := Subgroup.mem_subgroupOf.mpr hz
  have hzc : (⟨z, hZS hz⟩ : S) ∈ Subgroup.center ↥S := by
    have hmem : (⟨z, hZS hz⟩ : S) ∈ H := by rw [heq]; exact hz'
    rw [hH] at hmem
    exact hmem.2
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩)

theorem comm (h : Hyp3 G S Z) {z : G} (hz : z ∈ Z) {y : G} (hy : y ∈ S) : z * y = y * z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 S := by
    obtain ⟨P, hP⟩ := N588A.exists_sylow_of_isSylowOf_top h.sylow
    exact hP ▸ P.isPGroup'
  have hN : S ≤ Subgroup.normalizer (Z : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : x ∈ CFSG.conjugate Z s := by rw [h.conjugate_eq_of_mem hs]; exact hx
      exact N588A.mem_conjugate_iff.mp hx'
    · intro hx
      have hx' : x ∈ CFSG.conjugate Z s := N588A.mem_conjugate_iff.mpr hx
      rwa [h.conjugate_eq_of_mem hs] at hx'
  exact (Subgroup.mem_centralizer_iff.mp
    (le_centralizer_of_normal_of_card hSp h.le hN h.card hz) y hy).symm

theorem isPGroup (h : Hyp3 G S Z) : IsPGroup 3 Z :=
  IsPGroup.of_card (n := 1) (by rw [pow_one]; exact h.card)

theorem ne_bot (h : Hyp3 G S Z) : Z ≠ ⊥ := by
  intro hZ
  have h1 := h.card
  rw [hZ, Subgroup.card_bot] at h1
  omega

theorem eq_zpowers (h : Hyp3 G S Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) : Z = zpowers z := by
  have hle : zpowers z ≤ Z := (Subgroup.zpowers_le).mpr hz
  have hdvd : orderOf z ∣ 3 := h.card ▸ Subgroup.orderOf_dvd_natCard Z hz
  have ho : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, ho, h.card])).symm

theorem conjugate_eq_of_le_normalizer (h : Hyp3 G S Z) {g : G}
    (hg : CFSG.conjugate Z g ≤ Subgroup.normalizer (Z : Set G)) : CFSG.conjugate Z g = Z :=
  N588A.conjugate_eq_of_le_normalizer h.sylow h.wc h.isPGroup hg

theorem concl_of_le (h : Hyp3 G S Z)
    (hle : CFSG.Open.pRank 3 (normalClosure (Z : Set G)) ≤ 1) :
    CFSG.Open.pRank 3 (normalClosure (Z : Set G)) = 1 :=
  le_antisymm hle (N588A.one_le_pRank Nat.prime_three Subgroup.le_normalClosure h.card)

theorem concl_of_normal (h : Hyp3 G S Z) (hN : Z.Normal) :
    CFSG.Open.pRank 3 (normalClosure (Z : Set G)) = 1 := by
  rw [Subgroup.normalClosure_eq_self]
  exact N588A.pRank_eq_one_of_card Nat.prime_three h.card

theorem pRank_le_three (h : Hyp3 G S Z) (H : Subgroup G) : CFSG.Open.pRank 3 H ≤ 3 :=
  (N588A.pRank_le_of_isSylowOf Nat.prime_three h.sylow H).trans h.rank

theorem pRank_top_le_three (h : Hyp3 G S Z) (J : Subgroup G) :
    CFSG.Open.pRank 3 (⊤ : Subgroup J) ≤ 3 := by
  rw [← N588A.pRank_map_subtype (by norm_num) J, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  exact h.pRank_le_three J

theorem quotient (h : Hyp3 G S Z) (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) :
    Hyp3 (G ⧸ N) (S.map (QuotientGroup.mk' N)) (Z.map (QuotientGroup.mk' N)) := by
  obtain ⟨P, hPS⟩ := N588A.exists_sylow_of_isSylowOf_top h.sylow
  have hSp : IsPGroup 3 S := hPS ▸ P.isPGroup'
  have hSN : S ⊓ N = ⊥ := N588A.inf_eq_bot_of_coprime hSp hN
  have hker : ∀ x ∈ S, QuotientGroup.mk' N x = 1 → x = 1 := fun x hx h1 => by
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp h1
    have hx' : x ∈ S ⊓ N := ⟨hx, hxN⟩
    rwa [hSN, Subgroup.mem_bot] at hx'
  refine ⟨h.isKGroup.quotient N, ?_, ?_, ?_, Subgroup.map_mono h.le, ?_, ?_⟩
  · have hs := N588A.isSylowOf_top_of_sylow
      (P.mapSurjective (QuotientGroup.mk'_surjective N))
    rwa [Sylow.coe_mapSurjective, hPS] at hs
  · rintro _ ⟨x, hx, rfl⟩ hxp _ ⟨y, hy, rfl⟩ hyp
    have hxp' : x ^ 3 = 1 := hker _ (S.pow_mem hx 3) (by rw [map_pow]; exact hxp)
    have hyp' : y ^ 3 = 1 := hker _ (S.pow_mem hy 3) (by rw [map_pow]; exact hyp)
    rw [← map_mul, ← map_mul, h.omega x hx hxp' y hy hyp']
  · calc CFSG.Open.pRank 3 (S.map (QuotientGroup.mk' N))
          ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ N)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
          CFSG.SectionRank.pRank_quotient_eq N
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN)
      _ ≤ 3 := h.pRank_le_three ⊤
  · rw [N588A.card_map_of_injOn _ (fun x hx => hker x (h.le hx)), h.card]
  · intro gbar hgbar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    have hle : CFSG.conjugate Z g ≤ S ⊔ N := by
      intro x hx
      have hfx : QuotientGroup.mk' N x ∈ S.map (QuotientGroup.mk' N) := by
        apply hgbar
        rw [N588A.mem_conjugate_iff, ← map_inv, ← map_mul, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (N588A.mem_conjugate_iff.mp hx)
      have hx' : x ∈ (S.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hfx
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx'
    have hSSN : IsSylowOf 3 S (S ⊔ N) := h.sylow.of_le le_sup_left le_top
    obtain ⟨Q, hQ, hZgQ⟩ := N588A.exists_isSylowOf_ge_of_le hle (h.isPGroup.map _)
    obtain ⟨k, hk, hkQ⟩ := hSSN.exists_mem_conj hQ
    have h1 : CFSG.conjugate Z (g * k) = Z := by
      apply h.wc
      intro x hx
      rw [N588A.mem_conjugate_iff] at hx
      have hx' : k * x * k⁻¹ ∈ CFSG.conjugate Z g := by
        rw [N588A.mem_conjugate_iff]
        simpa [mul_assoc] using hx
      have hS := (hkQ _).mp (hZgQ hx')
      simpa [mul_assoc] using hS
    have h2 : CFSG.conjugate Z g = CFSG.conjugate Z k⁻¹ := by
      have e := congrArg (fun H => CFSG.conjugate H k⁻¹) h1
      simpa only [N588A.conjugate_conjugate, mul_inv_cancel_right] using e
    have hk' : k ∈ ((S ⊔ N : Subgroup G) : Set G) := hk
    rw [Subgroup.mul_normal] at hk'
    obtain ⟨s, hs, n, hn, rfl⟩ := hk'
    have hfn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [← N588A.map_conjugate, h2, N588A.map_conjugate, map_inv, map_mul, hfn, mul_one,
      ← map_inv, ← N588A.map_conjugate, h.conjugate_eq_of_mem (S.inv_mem hs)]

theorem concl_of_quotient (h : Hyp3 G S Z)
    (hq : CFSG.Open.pRank 3 (normalClosure
      ((Z.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) :
        Set (G ⧸ CFSG.pPrimeCore 3 G))) = 1) :
    CFSG.Open.pRank 3 (normalClosure (Z : Set G)) = 1 := by
  have hNc : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 G)) := CFSG.pPrimeCore_coprime_card
  rw [Subgroup.coe_map,
    ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 G))] at hq
  refine h.concl_of_le ?_
  rw [← hq]
  apply N588A.pRank_le_pRank_map (by norm_num)
  intro E _ hE x hx h1
  have hEN := N588A.inf_eq_bot_of_coprime (N588A.isPGroup_of_isElemAbelian hE) hNc
  have hx' : x ∈ E ⊓ CFSG.pPrimeCore 3 G := ⟨hx, (QuotientGroup.eq_one_iff x).mp h1⟩
  rwa [hEN, Subgroup.mem_bot] at hx'

theorem normal_of_le_normal_isPGroup (h : Hyp3 G S Z) {P : Subgroup G} [P.Normal]
    (hP : IsPGroup 3 P) (hZP : Z ≤ P) : Z.Normal := by
  obtain ⟨Q, hQS⟩ := N588A.exists_sylow_of_isSylowOf_top h.sylow
  have hPS : P ≤ S := hQS ▸ hP.le_sylow_of_normal Q
  refine N588A.normal_of_conjugate_eq fun g => h.wc g fun x hx => hPS ?_
  have hx' := hZP (N588A.mem_conjugate_iff.mp hx)
  have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e]
  have := (inferInstance : P.Normal).conj_mem _ hx' g⁻¹
  simpa using this

theorem dvd_card_of_isComponent (hcore : CFSG.pPrimeCore 3 G = ⊥) {J : Subgroup G}
    (hJ : CFSG.IsComponent J) : 3 ∣ Nat.card J := by
  have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact N588A.dvd_card_of_isSubnormal Nat.prime_three hcore hJ.2
    ((Subgroup.nontrivial_iff_ne_bot J).mp this)

theorem exists_component (h : Hyp3 G S Z) (hcore : CFSG.pPrimeCore 3 G = ⊥)
    (hZ : ¬ Z.Normal) :
    ∃ J : Subgroup G, CFSG.IsComponent J ∧ ¬ Z ≤ Subgroup.centralizer (J : Set G) := by
  by_contra hall
  push Not at hall
  have hF : CFSG.fittingSubgroup G = CFSG.pCore 3 G := CFSG.Fitting_eq_pcore G 3 hcore
  obtain ⟨Q, hQS⟩ := N588A.exists_sylow_of_isSylowOf_top h.sylow
  haveI : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
  have hPS : CFSG.pCore 3 G ≤ S := hQS ▸ CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have hZF : Z ≤ Subgroup.centralizer (CFSG.fittingSubgroup G : Set G) := by
    rw [Subgroup.le_centralizer_iff, hF]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact h.comm hz (hPS hx)
  have hZE : Z ≤ Subgroup.centralizer (CFSG.layer G : Set G) := by
    rw [Subgroup.le_centralizer_iff, CFSG.layer.eq_sSup]
    exact sSup_le fun J hJ => (Subgroup.le_centralizer_iff).mp (hall J hJ)
  have hZFs : Z ≤ Subgroup.centralizer (CFSG.generalizedFitting G : Set G) := by
    rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting.eq_sup]
    exact sup_le ((Subgroup.le_centralizer_iff).mp hZF) ((Subgroup.le_centralizer_iff).mp hZE)
  have hZP : Z ≤ CFSG.pCore 3 G :=
    hF ▸ hZFs.trans (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup G)
  exact hZ (h.normal_of_le_normal_isPGroup CFSG.pCore_isPGroup hZP)

theorem le_normalizer_of_isComponent (h : Hyp3 G S Z) (hcore : CFSG.pPrimeCore 3 G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J) : Z ≤ Subgroup.normalizer (J : Set G) := by
  intro z hz
  have hmap : J.map (MulAut.conj z).toMonoidHom = J := by
    by_contra hne
    have hJ' : CFSG.IsComponent (J.map (MulAut.conj z).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hJ
    have hcomm : ⁅J, J.map (MulAut.conj z).toMonoidHom⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hJ hJ').resolve_left (Ne.symm hne)
    have hTJ' : S ⊓ J ≤ J.map (MulAut.conj z).toMonoidHom := by
      intro x hx
      refine ⟨x, hx.2, ?_⟩
      change z * x * z⁻¹ = x
      rw [h.comm hz hx.1, mul_inv_cancel_right]
    obtain ⟨P, hP⟩ := N588A.isSylowOf_inf_of_isSubnormal h.sylow hJ.2
    have hPc : (P : Subgroup J) ≤ center J := by
      intro x hx
      have hxT : (x : G) ∈ S ⊓ J := hP ▸ ⟨x, hx, rfl⟩
      have hxC : (x : G) ∈ Subgroup.centralizer (J : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          ((Subgroup.commutator_comm _ _).trans hcomm)) (hTJ' hxT)
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    exact N588A.not_dvd_card_of_sylow_le_center hJ.1.1 P hPc (dvd_card_of_isComponent hcore hJ)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : y = x := by
      have e : z * y * z⁻¹ = z * x * z⁻¹ := hyx
      simpa using e
    exact hxy ▸ hy

theorem isSylowOf_subgroupOf (h : Hyp3 G S Z) {J : Subgroup G} (hJ : J.IsSubnormal) :
    IsSylowOf 3 (S.subgroupOf J) ⊤ := by
  have hTmap : (S.subgroupOf J).map J.subtype = S ⊓ J := Subgroup.subgroupOf_map_subtype S J
  have hJtop : (⊤ : Subgroup J).map J.subtype = J := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hs' := N588A.isSylowOf_inf_of_isSubnormal h.sylow hJ
  rw [← hTmap] at hs'
  conv at hs' => rhs; rw [← hJtop]
  exact (isSylowOf_map_subtype_iff J).mp hs'

theorem isPGroup_center (hcore : CFSG.pPrimeCore 3 G = ⊥) {J : Subgroup G}
    (hJ : CFSG.IsComponent J) : IsPGroup 3 (center J) := by
  have h1 : (center J).map J.subtype ≤ CFSG.pCore 3 G := by
    rw [← CFSG.Fitting_eq_pcore G 3 hcore]
    exact (CFSG.LocalCores.center_component_le_center_layer hJ).trans
      CFSG.WholeGroup.center_layer_le_fittingSubgroup
  have h2 : IsPGroup 3 ((center J).map J.subtype) := CFSG.pCore_isPGroup.to_le h1
  exact h2.of_equiv ((center J).equivMapOfInjective J.subtype J.subtype_injective).symm

theorem center_eq_bot (hM3 : UCK.KMult3Ab) (h : Hyp3 G S Z) (hcore : CFSG.pPrimeCore 3 G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J) : center J = ⊥ := by
  refine hM3 J ⟨hJ.1.1.commutator_eq_top, hJ.1.2.1⟩ ((h.isKGroup.subgroup J).quotient (center J))
    (isPGroup_center hcore hJ) (h.pRank_top_le_three J) (S.subgroupOf J)
    (h.isSylowOf_subgroupOf hJ.2) ?_
  intro x hx hx3 y hy hy3
  apply Subtype.ext
  exact h.omega _ (Subgroup.mem_subgroupOf.mp hx) (by simpa using congrArg Subtype.val hx3) _
    (Subgroup.mem_subgroupOf.mp hy) (by simpa using congrArg Subtype.val hy3)

theorem exists_ne_of_isComponent {J : Subgroup G} (hJ : CFSG.IsComponent J) :
    ∃ a b : J, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hJ.1.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun e => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e])⟩

end Hyp3

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588T
