module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Struct
public import CFSG.Quasithin.H13.KGFact68Base

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Quasithin.H13.KG68

section TwoByS

variable {G : Type} [Group G] {S : Type} [Group S]

theorem mem_pCoreOf_iff' {X : Subgroup G} {x : G} :
    x ∈ pCoreOf 2 X ↔ ∃ y : ↥X, (y : G) = x ∧ y ∈ CFSG.pCore 2 ↥X := by
  unfold pCoreOf
  simp [Subgroup.mem_map]

theorem le_pCoreOf_of_normal {K E : Subgroup G} (hEK : E ≤ K) (hEn : (E.subgroupOf K).Normal)
    (hE2 : IsPGroup 2 ↥E) : E ≤ pCoreOf 2 K :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E K hEK hEn hE2

theorem pCore_le_ker {K : Subgroup G} (hs : IsSimpleGroup S) (hn : ¬ IsPGroup 2 S)
    (α : ↥K →* S) (hα : Function.Surjective α) : CFSG.pCore 2 ↥K ≤ α.ker := by
  have hnorm : ((CFSG.pCore 2 ↥K).map α).Normal := Subgroup.Normal.map CFSG.pCore_normal α hα
  have hp2 : IsPGroup 2 ((CFSG.pCore 2 ↥K).map α) := (CFSG.pCore_isPGroup (p := 2)).map α
  have hbot : (CFSG.pCore 2 ↥K).map α = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map α) with hb | ht
    · exact hb
    · exfalso
      apply hn
      intro x
      obtain ⟨k, hk⟩ := hp2 ⟨x, by rw [ht]; trivial⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  intro x hx
  rw [MonoidHom.mem_ker]
  have : α x ∈ (CFSG.pCore 2 ↥K).map α := ⟨x, hx, rfl⟩
  rw [hbot] at this
  exact this

theorem pCoreOf_eq_of_hom {K E : Subgroup G} (hs : IsSimpleGroup S) (hn : ¬ IsPGroup 2 S)
    (hEK : E ≤ K) (hE2 : IsPGroup 2 ↥E) (α : ↥K →* S) (hα : Function.Surjective α)
    (hker : α.ker = E.subgroupOf K) : pCoreOf 2 K = E := by
  have hEn : (E.subgroupOf K).Normal := hker ▸ α.normal_ker
  refine le_antisymm ?_ (le_pCoreOf_of_normal hEK hEn hE2)
  calc pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := by
        unfold pCoreOf
        try with_reducible rfl
    _ ≤ (E.subgroupOf K).map K.subtype :=
        Subgroup.map_mono (by rw [← hker]; exact pCore_le_ker hs hn α hα)
    _ = E := Subgroup.map_subgroupOf_eq_of_le hEK

theorem quotient_card_of_hom {K E : Subgroup G} (hs : IsSimpleGroup S)
    (hE2 : IsPGroup 2 ↥E) (α : ↥K →* S) (hα : Function.Surjective α)
    (hker : α.ker = E.subgroupOf K) {B : Subgroup G} (hBK : B ≤ K)
    (hsub : (B.subgroupOf K).IsSubnormal) :
    Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1 ∨
      Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = Nat.card S := by
  have h1 : IsSubnormal ((B.subgroupOf K).map α) ⊤ := by
    have := A3.subnormal_map α (A3.subnormal_top_iff.mpr hsub)
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr hα] at this
  have hmemE : ∀ b : ↥B, α ⟨b, hBK b.2⟩ = 1 → (b : G) ∈ E := by
    intro b hb
    have : (⟨b, hBK b.2⟩ : ↥K) ∈ α.ker := hb
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  have h2pow : ∀ b : ↥B, α ⟨b, hBK b.2⟩ = 1 → ∃ k : ℕ, b ^ 2 ^ k = 1 := by
    intro b hb
    obtain ⟨k, hk⟩ := hE2 ⟨(b : G), hmemE b hb⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  rcases isSubnormal_of_simple h1 (Or.inr rfl) with hbot | htop
  · left
    have hB2 : IsPGroup 2 ↥B := by
      intro b
      apply h2pow
      have : α ⟨b, hBK b.2⟩ ∈ (B.subgroupOf K).map α :=
        ⟨⟨b, hBK b.2⟩, Subgroup.mem_subgroupOf.2 b.2, rfl⟩
      rw [hbot] at this
      exact this
    have htop' : CFSG.pCore 2 ↥B = ⊤ := by
      refine top_le_iff.mp (le_sSup ⟨inferInstance, ?_⟩)
      intro x
      obtain ⟨k, hk⟩ := hB2 (x : ↥B)
      exact ⟨k, Subtype.ext hk⟩
    rw [htop']
    exact Subgroup.index_top
  · set φ : ↥B →* S := α.comp (Subgroup.inclusion hBK) with hφ
    have hφs : Function.Surjective φ := by
      intro a
      have : a ∈ (B.subgroupOf K).map α := by rw [htop]; trivial
      obtain ⟨k, hk, hka⟩ := this
      exact ⟨⟨(k : G), Subgroup.mem_subgroupOf.1 hk⟩, by show α _ = a; exact hka⟩
    have hkerle : φ.ker ≤ CFSG.pCore 2 ↥B := by
      refine le_sSup ⟨φ.normal_ker, ?_⟩
      intro x
      obtain ⟨k, hk⟩ := h2pow (x : ↥B) x.2
      exact ⟨k, Subtype.ext hk⟩
    have hnorm : ((CFSG.pCore 2 ↥B).map φ).Normal := Subgroup.Normal.map CFSG.pCore_normal φ hφs
    rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥B).map φ) with hb | ht
    · have hP : CFSG.pCore 2 ↥B = φ.ker := by
        refine le_antisymm ?_ hkerle
        intro x hx
        rw [MonoidHom.mem_ker]
        have : φ x ∈ (CFSG.pCore 2 ↥B).map φ := ⟨x, hx, rfl⟩
        rw [hb] at this
        exact this
      have hq : ↥B ⧸ CFSG.pCore 2 ↥B ≃* S :=
        (QuotientGroup.quotientMulEquivOfEq hP).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
      right
      exact Nat.card_congr hq.toEquiv
    · left
      have hP : CFSG.pCore 2 ↥B = ⊤ := by
        refine eq_top_iff.2 fun b _ => ?_
        have : φ b ∈ (CFSG.pCore 2 ↥B).map φ := by rw [ht]; trivial
        obtain ⟨p, hp, hpb⟩ := this
        have : p⁻¹ * b ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hpb, inv_mul_cancel]
        have h2 := hkerle this
        have h3 := (CFSG.pCore 2 ↥B).mul_mem hp h2
        simpa using h3
      rw [hP]
      exact Subgroup.index_top

theorem not_hasChi0Block_of_hom {K E : Subgroup G} (hs : IsSimpleGroup S)
    (hE2 : IsPGroup 2 ↥E) (α : ↥K →* S) (hα : Function.Surjective α)
    (hker : α.ker = E.subgroupOf K) (hm : Nat.card S = 360 ∨ Nat.card S = 2520) :
    ¬ HasChi0Block K := by
  rintro ⟨B, ⟨⟨hsh, hBK, hsub⟩, htype⟩⟩
  have hdich := quotient_card_of_hom hs hE2 α hα hker hBK hsub
  have hord := card_quotient_of_chi0Type htype
  rcases hdich with h1 | h1
  · rcases hord with h3 | h3 | ⟨n, hn, h3⟩
    · omega
    · omega
    · exact (quotOrder_ne n hn).1 (h3.symm.trans h1)
  · rcases hord with h3 | h3 | ⟨n, hn, h3⟩
    · rcases hm with hm | hm <;> omega
    · rcases hm with hm | hm <;> omega
    · rcases hm with hm | hm
      · exact (quotOrder_ne n hn).2.1 (h3.symm.trans (h1.trans hm))
      · exact (quotOrder_ne n hn).2.2 (h3.symm.trans (h1.trans hm))

omit [Group S] in
theorem isPGroup_zpowers_of_pow_eq_one {g : G} {k : ℕ} (h : g ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem le_twoPrimeResidual_of_hom [Finite G] [Finite S] {K E : Subgroup G}
    (hs : IsSimpleGroup S) (h2S : 2 ∣ Nat.card S) (hE2 : IsPGroup 2 ↥E) (α : ↥K →* S)
    (hα : Function.Surjective α) (hker : α.ker = E.subgroupOf K) : K ≤ twoPrimeResidual K := by
  intro x hxK
  unfold twoPrimeResidual
  rw [Subgroup.mem_iInf]
  intro N
  rw [Subgroup.mem_iInf]
  intro hN
  obtain ⟨hNK, hKN, hodd⟩ := hN
  have hNn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hbig : ∀ y : ↥K, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ∈ N.subgroupOf K := by
    rintro y ⟨k, hk⟩
    have hy : (y : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hTK : Subgroup.zpowers (y : G) ≤ K := (Subgroup.zpowers_le).2 y.2
    exact Subgroup.mem_subgroupOf.2 (B6.le_of_isPGroup_of_odd_relIndex hTK
      (isPGroup_zpowers_of_pow_eq_one hy) hNK hKN hodd (Subgroup.mem_zpowers _))
  have hnorm : ((N.subgroupOf K).map α).Normal := Subgroup.Normal.map hNn α hα
  rcases hs.eq_bot_or_eq_top_of_normal ((N.subgroupOf K).map α) with hb | ht
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs2⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2S
    obtain ⟨y, hy⟩ := hα s
    obtain ⟨a, b, hbo, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    have hy' : (y ^ b) ∈ N.subgroupOf K := by
      apply hbig
      refine ⟨a, ?_⟩
      rw [← pow_mul, mul_comm, ← hab]
      exact pow_orderOf_eq_one y
    have : α (y ^ b) ∈ (N.subgroupOf K).map α := ⟨y ^ b, hy', rfl⟩
    rw [hb, Subgroup.mem_bot, map_pow, hy] at this
    have h2b : 2 ∣ b := hs2 ▸ orderOf_dvd_of_pow_eq_one this
    obtain ⟨c, hc⟩ := hbo
    omega
  · have hxm : α ⟨x, hxK⟩ ∈ (N.subgroupOf K).map α := by rw [ht]; trivial
    obtain ⟨n, hn, hnx⟩ := hxm
    have hker' : n⁻¹ * ⟨x, hxK⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hker'
    obtain ⟨k, hk⟩ := hE2 ⟨_, hker'⟩
    have h1 : (n⁻¹ * ⟨x, hxK⟩ : ↥K) ∈ N.subgroupOf K := by
      apply hbig
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have h2 : (⟨x, hxK⟩ : ↥K) ∈ N.subgroupOf K := by
      have := (N.subgroupOf K).mul_mem hn h1
      simpa using this
    exact h2

end TwoByS

section Lift

variable {A B : Type} [Group A] [Group B]

theorem comap_pCore_le (ρ : A →* B) (hρ2 : IsPGroup 2 ρ.ker) :
    (CFSG.pCore 2 B).comap ρ ≤ CFSG.pCore 2 A := by
  refine le_sSup ⟨inferInstance, ?_⟩
  intro a
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)) ⟨ρ a, a.2⟩
  have hker : (a : A) ^ 2 ^ j ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    simpa using congrArg Subtype.val hj
  obtain ⟨i, hi⟩ := hρ2 ⟨_, hker⟩
  refine ⟨j + i, Subtype.ext ?_⟩
  have := congrArg Subtype.val hi
  simp only [SubmonoidClass.mk_pow, Subgroup.coe_one] at this
  simp [pow_add, pow_mul, this]

end Lift

section CharTwoLift

variable {G G' : Type} [Group G] [Group G']

theorem charTwo_of_surj {K : Subgroup G} {K' : Subgroup G'} (ρ : ↥K →* ↥K')
    (hρ : Function.Surjective ρ) (hρ2 : IsPGroup 2 ρ.ker) (h : CharTwo K') : CharTwo K := by
  intro x hx
  obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.1 hx
  have hcomm : ∀ w ∈ CFSG.pCore 2 ↥K, w * (⟨x, hxK⟩ : ↥K) = ⟨x, hxK⟩ * w := by
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 K := mem_pCoreOf_iff'.2 ⟨w, rfl, hw⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc (w : G) hw')
  have key : ρ ⟨x, hxK⟩ ∈ CFSG.pCore 2 ↥K' := by
    have hmem : ((ρ ⟨x, hxK⟩ : ↥K') : G') ∈ K' ⊓ Subgroup.centralizer (pCoreOf 2 K' : Set G') := by
      refine ⟨(ρ ⟨x, hxK⟩).2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      obtain ⟨y', hy'G, hy'⟩ := mem_pCoreOf_iff'.1 hy
      obtain ⟨w, hw⟩ := hρ y'
      have hwmem : w ∈ CFSG.pCore 2 ↥K := comap_pCore_le ρ hρ2
        (show w ∈ (CFSG.pCore 2 ↥K').comap ρ from by rw [Subgroup.mem_comap, hw]; exact hy')
      have h2 : y' * ρ ⟨x, hxK⟩ = ρ ⟨x, hxK⟩ * y' := by
        rw [← hw, ← map_mul, ← map_mul, hcomm w hwmem]
      rw [← hy'G]
      exact congrArg Subtype.val h2
    obtain ⟨z, hzG, hz⟩ := mem_pCoreOf_iff'.1 (h hmem)
    have : z = ρ ⟨x, hxK⟩ := Subtype.ext hzG
    rw [← this]
    exact hz
  exact mem_pCoreOf_iff'.2 ⟨_, rfl, comap_pCore_le ρ hρ2 key⟩

end CharTwoLift

section Fixed

variable {G : Type} [Group G]

theorem eq_one_of_central_of_order_five [Finite G] {K E : Subgroup G} (hEK : E ≤ K)
    (hEn : (E.subgroupOf K).Normal) (hcard : Nat.card ↥E = 16)
    (hC : K ⊓ Subgroup.centralizer (E : Set G) ≤ E) {g : G} (hg : g ∈ K) (hg5 : orderOf g = 5)
    {c : G} (hc : c ∈ E) (hcK : ∀ k ∈ K, k * c = c * k) : c = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKN : K ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).1 hEn
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.zpowers_le).2 (hKN hg)
  let _ : MulAction ↥(Subgroup.zpowers g) ↥E :=
    MulAction.compHom ↥E (actHom E (Subgroup.zpowers g) hle)
  have hsmul : ∀ (a : ↥(Subgroup.zpowers g)) (e : ↥E),
      ((a • e : ↥E) : G) = (a : G) * e * (a : G)⁻¹ := fun a e => rfl
  have hP : IsPGroup 5 ↥(Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg5, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints ↥E
  set C : Subgroup ↥E := (E ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf E with hCdef
  have hmemC : ∀ e : ↥E, e ∈ C ↔ g * (e : G) = e * g := by
    intro e
    simp only [hCdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.2, fun h => ⟨e.2, h⟩⟩
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers g) ↥E = (C : Set ↥E) := by
    ext e
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, hmemC]
    constructor
    · intro h
      have h1 := congrArg (fun z : ↥E => (z : G)) (h ⟨g, Subgroup.mem_zpowers g⟩)
      simp only [hsmul] at h1
      calc g * (e : G) = (g * e * g⁻¹) * g := by group
        _ = e * g := by rw [h1]
    · intro h a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 a.2
      have hcomm : Commute (a : G) (e : G) := by
        rw [← hn]
        exact (Commute.zpow_left (show Commute g (e : G) from h) n)
      apply Subtype.ext
      rw [hsmul]
      calc (a : G) * e * (a : G)⁻¹ = (e : G) * a * (a : G)⁻¹ := by rw [hcomm.eq]
        _ = e := by group
  have hdvd : Nat.card ↥C ∣ 16 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hmod' : 16 % 5 = Nat.card ↥C % 5 := by
    have := hmod
    rw [hfix, hcard] at this
    exact this
  have hf : Nat.card ↥C = 1 ∨ Nat.card ↥C = 16 := by
    have hle16 : Nat.card ↥C ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    generalize Nat.card ↥C = f at hdvd hmod' hle16 hpos
    interval_cases f <;> omega
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  rcases hf with hf | hf
  · have hCbot : C = ⊥ := Subgroup.eq_bot_of_card_eq C hf
    have hcC : (⟨c, hc⟩ : ↥E) ∈ C := (hmemC _).2 (hcK g hg)
    rw [hCbot, Subgroup.mem_bot] at hcC
    exact congrArg Subtype.val hcC
  · exfalso
    have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (hf.trans hcard.symm)
    have hgC : g ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have : (⟨e, he⟩ : ↥E) ∈ C := by rw [hCtop]; trivial
      exact ((hmemC _).1 this).symm
    have hgE : g ∈ E := hC ⟨hg, hgC⟩
    obtain ⟨k, hk⟩ := hE2 ⟨g, hgE⟩
    have hgk : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h5 : 5 ∣ 2 ^ k := hg5 ▸ orderOf_dvd_of_pow_eq_one hgk
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5 : 5 ∣ 2)
    omega

end Fixed

end E68Proof

end E6

end CFSG.Quasithin
