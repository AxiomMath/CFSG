module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127
import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Item2127Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G),
    Pair2127 G A E U c L d →
      ∀ y ∈ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) ⊓
        Sec4.thetaQuotCentralizer L, y ^ 3 = 1 → y ∈ Subgroup.zpowers c

@[expose] def Item2127Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G),
    Pair2127 G A E U c L d → ∀ F : Subgroup G, IsFOf2127 A L F →
      (∀ x ∈ A ⊔ F, x ^ 3 = 1) ∧ d ∈ F ∧ Nat.card (Sec4.autThetaQuot (A ⊔ F) L) = 27

namespace Item2119End5Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {P K : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ S : Subgroup G, IsSylowOf p S K ∧ P ≤ S := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_⟩
  intro x hx
  exact ⟨⟨x, hPK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem exists_conj_of_isSylowOf {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (hP : IsSylowOf p P K) (hP' : IsSylowOf p P' K) :
    ∃ x ∈ K, P' = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨g, g.2, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

theorem exists_normalized_isSylowOf {p : ℕ} [Fact p.Prime] {H : Subgroup G} {x : G}
    (hxH : x ∈ Subgroup.normalizer (H : Set G)) {n : ℕ} (hxn : x ^ p ^ n = 1) :
    ∃ S : Subgroup G, IsSylowOf p S H ∧ x ∈ Subgroup.normalizer (S : Set G) := by
  have hKN : H ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxH)
  have hz : IsPGroup p (Subgroup.zpowers x) := by
    rintro ⟨g, m, rfl⟩
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxn, one_zpow]
  obtain ⟨S', hS', hzS'⟩ := exists_isSylowOf_ge (le_sup_right : Subgroup.zpowers x ≤ _) hz
  refine ⟨S' ⊓ H, hS'.inf_of_le_normalizer le_sup_left hKN, ?_⟩
  have hxS' : x ∈ S' := hzS' (Subgroup.mem_zpowers x)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hxS', hxH⟩

theorem eq_one_of_mem_theta {L T : Subgroup G} (hT : IsPGroup 3 T) {x : G}
    (hxθ : x ∈ inSubgroup (aschbacherSolvableCore 3) L) (hxT : x ∈ T) : x = 1 := by
  obtain ⟨l, hl, rfl⟩ := hxθ
  obtain ⟨k, hk⟩ := hT ⟨(l : G), hxT⟩
  have hlk : l ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 := orderOf_dvd_natCard (⟨l, hl⟩ : aschbacherSolvableCore 3 L)
  have h2 : orderOf (⟨l, hl⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hlk))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    have := congrArg (fun z : aschbacherSolvableCore 3 L => ((z : L) : G)) hj
    simpa using this
  · exfalso
    apply three_not_dvd_card_aschbacherSolvableCore (G := L)
    rw [hj] at h1
    exact (dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h1

theorem card_autThetaQuot_le {L Q : Subgroup G} (eL : lBar L ≃* projSL 3 (GaloisField 2 2))
    (hQ : IsPGroup 3 Q) : Nat.card (Sec4.autThetaQuot Q L) ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (MulAut (lBar L)) = 241920 := by
    have e := MulAut.congr (eL.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)))
    rw [Nat.card_congr e.toEquiv]
    apply KFacts.L34.card_mulAut
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hp : IsPGroup 3 (Sec4.autThetaQuot Q L) :=
    (((hQ.to_le inf_le_left).comap_subtype).map _).map _
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hdvd : Nat.card (Sec4.autThetaQuot Q L) ∣ 241920 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  rw [hm] at hdvd ⊢
  have hm3 : m ≤ 3 := by
    by_contra h
    have h4 : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h4
  calc 3 ^ m ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3
    _ = 27 := by norm_num

omit [Finite G] in
theorem conj_pow' (g x : G) (m : ℕ) : g * x ^ m * g⁻¹ = (g * x * g⁻¹) ^ m := by
  rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]

end Item2119End5Proof

open Item2119End5Proof

theorem item2127At_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hRank : Item2127Rank)
    (hStruct : Item2127Struct) : Item2127At := by
  intro G _ _ A E U c L d hP F hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hexp, hdF, h27⟩ := hStruct G A E U c L d hP F hF
  have hR := hRank G A E U c L d hP
  have hcfg := hP.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hdA : d ∈ A := hP.mem_d.1
  have hdL : d ∈ L := hP.mem_d.2
  have hd1 := hP.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hcfg).1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc : d ∉ Subgroup.zpowers c := Item2119End4Proof.not_mem_zpowers_symm hc3 hd1 hcd
  obtain ⟨hFe, -, hFAL, -, -⟩ := hF
  obtain ⟨eL⟩ := hP.l34
  set P₀ := A ⊔ F with hP₀
  have hP₀3 : IsPGroup 3 P₀ := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx c hcA)
  have hP₀C : P₀ ≤ Subgroup.centralizer ({c} : Set G) := sup_le hAc (hFAL.trans (sup_le hAc hLC))
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hP₀d : P₀ ≤ Subgroup.centralizer ({d} : Set G) := by
    apply sup_le
    · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx d hdA)
    · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm x hx d hdF)
  have hL3 : 3 ∣ Nat.card L := by
    have h1 := orderOf_dvd_natCard (⟨d, hdL⟩ : L)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd3 hd1] at h1
  have hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hge : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    have hL' : L.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 c := by
      have h1 := map_mem_thetaComponentsAt (MulAut.conj g) hLc
      rwa [MulAut.conj_apply, hge] at h1
    have h3L' : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hL3
    exact mem_normalizer_of_map_conj_eq (hP.unique _ hL' h3L')
  obtain ⟨T, hT, hP₀T⟩ := exists_isSylowOf_ge hP₀C hP₀3
  have hTC : T ≤ Subgroup.centralizer ({c} : Set G) := hT.le
  have hT3 : IsPGroup 3 T := hT.isPGroup
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hTC.trans hCN
  have hdecomp : ∀ y ∈ T, ∃ p ∈ P₀, p⁻¹ * y ∈ Sec4.thetaQuotCentralizer L := by
    have hle : Sec4.autThetaQuot P₀ L ≤ Sec4.autThetaQuot T L := by
      intro τ hτ
      obtain ⟨h, hN, hhP, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
      exact Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, hP₀T hhP, rfl⟩
    have hcardT := card_autThetaQuot_le eL hT3
    have heq : Sec4.autThetaQuot P₀ L = Sec4.autThetaQuot T L :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    intro y hy
    have hyρ : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hTN hy⟩) ∈
        Sec4.autThetaQuot T L := Sec4.mem_autThetaQuot_iff.mpr ⟨y, hTN hy, hy, rfl⟩
    rw [← heq] at hyρ
    obtain ⟨p, hpN, hpP, hpy⟩ := Sec4.mem_autThetaQuot_iff.mp hyρ
    refine ⟨p, hpP, ⟨⟨p, hpN⟩⁻¹ * ⟨y, hTN hy⟩, ?_, rfl⟩⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_mul, map_inv,
      map_inv, hpy, inv_mul_cancel]
  have hRd : ∀ r ∈ T, r ∈ Sec4.thetaQuotCentralizer L → r * d = d * r := by
    intro r hrT hrC
    have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hrC).2 d hdL
    have h2 : d⁻¹ * (r * d * r⁻¹) ∈ T :=
      T.mul_mem (T.inv_mem (hP₀T (Subgroup.mem_sup_left hdA)))
        (T.mul_mem (T.mul_mem hrT (hP₀T (Subgroup.mem_sup_left hdA))) (T.inv_mem hrT))
    have h3 := eq_one_of_mem_theta hT3 h1 h2
    calc r * d = d * (d⁻¹ * (r * d * r⁻¹)) * r := by group
      _ = d * r := by rw [h3, mul_one]
  have hTd : T ≤ Subgroup.centralizer ({d} : Set G) := by
    intro y hy
    obtain ⟨p, hp, hr⟩ := hdecomp y hy
    have hrT : p⁻¹ * y ∈ T := T.mul_mem (T.inv_mem (hP₀T hp)) hy
    have h1 := hRd _ hrT hr
    have h2 : p * d = d * p := Subgroup.mem_centralizer_singleton_iff.mp (hP₀d hp)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * d = p * ((p⁻¹ * y) * d) := by group
      _ = p * (d * (p⁻¹ * y)) := by rw [h1]
      _ = (p * d) * (p⁻¹ * y) := by group
      _ = d * y := by rw [h2]; group
  set H := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) with hH
  have hTH : T ≤ H := le_inf hTC hTd
  have hTsyl : IsSylowOf 3 T H := hT.of_le hTH inf_le_left
  obtain ⟨x, hxN, hx3, hxd, hxA, hxc⟩ := hP.mover
  obtain ⟨k, hk, hk0, hxck⟩ := exists_conj_eq_mul_pow hd3 hxA hcA hxc
  have hxH : x ∈ Subgroup.normalizer (H : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨hgc, hgd⟩ := hg
    have hgc' : Commute g c := (Subgroup.mem_centralizer_singleton_iff.mp hgc)
    have hgd' : Commute g d := (Subgroup.mem_centralizer_singleton_iff.mp hgd)
    have e1 : Commute (x * g * x⁻¹) (c * d ^ k) := by
      rw [← hxck]
      simpa [MulAut.conj_apply] using hgc'.map (MulAut.conj x)
    have e2 : Commute (x * g * x⁻¹) d := by
      have := hgd'.map (MulAut.conj x)
      simp only [MulAut.conj_apply] at this
      rwa [hxd] at this
    have e3 : Commute (x * g * x⁻¹) c := by
      have h4 : c = c * d ^ k * (d ^ k)⁻¹ := by group
      rw [h4]
      exact e1.mul_right (e2.pow_right k).inv_right
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr e3.eq,
      Subgroup.mem_centralizer_singleton_iff.mpr e2.eq⟩
  obtain ⟨P₁, hP₁, hxP₁⟩ := exists_normalized_isSylowOf hxH (n := 1) (by simpa using hx3)
  obtain ⟨h, hhH, hTeq⟩ := exists_conj_of_isSylowOf hP₁ hTsyl
  have hhc : h * c * h⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hhH.1, mul_inv_cancel_right]
  have hhd : h * d * h⁻¹ = d := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hhH.2, mul_inv_cancel_right]
  set x' := h * x * h⁻¹ with hx'
  have hx'T : x' ∈ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [hTeq] at ht ⊢
    obtain ⟨t₁, ht₁, rfl⟩ := ht
    refine ⟨x * t₁ * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxP₁ t₁).mp ht₁, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx']
    group
  have hx'c : x' * c * x'⁻¹ = c * d ^ k := by
    calc x' * c * x'⁻¹ = h * (x * (h⁻¹ * c * h) * x⁻¹) * h⁻¹ := by rw [hx']; group
      _ = h * (c * d ^ k) * h⁻¹ := by
          rw [show h⁻¹ * c * h = c by
            calc h⁻¹ * c * h = h⁻¹ * (h * c * h⁻¹) * h := by rw [hhc]
              _ = c := by group, hxck]
      _ = (h * c * h⁻¹) * (h * d * h⁻¹) ^ k := by rw [← conj_pow']; group
      _ = c * d ^ k := by rw [hhc, hhd]
  have hcube : ∀ y ∈ T, y ^ 3 ∈ Sec4.thetaQuotCentralizer L := by
    intro y hy
    obtain ⟨p, hp, hr⟩ := hdecomp y hy
    have hpN : p ∈ Subgroup.normalizer (L : Set G) := hTN (hP₀T hp)
    have hp3 : p ^ 3 = 1 := hexp p hp
    set r := p⁻¹ * y with hrdef
    have hyr : y = p * r := by rw [hrdef]; group
    have e1 : y ^ 3 = (p * r * p⁻¹) * ((p * p) * r * (p * p)⁻¹) * ((p * p * p) * r *
        (p * p * p)⁻¹) * (p * p * p) := by rw [hyr, pow_three]; group
    have hp3' : p * p * p = 1 := by rw [mul_assoc, ← pow_three]; exact hp3
    rw [e1, hp3', mul_one, one_mul, inv_one, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Sec6.conj_mem_thetaQuotCentralizer hr hpN)
      (Sec6.conj_mem_thetaQuotCentralizer hr (Subgroup.mul_mem _ hpN hpN))) hr
  have hP₀eq : P₀ = T := by
    by_contra hne
    obtain ⟨y, hyT, hyP⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hP₀T hne)
    obtain ⟨p, hp, hr⟩ := hdecomp y hyT
    set r := p⁻¹ * y with hrdef
    have hrT : r ∈ T := T.mul_mem (T.inv_mem (hP₀T hp)) hyT
    have hrc : r ∉ Subgroup.zpowers c := by
      intro hrc
      apply hyP
      have hrP : r ∈ P₀ := Subgroup.mem_sup_left ((Subgroup.zpowers_le.mpr hcA) hrc)
      rw [show y = p * r by rw [hrdef]; group]
      exact P₀.mul_mem hp hrP
    obtain ⟨j₀, hj₀⟩ := hT3 ⟨r, hrT⟩
    have hex : ∃ j : ℕ, r ^ 3 ^ j = 1 := ⟨j₀, by simpa using congrArg Subtype.val hj₀⟩
    classical
    set j := Nat.find hex with hj
    have hjr : r ^ 3 ^ j = 1 := Nat.find_spec hex
    have hjmin : ∀ i < j, r ^ 3 ^ i ≠ 1 := fun i hi => Nat.find_min hex hi
    have hRmem : ∀ m : ℕ, r ^ m ∈ Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G) ⊓ Sec4.thetaQuotCentralizer L := fun m =>
      ⟨⟨Subgroup.pow_mem _ (hTC hrT) m, Subgroup.pow_mem _ (hTd hrT) m⟩, Subgroup.pow_mem _ hr m⟩
    have hj2 : 2 ≤ j := by
      by_contra hj2
      interval_cases j
      · exact hrc (by rw [pow_zero, pow_one] at hjr; rw [hjr]; exact Subgroup.one_mem _)
      · exact hrc (hR r ⟨⟨hTC hrT, hTd hrT⟩, hr⟩ (by simpa using hjr))
    set z := r ^ 3 ^ (j - 2) with hzdef
    have hz3 : z ^ 3 ≠ 1 := by
      rw [hzdef, ← pow_mul, ← pow_succ]
      exact hjmin _ (by omega)
    have hz9 : (z ^ 3) ^ 3 = 1 := by
      have harith : 3 ^ (j - 2) * (3 * 3) = 3 ^ j := by
        rw [← mul_assoc, ← pow_succ, ← pow_succ]
        congr 1
        omega
      rw [hzdef, ← pow_mul, ← pow_mul, harith]
      exact hjr
    have hz3c : z ^ 3 ∈ Subgroup.zpowers c := by
      apply hR
      · rw [hzdef, ← pow_mul]
        exact hRmem _
      · exact hz9
    have hcz : c ∈ Subgroup.zpowers (z ^ 3) :=
      Item21Late2Proof.mem_zpowers_of_mem hc3 hz3c hz3 (Subgroup.mem_zpowers c)
    have hzT : z ∈ T := Subgroup.pow_mem _ hrT _
    have hx'zT : x' * z * x'⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hx'T z).mp hzT
    have hw3 : x' * z ^ 3 * x'⁻¹ ∈ Subgroup.zpowers c := by
      apply hR
      · rw [conj_pow']
        exact ⟨⟨Subgroup.pow_mem _ (hTC hx'zT) 3, Subgroup.pow_mem _ (hTd hx'zT) 3⟩,
          hcube _ hx'zT⟩
      · rw [conj_pow', ← pow_mul, show 3 * 3 = 9 by norm_num, ← conj_pow',
          show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hz9, mul_one, mul_inv_cancel]
    have hx'cmem : x' * c * x'⁻¹ ∈ Subgroup.zpowers c := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcz
      have e2 : x' * c * x'⁻¹ = (x' * z ^ 3 * x'⁻¹) ^ m := by
        rw [← hm, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      rw [e2]
      exact Subgroup.zpow_mem _ hw3 m
    rw [hx'c] at hx'cmem
    have hdk : d ^ k ∈ Subgroup.zpowers c := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) hx'cmem
      simpa using this
    apply hdc
    interval_cases k
    · exact absurd rfl hk0
    · simpa using hdk
    · have h1 := Subgroup.pow_mem _ hdk 2
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hd3, one_mul, pow_one] at h1
      exact h1
  rw [hP₀eq]
  exact hT

end CFSG.RankThree.PartTwo.Sec21
