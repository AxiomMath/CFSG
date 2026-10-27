module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTrans
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofE
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1617

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS CFSG.ABGLocalTools
open scoped Pointwise

theorem exists_conj_eq_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q K : Subgroup G} (hP : IsSylowOf p P K) (hQ : IsSylowOf p Q K) :
    ∃ k ∈ K, Q = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨SP, rfl⟩ := hP
  obtain ⟨SQ, rfl⟩ := hQ
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K SP SQ
  refine ⟨k, k.2, ?_⟩
  rw [← hk, Sylow.coe_subgroup_smul]
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.conj_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨k * z * k⁻¹, ⟨z, hz, rfl⟩, by simp⟩

theorem exists_isSylowOf_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (hP : IsPGroup p P) (hPK : P ≤ K) : ∃ T, IsSylowOf p T K ∧ P ≤ T := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨T₀, hT₀⟩ := hP'.exists_le_sylow
  refine ⟨(T₀ : Subgroup K).map K.subtype, ⟨T₀, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hT₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem eq_one_of_isPGroup_of_not_dvd {G : Type*} [Group G] {P T : Subgroup G}
    (hP : IsPGroup 3 P) (hT : ¬ 3 ∣ Nat.card T) [Finite T] {x : G} (hxP : x ∈ P) (hxT : x ∈ T) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card T := by
    have := orderOf_dvd_natCard (⟨x, hxT⟩ : T)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card T) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_thetaG {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {t : G} (ht : t ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype) :
    g * t * g⁻¹ ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
  obtain ⟨t', ht', rfl⟩ := ht
  have hmap := Sec4.map_aschbacherSolvableCore (conjL L hg)
  have hmem : conjL L hg t' ∈ aschbacherSolvableCore 3 ↥L := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ ht'
  exact ⟨_, hmem, conjL_apply_coe L hg t'⟩

theorem not_three_dvd_card_thetaG (L : Subgroup G) :
    ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥L).map L.subtype) := by
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1

theorem isSylowOf_sup_thetaG {L D : Subgroup G} (hDL : D ≤ L) (hD9 : Nat.card D = 9)
    (hD3 : IsPGroup 3 D) :
    Nat.card ((aschbacherSolvableCore 3 ↥L).map L.subtype ⊔ D : Subgroup G) =
        Nat.card ((aschbacherSolvableCore 3 ↥L).map L.subtype) * 9 ∧
      IsSylowOf 3 D ((aschbacherSolvableCore 3 ↥L).map L.subtype ⊔ D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θG := (aschbacherSolvableCore 3 ↥L).map L.subtype with hθG
  have hθ3 := not_three_dvd_card_thetaG L
  have hDN : D ≤ Subgroup.normalizer (θG : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun t ht => conj_mem_thetaG (Subgroup.le_normalizer (hDL hd)) ht
  have hbot : θG ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_not_dvd hD3 hθ3 hx.2 hx.1)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hDN
  rw [hbot, Subgroup.card_bot, mul_one, hD9, sup_comm] at h1
  refine ⟨h1, isSylowOf_of_card le_sup_right ?_⟩
  rw [h1, hD9, Nat.factorization_mul (by intro h0; rw [h0] at hθ3; simp at hθ3) (by norm_num),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hθ3, zero_add,
    show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same]

theorem mem_zpowers_of_trivial {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {n : ℕ}
    (hz : IsZ3LThreeTwo A c L n) {u : G} (hu3 : u ^ 3 = 1)
    (huc : u ∈ Subgroup.centralizer ({c} : Set G))
    (htriv : ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype) :
    u ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, h9, hAle⟩ := facts_of_isZ3 h hz
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.le_centralizer
  have hAeq := eq_zpowers_sup_inf h.mem_A hAle hLc
  have huN : u ∈ Subgroup.normalizer (L : Set G) := centralizer_le_normalizer_L h hz huc
  set D := A ⊓ L with hDdef
  set θG := (aschbacherSolvableCore 3 ↥L).map L.subtype with hθG
  have hθL : θG ≤ L := Subgroup.map_subtype_le _
  have hθ3 := not_three_dvd_card_thetaG L
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  obtain ⟨-, hDsyl⟩ := isSylowOf_sup_thetaG (inf_le_right : D ≤ L) h9 hD3
  set Dt := θG ⊔ D with hDt
  have hDtL : Dt ≤ L := sup_le hθL inf_le_right
  have hDN : D ≤ Subgroup.normalizer (θG : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun t ht =>
      conj_mem_thetaG (Subgroup.le_normalizer hd.2) ht
  have hDtset : (Dt : Set G) = (θG : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left θG D hDN
  have huDt : u ∈ Subgroup.normalizer (Dt : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' : y ∈ (θG : Set G) * (D : Set G) := hDtset ▸ hy
    obtain ⟨t, ht, d, hd, rfl⟩ := hy'
    have h1 : u * t * u⁻¹ ∈ θG := conj_mem_thetaG huN ht
    have h2 : u * d * u⁻¹ * d⁻¹ ∈ θG := htriv d hd.2
    have heq : u * (t * d) * u⁻¹ = (u * t * u⁻¹) * (u * d * u⁻¹ * d⁻¹) * d := by group
    rw [heq]
    exact Subgroup.mul_mem_sup (θG.mul_mem h1 h2) hd
  have hu3g : IsPGroup 3 (Subgroup.zpowers u) := by
    have hdvd : Nat.card (Subgroup.zpowers u) ∣ 3 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hu3
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hi
  set X := Subgroup.zpowers u ⊔ Dt with hX
  have hXN : X ≤ Subgroup.normalizer (Dt : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr huDt) Subgroup.le_normalizer
  obtain ⟨T, hTsyl, huT⟩ := exists_isSylowOf_le hu3g (le_sup_left : Subgroup.zpowers u ≤ X)
  have hSsyl : IsSylowOf 3 (T ⊓ Dt) Dt := hTsyl.inf_of_le_normalizer le_sup_right hXN
  obtain ⟨m, hm, hSeq⟩ := exists_conj_eq_of_isSylowOf hDsyl hSsyl
  have hm' : m ∈ (θG : Set G) * (D : Set G) := hDtset ▸ hm
  obtain ⟨t, ht, d₀, hd₀, rfl⟩ := hm'
  have htL : t ∈ L := hθL ht
  have huS : ∀ s ∈ T ⊓ Dt, u * s = s * u := by
    intro s hs
    have huT' : u ∈ T := huT (Subgroup.mem_zpowers u)
    have h1 : u * s * u⁻¹ * s⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem huT' hs.1) (T.inv_mem huT')) (T.inv_mem hs.1)
    have h2 : u * s * u⁻¹ * s⁻¹ ∈ θG := htriv s (hDtL hs.2)
    have h3 := eq_one_of_isPGroup_of_not_dvd hTsyl.isPGroup hθ3 h1 h2
    calc u * s = u * s * u⁻¹ * s⁻¹ * s * u := by group
      _ = s * u := by rw [h3, one_mul]
  set u' := t⁻¹ * u * t with hu'
  have hu'D : ∀ d ∈ D, d * u' = u' * d := by
    intro d hd
    have hs : t * d * t⁻¹ ∈ T ⊓ Dt := by
      rw [hSeq]
      refine ⟨d₀⁻¹ * d * d₀, ?_, ?_⟩
      · exact D.mul_mem (D.mul_mem (D.inv_mem hd₀) hd) hd₀
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have h1 := huS _ hs
    calc d * u' = t⁻¹ * ((t * d * t⁻¹) * u) * t := by rw [hu']; group
      _ = t⁻¹ * (u * (t * d * t⁻¹)) * t := by rw [h1]
      _ = u' * d := by rw [hu']; group
  have hu'c : c * u' = u' * c := by
    have htc : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hLc htL)
    have huc' : u * c = c * u := Subgroup.mem_centralizer_singleton_iff.mp huc
    have htc' : t⁻¹ * c = c * t⁻¹ := by
      calc t⁻¹ * c = t⁻¹ * (c * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * c) * t⁻¹ := by rw [htc]
        _ = c * t⁻¹ := by group
    calc c * u' = (c * t⁻¹) * u * t := by rw [hu']; group
      _ = (t⁻¹ * c) * u * t := by rw [htc']
      _ = t⁻¹ * (c * u) * t := by group
      _ = t⁻¹ * (u * c) * t := by rw [huc']
      _ = t⁻¹ * u * (c * t) := by group
      _ = t⁻¹ * u * (t * c) := by rw [htc]
      _ = u' * c := by rw [hu']; group
  have hAu' : A ≤ Subgroup.centralizer ({u'} : Set G) := by
    rw [hAeq]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hu'c))
      (fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr (hu'D d hd))
  have hu'3 : u' ^ 3 = 1 := by
    have : t⁻¹ * u * t = t⁻¹ * u * t⁻¹⁻¹ := by rw [inv_inv]
    rw [hu', this, conj_pow, hu3]
    group
  have hu'A : u' ∈ A := mem_of_mem_partTwoF h.mem_partTwoF hu'3 hAu'
  have hu'triv : ∀ y ∈ L, u' * y * u'⁻¹ * y⁻¹ ∈ θG := by
    intro y hy
    have hz : t * y * t⁻¹ ∈ L := L.mul_mem (L.mul_mem htL hy) (L.inv_mem htL)
    have h1 := htriv _ hz
    have h2 := conj_mem_thetaG (Subgroup.le_normalizer (L.inv_mem htL)) h1
    have heq : t⁻¹ * (u * (t * y * t⁻¹) * u⁻¹ * (t * y * t⁻¹)⁻¹) * t⁻¹⁻¹ =
        u' * y * u'⁻¹ * y⁻¹ := by rw [hu']; group
    rwa [heq] at h2
  have hu'sec : u' ∈ Late.sectionCentralizer A L θG := ⟨hu'A, hu'triv⟩
  rw [h.sectionCentralizer_eq] at hu'sec
  have htc : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hLc htL)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu'sec
  have htck : t * c ^ k = c ^ k * t := (Commute.zpow_right htc k).eq
  have hueq : u = c ^ k := by
    calc u = t * u' * t⁻¹ := by rw [hu']; group
      _ = t * c ^ k * t⁻¹ := by rw [hk]
      _ = c ^ k := by rw [htck]; group
  rw [hueq]
  exact Subgroup.zpow_mem_zpowers c k

theorem center_eq_bot_of_isZ3 {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {n : ℕ}
    (hz : IsZ3LThreeTwo A c L n) :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
  obtain ⟨hn, hiso, -⟩ := hz
  have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
  obtain ⟨-, h2⟩ := Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hiso
  obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := exists_projImage_model hn hiso
  have hq2 : 2 < 2 ^ n := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  exact center_eq_bot_of_mulEquiv φ (center_projImage_slPi hKf hq hq2)

theorem card_inf_eq_nine_of_inner {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {n : ℕ}
    (hz : IsZ3LThreeTwo A c L n) {A' : Subgroup G} (hA'ab : CFSG.Assembly.IsElemAbelian 3 A')
    (hA'27 : Nat.card A' = 27) (hcA' : c ∈ A')
    (hA'max : ∀ x : G, x ^ 3 = 1 → A' ≤ Subgroup.centralizer ({x} : Set G) → x ∈ A')
    (hinner : ∀ a ∈ A', ∃ l ∈ L, ∀ y ∈ L,
      a * y * a⁻¹ * (l * y * l⁻¹)⁻¹ ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype) :
    Nat.card (A' ⊓ L : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcL, -, -⟩ := facts_of_isZ3 h hz
  have hCN := centralizer_le_normalizer_L h hz
  have hZ := center_eq_bot_of_isZ3 h hz
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set θG := θ.map L.subtype with hθG
  have hθ3 := not_three_dvd_card_thetaG L
  have hθnorm : θ.Normal := by
    have := Sec4.aschbacherSolvableCore_characteristic ↥L
    infer_instance
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA'ab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA'C : A' ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hA'comm a ha c hcA')
  have hA'N : A' ≤ Subgroup.normalizer (L : Set G) := hA'C.trans hCN
  set ρA' : ↥A' →* MulAut (↥L ⧸ θ) :=
    ((Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom).comp (Subgroup.inclusion hA'N)
    with hρA'
  have hρapp : ∀ (a : ↥A') (y : ↥L), ρA' a (y : ↥L ⧸ θ) =
      ((L.normalizerMonoidHom ⟨a, hA'N a.2⟩ y : ↥L) : ↥L ⧸ θ) := fun a y => rfl
  have hker : ∀ a : ↥A', ρA' a = 1 ↔ (a : G) ∈ Subgroup.zpowers c := by
    intro a
    rw [show ρA' a = Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨a, hA'N a.2⟩) from rfl,
      thetaQuotMulAut_eq_one_iff]
    constructor
    · exact fun htriv => mem_zpowers_of_trivial h hz (hA'ab.2 a a.2) (hA'C a.2) htriv
    · intro hac l hl
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hac
      rw [← hk]
      have hcl : c ^ k * l = l * c ^ k :=
        (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)).symm
          k).eq
      rw [hcl, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hkercard : Nat.card ρA'.ker = 3 := by
    have : ρA'.ker = (Subgroup.zpowers c).subgroupOf A' := by
      ext a
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rw [this, card_subgroupOf_of_le (Subgroup.zpowers_le.mpr hcA'), h.card_zpowers]
  have hR9 : Nat.card ρA'.range = 9 := by
    have h1 := card_eq_card_range_mul_card_ker ρA'
    rw [hA'27, hkercard] at h1
    omega
  set ι : ↥L ⧸ θ →* MulAut (↥L ⧸ θ) := MulAut.conj with hι
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.center (↥L ⧸ θ) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut (↥L ⧸ θ) => σ z) (MonoidHom.mem_ker.mp hx)
      simp only [hι, MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * x = x * z * x⁻¹ * x := by rw [h1]
        _ = x * z := by group
    rw [hZ] at hxc
    exact hxc
  have hιker : Nat.card ι.ker = 1 := by
    rw [(MonoidHom.ker_eq_bot_iff ι).mpr hιinj, Subgroup.card_bot]
  have hRι : ρA'.range ≤ ι.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨l, hl, hly⟩ := hinner a a.2
    refine ⟨((⟨l, hl⟩ : ↥L) : ↥L ⧸ θ), ?_⟩
    ext z
    induction z using QuotientGroup.induction_on with
    | H y =>
      simp only [hι, MulAut.conj_apply]
      rw [hρapp, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq]
      obtain ⟨t, ht, hte⟩ := hly y y.2
      set p := L.normalizerMonoidHom ⟨a, hA'N a.2⟩ y with hp
      set q : ↥L := ⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹ with hq
      have hm : (p : G) = a * y * a⁻¹ := Sec4.normalizerMonoidHom_apply_coe _ _
      have htm : t = p * q⁻¹ :=
        Subtype.ext (by simp only [hq, Subgroup.coe_mul, Subgroup.coe_inv, hm]; exact hte)
      rw [htm] at ht
      have h2 := hθnorm.conj_mem _ (θ.inv_mem ht) p⁻¹
      have heq : p⁻¹ * (p * q⁻¹)⁻¹ * p⁻¹⁻¹ = (q⁻¹ * p)⁻¹ := by group
      rw [heq] at h2
      simpa using θ.inv_mem h2
  set D₁ := ρA'.range.comap ι with hD₁
  have hD₁9 : Nat.card D₁ = 9 := by rw [hD₁, card_comap_of_le_range ι hRι, hR9, hιker]
  have hD₁exp : ∀ z ∈ D₁, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨b, hb⟩ := hz
    apply hιinj
    rw [map_pow, map_one, ← hb, ← map_pow]
    have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hA'ab.2 b b.2)
    rw [hb3, map_one]
  have hD₁comm : ∀ (a : ↥A') (z : ↥L ⧸ θ), z ∈ D₁ → ρA' a z = z := by
    intro a z hz
    obtain ⟨b, hb⟩ := hz
    obtain ⟨w, hw⟩ := hRι ⟨a, rfl⟩
    have hab : ρA' a * ρA' b = ρA' b * ρA' a := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA'comm a a.2 b b.2)
    have hwz : w * z = z * w := by
      apply hιinj
      rw [map_mul, map_mul, hw, ← hb]
      exact hab
    rw [← hw]
    simp only [hι, MulAut.conj_apply]
    rw [hwz, mul_inv_cancel_right]
  set Dt : Subgroup G := (D₁.comap (QuotientGroup.mk' θ)).map L.subtype with hDt
  have hDtL : Dt ≤ L := Subgroup.map_subtype_le _
  have hDtcard : Nat.card Dt = Nat.card θG * 9 := by
    rw [hDt, Subgroup.card_map_of_injective L.subtype_injective,
      card_comap_of_le_range (QuotientGroup.mk' θ)
        (by rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective θ)]
            exact le_top),
      hD₁9, QuotientGroup.ker_mk', hθG, Subgroup.card_map_of_injective L.subtype_injective,
      mul_comm]
  have hact : ∀ a ∈ A', ∀ x ∈ Dt, a * x * a⁻¹ ∈ Dt ∧ a * x * a⁻¹ * x⁻¹ ∈ θG := by
    intro a ha x hx
    obtain ⟨x', hx', rfl⟩ := hx
    have h1 := hD₁comm ⟨a, ha⟩ _ hx'
    rw [QuotientGroup.mk'_apply, hρapp] at h1
    set p := L.normalizerMonoidHom ⟨a, hA'N ha⟩ x' with hp
    have hm : (p : G) = a * x' * a⁻¹ := Sec4.normalizerMonoidHom_apply_coe _ _
    rw [QuotientGroup.eq] at h1
    refine ⟨⟨p, ?_, hm⟩, ?_⟩
    · change QuotientGroup.mk' θ p ∈ D₁
      have : QuotientGroup.mk' θ p = QuotientGroup.mk' θ x' := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact h1
      rw [this]
      exact hx'
    · have h2 := hθnorm.conj_mem _ (θ.inv_mem h1) x'
      have heq : x' * (p⁻¹ * x')⁻¹ * x'⁻¹ = p * x'⁻¹ := by group
      rw [heq] at h2
      refine ⟨_, h2, ?_⟩
      simp [hm]
  have hDtN : A' ⊔ Dt ≤ Subgroup.normalizer (Dt : Set G) := by
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    exact Subgroup.mem_normalizer_fintype fun x hx => (hact a ha x hx).1
  have hA'3 : IsPGroup 3 A' := IsPGroup.of_card (n := 3) (by rw [hA'27]; norm_num)
  obtain ⟨T, hTsyl, hA'T⟩ := exists_isSylowOf_le hA'3 (le_sup_left : A' ≤ A' ⊔ Dt)
  have hSsyl : IsSylowOf 3 (T ⊓ Dt) Dt := hTsyl.inf_of_le_normalizer le_sup_right hDtN
  have hS9 : Nat.card (T ⊓ Dt : Subgroup G) = 9 := by
    rw [hSsyl.card_eq, hDtcard,
      Nat.factorization_mul (by intro h0; rw [h0] at hθ3; simp at hθ3) (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hθ3, zero_add,
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
  have hSA' : T ⊓ Dt ≤ A' ⊓ L := by
    intro s hs
    refine ⟨hA'max s ?_ (fun a ha => ?_), hDtL hs.2⟩
    ·
      obtain ⟨s', hs', rfl⟩ := hs.2
      have h1 : QuotientGroup.mk' θ (s' ^ 3) = 1 := by
        rw [map_pow]
        exact hD₁exp _ hs'
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 : ((s' : G)) ^ 3 ∈ θG := ⟨_, h1, by simp⟩
      have h3 : ((s' : G)) ^ 3 ∈ T ⊓ Dt := (T ⊓ Dt).pow_mem hs 3
      exact eq_one_of_isPGroup_of_not_dvd hSsyl.isPGroup hθ3 h3 h2
    ·
      have haT : a ∈ T := hA'T ha
      have h1 : a * s * a⁻¹ * s⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem haT hs.1) (T.inv_mem haT)) (T.inv_mem hs.1)
      have h2 : a * s * a⁻¹ * s⁻¹ ∈ θG := (hact a ha s hs.2).2
      have h3 : a * s * a⁻¹ * s⁻¹ ∈ T ⊓ Dt :=
        ⟨h1, Dt.mul_mem (hact a ha s hs.2).1 (Dt.inv_mem hs.2)⟩
      have h4 := eq_one_of_isPGroup_of_not_dvd hSsyl.isPGroup hθ3 h3 h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * s = a * s * a⁻¹ * s⁻¹ * s * a := by group
        _ = s * a := by rw [h4, one_mul]
  have h9le : 9 ≤ Nat.card (A' ⊓ L : Subgroup G) := hS9 ▸ Subgroup.card_le_of_le hSA'
  have hdvd : Nat.card (A' ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA'27]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (A' ⊓ L : Subgroup G) ≠ 27 := by
    intro h27
    have heq : A' ⊓ L = A' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA'27])
    have hc' : c ∈ A' ⊓ L := by rw [heq]; exact hcA'
    exact hcL hc'.2
  obtain ⟨i, hi, hiA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · rw [hiA] at h9le; norm_num at h9le
  · rw [hiA] at h9le; norm_num at h9le
  · rw [hiA]; norm_num
  · exact absurd (hiA.trans (by norm_num)) hne

end CFSG.RankThree.PartTwo.Sec16.Proof1617

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def KS1618Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → (∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x ∈ A) →
    ∀ g : G, g ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) → g * c * g⁻¹ ∈ A →
      ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, (g⁻¹ * a * g) * y * (g⁻¹ * a * g)⁻¹ * (l * y * l⁻¹)⁻¹ ∈
        (aschbacherSolvableCore 3 ↥L).map L.subtype

variable {G : Type} [Group G] [Finite G]

theorem ks1618Card_of (h1616 : Step1616) (hI : KS1618Inner) : KS1618Card := by
  intro G _ _ A c L h h1617 g hg hgc
  obtain ⟨n, hz⟩ := h1616 G A c L h
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hmemA' : ∀ x, x ∈ A' ↔ g * x * g⁻¹ ∈ A := fun x => by
    rw [hA', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hA'ab : CFSG.Assembly.IsElemAbelian 3 A' :=
    Proof1617.isElemAbelian_map' _ h.isElemAbelian
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, h.card_eq]
  have hcA' : c ∈ A' := (hmemA' c).mpr hgc
  have hA'max : ∀ x : G, x ^ 3 = 1 → A' ≤ Subgroup.centralizer ({x} : Set G) → x ∈ A' := by
    intro x hx3 hA'x
    rw [hmemA']
    refine mem_of_mem_partTwoF h.mem_partTwoF ?_ (fun a ha => ?_)
    · rw [conj_pow, hx3]
      group
    · have hga : g⁻¹ * a * g ∈ A' := by
        rw [hmemA']
        simpa [mul_assoc] using ha
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hA'x hga)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * a := by group
  have hinner : ∀ a' ∈ A', ∃ l ∈ L, ∀ y ∈ L,
      a' * y * a'⁻¹ * (l * y * l⁻¹)⁻¹ ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
    intro a' ha'
    obtain ⟨l, hl, hly⟩ := hI G A c L h h1617 g hg hgc (g * a' * g⁻¹) ((hmemA' a').mp ha')
    refine ⟨l, hl, fun y hy => ?_⟩
    have h1 := hly y hy
    have heq : g⁻¹ * (g * a' * g⁻¹) * g = a' := by group
    rwa [heq] at h1
  have h9 := Proof1617.card_inf_eq_nine_of_inner h hz hA'ab hA'27 hcA' hA'max hinner
  have hAA' : A'.map (MulAut.conj g).toMonoidHom = A := by
    rw [hA', Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
  have heq : A ⊓ L.map (MulAut.conj g).toMonoidHom =
      (A' ⊓ L).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hAA']
  rw [heq, Subgroup.card_map_of_injective (MulAut.conj g).injective, h9]

end CFSG.RankThree.PartTwo.Sec16
