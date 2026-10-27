module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4312Rank
public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LieType.SteinbergBRUnitaryThreePerfect
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Y

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436
open scoped MatrixGroups commutatorElement

namespace L4312

theorem eq_or_isPGroup_of_sl2 {Ω : Type*} [Group Ω] [Finite Ω] {K : Subgroup Ω}
    (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (χ : ↥K →* SL(2, F)) (hχ : Function.Surjective χ) (hχk : IsPGroup 2 χ.ker)
    (N : Subgroup Ω) (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set Ω)) :
    N = K ∨ IsPGroup 2 ↥N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup ↥K := N.subgroupOf K with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  have hsimp : IsSimpleGroup SL(2, F) := Vol2Native.A312L.sl2_isSimple hF4
  have hNm : (N'.map χ).Normal := hN'n.map χ hχ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map χ) with h | h
  · right
    have hle : N' ≤ χ.ker := (Subgroup.map_eq_bot_iff _).mp h
    intro x
    have hx' : (⟨(x : Ω), hNK x.2⟩ : ↥K) ∈ χ.ker := hle (by
      rw [hN', Subgroup.mem_subgroupOf]
      exact x.2)
    obtain ⟨k, hk⟩ := hχk ⟨_, hx'⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥χ.ker => ((z : ↥K) : Ω)) hk
    simpa using this
  · left
    have hKq : Group.IsPerfect (↥K ⧸ N') := by
      have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKp
      exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N')
    have hq2 : IsPGroup 2 (↥K ⧸ N') := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N' z
      obtain ⟨u, hu, hug⟩ : χ g ∈ N'.map χ := h ▸ Subgroup.mem_top _
      have hk : u⁻¹ * g ∈ χ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hug, inv_mul_cancel]
      obtain ⟨e, he⟩ := hχk ⟨_, hk⟩
      have he' : (u⁻¹ * g) ^ 2 ^ e = 1 := congrArg Subtype.val he
      refine ⟨e, ?_⟩
      have hu1 : QuotientGroup.mk' N' u = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hu
      have e1 : QuotientGroup.mk' N' g = QuotientGroup.mk' N' (u⁻¹ * g) := by
        rw [map_mul, map_inv, hu1, inv_one, one_mul]
      rw [e1, ← map_pow, he', map_one]
    have : Group.IsNilpotent (↥K ⧸ N') := hq2.isNilpotent
    have hsolv : Group.IsSolvable ↥(⊤ : Subgroup (↥K ⧸ N')) := by
      have : Group.IsSolvable (↥K ⧸ N') := inferInstance
      exact Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup (↥K ⧸ N')).subtype)
        Subtype.val_injective
    have htop : ⁅(⊤ : Subgroup (↥K ⧸ N')), ⊤⁆ = ⊤ := Group.isPerfect_def.mp hKq
    have hbot := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable htop
    have hN'top : N' = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : QuotientGroup.mk' N' g ∈ (⊤ : Subgroup (↥K ⧸ N')) := Subgroup.mem_top _
      rw [hbot, Subgroup.mem_bot] at hg
      exact (QuotientGroup.eq_one_iff g).mp hg
    refine le_antisymm hNK fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ N' := hN'top ▸ Subgroup.mem_top _
    rw [hN', Subgroup.mem_subgroupOf] at this
    exact this

end L4312

variable {G : Type} [Group G] [Finite G]

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem ZS_isPGroup : IsPGroup 2 ↥ZS :=
  (isPGroup_q4311 I K).to_le (s.ZS_le_U.trans inf_le_left)

theorem ZS_comm {a b : G} (ha : a ∈ ZS) (hb : b ∈ ZS) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (s.ZS_le_U hb).2 a (s.ZS_le_U ha).1

theorem ZS_ne_bot : ZS ≠ ⊥ := by
  intro h
  obtain ⟨z₀, hz₀⟩ := s.β_bij.2 (Multiplicative.ofAdd ![1, 0, 0])
  have hz : (z₀ : G) ∈ ZS := (s.ZS_iff z₀).mpr ⟨1, by rw [hz₀, toAdd_ofAdd, one_smul]⟩
  rw [h, Subgroup.mem_bot] at hz
  have h1 : z₀ = 1 := Subtype.ext hz
  rw [h1, map_one] at hz₀
  have := congrFun (congrArg Multiplicative.toAdd hz₀) 0
  simp at this

theorem ZS_le_centralizer : ZS ≤ Subgroup.centralizer (ZS : Set G) := fun _ hz =>
  Subgroup.mem_centralizer_iff.mpr fun _ hw => s.ZS_comm hw hz

theorem ZS_le_pCoreOf_GZ : ZS ≤ pCoreOf 2 (Subgroup.normalizer (ZS : Set G)) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    s.ZS_isPGroup

theorem ZS_le_pCoreOf_H₀ : ZS ≤ pCoreOf 2 (Subgroup.centralizer (ZS : Set G)) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 s.ZS_le_centralizer
    (Subgroup.centralizer_le_normalizer _) s.ZS_isPGroup

theorem inH_GZ : InH T (Subgroup.normalizer (ZS : Set G)) :=
  ⟨s.T_le_normalizer_ZS, fun h => s.ZS_ne_bot (le_bot_iff.mp (h ▸ s.ZS_le_pCoreOf_GZ))⟩

theorem sqtkGroup_GZ : SQTKGroup ↥(Subgroup.normalizer (ZS : Set G)) := by
  have hyp := s.sk.base.hyp
  have := hyp.simple
  exact InternalSec.sqtkGroup_of_localSQTK (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1 s.inH_GZ.2

theorem exists_odd_prime_dvd : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ m - 1 := by
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) s.two_le
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by have := s.two_le; omega)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  omega

theorem exists_elt_Y {p : ℕ} (hpn : p ∣ 2 ^ m - 1) :
    ∃ y' ∈ Subgroup.zpowers y, orderOf y' = p := by
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) s.two_le
  have hne : orderOf y ≠ 0 := by rw [s.orderOf_y]; omega
  have hdvd : p ∣ orderOf y := by rw [s.orderOf_y]; exact hpn
  exact ⟨y ^ (orderOf y / p), Subgroup.npow_mem_zpowers y _, orderOf_pow_orderOf_div hne hdvd⟩

theorem not_mem_centralizer_ZS {y' : G} (hy' : y' ∈ Subgroup.zpowers y) (hy1 : y' ≠ 1) :
    y' ∉ Subgroup.centralizer (ZS : Set G) := fun hc =>
  hy1 (s.Y_faithful hy' fun z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp hc z hz).symm, mul_inv_cancel_right])

theorem dvd_card_K₂ {p : ℕ} (hpn : p ∣ 2 ^ m - 1) : p ∣ Nat.card ↥K₂ := by
  have h1 : Nat.card SL(2, F) ∣ Nat.card ↥K₂ :=
    Subgroup.card_dvd_of_surjective s.levi_surjective
  have h2 : Nat.card SL(2, F) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [CFSG.GorensteinWalter.sl2_card_formula F, Nat.card_eq_fintype_card, s.card_F]
  have h3 : 2 ^ m - 1 ∣ (2 ^ m) ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 2
    rwa [one_pow] at this
  refine dvd_trans ?_ h1
  rw [h2]
  exact dvd_mul_of_dvd_right (hpn.trans h3) _

theorem exists_elt_K₂ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ m - 1) {y' : G}
    (hy' : y' ∈ Subgroup.zpowers y) (hy'o : orderOf y' = p) :
    ∃ a ∈ K₂, orderOf a = p ∧ y' * a = a * y' := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₂) p (s.dvd_card_K₂ hpn)
  set B := pCoreOf 2 K₂ with hB
  have hBK : B ≤ K₂ := pCoreOf_le 2 K₂
  have hX : IsPGroup p ↥(Subgroup.zpowers y') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hy'o, pow_one])
  have hBc : ¬ p ∣ Nat.card ↥B := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 K₂)
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hyN : Subgroup.zpowers y' ≤ Subgroup.normalizer (K₂ : Set G) :=
    (Subgroup.zpowers_le.mpr hy').trans s.Y_le_normalizer_K₂
  have hXB : Subgroup.zpowers y' ≤ Subgroup.normalizer (B : Set G) :=
    hyN.trans (normalizer_le_normalizer_pCoreOf 2 K₂)
  have ha : ∀ x ∈ Subgroup.zpowers y', (a₀ : G)⁻¹ * (x * a₀ * x⁻¹) ∈ B := by
    intro x hx
    have hxY : x ∈ Subgroup.zpowers y := (Subgroup.zpowers_le.mpr hy') hx
    have h1 := s.commutator_Y_mem a₀.2 hxY
    have h2 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K₂ (K₂.inv_mem a₀.2)) _).mp h1
    have e : (a₀ : G)⁻¹ * (x * a₀ * x⁻¹) =
        (a₀ : G)⁻¹ * (x * a₀ * x⁻¹ * (a₀ : G)⁻¹) * ((a₀ : G)⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  obtain ⟨b, hb, hfix⟩ := exists_mul_fixed_of_isPGroup hX hBc hXB ha
  set a₁ := (a₀ : G) * b with ha₁
  have ha₁K : a₁ ∈ K₂ := K₂.mul_mem a₀.2 (hBK hb)
  have hlev : s.levi ⟨a₁, ha₁K⟩ = s.levi a₀ := by
    have hb1 : s.levi ⟨b, hBK hb⟩ = 1 := by
      rw [← MonoidHom.mem_ker, s.ker_levi]
      exact (mem_pCoreOf_iff' _).mp hb
    have e : (⟨a₁, ha₁K⟩ : ↥K₂) = a₀ * ⟨b, hBK hb⟩ := rfl
    rw [e, map_mul, hb1, mul_one]
  have hpB : a₁ ^ p ∈ B := by
    have h1 : s.levi (⟨a₁, ha₁K⟩ ^ p) = 1 := by
      rw [map_pow, hlev, ← map_pow, ← ha₀, pow_orderOf_eq_one, map_one]
    rw [← MonoidHom.mem_ker, s.ker_levi] at h1
    have := (mem_pCoreOf_iff' _).mpr h1
    simpa using this
  obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 K₂) ⟨_, hpB⟩
  have he' : (a₁ ^ p) ^ 2 ^ e = 1 := congrArg Subtype.val he
  refine ⟨a₁ ^ 2 ^ e, K₂.pow_mem ha₁K _, ?_, ?_⟩
  · have hd : orderOf (a₁ ^ 2 ^ e) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, he'])
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exfalso
      have h1 : a₁ ^ 2 ^ e = 1 := orderOf_eq_one_iff.mp h
      have h2 : s.levi (⟨a₁, ha₁K⟩ ^ 2 ^ e) = 1 := by
        have : (⟨a₁, ha₁K⟩ : ↥K₂) ^ 2 ^ e = 1 := Subtype.ext (by simpa using h1)
        rw [this, map_one]
      rw [map_pow, hlev, ← map_pow] at h2
      have h3 : orderOf (s.levi a₀) ∣ 2 ^ e :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow]; exact h2)
      have h4 : orderOf (s.levi a₀) = p := by
        have hd' : orderOf (s.levi a₀) ∣ p := ha₀ ▸ orderOf_map_dvd _ _
        rcases (Nat.dvd_prime hp).mp hd' with h5 | h5
        · exfalso
          have h6 : s.levi a₀ = 1 := orderOf_eq_one_iff.mp h5
          rw [← MonoidHom.mem_ker, s.ker_levi] at h6
          obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K₂)) ⟨a₀, h6⟩
          have hk' : a₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
          have : p ∣ 2 ^ k := ha₀ ▸ orderOf_dvd_of_pow_eq_one hk'
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
        · exact h5
      rw [h4] at h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3))
    · exact h
  · have h1 := hfix y' (Subgroup.mem_zpowers y')
    have h2 : y' * a₁ ^ 2 ^ e * y'⁻¹ = a₁ ^ 2 ^ e := by
      rw [← conj_pow, ha₁, h1]
    calc y' * a₁ ^ 2 ^ e = y' * a₁ ^ 2 ^ e * y'⁻¹ * y' := by group
      _ = a₁ ^ 2 ^ e * y' := by rw [h2]

theorem exists_KZ (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    ∃ KZ ∈ cComp (Subgroup.centralizer (ZS : Set G)), K₂ ≤ KZ := by
  classical
  set H₀ := Subgroup.centralizer (ZS : Set G) with hH₀
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  set QZ := pCoreOf 2 GZ with hQZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  have hyp := s.sk.base.hyp
  have hH₀GZ : H₀ ≤ GZ := Subgroup.centralizer_le_normalizer _
  have hGZH₀ : GZ ≤ Subgroup.normalizer (H₀ : Set G) := fun g hg =>
    A4.mem_normalizer_centralizer hg
  have hH₀ : pCoreOf 2 H₀ ≠ ⊥ := fun h => s.ZS_ne_bot (le_bot_iff.mp (h ▸ s.ZS_le_pCoreOf_H₀))
  have hO₂ : pCoreOf 2 H₀ ≤ QZ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 H₀).trans hH₀GZ) (hGZH₀.trans (normalizer_le_normalizer_pCoreOf 2 H₀))
    (pCoreOf_isPGroup 2 H₀)
  have hK₂H₀ : K₂ ≤ H₀ := s.K₂_le_centralizer
  have hK₂GZ : K₂ ≤ GZ := hK₂H₀.trans hH₀GZ
  have hspan : cCompSpan H₀ = perfectCore H₀ :=
    lemma_1_2_1_one hyp.qtke hyp.simple hyp.nonabelian h39 hH₀
  have hK₂span : K₂ ≤ sSup (cComp H₀) := by
    have h1 := le_perfectCore_of_perfect hK₂H₀ s.K₂_perfect
    rw [← hspan] at h1
    exact h1
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥GZ) with hρ
  have hρ1 : ∀ x : ↥GZ, ρ x = 1 ↔ (x : G) ∈ QZ := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
  let img : Subgroup G → Subgroup (↥GZ ⧸ CFSG.pCore 2 ↥GZ) := fun X => (X.subgroupOf GZ).map ρ
  set 𝓛 := img '' cComp H₀ with h𝓛
  have hρmul : ∀ a b : ↥GZ, ρ a * ρ b = ρ b * ρ a ↔ (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ QZ := by
    intro a b
    have e : ((a * b * a⁻¹ * b⁻¹ : ↥GZ) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := by simp
    rw [← e, ← hρ1 (a * b * a⁻¹ * b⁻¹)]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc ρ a * ρ b = (ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹) * (ρ b * ρ a) := by group
        _ = ρ b * ρ a := by rw [h, one_mul]
  have hcomm : ∀ A ∈ 𝓛, ∀ B ∈ 𝓛, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨L₁, hL₁, rfl⟩ _ ⟨L₂, hL₂, rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    have hL : L₁ ≠ L₂ := fun h => hne (h ▸ rfl)
    have hc := (lemma_1_2_1_two hyp.qtke hyp.simple hyp.nonabelian h37 hH₀ hL₁ hL₂ hL)
    have h1 : (x : G) * z * (x : G)⁻¹ * (z : G)⁻¹ ∈ QZ := by
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
        (Subgroup.mem_subgroupOf.mp hz)
      rw [commutatorElement_def] at this
      exact hO₂ (hc.2 (hc.1 this))
    exact (hρmul x z).mpr h1
  have hSQ := SQTKHyp.of_sqtkGroup ↥GZ s.sqtkGroup_GZ
  have hO2 : ∀ A ∈ 𝓛, pCoreOf 2 A = ⊥ := by
    rintro _ ⟨L₁, hL₁, rfl⟩
    exact hSQ.pCoreOf_two_of_subnormal
      (subnormal_of_mem_cComp (modO2Image_mem_cComp (cComp_normalizer hL₁)))
  let ψ₀ : ↥K₂ →* ↥GZ ⧸ CFSG.pCore 2 ↥GZ := ρ.comp (Subgroup.inclusion hK₂GZ)
  have hrange : ψ₀.range = img K₂ := by
    show (ρ.comp (Subgroup.inclusion hK₂GZ)).range = (K₂.subgroupOf GZ).map ρ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let ψ : ↥K₂ →* ↥(img K₂) := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ₀.rangeRestrict
  have hψs : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ₀.rangeRestrict_surjective
  have hψ1 : ∀ k : ↥K₂, ψ k = 1 ↔ (k : G) ∈ QZ := by
    intro k
    show ψ k = 1 ↔ ((Subgroup.inclusion hK₂GZ k : ↥GZ) : G) ∈ QZ
    rw [← hρ1]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hψlevi : ψ.ker ≤ s.levi.ker := by
    rw [s.ker_levi]
    refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ψ) fun w => ?_
    have hw : ((w : ↥K₂) : G) ∈ QZ := (hψ1 w).mp w.2
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 GZ) ⟨_, hw⟩
    refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val he
    simpa using this
  let χ : ↥(img K₂) →* SL(2, F) := (MonoidHom.liftOfSurjective ψ hψs) ⟨s.levi, hψlevi⟩
  have hχψ : ∀ k, χ (ψ k) = s.levi k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hχs : Function.Surjective χ := fun z => by
    obtain ⟨k, hk⟩ := s.levi_surjective z
    exact ⟨ψ k, by rw [hχψ, hk]⟩
  have hχk : IsPGroup 2 χ.ker := by
    have hle : χ.ker ≤ s.levi.ker.map ψ := by
      intro z hz
      obtain ⟨k, rfl⟩ := hψs z
      refine Subgroup.mem_map_of_mem ψ ?_
      rw [MonoidHom.mem_ker, ← hχψ]
      exact hz
    have h2 : IsPGroup 2 s.levi.ker := by
      rw [s.ker_levi]
      exact CFSG.pCore_isPGroup
    exact (h2.map ψ).to_le hle
  have hKp : ⁅img K₂, img K₂⁆ = img K₂ := by
    have : Group.IsPerfect ↥K₂ := Subgroup.isPerfect_iff.mpr s.K₂_perfect
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective hψs)
  have hcardF : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, s.card_F]
  have h4F : 4 ≤ Nat.card F := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) s.two_le
  have hKL : img K₂ ≤ sSup 𝓛 := by
    have hle : sSup (cComp H₀) ≤ ((sSup 𝓛).comap ρ).map GZ.subtype := by
      refine sSup_le fun L₁ hL₁ x hx => ?_
      have hxGZ : x ∈ GZ := (le_of_mem_cComp hL₁).trans hH₀GZ hx
      refine ⟨⟨x, hxGZ⟩, ?_, rfl⟩
      exact (le_sSup (show img L₁ ∈ 𝓛 from ⟨L₁, hL₁, rfl⟩) : img L₁ ≤ sSup 𝓛)
        ⟨⟨x, hxGZ⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle (hK₂span (Subgroup.mem_subgroupOf.mp hx))
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨p, hp, hp2, hpn⟩ := s.exists_odd_prime_dvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y', hy', hy'o⟩ := s.exists_elt_Y hpn
  obtain ⟨a, haK₂, hao, hya⟩ := s.exists_elt_K₂ hp hp2 hpn hy' hy'o
  have hy'N : y' ∈ GZ := s.Y_le_normalizer_ZS hy'
  have hρord : ∀ x : ↥GZ, orderOf (x : G) = p → orderOf (ρ x) = p := by
    intro x hx
    have hx' : orderOf x = p := by rw [← Subgroup.orderOf_coe]; exact hx
    have hd : orderOf (ρ x) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, ← hx', pow_orderOf_eq_one, map_one])
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exfalso
      have h1 : (x : G) ∈ QZ := (hρ1 x).mp (orderOf_eq_one_iff.mp h)
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 GZ) ⟨x, h1⟩
      have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hdvd : p ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    · exact h
  have haKBar : ρ ⟨a, hK₂GZ haK₂⟩ ∈ img K₂ :=
    ⟨⟨a, hK₂GZ haK₂⟩, Subgroup.mem_subgroupOf.mpr haK₂, rfl⟩
  have hyaBar : ρ ⟨y', hy'N⟩ * ρ ⟨a, hK₂GZ haK₂⟩ = ρ ⟨a, hK₂GZ haK₂⟩ * ρ ⟨y', hy'N⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hya
  have hyKBar : ∀ k ∈ img K₂, ρ ⟨y', hy'N⟩ * k * (ρ ⟨y', hy'N⟩)⁻¹ ∈ img K₂ := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ K₂ := Subgroup.mem_subgroupOf.mp hk
    have hc : y' * k * y'⁻¹ ∈ K₂ :=
      (Subgroup.mem_normalizer_iff.mp (s.Y_le_normalizer_K₂ hy') k).mp hk'
    refine ⟨⟨y', hy'N⟩ * k * ⟨y', hy'N⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hc
    · rw [map_mul, map_mul, map_inv]
  have hyL : ∀ A ∈ 𝓛, A.map (MulAut.conj (ρ ⟨y', hy'N⟩)).toMonoidHom ∈ 𝓛 := by
    rintro _ ⟨L₁, hL₁, rfl⟩
    refine ⟨L₁.map (MulAut.conj y').toMonoidHom, ?_, ?_⟩
    · have h1 := cComp_map_mulEquiv (MulAut.conj y') hL₁
      have h2 : H₀.map (MulAut.conj y').toMonoidHom = H₀ :=
        A38.map_conj_eq_iff.mpr (hGZH₀ hy'N)
      rwa [h2] at h1
    · ext w
      constructor
      · intro hw
        obtain ⟨x, hx, hxw⟩ := hw
        obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        have hlGZ : l ∈ GZ := (le_of_mem_cComp hL₁).trans hH₀GZ hl
        refine Subgroup.mem_map.mpr
          ⟨ρ ⟨l, hlGZ⟩, ⟨⟨l, hlGZ⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, ?_⟩
        rw [← hxw]
        show ρ ⟨y', hy'N⟩ * ρ ⟨l, hlGZ⟩ * (ρ ⟨y', hy'N⟩)⁻¹ = ρ x
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hlx]
        rfl
      · intro hw
        obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
        obtain ⟨lG, hlG, rfl⟩ := hv
        refine Subgroup.mem_map.mpr ⟨⟨y', hy'N⟩ * lG * ⟨y', hy'N⟩⁻¹,
          Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · exact ⟨lG, Subgroup.mem_subgroupOf.mp hlG, by simp [MulAut.conj_apply]⟩
        · rw [← hvw]
          simp [map_mul, map_inv, MulAut.conj_apply]
  have hyS : ρ ⟨y', hy'N⟩ ∉ sSup 𝓛 := by
    intro h
    have hle : sSup 𝓛 ≤ img H₀ := sSup_le (by
      rintro _ ⟨L₁, hL₁, rfl⟩ _ ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ((le_of_mem_cComp hL₁)
        (Subgroup.mem_subgroupOf.mp hx)), rfl⟩)
    obtain ⟨x, hx, hxy⟩ := hle h
    have h1 : ρ (x⁻¹ * ⟨y', hy'N⟩) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := (hρ1 _).mp h1
    have hxH₀ : (x : G) ∈ H₀ := Subgroup.mem_subgroupOf.mp hx
    have hwQ : (x : G)⁻¹ * y' ∈ QZ := by simpa using h2
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 GZ) ⟨_, hwQ⟩
    have he' : ((x : G)⁻¹ * y') ^ 2 ^ e = 1 := congrArg Subtype.val he
    have hw1 : ∀ z ∈ ZS, ((x : G)⁻¹ * y') * z * ((x : G)⁻¹ * y')⁻¹ = y' * z * y'⁻¹ := by
      intro z hz
      have hyz : y' * z * y'⁻¹ ∈ ZS := (Subgroup.mem_normalizer_iff.mp hy'N z).mp hz
      have hxc := Subgroup.mem_centralizer_iff.mp hxH₀ _ hyz
      calc ((x : G)⁻¹ * y') * z * ((x : G)⁻¹ * y')⁻¹ =
            (x : G)⁻¹ * ((y' * z * y'⁻¹) * (x : G)) := by group
        _ = (x : G)⁻¹ * ((x : G) * (y' * z * y'⁻¹)) := by rw [hxc]
        _ = y' * z * y'⁻¹ := by group
    have hconj : ∀ j : ℕ, ∀ z ∈ ZS,
        ((x : G)⁻¹ * y') ^ j * z * (((x : G)⁻¹ * y') ^ j)⁻¹ = y' ^ j * z * (y' ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro z _; simp
      | succ j ih =>
        intro z hz
        have hz' : y' ^ j * z * (y' ^ j)⁻¹ ∈ ZS :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hy'N j) z).mp hz
        calc ((x : G)⁻¹ * y') ^ (j + 1) * z * (((x : G)⁻¹ * y') ^ (j + 1))⁻¹ =
              ((x : G)⁻¹ * y') * (((x : G)⁻¹ * y') ^ j * z * (((x : G)⁻¹ * y') ^ j)⁻¹) *
                ((x : G)⁻¹ * y')⁻¹ := by
              rw [pow_succ', mul_inv_rev]
              simp only [mul_assoc]
          _ = ((x : G)⁻¹ * y') * (y' ^ j * z * (y' ^ j)⁻¹) * ((x : G)⁻¹ * y')⁻¹ := by
              rw [ih z hz]
          _ = y' * (y' ^ j * z * (y' ^ j)⁻¹) * y'⁻¹ := hw1 _ hz'
          _ = y' ^ (j + 1) * z * (y' ^ (j + 1))⁻¹ := by group
    have hc : ∀ z ∈ ZS, y' ^ 2 ^ e * z * (y' ^ 2 ^ e)⁻¹ = z := by
      intro z hz
      rw [← hconj _ z hz, he', one_mul, inv_one, mul_one]
    have h3 : y' ^ 2 ^ e = 1 := s.Y_faithful (Subgroup.pow_mem _ hy' _) hc
    have h4 : p ∣ 2 ^ e := hy'o ▸ orderOf_dvd_of_pow_eq_one h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (↥GZ ⧸ CFSG.pCore 2 ↥GZ)) ≤ 2 := by
    rw [pRank_modO2_eq GZ hp hp2, ← pRank_top_subtype (p := p) GZ]
    exact s.sqtkGroup_GZ.1 p hp hp2
  obtain ⟨A, ⟨KZ, hKZ, rfl⟩, hle⟩ := L4312.exists_le_of_commuting' hcomm hO2
    (L4312.eq_or_isPGroup_of_sl2 hKp h4F χ hχs hχk) hKp s.two_le hcardF χ hχs hχk hKL hp2
    haKBar (hρord _ hao) (hρord _ hy'o) hyaBar hyKBar hyL hyS hrank
  refine ⟨KZ, hKZ, ?_⟩
  have hKZsup : K₂ ≤ KZ ⊔ QZ := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := hle ⟨⟨k, hK₂GZ hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h1 : ρ (x⁻¹ * ⟨k, hK₂GZ hk⟩) = 1 := by rw [map_mul, map_inv, hxk, inv_mul_cancel]
    have h2 := (hρ1 _).mp h1
    have e : k = (x : G) * ((x : G)⁻¹ * k) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_right (by simpa using h2))
  have hQZN : QZ ≤ Subgroup.normalizer (KZ : Set G) :=
    P134.pCoreOf_le_normalizer_of_mem_cComp (cComp_normalizer hKZ)
  exact L436.le_of_perfect_of_le_sup_of_isPGroup' (_root_.sup_le Subgroup.le_normalizer hQZN)
    (pCoreOf_isPGroup 2 GZ) s.K₂_perfect hKZsup

theorem dvd_card_modO2 {KZ : Subgroup G} (hK₂ : K₂ ≤ KZ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ m - 1) : p ∣ Nat.card (↥KZ ⧸ CFSG.pCore 2 ↥KZ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₂) p (s.dvd_card_K₂ hpn)
  set a' : ↥KZ := ⟨a, hK₂ a.2⟩ with ha'
  have ha'o : orderOf a' = p := by
    rw [← ha, ← Subgroup.orderOf_coe a', ← Subgroup.orderOf_coe a]
  set b : ↥KZ ⧸ CFSG.pCore 2 ↥KZ := QuotientGroup.mk a' with hb
  have hbp : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one (by
    rw [hb, ← QuotientGroup.mk_pow, ← ha'o, pow_orderOf_eq_one, QuotientGroup.mk_one])
  have hb1 : orderOf b ≠ 1 := by
    intro h1
    have hb1 : b = 1 := orderOf_eq_one_iff.mp h1
    have hmem : a' ∈ CFSG.pCore 2 ↥KZ := (QuotientGroup.eq_one_iff a').mp hb1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥KZ)) ⟨a', hmem⟩
    have hk' : a' ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : p ∣ 2 ^ k := ha'o ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hbo : orderOf b = p := ((Nat.dvd_prime hp).mp hbp).resolve_left hb1
  exact hbo ▸ orderOf_dvd_natCard b

theorem KZ_normal (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h122 : Lemma122A) {KZ : Subgroup G}
    (hKZ : KZ ∈ cComp (Subgroup.centralizer (ZS : Set G))) (hK₂ : K₂ ≤ KZ) :
    (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G))).Normal := by
  have hyp := s.sk.base.hyp
  have hH : pCoreOf 2 (Subgroup.normalizer (ZS : Set G)) ≠ ⊥ := s.inH_GZ.2
  have hKZ' := cComp_normalizer hKZ
  rcases lemma_1_2_1_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 hH hKZ' with h | ⟨h2, -⟩
  · exact h
  · exfalso
    obtain ⟨p, hp, hp2, hpn⟩ := s.exists_odd_prime_dvd
    obtain ⟨y', hy', hy'o⟩ := s.exists_elt_Y hpn
    have hyN : y' ∈ Subgroup.normalizer (ZS : Set G) := s.Y_le_normalizer_ZS hy'
    have hy1 : y' ≠ 1 := fun h => by
      rw [h, orderOf_one] at hy'o
      exact hp.one_lt.ne hy'o
    have hyC := s.not_mem_centralizer_ZS hy' hy1
    have hcl := h122 G hyp.simple hyp.qtke hyp.nonabelian _ KZ hH hKZ' p hp hp2 h2
      (s.dvd_card_modO2 hK₂ hp hp2 hpn)
    have hy : y' ∈ Subgroup.closure {x : G | x ∈ Subgroup.normalizer (ZS : Set G) ∧
        ∃ k : ℕ, orderOf x = p ^ k} := Subgroup.subset_closure ⟨hyN, 1, by rw [pow_one, hy'o]⟩
    rw [hcl] at hy
    have hle : conjClosure KZ (Subgroup.normalizer (ZS : Set G)) ≤
        Subgroup.centralizer (ZS : Set G) := conjClosure_le fun g hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer hg) k).mp
        (le_of_mem_cComp hKZ hk)
    exact hyC (hle hy)

theorem lemma_4_3_12_one (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h122 : Lemma122A) :
    ∃ KZ : Subgroup G, KZ ∈ cComp (Subgroup.normalizer (ZS : Set G)) ∧
      Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G) ∧ K₂ ≤ KZ ∧
      KZ ≤ Subgroup.centralizer (ZS : Set G) := by
  obtain ⟨KZ, hKZ, hK₂⟩ := s.exists_KZ h37 h39
  refine ⟨KZ, cComp_normalizer hKZ, ?_, hK₂, le_of_mem_cComp hKZ⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer ((le_of_mem_cComp hKZ).trans
    (Subgroup.centralizer_le_normalizer _))).mp (s.KZ_normal h37 h38 h122 hKZ hK₂)

end Setting4311

end CFSG.Quasithin.H13.Ch4
