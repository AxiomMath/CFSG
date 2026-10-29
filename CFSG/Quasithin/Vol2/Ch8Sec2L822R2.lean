module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Three
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Quasithin.Vol2.Ch8Sec2L822A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319
open scoped IsMulCommutative commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem res822_closure_conj {S : Set G} {m : G} (hS : ∀ x ∈ S, m * x * m⁻¹ ∈ S) (y : G)
    (hy : y ∈ Subgroup.closure S) : m * y * m⁻¹ ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure (hS x hx)
  exact hle hy

theorem res822_oTwoUpper_conj {P : Subgroup G} {m : G} (hm : ∀ x ∈ P, m * x * m⁻¹ ∈ P) (y : G)
    (hy : y ∈ oTwoUpper P) : m * y * m⁻¹ ∈ oTwoUpper P := by
  refine res822_closure_conj ?_ y hy
  rintro x ⟨hxP, hxo⟩
  refine ⟨hm x hxP, ?_⟩
  have key : orderOf (m * x * m⁻¹) = orderOf x :=
    orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective x
  rw [key]
  exact hxo

theorem res822_mem_pCoreOf_iff (L : Subgroup G) {z : G} (hz : z ∈ L) :
    (⟨z, hz⟩ : ↥L) ∈ CFSG.pCore 2 ↥L ↔ z ∈ pCoreOf 2 L := by
  unfold pCoreOf
  rw [Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    have : y = ⟨z, hz⟩ := Subtype.ext hyz
    rw [← this]
    exact hy

theorem res822_mk_mem_center_iff (L : Subgroup G) (x : ↥L) :
    (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ↔
      ∀ g : ↥L, x⁻¹ * g⁻¹ * x * g ∈ CFSG.pCore 2 ↥L := by
  constructor
  · intro h g
    have hc := Subgroup.mem_center_iff.mp h (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
    have := QuotientGroup.eq.mp hc
    have e : (g * x)⁻¹ * (x * g) = x⁻¹ * g⁻¹ * x * g := by group
    rw [e] at this
    exact this
  · intro h
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.mpr
    have := h g
    convert this using 1
    group

end Helpers

section Subgroups

variable {G : Type} [Group G]

@[expose] def res822P (L : Subgroup G) : Subgroup G :=
  ((Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype

@[expose] def res822Y (L : Subgroup G) : Subgroup G := oTwoUpper (res822P L)

@[expose] def res822J3 (H M : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ kerIn (H ⊓ M) H ∧ x ^ 3 = 1}

theorem res822_mem_P_iff (L : Subgroup G) (x : G) :
    x ∈ res822P L ↔ ∃ h : x ∈ L,
      (QuotientGroup.mk (⟨x, h⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  unfold res822P
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨x, h⟩, hc, rfl⟩

theorem res822_mk_mem_center_iff_G (L : Subgroup G) {x : G} (hxL : x ∈ L) :
    (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ↔
      ∀ g ∈ L, x⁻¹ * g⁻¹ * x * g ∈ pCoreOf 2 L := by
  rw [res822_mk_mem_center_iff L ⟨x, hxL⟩]
  constructor
  · intro h g hg
    exact (res822_mem_pCoreOf_iff L _).mp (h ⟨g, hg⟩)
  · intro h g
    exact (res822_mem_pCoreOf_iff L _).mpr (h g.1 g.2)

theorem res822_P_le (L : Subgroup G) : res822P L ≤ L := by
  intro x hx
  obtain ⟨h, -⟩ := (res822_mem_P_iff L x).mp hx
  exact h

theorem res822_P_normal (L : Subgroup G) {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) (x : G)
    (hx : x ∈ res822P L) : m * x * m⁻¹ ∈ res822P L := by
  obtain ⟨hxL, hc⟩ := (res822_mem_P_iff L x).mp hx
  have hc' := (res822_mk_mem_center_iff_G L hxL).mp hc
  have hmx : m * x * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hm x).mp hxL
  refine (res822_mem_P_iff L _).mpr ⟨hmx, (res822_mk_mem_center_iff_G L hmx).mpr ?_⟩
  intro g hg
  have hg' : m⁻¹ * g * m ∈ L := by
    apply (Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * g * m)).mpr
    have e : m * (m⁻¹ * g * m) * m⁻¹ = g := by group
    rw [e]
    exact hg
  have h1 := hc' _ hg'
  have h2 : m * (x⁻¹ * (m⁻¹ * g * m)⁻¹ * x * (m⁻¹ * g * m)) * m⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hm) _).mp h1
  have e : (m * x * m⁻¹)⁻¹ * g⁻¹ * (m * x * m⁻¹) * g =
      m * (x⁻¹ * (m⁻¹ * g * m)⁻¹ * x * (m⁻¹ * g * m)) * m⁻¹ := by group
  rw [e]
  exact h2

theorem res822_act_one {V L : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) (x : G) (hxL : x ∈ L)
    (hc : ∀ v ∈ V, x * v * x⁻¹ = v) : res822Act' hLV ⟨x, hxL⟩ = 1 := by
  have h : ∀ v : ↥V, ((res822Act' hLV ⟨x, hxL⟩ : ↥(autOn L V)) : MulAut ↥V) v = v := by
    intro v
    have hcoe : ((res822Act' hLV ⟨x, hxL⟩ : ↥(autOn L V)) : MulAut ↥V) = res822Act hLV ⟨x, hxL⟩ := rfl
    rw [hcoe]
    apply Subtype.ext
    rw [res822Act_apply]
    exact hc v v.2
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  rw [Subgroup.coe_one, MulAut.one_apply]
  exact h v

theorem res822_subgroupOf_normal {L Y : Subgroup G} (hYL : Y ≤ L) (hY : ∀ g ∈ L, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    (Y.subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact hY g g.2 n hn

theorem res822_Y_inter_pCore_eq_bot {L Y : Subgroup G} [Finite G] (hYL : Y ≤ L)
    (hYnorm : ∀ g ∈ L, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hO : pCoreOf 2 Y = ⊥) : Y ⊓ pCoreOf 2 L = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Y ⊓ pCoreOf 2 L ≤ pCoreOf 2 Y := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ ?_
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnY, hnO⟩ := hn
      refine ⟨Y.mul_mem (Y.mul_mem g.2 hnY) (Y.inv_mem g.2), ?_⟩
      have hgN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hYL g.2)
      have key := (Subgroup.mem_normalizer_iff.mp hgN (n : G)).mp hnO
      simpa using key
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem res822_card_Y_eq_three {L Y : Subgroup G} [Finite G] (hYL : Y ≤ L) (hYP : Y ≤ res822P L)
    (hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    (hYne : Y ≠ ⊥) (hYO : Y ⊓ pCoreOf 2 L = ⊥) : Nat.card ↥Y = 3 := by
  obtain ⟨g, hg⟩ : ∃ g : ↥(Y.subgroupOf L) →* (↥L ⧸ CFSG.pCore 2 ↥L),
      ∀ x : ↥(Y.subgroupOf L), g x = QuotientGroup.mk ((x : ↥L)) :=
    ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Y.subgroupOf L).subtype, fun x => rfl⟩
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hg] at hx
    have h1 : (x : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : ((x : ↥L) : G) ∈ pCoreOf 2 L := (res822_mem_pCoreOf_iff L _).mp h1
    have h3 : ((x : ↥L) : G) ∈ Y := x.2
    have h4 : ((x : ↥L) : G) ∈ Y ⊓ pCoreOf 2 L := ⟨h3, h2⟩
    rw [hYO, Subgroup.mem_bot] at h4
    apply Subtype.ext
    apply Subtype.ext
    exact h4
  have hgrange : g.range ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rintro _ ⟨x, rfl⟩
    rw [hg]
    have hxP : ((x : ↥L) : G) ∈ res822P L := hYP x.2
    obtain ⟨_, hc⟩ := (res822_mem_P_iff L _).mp hxP
    exact hc
  have hcardr : Nat.card g.range = Nat.card ↥(Y.subgroupOf L) :=
    (Nat.card_congr (Equiv.ofInjective g hginj)).symm
  have hdvd : Nat.card ↥(Y.subgroupOf L) ∣ 3 := by
    rw [← hcenter3, ← hcardr]
    exact Subgroup.card_dvd_of_le hgrange
  have hYL1 : 1 < Nat.card ↥(Y.subgroupOf L) := by
    have hex : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hYne (eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (hc y hy))
    obtain ⟨y, hyY, hy1⟩ := hex
    haveI hnt : Nontrivial ↥(Y.subgroupOf L) := by
      refine ⟨⟨(⟨⟨y, hYL hyY⟩, hyY⟩ : ↥(Y.subgroupOf L)), 1, ?_⟩⟩
      intro h
      apply hy1
      have := congrArg (fun z : ↥(Y.subgroupOf L) => ((z : ↥L) : G)) h
      simpa using this
    exact Finite.one_lt_card_iff_nontrivial.mpr hnt
  have hcard3 : Nat.card ↥(Y.subgroupOf L) = 3 := by
    have := (Nat.dvd_prime Nat.prime_three).mp hdvd
    omega
  have hYcard : Nat.card ↥Y = Nat.card ↥(Y.subgroupOf L) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv).symm
  exact hYcard.trans hcard3

theorem res822_pCoreOf_Y_ne_bot {L Y : Subgroup G} [Finite G] (hYL : Y ≤ L) (hYP : Y ≤ res822P L)
    (hYnorm : ∀ g ∈ L, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    (hYne : Y ≠ ⊥) (hF : CFSG.Open.quasithinGenFitting L = pCoreOf 2 L) : pCoreOf 2 Y ≠ ⊥ := by
  intro hO
  have hYO : Y ⊓ pCoreOf 2 L = ⊥ := res822_Y_inter_pCore_eq_bot hYL hYnorm hO
  have hcardY : Nat.card ↥Y = 3 := res822_card_Y_eq_three hYL hYP hcenter3 hYne hYO
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYp : IsPGroup 3 ↥Y := IsPGroup.of_card (n := 1) (by rw [hcardY]; norm_num)
  have hYnil : Group.IsNilpotent ↥Y := hYp.isNilpotent
  have hmemS : Y ∈ {N : Subgroup G | N ≤ L ∧ (N.subgroupOf L).Normal ∧ Group.IsNilpotent ↥N} :=
    ⟨hYL, res822_subgroupOf_normal hYL hYnorm, hYnil⟩
  have hYF : Y ≤ CFSG.Open.quasithinGenFitting L := by
    unfold CFSG.Open.quasithinGenFitting
    exact le_sup_of_le_left (le_sSup hmemS)
  rw [hF] at hYF
  have hY0 : Y ≤ Y ⊓ pCoreOf 2 L := le_inf le_rfl hYF
  rw [hYO] at hY0
  exact hYne (le_bot_iff.mp hY0)

theorem res822_decomp {L S : Subgroup G} [Finite G] (hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    {x0 : G} (hx0L : x0 ∈ L) (hx0S : x0 ∈ S) (hx0P : x0 ∈ res822P L) (hx03 : orderOf x0 = 3) :
    ∀ p ∈ res822P L, ∃ j ∈ S, ∃ o ∈ pCoreOf 2 L, p = j * o := by
  intro p hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz0c : (QuotientGroup.mk (⟨x0, hx0L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := ((res822_mem_P_iff L x0).mp hx0P).2
  have hx3 : x0 ^ 3 = 1 := by
    rw [← hx03]
    exact pow_orderOf_eq_one x0
  have hz3 : (QuotientGroup.mk (⟨x0, hx0L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x0, hx0L⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, QuotientGroup.mk_one]
  have hz0ne : (QuotientGroup.mk (⟨x0, hx0L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1 := by
    intro h1
    have h2 : (⟨x0, hx0L⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : x0 ∈ pCoreOf 2 L := (res822_mem_pCoreOf_iff L hx0L).mp h2
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨x0, h3⟩
    have hx0k : x0 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd := orderOf_dvd_of_pow_eq_one hx0k
    rw [hx03] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at this
  have hz03 : orderOf (QuotientGroup.mk (⟨x0, hx0L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 3 :=
    orderOf_eq_prime hz3 hz0ne
  have hzp : Subgroup.zpowers (QuotientGroup.mk (⟨x0, hx0L⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hz0c
    · rw [Nat.card_zpowers, hz03, hcenter3]
  obtain ⟨hpL, hpc⟩ := (res822_mem_P_iff L p).mp hp
  rw [← hzp] at hpc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpc
  have hk' : (QuotientGroup.mk ((⟨x0, hx0L⟩ : ↥L) ^ k) : ↥L ⧸ CFSG.pCore 2 ↥L) =
      QuotientGroup.mk (⟨p, hpL⟩ : ↥L) := by
    rw [QuotientGroup.mk_zpow]
    exact hk
  have hmem := (QuotientGroup.eq.mp hk')
  have ho : (((⟨x0, hx0L⟩ : ↥L) ^ k)⁻¹ * (⟨p, hpL⟩ : ↥L) : ↥L) ∈ CFSG.pCore 2 ↥L := hmem
  have hoG : ((((⟨x0, hx0L⟩ : ↥L) ^ k)⁻¹ * (⟨p, hpL⟩ : ↥L) : ↥L) : G) ∈ pCoreOf 2 L :=
    (res822_mem_pCoreOf_iff L _).mp ho
  refine ⟨x0 ^ k, zpow_mem hx0S k, _, hoG, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, Subgroup.coe_mk]
  group

theorem res822_o_mem {H S : Subgroup G} (hSH : S ≤ H) (hSn : ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S)
    {p j o : G} (hpH : p ∈ H) (hjS : j ∈ S) (hoH : o ∈ H) (hp : p = j * o) {n k : ℕ}
    (hn : Odd n) (hpn : p ^ n = 1) (hok : o ^ 2 ^ k = 1) : o ∈ S := by
  haveI hnorm : (S.subgroupOf H).Normal := ⟨fun s hs h => by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hSn h h.2 s hs⟩
  have hP' : (⟨p, hpH⟩ : ↥H) = (⟨j, hSH hjS⟩ : ↥H) * ⟨o, hoH⟩ := Subtype.ext (by simp [hp])
  have hJ1 : QuotientGroup.mk' (S.subgroupOf H) (⟨j, hSH hjS⟩ : ↥H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hjS)
  have hπ : QuotientGroup.mk' (S.subgroupOf H) (⟨p, hpH⟩ : ↥H) =
      QuotientGroup.mk' (S.subgroupOf H) (⟨o, hoH⟩ : ↥H) := by
    rw [hP', map_mul, hJ1, one_mul]
  have hn1 : (QuotientGroup.mk' (S.subgroupOf H) (⟨o, hoH⟩ : ↥H)) ^ n = 1 := by
    rw [← hπ, ← map_pow]
    have : (⟨p, hpH⟩ : ↥H) ^ n = 1 := Subtype.ext (by simpa using hpn)
    rw [this, map_one]
  have hn2 : (QuotientGroup.mk' (S.subgroupOf H) (⟨o, hoH⟩ : ↥H)) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨o, hoH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hok)
    rw [this, map_one]
  have hcop : Nat.Coprime n (2 ^ k) := by
    have h2n : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn.not_two_dvd_nat
    exact (Nat.Coprime.pow_left k h2n).symm
  have hg := pow_gcd_eq_one.mpr ⟨hn1, hn2⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
  have hmem := (QuotientGroup.eq_one_iff (⟨o, hoH⟩ : ↥H)).mp hg
  exact Subgroup.mem_subgroupOf.mp hmem

end Subgroups

section Residual

theorem res822CoverJ3_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK) (hB69 : B69Struct)
    (hM22 : M22Facts822) (hthree : Input822ThreeInL) : Res822CoverJ3 := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot hcov H hH hVH
  unfold KerNoThree
  intro h3
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hMeq : fsuM T L = Subgroup.normalizer (L : Set G) := by
    show Subgroup.normalizer (fsuL0 T L : Set G) = _
    rw [hL0]
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    obtain ⟨-, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
    rw [hL0] at hN
    exact le_sup_left.trans hN
  have hM : MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ := by
    have h := hrowM
    unfold Row711M22Code at h
    rw [hL0] at h
    exact h
  have hA := res822_autOn_iso hM
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hyp.fsu.quasisimple
  obtain ⟨ψ, hψs, hkerψ, hψl⟩ := res822_psi_of hLV hA hQ
  have hcov' : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
    unfold CoverM22 at hcov
    rw [hL0] at hcov
    have hS : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
      unfold pCoreOf
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    obtain ⟨_hnorm, hI⟩ := hcov
    exact IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hS) hI
  have hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := hcov'.2.1
  have hMmax : IsMaxTwoLocalSubgroup (fsuM T L) :=
    ((h331 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow).2 L hyp.fsu.maximal
      hyp.fsu.quasisimple).1.1
  have hF : CFSG.Open.quasithinGenFitting L = pCoreOf 2 L := hyp.fsu.faithful.2.2.1
  obtain ⟨hmin, hsq, hchar, hHMN⟩ := setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  have h318 := hyp318_of_normal h37 h38 h39 h3228 hyp hTL hH
  have h315 := h318.hyp315 hyp.fsu.sylow hH
  have hbase : Hyp315Base T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) := h315.toHyp315Base
  obtain ⟨hq, hdual, h6i, h6ii, h6iii⟩ :=
    hM22 G T L I hyp h731 h821 hc hrow hrowM hnot hbase.reduced.2.2.1
  have hII : Hyp315.CaseII (fsuM T L) H (fsuV T I) := hHMN
  have h319 : Hyp319 T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) :=
    ⟨hbase, hII, hq, h318.unique, hVH, hdual⟩
  have hconcl := Hyp319.concl_core hC58 hD15 hS316 hD125 hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow h318.inM h319
  obtain ⟨hmp, -, -, -, -, hstep2⟩ := lemma319Common_of_inputs hB69 G T hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) h318.inM hbase hII hq
    h318.unique hVH (fun ⟨_, hd⟩ => hdual hd) hconcl
  have hcent3 : ∀ x : G, x ∈ kerIn (H ⊓ fsuM T L) H → x ^ 3 = 1 → ∀ v ∈ fsuV T I, x * v * x⁻¹ = v := by
    intro x hxJ hx3 v hv
    have hxH : x ∈ H := hmp.kerIn_le_H hxJ
    have hcent : ∀ w ∈ conjClosure (fsuV T I) H, x * w * x⁻¹ = w := by
      refine centralizes_of_odd_series (n := 3) (by decide) hx3 hconcl.elemAbelian ?_ hconcl.chief
      intro L' N hst w hw
      by_cases hnc : IsCentralStep H L' N
      · exact hnc x hxH w hw
      · have hyC : x ∈ centralizerMod L' H N := by
          rw [hstep2 L' N hst hnc]
          exact hxJ
        exact hyC.2.2 w hw
    exact hcent v (le_conjClosure (fsuV T I) H hv)
  have hJconj : ∀ h ∈ H, ∀ x ∈ kerIn (H ⊓ fsuM T L) H, h * x * h⁻¹ ∈ kerIn (H ⊓ fsuM T L) H := by
    intro h hh x hx
    rw [mem_kerIn] at hx ⊢
    intro b hb
    have e : b * (h * x * h⁻¹) * b⁻¹ = (b * h) * x * (b * h)⁻¹ := by group
    rw [e]
    exact hx (b * h) (H.mul_mem hb hh)
  have hJ3conj : ∀ h ∈ H, ∀ y ∈ res822J3 H (fsuM T L), h * y * h⁻¹ ∈ res822J3 H (fsuM T L) := by
    intro h hh y hy
    unfold res822J3 at hy ⊢
    refine res822_closure_conj ?_ y hy
    rintro x ⟨hxJ, hx3⟩
    refine ⟨hJconj h hh x hxJ, ?_⟩
    rw [conj_pow, hx3]
    simp
  have hJ3H : res822J3 H (fsuM T L) ≤ H := by
    unfold res822J3
    rw [Subgroup.closure_le]
    rintro x ⟨hxJ, -⟩
    exact (kerIn_le hxJ).1
  have hodd3 : ∀ x : G, x ^ 3 = 1 → Odd (orderOf x) := fun x hx3 =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)
  have hJ3P : ∀ x ∈ kerIn (H ⊓ fsuM T L) H, x ^ 3 = 1 → x ∈ res822P L := by
    intro x hxJ hx3
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hxM : x ∈ fsuM T L := (inf_le_right : H ⊓ fsuM T L ≤ fsuM T L) (kerIn_le hxJ)
    have hxL : x ∈ L := by
      have h := hthree G T L I hyp h731 h821 hc hrow hrowM hnot x hxM hord
      rw [hL0] at h
      exact h
    refine (res822_mem_P_iff L x).mpr ⟨hxL, ?_⟩
    rw [← hkerψ, MonoidHom.mem_ker, hψl]
    exact res822_act_one hLV x hxL (hcent3 x hxJ hx3)
  have hJ3_le_Y : res822J3 H (fsuM T L) ≤ res822Y L := by
    unfold res822J3 res822Y oTwoUpper
    rw [Subgroup.closure_le]
    rintro x ⟨hxJ, hx3⟩
    exact Subgroup.subset_closure ⟨hJ3P x hxJ hx3, hodd3 x hx3⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x0, hx0J, hord0⟩ : ∃ x0 : G, x0 ∈ kerIn (H ⊓ fsuM T L) H ∧ orderOf x0 = 3 := by
    obtain ⟨x0', hx0'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(kerIn (H ⊓ fsuM T L) H)) 3 h3
    exact ⟨x0', x0'.2, by rw [Subgroup.orderOf_coe]; exact hx0'⟩
  have hx0M : x0 ∈ fsuM T L := (inf_le_right : H ⊓ fsuM T L ≤ fsuM T L) (kerIn_le hx0J)
  have hx0L : x0 ∈ L := by
    have h := hthree G T L I hyp h731 h821 hc hrow hrowM hnot x0 hx0M hord0
    rw [hL0] at h
    exact h
  have hx03 : x0 ^ 3 = 1 := by
    rw [← hord0]
    exact pow_orderOf_eq_one x0
  have hx0J3 : x0 ∈ res822J3 H (fsuM T L) := Subgroup.subset_closure ⟨hx0J, hx03⟩
  have hx0P : x0 ∈ res822P L := hJ3P x0 hx0J hx03
  have hx0ne : x0 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord0
    norm_num at hord0
  have hdec := res822_decomp hcenter3 hx0L hx0J3 hx0P hord0
  have hO2H : pCoreOf 2 L ≤ H := by
    have hidx : ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index := by
      have h1 : (T.subgroupOf (L ⊔ T)).index ∣ T.index :=
        ⟨(L ⊔ T).index, (Subgroup.relIndex_mul_index le_sup_right).symm⟩
      exact fun h => hyp.fsu.sylow.2 (h.trans h1)
    have hO2LT : pCoreOf 2 (L ⊔ T) ≤ T :=
      CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right hyp.fsu.sylow.1 hidx
    have hnorm : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    have hO2LT' : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hnorm
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact hO2LT'.trans (hO2LT.trans hH.1.1)
  have hY_le_J3 : res822Y L ≤ res822J3 H (fsuM T L) := by
    unfold res822Y oTwoUpper
    rw [Subgroup.closure_le]
    rintro p ⟨hpP, hpodd⟩
    obtain ⟨j, hjS, o, hoO, rfl⟩ := res822_decomp hcenter3 hx0L hx0J3 hx0P hord0 _ hpP
    have hjH : j ∈ H := hJ3H hjS
    have hoH : o ∈ H := hO2H hoO
    have hpH : j * o ∈ H := H.mul_mem hjH hoH
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨o, hoO⟩
    have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hoS : o ∈ res822J3 H (fsuM T L) :=
      res822_o_mem hJ3H (fun h hh s hs => hJ3conj h hh s hs) hpH hjS hoH rfl hpodd
        (pow_orderOf_eq_one _) hok
    exact (res822J3 H (fsuM T L)).mul_mem hjS hoS
  have hYeq : res822Y L = res822J3 H (fsuM T L) := le_antisymm hY_le_J3 hJ3_le_Y
  have hYL : res822Y L ≤ L := (oTwoUpper_le _).trans (res822_P_le L)
  have hYP : res822Y L ≤ res822P L := oTwoUpper_le _
  have hYconj : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ y ∈ res822Y L, g * y * g⁻¹ ∈ res822Y L :=
    fun g hg y hy => res822_oTwoUpper_conj (res822_P_normal L hg) y hy
  have hYnorm : ∀ g ∈ L, ∀ y ∈ res822Y L, g * y * g⁻¹ ∈ res822Y L :=
    fun g hg y hy => hYconj g (Subgroup.le_normalizer hg) y hy
  have hYne : res822Y L ≠ ⊥ := by
    intro hb
    have hx0Y : x0 ∈ res822Y L := hJ3_le_Y hx0J3
    rw [hb, Subgroup.mem_bot] at hx0Y
    exact hx0ne hx0Y
  have hOY : pCoreOf 2 (res822Y L) ≠ ⊥ :=
    res822_pCoreOf_Y_ne_bot hYL hYP hYnorm hcenter3 hYne hF
  have hMleY : fsuM T L ≤ Subgroup.normalizer (res822Y L : Set G) := by
    intro m hm
    rw [hMeq] at hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hYconj m hm y hy
    · intro hy
      have h1 := hYconj m⁻¹ (inv_mem hm) _ hy
      have e : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y := by group
      rw [e] at h1
      exact h1
  have hNY : Subgroup.normalizer (res822Y L : Set G) ≤ fsuM T L := by
    have hMle : fsuM T L ≤ Subgroup.normalizer (pCoreOf 2 (res822Y L) : Set G) :=
      hMleY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (res822Y L))
    have hTwo : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (res822Y L) : Set G)) :=
      ⟨pCoreOf 2 (res822Y L), hOY, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    have heq : Subgroup.normalizer (pCoreOf 2 (res822Y L) : Set G) = fsuM T L := hMmax.2 _ hTwo hMle
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (res822Y L)).trans heq.le
  have hHnorm : H ≤ Subgroup.normalizer (res822Y L : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff, hYeq]
    intro y
    constructor
    · intro hy
      exact hJ3conj h hh y hy
    · intro hy
      have h1 := hJ3conj h⁻¹ (inv_mem hh) _ hy
      have e : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
      rw [e] at h1
      exact h1
  exact hH.2.1 (hHnorm.trans hNY)

end Residual

end CFSG.Quasithin.H13
