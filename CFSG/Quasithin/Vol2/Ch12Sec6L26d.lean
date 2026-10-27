module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26b
public import CFSG.Quasithin.Vol2.Ch12Sec6L26c
public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.Quasithin.Vol2.Ch12Sec6Amalgam
public import CFSG.Quasithin.Vol2.Ch12Sec6L24b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open CFSG.Blueprint CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F Equiv
open scoped IsMulCommutative

namespace S126L26

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_two_three' {x : G} {n : ℕ} (h2 : x ^ 2 ^ n = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hc : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
  have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h1'
  exact orderOf_eq_one_iff.mp this

theorem false_of_e27 {H P : Subgroup G} (hSQ : SQTKGroup ↥H) (hPH : P ≤ H) (hP : IsElemAbelian 3 P)
    (hcP : Nat.card P = 9) {x v : G} (hxH : x ∈ H) (hvH : v ∈ H) (hx3 : x ^ 3 ∈ pCoreOf 2 H)
    (hxQ : x ∉ pCoreOf 2 H) (hxP : ∀ a ∈ P, x * a * x⁻¹ * a⁻¹ ∈ pCoreOf 2 H)
    (hvP : ∀ a ∈ P, v * a * v⁻¹ * a⁻¹ ∈ pCoreOf 2 H) (hvx : v * x * v⁻¹ * x ∈ pCoreOf 2 H) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥H with hOdef
  have hO2 : IsPGroup 2 ↥O := CFSG.pCore_isPGroup
  have hP' : O.map H.subtype = pCoreOf 2 H := by
    rw [hOdef]; rfl
  have hmemO : ∀ z : ↥H, z ∈ O ↔ (z : G) ∈ pCoreOf 2 H := by
    intro z
    rw [← hP']
    constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      rwa [show w = z from Subtype.ext hwz] at hw
  have hO3 : ¬ 3 ∣ Nat.card ↥O := by
    obtain ⟨e, he⟩ := hO2.exists_card_eq
    rw [he]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  set q := QuotientGroup.mk' O with hq
  have hq1 : ∀ z : ↥H, q z = 1 ↔ (z : G) ∈ pCoreOf 2 H := by
    intro z
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemO]
  have hcomm_q : ∀ a b : ↥H, ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H) →
      q a * q b = q b * q a := by
    intro a b hab
    have h1 : q (a * b * a⁻¹ * b⁻¹) = 1 := (hq1 _).2 hab
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc q a * q b = q a * q b * (q a)⁻¹ * (q b)⁻¹ * (q b * q a) := by group
      _ = q b * q a := by rw [h1, one_mul]
  set xb : ↥H ⧸ O := q ⟨x, hxH⟩ with hxb
  set vb : ↥H ⧸ O := q ⟨v, hvH⟩ with hvb
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    exact (hq1 _).2 hx3
  have hxb1 : xb ≠ 1 := fun h1 => hxQ ((hq1 _).1 h1)
  have hord : orderOf xb = 3 := orderOf_eq_prime hxb3 hxb1
  have hvxb : vb * xb * vb⁻¹ = xb⁻¹ := by
    have h1 : q (⟨v, hvH⟩ * ⟨x, hxH⟩ * ⟨v, hvH⟩⁻¹ * ⟨x, hxH⟩) = 1 := (hq1 _).2 hvx
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hvz : ∀ z ∈ Subgroup.zpowers xb, vb * z * vb⁻¹ = z⁻¹ := by
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hvxb, inv_zpow]
  let α : ↥P →* ↥H ⧸ O := q.comp (Subgroup.inclusion hPH)
  have hα : ∀ a : ↥P, α a = q ⟨a, hPH a.2⟩ := fun a => rfl
  have hαx : ∀ a : ↥P, α a * xb = xb * α a := fun a => by
    rw [hα, hxb]
    refine (hcomm_q _ _ ?_)
    have h := (pCoreOf 2 H).inv_mem (hxP a a.2)
    convert h using 1
    group
  have hαv : ∀ a : ↥P, α a * vb = vb * α a := fun a => by
    rw [hα, hvb]
    refine (hcomm_q _ _ ?_)
    have h := (pCoreOf 2 H).inv_mem (hvP a a.2)
    convert h using 1
    group
  have hαβ : ∀ (a : ↥P) (z : ↥(Subgroup.zpowers xb)),
      Commute (α a) ((Subgroup.zpowers xb).subtype z) := by
    intro a z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.2
    show α a * (z : ↥H ⧸ O) = (z : ↥H ⧸ O) * α a
    rw [← hn]
    exact (Commute.zpow_right (hαx a) n).eq
  let Φ := α.noncommCoprod (Subgroup.zpowers xb).subtype hαβ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h1
    simp only [Φ, MonoidHom.noncommCoprod_apply] at h1
    have hαz : α a = ((z : ↥H ⧸ O))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hzinv : ((z : ↥H ⧸ O))⁻¹ ∈ Subgroup.zpowers xb := (Subgroup.zpowers xb).inv_mem z.2
    have h2 : α a = (α a)⁻¹ := by
      have e1 := hvz _ hzinv
      rw [← hαz] at e1
      calc α a = vb * α a * vb⁻¹ := by rw [← hαv a]; group
        _ = (α a)⁻¹ := e1
    have h3 : (α a) ^ 3 = 1 := by
      rw [hαz, inv_pow]
      have hc3 : Nat.card ↥(Subgroup.zpowers xb) = 3 := by rw [Nat.card_zpowers, hord]
      have : (z : ↥H ⧸ O) ^ 3 = 1 := by
        have hz3 : z ^ 3 = 1 := by rw [← hc3]; exact pow_card_eq_one'
        exact congrArg Subtype.val hz3
      rw [this, inv_one]
    have h4 : α a = 1 := by
      have h2' : α a * α a = 1 := by
        calc α a * α a = α a * (α a)⁻¹ := by rw [← h2]
          _ = 1 := mul_inv_cancel _
      calc α a = (α a) ^ 3 * (α a * α a)⁻¹ := by group
        _ = 1 := by rw [h3, h2', inv_one, one_mul]
    have ha1 : (a : G) = 1 := by
      have h5 : (a : G) ∈ pCoreOf 2 H := (hq1 ⟨a, hPH a.2⟩).1 h4
      obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 H) ⟨_, h5⟩
      have he' : (a : G) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
      exact eq_one_of_two_three' he' (hP.2 _ a.2)
    have ha1' : a = 1 := Subtype.ext ha1
    subst ha1'
    have hz1 : (z : ↥H ⧸ O) = 1 := by
      rw [map_one, one_mul] at h1
      exact h1
    exact Prod.ext rfl (Subtype.ext hz1)
  have hcomm3 : ∀ x y : ↥P × ↥(Subgroup.zpowers xb), x * y = y * x := by
    rintro ⟨a, z⟩ ⟨a', z'⟩
    refine Prod.ext (hP.1.is_comm.comm a a') ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp z.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z'.2
    apply Subtype.ext
    show (z : ↥H ⧸ O) * z' = z' * z
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self xb m n).eq
  have hpow3 : ∀ x : ↥P × ↥(Subgroup.zpowers xb), x ^ 3 = 1 := by
    rintro ⟨a, z⟩
    refine Prod.ext (Subtype.ext (by simpa using hP.2 _ a.2)) ?_
    have hc3 : Nat.card ↥(Subgroup.zpowers xb) = 3 := by rw [Nat.card_zpowers, hord]
    show z ^ 3 = 1
    rw [← hc3]
    exact pow_card_eq_one'
  have h27 : Nat.card (↥P × ↥(Subgroup.zpowers xb)) = 3 ^ 3 := by
    rw [Nat.card_prod, hcP, Nat.card_zpowers, hord]
    norm_num
  have hrk := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm3 hpow3 h27 Φ
    hinj (H := ⊤) le_top
  rw [CFSG.SectionRank.pRank_quotient_eq O hO3] at hrk
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 := hSQ.1 3 Nat.prime_three (by norm_num)
  omega

omit [Finite G] in
theorem conjSubgroup_eq (V : Subgroup G) (g : G) : conjSubgroup V g = conjSub g⁻¹ V := by
  ext x
  rw [mem_conjSubgroup_iff, mem_conjSub, inv_inv]

theorem isPGroup_of_forall {H I : Subgroup G} (hall : ∀ x ∈ I, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) :
    IsPGroup 2 ↥I := by
  intro x
  obtain ⟨n, hn⟩ := hall x x.2
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hn⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

omit [Finite G] in
theorem comm_mem_Vp {V Vp : Subgroup G} (hidx : Vp.relIndex V = 2) {v l : G} (hv : v ∈ V)
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) (hlVp : l ∈ Subgroup.normalizer (Vp : Set G)) :
    v * l * v⁻¹ * l⁻¹ ∈ Vp := by
  have hw : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlV _).mp (V.inv_mem hv)
  have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
  rw [e]
  have key := Subgroup.mul_mem_iff_of_index_two (H := Vp.subgroupOf V) hidx
    (a := (⟨v, hv⟩ : ↥V)) (b := ⟨l * v⁻¹ * l⁻¹, hw⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  refine key.2 ⟨fun hvp => ?_, fun hwp => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hlVp _).mp (Vp.inv_mem hvp)
  · have h1 : l⁻¹ * (l * v⁻¹ * l⁻¹) * l⁻¹⁻¹ ∈ Vp :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlVp) _).mp hwp
    have h2 : l⁻¹ * (l * v⁻¹ * l⁻¹) * l⁻¹⁻¹ = v⁻¹ := by group
    rw [h2] at h1
    simpa using Vp.inv_mem h1

section Hyp

variable {T V L V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H)
include h

theorem Q_comm {q a : G} (hq : q ∈ pCoreOf 2 H) (ha : a ∈ conjClosure Vp H) :
    q * a * q⁻¹ * a⁻¹ ∈ V₁ := by
  have := V₁.inv_mem (h.commutator_conjClosure_le a ha q hq)
  convert this using 1
  group

theorem fix_comm {p y a : G} (hy : y ∈ H) (hpy : p * y * p⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (ha : a ∈ conjClosure Vp H) (hpa : p * a * p⁻¹ * a⁻¹ ∈ V₁)
    (hya : y * a * y⁻¹ * a⁻¹ ∈ conjClosure Vp H) :
    p * (y * a * y⁻¹ * a⁻¹) * p⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ ∈ V₁ := by
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hcen : ∀ z ∈ V₁, ∀ x ∈ H, x * z = z * x := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer hx) z hz).symm
  generalize hqdef : p * y * p⁻¹ * y⁻¹ = q at hpy
  generalize hzdef : p * a * p⁻¹ * a⁻¹ = z at hpa
  have hpy' : p * y * p⁻¹ = q * y := by rw [← hqdef]; group
  have hpa' : p * a * p⁻¹ = z * a := by rw [← hzdef]; group
  have hqH : q ∈ H := pCoreOf_le 2 H hpy
  have haH : a ∈ H := hUH ha
  have e : p * (y * a * y⁻¹ * a⁻¹) * p⁻¹ = (q * y) * (z * a) * (q * y)⁻¹ * (z * a)⁻¹ := by
    rw [← hpy', ← hpa']
    group
  have hzy : y * z = z * y := hcen z hpa y hy
  have hzq : q * z = z * q := hcen z hpa q hqH
  have e2 : (q * y) * (z * a) * (q * y)⁻¹ * (z * a)⁻¹ =
      q * (y * a * y⁻¹ * a⁻¹) * q⁻¹ * (q * a * q⁻¹ * a⁻¹) := by
    calc (q * y) * (z * a) * (q * y)⁻¹ * (z * a)⁻¹ =
        q * (y * z) * a * y⁻¹ * q⁻¹ * a⁻¹ * z⁻¹ := by group
      _ = z * (q * y * a * y⁻¹ * q⁻¹ * a⁻¹) * z⁻¹ := by
          rw [hzy, show q * (z * y) = (q * z) * y by group, hzq]; group
      _ = q * y * a * y⁻¹ * q⁻¹ * a⁻¹ := by
          have hc : (q * y * a * y⁻¹ * q⁻¹ * a⁻¹) * z = z * (q * y * a * y⁻¹ * q⁻¹ * a⁻¹) :=
            hcen z hpa _ (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hqH hy) haH)
              (H.inv_mem hy)) (H.inv_mem hqH)) (H.inv_mem haH))
          rw [← hc]
          group
      _ = _ := by group
  rw [e, e2]
  have h1 := Q_comm h hpy hya
  have h2 := Q_comm h hpy ha
  generalize hcdef : y * a * y⁻¹ * a⁻¹ = c at h1 hya ⊢
  have hcH : c ∈ H := hUH hya
  have e3 : q * c * q⁻¹ * (q * a * q⁻¹ * a⁻¹) * c⁻¹ =
      (q * c * q⁻¹ * c⁻¹) * (c * (q * a * q⁻¹ * a⁻¹) * c⁻¹) := by group
  rw [e3, hcen _ h2 c hcH, mul_inv_cancel_right]
  exact V₁.mul_mem h1 h2

theorem le_or_exists_of_le {K : Subgroup G} (hVK : V ≤ K) :
    V ≤ pCoreOf 2 K ∨ ∃ g ∈ K, ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : IsPGroup 2 ↥(V.subgroupOf K) :=
    h.isPGroup_V.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  rcases baer_suzuki_subgroup (G := ↥K) (p := 2) (X := V.subgroupOf K) hX2 with hle | ⟨g', hg'⟩
  · left
    exact fun v hv => ⟨⟨v, hVK hv⟩, hle (show (⟨v, hVK hv⟩ : ↥K) ∈ V.subgroupOf K from hv), rfl⟩
  · right
    refine ⟨g', g'.2, fun hall => hg' ?_⟩
    set Y : Subgroup ↥K := V.subgroupOf K ⊔ conjSubgroup (V.subgroupOf K) g' with hY
    have hmap : Y.map K.subtype = V ⊔ conjSub (g' : G)⁻¹ V := by
      rw [hY, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hVK]
      congr 1
      ext y
      rw [mem_conjSub, inv_inv]
      constructor
      · rintro ⟨y', hy', rfl⟩
        have h1 := Subgroup.mem_subgroupOf.mp (mem_conjSubgroup_iff.mp hy')
        simpa using h1
      · intro hy
        have hyK : y ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem g'.2) (hVK hy)) g'.2
          simpa [mul_assoc] using this
        refine ⟨⟨y, hyK⟩, mem_conjSubgroup_iff.mpr (Subgroup.mem_subgroupOf.mpr ?_), rfl⟩
        simpa using hy
    have h2 : IsPGroup 2 ↥(Y.map K.subtype) := by
      rw [hmap]
      exact isPGroup_of_forall hall
    exact h2.of_equiv (Y.equivMapOfInjective K.subtype K.subtype_injective).symm

end Hyp

section Frame

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] def QFix (z : Fin 6 → ZMod 2) : Prop :=
  S126L24.Ev (emb z) ∧ S126L24.BC (fun j => emb z (c1⁻¹ j) + -emb z j)

instance : DecidablePred QFix := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem card_QFix : Fintype.card {z // QFix z} = 8 := by decide

omit [Finite G] in
theorem qfix_of_mem (F : Frame126 T L V) {p : G} (hpV : p ∈ Subgroup.normalizer (V : Set G))
    (hpσ : ActsAs F p c1) {a : G} (ha5 : a ∈ F.V5) (ha1 : p * a * p⁻¹ * a⁻¹ ∈ F.V1) :
    QFix (cmp (Multiplicative.toAdd (iota (F.β ⟨a, S126L24.preV_le F W5 ha5⟩)))) := by
  have haV : a ∈ V := S126L24.preV_le F W5 ha5
  have hmy := S126N.mk_iota (F.β ⟨a, haV⟩)
  generalize hm : (⟨iota (F.β ⟨a, haV⟩), S126N.iota_mem _⟩ : ↥(coreMod 8)) = m at hmy
  have hvx : Multiplicative.toAdd (iota (F.β ⟨a, haV⟩)) = S126L24.vx m := by rw [← hm]
  rw [QFix, emb_iota, hvx]
  constructor
  · have h5 : F.β ⟨a, haV⟩ ∈ W5 := (S126L24.mem_preV haV).1 ha5
    rw [← hmy, S126L24.mem_W5_iff] at h5
    exact h5
  · have hpa : p * a * p⁻¹ ∈ V := conj_mem hpV ⟨a, haV⟩
    have h1 : F.β ⟨p * a * p⁻¹ * a⁻¹, V.mul_mem hpa (V.inv_mem haV)⟩ ∈ W1 :=
      (S126L24.mem_preV _).1 ha1
    have e : (⟨p * a * p⁻¹ * a⁻¹, V.mul_mem hpa (V.inv_mem haV)⟩ : ↥V) =
        ⟨p * a * p⁻¹, hpa⟩ * (⟨a, haV⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul, map_inv, hpσ ⟨a, haV⟩ ⟨p * a * p⁻¹, hpa⟩ rfl, ← hmy] at h1
    have e2 : dAct c1 (QuotientGroup.mk m) * (QuotientGroup.mk m : D8)⁻¹ =
        QuotientGroup.mk (coreAct 8 c1 m * m⁻¹) := rfl
    rw [e2, S126L24.mem_W1_iff, S126L24.vx_mul, S126L24.vx_inv, S126L24.vx_coreAct] at h1
    exact h1

omit [Finite G] in
theorem card_fixA_le (F : Frame126 T L V) (hinj : Function.Injective F.β) {B : Subgroup G}
    {v i : G} (hS : S126Crd.Setup F.V1 F.V5 B v i) {p : G}
    (hpV : p ∈ Subgroup.normalizer (V : Set G)) (hpσ : ActsAs F p c1) :
    Nat.card (hS.fixA p) ≤ 8 := by
  classical
  let φ : ↥(hS.fixA p) → {z // QFix z} := fun a =>
    ⟨cmp (Multiplicative.toAdd (iota (F.β ⟨a, S126L24.preV_le F W5 a.2.1⟩))),
      qfix_of_mem F hpV hpσ a.2.1 a.2.2⟩
  have hφ : Function.Injective φ := by
    intro a a' haa
    have h1 := congrArg (fun z : {z // QFix z} => emb z.1) haa
    simp only [φ, emb_iota] at h1
    have h3 := iota_inj (Multiplicative.toAdd.injective h1)
    have h4 := hinj h3
    have h5 : (a : G) = a' := congrArg (fun w : ↥V => (w : G)) h4
    exact Subtype.ext h5
  calc Nat.card (hS.fixA p) ≤ Nat.card {z // QFix z} := Nat.card_le_card_of_injective φ hφ
    _ = 8 := by rw [Nat.card_eq_fintype_card, card_QFix]

omit [Finite G] in
theorem not_fixA_le (F : Frame126 T L V) {B : Subgroup G} {v i : G}
    (hS : S126Crd.Setup F.V1 F.V5 B v i) {p : G} (hpV : p ∈ Subgroup.normalizer (V : Set G))
    (hpσ : ActsAs F p c1) : ¬ hS.fixA p ≤ F.V1 := by
  intro hle
  obtain ⟨a, ha⟩ := F.β_surj (QuotientGroup.mk (pe 4 5))
  have h5 : (a : G) ∈ F.V5 := (S126L24.mem_preV a.2).2 (by
    rw [ha, S126L24.mem_W5_iff, S126L24.vx_pe]
    decide)
  have hpa : p * a * p⁻¹ ∈ V := conj_mem hpV a
  have h1 : p * a * p⁻¹ * (a : G)⁻¹ ∈ F.V1 := by
    refine (S126L24.mem_preV (V.mul_mem hpa (V.inv_mem a.2))).2 ?_
    have e : (⟨p * a * p⁻¹ * (a : G)⁻¹, V.mul_mem hpa (V.inv_mem a.2)⟩ : ↥V) =
        ⟨p * a * p⁻¹, hpa⟩ * a⁻¹ := rfl
    rw [e, map_mul, map_inv, hpσ a ⟨p * a * p⁻¹, hpa⟩ rfl, ha]
    show (QuotientGroup.mk (coreAct 8 c1 (pe 4 5) * (pe 4 5)⁻¹) : D8) ∈ W1
    rw [S126L24.mem_W1_iff, S126L24.vx_mul, S126L24.vx_inv, S126L24.vx_coreAct,
      S126L24.vx_pe]
    decide
  have h1' := (S126L24.mem_preV a.2).1 (hle ⟨h5, h1⟩)
  rw [ha, S126L24.mem_W1_iff, S126L24.vx_pe] at h1'
  exact absurd h1' (by decide)

theorem indep_c1_c2 : ∀ i j : ℤ, c1 ^ i * c2 ^ j = 1 → ((3 : ℕ) : ℤ) ∣ i ∧ ((3 : ℕ) : ℤ) ∣ j := by
  intro i j h
  have h1 : c1 ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact c1_pow_three
  have h2 : c2 ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact c2_pow_three
  rw [zpow_eq_zpow_emod i h1, zpow_eq_zpow_emod j h2] at h
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hc : ∀ a b : Fin 3, c1 ^ (a : ℕ) * c2 ^ (b : ℕ) = 1 → a = 0 ∧ b = 0 := by decide
  have key : ∀ a b : Fin 3, i % 3 = (a : ℕ) → j % 3 = (b : ℕ) → i % 3 = 0 ∧ j % 3 = 0 := by
    intro a b ha hb
    rw [ha, hb, zpow_natCast, zpow_natCast] at h
    obtain ⟨rfl, rfl⟩ := hc a b h
    exact ⟨by simpa using ha, by simpa using hb⟩
  have hfin : ∀ x : ℤ, (x = 0 ∨ x = 1 ∨ x = 2) → ∃ a : Fin 3, x = (a : ℕ) := by
    rintro x (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  obtain ⟨a, ha⟩ := hfin _ hi
  obtain ⟨b, hb⟩ := hfin _ hj
  obtain ⟨hi0, hj0⟩ := key a b ha hb
  exact ⟨Int.dvd_of_emod_eq_zero (by simpa using hi0), Int.dvd_of_emod_eq_zero (by simpa using hj0)⟩

theorem exists_E9 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ∃ P ≤ Li L F.V1, IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1L : Li L F.V1 ≤ L := S126L19b.L1_le_L F
  obtain ⟨l₁, hl₁, hl₁V, hσ₁⟩ := S126L1b.exists_mem_L1 F c1_mem c1_pow_three c1_block
  obtain ⟨l₂, hl₂, hl₂V, hσ₂⟩ := S126L1b.exists_mem_L1 F c2_mem c2_pow_three c2_block
  let f : ↥(Li L F.V1) →* Perm (Fin 8) := (S126T2.psiP F hH).comp (Subgroup.inclusion hL1L)
  have hfa : ∀ l : ↥(Li L F.V1), ActsAs F l (f l) := fun l =>
    S126T2.actsAs_psiP F hH (Subgroup.inclusion hL1L l)
  have hf1 : f ⟨l₁, hl₁⟩ = c1 := (hfa ⟨l₁, hl₁⟩).unique hσ₁ hl₁V
  have hf2 : f ⟨l₂, hl₂⟩ = c2 := (hfa ⟨l₂, hl₂⟩).unique hσ₂ hl₂V
  have hk : IsPGroup 2 ↥f.ker := by
    intro k
    have hk1 : S126T2.psiP F hH (Subgroup.inclusion hL1L (k : ↥(Li L F.V1))) = 1 := k.2
    have hq : S126L19a.psi F hH (Subgroup.inclusion hL1L (k : ↥(Li L F.V1))) = 1 :=
      Subtype.ext hk1
    have hC := (S126L19a.psi_eq_one_iff F hH _).1 hq
    obtain ⟨n, hn⟩ := S126T2.isPGroup_CL h1222 hH
      ⟨((k : ↥(Li L F.V1)) : G), hL1L (k : ↥(Li L F.V1)).2, hC⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hk3 : ¬ 3 ∣ Nat.card ↥f.ker := by
    obtain ⟨e, he⟩ := hk.exists_card_eq
    rw [he]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hr : 2 ≤ CFSG.Open.pRank 3 (Li L F.V1) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_quotient_eq f.ker hk3, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    have hfb : Function.Injective (QuotientGroup.kerLift f) := QuotientGroup.kerLift_injective f
    have he₁ : QuotientGroup.kerLift f (⟨l₁, hl₁⟩ : ↥(Li L F.V1)) = c1 := hf1
    have he₂ : QuotientGroup.kerLift f (⟨l₂, hl₂⟩ : ↥(Li L F.V1)) = c2 := hf2
    refine CFSG.RankThree.PartOne.KLC.two_le_pRank_of_two_commuting Nat.prime_three
      (e₁ := ((⟨l₁, hl₁⟩ : ↥(Li L F.V1)) : ↥(Li L F.V1) ⧸ f.ker))
      (e₂ := ((⟨l₂, hl₂⟩ : ↥(Li L F.V1)) : ↥(Li L F.V1) ⧸ f.ker)) ?_ ?_ ?_ ?_
    · apply hfb
      rw [map_mul, map_mul, he₁, he₂]
      decide
    · apply hfb
      rw [map_pow, he₁, map_one]
      exact c1_pow_three
    · apply hfb
      rw [map_pow, he₂, map_one]
      exact c2_pow_three
    · intro i j hij
      have h := congrArg (QuotientGroup.kerLift f) hij
      rw [map_mul, map_zpow, map_zpow, he₁, he₂, map_one] at h
      exact indep_c1_c2 i j h
  obtain ⟨E, hEL, hE, hcE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (Li L F.V1)
  have h9 : 3 ^ 2 ∣ Nat.card ↥E := by
    rw [hcE]
    exact Nat.pow_dvd_pow 3 hr
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  have hEc := hE.1
  have hK3 : IsElemAbelian 3 K := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact hEc.is_comm.comm (a : ↥E) (b : ↥E)
    · simpa using hE.2 (x : G) x.2
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEL,
    CFSG.SectionRank.isElemAbelian_map hK3 E.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  norm_num

theorem setup126 (h1224 : Lemma12_6_24) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G} (hHz : S126.InHz T L F.V1 H) :
    HypF91 T V L F.V1 F.V5 H ∧ F.V5.relIndex V = 2 ∧
      (∀ g ∈ H, F.V1 < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V)) ∧
      Nat.card F.V5 = 32 ∧
      Subgroup.centralizer (F.V5 : Set G) ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨-, -, -, -, h5, h6, h78⟩ := h1224 G T L V F hH hZ
  have hinj := S126L24.beta_injective F hZ
  refine ⟨(h78 H hHz).2.1, ?_, fun g _ hg => ?_, S126L24.card_V5 hinj, h6.2.2.1.le⟩
  · have hV64 : Nat.card V = 64 := by
      rw [Nat.card_congr (Equiv.ofBijective F.β ⟨hinj, F.β_surj⟩), S126L20.card_D8_eq]
    have h1 := Subgroup.card_mul_index (F.V5.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show F.V5 ≤ V from S126L24.preV_le F W5)).toEquiv, S126L24.card_V5 hinj, hV64] at h1
    show (F.V5.subgroupOf V).index = 2
    omega
  · have := h5 g (by rwa [conjSubgroup_eq])
    rwa [conjSubgroup_eq] at this

theorem le_pCoreOf_K (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) (hV : ¬ V ≤ pCoreOf 2 H) :
    V ≤ pCoreOf 2 (centralizerMod (pCoreOf 2 H) H (Li L F.V1)) := by
  obtain ⟨h, hidx, hyp5, hcard, hC⟩ := setup126 h1224 F hH hZ hHz
  have hinj := S126L24.beta_injective F hZ
  obtain ⟨-, hXV, -, hXV5⟩ := S126L24.sup_le_normalizers h1222 F hH
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  have hVpQ : F.V5 ≤ pCoreOf 2 H := h.Vp_le_pCoreOf_and_commutator_le.1
  set K := centralizerMod (pCoreOf 2 H) H (Li L F.V1) with hKdef
  have hKH : K ≤ H := centralizerMod_le_left _ _ _
  have hKc : ∀ x ∈ K, ∀ l ∈ Li L F.V1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 H := fun x hx => hx.2.2
  have hVK : V ≤ K := fun v hv => ⟨h.V_le_H hv, le_normalizer_pCoreOf 2 H (h.V_le_H hv),
    fun l hl => hVpQ (comm_mem_Vp hidx hv (hXV (Subgroup.mem_sup_left hl))
      (hXV5 (Subgroup.mem_sup_left hl)))⟩
  rcases le_or_exists_of_le h hVK with hle | ⟨g, hgK, hI⟩
  · exact hle
  exfalso
  have hgH : g ∈ H := hKH hgK
  obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp hV
  have hvp : v ∉ F.V5 := fun h5 => hvQ (hVpQ h5)
  have hS := S126L26.setup h hidx hV hyp5 hcard hC hgH hI hv hvp
  have hVpU : F.V5 ≤ conjClosure F.V5 H := le_conjClosure F.V5 H
  have hBU : conjSub g⁻¹ F.V5 ≤ conjClosure F.V5 H := HypF91.conjSub_inv_le_U hgH hVpU
  have hQA : ∀ q ∈ pCoreOf 2 H, ∀ a ∈ F.V5, q * a * q⁻¹ * a⁻¹ ∈ F.V1 :=
    fun q hq a ha => Q_comm h hq (hVpU ha)
  have hQB : ∀ q ∈ pCoreOf 2 H, ∀ b ∈ conjSub g⁻¹ F.V5, q * b * q⁻¹ * b⁻¹ ∈ F.V1 :=
    fun q hq b hb => Q_comm h hq (hBU hb)
  have hvK : v ∈ K := hVK hv
  have hiK : g⁻¹ * v * g ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hgK) hvK) hgK
  rcases pow_mem h hidx hV hyp5 hcard hC hgH hI hv hvp with h5 | h6
  ·
    obtain ⟨p, hpL1, hpV, hpσ⟩ := S126L1b.exists_mem_L1 F c1_mem c1_pow_three c1_block
    have hpH : p ∈ H := hL1H hpL1
    have hpcomm : ∀ y ∈ K, p * y * p⁻¹ * y⁻¹ ∈ pCoreOf 2 H := fun y hy => by
      have := (pCoreOf 2 H).inv_mem (hKc y hy p hpL1)
      convert this using 1
      group
    refine hS.not_pow_five_triv (p := p) (fun z hz => ?_) (fun a ha => ?_) (fun a ha => ?_)
      (fun a ha => ?_) (fun b hb => ?_) (card_fixA_le F hinj hS hpV hpσ) (not_fixA_le F hS hpV hpσ)
      (fun a ha => hQA _ h5 a ha)
    · have := Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer hpH) z hz
      rw [← this, mul_inv_cancel_right]
    · exact (Subgroup.mem_normalizer_iff.mp (hXV5 (Subgroup.mem_sup_left hpL1)) a).mp ha
    · have hp3 : ActsAs F (p ^ 3) 1 := by
        have := hpσ.pow hpV 3
        rwa [c1_pow_three] at this
      have hp3C := S126L24.mem_centralizer_of_actsAs_one' hinj (Subgroup.pow_mem _ hpV 3) hp3
      have e := Subgroup.mem_centralizer_iff.mp hp3C a (S126L24.preV_le F W5 ha)
      rw [← e, mul_inv_cancel_right, mul_inv_cancel]
      exact F.V1.one_mem
    · exact ⟨hS.i_A a ha.1, fix_comm h (hKH hiK) (hpcomm _ hiK) (hVpU ha.1) ha.2
        (hBU (hS.i_A a ha.1))⟩
    · exact ⟨hS.v_B b hb.1, fix_comm h (h.V_le_H hv) (hpcomm _ hvK) (hBU hb.1) hb.2
        (hVpU (hS.v_B b hb.1))⟩
  ·
    have hv2 : v * v = 1 := by
      rw [← pow_two]
      exact isElemAbelian_pow_eq_one h.elemAbelian hv
    have hi2 : (g⁻¹ * v * g) * (g⁻¹ * v * g) = 1 := by
      calc (g⁻¹ * v * g) * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
        _ = 1 := by rw [hv2, mul_one, inv_mul_cancel]
    have hu : v * (v * (g⁻¹ * v * g)) * v⁻¹ = (v * (g⁻¹ * v * g))⁻¹ := by
      calc v * (v * (g⁻¹ * v * g)) * v⁻¹ = (v * v) * (g⁻¹ * v * g) * v⁻¹ := by group
        _ = (g⁻¹ * v * g)⁻¹ * v⁻¹ := by rw [hv2, one_mul, inv_eq_of_mul_eq_one_right hi2]
        _ = (v * (g⁻¹ * v * g))⁻¹ := by group
    generalize hudef : v * (g⁻¹ * v * g) = u at hu h6
    have huK : u ∈ K := by rw [← hudef]; exact K.mul_mem hvK hiK
    have hx3 : (u ^ 2) ^ 3 ∈ pCoreOf 2 H := by rw [← pow_mul]; exact h6
    have hxQ : u ^ 2 ∉ pCoreOf 2 H := by
      intro hx
      rw [← hudef] at hx
      exact hS.not_sq_triv (fun a ha => hQA _ hx a ha) (fun b hb => hQB _ hx b hb)
    have hvx : v * u ^ 2 * v⁻¹ * u ^ 2 ∈ pCoreOf 2 H := by
      rw [← conj_pow, hu, inv_pow, inv_mul_cancel]
      exact (pCoreOf 2 H).one_mem
    obtain ⟨P, hPL1, hP, hcP⟩ := exists_E9 h1222 F hH
    have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple
      hH.hyp.nonabelian hHz.1.2
    exact false_of_e27 hSQ (hPL1.trans hL1H) hP hcP (hKH (K.pow_mem huK 2)) (h.V_le_H hv) hx3 hxQ
      (fun a ha => hKc _ (K.pow_mem huK 2) a (hPL1 ha)) (fun a ha => hKc _ hvK a (hPL1 ha)) hvx

end Frame

end S126L26

end CFSG.Quasithin.H13
