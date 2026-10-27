module

public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
import CFSG.RankThree.PartTwo.Sec20.OneBasics

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

@[expose] def Claim1844Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    let Lc := inSubgroup perfectResidual
      ((inSubgroup perfectResidual H ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)))
    ∀ g : G, g * c * g⁻¹ ∈ A → ∀ a ∈ A,
      InducesInnerMod (g⁻¹ * a * g) Lc (CFSG.Open.pCoreOf 2 Lc)

namespace SylowFusion

theorem pow_conj_mul_inv_mem {K Y : Subgroup G} {a k : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hkY : k ∈ Subgroup.normalizer (Y : Set G))
    (hak : ∀ y ∈ K, a * y * a⁻¹ * (k * y * k⁻¹)⁻¹ ∈ Y) (n : ℕ) :
    ∀ y ∈ K, a ^ n * y * (a ^ n)⁻¹ * (k ^ n * y * (k ^ n)⁻¹)⁻¹ ∈ Y := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hz : a ^ n * y * (a ^ n)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ haK n) y).mp hy
    have h2 := (Subgroup.mem_normalizer_iff.mp hkY _).mp (ih y hy)
    convert Y.mul_mem (hak _ hz) h2 using 1
    rw [pow_succ', pow_succ']
    group

theorem mem_pCoreOf_of_forall_mem {K : Subgroup G}
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) {x : G} (hx : x ∈ K)
    (hcen : ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    x ∈ CFSG.Open.pCoreOf 2 K := by
  have hmem : ((⟨x, hx⟩ : K) : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : (((⟨x, hx⟩ : K) * y * (⟨x, hx⟩ : K)⁻¹ * y⁻¹ : K) : K ⧸ CFSG.pCore 2 K) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
      exact hcen y y.2
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hmem
  exact hmem

theorem commute_of_inducesInnerMod {K S : Subgroup G} {a : G} (ha3 : a ^ 3 = 1)
    (haS : a ∈ Subgroup.normalizer (S : Set G)) (hS : CFSG.ABGLocalTools.IsSylowOf 3 S K)
    (hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hinner : InducesInnerMod a K (CFSG.Open.pCoreOf 2 K))
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) {s : G} (hs : s ∈ S) :
    a * s = s * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨haK, k, hk, hak⟩ := hinner
  set Q := CFSG.Open.pCoreOf 2 K with hQ
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hSK : S ≤ K := hS.le
  have hS3 : IsPGroup 3 S := hS.isPGroup
  have hk3 : k ^ 3 ∈ Q := by
    refine mem_pCoreOf_of_forall_mem hZ (K.pow_mem hk 3) fun y hy => ?_
    have h3 := pow_conj_mul_inv_mem haK (hKQ hk) hak 3 y hy
    rw [ha3, one_mul, inv_one, mul_one] at h3
    convert Q.inv_mem h3 using 1
    group
  obtain ⟨P, hPS⟩ := hS
  have hmemS : ∀ x : K, x ∈ (P : Subgroup K) ↔ (x : G) ∈ S := by
    intro x
    rw [← hPS]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx⟩
      rwa [← Subtype.ext hxx]
  set P' : Sylow 3 (K ⧸ CFSG.pCore 2 K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'
  have hkN : ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K) ∈
      Subgroup.normalizer ((P' : Subgroup (K ⧸ CFSG.pCore 2 K)) : Set (K ⧸ CFSG.pCore 2 K)) := by
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro z hz
    rw [hP', Sylow.coe_mapSurjective] at hz ⊢
    obtain ⟨p, hp, rfl⟩ := hz
    have hpS : (p : G) ∈ S := (hmemS p).mp hp
    have hapS : a * p * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp haS _).mp hpS
    refine ⟨⟨a * p * a⁻¹, hSK hapS⟩, (hmemS _).mpr hapS, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf]
    have h2 := (Subgroup.mem_normalizer_iff.mp (hKQ (K.inv_mem (hSK hapS))) _).mp
      (Q.inv_mem (hak p (hSK hpS)))
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    group
  have hk3' : IsPGroup 3 (Subgroup.zpowers ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K)) := by
    have hpow : ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
      exact hk3
    have hdvd : Nat.card (Subgroup.zpowers ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K)) ∣ 3 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hm
  have hkP : ((⟨k, hk⟩ : K) : K ⧸ CFSG.pCore 2 K) ∈ (P' : Subgroup (K ⧸ CFSG.pCore 2 K)) :=
    ((hk3'.inf_normalizer_sylow P').le ⟨Subgroup.mem_zpowers _, hkN⟩).2
  rw [hP', Sylow.coe_mapSurjective] at hkP
  obtain ⟨p₀, hp₀, hp₀k⟩ := hkP
  have hq₀ : (p₀ : G)⁻¹ * k ∈ Q := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf] at hp₀k
    exact hp₀k
  have hp₀S : (p₀ : G) ∈ S := (hmemS p₀).mp hp₀
  have hsK := hSK hs
  have hks : k * s * k⁻¹ * s⁻¹ ∈ Q := by
    have hcomm : (p₀ : G) * s⁻¹ * (p₀ : G)⁻¹ = s⁻¹ := by
      rw [show (p₀ : G) * s⁻¹ * (p₀ : G)⁻¹ = ((p₀ : G) * s * (p₀ : G)⁻¹)⁻¹ by group,
        hSab _ hp₀S _ hs, mul_inv_cancel_right]
    have h1 : s * ((p₀ : G)⁻¹ * k)⁻¹ * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hKQ hsK) _).mp (Q.inv_mem hq₀)
    have h3 := (Subgroup.mem_normalizer_iff.mp (hKQ p₀.2) _).mp (Q.mul_mem hq₀ h1)
    have e : k * s * k⁻¹ * s⁻¹ =
        (p₀ : G) * ((p₀ : G)⁻¹ * k * (s * ((p₀ : G)⁻¹ * k)⁻¹ * s⁻¹)) * (p₀ : G)⁻¹ := by
      calc k * s * k⁻¹ * s⁻¹ = k * s * k⁻¹ * ((p₀ : G) * s⁻¹ * (p₀ : G)⁻¹) := by rw [hcomm]
        _ = _ := by group
    rw [e]
    exact h3
  have has : a * s * a⁻¹ * s⁻¹ ∈ Q := by
    convert Q.mul_mem (hak s hsK) hks using 1
    group
  have has' : a * s * a⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem ((Subgroup.mem_normalizer_iff.mp haS s).mp hs) (S.inv_mem hs)
  have hone : a * s * a⁻¹ * s⁻¹ = 1 :=
    Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) S Q hS3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)) has' has
  calc a * s = a * s * a⁻¹ * s⁻¹ * (s * a) := by group
    _ = s * a := by rw [hone, one_mul]

variable {A M H : Subgroup G} {c : G}

theorem lc_le_centralizer (H : Subgroup G) (c : G) :
    lc H c ≤ Subgroup.centralizer ({c} : Set G) :=
  (Subgroup.map_subtype_le _).trans
    (sup_le inf_le_right (CFSG.LieType.BorelTits.pCoreOf_le 2 _))

theorem nonempty_quotient_lc (h184 : Item184_1) (hH : Sec18H G A M H c) :
    Nonempty (lc H c ⧸ CFSG.pCore 2 (lc H c) ≃* projSL 3 (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hL
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set L₀ := inSubgroup perfectResidual (L ⊓ C) with hL₀
  set R := CFSG.Open.pCoreOf 2 C with hR
  set X := L ⊓ C ⊔ R with hX
  obtain ⟨e⟩ := nonempty_quotient_perfectResidual_inf_centralizer h184 hH
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hXC : X ≤ C := sup_le inf_le_right (CFSG.LieType.BorelTits.pCoreOf_le 2 C)
  have hlcX : lc H c ≤ X := Subgroup.map_subtype_le _
  have hL₀ : L₀ ≤ L ⊓ C := Subgroup.map_subtype_le _
  have hL₀lc : L₀ ≤ lc H c :=
    Sec18.le_inSubgroup_perfectResidual (commutator_inSubgroup_perfectResidual (L ⊓ C))
      (hL₀.trans le_sup_left)
  have hperf : Group.IsPerfect (lc H c) := by
    have := (CFSG.perfect_residual_characterization (G := ↥X)).2.2.1
    exact Group.IsPerfect.map X.subtype
  have hlcL₀ : lc H c ≤ L₀ ⊔ R :=
    Sec6.le_perfectResidual_sup hperf (inf_le_right.trans hCR) hlcX
  obtain ⟨⟨e₁⟩, -⟩ := Claim184LcProof.quotient_mulEquiv_of_le_sup (L := L₀) (R := R)
    (N := lc H c) hL₀lc hlcL₀ ((hL₀.trans inf_le_right).trans hCR) ((hlcX.trans hXC).trans hCR)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C)
  exact ⟨e₁.symm.trans e⟩

theorem center_quotient_lc_eq_bot (h184 : Item184_1) (hH : Sec18H G A M H c) :
    Subgroup.center (lc H c ⧸ CFSG.pCore 2 (lc H c)) = ⊥ := by
  obtain ⟨e⟩ := nonempty_quotient_lc h184 hH
  have hmap := Subgroup.map_center_eq e
  rw [Sec4.center_projSL_eq_bot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

end SylowFusion


namespace SylowFusion

variable {A M H : Subgroup G} {c : G}

theorem isSylowOf_lc (h1812 : Item181_2) (h184 : Item184_1) (hH : Sec18H G A M H c) :
    CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ inSubgroup perfectResidual H) (lc H c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := inSubgroup perfectResidual H with hL
  set B := A ⊓ L with hB
  have hBL := Sec20.isSylowOf_three_inf_of_mem_scriptH h1812 h184 hH.toSec18Std hH.mem_scriptH
  have hBlc : B ≤ lc H c := (inf_lc_eq h1812 h184 hH).ge.trans inf_le_right
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hBL ⊢
  obtain ⟨hBL', hB3, hidx⟩ := hBL
  refine ⟨hBlc, hB3, fun hdvd => hidx ?_⟩
  obtain ⟨e⟩ := nonempty_quotient_lc h184 hH
  obtain ⟨⟨e'⟩, -⟩ := h184 G A M hH.toSec18Std H hH.mem_scriptH
  have hq : Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (lc H c ⧸ CFSG.pCore 2 (lc H c)) :=
    (Nat.card_congr e'.toEquiv).trans (Nat.card_congr e.toEquiv).symm
  have h1 := Subgroup.relIndex_mul_card B L
  rw [inf_eq_left.mpr hBL'] at h1
  have h2 := Subgroup.relIndex_mul_card B (lc H c)
  rw [inf_eq_left.mpr hBlc] at h2
  have h3L := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L)
  have h3c := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 (lc H c))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := lc H c))
  have hb : 0 < Nat.card B := Nat.card_pos
  have key : B.relIndex (lc H c) * Nat.card (CFSG.pCore 2 L) =
      B.relIndex L * Nat.card (CFSG.pCore 2 (lc H c)) := by
    apply Nat.eq_of_mul_eq_mul_right hb
    calc B.relIndex (lc H c) * Nat.card (CFSG.pCore 2 L) * Nat.card B
        = B.relIndex (lc H c) * Nat.card B * Nat.card (CFSG.pCore 2 L) := by ring
      _ = Nat.card (L ⧸ CFSG.pCore 2 L) * Nat.card (CFSG.pCore 2 (lc H c)) *
          Nat.card (CFSG.pCore 2 L) := by rw [h2, h3c, ← hq]
      _ = B.relIndex L * Nat.card B * Nat.card (CFSG.pCore 2 (lc H c)) := by
          rw [h1, h3L]; ring
      _ = B.relIndex L * Nat.card (CFSG.pCore 2 (lc H c)) * Nat.card B := by ring
  have h3 : 3 ∣ B.relIndex L * 2 ^ n := by
    rw [← hn, ← key]
    exact Dvd.dvd.mul_right hdvd _
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

theorem exists_mem_normalizer_conj_eq (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (hin : Claim1844Inner) (hH : Sec18H G A M H c) {g : G}
    (hd : g * c * g⁻¹ ∈ A) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), w * c * w⁻¹ = g * c * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := lc H c with hK
  set B := A ⊓ inSubgroup perfectResidual H with hB
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set A' := A.comap (MulAut.conj g).toMonoidHom with hA'
  have hmemA' : ∀ x, x ∈ A' ↔ g * x * g⁻¹ ∈ A := fun x => Iff.rfl
  have hcA' : c ∈ A' := (hmemA' c).mpr hd
  have hA'3 : ∀ x ∈ A', x ^ 3 = 1 := by
    intro x hx
    have h := hA3 _ ((hmemA' x).mp hx)
    rwa [conj_pow, conj_eq_one_iff] at h
  have hA'ab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    have h := hAab _ ((hmemA' x).mp hx) _ ((hmemA' y).mp hy)
    have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := h
        _ = g * (y * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  have hA'K : ∀ x ∈ A', x ∈ Subgroup.normalizer (K : Set G) := by
    intro x hx
    apply normalizer_zpowers_le_normalizer_lc h1842 hH
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [(Commute.zpow_right (show Commute x c from hA'ab x hx c hcA') i).eq,
      mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c i
  have hTK : A' ⊔ K ≤ Subgroup.normalizer (K : Set G) := sup_le hA'K Subgroup.le_normalizer
  have hA'p : IsPGroup 3 A' := fun x => ⟨1, Subtype.ext (by simpa using hA'3 _ x.2)⟩
  obtain ⟨Q, hQ⟩ := (hA'p.comap_subtype : IsPGroup 3 (A'.subgroupOf (A' ⊔ K))).exists_le_sylow
  set R := (Q : Subgroup (A' ⊔ K : Subgroup G)).map (A' ⊔ K).subtype with hR
  have hRT : CFSG.ABGLocalTools.IsSylowOf 3 R (A' ⊔ K) := ⟨Q, rfl⟩
  have hA'R : A' ≤ R := fun x hx =>
    ⟨⟨x, le_sup_left (a := A') hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  set S := R ⊓ K with hS
  have hSK : CFSG.ABGLocalTools.IsSylowOf 3 S K := hRT.inf_of_le_normalizer le_sup_right hTK
  have hA'S : ∀ x ∈ A', x ∈ Subgroup.normalizer (S : Set G) := by
    intro x hx
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    rintro s ⟨hsR, hsK⟩
    exact ⟨R.mul_mem (R.mul_mem (hA'R hx) hsR) (R.inv_mem (hA'R hx)),
      (Subgroup.mem_normalizer_iff.mp (hA'K x hx) s).mp hsK⟩
  obtain ⟨y, hyK, hSy⟩ := exists_map_conj_eq_of_isSylowOf (isSylowOf_lc h1812 h184 hH) hSK
  have hmemS : ∀ s ∈ S, ∃ b ∈ B, s = y * b * y⁻¹ := by
    intro s hs
    rw [hSy] at hs
    obtain ⟨b, hb, rfl⟩ := hs
    exact ⟨b, hb, rfl⟩
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := hmemS s hs
    rw [conj_pow, hA3 b hb.1, mul_one, mul_inv_cancel]
  have hSab : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    obtain ⟨b, hb, rfl⟩ := hmemS s hs
    obtain ⟨b', hb', rfl⟩ := hmemS t ht
    calc y * b * y⁻¹ * (y * b' * y⁻¹) = y * (b * b') * y⁻¹ := by group
      _ = y * (b' * b) * y⁻¹ := by rw [hAab b hb.1 b' hb'.1]
      _ = y * b' * y⁻¹ * (y * b * y⁻¹) := by group
  have hZ := center_quotient_lc_eq_bot h184 hH
  have hinA' : ∀ x ∈ A', InducesInnerMod x K (CFSG.Open.pCoreOf 2 K) := by
    intro x hx
    have h := hin G A M H c hH g hd (g * x * g⁻¹) ((hmemA' x).mp hx)
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
  have hSA' : S ≤ A' := by
    intro s hs
    have hcomm : ∀ x ∈ A', x * s = s * x := fun x hx =>
      commute_of_inducesInnerMod (hA'3 x hx) (hA'S x hx) hSK hSab (hinA' x hx) hZ hs
    rw [hmemA']
    refine Item183NMProof.mem_of_commute_of_sec18Std hH.toSec18Std ?_ fun a ha => ?_
    · rw [conj_pow, hS3 s hs, mul_one, mul_inv_cancel]
    · have hx : g⁻¹ * a * g ∈ A' := by
        rw [hmemA']
        convert ha using 1
        group
      have h := hcomm _ hx
      calc a * (g * s * g⁻¹) = g * (g⁻¹ * a * g * s) * g⁻¹ := by group
        _ = g * (s * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
        _ = g * s * g⁻¹ * a := by group
  have hyC : y * c = c * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (lc_le_centralizer H c hyK)
  have hle : A ≤ A'.comap (MulAut.conj y).toMonoidHom := by
    refine (eq_zpowers_sup_of_sec18H h1812 h184 hH).le.trans (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le]
      show y * c * y⁻¹ ∈ A'
      rw [hyC, mul_inv_cancel_right]
      exact hcA'
    · intro b hb
      show y * b * y⁻¹ ∈ A'
      apply hSA'
      rw [hSy]
      exact ⟨b, hb, rfl⟩
  refine ⟨g * y, ?_, ?_⟩
  · apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro x hx
    have h := (hmemA' _).mp (Subgroup.mem_comap.mp (hle hx))
    convert h using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [show g * y * c * (g * y)⁻¹ = g * (y * c * y⁻¹) * g⁻¹ by group, hyC,
      mul_inv_cancel_right]

end SylowFusion

open SylowFusion in
theorem item184_4_of (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (hin : Claim1844Inner) : Item184_4 := by
  intro G _ _ A M H c hH
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  ext F
  constructor
  · rintro ⟨⟨g, rfl⟩, hFA⟩
    have hd : g * c * g⁻¹ ∈ A := by
      simpa using hFA (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers c))
    obtain ⟨w, hw, hwc⟩ := exists_mem_normalizer_conj_eq h1812 h184 h1842 hin hH hd
    refine ⟨w, hw, ?_⟩
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hwc]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, rfl⟩, ?_⟩
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa using (Subgroup.mem_normalizer_iff.mp hw c).mp hcA

end CFSG.RankThree.PartTwo.Sec18
