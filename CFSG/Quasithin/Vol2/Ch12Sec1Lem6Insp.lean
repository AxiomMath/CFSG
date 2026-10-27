module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Comp
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Ctr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankSmall
public import CFSG.GH74.KGroups.CoverM11
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
public import CFSG.Quasithin.Vol2.KGFactL34Uni
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Vol2.Ch5Sec1Borel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)

namespace Sec1216Insp

open Sec1216Ctr

structure Config (K : Type) [Group K] [Finite K] (v y : K) (A B S : Subgroup K) : Prop where
  quasi : CFSG.IsQuasisimple K
  hv : v ∈ Subgroup.center K
  hv1 : v ≠ 1
  hvA : v ∈ A
  elem : IsElemAbelian 2 (A ⊔ B)
  inf : A ⊓ B = ⊥
  cardA : 2 ^ 4 ≤ Nat.card A
  cardB : 2 ^ 3 ≤ Nat.card B
  cen : ∀ x ∈ A ⊔ B, x ∈ Subgroup.center K → x ∈ Subgroup.zpowers v
  sylow : IsSylowTwoOf S ⊤
  le : A ⊔ B ≤ S
  normA : S ≤ Subgroup.normalizer (A : Set K)
  normB : S ≤ Subgroup.normalizer (B : Set K)
  y7 : orderOf y = 7
  yA : y ∈ Subgroup.normalizer (A : Set K)

theorem card_le_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {c : ℕ}
    (h : ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E ≤ c) :
    ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E ≤ c := by
  intro E hE
  have h1 := h (E.map e.toMonoidHom) (Lin2.isElemAbelian_map' hE _)
  rwa [Lin2.card_map_of_inf_ker_eq_bot E _ (fun x _ hx => (e.map_eq_one_iff).mp hx)] at h1

namespace Config

variable {K : Type} [Group K] [Finite K] {v y : K} {A B S : Subgroup K}
  (c : Config K v y A B S)
include c

theorem sq_eq_one {x : K} (hx : x ∈ A ⊔ B) : x ^ 2 = 1 := c.elem.2 x hx

theorem orderOf_v : orderOf v = 2 :=
  orderOf_eq_prime (c.sq_eq_one (Subgroup.mem_sup_left c.hvA)) c.hv1

theorem two_dvd_card_center : 2 ∣ Nat.card (Subgroup.center K) := by
  have h := orderOf_dvd_natCard (⟨v, c.hv⟩ : ↥(Subgroup.center K))
  rwa [Subgroup.orderOf_mk, c.orderOf_v] at h

theorem card_zpowers_v : Nat.card (Subgroup.zpowers v) = 2 := by
  rw [Nat.card_zpowers, c.orderOf_v]

theorem zpowers_le_A : Subgroup.zpowers v ≤ A := by
  rw [Subgroup.zpowers_le]
  exact c.hvA

theorem card_sup : 2 ^ 7 ≤ Nat.card ↥(A ⊔ B) := by
  have hinj : Function.Injective (fun p : ↥A × ↥B =>
      (⟨(p.1 : K) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : K) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : K)⁻¹ * a = b' * (b : K)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
    have h3 : (a' : K)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [c.inf, Subgroup.mem_bot] at h3
    have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp h3).symm
    subst ha
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h1))
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h
  calc 2 ^ 7 = 2 ^ 4 * 2 ^ 3 := by norm_num
    _ ≤ Nat.card A * Nat.card B := Nat.mul_le_mul c.cardA c.cardB
    _ ≤ _ := h

theorem pCore_le_center : CFSG.pCore 2 K ≤ Subgroup.center K :=
  Lin2.OddRank.pCore_le_center c.quasi

theorem mem_zpowers_of_mem {x : K} (hx : x ∈ A ⊔ B) (hxQ : x ∈ CFSG.pCore 2 K) :
    x ∈ Subgroup.zpowers v :=
  c.cen x hx (c.pCore_le_center hxQ)

theorem card_map_sup :
    2 ^ 6 ≤ Nat.card ↥((A ⊔ B).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
  have h1 := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (A ⊔ B).subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  have hmem : ∀ x : ↥(A ⊔ B), ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (A ⊔ B).subtype) x = 1 →
      (x : K) ∈ Subgroup.zpowers v := by
    intro x hx
    refine c.mem_zpowers_of_mem x.2 ?_
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact hx
  have hinj : Function.Injective (fun x : ↥((QuotientGroup.mk' (CFSG.pCore 2 K)).comp
      (A ⊔ B).subtype).ker => (⟨((x : ↥(A ⊔ B)) : K), hmem x x.2⟩ : ↥(Subgroup.zpowers v))) := by
    intro x x' h
    have h' := congrArg Subtype.val h
    simp only at h'
    exact Subtype.ext (Subtype.ext h')
  have hker := (Nat.card_le_card_of_injective _ hinj).trans c.card_zpowers_v.le
  have h2 := c.card_sup
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card ↥((A ⊔ B).map (QuotientGroup.mk' (CFSG.pCore 2 K))) ≤ 63 := by omega
  have h3 := Nat.mul_le_mul hker h4
  omega

theorem elem_map : IsElemAbelian 2 ((A ⊔ B).map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
  Lin2.isElemAbelian_map' c.elem _

theorem inf_map : A.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ⊓
    B.map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
  have h1 : (QuotientGroup.mk a : K ⧸ CFSG.pCore 2 K) = QuotientGroup.mk b := hab.symm
  have h2 : a⁻¹ * b ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp h1
  have h3 : a⁻¹ * b ∈ A := c.zpowers_le_A (c.mem_zpowers_of_mem
    ((A ⊔ B).mul_mem (Subgroup.mem_sup_left (A.inv_mem ha)) (Subgroup.mem_sup_right hb)) h2)
  have hbA : b ∈ A := by
    have := A.mul_mem ha h3
    rwa [mul_inv_cancel_left] at this
  have hb1 : b = 1 := by
    have : b ∈ A ⊓ B := ⟨hbA, hb⟩
    rwa [c.inf, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, ← hab, hb1, map_one]

theorem map_A_ne_bot : A.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≠ ⊥ := by
  intro h
  have hA : A ≤ Subgroup.zpowers v := by
    intro a ha
    refine c.mem_zpowers_of_mem (Subgroup.mem_sup_left ha) ?_
    have : QuotientGroup.mk' (CFSG.pCore 2 K) a ∈ A.map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
      Subgroup.mem_map_of_mem _ ha
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have h1 := Subgroup.card_le_of_le hA
  have := c.cardA
  rw [c.card_zpowers_v] at h1
  omega

theorem map_B_ne_bot : B.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≠ ⊥ := by
  intro h
  have hB : B ≤ ⊥ := by
    intro b hb
    have hbQ : b ∈ CFSG.pCore 2 K := by
      have : QuotientGroup.mk' (CFSG.pCore 2 K) b ∈ B.map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
        Subgroup.mem_map_of_mem _ hb
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hbA := c.zpowers_le_A (c.mem_zpowers_of_mem (Subgroup.mem_sup_right hb) hbQ)
    rw [← c.inf]
    exact ⟨hbA, hb⟩
  have h1 := Subgroup.card_le_of_le hB
  have := c.cardB
  rw [Subgroup.card_bot] at h1
  omega

theorem false_of_card_le {c₀ : ℕ} (hc₀ : c₀ < 2 ^ 6)
    (h : ∀ E : Subgroup (K ⧸ CFSG.pCore 2 K), IsElemAbelian 2 E → Nat.card E ≤ c₀) : False := by
  have h1 := h _ c.elem_map
  have h2 := c.card_map_sup
  omega

theorem false_of_sylowCenter (h : SylowCenterLeTwo (K ⧸ CFSG.pCore 2 K)) : False := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hS : IsSylowTwoOf (S.map π) ⊤ :=
    A312.isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective _) c.sylow
  have hnorm : ∀ {X : Subgroup K}, S ≤ Subgroup.normalizer (X : Set K) →
      S.map π ≤ Subgroup.normalizer ((X.map π : Subgroup _) : Set _) := fun hX =>
    (Subgroup.map_mono hX).trans (Subgroup.le_normalizer_map π)
  obtain ⟨a, haA, ha1, haC⟩ := Sec1215.exists_ne_one_mem_centralizer hS.2.1
    (Subgroup.map_mono (le_sup_left.trans c.le)) (hnorm c.normA) c.map_A_ne_bot
  obtain ⟨b, hbB, hb1, hbC⟩ := Sec1215.exists_ne_one_mem_centralizer hS.2.1
    (Subgroup.map_mono (le_sup_right.trans c.le)) (hnorm c.normB) c.map_B_ne_bot
  have hab := h _ hS a (Subgroup.map_mono (le_sup_left.trans c.le) haA) b
    (Subgroup.map_mono (le_sup_right.trans c.le) hbB)
    (fun u hu => (Subgroup.mem_centralizer_iff.mp haC u hu).symm)
    (fun u hu => (Subgroup.mem_centralizer_iff.mp hbC u hu).symm) ha1 hb1
  have : a ∈ A.map π ⊓ B.map π := ⟨haA, hab ▸ hbB⟩
  rw [c.inf_map, Subgroup.mem_bot] at this
  exact ha1 this

theorem false_of_seven
    (h : ∀ (P E : Subgroup (K ⧸ CFSG.pCore 2 K)) (g : K ⧸ CFSG.pCore 2 K), IsSylowTwoOf P ⊤ →
      E ≠ ⊥ → E ≤ P → P ≤ Subgroup.normalizer (E : Set _) → orderOf g = 7 →
      g ∈ Subgroup.normalizer (E : Set _) → False) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf (S.map (QuotientGroup.mk' (CFSG.pCore 2 K))) ⊤ :=
    A312.isSylowTwoOf_top_map _ (QuotientGroup.mk'_surjective _) c.sylow
  have hy1 : QuotientGroup.mk' (CFSG.pCore 2 K) y ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨y, h1⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h7 := orderOf_dvd_of_pow_eq_one hk'
    rw [c.y7] at h7
    have := (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 7 2)).eq_one_of_dvd h7
    omega
  have hy7 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 K) y) = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 K)) y
    rw [c.y7] at h1
    rcases (Nat.dvd_prime this.out).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hy1
    · exact h2
  exact h _ _ _ hS c.map_A_ne_bot (Subgroup.map_mono (le_sup_left.trans c.le))
    ((Subgroup.map_mono c.normA).trans (Subgroup.le_normalizer_map _)) hy7
    (Subgroup.le_normalizer_map _ ⟨y, c.yA, rfl⟩)

theorem center_eq_pCore {Y : Type} [Group Y] [IsSimpleGroup Y]
    (e : (K ⧸ CFSG.pCore 2 K) ≃* Y) : Subgroup.center K = CFSG.pCore 2 K := by
  refine le_antisymm ?_ c.pCore_le_center
  have : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := e.isSimpleGroup
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hN : ((Subgroup.center K).map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center K).map π) with h | h
  · intro x hx
    have hmem : π x ∈ (Subgroup.center K).map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    have hcenter : ∀ k : K, k ∈ Subgroup.center K := by
      intro k
      have hk : π k ∈ (Subgroup.center K).map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨z, hz, hzk⟩ := hk
      have hn : z⁻¹ * k ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp hzk
      have e1 : k = z * (z⁻¹ * k) := by group
      rw [e1]
      exact (Subgroup.center K).mul_mem hz (c.pCore_le_center hn)
    obtain ⟨a, b, hab⟩ := c.quasi.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      (Subgroup.mem_center_iff.mp (hcenter x) y').symm]

theorem false_of_noDoubleCover {Y : Type} [Group Y] [IsSimpleGroup Y]
    (e : (K ⧸ CFSG.pCore 2 K) ≃* Y) (hY : CFSG.Monster.Schur.NoPerfectDoubleCover Y) : False := by
  have hZ := c.center_eq_pCore e
  have hperf : commutator K = ⊤ := c.quasi.1.commutator_eq_top
  have hZ2 : IsPGroup 2 (Subgroup.center K) := hZ ▸ CFSG.pCore_isPGroup
  have hZ1 : Subgroup.center K ≠ ⊥ := fun h =>
    c.hv1 (Subgroup.mem_bot.mp (h ▸ c.hv))
  have hJ := CFSG.GH74.KGroups.center_quotient_eq_bot hperf c.quasi.2.1
  obtain ⟨C, _, _, -, -, -, hperfC, hcard, ⟨eC⟩⟩ :=
    CFSG.GH74.KGroups.exists_double_cover hperf hZ2 hZ1 hJ
  have : Group.IsPerfect C := Group.isPerfect_def.mpr hperfC
  let e' : K ⧸ Subgroup.center K ≃* Y := (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  exact hY C (CFSG.GH74.Generic.centralQuotientMap (eC.trans e'))
    (CFSG.GH74.Generic.centralQuotientMap_surjective _) inferInstance
    (by rw [CFSG.GH74.Generic.centralQuotientMap_ker]; exact hcard)

end Config

theorem g24_false (hG24 : LemCompG24) {Y : Type} [Group Y] [Finite Y]
    (hY : ChevalleyExceptionalModel Y .G2 2 2) (P E : Subgroup Y) (g : Y) (hP : IsSylowTwoOf P ⊤)
    (hE : E ≠ ⊥) (hEP : E ≤ P) (hPE : P ≤ Subgroup.normalizer (E : Set Y)) (hg : orderOf g = 7)
    (hgE : g ∈ Subgroup.normalizer (E : Set Y)) : False := by
  apply hG24 Y hY P E hP hE hEP hPE
  have h1 : Subgroup.zpowers g ≤ Subgroup.normalizer (E : Set Y) := by
    rw [Subgroup.zpowers_le]
    exact hgE
  have h2 := Subgroup.card_dvd_of_le h1
  rwa [Nat.card_zpowers, hg] at h2

theorem isElemAbelian_subgroupOf {G : Type} [Group G] {E K : Subgroup G}
    (h : IsElemAbelian 2 E) : IsElemAbelian 2 (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf h K

end Sec1216Insp

open Sec1216Insp Sec1216Ctr

theorem lem1216CompInsp_of
    (hG24 : LemCompG24) : Lem1216CompInsp := by
  intro G _ _ K z hq hcases v y A B S hvC hv1 hvA helem hinf hcA hcB hcen hS hABS hSA hSB hyK hy7
    hyA
  have hSK : S ≤ K := hS.1
  have hAK : A ≤ K := le_sup_left.trans (hABS.trans hSK)
  have hBK : B ≤ K := le_sup_right.trans (hABS.trans hSK)
  have hvK : v ∈ K := hAK hvA
  have hsup : (A ⊔ B).subgroupOf K = A.subgroupOf K ⊔ B.subgroupOf K :=
    Subgroup.subgroupOf_sup hAK hBK
  have cfg : Config ↥K ⟨v, hvK⟩ ⟨y, hyK⟩ (A.subgroupOf K) (B.subgroupOf K) (S.subgroupOf K) :=
    { quasi := hq
      hv := Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hvC g g.2)
      hv1 := fun h => hv1 (congrArg Subtype.val h)
      hvA := Subgroup.mem_subgroupOf.mpr hvA
      elem := hsup ▸ isElemAbelian_subgroupOf helem
      inf := by
        rw [eq_bot_iff]
        intro x hx
        have : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
        rw [hinf, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (Subtype.ext this)
      cardA := by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
      cardB := by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv]
      cen := by
        intro x hx hxc
        rw [← hsup] at hx
        have hxC : (x : G) ∈ Subgroup.centralizer (K : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨k, hk⟩)
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hcen x hx hxC)
        exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simpa using hm)⟩
      sylow := by
        refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm, ?_⟩
        show ¬ 2 ∣ (S.subgroupOf K).relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact hS.2.2
      le := hsup ▸ fun x hx => hABS hx
      normA := le_normalizer_subgroupOf hSA
      normB := le_normalizer_subgroupOf hSB
      y7 := by rw [← Subgroup.orderOf_coe]; exact hy7
      yA := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have := Subgroup.mem_normalizer_iff.mp hyA x
        simpa [Subgroup.mem_subgroupOf] using this }
  rcases hcases with ha | hb | hc | hd | he | hf
  ·
    have hs : IsSimpleGroup ↥K := ha.1
    have hZ : Subgroup.center ↥K = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hq.2.2
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
        have hx : x ∈ Subgroup.center ↥K := by rw [h]; exact Subgroup.mem_top x
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (Subgroup.mem_center_iff.mp hx y').symm]
    have := cfg.hv
    rw [hZ, Subgroup.mem_bot] at this
    exact cfg.hv1 this
  ·
    obtain ⟨-, -, hm | hm, -⟩ := hb
    · obtain ⟨k, _, _, hk, ⟨e⟩⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
          (Q := ↥K ⧸ CFSG.pCore 2 ↥K) (Or.inl ⟨by decide, hm⟩)
      refine cfg.false_of_card_le (c₀ := 16) (by norm_num) (card_le_of_mulEquiv e ?_)
      intro E hE
      exact KGL34A.card_le_sixteen (by rw [hk]; norm_num)
        (fun x hx y hy => congrArg Subtype.val (hE.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩))
        (fun x hx => by rw [← sq]; exact hE.2 x hx)
    · exact cfg.false_of_seven fun P E g hP hE hEP hPE hg hgE =>
        g24_false hG24 hm P E g hP hE hEP hPE hg hgE
  ·
    obtain ⟨-, -, hZ, -⟩ := hc
    have h2 := cfg.two_dvd_card_center
    rcases hZ with h | h <;> rw [h] at h2 <;> norm_num at h2
  ·
    obtain ⟨-, -, hZ, -, -⟩ := hd
    have h2 := cfg.two_dvd_card_center
    rcases hZ with h | h <;> rw [h] at h2 <;> norm_num at h2
  ·
    obtain ⟨hm | ⟨p, hp, hm⟩, -⟩ := he
    · have hcard : Nat.card ↥K = 5616 := Lin2.OddRank.card_L33 hm
      have h1 := Subgroup.card_subgroup_dvd_card (A.subgroupOf K ⊔ B.subgroupOf K)
      rw [hcard] at h1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hE2 : IsPGroup 2 ↥(A.subgroupOf K ⊔ B.subgroupOf K) := fun x =>
        ⟨1, Subtype.ext (by simpa using cfg.elem.2 x x.2)⟩
      obtain ⟨m, hm'⟩ := hE2.exists_card_eq
      have h2 := cfg.card_sup
      rw [hm'] at h1 h2
      have h7 : 7 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
      have h3 : 2 ^ 7 ∣ 5616 := (pow_dvd_pow 2 h7).trans h1
      norm_num at h3
    · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
      have hchar : CharP F p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp.1 le_rfl hF
      have hF2 : ringChar F ≠ 2 := by
        rw [ringChar.eq F p]
        exact Lin2.OddRank.ne_two_of_fermat_or_mersenne hp
      have h1 := Lin2.card_le_four_psl2 hF2 (Lin2.isElemAbelian_map' cfg.elem e.toMonoidHom)
      rw [Lin2.card_map_of_inf_ker_eq_bot _ _ (fun x _ hx => (e.map_eq_one_iff).mp hx)] at h1
      have h2 := cfg.card_sup
      omega
  ·
    obtain ⟨⟨s, hs, ⟨e⟩⟩, -⟩ := hf
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have : IsSimpleGroup (Carrier .M11) := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
      have hZ := cfg.center_eq_pCore e
      have h := CFSG.GH74.KGroups.M11.noTwoCover_M11 (Carrier .M11) ⟨MulEquiv.refl _⟩ ↥K hq
        (hZ ▸ CFSG.pCore_isPGroup) ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans e⟩
      have := cfg.hv
      rw [h, Subgroup.mem_bot] at this
      exact cfg.hv1 this
    ·
      refine cfg.false_of_card_le (c₀ := 2 ^ 3) (by norm_num) (card_le_of_mulEquiv e ?_)
      intro E hE
      exact Setup.X1.m12_rank_le E (fun x hx y hy => congrArg Subtype.val
        (hE.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)) (fun x hx => by rw [← sq]; exact hE.2 x hx)
    ·
      refine cfg.false_of_card_le (c₀ := 2 ^ 4) (by norm_num) (card_le_of_mulEquiv e ?_)
      intro E hE
      exact Setup.X1.m22_rank_le E (fun x hx y hy => congrArg Subtype.val
        (hE.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)) (fun x hx => by rw [← sq]; exact hE.2 x hx)
    ·
      refine cfg.false_of_card_le (c₀ := 2 ^ 4) (by norm_num) (card_le_of_mulEquiv e ?_)
      intro E hE
      exact Setup.X1.m23_rank_le E (fun x hx y hy => congrArg Subtype.val
        (hE.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)) (fun x hx => by rw [← sq]; exact hE.2 x hx)
    ·
      exact cfg.false_of_sylowCenter (SylowCenterLeTwo.of_mulEquiv e m24_sylowCenterLeTwo)
    ·
      refine cfg.false_of_card_le (c₀ := 31) (by norm_num) (card_le_of_mulEquiv e ?_)
      intro E hE
      have := Lin2.j2_native_rank E hE
      omega
    ·
      have : IsSimpleGroup (Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
      exact cfg.false_of_noDoubleCover e
        (CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
          CFSG.ComponentClassification.RankTwoSporadic.J4.j4_foxCert
          CFSG.ComponentClassification.RankTwoSporadic.J4.j4_formCert)
    ·
      refine cfg.false_of_card_le (c₀ := 31) (by norm_num) (card_le_of_mulEquiv e ?_)
      intro E hE
      have := Lin2.hs_native_rank E hE
      omega
    ·
      exact cfg.false_of_sylowCenter (SylowCenterLeTwo.of_mulEquiv e he_sylowCenterLeTwo)
    ·
      exact cfg.false_of_sylowCenter (SylowCenterLeTwo.of_mulEquiv e ru_sylowCenterLeTwo)

end CFSG.Quasithin.H13
