module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11a
public import CFSG.Quasithin.EmptyFaithful.S153LList3
public import CFSG.Quasithin.Background.FFC4Ord3
public import CFSG.Quasithin.Vol2.Ch12Sec6L3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

section B56

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem three_dvd_card_of_order_three {X : Type} [Group X] [Finite X] {x : X} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1) : 3 ∣ Nat.card X := by
  have h : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  rw [← h]
  exact orderOf_dvd_natCard x

omit [Finite W] in
theorem three_dvd_card_of_le_of_order_three {G₁ G₀ : Subgroup (MulAut W)} [Finite ↥G₀]
    (hle : G₁ ≤ G₀) {x : ↥G₁} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) : 3 ∣ Nat.card ↥G₀ := by
  have hx1' : (⟨(x : MulAut W), hle x.2⟩ : ↥G₀) ≠ 1 := fun h =>
    hx1 (Subtype.ext (congrArg (fun y : ↥G₀ => (y : MulAut W)) h))
  refine three_dvd_card_of_order_three hx1' (Subtype.ext ?_)
  have := congrArg (fun y : ↥G₁ => (y : MulAut W)) hx3
  simpa using this

theorem three_dvd_card_of_b56Cases {G₀ : Subgroup (MulAut W)}
    (h : B56Case1 G₀ ∨ B56Case2 G₀ ∨ B56Case3 G₀ ∨ B56Case4 G₀ ∨ B56Case5 G₀) :
    3 ∣ Nat.card ↥G₀ := by
  rcases h with h | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, -, -, hf₁, -⟩ |
      ⟨G₁, G₂, t, hJt, -, -, -, hc₂, -⟩ | ⟨G₁, G₂, hsup, -, -, -, ⟨e₁⟩, -⟩
  · have h3 := S153L.three_dvd_card_of_b56QL h.2.2 h.1
    exact h3.trans (Subgroup.card_dvd_of_le (quasithinGenFitting_le G₀))
  · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  · obtain ⟨x, hx1, hx3⟩ := FFC.exists_order_three_of_factorList hf₁
    have hle : G₁ ≤ G₀ := hsup ▸ le_sup_left
    exact three_dvd_card_of_le_of_order_three hle hx1 hx3
  · have hle : G₂ ≤ G₀ := by rw [hJt]; exact le_sup_right.trans le_sup_left
    rw [← hc₂]
    exact Subgroup.card_dvd_of_le hle
  · have hf : B56FactorList ↥G₁ :=
      Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one,
        by rw [Nat.card_zmod, pow_one], ⟨e₁⟩⟩)
    obtain ⟨x, hx1, hx3⟩ := FFC.exists_order_three_of_factorList hf
    have hle : G₁ ≤ G₀ := hsup ▸ le_sup_left
    exact three_dvd_card_of_le_of_order_three hle hx1 hx3

end B56

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_three_comm (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y : G}
    (hyG : y ∈ Gv v) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyc : ∀ l ∈ Lv L v, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (Gv v)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Gv v with hHdef
  have hyp := hH.hyp
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  set O := CFSG.pCore 2 ↥H with hOdef
  have hO2 : IsPGroup 2 ↥O := CFSG.pCore_isPGroup
  have hP : O.map H.subtype = pCoreOf 2 H := by
    rw [hOdef]; rfl
  have hmemO : ∀ z : ↥H, z ∈ O ↔ (z : G) ∈ pCoreOf 2 H := by
    intro z
    rw [← hP]
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
  have hqeq : ∀ a b : ↥H, q a = q b ↔ ((a⁻¹ * b : ↥H) : G) ∈ pCoreOf 2 H := by
    intro a b
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hmemO]
  set yb : ↥H ⧸ O := q ⟨y, hyG⟩ with hyb
  have hyc' : ∀ k (hk : k ∈ Lv L v), q ⟨k, hLvH hk⟩ * yb = yb * q ⟨k, hLvH hk⟩ := by
    intro k hk
    rw [hyb, ← map_mul, ← map_mul, hqeq]
    have hkyN : (k * y)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      le_normalizer_pCoreOf 2 H (H.inv_mem (H.mul_mem (hLvH hk) hyG))
    have h1 := (Subgroup.mem_normalizer_iff.1 hkyN _).1 (hyc k hk)
    have e : ((⟨k, hLvH hk⟩ * ⟨y, hyG⟩ : ↥H)⁻¹ * (⟨y, hyG⟩ * ⟨k, hLvH hk⟩) : ↥H) =
        (k * y)⁻¹ * (y * k * y⁻¹ * k⁻¹) * (k * y)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact h1
  have hzc : ∀ z ∈ Subgroup.zpowers yb, ∀ k (hk : k ∈ Lv L v),
      q ⟨k, hLvH hk⟩ * z = z * q ⟨k, hLvH hk⟩ := by
    intro z hz k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (hyc' k hk) n).eq
  have hyb1 : yb ≠ 1 := by
    intro h1
    have h2 : q ⟨y, hyG⟩ = q 1 := by rw [← hyb, h1, map_one]
    rw [hqeq] at h2
    have h3' : ((⟨y, hyG⟩ : ↥H)⁻¹ * 1 : ↥H) = (⟨y, hyG⟩ : ↥H)⁻¹ := mul_one _
    rw [h3'] at h2
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 H) ⟨_, h2⟩
    have he' : (y⁻¹) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have h4 : y⁻¹ = 1 := Sec1211Kv.eq_one_of_two_three he' (by rw [inv_pow, hy3, inv_one])
    exact hy1 (inv_eq_one.mp h4)
  have hord : orderOf yb = 3 := by
    refine orderOf_eq_prime ?_ hyb1
    rw [hyb, ← map_pow]
    have : (⟨y, hyG⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  obtain ⟨A, hALv, hA, hcA⟩ := exists_nine_Lv h1222 F hH hv hβ
  have hAH : A ≤ H := hALv.trans hLvH
  let α : ↥A →* ↥H ⧸ O := q.comp (Subgroup.inclusion hAH)
  have hαβ : ∀ (a : ↥A) (z : ↥(Subgroup.zpowers yb)),
      Commute (α a) ((Subgroup.zpowers yb).subtype z) := by
    intro a z
    exact hzc z z.2 (a : G) (hALv a.2)
  let Φ := α.noncommCoprod (Subgroup.zpowers yb).subtype hαβ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h1
    simp only [Φ, MonoidHom.noncommCoprod_apply] at h1
    have hαz : α a = ((z : ↥H ⧸ O))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hzinv : ((z : ↥H ⧸ O))⁻¹ ∈ Subgroup.zpowers yb := (Subgroup.zpowers yb).inv_mem z.2
    have hac : ∀ l ∈ Lv L v, ((a : G) * l)⁻¹ * (l * a) ∈ pCoreOf 2 H := by
      intro l hl
      have h2 := hzc _ hzinv l hl
      rw [← hαz] at h2
      have h3 : q (⟨a, hAH a.2⟩ * ⟨l, hLvH hl⟩) = q (⟨l, hLvH hl⟩ * ⟨a, hAH a.2⟩) := by
        rw [map_mul, map_mul]
        exact h2.symm
      rw [hqeq] at h3
      simpa using h3
    have ha1 : (a : G) = 1 :=
      eq_one_of_comm_mem h1222 F hH hv hβ (fun l hl => le_normalizer_pCoreOf 2 H (hLvH hl))
        (pCoreOf_isPGroup 2 H) (hALv a.2) (hA.2 _ a.2) hac
    have ha1' : a = 1 := Subtype.ext ha1
    subst ha1'
    have hz1 : (z : ↥H ⧸ O) = 1 := by
      rw [map_one, one_mul] at h1
      exact h1
    exact Prod.ext rfl (Subtype.ext hz1)
  have hcomm3 : ∀ x y : ↥A × ↥(Subgroup.zpowers yb), x * y = y * x := by
    rintro ⟨a, z⟩ ⟨a', z'⟩
    refine Prod.ext (hA.1.is_comm.comm a a') ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp z.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z'.2
    apply Subtype.ext
    show (z : ↥H ⧸ O) * z' = z' * z
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self yb m n).eq
  have hpow3 : ∀ x : ↥A × ↥(Subgroup.zpowers yb), x ^ 3 = 1 := by
    rintro ⟨a, z⟩
    refine Prod.ext (Subtype.ext (by simpa using hA.2 _ a.2)) ?_
    have hc3 : Nat.card ↥(Subgroup.zpowers yb) = 3 := by rw [Nat.card_zpowers, hord]
    show z ^ 3 = 1
    rw [← hc3]
    exact pow_card_eq_one'
  have h27 : Nat.card (↥A × ↥(Subgroup.zpowers yb)) = 3 ^ 3 := by
    rw [Nat.card_prod, hcA, Nat.card_zpowers, hord]
    norm_num
  have hrk := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm3 hpow3 h27 Φ
    hinj (H := ⊤) le_top
  rw [CFSG.SectionRank.pRank_quotient_eq O hO3] at hrk
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 := hSQ.1 3 Nat.prime_three (by norm_num)
  omega

omit [IsMulCommutative ↥V] in
theorem not_isFFModule_of_three (h56 : AsB56) {W Y : Subgroup G} [IsMulCommutative ↥W]
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hS : SQTKGroup ↥Y) (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (h3 : ¬ 3 ∣ Nat.card ↥Y) :
    ¬ IsFFModule (V := ↥W) (autOn Y W) := by
  intro hFF
  have hV : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW2 w w.2)
  have hJ := InternalSec.ffJ_ne_bot_of_isFFModule hV hFF
  have hB := InternalSec.b53Hyp_ffJ_autOn hYW hS hO2
  have hcases := h56 ↥W hV _ hJ hB
  have h3A : 3 ∣ Nat.card ↥(autOn Y W) :=
    (three_dvd_card_of_b56Cases hcases).trans (Subgroup.card_dvd_of_le (B6.ffJ_le _))
  apply h3
  refine h3A.trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYW).toEquiv]

omit [IsMulCommutative ↥V] in
theorem V_le_normalizer_Lv (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    V ≤ Subgroup.normalizer (Lv L v : Set G) := by
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  intro x hx
  have hxG : x ∈ Gv v := by
    show x ∈ Subgroup.centralizer {v}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨v, hv⟩)
  refine normalizer_le_normalizer_perfectCore _ ?_
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hH.hyp.normalizes (hVT hx), Subgroup.le_normalizer hxG⟩

omit [IsMulCommutative ↥V] in
theorem Vv_le_pCoreOf (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    Vv L V v ≤ pCoreOf 2 (Lv L v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVT, -⟩ := V_facts h1222 hH
  have hVN := V_le_normalizer_Lv h1222 hH hv
  have hle : Vv L V v ≤ Lv L v := by
    rw [Vv, Subgroup.commutator_le]
    intro x hx l hl
    rw [commutatorElement_def]
    exact (Lv L v).mul_mem ((Subgroup.mem_normalizer_iff.1 (hVN hx) l).1 hl) ((Lv L v).inv_mem hl)
  have h2 : IsPGroup 2 ↥(Vv L V v) := by
    refine hH.hyp.sylow.1.to_le ?_
    rw [Vv]
    refine (Subgroup.commutator_le.2 fun x hx l hl => ?_).trans hVT
    have hl' : l ∈ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1 (Lv_le_L L v hl)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hx ((Subgroup.mem_normalizer_iff.1 hl' _).1 (V.inv_mem hx))
  exact le_pCoreOf_of_le_normalizer 2 hle (Lv_le_normalizer_Vv hH v) h2

theorem pair23 : ∀ a b c d : Fin 8, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) → c.val < 4 →
    d.val < 4 → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c ≠ d → (c = 2 ∧ d = 3) ∨ (c = 3 ∧ d = 2) := by
  decide

end S126T2

end CFSG.Quasithin.H13
