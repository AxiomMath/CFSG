module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Lv
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

@[expose] def Lem1216CompInsp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G), CFSG.IsQuasisimple ↥K →
    Lemma115Cases K z →
    ∀ (v y : G) (A B S : Subgroup G), v ∈ Subgroup.centralizer (K : Set G) → v ≠ 1 → v ∈ A →
      IsElemAbelian 2 (A ⊔ B) → A ⊓ B = ⊥ → 2 ^ 4 ≤ Nat.card A → 2 ^ 3 ≤ Nat.card B →
      (∀ x ∈ A ⊔ B, x ∈ Subgroup.centralizer (K : Set G) → x ∈ Subgroup.zpowers v) →
      IsSylowTwoOf S K → A ⊔ B ≤ S → S ≤ Subgroup.normalizer (A : Set G) →
      S ≤ Subgroup.normalizer (B : Set G) → y ∈ K → orderOf y = 7 →
      y ∈ Subgroup.normalizer (A : Set G) → False

@[expose] def LemCompG24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .G2 2 2 →
    ∀ S E : Subgroup X, IsSylowTwoOf S ⊤ → E ≠ ⊥ → E ≤ S →
      S ≤ Subgroup.normalizer (E : Set X) → ¬ 7 ∣ Nat.card (Subgroup.normalizer (E : Set X))

namespace Sec1216Lv

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hN : X ≤ Subgroup.normalizer (Y : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hXY x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h2 : x * y * x⁻¹ = y := mul_left_cancel (a := x) (by rw [hXY x hx _ hy]; group)
      exact h2 ▸ hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X Y hN] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  exact ⟨x, hx, y, hy, rfl⟩

theorem cComp_of_isComponentIn [Finite G] {K H : Subgroup G} (hK : IsComponentIn K H) :
    K ∈ cComp H := by
  have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
  rwa [Subgroup.map_subgroupOf_eq_of_le hK.1] at h2

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {v : G} (S : Setting T L V V₁ V₂ n v)
include S

theorem comm_V₁_V {a x : G} (ha : a ∈ V₁) (hx : x ∈ V) : a * x = x * a :=
  S.ctx.comm (S.ctx.V₁_le ha) hx

theorem card_U₂ : 2 * Nat.card S.ctx.U₂ = 2 ^ n := by
  have := S.ctx.hVe.1
  obtain ⟨-, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 S.ctx.hyp
  obtain ⟨K, hKV, hK, hcard⟩ := Sec1212.exists_ker (X := V₂) (fun c => KGH91.pairing S.C₁ S.C₂ v c)
    (fun a ha b hb => S.ctx.hβ.2.1 v S.ctx.v_mem_V₁ a ha b hb)
  have hKU : K = S.ctx.U₂ := by
    ext c
    constructor
    · intro hc
      exact ⟨hKV hc, (hK c (hKV hc)).mp hc⟩
    · intro hc
      exact (hK c hc.1).mpr hc.2
  obtain ⟨c, hc, hvc⟩ := S.ctx.hβ.2.2.1 v S.ctx.v_mem_V₁ S.ctx.v_ne_one
  rw [← hKU, hcard c hc (by show KGH91.pairing S.C₁ S.C₂ v c ≠ 0; rw [hvc]; exact one_ne_zero),
    hcard₂]

theorem eight_le_card_U₂ : 2 ^ 3 ≤ Nat.card S.ctx.U₂ := by
  have h := S.card_U₂
  have h4 : 2 ^ 4 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) (by rcases S.rank with h | h <;> omega)
  omega

theorem sixteen_le_card_V₁ : 2 ^ 4 ≤ Nat.card V₁ := by
  have := S.ctx.hVe.1
  obtain ⟨hcard₁, -, -⟩ := Sec1212.card_eq_of_hyp121 S.ctx.hyp
  rw [hcard₁]
  exact Nat.pow_le_pow_right (by norm_num) (by rcases S.rank with h | h <;> omega)

theorem pairing_eq_zero {c : G} (hc : c ∈ V₂)
    (hcT : ∀ t ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), t * c * t⁻¹ = c) :
    KGH91.pairing S.C₁ S.C₂ v c = 0 := by
  have := S.ctx.hVe.1
  by_cases hc1 : c = 1
  · rw [hc1]
    exact S.ctx.β_one_right S.ctx.v_mem_V₁
  obtain ⟨K, hKV, hK, hcard⟩ := Sec1212.exists_ker (X := V₁)
    (fun a => KGH91.pairing S.C₁ S.C₂ a c) (fun a ha b hb => S.ctx.hβ.1 a ha b hb c hc)
  obtain ⟨a₀, ha₀, ha₀c⟩ := S.ctx.hβ.2.2.2.1 c hc hc1
  have h2K := hcard a₀ ha₀ (by
    show KGH91.pairing S.C₁ S.C₂ a₀ c ≠ 0
    rw [ha₀c]
    exact one_ne_zero)
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2K
    have := S.sixteen_le_card_V₁
    omega
  have hT₁2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    S.ctx.hyp.sylow.1.to_le inf_le_left
  have hKT : K ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) :=
    hKV.trans (S.ctx.V₁_le.trans S.ctx.V_le_T₁)
  have hTK : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have haV : a ∈ V₁ := hKV ha
    have htaV : t * a * t⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp ht.2 a).mp haV
    refine (hK _ htaV).mpr ?_
    have h1 := S.ctx.β_conj (S.ctx.T₁_le_NL ht) ht.2 haV hc
    rw [hcT t ht] at h1
    show KGH91.pairing S.C₁ S.C₂ (t * a * t⁻¹) c = 0
    rw [h1]
    exact (hK a haV).mp ha
  obtain ⟨a, haK, ha1, haC⟩ := Sec1215.exists_ne_one_mem_centralizer hT₁2 hKT hTK hK1
  have hav : a ∈ Subgroup.zpowers v := by
    rw [← S.ctx.hv]
    exact ⟨hKV haK, haC⟩
  rcases S.ctx.mem_zpowers_iff.mp hav with h | h
  · exact absurd h ha1
  · have h1 := (hK a (hKV haK)).mp haK
    rwa [h] at h1

theorem mem_sup_U₂ {z : G} (hz : z ∈ V)
    (hzT : ∀ t ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), t * z * t⁻¹ = z) :
    z ∈ V₁ ⊔ S.ctx.U₂ := by
  have hz' : z ∈ V₁ ⊔ V₂ := by
    rw [S.ctx.hyp.sup]
    exact hz
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup
    (fun a ha c hc => S.comm_V₁_V ha (S.ctx.V₂_le hc)) hz'
  have hcT : ∀ t ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), t * c * t⁻¹ = c := by
    intro t ht
    have h1 : (t * a * t⁻¹) * (t * c * t⁻¹) = a * c := by
      rw [← hzT t ht]
      group
    exact (Sec1212.decomp_unique S.ctx.hyp.inf
      ((Subgroup.mem_normalizer_iff.mp ht.2 a).mp ha)
      (S.ctx.conj_V₂ (S.ctx.T₁_le_NL ht) ht.2 hc) ha hc h1).2
  exact Subgroup.mul_mem_sup ha ⟨hc, S.pairing_eq_zero hc hcT⟩

theorem mem_zpowers_of_mem_sup {x : G} (hx : x ∈ V₁ ⊔ S.ctx.U₂)
    (hxl : ∀ l ∈ Sec1216Lv.lv L v, l * x * l⁻¹ = x) : x ∈ Subgroup.zpowers v := by
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup
    (fun a ha c hc => S.comm_V₁_V ha (S.ctx.U₂_le_V hc)) hx
  have hfix : ∀ l ∈ Sec1216Lv.lv L v, l * a * l⁻¹ = a ∧ l * c * l⁻¹ = c := by
    intro l hl
    have h1 : (l * a * l⁻¹) * (l * c * l⁻¹) = a * c := by
      rw [← hxl l hl]
      group
    exact Sec1212.decomp_unique S.ctx.hyp.inf
      ((Subgroup.mem_normalizer_iff.mp (S.ctx.hyp.norm₁ (lv_le_L L v hl)) a).mp ha)
      (S.lv_conj_mem_U₂ hl hc).1 ha hc.1 h1
  have hc1 : c = 1 := S.eq_one_of_fixed hc fun l hl => (hfix l hl).2
  rw [hc1, mul_one]
  exact S.mem_zpowers_of_fixed ha fun l hl => (hfix l hl).1

end Setting

end Sec1216Lv

open Sec1216Lv

theorem lem1216Comp_of (hlist : Lemma115_3_List) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hinsp : Lem1216CompInsp) : Lem1216Comp := by
  intro G _ _ T L V V₁ V₂ n hyp hTL v hv hSyl _ K hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hyp.simple
  obtain ⟨C₁, C₂, hd⟩ := KGH91.exists_dualCoord hyp
  obtain ⟨S⟩ : Nonempty (Setting T L V V₁ V₂ n v) :=
    ⟨⟨C₁, C₂, hd, ⟨hyp, hTL, KGH91.isDualPairing C₁ C₂ hd, hv⟩⟩⟩
  have hqtke : QTKECore G := qtkeCore_of_cat hyp.nonabelian hyp.qtke
  set H := Subgroup.centralizer ({v} : Set G) with hH
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  have hT : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hyp.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hyp.sylow.2
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := by
    obtain ⟨hn, -⟩ := hyp.reduced
    exact hTL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hyp.le).mp hn)
  have hV1 : V ≠ ⊥ := fun h => S.ctx.v_ne_one (Subgroup.mem_bot.mp (h ▸ S.ctx.v_mem_V))
  obtain ⟨z, hzV, hz1, hzc⟩ :=
    Sec1215.exists_ne_one_mem_centralizer hyp.sylow.1 S.ctx.V_le_T hTV hV1
  have hz2 : z ^ 2 = 1 := S.ctx.hVe.2 z hzV
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzU : z ∈ V₁ ⊔ S.ctx.U₂ := S.mem_sup_U₂ hzV fun t ht => by
    rw [Subgroup.mem_centralizer_iff.mp hzc t ht.1, mul_inv_cancel_right]
  obtain ⟨M', hM', hCM'⟩ := exists_maxTwoLocal_ge (I4.isTwoLocal_centralizer hzo)
  have hB : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.ctx.orderOf_v, pow_one])
  have hB1 : Subgroup.zpowers v ≠ ⊥ := by
    intro h
    have : v ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers v
    exact S.ctx.v_ne_one (Subgroup.mem_bot.mp this)
  have hBH : Subgroup.zpowers v ⊔ Subgroup.centralizer (Subgroup.zpowers v : Set G) ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · intro g hg
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hg v (Subgroup.mem_zpowers v)).symm
  have hHB : H ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) :=
    S.ctx.centralizer_eq_normalizer.ge
  have h115 := lemma116 hyp.qtke.2.1 hB hB1 hBH hHB hSyl hT inf_le_left
    (S.ctx.V_le_T hzV) hzc hz1 hz2 hM' hCM'
  obtain ⟨-, hKz, -, hcases⟩ :=
    Lemma115_3_List.component_cases hlist hyp.simple hyp.nonabelian hqtke h115 hK
  have hpc : pCoreOf 2 H ≠ ⊥ := fun h => hB1 (le_bot_iff.mp (S.ctx.zpowers_le_Qv.trans h.le))
  have hlvH : lv L v ≤ H := lv_le_centralizer L v
  obtain ⟨Kv, ⟨hKv, hlvKv⟩, -⟩ := Vol2Native.lemma_1_2_4_existsUnique hqtke.1 h37 h39 hpc hSyl
    hlvH S.mem_lFamily
  have hK' : K ∈ cComp H := Sec1216Lv.cComp_of_isComponentIn hK
  have hUlv : V₁ ⊔ S.ctx.U₂ ≤ lv L v := sup_le S.V₁_le_lv S.U₂_le_lv
  have hKKv : K = Kv := by
    by_contra hne
    have h1 := (Vol2Native.lemma_1_2_1_two hqtke.1 h37 hpc hK' hKv hne).1
    have hzKv : Subgroup.zpowers z ≤ Kv := by
      rw [Subgroup.zpowers_le]
      exact hlvKv (hUlv hzU)
    have h2 : K ≤ pCoreOf 2 K := by
      calc K = ⁅K, Subgroup.zpowers z⁆ := hKz.symm
        _ ≤ ⁅K, Kv⁆ := Subgroup.commutator_mono le_rfl hzKv
        _ ≤ pCoreOf 2 K := h1.trans inf_le_left
    exact ne_bot_of_mem_cComp hK' (Sec1216Lv.eq_bot_of_perfect_two (perfect_of_mem_cComp hK')
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le h2))
  subst hKKv
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hKH : K ≤ H := hK.1
  have hvK : v ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKH hk)
  obtain ⟨y, hylv, hy7⟩ := S.exists_orderOf_seven
  have hUT : V₁ ⊔ S.ctx.U₂ ≤ T₁ := sup_le (S.ctx.V₁_le.trans S.ctx.V_le_T₁)
    (S.ctx.U₂_le_V.trans S.ctx.V_le_T₁)
  refine hinsp G K z hq hcases v y V₁ S.ctx.U₂ (T₁ ⊓ K) hvK S.ctx.v_ne_one S.ctx.v_mem_V₁
    (Sec1216Gen.isElemAbelian_of_le S.ctx.hVe (sup_le S.ctx.V₁_le S.ctx.U₂_le_V))
    (le_bot_iff.mp ((inf_le_inf_left V₁ S.ctx.U₂_le).trans S.ctx.hyp.inf.le)) S.sixteen_le_card_V₁
    S.eight_le_card_U₂ (fun x hx hxK => S.mem_zpowers_of_mem_sup hx fun l hl => ?_)
    (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK') hSyl)
    (le_inf hUT (hUlv.trans hlvKv)) (inf_le_left.trans inf_le_right)
    (fun t ht => Sec121Swap.mem_normalizer_of_conj_mem fun c hc => S.T₁_conj_mem_U₂ ht.1 hc)
    (hlvKv hylv) hy7 (S.ctx.hyp.norm₁ (lv_le_L L v hylv))
  rw [Subgroup.mem_centralizer_iff.mp hxK l (hlvKv hl), mul_inv_cancel_right]

end CFSG.Quasithin.H13
