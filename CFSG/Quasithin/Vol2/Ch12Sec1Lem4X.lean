module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4R
public import CFSG.Quasithin.Vol2.Ch12Sec1H9FourJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.LieType.BorelTits
  Sec121H9
open scoped IsMulCommutative commutatorElement

namespace Sec1214

variable {G : Type} [Group G]

@[expose] noncomputable def preI {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (B : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  (B.comap (convI hV)).map (Subgroup.normalizer (V : Set G)).subtype

theorem mem_preI {V : Subgroup G} {hV : IsElemAbelian 2 V} {B : Subgroup (MulAut (IntMod V hV))}
    {g : G} : g ∈ preI hV B ↔ ∃ hg : g ∈ Subgroup.normalizer (V : Set G), convI hV ⟨g, hg⟩ ∈ B := by
  constructor
  · rintro ⟨⟨h, hh⟩, hb, rfl⟩
    exact ⟨hh, hb⟩
  · rintro ⟨hg, hb⟩
    exact ⟨⟨g, hg⟩, hb, rfl⟩

theorem oTwoUpper_oTwoUpper (Y : Subgroup G) : oTwoUpper (oTwoUpper Y) = oTwoUpper Y := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem autI_oTwoUpper [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) : autI hV (oTwoUpper Y) = oTwoUpper (autI hV Y) := by
  set N := Subgroup.normalizer (V : Set G)
  have h1 : (oTwoUpper Y).subgroupOf N = oTwoUpper (Y.subgroupOf N) := by
    have h2 := oTwoUpper_map N.subtype (Y.subgroupOf N)
    rw [Subgroup.map_subgroupOf_eq_of_le hY] at h2
    rw [h2]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  rw [autI, h1, autI, oTwoUpper_map]

structure IsXSub (T L V V₁ X : Subgroup G) : Prop where
  le_L : X ≤ L
  le_normalizer : X ≤ Subgroup.normalizer (thompsonJ T : Set G)
  xi : IsXi T X
  relIndex : (pCoreOf 2 X).relIndex X = 9
  sylow : ∃ P : Subgroup G, P ≤ X ∧ IsPGroup 3 P ∧ Nat.card P = 9
  fix : ∀ w ∈ V, (∀ x ∈ X, x * w * x⁻¹ = w) → w = 1
  pCoreOf_le : pCoreOf 2 X ≤ T ⊓ Subgroup.normalizer (V₁ : Set G)
  ker : ∀ t ∈ T, (∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 X) →
    t ∈ Subgroup.normalizer (V₁ : Set G)
  le_V : V ≤ X
  xf : IsXf X
  nonab : ∃ a ∈ T, ∃ b ∈ T, ∃ y ∈ X,
    a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∉ pCoreOf 2 X

namespace Setting

variable [Finite G] {T L V V₁ V₂ T₀ : Subgroup G} {v : G} (c : Setting T L V V₁ V₂ v T₀)
include c

theorem sup_le_normalizer_V : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (Subgroup.le_normalizer.trans (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp))
    c.T_le_normalizer_V

theorem exists_pow_eq_one_of_mem_centralizer {x : G} (hxL : x ∈ L)
    (hxC : x ∈ Subgroup.centralizer (V : Set G)) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc₁, hnat₁⟩ := c.S.ctx.hyp.nat₁
  have h1 : x ∈ pCoreOf 2 L :=
    Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 c.S.ctx.hyp c.S.ctx.V₁_le c.S.ctx.hyp.norm₁
      hnat₁ ⟨hxL, Subgroup.centralizer_le (by exact_mod_cast c.S.ctx.V₁_le) hxC⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨x, h1⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem inf_centralizer_le : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hD
  have h2 : IsPGroup 2 ↥D := by
    rintro ⟨d, hd⟩
    have hdLT : d ∈ ((L ⊔ T : Subgroup G) : Set G) := hd.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T c.S.ctx.hTL] at hdLT
    obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hdLT
    obtain ⟨a, ha⟩ := c.S.ctx.hyp.sylow.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := A4.exists_pow_mul_eq hl (c.S.ctx.hTL ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hl'C : l' ∈ Subgroup.centralizer (V : Set G) := he ▸ (D.pow_mem hd (2 ^ a)).2
    obtain ⟨b, hb⟩ := c.exists_pow_eq_one_of_mem_centralizer hl' hl'C
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, he, hb]
  have hDn : L ⊔ T ≤ Subgroup.normalizer (D : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer c.sup_le_normalizer_V hg⟩
  have hDO : D ≤ pCoreOf 2 (L ⊔ T) := le_pCoreOf_of_le_normalizer 2 inf_le_left hDn h2
  rw [setup121Q_holds G T L V V₁ V₂ 4 c.S.ctx.hyp c.S.ctx.hTL] at hDO
  exact hDO.trans inf_le_left

theorem mem_T_of_convI_mem {g : G} (hg : g ∈ L ⊔ T) (hgN : g ∈ Subgroup.normalizer (V : Set G))
    (hgT : convI c.S.ctx.hVe ⟨g, hgN⟩ ∈ autI c.S.ctx.hVe T) : g ∈ T := by
  obtain ⟨⟨t, htN⟩, ht, he⟩ := (mem_autI c.S.ctx.hVe).1 hgT
  have h1 : convI c.S.ctx.hVe (⟨t, htN⟩⁻¹ * ⟨g, hgN⟩) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have h2 := (convI_eq_one_iff c.S.ctx.hVe _).mp h1
  have h3 : t⁻¹ * g ∈ T := c.inf_centralizer_le
    ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht)) hg, h2⟩
  have := T.mul_mem ht h3
  rwa [mul_inv_cancel_left] at this

theorem exists_isXSub (hJ4 : LemH9J4) : ∃ X : Subgroup G, IsXSub T L V V₁ X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := c.S.ctx.hVe
  have hcV : IsMulCommutative ↥V := hV.1
  have hH9 := h9Hyp_of_hyp121 c.S.ctx.hyp c.S.ctx.hTL hV
  obtain ⟨J, Xb, hoff, hJTL, hJc, hJX, hXL, hXN, hTX, hXo, hXc, hcube, hcomm, hirr, hfix, hfix9,
    hmv, hker, hnab⟩ := hJ4 _ _ _ _ _ _ hH9
  set N := Subgroup.normalizer (V : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer.trans (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp)
  have hTN : T ≤ N := c.T_le_normalizer_V
  set Y := L ⊓ preI hV Xb with hY
  set X := oTwoUpper Y with hX
  have hYL : Y ≤ L := inf_le_left
  have hXY : X ≤ Y := oTwoUpper_le Y
  have hXL' : X ≤ L := hXY.trans hYL
  have hXN' : X ≤ N := hXL'.trans hLN
  have hπX : ∀ {x : G} (hx : x ∈ X), convI hV ⟨x, hXN' hx⟩ ∈ Xb := fun hx =>
    (mem_preI.mp (hXY hx).2).2
  have hconv : ∀ (g : N) (w : IntMod V hV), (convI hV g w).val = g * w.val * (g : G)⁻¹ :=
    fun g w => convI_apply_val hV g w
  have hYb : autI hV Y = Xb := by
    apply le_antisymm
    · rintro _ ⟨⟨y, hyN⟩, hy, rfl⟩
      exact (mem_preI.mp (Subgroup.mem_subgroupOf.mp hy).2).2
    · intro xb hxb
      obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := (mem_autI hV).1 (hXL hxb)
      exact (mem_autI hV).2 ⟨⟨l, hlN⟩, ⟨hl, mem_preI.mpr ⟨hlN, hxb⟩⟩, rfl⟩
  have hXb : autI hV X = Xb := by
    rw [hX, autI_oTwoUpper hV (hYL.trans hLN), hYb, ← hXo]
  have hJ2 : IsPGroup 2 ↥J := IsPGroup.of_card hJc
  have hJT : J ≤ autI hV T := hJTL.trans inf_le_left
  have hJL : J ≤ autI hV L := hJTL.trans inf_le_right
  have hAJ : ∀ A : Subgroup G, IsMaxElemAbelian T A → autI hV A ≤ J := by
    intro A hA
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · rw [(autI_eq_bot_iff hV (hA.1.trans hTN)).mpr hAC]
      exact bot_le
    · exact (hoff _ (offenderImages_isFFStarOffender hV c.S.ctx.V_le_T hTN
        ⟨A, ⟨hA, hAC⟩, rfl⟩)).le
  have hXJ : X ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    intro x hx
    have hxb := hπX hx
    have hle : thompsonJ T ≤ B6.conjSub x⁻¹ (thompsonJ T) := by
      refine iSup₂_le fun A hA => ?_
      have hAx : IsMaxElemAbelian T (B6.conjSub x A) := by
        refine ⟨fun a ha => ?_, B6.isElemAbelian_conjSub hA.2.1 x, fun B hBT hB => ?_⟩
        · rw [B6.mem_conjSub] at ha
          have haT : x⁻¹ * a * x ∈ T := hA.1 ha
          have ha' : a = x * (x⁻¹ * a * x) * x⁻¹ := by group
          have haN : a ∈ N := by
            rw [ha']
            exact N.mul_mem (N.mul_mem (hXN' hx) (hTN haT)) (N.inv_mem (hXN' hx))
          refine c.mem_T_of_convI_mem ?_ haN (hJT ?_)
          · rw [ha']
            exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_left (hXL' hx))
              (Subgroup.mem_sup_right haT)) ((L ⊔ T).inv_mem (Subgroup.mem_sup_left (hXL' hx)))
          · have h1 : convI hV ⟨x⁻¹ * a * x, hTN haT⟩ ∈ J :=
              hAJ A hA ((mem_autI hV).2 ⟨_, ha, rfl⟩)
            have h2 : (⟨a, haN⟩ : N) = ⟨x, hXN' hx⟩ * ⟨x⁻¹ * a * x, hTN haT⟩ * ⟨x, hXN' hx⟩⁻¹ :=
              Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
            rw [h2, map_mul, map_mul, map_inv]
            exact (Subgroup.mem_normalizer_iff.mp (hXN hxb) _).mp h1
        · rw [B6.card_conjSub]
          exact hA.2.2 B hBT hB
      intro a ha
      rw [B6.mem_conjSub, inv_inv]
      have : x * a * x⁻¹ ∈ B6.conjSub x A := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using ha
      exact B6.le_thompsonJ hAx this
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := hle ha
    rw [B6.mem_conjSub, inv_inv] at h1
    exact h1
  set K := X ⊓ preI hV J with hK
  have hπK : ∀ {k : G} (hk : k ∈ K), convI hV ⟨k, hXN' hk.1⟩ ∈ J := fun hk =>
    (mem_preI.mp hk.2).2
  have hK2 : IsPGroup 2 ↥K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := hJ2 ⟨_, hπK hk⟩
    have h1 : convI hV (⟨k, hXN' hk.1⟩ ^ 2 ^ a) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val ha
    have h2 := (convI_eq_one_iff hV _).mp h1
    obtain ⟨b, hb⟩ := c.exists_pow_eq_one_of_mem_centralizer (L.pow_mem (hXL' hk.1) (2 ^ a))
      (by simpa using h2)
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb]
  have hKn : X ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    refine Sec121Swap.mem_normalizer_of_conj_mem fun k hk => ⟨X.mul_mem (X.mul_mem hx hk.1)
      (X.inv_mem hx), mem_preI.mpr ⟨N.mul_mem (N.mul_mem (hXN' hx) (hXN' hk.1))
        (N.inv_mem (hXN' hx)), ?_⟩⟩
    have h2 : (⟨x * k * x⁻¹, N.mul_mem (N.mul_mem (hXN' hx) (hXN' hk.1)) (N.inv_mem (hXN' hx))⟩ :
        N) = ⟨x, hXN' hx⟩ * ⟨k, hXN' hk.1⟩ * ⟨x, hXN' hx⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXN (hπX hx)) _).mp (hπK hk)
  have hKO : K ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 inf_le_left hKn hK2
  have hKX9 : K.relIndex X = 9 := by
    rw [hK, Subgroup.inf_relIndex_left, ← Subgroup.relIndex_subgroupOf hXN', preI,
      Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective,
      Subgroup.relIndex_comap]
    have h1 : (X.subgroupOf N).map (convI hV) = Xb := hXb
    rw [h1]
    have h2 := Subgroup.relIndex_mul_card J Xb
    rw [inf_eq_left.mpr hJX, hXc] at h2
    have h3 : 0 < Nat.card J := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right h3 h2
  have hOK : pCoreOf 2 X = K := by
    refine le_antisymm ?_ hKO
    have h1 := Subgroup.relIndex_mul_relIndex K (pCoreOf 2 X) X hKO (pCoreOf_le 2 X)
    rw [hKX9] at h1
    have h2 : K.relIndex (pCoreOf 2 X) ∣ 9 := ⟨_, h1.symm⟩
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 X).exists_card_eq
    have h3 : K.relIndex (pCoreOf 2 X) ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card K _
    have hcop : Nat.Coprime (2 ^ n) 9 := Nat.Coprime.pow_left n (by norm_num)
    have h4 : K.relIndex (pCoreOf 2 X) = 1 :=
      Nat.eq_one_of_dvd_one (by rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd h3 h2)
    exact Subgroup.relIndex_eq_one.mp h4
  have hmemO : ∀ {x : G} (hx : x ∈ X), convI hV ⟨x, hXN' hx⟩ ∈ J → x ∈ pCoreOf 2 X :=
    fun hx hxJ => hOK ▸ ⟨hx, mem_preI.mpr ⟨hXN' hx, hxJ⟩⟩
  have hNmul : ∀ {a b : G} (ha : a ∈ N) (hb : b ∈ N),
      (⟨a * b, N.mul_mem ha hb⟩ : N) = ⟨a, ha⟩ * ⟨b, hb⟩ := fun _ _ => rfl
  have hNinv : ∀ {a : G} (ha : a ∈ N), (⟨a⁻¹, N.inv_mem ha⟩ : N) = ⟨a, ha⟩⁻¹ := fun _ => rfl
  have hTXG : T ≤ Subgroup.normalizer (X : Set G) := by
    intro t ht
    refine normalizer_le_normalizer_oTwoUpper Y (Sec121Swap.mem_normalizer_of_conj_mem
      fun y hy => ⟨(Subgroup.mem_normalizer_iff.mp (c.S.ctx.hTL ht) _).mp hy.1, ?_⟩)
    obtain ⟨hyN, hyb⟩ := mem_preI.mp hy.2
    refine mem_preI.mpr ⟨N.mul_mem (N.mul_mem (hTN ht) hyN) (N.inv_mem (hTN ht)), ?_⟩
    rw [hNmul (N.mul_mem (hTN ht) hyN) (N.inv_mem (hTN ht)), hNmul (hTN ht) hyN, hNinv (hTN ht),
      map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hTX ((mem_autI hV).2 ⟨_, ht, rfl⟩)) _).mp hyb
  have hO2ne : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    have hV2 : IsPGroup 2 ↥V := fun w => ⟨1, Subtype.ext (by simpa using hV.2 w w.2)⟩
    have h1 : V ≤ pCoreOf 2 (X ⊔ T) := le_pCoreOf_of_le_normalizer 2
      (c.S.ctx.V_le_T.trans le_sup_right) (sup_le hXN' hTN) hV2
    intro hb
    apply Sec121Thm.ne_bot_of_hyp121 c.S.ctx.hyp
    rw [eq_bot_iff, ← hb]
    exact h1
  have hcubeG : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X := by
    intro x hx
    refine hmemO (X.pow_mem hx 3) ?_
    have h1 : (⟨x ^ 3, hXN' (X.pow_mem hx 3)⟩ : N) = ⟨x, hXN' hx⟩ ^ 3 := rfl
    rw [h1, map_pow]
    exact hcube _ (hπX hx)
  have hcommG : ⁅X, X⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ X := X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
    refine hmemO hab ?_
    have h1 : (⟨⁅a, b⁆, hXN' hab⟩ : N) =
        ⟨a, hXN' ha⟩ * ⟨b, hXN' hb⟩ * ⟨a, hXN' ha⟩⁻¹ * ⟨b, hXN' hb⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (hπX ha) _ (hπX hb)
  have hKJ : autI hV K = J := by
    apply le_antisymm
    · rintro _ ⟨⟨k, hkN⟩, hk, rfl⟩
      exact hπK (Subgroup.mem_subgroupOf.mp hk)
    · intro j hj
      rw [← hXb] at hJX
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := (mem_autI hV).1 (hJX hj)
      exact (mem_autI hV).2 ⟨⟨x, hxN⟩, ⟨hx, mem_preI.mpr ⟨hxN, hj⟩⟩, rfl⟩
  have hirrG : ∀ Z : Subgroup G, ⁅X, X⁆ ⊔ pCoreOf 2 X ≤ Z → Z ≤ X →
      T ≤ Subgroup.normalizer (Z : Set G) → Z = ⁅X, X⁆ ⊔ pCoreOf 2 X ∨ Z = X := by
    intro Z hZ1 hZX hTZ
    rw [sup_eq_right.mpr hcommG] at hZ1 ⊢
    have hZN : Z ≤ N := hZX.trans hXN'
    have h1 : J ≤ autI hV Z := hKJ ▸ autI_mono hV (hOK ▸ hZ1)
    have h2 : autI hV Z ≤ Xb := hXb ▸ autI_mono hV hZX
    have h3 : autI hV T ≤ Subgroup.normalizer (autI hV Z : Set (MulAut (IntMod V hV))) := by
      rintro _ ⟨⟨t, htN⟩, ht, rfl⟩
      refine Sec121Swap.mem_normalizer_of_conj_mem fun φ hφ => ?_
      obtain ⟨⟨z, hzN⟩, hz, rfl⟩ := hφ
      have hz' : z ∈ Z := Subgroup.mem_subgroupOf.mp hz
      have htz : t * z * t⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp
        (hTZ (Subgroup.mem_subgroupOf.mp ht)) z).mp hz'
      refine ⟨⟨t * z * t⁻¹, hZN htz⟩, Subgroup.mem_subgroupOf.mpr htz, ?_⟩
      show convI hV (⟨t, htN⟩ * ⟨z, hzN⟩ * ⟨t, htN⟩⁻¹) = _
      rw [map_mul, map_mul, map_inv]
    rcases hirr _ h1 h2 h3 with h | h
    · left
      refine le_antisymm (fun z hz => ?_) hZ1
      refine hmemO (hZX hz) ?_
      rw [← h]
      exact ⟨⟨z, hZN hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    · right
      refine le_antisymm hZX fun x hx => ?_
      have hxZ : convI hV ⟨x, hXN' hx⟩ ∈ autI hV Z := h ▸ hπX hx
      obtain ⟨⟨z, hzN⟩, hz, hzx⟩ := (mem_autI hV).1 hxZ
      have hz' : z ∈ Z := hz
      have h4 : convI hV (⟨z, hzN⟩⁻¹ * ⟨x, hXN' hx⟩) = 1 := by
        rw [map_mul, map_inv, hzx, inv_mul_cancel]
      have h5 : z⁻¹ * x ∈ pCoreOf 2 X := by
        refine hmemO (X.mul_mem (X.inv_mem (hZX hz')) hx) ?_
        have h6 : (⟨z⁻¹ * x, hXN' (X.mul_mem (X.inv_mem (hZX hz')) hx)⟩ : N) =
            ⟨z, hzN⟩⁻¹ * ⟨x, hXN' hx⟩ := rfl
        rw [h6, h4]
        exact J.one_mem
      have := Z.mul_mem hz' (hZ1 h5)
      rwa [mul_inv_cancel_left] at this
  have hidx : (pCoreOf 2 X).relIndex X = 9 := by rw [hOK]; exact hKX9
  have hcardX : Nat.card X = 9 * Nat.card (pCoreOf 2 X) := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 X) X
    rw [inf_eq_left.mpr (pCoreOf_le 2 X), hidx] at h1
    exact h1.symm
  have hsyl : ∃ P : Subgroup G, P ≤ X ∧ IsPGroup 3 P ∧ Nat.card P = 9 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3
      (show 3 ^ 2 ∣ Nat.card X from ⟨Nat.card (pCoreOf 2 X), by rw [hcardX]; norm_num⟩)
    refine ⟨P.map X.subtype, Subgroup.map_subtype_le P, IsPGroup.of_card (n := 2) ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hP]
    · rw [Subgroup.card_map_of_injective X.subtype_injective, hP]
      norm_num
  have hfixG : ∀ w ∈ V, (∀ x ∈ X, x * w * x⁻¹ = w) → w = 1 := by
    intro w hw hwX
    have h1 : IntMod.mk hV ⟨w, hw⟩ ∈ fixV Xb := by
      rw [← hXb]
      rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
      refine IntMod.val_injective ?_
      rw [hconv]
      exact hwX x hx
    rw [hfix, Subgroup.mem_bot] at h1
    exact congrArg IntMod.val h1
  have hOT : pCoreOf 2 X ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
    rw [hOK]
    intro k hk
    exact ⟨c.mem_T_of_convI_mem (Subgroup.mem_sup_left (hXL' hk.1)) (hXN' hk.1) (hJT (hπK hk)),
      c.S.ctx.hyp.norm₁ (hXL' hk.1)⟩
  have hkerG : ∀ t ∈ T, (∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 X) →
      t ∈ Subgroup.normalizer (V₁ : Set G) := by
    intro t ht h
    have h1 : convI hV ⟨t, hTN ht⟩ ∈ J := by
      refine hker _ ((mem_autI hV).2 ⟨_, ht, rfl⟩) fun φ hφ => ?_
      rw [← hXb] at hφ
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hφ
      have hx' : x ∈ X := hx
      have h2 := h x hx'
      rw [hOK] at h2
      have h3 := hπK h2
      have h4 : (⟨t * x * t⁻¹ * x⁻¹, hXN' h2.1⟩ : N) =
          ⟨t, hTN ht⟩ * ⟨x, hxN⟩ * ⟨t, hTN ht⟩⁻¹ * ⟨x, hxN⟩⁻¹ := rfl
      rwa [h4, map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    have hφ : convI hV ⟨t, hTN ht⟩ ∈ autI hV L := hJL h1
    refine Sec121Swap.mem_normalizer_of_conj_mem fun x hx => ?_
    have h2 := hH9.inv₁ hφ (IntMod.mk hV ⟨x, c.S.ctx.V₁_le hx⟩)
    rw [mem_subI, mem_subI, convI_apply_val] at h2
    exact h2.mp hx
  have hV2 : IsPGroup 2 ↥V := fun w => ⟨1, Subtype.ext (by simpa using hV.2 w w.2)⟩
  have hVL : V ≤ L := by
    intro w hw
    rw [Sec1219.eq_commutator_of_hyp121 c.S.ctx.hyp] at hw
    refine (Subgroup.commutator_le.mpr fun a ha b hb => ?_) hw
    have h1 : a * b * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (c.S.ctx.hyp.le ha) b).mp hb
    exact L.mul_mem h1 (L.inv_mem hb)
  have hVN : V ≤ N := c.S.ctx.V_le_T.trans hTN
  have hVY : V ≤ Y := fun w hw => ⟨hVL hw, mem_preI.mpr ⟨hVN hw, by
    rw [(convI_eq_one_iff hV ⟨w, hVN hw⟩).mpr (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      setLike_mul_comm hu hw)]
    exact Xb.one_mem⟩⟩
  have hVnX : V ≤ Subgroup.normalizer (X : Set G) := hVY.trans (le_normalizer_oTwoUpper Y)
  have hVX : V ≤ X := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Pb, hPb⟩ := Sylow.exists_subgroup_card_pow_prime 3
      (show 3 ^ 2 ∣ Nat.card Xb from ⟨Nat.card J, by rw [hXc]; norm_num⟩)
    set P := Pb.map Xb.subtype with hP
    have hPX : P ≤ Xb := Subgroup.map_subtype_le Pb
    have hPc : Nat.card P = 9 := by
      rw [hP, Subgroup.card_map_of_injective Xb.subtype_injective, hPb]
      norm_num
    have hfixP := hfix9 P hPX hPc
    have hcommP : commV P = ⊤ := by
      have h := (coprime_decomp (P := P) (by rw [hPc]; decide) (fun w => IntMod.sq_eq_one w)
        (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).1
      rw [← commV_eq_commSub, top_inf_eq, hfixP, sup_bot_eq] at h
      exact h
    let VX : Subgroup (IntMod V hV) :=
      { carrier := {u | u.val ∈ X}
        mul_mem' := fun ha hb => X.mul_mem ha hb
        one_mem' := X.one_mem
        inv_mem' := fun ha => X.inv_mem ha }
    have hle : commV P ≤ VX := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨φ, hφ, u, rfl⟩
      rw [← hXb] at hPX
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hPX hφ
      have hx' : x ∈ X := hx
      show ((convI hV ⟨x, hxN⟩ u) * u⁻¹).val ∈ X
      rw [IntMod.val_mul, IntMod.val_inv, hconv]
      have h1 : u.val * x⁻¹ * u.val⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hVnX u.val_mem) _).mp (X.inv_mem hx')
      have e : (x : G) * u.val * x⁻¹ * u.val⁻¹ = x * (u.val * x⁻¹ * u.val⁻¹) := by group
      rw [e]
      exact X.mul_mem hx' h1
    intro w hw
    have h1 : IntMod.mk hV ⟨w, hw⟩ ∈ VX := hle (hcommP ▸ Subgroup.mem_top _)
    exact h1
  have hVO : V ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hVX (hXN') hV2
  have hxf : IsXf X := by
    refine ⟨⟨fun hb => Sec121Thm.ne_bot_of_hyp121 c.S.ctx.hyp (eq_bot_iff.mpr (hb ▸ hVX)),
      (oTwoUpper_oTwoUpper Y).symm, fun x hx => ?_⟩, fun hb => ?_⟩
    · have hxC : x ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.centralizer_le (by exact_mod_cast hVO) hx.2
      refine hmemO hx.1 ?_
      rw [(convI_eq_one_iff hV _).mpr hxC]
      exact J.one_mem
    · obtain ⟨wb, hwb, xb, hxb, hne⟩ := hmv
      rw [← hXb] at hxb
      obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hxb
      have hx' : x ∈ X := hx
      have hwO : wb.val ∈ omegaOneCenterOf (pCoreOf 2 X) := by
        refine Subgroup.subset_closure ⟨⟨hVO wb.val_mem, Subgroup.mem_centralizer_iff.mpr
          fun o ho => ?_⟩, by simpa using hV.2 _ wb.val_mem⟩
        rw [hOK] at ho
        have h1 := hwb _ (hπK ho)
        have h2 := congrArg IntMod.val h1
        rw [hconv] at h2
        calc o * wb.val = (o * wb.val * o⁻¹) * o := by group
          _ = wb.val * o := by rw [h2]
      have h3 : ⁅wb.val, x⁆ ∈ VY X := Subgroup.commutator_mem_commutator hwO hx'
      rw [VY, VYR] at hb
      rw [VY, VYR, hb, Subgroup.mem_bot] at h3
      apply hne
      refine IntMod.val_injective ?_
      rw [hconv]
      have h4 : wb.val * x * wb.val⁻¹ * x⁻¹ = 1 := h3
      calc x * wb.val * x⁻¹ = (wb.val * x * wb.val⁻¹ * x⁻¹)⁻¹ * wb.val := by group
        _ = wb.val := by rw [h4, inv_one, one_mul]
  have hnabG : ∃ a ∈ T, ∃ b ∈ T, ∃ y ∈ X,
      a * b * y * (a * b)⁻¹ * (b * a * y * (b * a)⁻¹)⁻¹ ∉ pCoreOf 2 X := by
    obtain ⟨ab, hab, bb, hbb, xb, hxb, hne⟩ := hnab
    obtain ⟨⟨a, haN⟩, ha, rfl⟩ := (mem_autI hV).1 hab
    obtain ⟨⟨b, hbN⟩, hb, rfl⟩ := (mem_autI hV).1 hbb
    rw [← hXb] at hxb
    obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := (mem_autI hV).1 hxb
    have ha' : a ∈ T := ha
    have hb' : b ∈ T := hb
    have hx' : x ∈ X := hx
    refine ⟨a, ha', b, hb', x, hx', fun hmem => hne ?_⟩
    rw [hOK] at hmem
    have h1 := hπK hmem
    have h2 : (⟨a * b * x * (a * b)⁻¹ * (b * a * x * (b * a)⁻¹)⁻¹, hXN' hmem.1⟩ : N) =
        ⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨x, hxN⟩ * (⟨a, haN⟩ * ⟨b, hbN⟩)⁻¹ *
          (⟨b, hbN⟩ * ⟨a, haN⟩ * ⟨x, hxN⟩ * (⟨b, hbN⟩ * ⟨a, haN⟩)⁻¹)⁻¹ := rfl
    rw [h2] at h1
    simpa only [map_mul, map_inv] using h1
  exact ⟨X, ⟨hXL', hXJ, ⟨(oTwoUpper_oTwoUpper Y).symm, hTXG, hO2ne, 3, Nat.prime_three,
    by norm_num, hcubeG, Or.inl (by rw [hidx]; norm_num), hirrG⟩, hidx, hsyl, hfixG, hOT,
    hkerG, hVX, hxf, hnabG⟩⟩

theorem mem_centralizer_of_isXSub (hFF : LemH9FF4) (hA21 : AsA21SQTKSection) (h51 : AsB51)
    {X : Subgroup G} (hX : IsXSub T L V V₁ X) {z : G}
    (hz : z ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)))
    (hzX : z ∈ Subgroup.centralizer (X : Set G)) : z ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨w, hw, y, hy, rfl⟩ := c.exists_mul_of_mem_omegaOneCenterOf hFF hA21 h51 hz
  have hw1 : w = 1 := hX.fix w hw fun x hx => by
    have h1 : x * (w * y) = w * y * x := Subgroup.mem_centralizer_iff.mp hzX x hx
    have h2 : x * y = y * x := Subgroup.mem_centralizer_iff.mp hy x (hX.le_L hx)
    calc x * w * x⁻¹ = x * (w * y) * y⁻¹ * x⁻¹ := by group
      _ = w * (y * x) * y⁻¹ * x⁻¹ := by rw [h1]; group
      _ = w * (x * y) * y⁻¹ * x⁻¹ := by rw [h2]
      _ = w := by group
  rw [hw1, one_mul]
  exact hy

end Setting

end Sec1214

end CFSG.Quasithin.H13
