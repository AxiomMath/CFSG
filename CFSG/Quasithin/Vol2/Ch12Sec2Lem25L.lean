module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25G
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {A : Subgroup G} {w : G}
    (h : ∀ a ∈ A, w * a * w⁻¹ ∈ A) : w ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hle : A.map (MulAut.conj w).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have hcard : Nat.card (A.map (MulAut.conj w).toMonoidHom) = Nat.card A :=
    (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).toEquiv).symm
  have heq : A.map (MulAut.conj w).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [← heq] at hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
  have hax' : a = x := by
    have : w * a * w⁻¹ = w * x * w⁻¹ := by simpa [MulAut.conj_apply] using hax
    calc a = w⁻¹ * (w * a * w⁻¹) * w := by group
      _ = w⁻¹ * (w * x * w⁻¹) * w := by rw [this]
      _ = x := by group
  rw [← hax']
  exact ha

theorem exists_hyp_rep [Finite G] {L V A : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hsq : ∀ v ∈ V, v ^ 2 = 1)
    (htop : autOn L V = ⊤)
    (hCL : ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) → ∃ k : ℕ, l ^ 2 ^ k = 1)
    (hAV : A ≤ V) {m : ℕ} (hA : Nat.card A = 2 ^ m) (hm : 3 ≤ m)
    (hidx : (A.subgroupOf V).index = 2) :
    ∃ (Q : Type) (_ : Group Q) (ρ : ↥(oTwoUpper (L ⊓ Subgroup.normalizer (A : Set G))) →* Q),
      Function.Surjective ρ ∧
      ρ.ker = CFSG.pCore 2 ↥(oTwoUpper (L ⊓ Subgroup.normalizer (A : Set G))) ∧
      (∀ y, ρ y = 1 ↔ (y : G) ∈ Subgroup.centralizer (A : Set G)) ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := zmodModuleOf hsq
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  set X := L ⊓ Subgroup.normalizer (A : Set G) with hXdef
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hLV
  set W := subOf (V := V) A with hW
  have hdimW : Module.finrank (ZMod 2) W = m := finrank_subOf hAV hA
  obtain ⟨eQ⟩ := nonempty_linearEquiv_mulEquiv_sl hdimW
  obtain ⟨hsimp, a₀, b₀, hab₀⟩ := isSimpleGroup_sl_zmod_two (m := m) hm
  have : IsSimpleGroup (W ≃ₗ[ZMod 2] W) := eQ.isSimpleGroup
  have : Finite (W ≃ₗ[ZMod 2] W) := Finite.of_equiv _ eQ.symm.toEquiv
  have hnabQ : ∃ a b : W ≃ₗ[ZMod 2] W, a * b ≠ b * a :=
    ⟨eQ.symm a₀, eQ.symm b₀, fun h' => hab₀ (by simpa using congrArg eQ h')⟩
  let σ : ↥X →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    linHom.comp ((conjAct V).comp (Subgroup.inclusion hXV))
  have hσ : ∀ (x : ↥X) (v : Additive ↥V), ((Additive.toMul (σ x v) : ↥V) : G) =
      (x : G) * ((Additive.toMul v : ↥V) : G) * (x : G)⁻¹ := fun x v => rfl
  have hσle : ∀ x : ↥X, W.map (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) ≤ W := by
    rintro x _ ⟨w, hw, rfl⟩
    have hw' : ((w.toMul : ↥V) : G) ∈ A := mem_subOf.1 hw
    show (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w ∈ subOf (V := V) A
    rw [mem_subOf, show ((σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w) = σ x w from rfl, hσ]
    exact (Subgroup.mem_normalizer_iff.1 x.2.2 _).1 hw'
  have hσW : ∀ x : ↥X, W.map (σ x : Additive ↥V →ₗ[ZMod 2] Additive ↥V) = W := by
    intro x
    refine le_antisymm (hσle x) fun w hw => ?_
    refine ⟨σ x⁻¹ w, hσle x⁻¹ ⟨w, hw, rfl⟩, ?_⟩
    show σ x (σ x⁻¹ w) = w
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  let ρX : ↥X →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun x => (σ x).ofSubmodules W W (hσW x)
      map_one' := by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        simp [LinearEquiv.ofSubmodules_apply, map_one]
      map_mul' := fun x y => by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        simp [LinearEquiv.ofSubmodules_apply, map_mul] }
  have hρX : ∀ (x : ↥X) (w : W), ((ρX x w : W) : Additive ↥V) = σ x w := fun x w => rfl
  have hρXsurj : Function.Surjective ρX := by
    intro τ
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
    let β : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V :=
      ((Submodule.prodEquivOfIsCompl W C hC).symm.trans
        (τ.prodCongr (LinearEquiv.refl (ZMod 2) C))).trans
        (Submodule.prodEquivOfIsCompl W C hC)
    have hβW : ∀ w : W, β w = τ w := fun w => by
      have h1 : (Submodule.prodEquivOfIsCompl W C hC).symm w = (w, 0) :=
        Submodule.prodEquivOfIsCompl_symm_apply_left W C hC w
      simp only [β, LinearEquiv.trans_apply, h1]
      simp [Submodule.coe_prodEquivOfIsCompl']
    have hαL : mulAutOfLin β ∈ autOn L V := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
    have hconj : ∀ v : ↥V, l * (v : G) * l⁻¹ =
        ((Additive.toMul (β (Additive.ofMul v)) : ↥V) : G) := fun v => by
      rw [← mulAutOfLin_apply, ← hlα]
      rfl
    have hlA : l ∈ Subgroup.normalizer (A : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro a ha
      have hw : Additive.ofMul (⟨a, hAV ha⟩ : ↥V) ∈ W := mem_subOf.2 ha
      rw [hconj ⟨a, hAV ha⟩, show Additive.ofMul (⟨a, hAV ha⟩ : ↥V) =
        ((⟨_, hw⟩ : W) : Additive ↥V) from rfl, hβW ⟨_, hw⟩]
      exact mem_subOf.1 (τ ⟨_, hw⟩).2
    refine ⟨⟨l, Subgroup.mem_subgroupOf.1 hlL, hlA⟩, ?_⟩
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hρX, ← hβW w]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    exact hconj (Additive.toMul (w : Additive ↥V))
  have hρXone : ∀ x : ↥X, ρX x = 1 ↔ (x : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hw : Additive.ofMul (⟨a, hAV ha⟩ : ↥V) ∈ W := mem_subOf.2 ha
      have h1 := LinearEquiv.congr_fun hx ⟨_, hw⟩
      have h2 := congrArg (fun z : W => (((z : Additive ↥V).toMul : ↥V) : G)) h1
      simp only [LinearEquiv.coe_one, id_eq] at h2
      change ((Additive.toMul (σ x (Additive.ofMul (⟨a, hAV ha⟩ : ↥V))) : ↥V) : G) = a at h2
      rw [hσ] at h2
      change (x : G) * a * (x : G)⁻¹ = a at h2
      calc a * (x : G) = ((x : G) * a * (x : G)⁻¹) * x := by rw [h2]
        _ = x * a := by group
    · intro hx
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hρX, LinearEquiv.coe_one, id_eq]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hσ]
      have hwA : (((w : Additive ↥V).toMul : ↥V) : G) ∈ A := mem_subOf.1 w.2
      rw [← Subgroup.mem_centralizer_iff.mp hx _ hwA, mul_inv_cancel_right]
  have hkerX : ∀ x : ↥X, ρX x = 1 → ∃ k : ℕ, (x : G) ^ 2 ^ k = 1 := by
    intro x hx
    have hxA := (hρXone x).1 hx
    have hx2 : (x : G) ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      set d := (x : G) * v * (x : G)⁻¹ * v⁻¹ with hddef
      have hd : d ∈ A := comm_mem_of_index_two hidx (hXV x.2) x.2.2 hv
      have hdV : d ∈ V := hAV hd
      have hxd : (x : G) * d * (x : G)⁻¹ = d := by
        rw [(Subgroup.mem_centralizer_iff.mp hxA d hd).symm, mul_inv_cancel_right]
      have e2 : (x : G) * v * (x : G)⁻¹ = d * v := by rw [hddef]; group
      have hd2 : d * d = 1 := by rw [← pow_two]; exact hsq d hdV
      have e4 : (x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹ = v := by
        have e5 : (x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹ =
            (x : G) * ((x : G) * v * (x : G)⁻¹) * (x : G)⁻¹ := by rw [pow_two]; group
        rw [e5, e2, show (x : G) * (d * v) * (x : G)⁻¹ =
          ((x : G) * d * (x : G)⁻¹) * ((x : G) * v * (x : G)⁻¹) by group, hxd, e2,
          ← mul_assoc, hd2, one_mul]
      calc v * (x : G) ^ 2 = ((x : G) ^ 2 * v * ((x : G) ^ 2)⁻¹) * (x : G) ^ 2 := by rw [e4]
        _ = (x : G) ^ 2 * v := inv_mul_cancel_right _ _
    obtain ⟨k, hk⟩ := hCL _ (L.pow_mem x.2.1 2) hx2
    exact ⟨k + 1, by rw [pow_succ', pow_mul]; exact hk⟩
  set Y := oTwoUpper X with hYdef
  have hYX : Y ≤ X := oTwoUpper_le X
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_oTwoUpper X
  let ρ : ↥Y →* (W ≃ₗ[ZMod 2] W) := ρX.comp (Subgroup.inclusion hYX)
  have hρsurj : Function.Surjective ρ := by
    have hnorm : ρ.range.Normal := by
      refine ⟨fun a ha g => ?_⟩
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 ha
      obtain ⟨x, rfl⟩ := hρXsurj g
      have hy : (x : G) * (y : G) * (x : G)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hXY x.2) _).1 y.2
      refine MonoidHom.mem_range.2 ⟨⟨_, hy⟩, ?_⟩
      show ρX (Subgroup.inclusion hYX ⟨_, hy⟩) =
        ρX x * ρX (Subgroup.inclusion hYX y) * (ρX x)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.range with hb | ht
    · exfalso
      apply not_isPGroup_of_isSimpleGroup hnabQ (p := 2)
      intro τ
      obtain ⟨x, rfl⟩ := hρXsurj τ
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X x.2
      refine ⟨k, ?_⟩
      have h1 : ρ ⟨_, hk⟩ ∈ ρ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      rw [← map_pow, ← h1]
      show ρX _ = ρX _
      congr 1
    · exact MonoidHom.range_eq_top.1 ht
  have hker : ρ.ker = CFSG.pCore 2 ↥Y := by
    apply le_antisymm
    · have hp : IsPGroup 2 ρ.ker := by
        intro y
        have hy1 : ρ (y : ↥Y) = 1 := MonoidHom.mem_ker.1 y.2
        obtain ⟨k, hk⟩ := hkerX _ hy1
        refine ⟨k, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simpa using hk
      exact LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ρ) hp
    · have hm' : ((CFSG.pCore 2 ↥Y).map ρ).Normal :=
        Subgroup.Normal.map CFSG.pCore_normal ρ hρsurj
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥Y).map ρ) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map ρ
      exact (Subgroup.map_eq_bot_iff _).1 (eq_bot_of_normal_of_isPGroup hnabQ _ hp)
  exact ⟨_, inferInstance, ρ, hρsurj, hker, fun y => hρXone _, ⟨eQ⟩⟩

theorem le_normalizer_Y (h1222 : Stmt12_2_2) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) :
    T ≤ Subgroup.normalizer
      ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
        Set G) := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hHs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hHU, -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  intro t ht
  have htA : t ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHU (hHs.1.1 ht), hTV ht⟩
  apply normalizer_le_normalizer_oTwoUpper
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hH.normalizes ht, Subgroup.le_normalizer htA⟩

theorem inf_V_eq (h1222 : Stmt12_2_2) [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) :
    (T ⊓ Subgroup.centralizer (U : Set G)) ⊓ V = U ⊓ V := by
  classical
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, hn, hVn, -, -, -, -, -, -, -, -, -, -, -, -, hUe, -, -, hidx, ⟨hcommV, htv⟩,
    -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  apply le_antisymm
  · rintro v ⟨⟨-, hvU⟩, hv⟩
    by_contra hvA
    have : IsMulCommutative ↥V := hcommV
    have hV2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hVe.2 w w.2)
    set W := (U ⊓ V).subgroupOf V with hWdef
    have hidx' : W.index = 2 := hidx
    have hWne : W ≠ ⊥ := by
      intro hbot
      have h1 := W.card_mul_index
      rw [hidx', hbot, Subgroup.card_bot] at h1
      have h2 : Nat.card ↥V = 2 ^ n := hVn
      rw [h2] at h1
      rcases hn with rfl | rfl | rfl <;> norm_num at h1
    obtain ⟨⟨a, haW⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Lem24.transvAxis_ne_bot hV2 hidx' haW ha1')
    have hcU : c ∈ autOn U V := htv ▸ hc
    obtain ⟨x, hxU, hxc⟩ := hcU
    have hxU' : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hxU
    have hcv : c ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [← hxc]
      apply Subtype.ext
      change (x : G) * v * (x : G)⁻¹ = v
      rw [Subgroup.mem_centralizer_iff.mp hvU x hxU', mul_inv_cancel_right]
    apply hc1
    apply Subtype.ext
    ext w
    change ((c w : ↥V) : G) = (w : G)
    by_cases hw : w ∈ W
    · rw [hc.1 w hw]
    · have hvW : (⟨v, hv⟩ : ↥V) ∉ W := fun h' => hvA ⟨(Subgroup.mem_subgroupOf.mp h').1, hv⟩
      have hwv : w * (⟨v, hv⟩ : ↥V)⁻¹ ∈ W := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx', inv_mem_iff]
        exact ⟨fun h' => absurd h' hw, fun h' => absurd h' hvW⟩
      have e1 : w = (w * (⟨v, hv⟩ : ↥V)⁻¹) * ⟨v, hv⟩ := by group
      rw [e1, map_mul, hc.1 _ hwv, hcv]
  · rintro v ⟨hvU, hvV⟩
    exact ⟨⟨hVT hvV, Subgroup.mem_centralizer_iff.mpr fun u hu => (hUab v hvU u hu).symm⟩, hvV⟩

theorem V_le_L' [Finite G] {T L V : Subgroup G} (hH : Hyp1223 G T L V) : V ≤ L := by
  rw [← commutator_eq_of_hyp1223 hH, Subgroup.commutator_le]
  intro v hv l hl
  rw [commutatorElement_def]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hH.normalizes (S125.le_of_hyp1223 hH hv))
    l).mp hl) (L.inv_mem hl)

theorem card_inf_V [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hC : Config12_2_24 T L V H P U I h n p) : Nat.card ↥(U ⊓ V) = 2 ^ (n - 1) := by
  obtain ⟨-, -, hn, hVn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -⟩ := hC
  have h1 := Subgroup.relIndex_mul_card (U ⊓ V) V
  rw [hidx, inf_assoc, inf_idem, hVn] at h1
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    rcases hn with rfl | rfl | rfl <;> rfl
  omega

theorem exists_Y_rep
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    ∃ (Q : Type) (_ : Group Q)
      (ρ : ↥(oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G))) →* Q),
      Function.Surjective ρ ∧
      ρ.ker = CFSG.pCore 2 ↥(oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) :
        Set G))) ∧
      (∀ y, ρ y = 1 ↔ (y : G) ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G)) ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := card_inf_V hC
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, hn, hVn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, ⟨hcommV, -⟩,
    -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl | rfl <;> omega
  obtain ⟨e⟩ := Lem24.nonempty_coords hVab hVe.2 hVn
  have hCLV := Lem24.centralizer_le_pCoreOf hH hred (by omega) e htop
  have : IsMulCommutative ↥V := hcommV
  refine exists_hyp_rep hLV hVe.2 htop (fun l hl hlV => ?_) inf_le_right hA (by omega) hidx
  have hlO := hCLV ⟨hl, hlV⟩
  obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨l, hlO⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem Y_mem_lFamily
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ∈ lFamily T := by
  obtain ⟨Q, _, ρ, hsurj, hker, -, ⟨eQ⟩⟩ := exists_Y_rep h1222 h1220 hH hNE hC hn3
  have hn4 : 4 ≤ n := by
    obtain ⟨-, -, hn, -⟩ := hC
    rcases hn with rfl | rfl | rfl <;> omega
  have e := ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)).trans eQ
  rw [lFamily, Set.mem_ofPred_eq]
  refine mem_cComp_of_quasisimple_quotient (oTwoUpper_eq_top_of_isPGroup _)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl_zmod_two (by omega)).1)
    (A3.subnormal_of_normal le_sup_left ?_)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer (le_normalizer_Y h1222 hH hC)

theorem conj_eq_of_odd {x q d : G} (hd : x * q * x⁻¹ = d * q) (hxd : x * d * x⁻¹ = d)
    (hd2 : ∃ k : ℕ, d ^ 2 ^ k = 1) (hx : Odd (orderOf x)) : x * q * x⁻¹ = q := by
  have hpow : ∀ j : ℕ, x ^ j * q * (x ^ j)⁻¹ = d ^ j * q := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hxdj : x * d ^ j * x⁻¹ = d ^ j := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hxd]
      calc x ^ (j + 1) * q * (x ^ (j + 1))⁻¹ = x * (x ^ j * q * (x ^ j)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * (d ^ j * q) * x⁻¹ := by rw [ih]
        _ = (x * d ^ j * x⁻¹) * (x * q * x⁻¹) := by group
        _ = d ^ (j + 1) * q := by rw [hxdj, hd, pow_succ, mul_assoc]
  have h1 := hpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h2 : d ^ orderOf x = 1 := by
    have := congrArg (· * q⁻¹) h1
    simpa using this.symm
  obtain ⟨k, hk⟩ := hd2
  have h3 : orderOf d ∣ Nat.gcd (2 ^ k) (orderOf x) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.gcd (2 ^ k) (orderOf x) = 1 :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hx)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  rw [hd, h3, one_mul]

theorem pCoreOf_Y_le
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G))) ≤
      (T ⊓ Subgroup.centralizer (U : Set G)) ⊔ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, _, ρ, -, hker, hρ1, -⟩ := exists_Y_rep h1222 h1220 hH hNE hC hn3
  have hTY := le_normalizer_Y h1222 hH hC
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨-, -, hc3, -, hc5, -, -, -, -, hc10, -⟩ := hstar
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hHs, -, hn, hVn, -, -, -, -, -, -, -, -, -, -, -, -, hUe, -, -, hidx,
    ⟨hcommV, htv⟩, hUO, -, -, hHU, -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨e⟩ := Lem24.nonempty_coords hVab hVe.2 hVn
  have hn3' : 3 ≤ n := by rcases hn with rfl | rfl | rfl <;> omega
  have hCLV := Lem24.centralizer_le_pCoreOf hH hred hn3' e htop
  have hVL := V_le_L' hH
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  set Y := oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) with hYdef
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ (S : Subgroup G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (LieType.BorelTits.pCoreOf_le 2 L |>.trans
      le_sup_left) (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hH.normalizes.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hCTV : (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤
      V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := by
    rintro t ⟨htS, htV⟩
    have ht : t ∈ ((S : Subgroup G) ⊓ L) ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      hc10 ▸ htS
    have hKU : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
        Subgroup.centralizer ((((S : Subgroup G) ⊓ L : Subgroup G)) : Set G) := fun c hc =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => Subgroup.mem_centralizer_iff.mp hc.2 x hx.2
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hKU ht
    have hcV : c ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le hVL hc.2
    have hlV : l ∈ Subgroup.centralizer (V : Set G) := by
      have := Subgroup.mul_mem _ htV (Subgroup.inv_mem _ hcV)
      simpa using this
    have hlQ : l ∈ V ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
      hc5 ▸ hOL (hCLV ⟨hl.2, hlV⟩)
    exact Subgroup.mul_mem _ hlQ (Subgroup.mem_sup_right hc)
  intro y hy
  have hyS : y ∈ (S : Subgroup G) := A7.pCoreOf_le_of_le_normalizer S hTY hy
  have hyA : y ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := by
    obtain ⟨y', hy', rfl⟩ := hy
    show (y' : G) ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G)
    refine (hρ1 y').mp ?_
    rw [← MonoidHom.mem_ker, hker]
    exact hy'
  have hyV : y ∈ Subgroup.normalizer (V : Set G) := hTV hyS
  have hyN : y ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hyA
  have : IsMulCommutative ↥V := hcommV
  have hc : conjAct V ⟨y, hyV⟩ ∈ transvAxis ((U ⊓ V).subgroupOf V) := by
    refine ⟨fun a ha => ?_, fun v => ?_⟩
    · apply Subtype.ext
      change y * (a : G) * y⁻¹ = a
      rw [← Subgroup.mem_centralizer_iff.mp hyA a (Subgroup.mem_subgroupOf.mp ha),
        mul_inv_cancel_right]
    · rw [Subgroup.mem_subgroupOf]
      exact comm_mem_of_index_two hidx hyV hyN v.2
  rw [← htv] at hc
  obtain ⟨x, hxU, hxc⟩ := hc
  have hxU' : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hxU
  have hxy : (x : G)⁻¹ * y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUT hxU')) hyS,
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 : (x : G) * v * (x : G)⁻¹ = y * v * y⁻¹ := by
      have := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) hxc
      exact this
    calc v * ((x : G)⁻¹ * y) = (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹) * y := by group
      _ = (x : G)⁻¹ * (y * v * y⁻¹) * y := by rw [h1]
      _ = (x : G)⁻¹ * y * v := by group
  have hy' : y = x * ((x : G)⁻¹ * y) := by group
  rw [hy']
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hc3 ▸ Subgroup.mem_sup_left hxU')) ?_
  have h2 := hCTV hxy
  have h3 : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
    rw [hc3]
    exact le_sup_right
  exact (sup_le le_sup_right (h3.trans le_sup_left)) h2

theorem le_normalizer_R [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hC : Config12_2_24 T L V H P U I h n p) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hHs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hHU, -⟩ := hC
  exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hHU (hHs.1.1 ht)⟩

theorem centralizer_R_le [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) :
    Subgroup.centralizer ((T ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) ≤
      T ⊓ Subgroup.centralizer (U : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := card_inf_V hC
  have hTR := le_normalizer_R hC
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hHs, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, hUe, -, -, -, -, hUO, -⟩ := hC
  set R := (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) with hRdef
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUR : U ≤ R := fun u hu =>
    ⟨hUT hu, Subgroup.mem_centralizer_iff.mpr fun x hx => (hUab u hu x hx).symm⟩
  have hR2 : IsPGroup 2 R := S.isPGroup'.to_le inf_le_left
  have hRne : R ≠ ⊥ := by
    intro hb
    have h1 : U ⊓ V ≤ ⊥ := hb ▸ (inf_le_left.trans hUR)
    rw [le_bot_iff] at h1
    rw [h1, Subgroup.card_bot] at hA
    have h2 : 2 ≤ n - 1 := by rcases hn with rfl | rfl | rfl <;> omega
    have h3 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  set N := Subgroup.normalizer (R : Set G) with hNdef
  have hSN : (S : Subgroup G) ≤ N := hTR
  have hEv := hH.qtke.2.1 N ⟨R, hRne, hR2, rfl⟩ ⟨S, hSN⟩
  have hON : pCoreOf 2 N ≤ (S : Subgroup G) :=
    A7.pCoreOf_le_of_le_normalizer S (hSN.trans Subgroup.le_normalizer)
  have hNO : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hCN : Subgroup.centralizer (R : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hCTR : ∀ t ∈ (S : Subgroup G), t ∈ Subgroup.centralizer (R : Set G) → t ∈ R :=
    fun t ht htR => ⟨ht, Subgroup.centralizer_le hUR htR⟩
  have hodd : ∀ x ∈ Subgroup.centralizer (R : Set G), Odd (orderOf x) → x = 1 := by
    intro x hx hxo
    have hxN : x ∈ N := hCN hx
    have hxO : x ∈ N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) := by
      refine ⟨hxN, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have hqN : q ∈ N := LieType.BorelTits.pCoreOf_le 2 N hq
      set d := x * q * x⁻¹ * q⁻¹ with hddef
      have hdO : d ∈ pCoreOf 2 N := Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (hNO hxN) q).mp hq) (Subgroup.inv_mem _ hq)
      have hdC : d ∈ Subgroup.centralizer (R : Set G) := by
        have h1 : q * x⁻¹ * q⁻¹ ∈ Subgroup.centralizer (R : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer le_rfl hqN) _).mp
            (Subgroup.inv_mem _ hx)
        rw [hddef, show x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) by group]
        exact Subgroup.mul_mem _ hx h1
      have hdR : d ∈ R := hCTR d (hON hdO) hdC
      have hxd : x * d * x⁻¹ = d := by
        rw [← Subgroup.mem_centralizer_iff.mp hx d hdR, mul_inv_cancel_right]
      have hd2 : ∃ k : ℕ, d ^ 2 ^ k = 1 := by
        obtain ⟨k, hk⟩ := hR2 ⟨d, hdR⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      have hq' := conj_eq_of_odd (q := q) (d := d) (by rw [hddef]; group) hxd hd2 hxo
      calc q * x = (x * q * x⁻¹) * x := by rw [hq']
        _ = x * q := by group
    have hxO' := hEv hxO
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 N ⟨x, hxO'⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : Nat.Coprime (2 ^ k) (orderOf x) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hxo)
    have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes h2 h1 dvd_rfl
    exact orderOf_eq_one_iff.mp h3
  have hC2 : IsPGroup 2 (Subgroup.centralizer (R : Set G)) := by
    intro g
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    refine ⟨k, Subtype.ext ?_⟩
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    have hdvd : 2 ^ k ∣ orderOf (g : G) := ⟨m, hkm⟩
    have hord : orderOf ((g : G) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd h2k hdvd, hkm, Nat.mul_div_cancel_left _ (by positivity)]
    have := hodd _ (Subgroup.pow_mem _ g.2 _) (hord ▸ hm)
    simpa using this
  have hTC : (S : Subgroup G) ≤ Subgroup.normalizer
      (Subgroup.centralizer (R : Set G) : Set G) := fun t ht =>
    B6.le_normalizer_centralizer hTR ht
  have hsup : IsPGroup 2 ↥((S : Subgroup G) ⊔ Subgroup.centralizer (R : Set G)) :=
    IsPGroup.to_sup_of_normal_right' S.isPGroup' hC2 hTC
  have hmax : (S : Subgroup G) ⊔ Subgroup.centralizer (R : Set G) = S :=
    S.is_maximal' hsup le_sup_left
  intro x hx
  exact hCTR x (hmax ▸ Subgroup.mem_sup_right hx) hx

theorem mem_normalizer_of_fix (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) [Finite G]
    {T L V : Subgroup G} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V) {x a : G}
    (haV : a ∈ V) (ha1 : a ≠ 1) (hxa : x * a = a * x) :
    x ∈ Subgroup.normalizer (L : Set G) ∧ x ∈ Subgroup.normalizer (V : Set G) := by
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    hNE a haV ha1 (Subgroup.mem_centralizer_singleton_iff.mpr hxa)
  have hxc : x ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute a x from hxa.symm) k)).eq
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ hxc)
  have h1 := (stmt12_2_6_of h1222 h323 G T L V hH).2 (Subgroup.zpowers a) (Subgroup.zpowers x)
    (fun hb => ha1 (by rwa [Subgroup.zpowers_eq_bot] at hb)) ((Subgroup.zpowers_le).mpr haV) hle
  have h2 : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (L : Set G) :=
    ⟨Subgroup.mem_zpowers x, hxL⟩
  rw [h1] at h2
  exact ⟨hxL, h2.2⟩

theorem eq_of_card_le_two [Finite G] {K : Subgroup G} (hK : Nat.card K ≤ 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  let f : Fin 3 → K := ![⟨1, K.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, eq_comm]
  have h3 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h3
  omega

theorem mem_centralizer_L_of_fix
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx : Odd (orderOf x))
    (hxA : ∀ a ∈ U ⊓ V, x * a = a * x) : x ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨-, -, -, -, hc5, hc6, -, -, hc9, -⟩ := hstar
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, hn, hVn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨e⟩ := Lem24.nonempty_coords hVab hVe.2 hVn
  have hn3' : 3 ≤ n := by rcases hn with rfl | rfl | rfl <;> omega
  have hCLV := Lem24.centralizer_le_pCoreOf hH hred hn3' e htop
  have hVL := V_le_L' hH
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ (S : Subgroup G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (LieType.BorelTits.pCoreOf_le 2 L |>.trans
      le_sup_left) (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hH.normalizes.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hVO : V ≤ pCoreOf 2 L :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV (B2F.isPGroup_of_isElemAbelian hVe)
  have hCTLV : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (V : Set G) := fun c hc => Subgroup.centralizer_le hVL hc.2
  have hxN : x ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hxA a ha).symm)
  have hxCV : ∀ v ∈ V, x * v * x⁻¹ = v := by
    intro v hv
    set d := x * v * x⁻¹ * v⁻¹ with hddef
    have hd : d ∈ U ⊓ V := comm_mem_of_index_two hidx hxV hxN hv
    have hxd : x * d * x⁻¹ = d := by rw [hxA d hd, mul_inv_cancel_right]
    have hd2 : ∃ k : ℕ, d ^ 2 ^ k = 1 := ⟨1, by rw [pow_one]; exact hVe.2 d hd.2⟩
    exact conj_eq_of_odd (q := v) (d := d) (by rw [hddef]; group) hxd hd2 hx
  have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxL
  have hdec : ∀ q ∈ pCoreOf 2 L, ∃ v ∈ V, ∃ c ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer (L : Set G), v * c = q := fun q hq =>
    exists_mul_of_mem_sup_centralizer hCTLV (hc5 ▸ hOL hq)
  have hZ : ∀ q ∈ pCoreOf 2 L, q ∈ Subgroup.centralizer (L : Set G) →
      q ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) := by
    intro q hq hqC
    obtain ⟨v, hv, c, hc, rfl⟩ := hdec q hq
    have hvC : v ∈ Subgroup.centralizer (L : Set G) := by
      have := Subgroup.mul_mem _ hqC (Subgroup.inv_mem _ hc.2)
      simpa using this
    have hv1 : v = 1 := by
      have : v ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hv, hvC⟩
      rw [hc6] at this
      exact this
    rw [hv1, one_mul]
    exact hc
  have hxOL : ∀ q ∈ pCoreOf 2 L, x * q * x⁻¹ = q := by
    intro q hq
    obtain ⟨v, hv, c, hc, rfl⟩ := hdec q hq
    have hcO : c ∈ pCoreOf 2 L := by
      have h1 : v⁻¹ * (v * c) ∈ pCoreOf 2 L :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (hVO hv)) hq
      simpa using h1
    have hxc : x * c * x⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) := by
      refine hZ _ ((Subgroup.mem_normalizer_iff.mp hxO c).mp hcO) ?_
      exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer le_rfl hxL) c).mp hc.2
    have hxcc : x * c * x⁻¹ = c := by
      by_cases hc1 : c = 1
      · rw [hc1, mul_one, mul_inv_cancel]
      · refine eq_of_card_le_two hc9 hxc hc ?_ hc1
        intro h1
        apply hc1
        calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
          _ = 1 := by rw [h1]; group
    calc x * (v * c) * x⁻¹ = (x * v * x⁻¹) * (x * c * x⁻¹) := by group
      _ = v * c := by rw [hxCV v hv, hxcc]
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  set d := x * l * x⁻¹ * l⁻¹ with hddef
  have hdL : d ∈ L := L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxL l).mp hl) (L.inv_mem hl)
  have hdV : d ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hl)) v).mp hv
      simpa using this
    have hxw : x⁻¹ * (l⁻¹ * v * l) * x = l⁻¹ * v * l := by
      have h1 := hxCV _ hw
      calc x⁻¹ * (l⁻¹ * v * l) * x = x⁻¹ * (x * (l⁻¹ * v * l) * x⁻¹) * x := by rw [h1]
        _ = l⁻¹ * v * l := by group
    have h2 : d * v * d⁻¹ = v := by
      calc d * v * d⁻¹ = x * l * (x⁻¹ * (l⁻¹ * v * l) * x) * l⁻¹ * x⁻¹ := by rw [hddef]; group
        _ = x * l * (l⁻¹ * v * l) * l⁻¹ * x⁻¹ := by rw [hxw]
        _ = x * v * x⁻¹ := by group
        _ = v := hxCV v hv
    calc v * d = (d * v * d⁻¹) * d := by rw [h2]
      _ = d * v := by group
  have hdO : d ∈ pCoreOf 2 L := hCLV ⟨hdL, hdV⟩
  have hxd : x * d * x⁻¹ = d := hxOL d hdO
  have hd2 : ∃ k : ℕ, d ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨d, hdO⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hl' := conj_eq_of_odd (q := l) (d := d) (by rw [hddef]; group) hxd hd2 hx
  calc l * x = (x * l * x⁻¹) * x := by rw [hl']
    _ = x * l := by group

theorem mem_normalizer_Y {L U V : Subgroup G} {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxA : x ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer
      ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
        Set G) :=
  normalizer_le_normalizer_oTwoUpper _
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hxL, Subgroup.le_normalizer hxA⟩)

end Lem25

end CFSG.Quasithin.H13
