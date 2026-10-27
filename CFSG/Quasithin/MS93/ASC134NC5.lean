module

public import CFSG.Quasithin.MS93.ASC134NC5Pt
public import CFSG.Quasithin.MS93.ASC134NC

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.MS93.AS
open CFSG.Open hiding StatedSL StatedSp
open scoped Pointwise
open Matrix

theorem c134NotCentralizer5_holds : C134NotCentralizer5 := by
  intro G _ _ G₀ R L hMS hL hG h hX h5
  obtain ⟨n, F, _, _, α, hF, hmod, hW⟩ := isModO2Surj_of_case5 h h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_eq hF
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  set V := Vq G₀ L with hVdef
  intro S hS hRS hRO
  set C := G₀ ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set G) with hCdef
  have hLn : (L.subgroupOf G₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hSL : IsSylowTwoOf (S ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hS h.L_le hLn.isSubnormal
  obtain ⟨α₁, b, hα₁, hker₁, hα₁S, hb, hbadd, hbeq⟩ := exists_standard_natural2 hF hmod.1 hW hSL
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hW.1
  have hGV : G₀ ≤ Subgroup.normalizer (V : Set G) := le_normalizer_Vq h.le_normalizer
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := h.le.trans hGV
  have hVR : V ≤ R := (Vq_le_pCoreOf h.L_le).trans h.pCore_le
  have hb1 : b 1 = 0 := by
    have h1 : b 1 + b 1 = b 1 + 0 := by rw [add_zero, ← hbadd, mul_one]
    exact add_left_cancel h1
  have hVab : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun x y => hb.1 (by rw [hbadd, hbadd, add_comm])⟩⟩, fun x hx => ?_⟩
    have h2 : (⟨x, hx⟩ : ↥V) * ⟨x, hx⟩ = 1 := hb.1 (by
      rw [hbadd, hb1]
      funext i j
      simp [CharTwo.add_self_eq_zero])
    rw [pow_two]
    exact congrArg Subtype.val h2
  have htriv : ∀ ℓ : ↥L, (∀ v : ↥V, (ℓ : G) * v * (ℓ : G)⁻¹ = v) → α₁ ℓ = 1 := by
    intro ℓ hℓ
    apply dg_injective
    intro n
    obtain ⟨v, rfl⟩ := hb.2 n
    rw [dg_one, ← hbeq ℓ v v (hℓ v).symm]
  have hK2 : IsPGroup 2 ↥(G₀ ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨c, hcG, hcV⟩
    have hc : c ∈ (L : Set G) * (R : Set G) := hG ▸ hcG
    obtain ⟨ℓ, hℓ, r, hr, rfl⟩ := hc
    obtain ⟨m, hm⟩ := h.isPGroup ⟨r, hr⟩
    have hrm : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hrL : r ∈ Subgroup.normalizer (L : Set G) := h.le_normalizer (h.le hr)
    have hpow : ∀ k : ℕ, (ℓ * r) ^ k * (r ^ k)⁻¹ ∈ L := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hconj : r ^ k * ℓ * (r ^ k)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (pow_mem hrL k) ℓ).mp hℓ
        have e : (ℓ * r) ^ (k + 1) * (r ^ (k + 1))⁻¹ =
            ((ℓ * r) ^ k * (r ^ k)⁻¹) * (r ^ k * ℓ * (r ^ k)⁻¹) := by
          rw [pow_succ, pow_succ]
          group
        rw [e]
        exact L.mul_mem ih hconj
    have hdL : (ℓ * r) ^ 2 ^ m ∈ L := by simpa [hrm] using hpow (2 ^ m)
    have hdV : (ℓ * r) ^ 2 ^ m ∈ Subgroup.centralizer (V : Set G) := pow_mem hcV _
    have hd1 : α₁ ⟨_, hdL⟩ = 1 := htriv ⟨_, hdL⟩ fun v => by
      rw [show ((ℓ * r) ^ 2 ^ m) * (v : G) = v * (ℓ * r) ^ 2 ^ m from
        (Subgroup.mem_centralizer_iff.mp hdV v v.2).symm]
      exact mul_inv_cancel_right _ _
    have hdker : (⟨_, hdL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hmod.2, ← hker₁]
      exact hd1
    obtain ⟨m', hm'⟩ := isPGroup_cfsgPCore ↥L ⟨_, hdker⟩
    have hm'' : ((ℓ * r) ^ 2 ^ m) ^ 2 ^ m' = 1 := by
      simpa using congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hm'
    refine ⟨m + m', Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hm'']
  have hKQ : G₀ ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 G₀ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ hK2
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hGV)
  have hKR : G₀ ⊓ Subgroup.centralizer (V : Set G) ≤ R := hKQ.trans h.pCore_le
  by_cases hJ : thompsonJ R ≤ Subgroup.centralizer (V : Set G)
  · have hJQ : thompsonJ R ≤ pCoreOf 2 G₀ :=
      (le_inf ((thompsonJ_le_self R).trans h.le) hJ).trans hKQ
    have hJeq : thompsonJ R = thompsonJ (pCoreOf 2 G₀) := thompsonJ_eq_of_le hJQ h.pCore_le
    exact absurd ((le_normalizer_pCoreOf G₀).trans
      (hJeq ▸ normalizer_le_normalizer_thompsonJ (pCoreOf 2 G₀)))
      (h.noChar (thompsonJ R) (thompsonJ_le_self R) (Setup.thompsonJ_ne_bot h.isPGroup h.ne_bot)
        (Setup.characteristic_thompsonJ R))
  have hZN : Zq G₀ L ≤ Subgroup.normalizer (V : Set G) := Zq_le.trans hGV
  have hdec : ∀ x ∈ Xq G₀, ∃ c ∈ Subgroup.centralizer (L : Set G), ∃ w ∈ V, x = c * w := by
    intro x hx
    have hUV : Uq G₀ R L ≤ V := fun u hu => (Subgroup.mem_inf.mp (Uq_le_centerOf_Vq h hu)).1
    have hxZ : x ∈ Zq G₀ L ⊔ V := sup_le_sup_left hUV _ (hX hx)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZN] at hxZ
    obtain ⟨c, hc, w, hw, rfl⟩ := hxZ
    exact ⟨c, (Subgroup.mem_inf.mp hc).2, w, hw, rfl⟩
  have hstabC : ∀ ℓ : ↥L,
      ((α₁ ℓ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] → (ℓ : G) ∈ C := by
    intro ℓ hℓe
    refine Subgroup.mem_inf.mpr ⟨h.L_le ℓ.2, ?_⟩
    have hQS : pCoreOf 2 G₀ ≤ S := h.pCore_le.trans hRS
    unfold omegaOneCenterOf omegaOneOf
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro x ⟨⟨hxS, hxC⟩, hx2⟩
    have hxCQ : x ∈ Subgroup.centralizer (pCoreOf 2 G₀ : Set G) :=
      Subgroup.centralizer_le hQS hxC
    have hxQ : x ∈ pCoreOf 2 G₀ := h.charTwo ⟨hS.1 hxS, hxCQ⟩
    have hxX : x ∈ Xq G₀ := Subgroup.subset_closure ⟨⟨hxQ, hxCQ⟩, hx2⟩
    obtain ⟨c, hc, w, hw, rfl⟩ := hdec x hxX
    have hwS : ∀ t : ↥L, t ∈ (S ⊓ L).subgroupOf L → (w : G) = t * w * t⁻¹ := by
      intro t ht
      have htS : (t : G) ∈ S := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1
      have h1 : (t : G) * (c * w) = c * w * t := Subgroup.mem_centralizer_iff.mp hxC t htS
      have h2 : (t : G) * c = c * t := Subgroup.mem_centralizer_iff.mp hc t t.2
      have h3 : (t : G) * w = w * t := by
        have e : c * ((t : G) * w) = c * (w * t) := by
          rw [← mul_assoc, ← h2, mul_assoc, h1, mul_assoc]
        exact mul_left_cancel e
      have h4 : (w : G) = t * w * (t : G)⁻¹ := by rw [h3, mul_inv_cancel_right]
      exact h4
    have hbw : ∀ i, b ⟨w, hw⟩ i ∈ (pt0 : Submodule F (Fin 3 → F)) := by
      intro i
      rw [← fixN_sStar, ← hα₁S]
      rintro g ⟨t, ht, rfl⟩
      have := congrFun (hbeq t ⟨w, hw⟩ ⟨w, hw⟩ (hwS t ht)) i
      rw [dg_apply] at this
      exact this.symm
    have hℓw : (ℓ : G) * w * (ℓ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) w).mp hw
    have hfixw : (ℓ : G) * w * (ℓ : G)⁻¹ = w := by
      have e := hbeq ℓ ⟨w, hw⟩ ⟨_, hℓw⟩ rfl
      have e2 : dg (α₁ ℓ) (b ⟨w, hw⟩) = b ⟨w, hw⟩ := by
        funext i
        rw [dg_apply]
        exact mulVec_eq_of_mem_pt0 hℓe (hbw i)
      rw [e2] at e
      exact congrArg Subtype.val (hb.1 e)
    have hcℓ : (ℓ : G) * c = c * ℓ := Subgroup.mem_centralizer_iff.mp hc ℓ ℓ.2
    have hℓw' : (ℓ : G) * w = w * ℓ := by
      calc (ℓ : G) * w = (ℓ : G) * w * (ℓ : G)⁻¹ * ℓ := by group
        _ = w * ℓ := by rw [hfixw]
    calc c * w * ℓ = c * (w * ℓ) := mul_assoc _ _ _
      _ = c * (ℓ * w) := by rw [hℓw']
      _ = (c * ℓ) * w := (mul_assoc _ _ _).symm
      _ = (ℓ * c) * w := by rw [hcℓ]
      _ = ℓ * (c * w) := mul_assoc _ _ _
  have hRLq : ∀ t : ↥L, (t : G) ∈ R → α₁ t ∈ (qPt : Subgroup (SL3 F)) := by
    have hY2 : IsPGroup 2 ↥((R.subgroupOf L).map α₁) :=
      (h.isPGroup.comap_of_injective L.subtype L.subtype_injective).map α₁
    have hYn : ∀ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        ∀ y ∈ (R.subgroupOf L).map α₁, g * y * g⁻¹ ∈ (R.subgroupOf L).map α₁ := by
      intro g hg y hy
      obtain ⟨ℓ, rfl⟩ := hα₁ g
      obtain ⟨t, ht, rfl⟩ := hy
      have hℓR : (ℓ : G) ∈ Subgroup.normalizer (R : Set G) := by
        rw [hRO]
        exact le_normalizer_pCoreOf C (hstabC ℓ hg)
      refine ⟨ℓ * t * ℓ⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp hℓR t).mp (Subgroup.mem_subgroupOf.mp ht)
      simpa using this
    intro t ht
    exact le_qPt_of_normalized hF' hY2 hYn ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  obtain ⟨B', hB'⟩ := (offenderImages_nonempty_iff_not_le (H := R) hVab).mpr hJ
  have hoff := offenderImages_isFFStarOffender hVab hVR hRV hB'
  apply hoff.2.1
  let e : IntMod V hVab ≃ (Fin 2 → Fin 3 → F) := Equiv.ofBijective (fun v => b v) hb
  have he : ∀ v : IntMod V hVab, e v = b v := fun _ => rfl
  refine offender_eq_bot_of_equiv hF e (fun x y => hbadd x y) hoff.2.2.1 ?_ ?_ ?_
  · intro x hx g
    obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := (mem_autI hVab).mp (hoff.1 hx)
    obtain ⟨ℓ, rfl⟩ := hα₁ g
    have hℓ' : r * (ℓ : G) * r⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (h.le_normalizer (h.le hrR)) ℓ).mp ℓ.2
    refine ⟨α₁ ⟨_, hℓ'⟩, fun v w hvw => ?_⟩
    have hℓv : (ℓ : G) * v.val * (ℓ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) _).mp v.val_mem
    have hw : (w : ↥V) = ⟨_, hℓv⟩ := hb.1 (hvw.trans (hbeq ℓ v ⟨_, hℓv⟩ rfl).symm)
    have hw' : w.val = ℓ * v.val * (ℓ : G)⁻¹ := congrArg Subtype.val hw
    rw [he, he]
    refine hbeq _ _ _ ?_
    show (convI hVab ⟨r, hrN⟩ w).val =
      (r * ℓ * r⁻¹) * (convI hVab ⟨r, hrN⟩ v).val * (r * ℓ * r⁻¹)⁻¹
    rw [convI_apply_val, convI_apply_val, hw']
    group
  · intro x hx g hg
    obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := (mem_autI hVab).mp (hoff.1 hx)
    obtain ⟨ℓ, rfl⟩ := hα₁ g
    have hrv : ∀ v ∈ V, r * v * r⁻¹ = (ℓ : G) * v * (ℓ : G)⁻¹ := by
      intro v hv
      have hℓv : (ℓ : G) * v * (ℓ : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) _).mp hv
      have e1 := hg (IntMod.mk hVab ⟨v, hv⟩)
      rw [he, he] at e1
      have e2 := (hbeq ℓ ⟨v, hv⟩ ⟨_, hℓv⟩ rfl).symm
      have e3 := hb.1 (e1.trans e2)
      have e4 := congrArg Subtype.val e3
      have e5 := convI_apply_val hVab ⟨r, hrN⟩ (IntMod.mk hVab ⟨v, hv⟩)
      exact e5.symm.trans e4
    have hcen : (ℓ : G)⁻¹ * r ∈ G₀ ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨G₀.mul_mem (G₀.inv_mem (h.L_le ℓ.2)) (h.le hrR), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      calc v * ((ℓ : G)⁻¹ * r) = (ℓ : G)⁻¹ * ((ℓ : G) * v * (ℓ : G)⁻¹) * r := by group
        _ = (ℓ : G)⁻¹ * (r * v * r⁻¹) * r := by rw [hrv v hv]
        _ = (ℓ : G)⁻¹ * r * v := by group
    have hℓR : (ℓ : G) ∈ R := by
      have := R.mul_mem hrR (R.inv_mem (hKR hcen))
      simpa using this
    exact hRLq ℓ hℓR
  · have h0 := hoff.2.2.2 ⊥ bot_le
    have hfix : fixV (⊥ : Subgroup (MulAut (IntMod V hVab))) = ⊤ :=
      eq_top_iff.mpr fun v _ x hx => by rw [Subgroup.mem_bot.mp hx]; rfl
    rw [Subgroup.card_bot, one_mul, hfix, Subgroup.card_top] at h0
    exact h0

end CFSG.Quasithin.MS93
