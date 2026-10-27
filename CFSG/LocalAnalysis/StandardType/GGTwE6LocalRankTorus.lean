module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankFrame
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6

namespace TwE6Lang

section Cond

variable {k : Type*} [Field k]

@[expose] def sHom (ζ : kˣ) :
    (Fin (Tag.rank .E6) → Subgroup.zpowers ζ) →* Subgroup.zpowers ζ :=
  (Pi.evalMonoidHom (fun _ => Subgroup.zpowers ζ) (nd 1)) ^ 2 *
    (Pi.evalMonoidHom (fun _ => Subgroup.zpowers ζ) (nd 3))⁻¹

@[expose] def sCond (ζ : kˣ) : Subgroup (Fin (Tag.rank .E6) → Subgroup.zpowers ζ) :=
  (sHom ζ).ker

theorem mem_sCond {ζ : kˣ} {w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ} :
    w ∈ sCond ζ ↔ w (nd 3) = w (nd 1) ^ 2 := by
  rw [sCond, MonoidHom.mem_ker]
  show sHom ζ w = 1 ↔ w (nd 3) = w (nd 1) ^ 2
  simp only [sHom, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply,
    Pi.evalMonoidHom_apply]
  rw [mul_inv_eq_one, eq_comm]

theorem card_sCond {ζ : kˣ} (hζ : orderOf ζ = 3) : Nat.card (sCond ζ) = 3 ^ 5 := by
  have hcardG : Nat.card (Fin (Tag.rank .E6) → Subgroup.zpowers ζ) = 3 ^ 6 := by
    rw [Nat.card_fun, Nat.card_zpowers, Nat.card_eq_fintype_card, Fintype.card_fin, hζ]
    rfl
  have hsurj : Function.Surjective (sHom ζ) := by
    intro z
    refine ⟨(Pi.mulSingle (nd 3) z⁻¹ : Fin (Tag.rank .E6) → Subgroup.zpowers ζ), ?_⟩
    simp only [sHom, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply,
      Pi.evalMonoidHom_apply, Pi.mulSingle_eq_of_ne (by decide : (nd 1) ≠ nd 3),
      Pi.mulSingle_eq_same, inv_inv]
    simp
  have hrange : Nat.card (sHom ζ).range = 3 := by
    rw [(sHom ζ).range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_zpowers, hζ]
  rw [sCond]
  have h := Subgroup.card_mul_index (sHom ζ).ker
  rw [Subgroup.index_ker, hrange, hcardG] at h
  rw [show (3 : ℕ) ^ 6 = 3 ^ 5 * 3 from by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end Cond


variable {k : Type*} [Field k]

variable (k) in
@[expose] noncomputable def torusConj3 (θ : k →+* k) (l : k) (ζ : kˣ) :
    (Fin (Tag.rank .E6) → Subgroup.zpowers ζ) →* e6Data_valid.minGroup k :=
  (MulAut.conj (langG3 k θ l)).toMonoidHom.comp
    ((torusHom k).comp (MonoidHom.compLeft (Subgroup.zpowers ζ).subtype _))

theorem torusConj3_injective (θ : k →+* k) (l : k) (ζ : kˣ) :
    Function.Injective (torusConj3 k θ l ζ) := by
  intro w w' h
  simp only [torusConj3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  have h2 := torusHom_injective ((MulAut.conj (langG3 k θ l)).injective h)
  funext a
  exact Subtype.ext (congrFun h2 a)

theorem exists_torusConj3_eq (θ : k →+* k) (l : k) (ζ : kˣ)
    (w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ) :
    ∃ v : Fin (Tag.rank .E6) → ℤ, (∀ a, ζ ^ v a = (w a : kˣ)) ∧
      torusConj3 k θ l ζ w = langG3 k θ l * torusPow ζ v * (langG3 k θ l)⁻¹ := by
  have hw : ∀ a, ∃ m : ℤ, ζ ^ m = (w a : kˣ) := fun a =>
    Subgroup.mem_zpowers_iff.1 (w a).2
  choose v hv using hw
  refine ⟨v, hv, ?_⟩
  have hfun : MonoidHom.compLeft (Subgroup.zpowers ζ).subtype (Fin (Tag.rank .E6)) w =
      fun a => ζ ^ v a := by
    funext a
    rw [MonoidHom.compLeft_apply, Function.comp_apply, Subgroup.coe_subtype, hv]
  rw [torusConj3, MonoidHom.comp_apply, MonoidHom.comp_apply, hfun, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, torusPow]

theorem lr5_cartan_one_mul_sum (v : Fin (Tag.rank .E6) → ℤ) :
    (∑ j, Tag.cartan .E6 (nd 1) j * v j) = 2 * v (nd 1) - v (nd 3) := by
  have h1 : (∑ j, Tag.cartan .E6 (nd 1) j * v j) =
      ∑ j, (if j = nd 1 then (2 : ℤ) else if j = nd 3 then -1 else 0) * v j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    fin_cases j <;> decide
  rw [h1]
  have hsplit : ∀ j : Fin (Tag.rank .E6),
      (if j = nd 1 then (2 : ℤ) else if j = nd 3 then -1 else 0) * v j =
        (if j = nd 1 then 2 * v j else 0) + (if j = nd 3 then -v j else 0) := by
    intro j
    by_cases h1' : j = nd 1
    · subst h1'
      rw [if_pos rfl, if_pos rfl, if_neg (by decide : nd 1 ≠ nd 3)]
      ring
    · rw [if_neg h1']
      by_cases h3 : j = nd 3
      · subst h3
        rw [if_pos rfl, if_neg (by decide : nd 3 ≠ nd 1), if_pos rfl]
        ring
      · rw [if_neg h3, if_neg h3, if_neg h1']
        ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

theorem torusPow_frameAct_zero {ζ : kˣ} {v : Fin (Tag.rank .E6) → ℤ}
    (h : ζ ^ (2 * v (nd 1) - v (nd 3)) = 1) : torusPow ζ (frameAct 0 v) = torusPow ζ v := by
  rw [frameAct_zero, torusPow, torusPow]
  congr 1
  funext a
  rw [reflect]
  by_cases ha : a = nd 1
  · subst ha
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [lr5_cartan_one_mul_sum, sub_eq_add_neg, zpow_add, zpow_neg, h, inv_one, mul_one]
  · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne' (Ne.symm ha), smul_eq_mul,
      mul_zero, sub_zero]

theorem torusConj3_mem_fixedGroup (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l)
    {ζ : kˣ} {m : ℤ} (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1)
    {w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ} (hw : w ∈ sCond ζ) :
    torusConj3 k θ l ζ w ∈ fixedGroup k θ := by
  obtain ⟨v, hvw, hconj⟩ := exists_torusConj3_eq θ l ζ w
  rw [hconj, mem_fixedGroup, sigma_langG3_conj_torusPow θ hθ hl hζ v,
    torusPow_neg_smul hm (frameAct 0 v)]
  have h3 : ζ ^ v (nd 3) = (ζ ^ v (nd 1)) ^ 2 := by
    rw [hvw (nd 3), mem_sCond.1 hw, hvw (nd 1)]
    simp
  have h : ζ ^ (2 * v (nd 1) - v (nd 3)) = 1 := by
    rw [zpow_sub, zpow_mul', h3]
    exact mul_inv_cancel _
  rw [torusPow_frameAct_zero (v := v) h]

theorem torusHom_conj_xm_eOne (u : Fin (Tag.rank .E6) → kˣ) (c : k) :
    torusHom k u * e6Data_valid.xm k eOne c * (torusHom k u)⁻¹ =
      e6Data_valid.xm k eOne (((u (nd 1) ^ 2 * (u (nd 3))⁻¹ : kˣ) : k) * c) := by
  let P : (Fin (Tag.rank .E6) → kˣ) → Prop := fun u => ∀ c : k,
    torusHom k u * e6Data_valid.xm k eOne c * (torusHom k u)⁻¹ =
      e6Data_valid.xm k eOne (((u (nd 1) ^ 2 * (u (nd 3))⁻¹ : kˣ) : k) * c)
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb c
    simp only [P] at ha hb
    simp only [map_mul]
    rw [show torusHom k a * torusHom k b * e6Data_valid.xm k eOne c *
        (torusHom k a * torusHom k b)⁻¹ =
        torusHom k a * (torusHom k b * e6Data_valid.xm k eOne c * (torusHom k b)⁻¹) *
          (torusHom k a)⁻¹ by group]
    rw [hb c, ha (((b (nd 1)) ^ 2 * (b (nd 3))⁻¹ : kˣ) * c)]
    congr 1
    simp only [Pi.mul_apply]
    push_cast
    ring
  have hone : P 1 := by
    intro c
    simp
  have hsingle : ∀ j ∈ (Finset.univ : Finset (Fin (Tag.rank .E6))),
      P (Pi.mulSingle j (u j)) := by
    intro j _
    intro c
    rw [torusHom_mulSingle, e6Data_valid.hm_conj_xm k (IsRoot.basis (nd 1)) j (u j) c]
    congr 1
    have hsc : (u j) ^ MinData.toWeight eOne j =
        ((Pi.mulSingle j (u j) : Fin (Tag.rank .E6) → kˣ) (nd 1)) ^ 2 *
          (((Pi.mulSingle j (u j) : Fin (Tag.rank .E6) → kˣ) (nd 3)))⁻¹ := by
      have htw : MinData.toWeight eOne j =
          if j = nd 1 then (2 : ℤ) else if j = nd 3 then -1 else 0 := by
        rw [MinData.toWeight_apply]
        fin_cases j <;> decide
      rw [htw]
      by_cases h1 : j = nd 1
      · subst h1
        rw [if_pos rfl]
        simp [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (nd 3) ≠ nd 1)]
      · rw [if_neg h1]
        by_cases h3 : j = nd 3
        · subst h3
          rw [if_pos rfl]
          simp [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (nd 1) ≠ nd 3)]
        · rw [if_neg h3]
          simp [Pi.mulSingle_eq_of_ne (fun h => h1 h.symm),
            Pi.mulSingle_eq_of_ne (fun h => h3 h.symm)]
    rw [hsc]
  have hprod : P (∏ j, Pi.mulSingle j (u j)) := by
    refine Finset.prod_induction (s := Finset.univ) (fun j => Pi.mulSingle j (u j)) P hmul
      hone ?_
    intro j _
    exact hsingle j (Finset.mem_univ j)
  have hu : u = ∏ j, Pi.mulSingle j (u j) := by
    funext i
    exact (Fintype.prod_pi_mulSingle i u).symm
  have hprod' : P u := by
    rw [hu]
    exact hprod
  exact hprod' c

theorem torusConj3_commute_xm (θ : k →+* k) (l : k) (ζ : kˣ)
    {w : Fin (Tag.rank .E6) → Subgroup.zpowers ζ} (hw : w ∈ sCond ζ) (c : k) :
    Commute (torusConj3 k θ l ζ w) (e6Data_valid.xm k eOne c) := by
  obtain ⟨v, hvw, hconj⟩ := exists_torusConj3_eq θ l ζ w
  rw [hconj]
  have hscalar : ((ζ ^ v (nd 1)) ^ 2 * (ζ ^ v (nd 3))⁻¹ : kˣ) = 1 := by
    rw [hvw (nd 1), hvw (nd 3), mem_sCond.1 hw]
    simp
  have hT : Commute (torusPow ζ v) (e6Data_valid.xm k eOne c) := by
    rw [torusPow, Commute, SemiconjBy]
    have h := torusHom_conj_xm_eOne (fun a => ζ ^ v a) c
    rw [hscalar] at h
    simp only [Units.val_one, one_mul] at h
    calc torusHom k (fun a => ζ ^ v a) * e6Data_valid.xm k eOne c =
        (torusHom k (fun a => ζ ^ v a) * e6Data_valid.xm k eOne c *
          (torusHom k (fun a => ζ ^ v a))⁻¹) * torusHom k (fun a => ζ ^ v a) := by group
      _ = e6Data_valid.xm k eOne c * torusHom k (fun a => ζ ^ v a) := by rw [h]
  have hG : Commute (langG3 k θ l) (e6Data_valid.xm k eOne c) :=
    (commute_langG3 θ l (xm_mem_rankOne eOne c)).symm
  exact (hG.mul_left hT).mul_left hG.inv_left

variable (k) in
@[expose] noncomputable def langTorusE5 (θ : k →+* k) (l : k) (ζ : kˣ) :
    Subgroup (e6Data_valid.minGroup k) :=
  (sCond ζ).map (torusConj3 k θ l ζ)

theorem card_langTorusE5 (θ : k →+* k) (l : k) {ζ : kˣ} (hζ : orderOf ζ = 3) :
    Nat.card (langTorusE5 k θ l ζ) = 3 ^ 5 := by
  rw [langTorusE5, Subgroup.card_map_of_injective (torusConj3_injective θ l ζ), card_sCond hζ]

theorem langTorusE5_le_fixedGroup (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : k} (hl : θ l ≠ l)
    {ζ : kˣ} {m : ℤ} (hζ : Units.map (θ : k →* k) ζ = ζ ^ m) (hm : ζ ^ (m + 1) = 1) :
    langTorusE5 k θ l ζ ≤ fixedGroup k θ := by
  rintro _ ⟨w, hw, rfl⟩
  exact torusConj3_mem_fixedGroup θ hθ hl hζ hm hw

theorem lr5_langTorusE5_commute (θ : k →+* k) (l : k) (ζ : kˣ)
    {x y : e6Data_valid.minGroup k} (hx : x ∈ langTorusE5 k θ l ζ)
    (hy : y ∈ langTorusE5 k θ l ζ) : Commute x y := by
  obtain ⟨w, -, rfl⟩ := hx
  obtain ⟨w', -, rfl⟩ := hy
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem langTorusE5_isElemAbelian (θ : k →+* k) (l : k) {ζ : kˣ} (hζ : orderOf ζ = 3) :
    IsElemAbelian 3 (langTorusE5 k θ l ζ) := by
  have h3 : ζ ^ (3 : ℕ) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine ⟨⟨⟨fun x y => Subtype.ext (lr5_langTorusE5_commute θ l ζ x.2 y.2).eq⟩⟩, fun x hx => ?_⟩
  obtain ⟨w, -, rfl⟩ := hx
  rw [← map_pow]
  have hw3 : w ^ 3 = 1 := by
    funext a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (w a).2
    apply Subtype.ext
    rw [Pi.pow_apply, SubgroupClass.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, h3, one_zpow]
    rfl
  rw [hw3, map_one]

theorem langTorusE5_commute_xm (θ : k →+* k) (l : k) (ζ : kˣ) {x : e6Data_valid.minGroup k}
    (hx : x ∈ langTorusE5 k θ l ζ) (c : k) : Commute x (e6Data_valid.xm k eOne c) := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact torusConj3_commute_xm θ l ζ hw c

variable (k) in
@[expose] noncomputable def langRootU (θ : k →+* k) : Subgroup (e6Data_valid.minGroup k) :=
  e6Data_valid.rootGroup k eOne ⊓ fixedGroup k θ

theorem langRootU_ne_bot (θ : k →+* k) : langRootU k θ ≠ ⊥ := by
  intro h
  have h1 : e6Data_valid.xm k eOne 1 ∈ langRootU k θ := by
    refine ⟨e6Data_valid.xm_mem_rootGroup k eOne 1, ?_⟩
    exact (mem_fixedGroup θ).2 (by rw [sigma_xm_single, rhoPerm_nd_one, map_one])
  rw [h, Subgroup.mem_bot, ← e6Data_valid.xm_zero k eOne] at h1
  exact one_ne_zero (e6Data_valid.xm_injective k (IsRoot.basis (nd 1)) h1)

theorem langRootU_isPGroup [CharP k 2] (θ : k →+* k) : IsPGroup 2 (langRootU k θ) := by
  intro g
  refine ⟨1, ?_⟩
  show g ^ 2 = 1
  obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup k).1 g.2.1
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hc]
  rw [pow_two, ← e6Data_valid.xm_add k eOne c c, CharTwo.add_self_eq_zero,
    e6Data_valid.xm_zero]

theorem langTorusE5_le_normalizer (θ : k →+* k) (l : k) (ζ : kˣ) :
    langTorusE5 k θ l ζ ≤ Subgroup.normalizer (langRootU k θ : Set (e6Data_valid.minGroup k)) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer
    (langRootU k θ : Set (e6Data_valid.minGroup k)))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy.1
  exact (langTorusE5_commute_xm θ l ζ hx c).eq.symm

end TwE6Lang

end CFSG.StandardType
