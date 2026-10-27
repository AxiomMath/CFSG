module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenHyp139N3
public import CFSG.GroupTheory.PCoreOfSubnormal

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.QuasithinUnique
open scoped commutatorElement

theorem isElemAbelian2_of_fixed_and_quotient {W : Type} [CommGroup W]
    (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup W} {L : Subgroup (MulAut W)}
    (hLY : ∀ l ∈ L, ∀ y ∈ Y, l y = y)
    (hLQ : ∀ l ∈ L, ∀ w : W, l w * w⁻¹ ∈ Y) :
    CFSG.Quasithin.IsElemAbelian2 L := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw2 w)
  have hdisp : ∀ (l : MulAut W) (w : W), l w = (l w * w⁻¹) * w := by
    intro l w
    rw [mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨?_, ?_⟩
  · intro l hl m hm
    ext w
    have hyl : l w * w⁻¹ ∈ Y := hLQ l hl w
    have hym : m w * w⁻¹ ∈ Y := hLQ m hm w
    have hly : l (m w * w⁻¹) = m w * w⁻¹ := hLY l hl _ hym
    have hmy : m (l w * w⁻¹) = l w * w⁻¹ := hLY m hm _ hyl
    calc
      (l * m) w = l (m w) := rfl
      _ = l ((m w * w⁻¹) * w) := by conv_lhs => rw [hdisp m w]
      _ = l (m w * w⁻¹) * l w := by rw [map_mul]
      _ = (m w * w⁻¹) * ((l w * w⁻¹) * w) := by
            conv_lhs => rw [hly, hdisp l w]
      _ = (m w * w⁻¹) * (l w * w⁻¹) * w := by rw [← mul_assoc]
      _ = (l w * w⁻¹) * (m w * w⁻¹) * w := by
            conv_lhs => rw [mul_comm (m w * w⁻¹) (l w * w⁻¹)]
      _ = (l w * w⁻¹) * ((m w * w⁻¹) * w) := by
            conv_lhs => rw [mul_assoc]
      _ = (l w * w⁻¹) * m w := by conv_lhs => rw [← hdisp m w]
      _ = m (l w * w⁻¹) * m w := by conv_lhs => rw [← hmy]
      _ = m ((l w * w⁻¹) * w) := by conv_lhs => rw [← map_mul]
      _ = m (l w) := by conv_lhs => rw [← hdisp l w]
      _ = (m * l) w := rfl
  · intro l hl
    ext w
    rw [pow_two]
    have hy : l w * w⁻¹ ∈ Y := hLQ l hl w
    have hly : l (l w * w⁻¹) = l w * w⁻¹ := hLY l hl _ hy
    calc
      (l * l) w = l (l w) := rfl
      _ = l ((l w * w⁻¹) * w) := by conv_lhs => rw [hdisp l w]
      _ = l (l w * w⁻¹) * l w := by rw [map_mul]
      _ = (l w * w⁻¹) * l w := by conv_lhs => rw [hly]
      _ = w := by
        rw [mul_assoc, mul_comm (w⁻¹) (l w), ← mul_assoc]
        rw [show l w * l w = 1 by simpa [pow_two] using hw2 (l w)]
        rw [one_mul, hinv]
      _ = (1 : MulAut W) w := rfl

theorem sixfourteen_n3_D_faithful_on_L_rel {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W} {n : ℕ}
    (hK : CFSG.Open.IsKGroup ↥G) (hpCore : pCoreOf 2 G = ⊥)
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (ht2 : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hXcard : Nat.card X = 3)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYrk : rkIdx Y = 2)
    (hW : Nat.card W = 4 ^ n)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2 ^ (n - 1))
    (hYD : Y ≤ fixV D)
    (hn : 2 < n)
    (L : Subgroup (MulAut W)) (hLG : L ≤ G) (hLne : L ≠ ⊥)
    (hLsub : CFSG.Open.IsSubnormal L G)
    (hLD : ⁅L, D⁆ = L)
    (hLinv : ∀ d ∈ D, L.map (MulAut.conj d).toMonoidHom = L) :
    ∀ d ∈ D, (∀ l ∈ L, d * l = l * d) → d = 1 := by
  intro d hdD hdL
  by_contra hd_ne
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    omega
  have hfixX : fixV X = ⊥ := fixV_eq_bot_of_irreducible hirr hXG hXnorm hXne
  have hXcard' : Nat.card ↥X = 3 := hXcard
  letI : Fintype ↥X := Fintype.ofFinite _
  have hXcardF : Fintype.card ↥X = 3 := by
    rw [← Nat.card_eq_fintype_card, hXcard']
  obtain ⟨xX, hxXne⟩ : ∃ xX : ↥X, xX ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥X)
    rw [hXcardF]
    norm_num
  let x : MulAut W := xX
  have hxX : x ∈ X := xX.2
  have hx_ne : x ≠ 1 := by
    intro h
    exact hxXne (Subtype.ext h)
  have hx_ord_dvd : orderOf x ∣ 3 := by
    have h : orderOf xX ∣ 3 := by
      have h2 := orderOf_dvd_natCard xX
      rwa [Nat.card_eq_fintype_card, hXcardF] at h2
    rwa [← Subgroup.orderOf_coe xX] at h
  have hx_ord3 : orderOf x = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf x) hx_ord_dvd with
      h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hx3 : x ^ 3 = 1 := by
    rw [← hx_ord3]
    exact pow_orderOf_eq_one x
  have hxgen : X = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_
    rw [Nat.card_zpowers, hx_ord3, hXcard]
  have hfix : fixV (Subgroup.zpowers x) = ⊥ := by
    rw [← hxgen]
    exact hfixX
  have hWpow : Nat.card W = 2 ^ (2 * n) := by
    rw [hW, show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  have hYidx_dvd : Y.index ∣ 2 ^ (2 * n) := by
    rw [← hWpow]
    exact ⟨Nat.card Y, by rw [mul_comm]; exact (Y.card_mul_index).symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hYidx_dvd
  have hk2 : k = 2 := by
    have h := hYrk
    change padicValNat 2 Y.index = 2 at h
    rw [hk, padicValNat.pow, padicValNat_self] at h
    norm_num at h
    exact h
  have hYidx : Y.index = 4 := by
    rw [hk, hk2]
    norm_num
  have hcardY : Nat.card Y = 4 ^ (n - 1) := by
    have hcard := Y.card_mul_index
    rw [hW, hYidx] at hcard
    have hpow : (4 : ℕ) ^ n = 4 ^ (n - 1) * 4 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    rw [hpow] at hcard
    exact Nat.mul_right_cancel (by norm_num : 0 < 4) hcard
  have hfix_of_mem : ∀ e : MulAut W, e ∈ D → e ≠ 1 → fixV (Subgroup.zpowers e) = Y := by
    intro e heD he_ne
    have hcomm : e * x = x * e := hDCX e heD x hxX
    letI := galoisModule hw2 x hx3 hfix
    let Ys : Submodule (GaloisField 2 2) (Additive W) :=
      YSubmodule hw2 x hx3 hfix hxX hYinv
    have hKcard : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hYcardYs : Nat.card Ys = 4 ^ (n - 1) := by
      calc Nat.card Ys = Nat.card Y :=
            (Nat.card_congr (YSubmoduleEquiv hw2 x hx3 hfix hxX hYinv)).symm
        _ = 4 ^ (n - 1) := hcardY
    have hVn : Module.finrank (GaloisField 2 2) (Additive W) = n := by
      have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Additive W)
      change Nat.card W = Nat.card (GaloisField 2 2) ^
        Module.finrank (GaloisField 2 2) (Additive W) at h
      rw [hW, hKcard] at h
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
    have hYn : Module.finrank (GaloisField 2 2) Ys = n - 1 := by
      have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Ys)
      rw [hYcardYs, hKcard] at h
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
    have hfin : Module.finrank (GaloisField 2 2) Ys + 1 =
        Module.finrank (GaloisField 2 2) (Additive W) := by omega
    have hYfix : Ys ≤ fixedSubmodule
        (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm).toLinearMap :=
      YSubmodule_le_fixedSubmodule hw2 x hx3 hfix hxX hYinv heD hYD hcomm
    have hg_ne : hGaloisLinearEquiv hw2 x hx3 hfix e hcomm ≠ 1 :=
      hGaloisLinearEquiv_ne_one hw2 x hx3 hfix hcomm he_ne
    have hF_eq : fixedSubmodule
        (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm).toLinearMap = Ys :=
      fixedSubmodule_eq_of_finrank_eq_sub_one hYfix hfin hg_ne
    have hgapp : ∀ v : Additive W,
        (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm) v =
          Additive.ofMul (e (Additive.toMul v)) := by
      intro v
      rw [hGaloisLinearEquiv_apply (hw2 := hw2) (x := x) (hx3 := hx3) (hfix := hfix) (h := e) hcomm]
      simp [autAddHom_apply]
    have hcardZ : Nat.card ↥(fixV (Subgroup.zpowers e)) =
        Nat.card ↥(fixedSubmodule
          (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm).toLinearMap) := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun z => ⟨Additive.ofMul z.1, ?_⟩
          invFun := fun v => ⟨Additive.toMul v.1, ?_⟩
          left_inv := fun z => by ext; simp
          right_inv := fun v => by ext; simp }
      · rw [mem_fixedSubmodule]
        have hz : e z.1 = z.1 := mem_fixV_zpowers_iff.mp z.2
        have hconv : (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm) (Additive.ofMul z.1) =
            Additive.ofMul (e (Additive.toMul (Additive.ofMul z.1))) := hgapp _
        change (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm) (Additive.ofMul z.1) =
          Additive.ofMul z.1
        rw [hconv]
        simp [hz]
      · rw [mem_fixV_zpowers_iff]
        have h := mem_fixedSubmodule.mp v.2
        have hconv : (hGaloisLinearEquiv hw2 x hx3 hfix e hcomm) v.1 =
            Additive.ofMul (e (Additive.toMul v.1)) := hgapp v.1
        have h' : Additive.ofMul (e (Additive.toMul v.1)) = v.1 := by
          rw [← hconv]
          simpa using h
        have h'' := congrArg Additive.toMul h'
        simpa using h''
    have hYe : Y ≤ fixV (Subgroup.zpowers e) :=
      fun w hw y hy => hYD hw y (Subgroup.zpowers_le.mpr heD hy)
    apply (Subgroup.eq_of_le_of_card_ge hYe ?_).symm
    rw [hcardZ, hF_eq, hYcardYs, hcardY]
  have hfix_d : fixV (Subgroup.zpowers d) = Y := hfix_of_mem d hdD hd_ne
  have hDY : ∀ e ∈ D, ∀ y ∈ Y, e y = y := fun e he y hy => hYD hy e he
  have hDYinv : ∀ e ∈ D, ∀ y ∈ Y, e⁻¹ y = y := by
    intro e he y hy
    have h : e⁻¹ (e y) = y := by simp
    rwa [hDY e he y hy] at h
  have hinv : ∀ w : W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw2 w)
  have hDQ : ∀ e ∈ D, ∀ w : W, e w * w⁻¹ ∈ Y := by
    intro e he w
    by_cases he1 : e = 1
    · subst he1
      simp
    · have hfixe : fixV (Subgroup.zpowers e) = Y := hfix_of_mem e he he1
      have he2 : e * e = 1 := by
        have h := hElem.2 e he
        rwa [pow_two] at h
      have hmem : e w * w⁻¹ ∈ fixV (Subgroup.zpowers e) := by
        rw [mem_fixV_zpowers_iff]
        calc
          e (e w * w⁻¹) = e (e w) * (e w)⁻¹ := by rw [map_mul, map_inv]
          _ = w * (e w)⁻¹ := by
            rw [show e (e w) = w by rw [← MulAut.mul_apply, he2, MulAut.one_apply]]
          _ = (e w * w⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
          _ = e w * w⁻¹ := by rw [hinv]
      rwa [hfixe] at hmem
  have hpresY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y := by
    intro l hl y hy
    have hdy : d y = y := hDY d hdD y hy
    have hcomm : d * l = l * d := hdL l hl
    have hfix : d (l y) = l y := by
      calc
        d (l y) = (d * l) y := rfl
        _ = (l * d) y := by rw [hcomm]
        _ = l (d y) := rfl
        _ = l y := by rw [hdy]
    rw [← hfix_d]
    exact mem_fixV_zpowers_iff.mpr hfix
  let KY : Subgroup (MulAut W) :=
    { carrier := {l | ∀ y ∈ Y, l y = y}
      one_mem' := fun y _ => rfl
      mul_mem' := by
        intro l m hl hm y hy
        rw [MulAut.mul_apply, hm y hy, hl y hy]
      inv_mem' := by
        intro l hl y hy
        have h : l⁻¹ (l y) = y := by simp
        rwa [hl y hy] at h }
  have hLKY : L ≤ KY := by
    rw [← hLD]
    refine Subgroup.commutator_le.mpr ?_
    intro l hl e he y hy
    calc
      (⁅l, e⁆) y = l (e (l⁻¹ (e⁻¹ y))) := rfl
      _ = l (e (l⁻¹ y)) := by rw [hDYinv e he y hy]
      _ = l (l⁻¹ y) := by
            rw [hDY e he (l⁻¹ y) (hpresY l⁻¹ (L.inv_mem hl) y hy)]
      _ = y := by simp
  have hLY : ∀ l ∈ L, ∀ y ∈ Y, l y = y := fun l hl => hLKY hl
  let KQ : Subgroup (MulAut W) :=
    { carrier := {m | ∀ w : W, m w * w⁻¹ ∈ Y}
      one_mem' := by intro w; simp
      mul_mem' := by
        intro m n hm hn w
        have h1 : m (n w) * (n w)⁻¹ ∈ Y := hm (n w)
        have h2 : n w * w⁻¹ ∈ Y := hn w
        have heq : (m * n) w * w⁻¹ = (m (n w) * (n w)⁻¹) * (n w * w⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [heq]
        exact Y.mul_mem h1 h2
      inv_mem' := by
        intro m hm w
        have h := hm (m⁻¹ w)
        have h' : w * (m⁻¹ w)⁻¹ ∈ Y := by simpa using h
        simpa only [mul_inv_rev, inv_inv] using Y.inv_mem h' }
  have hDKQ : D ≤ KQ := fun e he => hDQ e he
  have hLKQ : L ≤ KQ := by
    rw [← hLD]
    refine Subgroup.commutator_le.mpr ?_
    intro l hl e he w
    have hconj : l * e * l⁻¹ ∈ KQ := by
      intro v
      have h := hDQ e he (l⁻¹ v)
      have heq : (l * e * l⁻¹) v * v⁻¹ = l (e (l⁻¹ v) * (l⁻¹ v)⁻¹) := by
        simp [map_mul, map_inv]
      rw [heq]
      exact hpresY l hl _ h
    have h := KQ.mul_mem hconj (KQ.inv_mem (hDKQ he))
    exact h w
  have hElemL : CFSG.Quasithin.IsElemAbelian2 L :=
    isElemAbelian2_of_fixed_and_quotient hw2 hLY (fun l hl => hLKQ hl)
  have hLpg : IsPGroup 2 ↥L := E3.isPGroup_of_isElemAbelian2 hElemL
  have hpCoreL : pCoreOf 2 L = L := by
    refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 L) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) hLpg
  have hpc := CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal (K := L) (H := G) hLsub
  rw [hpCoreL, hpCore, inf_bot_eq] at hpc
  exact hLne hpc

end CFSG.LocalAnalysis.WeakClosure81
