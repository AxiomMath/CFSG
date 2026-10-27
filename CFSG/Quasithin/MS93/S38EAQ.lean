module

public import CFSG.Quasithin.MS93.S38EAMap
public import CFSG.Quasithin.MS93.Sec2Three
public import CFSG.Quasithin.MS93.SkHyp

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.MS93.S38E
open scoped commutatorElement

variable {U₀ : Type} [Group U₀]

theorem le_normalizer_of_conj {S H : Subgroup U₀} (h : ∀ g ∈ S, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    S ≤ Subgroup.normalizer (H : Set U₀) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hx
  simpa [mul_assoc] using this

variable {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ} (hS : EndSetup V G₀ Lt Tb Qa E e)
  (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

section BQ

include hS in
theorem mem_bSub_iff (v : ↥V) :
    (v : U₀) ∈ bSub V Lt ↔ (QuotientGroup.mk v : VQ hS.cls2) ∈ fixV (kQ hS) := by
  constructor
  · rintro ⟨-, hv⟩ _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl
    rw [vqAct_mk, QuotientGroup.eq, mem_zc]
    intro w
    have hc := hv _ hl
    have e : (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) = ⁅(v : U₀), (l : U₀)⁆ := by
      have hvc : (v : U₀) * ⁅(v : U₀), (l : U₀)⁆ = ⁅(v : U₀), (l : U₀)⁆ * v :=
        Subgroup.mem_centralizer_iff.mp hc v v.2
      have e1 : (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) =
          (v : U₀)⁻¹ * ⁅(v : U₀), (l : U₀)⁆ * v := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjV_apply_coe, commutatorElement_def]
        group
      rw [e1, mul_assoc, ← hvc, inv_mul_cancel_left]
    apply Subtype.ext
    show (w : U₀) * (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) =
      (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) * w
    rw [e]
    exact Subgroup.mem_centralizer_iff.mp hc w w.2
  · intro hv
    refine ⟨v.2, fun l hl => ?_⟩
    have h1 := hv (vqAct hS.cls2 hS.nV ⟨l, hS.lt_le hl⟩)
      ⟨⟨l, hS.lt_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    rw [vqAct_mk, QuotientGroup.eq, mem_zc] at h1
    set z : ↥V := (conjV hS.nV ⟨l, hS.lt_le hl⟩ v)⁻¹ * v with hz
    have hz' : (z : U₀) = (l * (v : U₀) * l⁻¹)⁻¹ * v := rfl
    have hzc : (z : U₀) ∈ Subgroup.centralizer (V : Set U₀) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (h1 ⟨w, hw⟩)
    have hzv : (v : U₀) * z = z * v := Subgroup.mem_centralizer_iff.mp hzc v v.2
    have e : ⁅(v : U₀), l⁆ = z := by
      have : (v : U₀) * z * (v : U₀)⁻¹ = z := by rw [hzv, mul_inv_cancel_right]
      rw [← this, hz', commutatorElement_def]
      group
    rw [e]
    exact hzc

include hS in
theorem le_bSub_of_commutator_le {X : Subgroup U₀} (hXV : X ≤ V)
    (hXn : Lt ≤ Subgroup.normalizer (X : Set U₀))
    (h : ∀ x ∈ X, ∀ l ∈ Lt, ⁅x, l⁆ ∈ bSub V Lt) : X ≤ bSub V Lt := by
  set Xb : Subgroup (VQ hS.cls2) := (X.subgroupOf V).map (QuotientGroup.mk' (zc hS.cls2))
  have hXs : Stab (kQ hS) Xb := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl hx
    refine ⟨conjV hS.nV l x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, conjV_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hXn hl) x).mp hx
  have h1 : ∀ k ∈ kQ hS, ∀ w ∈ Xb, k w * w⁻¹ ∈ fixV (kQ hS) := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl hx
    have hlx : (l : U₀) * x * (l : U₀)⁻¹ * (x : U₀)⁻¹ ∈ bSub V Lt := by
      have := (bSub V Lt).inv_mem (h x hx l hl)
      rw [← commutatorElement_inv] at this
      simpa [commutatorElement_def, mul_assoc] using this
    have e : vqAct hS.cls2 hS.nV l (QuotientGroup.mk' (zc hS.cls2) x) *
        (QuotientGroup.mk' (zc hS.cls2) x)⁻¹ =
        QuotientGroup.mk (⟨(l : U₀) * x * (l : U₀)⁻¹ * (x : U₀)⁻¹,
          bSub_le hlx⟩ : ↥V) := by
      rw [QuotientGroup.mk'_apply, vqAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
    rw [e]
    exact (mem_bSub_iff hS _).mp hlx
  have h2 : ∀ k ∈ kQ hS, ∀ w ∈ fixV (kQ hS), k w * w⁻¹ ∈ (⊥ : Subgroup (VQ hS.cls2)) :=
    fun k hk w hw => by rw [Subgroup.mem_bot, mul_inv_eq_one]; exact hw k hk
  have h3 := perfect_trivial_of_two_step (kQ_perfect hS) hXs (stab_bot _) h1 h2
  intro x hx
  have hxV := hXV hx
  rw [show x = ((⟨x, hxV⟩ : ↥V) : U₀) from rfl, mem_bSub_iff hS]
  intro k hk
  have := h3 k hk _ ⟨⟨x, hxV⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rwa [Subgroup.mem_bot, mul_inv_eq_one] at this

end BQ

section Step7

variable {Vb : Subgroup U₀} (hVb : Vb ≤ V) (hTbVb : Tb ≤ Subgroup.normalizer (Vb : Set U₀))
  (hgen : ∀ K : Subgroup U₀, G₀ ≤ Subgroup.normalizer (K : Set U₀) → Vb ≤ K → V ≤ K)
include hVb hTbVb hgen

include hS in
theorem le_v0_sup : V ≤ ⁅V, Lt⁆ ⊔ Vb := by
  refine hgen _ ?_ le_sup_right
  rw [hS.sup]
  refine sup_le ?_ ?_
  · rw [sup_comm]
    refine le_normalizer_sup_of_commutator_le (hS.lt_le.trans (le_normalizer_v0 hS)) ?_
    exact (Subgroup.commutator_mono hVb le_rfl).trans le_sup_right
  · exact le_normalizer_sup (hS.tb_le.trans (le_normalizer_v0 hS)) hTbVb

include hS in
theorem commutator_qa_le
    (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
      (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
    (he : 2 ≤ e ∧ e ≤ 4) (h4 : (fixV (hS.eS lam hlam1)).index = 4)
    (hVbab : ⁅Vb, Vb⁆ = ⊥) (hVQa : V ≤ Qa) (hQaTb : Qa ≤ Tb) (hnab : ⁅V, V⁆ ≠ ⊥) :
    ⁅V, Qa⁆ ≤ Subgroup.centralizer (V : Set U₀) := by
  have : Finite ↥G₀ := hS.finite
  set V₀ := ⁅V, Lt⁆ with hV₀
  set B := bSub V Lt with hB
  set C := Subgroup.centralizer (V : Set U₀) with hC
  have hQaG : Qa ≤ G₀ := hS.qa_le
  have hVQ_le : ⁅V, Qa⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQaG.trans hS.nV)
  have hnVQ : G₀ ≤ Subgroup.normalizer ((⁅V, Qa⁆ : Subgroup U₀) : Set U₀) :=
    le_normalizer_comm_of hS.nV hS.nQa
  have hnC : G₀ ≤ Subgroup.normalizer (C : Set U₀) := le_normalizer_centralizer hS.nV
  have hnZ : G₀ ≤ Subgroup.normalizer ((V ⊓ C : Subgroup U₀) : Set U₀) :=
    le_normalizer_inf hS.nV hnC
  have hnB : G₀ ≤ Subgroup.normalizer (B : Set U₀) := le_normalizer_bSub hS
  have hZB : V ⊓ C ≤ B := by
    rintro z ⟨hzV, hzC⟩
    refine ⟨hzV, fun l hl => ?_⟩
    have h1 : l * z⁻¹ * l⁻¹ ∈ V ⊓ C :=
      (Subgroup.mem_normalizer_iff.mp (hnZ (hS.lt_le hl)) _).mp
        ((V ⊓ C).inv_mem ⟨hzV, hzC⟩)
    have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact C.mul_mem hzC h1.2
  have hBZ : ∀ x ∈ B, ∀ l ∈ Lt, ⁅x, l⁆ ∈ V ⊓ C := by
    intro x hx l hl
    refine ⟨?_, hx.2 l hl⟩
    exact hS.commV_le (Subgroup.commutator_mem_commutator (bSub_le hx) hl)
  by_cases hA : ⁅V, Qa⁆ ≤ B
  ·
    set Y' := ⁅Vb, Qa⁆ ⊔ (V ⊓ C) with hY'
    have hY'B : Y' ≤ B := sup_le ((Subgroup.commutator_mono hVb le_rfl).trans hA) hZB
    have hnY' : G₀ ≤ Subgroup.normalizer (Y' : Set U₀) := by
      rw [hS.sup]
      refine sup_le ?_ ?_
      · refine le_normalizer_of_conj fun l hl y hy => ?_
        have hc : ⁅l, y⁆ ∈ V ⊓ C := by
          rw [← commutatorElement_inv]
          exact (V ⊓ C).inv_mem (hBZ y (hY'B hy) l hl)
        have e : l * y * l⁻¹ = ⁅l, y⁆ * y := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact Y'.mul_mem (Subgroup.mem_sup_right hc) hy
      · exact le_normalizer_sup (le_normalizer_comm_of hTbVb (hS.tb_le.trans hS.nQa))
          (hS.tb_le.trans hnZ)
    let K' : Subgroup U₀ :=
      { carrier := {v | v ∈ V ∧ ∀ q ∈ Qa, ⁅v, q⁆ ∈ Y'}
        one_mem' := ⟨V.one_mem, fun q _ => by
          rw [commutatorElement_one_left]
          exact Y'.one_mem⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨V.mul_mem ha hb, fun q hq => ?_⟩
          have e : ⁅a * b, q⁆ = (a * ⁅b, q⁆ * a⁻¹) * ⁅a, q⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact Y'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnY' (hS.v_le ha)) _).mp
            (hb' q hq)) (ha' q hq)
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨V.inv_mem ha, fun q hq => ?_⟩
          have e : ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp (hnY' (hS.v_le (V.inv_mem ha))) _).mp
            (Y'.inv_mem (ha' q hq)) }
    have hK'n : G₀ ≤ Subgroup.normalizer (K' : Set U₀) := by
      refine le_normalizer_of_conj fun g hg v hv => ?_
      refine ⟨conj_mem_of_le_normalizer hS.nV hg hv.1, fun q hq => ?_⟩
      have hq' : g⁻¹ * q * g ∈ Qa := by
        have := (Subgroup.mem_normalizer_iff.mp (hS.nQa (G₀.inv_mem hg)) q).mp hq
        simpa using this
      have e : ⁅g * v * g⁻¹, q⁆ = g * ⁅v, g⁻¹ * q * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hnY' hg) _).mp (hv.2 _ hq')
    have hVbK' : Vb ≤ K' := fun w hw =>
      ⟨hVb hw, fun q hq => Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hw hq)⟩
    have hVK' := hgen K' hK'n hVbK'
    have hVQY : ⁅V, Qa⁆ ≤ Y' :=
      Subgroup.commutator_le.mpr fun v hv q hq => (hVK' hv).2 q hq
    have hVbc : Vb ≤ Subgroup.centralizer (Vb : Set U₀) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVbab
    have hY'c : Y' ≤ Subgroup.centralizer (Vb : Set U₀) := by
      refine sup_le ?_ ?_
      · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQaTb.trans hTbVb)).trans hVbc
      · exact inf_le_right.trans (Subgroup.centralizer_le hVb)
    have hV : V ≤ Subgroup.centralizer ((⁅V, Qa⁆ : Subgroup U₀) : Set U₀) := by
      refine hgen _ (le_normalizer_centralizer hnVQ) ?_
      rw [Subgroup.le_centralizer_iff]
      exact hVQY.trans hY'c
    rwa [Subgroup.le_centralizer_iff] at hV
  ·
    exfalso
    set X := ⁅V, Qa⁆ ⊔ B with hX
    have hXV : X ≤ V := sup_le hVQ_le bSub_le
    have hnX : G₀ ≤ Subgroup.normalizer (X : Set U₀) := le_normalizer_sup hnVQ hnB
    set J : Subgroup (hS.SM lam hlam1) := (X.subgroupOf V₀).map (sMap hS lam hlam1) with hJdef
    have hJ : ∀ g : ↥G₀, ∀ s ∈ J, hS.secRho lam hlam1 g s ∈ J := by
      rintro g _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
      refine ⟨⟨(g : U₀) * x * (g : U₀)⁻¹, conj_mem_of_le_normalizer (le_normalizer_v0 hS) g.2 x.2⟩,
        ?_, sMap_conj hS lam hlam1 g x⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hnX g.2) _).mp hx
    rcases hS.irr_SM lam hlam1 hirr J hJ with hJ0 | hJ1
    ·
      apply hA
      refine le_sup_left.trans (le_bSub_of_commutator_le hS hXV (hS.lt_le.trans hnX) ?_)
      intro x hx l hl
      have hxl : ⁅x, l⁆ ∈ V₀ := Subgroup.commutator_mem_commutator (hXV hx) hl
      have hxlX : ⁅x, l⁆ ∈ X := by
        have h1 : l * x⁻¹ * l⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hnX (hS.lt_le hl)) _).mp (X.inv_mem hx)
        have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact X.mul_mem hx h1
      have h1 : sMap hS lam hlam1 ⟨_, hxl⟩ ∈ J :=
        ⟨⟨_, hxl⟩, Subgroup.mem_subgroupOf.mpr hxlX, rfl⟩
      rw [hJ0, Subgroup.mem_bot, sMap_eq_one_iff] at h1
      exact mem_bSub_of_fix hS lam hlam1 he h4 _ h1
    ·
      have hV₀X : V₀ ≤ X := by
        intro v hv
        have hs : sMap hS lam hlam1 ⟨v, hv⟩ ∈ J := by rw [hJ1]; exact Subgroup.mem_top _
        obtain ⟨x, hx, hxv⟩ := hs
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
        have h1 : sMap hS lam hlam1 (x⁻¹ * ⟨v, hv⟩) = 1 := by
          rw [map_mul, map_inv, hxv, inv_mul_cancel]
        rw [sMap_eq_one_iff] at h1
        have h2 := mem_bSub_of_fix hS lam hlam1 he h4 _ h1
        have e : v = (x : U₀) * ((x⁻¹ * ⟨v, hv⟩ : ↥V₀) : U₀) := by simp
        rw [e]
        exact X.mul_mem hx (Subgroup.mem_sup_right h2)
      set Z' := ⁅V, Qa⁆ ⊔ (V ⊓ C) with hZ'
      have hnZ' : G₀ ≤ Subgroup.normalizer (Z' : Set U₀) := le_normalizer_sup hnVQ hnZ
      let T' : Subgroup U₀ :=
        { carrier := {x | x ∈ V ∧ ∀ l ∈ Lt, ⁅x, l⁆ ∈ Z'}
          one_mem' := ⟨V.one_mem, fun l _ => by
            rw [commutatorElement_one_left]
            exact Z'.one_mem⟩
          mul_mem' := by
            rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
            refine ⟨V.mul_mem ha hb, fun l hl => ?_⟩
            have e : ⁅a * b, l⁆ = (a * ⁅b, l⁆ * a⁻¹) * ⁅a, l⁆ := by
              simp only [commutatorElement_def]
              group
            rw [e]
            exact Z'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnZ' (hS.v_le ha)) _).mp
              (hb' l hl)) (ha' l hl)
          inv_mem' := by
            rintro a ⟨ha, ha'⟩
            refine ⟨V.inv_mem ha, fun l hl => ?_⟩
            have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a⁻¹⁻¹ := by
              simp only [commutatorElement_def]
              group
            rw [e]
            exact (Subgroup.mem_normalizer_iff.mp (hnZ' (hS.v_le (V.inv_mem ha))) _).mp
              (Z'.inv_mem (ha' l hl)) }
      have hXT : X ≤ T' := by
        refine sup_le (fun x hx => ⟨hVQ_le hx, fun l hl => ?_⟩) (fun x hx => ⟨hx.1, fun l hl =>
          Subgroup.mem_sup_right (hBZ x hx l hl)⟩)
        refine Subgroup.mem_sup_left ?_
        rw [commutatorElement_def]
        have h1 : l * x⁻¹ * l⁻¹ ∈ ⁅V, Qa⁆ :=
          (Subgroup.mem_normalizer_iff.mp (hnVQ (hS.lt_le hl)) _).mp (Subgroup.inv_mem _ hx)
        have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hx h1
      have hV₀Z : V₀ ≤ Z' :=
        calc V₀ = ⁅V₀, Lt⁆ := (commutator_v0_lt hS).symm
          _ ≤ Z' := Subgroup.commutator_le.mpr fun x hx l hl => (hXT (hV₀X hx)).2 l hl
      set X' := (V ⊓ C) ⊔ Vb with hX'
      have hX'V : X' ≤ V := sup_le inf_le_left hVb
      have hVX' : V ≤ X' ⊔ ⁅V, Qa⁆ := by
        refine (le_v0_sup hS hVb hTbVb hgen).trans (sup_le ?_ ?_)
        · refine hV₀Z.trans (sup_le le_sup_right ?_)
          exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left
      have hfinQ : Finite ↥Qa :=
        Finite.of_injective _ (Subgroup.inclusion_injective hQaG)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnil : Group.IsNilpotent ↥Qa := hS.qa2.isNilpotent
      have hnX' : Qa ≤ Subgroup.normalizer (X' : Set U₀) :=
        le_normalizer_sup (hQaG.trans hnZ) (hQaTb.trans hTbVb)
      have hVeq : V = X' :=
        eq_of_le_sup_commutator hnil (hX'V.trans hVQa) hVQa le_rfl hnX' hX'V hVX'
      apply hnab
      have hX'c : X' ≤ Subgroup.centralizer (X' : Set U₀) := by
        refine sup_le ?_ ?_
        · exact inf_le_right.trans (Subgroup.centralizer_le hX'V)
        · rw [← Subgroup.le_centralizer_iff]
          refine sup_le ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVbab)
          exact inf_le_right.trans (Subgroup.centralizer_le hVb)
      rw [eq_bot_iff]
      calc ⁅V, V⁆ ≤ ⁅X', X'⁆ := Subgroup.commutator_mono hVeq.le hVeq.le
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hX'c

end Step7

end CFSG.Quasithin.MS93.S38EA
