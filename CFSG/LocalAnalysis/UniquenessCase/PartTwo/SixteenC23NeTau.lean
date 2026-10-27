module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeY
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_tau_mem_Y {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) {v c : G} (hv : v ∈ V)
    (hc : c ∈ c23neQ2 K₁ K₂) : c * v * c⁻¹ * v⁻¹ ∈ c23neY V K₁ K₂ := by
  have h := Subgroup.commutator_mem_commutator hc hv
  rw [Subgroup.commutator_comm] at h
  simpa [c23neY, commutatorElement_def] using h

private theorem c23_omega_closure_top {U : Type*} [CommGroup U] [Finite U]
    {Y₁ Y₂ : Subgroup U} {A₁ A₂ Mb : Subgroup (MulAut U)} (h : C23Core Y₁ Y₂ A₁ A₂ Mb) :
    Subgroup.closure (c23Omega Y₁ Y₂ : Set U) = ⊤ := by
  classical
  set H : Subgroup U := Subgroup.closure (c23Omega Y₁ Y₂ : Set U) with hH
  have hcomp : ((H : Set U)ᶜ) ⊆ ((Y₁ : Set U) ∪ (Y₂ : Set U)) := by
    intro u hu
    by_contra hmem
    exact hu (Subgroup.subset_closure (by
      simp only [c23Omega, Set.mem_setOf_eq]
      simpa [Set.mem_union, not_or] using hmem))
  have hcardU : Nat.card U = 64 := c23_core_card_top h
  have hunion : ((Y₁ : Set U) ∪ (Y₂ : Set U)).ncard = 15 := by
    have h1 : (Y₁ : Set U).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact h.card₁
    have h2 : (Y₂ : Set U).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact h.card₂
    have hinter : ((Y₁ : Set U) ∩ (Y₂ : Set U)).ncard = 1 := by
      have hcoe : (Y₁ : Set U) ∩ (Y₂ : Set U) = ((Y₁ ⊓ Y₂ : Subgroup U) : Set U) :=
        (Subgroup.coe_inf Y₁ Y₂).symm
      rw [hcoe, h.inf_eq, Subgroup.coe_bot, Set.ncard_singleton]
    have hsum := Set.ncard_union_add_ncard_inter (Y₁ : Set U) (Y₂ : Set U)
    rw [hinter, h1, h2] at hsum
    omega
  have hcompcard : ((H : Set U)ᶜ).ncard ≤ 15 := by
    rw [← hunion]
    exact Set.ncard_le_ncard hcomp
  have hcompl : ((H : Set U)ᶜ).ncard = Nat.card U - Nat.card H := by
    rw [Set.ncard_compl]
    rfl
  have hHcard : 49 ≤ Nat.card H := by
    rw [hcompl, hcardU] at hcompcard
    omega
  have hdvd : Nat.card H ∣ Nat.card U := Subgroup.card_subgroup_dvd_card H
  rw [hcardU] at hdvd
  have hle : Nat.card H ≤ 64 := by
    rw [← hcardU]; exact Subgroup.card_le_card_group H
  have hH64 : Nat.card H = 64 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by rintro rfl; norm_num at hk
    have hk1 : k = 1 := by
      by_contra hk1
      have hk2 : 2 ≤ k := by omega
      nlinarith [hHcard, hle, hk, hk2]
    rw [hk1, mul_one] at hk
    exact hk.symm
  exact Subgroup.eq_top_of_card_eq H (by omega)

private theorem c23ne_preTil_imgTil_eq {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (h0U : V₀ ≤ U) (hUV : U ≤ V) :
    preTil V₀ V hV (imgTil V₀ V hV U) = U := by
  refine le_antisymm ?_ (le_trans (le_inf le_rfl hUV) (le_preTil_imgTil V₀ V hV U))
  intro g hg
  obtain ⟨x, hx, hxg⟩ := (mem_preTil V₀ V hV _).1 hg
  have hx' : mkTil V₀ V hV x ∈ imgTil V₀ V hV U := hxg
  obtain ⟨y, hyU, hyx⟩ := (mem_imgTil V₀ V hV U _).1 hx'
  have hxy : x.val * (y.val)⁻¹ ∈ V₀ := (mkTil_eq_iff V₀ V hV x y).1 hyx.symm
  have : x.val = (x.val * (y.val)⁻¹) * y.val := by group
  rw [← hx, this]
  exact U.mul_mem (h0U hxy) hyU

private theorem c23ne_tau_eq_of_mem_V₀ {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : G} {K₁ K₂ : Subgroup G}
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V) (hV₀V : V₀ ≤ V)
    {u u' : G} (hu : u ∈ V) (hu' : u' ∈ V) (h : u * u'⁻¹ ∈ V₀)
    {c : G} (hc : c ∈ c23neQ2 K₁ K₂) :
    c * u * c⁻¹ * u⁻¹ = c * u' * c⁻¹ * u'⁻¹ := by
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hZV₀ : c23neY V K₁ K₂ ≤ V₀ := c23ne_Y_le_V₀ hctx hM
  have hQL : c23neQ2 K₁ K₂ ≤ K₁ ⊔ K₂ :=
    sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans le_sup_left)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₂).trans le_sup_right)
  have hc0 : c ∈ centralizer (V₀ : Set G) := hctx.cent₀ (hQL hc)
  have hcu' : c * u' * c⁻¹ * u'⁻¹ ∈ V₀ := hZV₀ (c23ne_tau_mem_Y hctx hu' hc)
  set e : G := u * u'⁻¹ with he
  have he0 : e ∈ V₀ := by rw [he]; exact h
  have hu_eq : u = e * u' := by rw [he]; group
  have hce : c * e = e * c := (Subgroup.mem_centralizer_iff.1 hc0 e he0).symm
  have hce' : c * e * c⁻¹ = e := by rw [hce]; group
  have hcomm : e * (c * u' * c⁻¹ * u'⁻¹) = (c * u' * c⁻¹ * u'⁻¹) * e :=
    congrArg Subtype.val (hV.1.is_comm.comm ⟨e, hV₀V he0⟩ ⟨_, hV₀V hcu'⟩)
  calc c * u * c⁻¹ * u⁻¹
      = c * (e * u') * c⁻¹ * (e * u')⁻¹ := by rw [hu_eq]
    _ = e * (c * u' * c⁻¹ * u'⁻¹) * e⁻¹ := by
          rw [mul_inv_rev]
          calc c * (e * u') * c⁻¹ * (u'⁻¹ * e⁻¹)
              = (c * e * c⁻¹) * (c * u' * c⁻¹ * u'⁻¹) * e⁻¹ := by group
            _ = e * (c * u' * c⁻¹ * u'⁻¹) * e⁻¹ := by rw [hce']
    _ = c * u' * c⁻¹ * u'⁻¹ := by rw [hcomm]; group

private theorem c23ne_tau_conj_X {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ X : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) (hXL : X ≤ K₁ ⊔ K₂) {v q g : G} (hv : v ∈ V)
    (hq : q ∈ c23neQ2 K₁ K₂) (hg : g ∈ X) (hgv : g * v = v * g) :
    (g * q * g⁻¹) * v * (g * q * g⁻¹)⁻¹ * v⁻¹ = q * v * q⁻¹ * v⁻¹ := by
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hZV₀ : c23neY V K₁ K₂ ≤ V₀ := c23ne_Y_le_V₀ hctx hM
  have hq0 : q * v * q⁻¹ * v⁻¹ ∈ V₀ := hZV₀ (c23ne_tau_mem_Y hctx hv hq)
  have hg0 : g ∈ centralizer (V₀ : Set G) := hctx.cent₀ (hXL hg)
  have hgv' : g⁻¹ * v * g = v := by
    calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
      _ = g⁻¹ * (g * v) := by rw [← hgv]
      _ = v := by group
  have hgv_inv : g⁻¹ * v⁻¹ = v⁻¹ * g⁻¹ := by
    have h1 : g⁻¹ * v⁻¹ = (v * g)⁻¹ := (mul_inv_rev v g).symm
    rw [h1, ← hgv, mul_inv_rev]
  have hgc : g * (q * v * q⁻¹ * v⁻¹) * g⁻¹ = q * v * q⁻¹ * v⁻¹ := by
    have h := (Subgroup.mem_centralizer_iff.1 hg0 (q * v * q⁻¹ * v⁻¹) hq0).symm
    rw [h]; group
  calc (g * q * g⁻¹) * v * (g * q * g⁻¹)⁻¹ * v⁻¹
      = g * (q * (g⁻¹ * v * g) * q⁻¹) * g⁻¹ * v⁻¹ := by group
    _ = g * (q * v * q⁻¹) * g⁻¹ * v⁻¹ := by rw [hgv']
    _ = g * (q * v * q⁻¹ * v⁻¹) * g⁻¹ := by
          rw [show g * (q * v * q⁻¹) * g⁻¹ * v⁻¹
              = g * (q * v * q⁻¹) * (g⁻¹ * v⁻¹) from by group, hgv_inv]
          group
    _ = q * v * q⁻¹ * v⁻¹ := hgc

private theorem c23ne_tau_image_subset_of_generic {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : G} {K₁ K₂ : Subgroup G}
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V) (hV₀V : V₀ ≤ V)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V)
    (hΩv : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ∈
      c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)))
    (hΩw : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ∈
      c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x))) :
    ∀ c ∈ c23neQ2 K₁ K₂, ∃ c' ∈ c23neQ2 K₁ K₂,
      c' * v * c'⁻¹ * v⁻¹ = c * w * c⁻¹ * w⁻¹ := by
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hZV₀ : c23neY V K₁ K₂ ≤ V₀ := c23ne_Y_le_V₀ hctx hM
  have hLDM : K₁ ⊔ K₂ ≤ D.M :=
    sup_le (CFSG.Quasithin.A3.subnormal_le hctx.mem₁.1)
      (CFSG.Quasithin.A3.subnormal_le hctx.mem₂.1)
  have hLQ₂ : K₁ ⊔ K₂ ≤ normalizer (c23neQ2 K₁ K₂ : Set G) := by
    have h₁ : K₁ ⊔ K₂ ≤ normalizer (CFSG.Open.pCoreOf 2 K₁ : Set G) :=
      sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K₁)
        (hctx.norm₂.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K₁))
    have h₂ : K₁ ⊔ K₂ ≤ normalizer (CFSG.Open.pCoreOf 2 K₂ : Set G) :=
      sup_le (hctx.norm₁.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K₂))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K₂)
    refine (le_inf h₁ h₂).trans ?_
    simpa [c23neQ2] using
      Subgroup.inf_normalizer_le_normalizer_sup (CFSG.Open.pCoreOf 2 K₁) (CFSG.Open.pCoreOf 2 K₂)
  obtain ⟨a, ha, b, hb, hab⟩ := c23_omega_trans hctx.core hΩw hΩv
  have ha' : a ∈ barSub V₀ V hV K₁ := by rw [hctx.bar₁]; exact ha
  obtain ⟨g₁, hg₁K, hg₁a⟩ := (mem_barSub V₀ V hV K₁ a).1 ha'
  have hb' : b ∈ barSub V₀ V hV K₂ := by rw [hctx.bar₂]; exact hb
  obtain ⟨g₂, hg₂K, hg₂a⟩ := (mem_barSub V₀ V hV K₂ b).1 hb'
  let m : G := (g₁ : G) * (g₂ : G)
  have hmL : m ∈ K₁ ⊔ K₂ := mul_mem_sup hg₁K hg₂K
  have hmDM : m ∈ D.M := hLDM hmL
  have hφ : actTil V₀ V hV (g₁ * g₂) = a * b := by rw [map_mul, hg₁a, hg₂a]
  have hval : actTil V₀ V hV (g₁ * g₂) (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩))
      = mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) := by
    rw [hφ, MulAut.mul_apply]
    exact hab
  have hval' : mkTil V₀ V hV (actStab V₀ V hV (g₁ * g₂) (IntMod.mk hV ⟨w, hw⟩))
      = mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) := by
    rw [← actTil_mk]; exact hval
  have hmwV₀ : m * w * m⁻¹ * v⁻¹ ∈ V₀ := by
    have h := (mkTil_eq_iff V₀ V hV _ (IntMod.mk hV ⟨v, hv⟩)).1 hval'
    rw [actStab_apply_val] at h
    exact h
  have hmwV : m * w * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hM hmDM) w).1 hw
  intro c hc
  have hc'Q : m * c * m⁻¹ ∈ c23neQ2 K₁ K₂ :=
    (Subgroup.mem_normalizer_iff.1 (hLQ₂ hmL) c).1 hc
  refine ⟨m * c * m⁻¹, hc'Q, ?_⟩
  have hdep := c23ne_tau_eq_of_mem_V₀ hctx hMs hV₀V hmwV hv hmwV₀ hc'Q
  have hconj : (m * c * m⁻¹) * (m * w * m⁻¹) * (m * c * m⁻¹)⁻¹ * (m * w * m⁻¹)⁻¹
      = m * (c * w * c⁻¹ * w⁻¹) * m⁻¹ := by group
  have hcent : m * (c * w * c⁻¹ * w⁻¹) * m⁻¹ = c * w * c⁻¹ * w⁻¹ := by
    have hmem : c * w * c⁻¹ * w⁻¹ ∈ V₀ := hZV₀ (c23ne_tau_mem_Y hctx hw hc)
    have h := (Subgroup.mem_centralizer_iff.1 (hctx.cent₀ hmL) _ hmem).symm
    rw [h]; group
  rw [← hdep, hconj, hcent]

theorem c23ne_tau_surj {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ X : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V)
    (hV₀V : V₀ ≤ V) (hXsyl : CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂)) {z : IntMod V hV}
    (hΩ : mkTil V₀ V hV z ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)))
    {v : G} (hv : v ∈ V) (hvz : v * (z.val)⁻¹ ∈ V₀) (hvX : ∀ g ∈ X, g * v = v * g) :
    ∀ y ∈ c23neY V K₁ K₂, ∃ c ∈ c23neQ2 K₁ K₂ ⊓ centralizer (X : Set G), c * v * c⁻¹ * v⁻¹ = y := by
  intro y hy
  let Q₂ : Subgroup G := c23neQ2 K₁ K₂
  let Z : Subgroup G := c23neY V K₁ K₂
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hZV₀ : Z ≤ V₀ := c23ne_Y_le_V₀ hctx hM
  have hZV : Z ≤ V := hZV₀.trans hV₀V
  have hQL : Q₂ ≤ K₁ ⊔ K₂ :=
    sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans le_sup_left)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₂).trans le_sup_right)
  have hLQ₂ : K₁ ⊔ K₂ ≤ normalizer (Q₂ : Set G) := by
    have h₁ : K₁ ⊔ K₂ ≤ normalizer (CFSG.Open.pCoreOf 2 K₁ : Set G) :=
      sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K₁)
        (hctx.norm₂.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K₁))
    have h₂ : K₁ ⊔ K₂ ≤ normalizer (CFSG.Open.pCoreOf 2 K₂ : Set G) :=
      sup_le (hctx.norm₁.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K₂))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K₂)
    have h := (le_inf h₁ h₂).trans (Subgroup.inf_normalizer_le_normalizer_sup
      (CFSG.Open.pCoreOf 2 K₁) (CFSG.Open.pCoreOf 2 K₂))
    simpa [Q₂, c23neQ2] using h
  have hXQ₂ : X ≤ normalizer (Q₂ : Set G) := hXsyl.le.trans hLQ₂
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg (fun x : ↥V => (x : G)) (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI hZcomm : IsMulCommutative ↥Z := ⟨⟨fun a b => by
    apply Subtype.ext
    exact hVcomm a.1 (hZV a.2) b.1 (hZV b.2)⟩⟩
  let τ : ↥Q₂ →* ↥Z :=
  { toFun := fun c => ⟨(c : G) * v * (c : G)⁻¹ * v⁻¹, c23ne_tau_mem_Y hctx hv c.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := fun c c' => by
      apply Subtype.ext
      set h : G := (c' : G) * v * (c' : G)⁻¹ * v⁻¹ with hh
      have hh0 : h ∈ V₀ := hZV₀ (c23ne_tau_mem_Y hctx hv c'.2)
      have hce : (c : G) * h = h * (c : G) :=
        (Subgroup.mem_centralizer_iff.1 (hctx.cent₀ (hQL c.2)) h hh0).symm
      have hce' : (c : G) * h * (c : G)⁻¹ = h := by rw [hce]; group
      calc ((c : G) * (c' : G)) * v * ((c : G) * (c' : G))⁻¹ * v⁻¹
          = (c : G) * ((c' : G) * v * (c' : G)⁻¹) * (c : G)⁻¹ * v⁻¹ := by group
        _ = (c : G) * (h * v) * (c : G)⁻¹ * v⁻¹ := by
              rw [show (c' : G) * v * (c' : G)⁻¹ = h * v from by rw [hh]; group]
        _ = (c : G) * h * (c : G)⁻¹ * ((c : G) * v * (c : G)⁻¹ * v⁻¹) := by group
        _ = h * ((c : G) * v * (c : G)⁻¹ * v⁻¹) := by rw [hce']
        _ = ((c : G) * v * (c : G)⁻¹ * v⁻¹) * h :=
              (hVcomm _ (hZV (c23ne_tau_mem_Y hctx hv c.2)) _ (hV₀V hh0)).symm
        _ = ((c : G) * v * (c : G)⁻¹ * v⁻¹) * ((c' : G) * v * (c' : G)⁻¹ * v⁻¹) := by
              rw [hh] }
  let S : Subgroup G := τ.range.map Z.subtype
  have hmemS : ∀ u : G, u ∈ S ↔ ∃ c : ↥Q₂, (c : G) * v * (c : G)⁻¹ * v⁻¹ = u := by
    intro u
    unfold S
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hz
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨τ c, ⟨c, rfl⟩, rfl⟩
  have hSZ : S ≤ Z := by
    intro u hu
    obtain ⟨c, rfl⟩ := (hmemS u).1 hu
    exact c23ne_tau_mem_Y hctx hv c.2
  have hSV₀ : S ≤ V₀ := hSZ.trans hZV₀
  let T : Subgroup G :=
  { carrier := {u | u ∈ V ∧ ∀ c : G, c ∈ Q₂ → c * u * c⁻¹ * u⁻¹ ∈ S}
    one_mem' := by
      refine ⟨V.one_mem, ?_⟩
      intro c hc
      have h1 : c * 1 * c⁻¹ * 1⁻¹ = 1 := by group
      rw [h1]
      exact S.one_mem
    mul_mem' := by
      intro a b ha hb
      refine ⟨V.mul_mem ha.1 hb.1, ?_⟩
      intro c hc
      have hca : c * a * c⁻¹ * a⁻¹ ∈ S := ha.2 c hc
      have hcb : c * b * c⁻¹ * b⁻¹ ∈ S := hb.2 c hc
      have hcb0 : c * b * c⁻¹ * b⁻¹ ∈ V₀ := hSV₀ hcb
      have hcomm : a * (c * b * c⁻¹ * b⁻¹) * a⁻¹ = c * b * c⁻¹ * b⁻¹ := by
        have h := hVcomm a ha.1 (c * b * c⁻¹ * b⁻¹) (hV₀V hcb0)
        rw [h]; group
      have heq : c * (a * b) * c⁻¹ * (a * b)⁻¹
          = (c * a * c⁻¹ * a⁻¹) * (c * b * c⁻¹ * b⁻¹) := by
        calc c * (a * b) * c⁻¹ * (a * b)⁻¹
            = (c * a * c⁻¹ * a⁻¹) * (a * (c * b * c⁻¹ * b⁻¹) * a⁻¹) := by group
          _ = (c * a * c⁻¹ * a⁻¹) * (c * b * c⁻¹ * b⁻¹) := by rw [hcomm]
      rw [heq]
      exact S.mul_mem hca hcb
    inv_mem' := by
      intro a ha
      refine ⟨V.inv_mem ha.1, ?_⟩
      intro c hc
      have hca : c * a * c⁻¹ * a⁻¹ ∈ S := ha.2 c hc
      have hca0 : c * a * c⁻¹ * a⁻¹ ∈ V₀ := hSV₀ hca
      simp only [inv_inv]
      have heq : c * a⁻¹ * c⁻¹ * a = (c * a * c⁻¹ * a⁻¹)⁻¹ := by
        have h1 : c * a⁻¹ * c⁻¹ * a = a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [h1]
        have hcomm : a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a = (c * a * c⁻¹ * a⁻¹)⁻¹ := by
          have h := hVcomm a⁻¹ (V.inv_mem ha.1) ((c * a * c⁻¹ * a⁻¹)⁻¹)
            (hV₀V (V₀.inv_mem hca0))
          rw [h]; group
        exact hcomm
      rw [heq]
      exact S.inv_mem hca }
  have hV₀T : V₀ ≤ T := by
    intro e he
    refine ⟨hV₀V he, ?_⟩
    intro c hc
    have hce : c * e * c⁻¹ * e⁻¹ = 1 := by
      have h := Subgroup.mem_centralizer_iff.1 (hctx.cent₀ (hQL hc)) e he
      rw [← h]; group
    rw [hce]
    exact S.one_mem
  have hΩv : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ∈
      c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) := by
    rw [show mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) = mkTil V₀ V hV z
        from (mkTil_eq_iff V₀ V hV _ _).2 hvz]
    exact hΩ
  have hgenT : ∀ (w : G) (hw : w ∈ V),
      mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ∈
        c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) → w ∈ T := by
    intro w hw hΩw
    refine ⟨hw, ?_⟩
    intro c hc
    rw [hmemS]
    obtain ⟨c', hc'Q, hc'eq⟩ :=
      c23ne_tau_image_subset_of_generic hctx hMs hV₀V hv hw hΩv hΩw c hc
    exact ⟨⟨c', hc'Q⟩, hc'eq⟩
  let Gens : Set G := {w | ∃ hw : w ∈ V,
    mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ∈
      c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x))}
  let H : Subgroup G := Subgroup.closure Gens
  have hHV : H ≤ V := by
    rw [Subgroup.closure_le]
    rintro w ⟨hw, -⟩
    exact hw
  have hHT : H ≤ T := by
    rw [Subgroup.closure_le]
    rintro w ⟨hw, hΩw⟩
    exact hgenT w hw hΩw
  have hUH : V₀ ⊔ H ≤ T := sup_le hV₀T hHT
  have hΩsub : c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x))
      ⊆ imgTil V₀ V hV (V₀ ⊔ H) := by
    intro q hq
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    have hxV : x.val ∈ V := x.2
    have hxG : x.val ∈ Gens := by
      refine ⟨hxV, ?_⟩
      have hxeq : IntMod.mk hV ⟨x.val, hxV⟩ = x := Subtype.ext rfl
      rw [hxeq]; exact hq
    have hxH : x.val ∈ H := Subgroup.subset_closure hxG
    exact (mem_imgTil V₀ V hV (V₀ ⊔ H) _).2
      ⟨x, (le_sup_right : H ≤ V₀ ⊔ H) hxH, rfl⟩
  have himg : imgTil V₀ V hV (V₀ ⊔ H) = ⊤ := by
    rw [eq_top_iff]
    have hle : Subgroup.closure
        (c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) : Set (Vtil V₀ V hV))
        ≤ imgTil V₀ V hV (V₀ ⊔ H) := by
      rw [Subgroup.closure_le]
      exact hΩsub
    rwa [c23_omega_closure_top hctx.core] at hle
  have hpre : preTil V₀ V hV (imgTil V₀ V hV (V₀ ⊔ H)) = V₀ ⊔ H :=
    c23ne_preTil_imgTil_eq hV le_sup_left (sup_le hV₀V hHV)
  have hVeq : V₀ ⊔ H = V := by rw [← hpre, himg, preTil_top]
  have hVT : V ≤ T := hVeq ▸ hUH
  have hYS : Z ≤ S := by
    change ⁅V, c23neQ2 K₁ K₂⁆ ≤ S
    rw [Subgroup.commutator_le]
    intro u hu c hc
    have huT : u ∈ T := hVT hu
    have hcu : c * u * c⁻¹ * u⁻¹ ∈ S := huT.2 c hc
    change u * c * u⁻¹ * c⁻¹ ∈ S
    have heq : u * c * u⁻¹ * c⁻¹ = (c * u * c⁻¹ * u⁻¹)⁻¹ := by group
    rw [heq]
    exact S.inv_mem hcu
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 3 (Nat.card Q₂) := by
    obtain ⟨k, hk⟩ := hctx.q2_pgroup.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  have hprod := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_product
    3 Nat.prime_three X Q₂ hXsyl.isPGroup hXQ₂ hcop
  have hAQ : (⁅Q₂, X⁆ : Subgroup G) ≤ Q₂ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hb' : b * a⁻¹ * b⁻¹ ∈ Q₂ :=
      (Subgroup.mem_normalizer_iff.1 (hXQ₂ hb) a⁻¹).1 (Q₂.inv_mem ha)
    rw [commutatorElement_def]
    simpa [mul_assoc] using Q₂.mul_mem ha hb'
  let K : Subgroup G := (τ.ker).map Q₂.subtype
  have hAK : (⁅Q₂, X⁆ : Subgroup G) ≤ K := by
    rw [Subgroup.commutator_le]
    intro q hq g hg
    have hmem : ⁅q, g⁆ ∈ Q₂ := by
      have hgq : g * q⁻¹ * g⁻¹ ∈ Q₂ :=
        (Subgroup.mem_normalizer_iff.1 (hXQ₂ hg) q⁻¹).1 (Q₂.inv_mem hq)
      rw [commutatorElement_def]
      simpa [mul_assoc] using Q₂.mul_mem hq hgq
    refine Subgroup.mem_map.mpr ⟨⟨⁅q, g⁆, hmem⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hconj : τ ⟨g * q * g⁻¹, (Subgroup.mem_normalizer_iff.1 (hXQ₂ hg) q).1 hq⟩
        = τ ⟨q, hq⟩ := by
      apply Subtype.ext
      exact c23ne_tau_conj_X hctx hMs hXsyl.le hv hq hg (hvX g hg)
    have hgq : ⁅g, q⁆ ∈ Q₂ := by
      have h1 : g * q * g⁻¹ ∈ Q₂ := (Subgroup.mem_normalizer_iff.1 (hXQ₂ hg) q).1 hq
      rw [commutatorElement_def]
      simpa [mul_assoc] using Q₂.mul_mem h1 (Q₂.inv_mem hq)
    have hτgq : τ ⟨⁅g, q⁆, hgq⟩ = 1 := by
      have hgq' : g * q * g⁻¹ ∈ Q₂ := (Subgroup.mem_normalizer_iff.1 (hXQ₂ hg) q).1 hq
      have heq : (⟨⁅g, q⁆, hgq⟩ : ↥Q₂)
          = ⟨g * q * g⁻¹, hgq'⟩ * ⟨q⁻¹, Q₂.inv_mem hq⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      have hqinv : (⟨q⁻¹, Q₂.inv_mem hq⟩ : ↥Q₂) = (⟨q, hq⟩ : ↥Q₂)⁻¹ := Subtype.ext rfl
      rw [heq, map_mul, hconj, hqinv, map_inv]
      group
    have heq2 : (⟨⁅q, g⁆, hmem⟩ : ↥Q₂) = (⟨⁅g, q⁆, hgq⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_inv]
      rw [commutatorElement_inv]
    rw [heq2, map_inv, hτgq, inv_one]
  have hyS : y ∈ S := hYS hy
  obtain ⟨qtilde, hqy⟩ := (hmemS y).1 hyS
  set q : G := (qtilde : G) with hq_def
  have hqQ₂ : q ∈ Q₂ := qtilde.2
  have hqy' : q * v * q⁻¹ * v⁻¹ = y := by rw [hq_def]; exact hqy
  have hqAC : q ∈ CFSG.SignalizerFunctor.Helpers.subgroupProduct (⁅Q₂, X⁆ : Subgroup G)
      (Q₂ ⊓ centralizer (X : Set G)) := by
    rw [hprod]
    exact hqQ₂
  obtain ⟨d, hdA, c, hcC, hdc⟩ := Set.mem_mul.1 hqAC
  have hdQ₂ : d ∈ Q₂ := hAQ hdA
  have hdK : d ∈ K := hAK hdA
  obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.1 hdK
  have hk1 : τ k = 1 := MonoidHom.mem_ker.1 hk
  have hτd : d * v * d⁻¹ * v⁻¹ = 1 := by
    have h : ((τ k : ↥Z) : G) = 1 := congrArg Subtype.val hk1
    have h2 : ((τ k : ↥Z) : G) = d * v * d⁻¹ * v⁻¹ := by
      change (k : G) * v * (k : G)⁻¹ * v⁻¹ = d * v * d⁻¹ * v⁻¹
      rw [show (k : G) = d from hkval]
    rwa [h2] at h
  have hcQ₂ : c ∈ Q₂ := hcC.1
  have hτc_eq : q * v * q⁻¹ * v⁻¹ = c * v * c⁻¹ * v⁻¹ := by
    have hcommd : d * (c * v * c⁻¹ * v⁻¹) * d⁻¹ = c * v * c⁻¹ * v⁻¹ := by
      have hmem : c * v * c⁻¹ * v⁻¹ ∈ V₀ := hZV₀ (c23ne_tau_mem_Y hctx hv hcQ₂)
      have h := (Subgroup.mem_centralizer_iff.1 (hctx.cent₀ (hQL hdQ₂)) _ hmem).symm
      rw [h]; group
    calc q * v * q⁻¹ * v⁻¹
        = (d * c) * v * (d * c)⁻¹ * v⁻¹ := by rw [hdc]
      _ = (d * v * d⁻¹ * v⁻¹) * (c * v * c⁻¹ * v⁻¹) := by
            rw [mul_inv_rev]
            calc (d * c) * v * (c⁻¹ * d⁻¹) * v⁻¹
                = d * (c * v * c⁻¹ * v⁻¹) * d⁻¹ * (d * v * d⁻¹ * v⁻¹) := by group
              _ = (c * v * c⁻¹ * v⁻¹) * (d * v * d⁻¹ * v⁻¹) := by rw [hcommd]
              _ = (d * v * d⁻¹ * v⁻¹) * (c * v * c⁻¹ * v⁻¹) :=
                    hVcomm (c * v * c⁻¹ * v⁻¹) (hZV (c23ne_tau_mem_Y hctx hv hcQ₂))
                      (d * v * d⁻¹ * v⁻¹) (hZV (c23ne_tau_mem_Y hctx hv hdQ₂))
      _ = c * v * c⁻¹ * v⁻¹ := by rw [hτd]; group
  exact ⟨c, hcC, by rw [← hτc_eq, hqy']⟩

theorem c23ne_tau_le {V₀ V Y KK : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀V : V₀ ≤ V)
    (hYV₀ : Y ≤ V₀) (hKK : KK ≤ centralizer (V₀ : Set G))
    (hgood : Y = V₀ ∨ C23NeSplit V₀ V Y KK) {v : G} (hv : v ∈ V) {n : G} (hn : n ∈ KK)
    (hnv : n * v * n⁻¹ * v⁻¹ ∈ V₀) : n * v * n⁻¹ * v⁻¹ ∈ Y := by
  rcases hgood with hY | ⟨C, hYC, hCV, hCinf, hCsup, hCinv⟩
  · rwa [hY]
  · haveI : IsMulCommutative ↥V := hV.1
    have hsupV : (C.subgroupOf V) ⊔ (V₀.subgroupOf V) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hCV hV₀V, hCsup, Subgroup.subgroupOf_self]
    have hvtop : (⟨v, hv⟩ : ↥V) ∈ (C.subgroupOf V) ⊔ (V₀.subgroupOf V) := by
      rw [hsupV]; trivial
    obtain ⟨c, hcC, e, he0, hce⟩ := Subgroup.mem_sup_of_normal_right.1 hvtop
    have hcCG : (c : G) ∈ C := hcC
    have he0G : (e : G) ∈ V₀ := he0
    have hprod : (c : G) * (e : G) = v := congrArg Subtype.val hce
    have hne : n * (e : G) = (e : G) * n :=
      (Subgroup.mem_centralizer_iff.1 (hKK hn) (e : G) he0G).symm
    have heq : n * v * n⁻¹ * v⁻¹ = n * (c : G) * n⁻¹ * (c : G)⁻¹ := by
      rw [← hprod]
      have h1 : (e : G) * n⁻¹ = n⁻¹ * (e : G) := (Commute.inv_right (Commute.symm hne)).eq
      calc n * ((c : G) * (e : G)) * n⁻¹ * ((c : G) * (e : G))⁻¹
          = n * (c : G) * ((e : G) * n⁻¹) * (e : G)⁻¹ * (c : G)⁻¹ := by group
        _ = n * (c : G) * (n⁻¹ * (e : G)) * (e : G)⁻¹ * (c : G)⁻¹ := by rw [h1]
        _ = n * (c : G) * n⁻¹ * (c : G)⁻¹ := by group
    have hmemC : n * (c : G) * n⁻¹ * (c : G)⁻¹ ∈ C := by
      have h1 : n * (c : G) * n⁻¹ ∈ C := hCinv n hn (c : G) hcCG
      simpa [mul_assoc] using C.mul_mem h1 (C.inv_mem hcCG)
    have hmem0 : n * (c : G) * n⁻¹ * (c : G)⁻¹ ∈ V₀ := by rw [← heq]; exact hnv
    rw [← hCinf, heq]
    exact Subgroup.mem_inf.2 ⟨hmemC, hmem0⟩

theorem c23ne_aut_cond {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ X : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V)
    (hV₀V : V₀ ≤ V)
    (hgood : c23neY V K₁ K₂ = V₀ ∨ C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂))
    (hXsyl : CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂)) {z : IntMod V hV}
    (hΩ : mkTil V₀ V hV z ∈ c23Omega (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)))
    (hzX : ∀ g ∈ X, g * z.val = z.val * g)
    (hzN : ∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z.val * n⁻¹ * (z.val)⁻¹ ∈ V₀)
    {v : G} (hv : v ∈ V) (hvz : v * (z.val)⁻¹ ∈ V₀) :
    ∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (centralizer ({v} : Set G) ⊓ (K₁ ⊔ K₂)) ⊓ normalizer (X : Set G),
        ∀ g ∈ X, m * g * m⁻¹ = n * g * n⁻¹ := by
  intro n hn
  obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.1 hn
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hL₀ : ∀ k ∈ K₁ ⊔ K₂, ∀ e ∈ V₀, k * e = e * k := fun k hk e he =>
    (Subgroup.mem_centralizer_iff.1 (hctx.cent₀ hk) e he).symm
  set e : G := v * (z.val)⁻¹ with he_def
  have hv_eq : v = e * z.val := by rw [he_def]; group
  have hvX : ∀ g ∈ X, g * v = v * g := by
    intro g hg
    have hgL : g ∈ K₁ ⊔ K₂ := hXsyl.le hg
    rw [hv_eq]
    calc g * (e * z.val) = (g * e) * z.val := by group
      _ = (e * g) * z.val := by rw [hL₀ g hgL e hvz]
      _ = e * (g * z.val) := by group
      _ = e * (z.val * g) := by rw [hzX g hg]
      _ = (e * z.val) * g := by group
  set τ : G := n * v * n⁻¹ * v⁻¹ with hτ_def
  have hτV₀ : τ ∈ V₀ := by
    have h1 : τ = e * (n * z.val * n⁻¹ * (z.val)⁻¹) * e⁻¹ := by
      have h2 : n * e = e * n := hL₀ n hnL e hvz
      calc τ = n * (e * z.val) * n⁻¹ * (e * z.val)⁻¹ := by rw [hτ_def, ← hv_eq]
        _ = (n * e) * z.val * n⁻¹ * (z.val)⁻¹ * e⁻¹ := by group
        _ = (e * n) * z.val * n⁻¹ * (z.val)⁻¹ * e⁻¹ := by rw [h2]
        _ = e * (n * z.val * n⁻¹ * (z.val)⁻¹) * e⁻¹ := by group
    rw [h1]
    exact V₀.mul_mem (V₀.mul_mem hvz (hzN n hn)) (V₀.inv_mem hvz)
  have hYV₀ : c23neY V K₁ K₂ ≤ V₀ := c23ne_Y_le_V₀ hctx hM
  have hτY : τ ∈ c23neY V K₁ K₂ :=
    c23ne_tau_le hV hV₀V hYV₀ hctx.cent₀ hgood hv hnL hτV₀
  obtain ⟨c, hcQ, hcτ⟩ := c23ne_tau_surj hctx hMs hV₀V hXsyl hΩ hv hvz hvX τ⁻¹
    ((c23neY V K₁ K₂).inv_mem hτY)
  obtain ⟨hcQ', hcC⟩ := Subgroup.mem_inf.1 hcQ
  have hcL : c ∈ K₁ ⊔ K₂ := by
    have : c ∈ F11.CTilde D.M V₀ V ⊓ (K₁ ⊔ K₂) := hctx.ker ▸ hcQ'
    exact (Subgroup.mem_inf.1 this).2
  have hcN : c ∈ normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ hcC
  have hnv : n * v * n⁻¹ = τ * v := by rw [hτ_def]; group
  have hcv : c * v * c⁻¹ = τ⁻¹ * v := by
    calc c * v * c⁻¹ = (c * v * c⁻¹ * v⁻¹) * v := by group
      _ = τ⁻¹ * v := by rw [hcτ]
  have hcτ' : c * τ * c⁻¹ = τ := by
    have := hL₀ c hcL τ hτV₀
    calc c * τ * c⁻¹ = (τ * c) * c⁻¹ := by rw [this]
      _ = τ := by group
  refine ⟨c * n, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, (K₁ ⊔ K₂).mul_mem hcL hnL⟩,
    (normalizer (X : Set G)).mul_mem hcN hnN⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h : (c * n) * v * (c * n)⁻¹ = v := by
      calc (c * n) * v * (c * n)⁻¹ = c * (n * v * n⁻¹) * c⁻¹ := by group
        _ = c * (τ * v) * c⁻¹ := by rw [hnv]
        _ = (c * τ * c⁻¹) * (c * v * c⁻¹) := by group
        _ = τ * (τ⁻¹ * v) := by rw [hcτ', hcv]
        _ = v := by group
    calc (c * n) * v = (c * n) * v * (c * n)⁻¹ * (c * n) := by group
      _ = v * (c * n) := by rw [h]
  · intro g hg
    have hng : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hnN g).1 hg
    have hcg : (n * g * n⁻¹) * c = c * (n * g * n⁻¹) := Subgroup.mem_centralizer_iff.1 hcC _ hng
    calc (c * n) * g * (c * n)⁻¹ = c * (n * g * n⁻¹) * c⁻¹ := by group
      _ = ((n * g * n⁻¹) * c) * c⁻¹ := by rw [hcg]
      _ = n * g * n⁻¹ := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
