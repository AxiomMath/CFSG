module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreA
public import CFSG.RankThree.GF2n.Stroth80.Sec78CV
public import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmegaTwo
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Sec
public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem natIrred_statedOmegaPlus_two91 {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) : NatIrred (StatedOmega (StatedQuadPlus 2 K)) := by
  intro S hS
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four h4
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  let E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)) :=
    ElemMatrixIso.ofStated (coe_quadPlus 2 K)
      (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)
  let a : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 1) 1
  have ha0 : a ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl 1)
    simp [a] at h1
  have hae : polar (quadPlus 2 K) (plusPair K (0 : Fin 2)).e a = 0 := by
    rw [plusPair_e, polar_single_inl_quadPlus]
    simp [a, Pi.single_apply]
  have haf : polar (quadPlus 2 K) (plusPair K (0 : Fin 2)).f a = 0 := by
    rw [plusPair_f, polar_single_inr_quadPlus]
    simp [a, Pi.single_apply]
  have hW : ∀ u w : Fin 2 ⊕ Fin 2 → K, ∀ x ∈ S, eichler (quadPlus 2 K) u w x ∈ S := by
    intro u w x hx
    let g : Gom (quadPlus 2 K) :=
      ⟨eichler (quadPlus 2 K) u w, eichler_mem_elementaryGroup (quadPlus 2 K) u w⟩
    have hA := hS (E.equiv.symm g).1 (E.equiv.symm g).2 x hx
    have happ := E.app (E.equiv.symm g) x
    rw [MulEquiv.apply_symm_apply] at happ
    rw [← happ] at hA
    exact hA
  exact submodule_eq_bot_or_top_of_eichler_invariant (plusPair K (0 : Fin 2)).Q_e
    (plusPair K (0 : Fin 2)).Q_f (plusPair K (0 : Fin 2)).polar_ef hQ ha0 hae haf hW

theorem sec9VtIrred91 {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {U : Subgroup G} (hZU : Z ≤ U) (hUV : U ≤ Vt M (LB M Q B) B Z t)
    (hRU : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ U, r * u * r⁻¹ ∈ U) :
    U = Z ∨ U = Vt M (LB M Q B) B Z t := by
  obtain ⟨K, fK, finK, hK, hrep⟩ := hs.plus4
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have h4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four h4
  exact hrep.eq_or_eq_of_invariant (natIrred_statedOmegaPlus_two91 h4)
    (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) hZU hUV hRU

theorem comm_Q91 (hc : Ctx M Q Z B) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ ∈ Z :=
  hc.hyp.toHyp79.comm_mem_V hx hy

theorem zconj91 (hc : Ctx M Q Z B) {g : G} (hg : g ∈ M) {z : G} (hz : z ∈ Z) :
    g * z * g⁻¹ ∈ Z :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg) z).mp hz

theorem comm_Z_Q91 (hc : Ctx M Q Z B) {x z : G} (hx : x ∈ Q) (hz : z ∈ Z) : x * z = z * x := by
  have := hc.conj_Z_of_mem_Q hx hz
  calc x * z = (x * z * x⁻¹) * x := by group
    _ = z * x := by rw [this]

theorem Rt_cent_Z91 (hc : Ctx M Q Z B) (t : G) {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) {z : G}
    (hz : z ∈ Z) : ρ * z * ρ⁻¹ = z := by
  have h := Subgroup.mem_centralizer_iff.mp (hc.Rt_le_H0 t hρ).2 z hz
  calc ρ * z * ρ⁻¹ = (ρ * z) * ρ⁻¹ := rfl
    _ = (z * ρ) * ρ⁻¹ := by rw [← h]
    _ = z := by group

theorem comm_conj_mem91 (hc : Ctx M Q Z B) {s ρ w : G} (hsM : s ∈ M) (hρM : ρ ∈ M)
    (hw : w ∈ Q) (hq : ⁅ρ⁻¹, s⁆ ∈ Q) :
    ⁅s, ρ * w * ρ⁻¹⁆ * (ρ * ⁅s, w⁆ * ρ⁻¹)⁻¹ ∈ Z := by
  set q₀ := ⁅ρ⁻¹, s⁆ with hq₀
  have hx : ⁅s, w⁆ ∈ Q := by
    have : ⁅s, w⁆ = (s * w * s⁻¹) * w⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact Q.mul_mem (conj_mem_Q91 hc hsM hw) (Q.inv_mem hw)
  have h1 : ⁅s, ρ * w * ρ⁻¹⁆ = ρ * ⁅q₀ * s, w⁆ * ρ⁻¹ := by
    simp only [hq₀, commutatorElement_def]; group
  have h2 : ⁅q₀ * s, w⁆ = q₀ * ⁅s, w⁆ * q₀⁻¹ * ⁅q₀, w⁆ := by
    simp only [commutatorElement_def]; group
  have h3 : q₀ * ⁅s, w⁆ * q₀⁻¹ = ⁅q₀, ⁅s, w⁆⁆ * ⁅s, w⁆ := by
    simp only [commutatorElement_def]; group
  have hc1 : ⁅q₀, ⁅s, w⁆⁆ ∈ Z := comm_Q91 hc hq hx
  have hc2 : ⁅q₀, w⁆ ∈ Z := comm_Q91 hc hq hw
  have h4 : ⁅q₀ * s, w⁆ * ⁅s, w⁆⁻¹ = ⁅q₀, ⁅s, w⁆⁆ * ⁅q₀, w⁆ := by
    rw [h2, h3]
    have hcomm := comm_Z_Q91 hc hx hc2
    calc ⁅q₀, ⁅s, w⁆⁆ * ⁅s, w⁆ * ⁅q₀, w⁆ * ⁅s, w⁆⁻¹
        = ⁅q₀, ⁅s, w⁆⁆ * (⁅s, w⁆ * ⁅q₀, w⁆) * ⁅s, w⁆⁻¹ := by group
      _ = ⁅q₀, ⁅s, w⁆⁆ * (⁅q₀, w⁆ * ⁅s, w⁆) * ⁅s, w⁆⁻¹ := by rw [hcomm]
      _ = ⁅q₀, ⁅s, w⁆⁆ * ⁅q₀, w⁆ := by group
  have h5 : ⁅s, ρ * w * ρ⁻¹⁆ * (ρ * ⁅s, w⁆ * ρ⁻¹)⁻¹ = ρ * (⁅q₀, ⁅s, w⁆⁆ * ⁅q₀, w⁆) * ρ⁻¹ := by
    rw [h1, ← h4]; group
  rw [h5]
  exact zconj91 hc hρM (Z.mul_mem hc1 hc2)

theorem comm_LB_QB91 (hc' : Ctx M Q Z B) {l p : G} (hl : l ∈ LB M Q B) (hp : p ∈ Q)
    (hpB : p ∈ QB B) : ⁅l, p⁆ ∈ Z ⊔ B := by
  obtain ⟨σ, hσ, y, hy, rfl⟩ := hc'.exists_mul_of_mem_LB hl
  have e : ⁅σ * y, p⁆ = (σ * ⁅y, p⁆ * σ⁻¹) * ⁅σ, p⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Z ⊔ B).mul_mem (Subgroup.mem_sup_left (zconj91 hc' hσ.2 (comm_Q91 hc' hy hp)))
    (Subgroup.mem_sup_right (hc'.comm_QB_le_B hσ.1 hpB))

@[expose] def nuHom91 {V W : Subgroup G} (s : G) (hWV : ∀ w ∈ W, ∀ v ∈ V, w * v = v * w)
    (hν : ∀ w ∈ W, ⁅s, w⁆ ∈ V) : ↥W →* G where
  toFun w := ⁅s, (w : G)⁆
  map_one' := by simp [commutatorElement_def]
  map_mul' a b := by
    have hc : (a : G) * ⁅s, (b : G)⁆ = ⁅s, (b : G)⁆ * (a : G) := hWV a a.2 _ (hν b b.2)
    show ⁅s, (a : G) * (b : G)⁆ = ⁅s, (a : G)⁆ * ⁅s, (b : G)⁆
    have e : ⁅s, (a : G) * (b : G)⁆ = ⁅s, (a : G)⁆ * ((a : G) * ⁅s, (b : G)⁆ * (a : G)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, hc]; group

theorem card_sup_le91 {H K : Subgroup G} (hH : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card ↥H * Nat.card ↥K := by
  have hsurj : Function.Surjective
      (fun p : ↥H × ↥K => (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
        ↥(H ⊔ K))) := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  calc Nat.card ↥(H ⊔ K) ≤ Nat.card (↥H × ↥K) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

theorem card_le_prod91 {V X Y : Subgroup G} (h : ∀ v ∈ V, ∃ x ∈ X, ∃ y ∈ Y, v = x * y) :
    Nat.card ↥V ≤ Nat.card ↥X * Nat.card ↥Y := by
  classical
  choose! x hx y hy hxy using h
  let f : ↥V → ↥X × ↥Y := fun v => (⟨x v, hx v v.2⟩, ⟨y v, hy v v.2⟩)
  have hf : Function.Injective f := by
    intro v v' h
    apply Subtype.ext
    have h1 : x v = x v' := congrArg (fun p => (p.1 : G)) h
    have h2 : y v = y v' := congrArg (fun p => (p.2 : G)) h
    rw [hxy v v.2, hxy v' v'.2, h1, h2]
  calc Nat.card ↥V ≤ Nat.card (↥X × ↥Y) := Nat.card_le_card_of_injective f hf
    _ = Nat.card ↥X * Nat.card ↥Y := Nat.card_prod _ _

theorem nu_mul91 {V W : Subgroup G} (s : G) (hWV : ∀ w ∈ W, ∀ v ∈ V, w * v = v * w)
    (hν : ∀ w ∈ W, ⁅s, w⁆ ∈ V) {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    ⁅s, a * b⁆ = ⁅s, a⁆ * ⁅s, b⁆ :=
  (nuHom91 s hWV hν).map_mul ⟨a, ha⟩ ⟨b, hb⟩

theorem nu_mem_sup91 {hc : Ctx M Q Z B} {t : G} {B' : Subgroup G}
    (hc' : Ctx M Q Z B') (hL'R : LB M Q B' ≤ Rt M (LB M Q B) t)
    (hB'V : B' ≤ Vt M (LB M Q B) B Z t)
    (h35' : CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G))
    (hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t))
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0)
    (hsN : s ∈ hc.CN t)
    (hν : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t)
    {p : G} (hp : p ∈ QB B' ⊓ Wt Q (Vt M (LB M Q B) B Z t)) :
    ⁅s, p⁆ ∈ B' ⊔ Z := by
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hpW : p ∈ Wt Q (Vt M (LB M Q B) B Z t) := hp.2
  have hpQ : p ∈ Q := hpW.1
  have hνV : ⁅s, p⁆ ∈ Vt M (LB M Q B) B Z t := hν p hpW
  have hmem : ⁅s, p⁆ ∈ CQt Q Z (LB M Q B') := by
    refine ⟨hVQ hνV, fun l hl => ?_⟩
    have hlR : l ∈ Rt M (LB M Q B) t := hL'R hl
    have hlM : l ∈ M := hc.Rt_le_M t hlR
    have hq : ⁅l⁻¹, s⁆ ∈ Q := by
      have := hZ0.comm_mem hsZ ((Rt M (LB M Q B) t).inv_mem hlR)
      rw [← commutatorElement_inv]
      exact Q.inv_mem this
    have hζ := comm_conj_mem91 hc hsM hlM hpQ hq
    have hlp : ⁅l, p⁆ ∈ Z ⊔ B' := comm_LB_QB91 hc' hl hpQ hp.1
    have hlpV : ⁅l, p⁆ ∈ Vt M (LB M Q B) B Z t := (sup_le hZV hB'V) hlp
    have hsc : ⁅s, ⁅l, p⁆⁆ ∈ Z := (Ctx.mem_CN.mp hsN).2 _ hlpV
    have hcomm : ⁅l, p⁆ * ⁅s, p⁆ = ⁅s, p⁆ * ⁅l, p⁆ :=
      (Om10.mul_comm_of_mem_Wt (hVW hνV) hlpV).symm
    have e2 : ⁅s, l * p * l⁻¹⁆ = ⁅s, ⁅l, p⁆⁆ * ⁅s, p⁆ := by
      have e : l * p * l⁻¹ = ⁅l, p⁆ * p := by simp only [commutatorElement_def]; group
      rw [e]
      have : ⁅s, ⁅l, p⁆ * p⁆ = ⁅s, ⁅l, p⁆⁆ * (⁅l, p⁆ * ⁅s, p⁆ * ⁅l, p⁆⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this, hcomm]; group
    set ζ₀ := ⁅s, l * p * l⁻¹⁆ * (l * ⁅s, p⁆ * l⁻¹)⁻¹ with hζ₀
    have e1 : l * ⁅s, p⁆ * l⁻¹ = ζ₀⁻¹ * (⁅s, ⁅l, p⁆⁆ * ⁅s, p⁆) := by
      rw [← e2, hζ₀]; group
    have : ⁅l, ⁅s, p⁆⁆ = ζ₀⁻¹ * ⁅s, ⁅l, p⁆⁆ := by
      calc ⁅l, ⁅s, p⁆⁆ = (l * ⁅s, p⁆ * l⁻¹) * ⁅s, p⁆⁻¹ := by simp only [commutatorElement_def]
        _ = ζ₀⁻¹ * (⁅s, ⁅l, p⁆⁆ * ⁅s, p⁆) * ⁅s, p⁆⁻¹ := by rw [e1]
        _ = ζ₀⁻¹ * ⁅s, ⁅l, p⁆⁆ := by group
    rw [this]
    exact Z.mul_mem (Z.inv_mem hζ) hsc
  rw [h35'] at hmem
  exact hmem

theorem comm_Wt_le_Z91 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hsZ : s ∈ Z0) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Z := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcr : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have h35A := hc.CQt_conj hrM h35
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]; exact le_sup_right
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hAV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 : r⁻¹ * x * r ∈ Vt M (LB M Q B) B Z t := hBV hx
    have := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hrR) _).mp h1
    have e : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rw [e] at this
    exact this
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7ctr_Vt_le_Wt h34 hc hs5
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hsN : s ∈ hc.CN t := isCentrePre_le_CN91 hs hZ0 hsZ
  obtain ⟨hdirect, hNW⟩ := h91b G M Q Z B hc n t hs r hr _ _ rfl rfl
  have hν : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t :=
    fun w hw => hNW s hsN w hw
  have hWV : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ∀ v ∈ Vt M (LB M Q B) B Z t, w * v = v * w :=
    fun w hw v hv => Om10.mul_comm_of_mem_Wt hw hv
  have hsV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅s, v⁆ ∈ Z := (Ctx.mem_CN.mp hsN).2
  let ν := nuHom91 (V := Vt M (LB M Q B) B Z t) (W := Wt Q (Vt M (LB M Q B) B Z t)) s hWV hν
  have hrangeV : ν.range ≤ Vt M (LB M Q B) B Z t := by
    rintro _ ⟨w, rfl⟩
    exact hν w w.2
  have hnormZ : ∀ y ∈ Vt M (LB M Q B) B Z t, y ∈ Subgroup.normalizer (Z : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun z hz => zconj91 hc (hQM (hVQ hy)) hz
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G, U = ν.range ⊔ Z := ⟨_, rfl⟩
  have hZU : Z ≤ U := by rw [hU]; exact le_sup_right
  have hUV : U ≤ Vt M (LB M Q B) B Z t := by rw [hU]; exact sup_le hrangeV hZV
  have hmemU : ∀ u ∈ U, ∃ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)), ∃ z ∈ Z,
      u = ⁅s, (w : G)⁆ * z := by
    intro u hu
    rw [hU] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (fun y hy => hnormZ y (hrangeV hy)) hu
    obtain ⟨w, rfl⟩ := hy
    exact ⟨w, z, hz, rfl⟩
  have hRU : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U := by
    intro ρ hρ u hu
    obtain ⟨w, z, hz, rfl⟩ := hmemU u hu
    have hρM : ρ ∈ M := hc.Rt_le_M t hρ
    have hq : ⁅ρ⁻¹, s⁆ ∈ Q := by
      have := hZ0.comm_mem hsZ ((Rt M (LB M Q B) t).inv_mem hρ)
      rw [← commutatorElement_inv]
      exact Q.inv_mem this
    have hζ := comm_conj_mem91 hc (hc.Rt_le_M t hsR) hρM (hWQ w.2) hq
    have hw' : ρ * (w : G) * ρ⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := sec9_conj_mem_Wt hc ht hρ w.2
    set ζ₀ := ⁅s, ρ * (w : G) * ρ⁻¹⁆ * (ρ * ⁅s, (w : G)⁆ * ρ⁻¹)⁻¹ with hζ₀
    have e : ρ * (⁅s, (w : G)⁆ * z) * ρ⁻¹ = ζ₀⁻¹ * ⁅s, ρ * (w : G) * ρ⁻¹⁆ * (ρ * z * ρ⁻¹) := by
      rw [hζ₀]; group
    rw [e]
    have hzρ : ρ * z * ρ⁻¹ ∈ Z := zconj91 hc hρM hz
    have hmemν : ⁅s, ρ * (w : G) * ρ⁻¹⁆ ∈ U := by
      rw [hU]
      exact Subgroup.mem_sup_left ⟨⟨_, hw'⟩, rfl⟩
    exact U.mul_mem (U.mul_mem (hZU (Z.inv_mem hζ)) hmemν) (hZU hzρ)
  rcases sec9VtIrred91 hs hZU hUV hRU with hUZ | hUVeq
  swap
  · exfalso
    obtain ⟨hVA₁, hA₁W, hVA₂, hA₂W, hsup, -⟩ := hdirect
    have hnormA : ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t) ≤ Subgroup.normalizer
        ((((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) : Subgroup G) :
          Set G) := by
      intro a ha
      refine Subgroup.mem_normalizer_fintype fun b hb => ?_
      have e : a * b * a⁻¹ = ⁅a, b⁆ * b := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (hVA₂ (hZV (comm_Q91 hc (hWQ (hA₁W ha)) (hWQ (hA₂W hb))))) hb
    have hdec : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ∃ p₁ ∈ QB (conjSubgroup r B) ⊓
        Wt Q (Vt M (LB M Q B) B Z t), ∃ p₂ ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
        ∃ v₁ ∈ Vt M (LB M Q B) B Z t, ∃ v₂ ∈ Vt M (LB M Q B) B Z t,
          w = (p₁ * v₁) * (p₂ * v₂) := by
      intro w hw
      have hw' : w ∈ ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
          Vt M (LB M Q B) B Z t) ⊔ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
          Vt M (LB M Q B) B Z t) := by rw [hsup]; exact hw
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormA hw'
      have hH : ∀ X : Subgroup G, X ≤ Wt Q (Vt M (LB M Q B) B Z t) →
          X ≤ Subgroup.normalizer ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G) := by
        intro X hX p hp
        refine Subgroup.mem_normalizer_fintype fun v hv => ?_
        have h1 := hWV p (hX hp) v hv
        have : p * v * p⁻¹ = v := by rw [h1]; group
        rw [this]; exact hv
      obtain ⟨p₁, hp₁, v₁, hv₁, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
        (hH _ inf_le_right) ha₁
      obtain ⟨p₂, hp₂, v₂, hv₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
        (hH _ inf_le_right) ha₂
      exact ⟨p₁, hp₁, p₂, hp₂, v₁, hv₁, v₂, hv₂, rfl⟩
    have hAB : ∀ v ∈ Vt M (LB M Q B) B Z t, ∃ x ∈ conjSubgroup r B ⊔ Z, ∃ y ∈ B ⊔ Z,
        v = x * y := by
      intro v hv
      have hvU : v ∈ U := hUVeq ▸ hv
      obtain ⟨w, z, hz, rfl⟩ := hmemU v hvU
      obtain ⟨p₁, hp₁, p₂, hp₂, v₁, hv₁, v₂, hv₂, hwe⟩ := hdec w w.2
      have hp₁W := hp₁.2
      have hp₂W := hp₂.2
      have hv₁W := hVW hv₁
      have hv₂W := hVW hv₂
      have hm1 : ⁅s, (p₁ * v₁) * (p₂ * v₂)⁆ =
          ⁅s, p₁⁆ * ⁅s, v₁⁆ * (⁅s, p₂⁆ * ⁅s, v₂⁆) := by
        rw [nu_mul91 s hWV hν (Subgroup.mul_mem _ hp₁W hv₁W) (Subgroup.mul_mem _ hp₂W hv₂W),
          nu_mul91 s hWV hν hp₁W hv₁W, nu_mul91 s hWV hν hp₂W hv₂W]
      have hz₁ : ⁅s, v₁⁆ ∈ Z := hsV v₁ hv₁
      have hz₂ : ⁅s, v₂⁆ ∈ Z := hsV v₂ hv₂
      have hA := nu_mem_sup91 (hc := hc) hcr hL'R hAV h35A hVW hZ0 hsZ hsN hν hp₁
      have hB' := nu_mem_sup91 (hc := hc) hc hLR hBV h35 hVW hZ0 hsZ hsN hν hp₂
      have hp₂Q : ⁅s, p₂⁆ ∈ Q := hVQ (hν p₂ hp₂W)
      have hcm : ⁅s, p₂⁆ * ⁅s, v₁⁆ = ⁅s, v₁⁆ * ⁅s, p₂⁆ := comm_Z_Q91 hc hp₂Q hz₁
      refine ⟨⁅s, p₁⁆, ?_, ⁅s, p₂⁆ * (⁅s, v₁⁆ * (⁅s, v₂⁆ * z)), ?_, ?_⟩
      · exact hA
      · exact (B ⊔ Z).mul_mem hB' (Subgroup.mem_sup_right (Z.mul_mem hz₁ (Z.mul_mem hz₂ hz)))
      · have e : ⁅s, (w : G)⁆ = ⁅s, p₁⁆ * ⁅s, v₁⁆ * (⁅s, p₂⁆ * ⁅s, v₂⁆) := by
          rw [← hm1, ← hwe]
        rw [e]
        calc ⁅s, p₁⁆ * ⁅s, v₁⁆ * (⁅s, p₂⁆ * ⁅s, v₂⁆) * z
            = ⁅s, p₁⁆ * (⁅s, v₁⁆ * ⁅s, p₂⁆) * (⁅s, v₂⁆ * z) := by group
          _ = ⁅s, p₁⁆ * (⁅s, p₂⁆ * ⁅s, v₁⁆) * (⁅s, v₂⁆ * z) := by rw [hcm]
          _ = ⁅s, p₁⁆ * (⁅s, p₂⁆ * (⁅s, v₁⁆ * (⁅s, v₂⁆ * z))) := by group
    have hcard := card_le_prod91 hAB
    have hBcard : Nat.card ↥B = Nat.card ↥Z := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup]
    have hAcard : Nat.card ↥(conjSubgroup r B) = Nat.card ↥Z := by
      rw [card_conjSubgroup, hBcard]
    have hnA : conjSubgroup r B ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
      Subgroup.mem_normalizer_fintype fun z hz => zconj91 hc (hQM (hVQ (hAV ha))) hz
    have hnB : B ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
      Subgroup.mem_normalizer_fintype fun z hz => zconj91 hc (hQM (hVQ (hBV ha))) hz
    have h1 := card_sup_le91 hnA
    have h2 := card_sup_le91 hnB
    rw [hAcard] at h1
    rw [hBcard] at h2
    have hV5 := hs.card_V
    have hq : 1 < Nat.card ↥Z := by
      have := hc.hyp.q4
      omega
    have h5 : Nat.card ↥Z ^ 4 < Nat.card ↥Z ^ 5 := Nat.pow_lt_pow_right hq (by norm_num)
    have : Nat.card ↥(Vt M (LB M Q B) B Z t) ≤ Nat.card ↥Z ^ 4 := by
      calc Nat.card ↥(Vt M (LB M Q B) B Z t)
          ≤ Nat.card ↥(conjSubgroup r B ⊔ Z) * Nat.card ↥(B ⊔ Z) := hcard
        _ ≤ (Nat.card ↥Z * Nat.card ↥Z) * (Nat.card ↥Z * Nat.card ↥Z) := Nat.mul_le_mul h1 h2
        _ = Nat.card ↥Z ^ 4 := by ring
    omega
  · intro w hw
    have : ⁅s, w⁆ ∈ U := by
      rw [hU]
      exact Subgroup.mem_sup_left ⟨⟨w, hw⟩, rfl⟩
    rwa [hUZ] at this

end HS9

end CFSG.RankThree.GF2n.Stroth80
