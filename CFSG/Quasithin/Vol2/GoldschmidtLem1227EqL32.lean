module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCoordinates
public import CFSG.Quasithin.H13.L32NoIrrFourProof
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

namespace Lem1227Eq

@[expose] noncomputable def quotAct {A W : Type*} [Group A] [CommGroup W] (ρ : A →* MulAut W)
    (C : Subgroup W) (hC : ∀ a, C.map (ρ a).toMonoidHom = C) : A →* MulAut (W ⧸ C) where
  toFun a := QuotientGroup.congr C C (ρ a) (hC a)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H w =>
      show (QuotientGroup.mk ((ρ 1) w) : W ⧸ C) = QuotientGroup.mk w
      rw [map_one]
      rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H w =>
      show (QuotientGroup.mk ((ρ (a * b)) w) : W ⧸ C) = QuotientGroup.mk ((ρ a) ((ρ b) w))
      rw [map_mul]
      rfl

theorem quotAct_mk {A W : Type*} [Group A] [CommGroup W] (ρ : A →* MulAut W) (C : Subgroup W)
    (hC : ∀ a, C.map (ρ a).toMonoidHom = C) (a : A) (w : W) :
    quotAct ρ C hC a (QuotientGroup.mk w) = QuotientGroup.mk (ρ a w) := rfl

theorem quotAct_eq_one_iff {A W : Type*} [Group A] [CommGroup W] (ρ : A →* MulAut W)
    (C : Subgroup W) (hC : ∀ a, C.map (ρ a).toMonoidHom = C) (a : A) :
    quotAct ρ C hC a = 1 ↔ ∀ w : W, ρ a w * w⁻¹ ∈ C := by
  constructor
  · intro h w
    have h1 := congrArg (fun φ : MulAut (W ⧸ C) => φ (QuotientGroup.mk w)) h
    simp only [quotAct_mk, MulAut.one_apply] at h1
    have := (QuotientGroup.eq (s := C)).1 h1.symm
    simpa [mul_comm] using this
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [quotAct_mk, MulAut.one_apply]
      refine (QuotientGroup.eq (s := C)).2 ?_
      have := C.inv_mem (h w)
      simpa [mul_comm] using this

theorem isElementaryAbelian_quot {W : Type*} [CommGroup W] (hsq : ∀ w : W, w ^ 2 = 1)
    (C : Subgroup W) : IsElementaryAbelian 2 (W ⧸ C) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]


section Sec

variable {G : Type} [Group G] {K V : Subgroup G} [IsMulCommutative ↥V]

abbrev fixC (K V : Subgroup G) : Subgroup G := V ⊓ Subgroup.centralizer (K : Set G)

abbrev Iq (K V : Subgroup G) [IsMulCommutative ↥V] : Type := ↥V ⧸ (fixC K V).subgroupOf V

omit [IsMulCommutative ↥V] in
theorem map_actionOn_fixC {A : Subgroup G} (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hAC : A ≤ Subgroup.normalizer (fixC K V : Set G)) (a : ↥A) :
    ((fixC K V).subgroupOf V).map (A4.actionOn V A hAV a).toMonoidHom =
      (fixC K V).subgroupOf V := by
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hAC a.2) u).1 hu
  · intro hw
    refine ⟨A4.actionOn V A hAV a⁻¹ w, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hAC (a⁻¹).2) w).1 hw
    · show (A4.actionOn V A hAV a) ((A4.actionOn V A hAV a⁻¹) w) = w
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl

@[expose] noncomputable def secAct (A : Subgroup G) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hAC : A ≤ Subgroup.normalizer (fixC K V : Set G)) : ↥A →* MulAut (Iq K V) :=
  quotAct (A4.actionOn V A hAV) ((fixC K V).subgroupOf V) (map_actionOn_fixC hAV hAC)

theorem secAct_eq_one_iff {A : Subgroup G} (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hAC : A ≤ Subgroup.normalizer (fixC K V : Set G)) (a : ↥A) :
    secAct A hAV hAC a = 1 ↔
      ∀ v : ↥V, (a : G) * v * (a : G)⁻¹ * (v : G)⁻¹ ∈ fixC K V := by
  rw [secAct, quotAct_eq_one_iff]
  refine forall_congr' fun v => ?_
  rw [Subgroup.mem_subgroupOf]
  rfl

omit [IsMulCommutative ↥V] in
theorem conj_mem_fixC {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ fixC K V) :
    t * x * t⁻¹ ∈ fixC K V := by
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 htV x).1 (Subgroup.mem_inf.1 hx).1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : t⁻¹ * k * t ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htK) k).1 hk
  have h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 _ hk'
  calc k * (t * x * t⁻¹) = t * ((t⁻¹ * k * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * k * t)) * t⁻¹ := by rw [h]
    _ = t * x * t⁻¹ * k := by group

omit [IsMulCommutative ↥V] in
theorem mem_normalizer_fixC {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer (fixC K V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_fixC htV htK hx, fun hx => ?_⟩
  have := conj_mem_fixC (K := K) (V := V) (Subgroup.inv_mem _ htV) (Subgroup.inv_mem _ htK) hx
  simpa [mul_assoc] using this

end Sec


section Main

variable {G : Type} [Group G] {T K V : Subgroup G} [IsMulCommutative ↥V]

structure SL32Data (K V : Subgroup G) [IsMulCommutative ↥V] : Prop where
  normalizes : K ≤ Subgroup.normalizer (V : Set G)
  sq : ∀ v ∈ V, v ^ 2 = 1
  comm : ⁅V, K⁆ = V
  irr : ∀ J : Subgroup G, fixC K V ≤ J → J ≤ V → K ≤ Subgroup.normalizer (J : Set G) →
    J = fixC K V ∨ J = V
  o2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G)
  iso : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  card : Nat.card V = 8 ∨ Nat.card V = 16

namespace SL32Data

variable (d : SL32Data K V)

include d

theorem sq' : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (d.sq v v.2)

theorem le_stab : K ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (fixC K V : Set G) :=
  le_inf d.normalizes fun _ hk => mem_normalizer_fixC (d.normalizes hk) (Subgroup.le_normalizer hk)

@[expose] noncomputable def kappa : ↥K →* MulAut (Iq K V) :=
  (secAct (Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (fixC K V : Set G)) inf_le_left
    inf_le_right).comp (Subgroup.inclusion d.le_stab)

theorem kappa_eq_one_iff (k : ↥K) :
    d.kappa k = 1 ↔ ∀ v : ↥V, (k : G) * v * (k : G)⁻¹ * (v : G)⁻¹ ∈ fixC K V :=
  secAct_eq_one_iff inf_le_left inf_le_right (Subgroup.inclusion d.le_stab k)

theorem pCore_le_ker_kappa : CFSG.pCore 2 ↥K ≤ d.kappa.ker := by
  intro k hk
  rw [MonoidHom.mem_ker, kappa_eq_one_iff]
  intro v
  have hkc : (k : G) ∈ Subgroup.centralizer (V : Set G) :=
    d.o2 ((mem_pCore_iff_coe k).1 hk)
  have h1 := Subgroup.mem_centralizer_iff.1 hkc v v.2
  have h2 : (k : G) * v * (k : G)⁻¹ * (v : G)⁻¹ = 1 := by
    calc (k : G) * v * (k : G)⁻¹ * (v : G)⁻¹ = (v * k) * (k : G)⁻¹ * (v : G)⁻¹ := by rw [← h1]
      _ = 1 := by group
  rw [h2]
  exact (fixC K V).one_mem

@[expose] noncomputable def kappaBar : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (Iq K V) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥K) d.kappa d.pCore_le_ker_kappa

theorem kappaBar_mk (k : ↥K) : d.kappaBar (QuotientGroup.mk k) = d.kappa k := rfl

theorem simple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
  obtain ⟨e⟩ := d.iso
  have := isSimpleGroup_sl_zmodTwo (n := 3) le_rfl
  exact e.isSimpleGroup

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  rcases d.card with hc | hc <;>
    · have : Nat.card V = 1 := by rw [h]; exact Subgroup.card_bot
      omega

theorem not_le_centralizer : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
  intro h
  apply d.V_ne_bot
  rw [← d.comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)

theorem kappa_ne_one : d.kappa ≠ 1 := by
  intro h
  have hall : ∀ k : ↥K, ∀ v : ↥V, (k : G) * v * (k : G)⁻¹ * (v : G)⁻¹ ∈ fixC K V := fun k v =>
    (d.kappa_eq_one_iff k).1 (by rw [h]; rfl) v
  have hle : ⁅V, K⁆ ≤ fixC K V := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have := (fixC K V).inv_mem (hall ⟨k, hk⟩ ⟨v, hv⟩)
    simpa [commutatorElement_def, mul_assoc] using this
  rw [d.comm] at hle
  refine d.not_le_centralizer fun k hk => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.1 (hle hv).2 k hk)).symm

theorem kappaBar_injective : Function.Injective d.kappaBar := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have := d.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal d.kappaBar.ker with h | h
  · exact h
  · exfalso
    apply d.kappa_ne_one
    refine MonoidHom.ext fun k => ?_
    have hk : (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ d.kappaBar.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, kappaBar_mk] at hk
    exact hk

theorem card_K_bar : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 := by
  obtain ⟨e⟩ := d.iso
  rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two]

omit d in
theorem card_Iq_dvd : Nat.card (Iq K V) ∣ Nat.card V := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((fixC K V).subgroupOf V)
  exact ⟨_, by rw [h]⟩

variable [Finite G]

theorem factorial_ge : 168 ≤ (Nat.card (Iq K V)).factorial := by
  have hinj : Function.Injective (fun f : MulAut (Iq K V) => MulAut.toPerm (Iq K V) f) :=
    fun f g h => MulEquiv.ext fun x => congrArg (fun p : Equiv.Perm (Iq K V) => p x) h
  have h1 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≤ Nat.card (MulAut (Iq K V)) :=
    Nat.card_le_card_of_injective _ d.kappaBar_injective
  have h2 : Nat.card (MulAut (Iq K V)) ≤ Nat.card (Equiv.Perm (Iq K V)) :=
    Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card (Equiv.Perm (Iq K V)) = (Nat.card (Iq K V)).factorial := by
    classical
    have := Fintype.ofFinite (Iq K V)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
  rw [← h3, ← d.card_K_bar]
  exact h1.trans h2

theorem card_Iq : Nat.card (Iq K V) = 8 := by
  have hdvd := card_Iq_dvd (K := K) (V := V)
  have hfact := d.factorial_ge
  have hne1 : Nat.card (Iq K V) ≠ 1 := by
    intro h1
    have : Subsingleton (Iq K V) := (Nat.card_eq_one_iff_unique.1 h1).1
    apply d.kappa_ne_one
    exact MonoidHom.ext fun k => MulEquiv.ext fun x => Subsingleton.elim _ _
  have hn : Nat.card (Iq K V) = 8 ∨ Nat.card (Iq K V) = 16 := by
    have hle : Nat.card (Iq K V) ≤ 16 := by
      rcases d.card with hc | hc <;> rw [hc] at hdvd <;>
        exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
    generalize Nat.card (Iq K V) = n at hdvd hfact hne1 hle ⊢
    rcases d.card with hc | hc <;> rw [hc] at hdvd <;> interval_cases n <;>
      first | (left; rfl) | (right; rfl) | (exfalso; revert hne1 hdvd hfact; decide)
  rcases hn with h8 | h16
  · exact h8
  · exfalso
    have hV16 : Nat.card V = 16 := by
      rcases d.card with hc | hc
      · rw [hc, h16] at hdvd
        omega
      · exact hc
    have hC1 : Nat.card ((fixC K V).subgroupOf V) = 1 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((fixC K V).subgroupOf V)
      change Nat.card V = Nat.card (Iq K V) * Nat.card ((fixC K V).subgroupOf V) at h
      rw [hV16, h16] at h
      omega
    have hCbot : fixC K V = ⊥ := by
      have h0 := Subgroup.eq_bot_of_card_eq _ hC1
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥V) ∈ (fixC K V).subgroupOf V := hx
      rw [h0, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hx'
    obtain ⟨e⟩ := d.iso
    have := isSimpleGroup_sl_zmodTwo (n := 3) le_rfl
    obtain ⟨e'⟩ := nonempty_autOn_mulEquiv_of_simple d.normalizes d.o2 d.not_le_centralizer e
    obtain ⟨W, hW0, hWt, hWinv⟩ := l32NoIrrFour_holds ↥V d.sq' (by rw [hV16]; rfl) (autOn K V)
      ⟨e'⟩
    have hJK : K ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) :=
      le_normalizer_map_of_invariant d.normalizes hWinv
    rcases d.irr (W.map V.subtype) (by rw [hCbot]; exact bot_le) (Subgroup.map_subtype_le W)
        hJK with h | h
    · apply hW0
      rw [hCbot] at h
      exact (Subgroup.map_eq_bot_iff_of_injective W V.subtype_injective).1 h
    · apply hWt
      rw [eq_top_iff]
      intro w _
      have hw : (w : G) ∈ W.map V.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', hww'⟩ := hw
      rwa [← Subtype.ext hww']

theorem card_aut_Iq : Nat.card (MulAut (Iq K V)) = 168 := by
  have := isElementaryAbelian_quot d.sq' ((fixC K V).subgroupOf V)
  exact CFSG.ProperTwoGeneratedCore.ExceptionalEight.card_mulAut_eq_168 d.card_Iq

theorem range_kappa_eq_top : d.kappa.range = ⊤ := by
  have h1 : d.kappa.range = d.kappaBar.range := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨k, rfl⟩
  apply Subgroup.eq_top_of_card_eq
  rw [h1, d.card_aut_Iq]
  have : Nat.card d.kappaBar.range = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (Nat.card_congr (MonoidHom.ofInjective d.kappaBar_injective).toEquiv).symm
  rw [this, d.card_K_bar]

theorem exists_mul_mem_pCoreOf {T : Subgroup G} (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ∀ t ∈ T, ∃ k ∈ K, ∀ x ∈ K,
      (k⁻¹ * t) * x * (k⁻¹ * t)⁻¹ * x⁻¹ ∈ pCoreOf 2 K := by
  intro t ht
  set A : Subgroup G :=
    Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (fixC K V : Set G) with hA
  have hKA : K ≤ A := d.le_stab
  have htA : t ∈ A := ⟨hTV ht, mem_normalizer_fixC (hTV ht) (hTK ht)⟩
  let σ : ↥A →* MulAut (Iq K V) := secAct A inf_le_left inf_le_right
  have hσ : ∀ k : ↥K, d.kappa k = σ (Subgroup.inclusion hKA k) := fun k => rfl
  have hmem : σ ⟨t, htA⟩ ∈ d.kappa.range := by
    rw [d.range_kappa_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨k₀, hk₀⟩ := hmem
  refine ⟨k₀, k₀.2, fun x hx => ?_⟩
  let c : ↥A := (Subgroup.inclusion hKA k₀)⁻¹ * ⟨t, htA⟩
  have hc1 : σ c = 1 := by
    simp only [c, map_mul, map_inv]
    rw [← hσ, hk₀, inv_mul_cancel]
  let x' : ↥A := Subgroup.inclusion hKA ⟨x, hx⟩
  have hn1 : σ (c * x' * c⁻¹ * x'⁻¹) = 1 := by
    simp only [map_mul, map_inv, hc1, one_mul, inv_one, mul_one, mul_inv_cancel]
  have hnK : ((k₀ : G)⁻¹ * t) * x * ((k₀ : G)⁻¹ * t)⁻¹ * x⁻¹ ∈ K := by
    have hk : (k₀ : G)⁻¹ * t ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer k₀.2)) (hTK ht)
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 hk x).1 hx) (K.inv_mem hx)
  have hkn : d.kappa ⟨_, hnK⟩ = 1 := by
    rw [hσ]
    have : Subgroup.inclusion hKA
        ⟨((k₀ : G)⁻¹ * t) * x * ((k₀ : G)⁻¹ * t)⁻¹ * x⁻¹, hnK⟩ = c * x' * c⁻¹ * x'⁻¹ := by
      apply Subtype.ext
      simp [c, x']
    rw [this]
    exact hn1
  set n : ↥K := ⟨_, hnK⟩ with hn
  have hbar : (QuotientGroup.mk n : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
    d.kappaBar_injective (by rw [kappaBar_mk, hkn, map_one])
  exact (mem_pCore_iff_coe n).1 ((QuotientGroup.eq_one_iff n).1 hbar)

end SL32Data

end Main

end Lem1227Eq

end CFSG.Quasithin.H13
