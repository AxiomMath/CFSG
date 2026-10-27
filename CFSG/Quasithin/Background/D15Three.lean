module

public import CFSG.Quasithin.Background.D15Twelve
public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.Vol2.Ch3Sec1D12

public section

namespace CFSG.Quasithin.D15Proof

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

@[expose] def D125 (G₂ T U : Subgroup G) : Prop :=
  ∀ L N : Subgroup G, IsChiefStep G₂ U L N → ¬ IsCentralStep G₂ L N →
    ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ⁅⁅N, A⁆, A⁆ ≤ L →
      (centralizerMod L A N).relIndex A ≤ (centralizerMod L N A).relIndex N

omit [Finite G] in
theorem commSeries_autOn_two_eq_bot {A V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : ⁅⁅V, A⁆, A⁆ = ⊥) :
    @commSeries V (commGroupOfElemAbelian hV) (autOn A V) 2 = ⊥ := by
  let _ := commGroupOfElemAbelian hV
  have h0 : ∀ w ∈ commSeries (autOn A V) 0, (w : G) ∈ V := fun w _ => w.2
  have h1 : ∀ w ∈ commSeries (autOn A V) 1, (w : G) ∈ ⁅V, A⁆ :=
    fun _ hw => EmptyFaithfulMultiple.coe_mem_commutator_of_mem_commSub hV h0 hw
  have h2 : ∀ w ∈ commSeries (autOn A V) 2, (w : G) ∈ ⁅⁅V, A⁆, A⁆ :=
    fun _ hw => EmptyFaithfulMultiple.coe_mem_commutator_of_mem_commSub hV h1 hw
  refine eq_bot_iff.mpr fun w hw => ?_
  have hw2 := h2 w hw
  rw [h, Subgroup.mem_bot] at hw2
  exact Subgroup.mem_bot.mpr (Subtype.ext hw2)

theorem qInt_le_two_of {A H V : Subgroup G} (hV : IsElemAbelian 2 V) (hAH : A ≤ H)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hA : IsElemAbelian 2 A)
    (hquad : ⁅⁅V, A⁆, A⁆ = ⊥) (hnc : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hidx : (Subgroup.centralizer (A : Set G)).relIndex V ≤
      ((Subgroup.centralizer (V : Set G)).relIndex A) ^ 2) :
    qInt H V hV ≤ 2 := by
  let _ := commGroupOfElemAbelian hV
  have hne : autOn A V ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hAN hnc
  have hel : IsElemAbelian2 (autOn A V) := isElemAbelian2_autOn hV hA hAN
  have hcard : Nat.card (autOn A V) = (Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [card_autOn_eq_relIndex hAN, Subgroup.inf_relIndex_left]
  have hfix : Nat.card (fixV (autOn A V)) =
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := card_fixV_autOn_eq hV hAN
  have hindex : (fixV (autOn A V)).index = (Subgroup.centralizer (A : Set G)).relIndex V := by
    have e1 := Subgroup.card_mul_index (fixV (autOn A V))
    have e2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
    rw [inf_eq_left.mpr inf_le_left, Subgroup.inf_relIndex_left] at e2
    rw [hfix] at e1
    have hpos : 0 < Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
    have e3 : Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
        (fixV (autOn A V)).index = Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
          (Subgroup.centralizer (A : Set G)).relIndex V := by
      rw [e1, mul_comm, e2]
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  have hb : Nat.card (autOn A V) = 2 ^ rk (autOn A V) :=
    card_eq_two_pow_of_isPGroup hel.isPGroup
  have hrk : 0 < rk (autOn A V) := hel.rk_pos hne
  have h2a : 2 ^ rkIdx (fixV (autOn A V)) ≤ 2 ^ (2 * rk (autOn A V)) := by
    calc 2 ^ rkIdx (fixV (autOn A V)) ≤ (fixV (autOn A V)).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
            pow_padicValNat_dvd
      _ = (Subgroup.centralizer (A : Set G)).relIndex V := hindex
      _ ≤ ((Subgroup.centralizer (V : Set G)).relIndex A) ^ 2 := hidx
      _ = 2 ^ (2 * rk (autOn A V)) := by rw [← hcard, hb, ← pow_mul, mul_comm]
  have hle : rkIdx (fixV (autOn A V)) ≤ 2 * rk (autOn A V) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h2a
  show kq (autOn H V) 2 ≤ ((2 : ℚ) : WithTop ℚ)
  refine kq_le_iff.mpr ⟨autOn A V, ⟨autOn_le_autOn V hAH, hne, hel⟩,
    commSeries_autOn_two_eq_bot hV hquad, ?_⟩
  unfold rAV
  have hrkq : (0 : ℚ) < rk (autOn A V) := by exact_mod_cast hrk
  rw [div_le_iff₀ hrkq]
  exact_mod_cast hle

theorem sq_relIndex_lt_of_not_qInt_le_two {G₁ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G)) (hq : ¬ qInt G₁ V hV ≤ 2) {E : Subgroup G}
    (hEG₁ : E ≤ G₁) (hE : IsElemAbelian 2 E) (hquad : ⁅⁅V, E⁆, E⁆ = ⊥)
    (hnc : ¬ E ≤ Subgroup.centralizer (V : Set G)) :
    ((Subgroup.centralizer (V : Set G)).relIndex E) ^ 2 <
      (Subgroup.centralizer (E : Set G)).relIndex V := by
  by_contra hle
  push Not at hle
  exact hq (qInt_le_two_of hV hEG₁ (hEG₁.trans hG₁V) hE hquad hnc hle)

omit [Finite G] in
theorem relIndex_conj_lt {G₁ V R₂ : Subgroup G}
    (hq : ∀ E₀ : Subgroup G, E₀ ≤ G₁ → IsElemAbelian 2 E₀ → ⁅⁅V, E₀⁆, E₀⁆ = ⊥ →
      ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ 2 <
        (Subgroup.centralizer (E₀ : Set G)).relIndex V)
    (hR₂G₁ : R₂ ≤ G₁) {g : G} (hg : g ∈ Subgroup.normalizer (R₂ : Set G)) {E : Subgroup G}
    (hER₂ : E ≤ R₂) (hE : IsElemAbelian 2 E) (hquad : ⁅⁅cjSub g V, E⁆, E⁆ = ⊥)
    (hnc : ¬ E ≤ Subgroup.centralizer (cjSub g V : Set G)) :
    ((Subgroup.centralizer (cjSub g V : Set G)).relIndex E) ^ 2 <
      (Subgroup.centralizer (E : Set G)).relIndex (cjSub g V) := by
  have hE₀R₂ : cjSub g⁻¹ E ≤ R₂ := cjSub_le (Subgroup.inv_mem _ hg) hER₂
  have hquad₀ : ⁅⁅V, cjSub g⁻¹ E⁆, cjSub g⁻¹ E⁆ = ⊥ := by
    have e : (⁅⁅cjSub g V, E⁆, E⁆).map (MulAut.conj g⁻¹).toMonoidHom =
        ⁅⁅V, cjSub g⁻¹ E⁆, cjSub g⁻¹ E⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
      have h1 : (cjSub g V).map (MulAut.conj g⁻¹).toMonoidHom = V := cjSub_inv_cjSub g V
      rw [h1]
      rfl
    rw [← e, hquad, Subgroup.map_bot]
  have hnc₀ : ¬ cjSub g⁻¹ E ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hnc
    have := cjSub_mono (g := g) hle
    rwa [cjSub_cjSub_inv, cjSub_centralizer] at this
  have h := hq _ (hE₀R₂.trans hR₂G₁) (isElemAbelian_cjSub hE) hquad₀ hnc₀
  have r1 : (cjSub g (Subgroup.centralizer (V : Set G))).relIndex (cjSub g (cjSub g⁻¹ E)) =
      (Subgroup.centralizer (V : Set G)).relIndex (cjSub g⁻¹ E) :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have r2 : (cjSub g (Subgroup.centralizer (cjSub g⁻¹ E : Set G))).relIndex (cjSub g V) =
      (Subgroup.centralizer (cjSub g⁻¹ E : Set G)).relIndex V :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  rw [cjSub_centralizer, cjSub_cjSub_inv] at r1 r2
  rw [r1, r2]
  exact h

omit [Finite G] in
theorem cjSub_le_conjClosure {V H : Subgroup G} {h : G} (hh : h ∈ H) :
    cjSub h V ≤ conjClosure V H := by
  intro x hx
  rw [mem_cjSub] at hx
  have := mem_conjClosure hh hx
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this

omit [Finite G] in
theorem le_centralizer_conjClosure_of_forall {V H E : Subgroup G}
    (h : ∀ k ∈ H, E ≤ Subgroup.centralizer (cjSub k V : Set G)) :
    E ≤ Subgroup.centralizer (conjClosure V H : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun k hk v hv => ?_
  refine Subgroup.le_centralizer_iff.mp (h k hk) ?_
  rw [mem_cjSub]
  convert hv using 1
  group

theorem sq_relIndex_le {V H B : Subgroup G}
    (hQ : ∀ h ∈ H, ∀ E : Subgroup G, E ≤ B → ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) →
      ((Subgroup.centralizer (cjSub h V : Set G)).relIndex E) ^ 2 <
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub h V)) :
    ∀ E : Subgroup G, E ≤ B →
      ((Subgroup.centralizer (conjClosure V H : Set G)).relIndex E) ^ 2 ≤
          (Subgroup.centralizer (E : Set G)).relIndex (conjClosure V H) ∧
        (¬ E ≤ Subgroup.centralizer (conjClosure V H : Set G) →
          ((Subgroup.centralizer (conjClosure V H : Set G)).relIndex E) ^ 2 <
            (Subgroup.centralizer (E : Set G)).relIndex (conjClosure V H)) := by
  set U := conjClosure V H with hUdef
  intro E
  induction E using WellFoundedLT.induction with
  | _ E ih =>
    intro hEB
    by_cases hEU : E ≤ Subgroup.centralizer (U : Set G)
    · refine ⟨?_, fun h => absurd hEU h⟩
      rw [Subgroup.relIndex_eq_one.mpr hEU, one_pow]
      exact Nat.one_le_iff_ne_zero.mpr (relIndex_ne_zero _ _)
    obtain ⟨h, hh, hEW⟩ : ∃ h ∈ H, ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) := by
      by_contra hall
      push Not at hall
      exact hEU (le_centralizer_conjClosure_of_forall hall)
    set W := cjSub h V with hWdef
    set E' := Subgroup.centralizer (W : Set G) ⊓ E with hE'def
    have hWU : W ≤ U := cjSub_le_conjClosure hh
    have hE'E : E' ≤ E := inf_le_right
    have hE'lt : E' < E := lt_of_le_of_ne hE'E fun he => hEW (he ▸ inf_le_left)
    obtain ⟨ih1, -⟩ := ih E' hE'lt (hE'E.trans hEB)
    have hq := hQ h hh E hEB hEW
    have hCUW : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (W : Set G) :=
      Subgroup.centralizer_le fun x hx => hWU hx
    have e1 : (Subgroup.centralizer (U : Set G)).relIndex E =
        (Subgroup.centralizer (U : Set G)).relIndex E' *
          (Subgroup.centralizer (W : Set G)).relIndex E := by
      have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (U : Set G))
        (Subgroup.centralizer (W : Set G)) E
      rw [inf_eq_left.mpr hCUW] at this
      exact this.symm
    have hCEE' : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (E' : Set G) :=
      Subgroup.centralizer_le fun x hx => hE'E hx
    have e2 : (Subgroup.centralizer (E : Set G)).relIndex U =
        (Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E' : Set G) ⊓ U) *
          (Subgroup.centralizer (E' : Set G)).relIndex U := by
      have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (E : Set G))
        (Subgroup.centralizer (E' : Set G)) U
      rw [inf_eq_left.mpr hCEE'] at this
      exact this.symm
    have hWE' : W ≤ Subgroup.centralizer (E' : Set G) ⊓ U :=
      le_inf (Subgroup.le_centralizer_iff.mp inf_le_left) hWU
    have i3 : (Subgroup.centralizer (E : Set G)).relIndex W ≤
        (Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E' : Set G) ⊓ U) :=
      Subgroup.relIndex_le_of_le_right hWE' (relIndex_ne_zero _ _)
    have hpos : 0 < (Subgroup.centralizer (E' : Set G)).relIndex U :=
      Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
    have hstrict : ((Subgroup.centralizer (U : Set G)).relIndex E) ^ 2 <
        (Subgroup.centralizer (E : Set G)).relIndex U := by
      rw [e1, e2, mul_pow, mul_comm ((Subgroup.centralizer (E : Set G)).relIndex _)]
      exact Nat.mul_lt_mul_of_le_of_lt ih1 (hq.trans_le i3) hpos
    exact ⟨hstrict.le, fun _ => hstrict⟩

theorem exists_quadratic_offender {U A₀ : Subgroup G} (hU : IsElemAbelian 2 U)
    (hA₀N : A₀ ≤ Subgroup.normalizer (U : Set G)) (hA₀ : IsElemAbelian 2 A₀)
    (hnc : ¬ A₀ ≤ Subgroup.centralizer (U : Set G))
    (hoff : Nat.card U ≤ (A₀ ⊓ Subgroup.centralizer (U : Set G)).relIndex A₀ *
      Nat.card (U ⊓ Subgroup.centralizer (A₀ : Set G) : Subgroup G)) :
    ∃ A : Subgroup G, A ≤ A₀ ∧ ¬ A ≤ Subgroup.centralizer (U : Set G) ∧ ⁅⁅U, A⁆, A⁆ = ⊥ ∧
      Nat.card U ≤ (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  let _ : CommGroup U := commGroupOfElemAbelian hU
  have hsq : ∀ v : U, v ^ 2 = 1 := fun v => Subtype.ext (hU.2 v v.2)
  have hcoe : ∀ (g : Subgroup.normalizer (U : Set G)) (v : U),
      ((conjAct U g v : U) : G) = g * v * (g : G)⁻¹ := fun g v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion le_rfl g) v
  set X : Subgroup (MulAut U) := autOn A₀ U with hX
  have hX2 : IsA2 X X :=
    ⟨le_rfl, autOn_ne_bot_of_not_le_centralizer hA₀N hnc, isElemAbelian2_autOn hU hA₀ hA₀N⟩
  have h0 : Nat.card U + 0 ≤ Nat.card X * Nat.card (fixV X) := by
    rw [add_zero, hX, card_autOn_eq_relIndex hA₀N, card_fixV_autOn_eq hU hA₀N]
    exact hoff
  obtain ⟨B₁, -, hB₁, -⟩ := B1.exists_offender_below hX2 0 h0
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image {B : Subgroup (MulAut U) | IsFFStarOffender X B}
    (fun B => Nat.card B) (Set.toFinite _) ⟨B₁, hB₁⟩
  have hBo : IsFFStarOffender X B := hB
  have hquad : IsQuadratic B := B1_4_3_of_minimal hsq hBo fun B' hB' hB'B =>
    Subgroup.eq_of_le_of_card_ge hB'B (hmin B' hB')
  have hBcard : Nat.card U ≤ Nat.card B * Nat.card (fixV B) :=
    B1.card_mul_card_fixV_of_isFFStarOffender_ge hBo
  have hBX : B ≤ X := hBo.1
  have hB1 : B ≠ ⊥ := hBo.2.1
  set A : Subgroup G :=
    A₀ ⊓ (B.comap (conjAct U)).map (Subgroup.normalizer (U : Set G)).subtype with hAdef
  have hAA₀ : A ≤ A₀ := inf_le_left
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAA₀.trans hA₀N
  have hAB : autOn A U = B := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      have hn' : (n : G) ∈ A := hn
      obtain ⟨m, hm, hmn⟩ := hn'.2
      have hmn' : m = n := Subtype.ext hmn
      rw [← hmn']
      exact hm
    · intro b hb
      obtain ⟨n, hn, rfl⟩ := hBX hb
      exact ⟨n, ⟨hn, n, hb, rfl⟩, rfl⟩
  have hmemB : ∀ a (ha : a ∈ A), conjAct U ⟨a, hAN ha⟩ ∈ B := fun a ha =>
    hAB ▸ ⟨⟨a, hAN ha⟩, ha, rfl⟩
  refine ⟨A, hAA₀, ?_, ?_, ?_⟩
  · intro hle
    apply hB1
    rw [← hAB, eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.mem_bot.mpr ((EmptyFaithfulMultiple.conjAct_eq_one_iff n).mpr (hle hn))
  ·
    have key : ∀ u ∈ U, ∀ a ∈ A, ⁅u, a⁆ ∈ U ⊓ Subgroup.centralizer (A : Set G) := by
      intro u hu a ha
      have h1 : a * u⁻¹ * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (U.inv_mem hu)
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def, show u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) by group]
        exact U.mul_mem hu h1
      rw [Subgroup.mem_centralizer_iff]
      intro a' ha'
      have hw : (conjAct U ⟨a, hAN ha⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : U)⁻¹ : U) ∈ commV B :=
        Subgroup.subset_closure ⟨_, hmemB a ha, ⟨u, hu⟩, rfl⟩
      have hfix := hquad hw _ (hmemB a' ha')
      have h2 := congrArg (fun z : U => (z : G)) hfix
      simp only [hcoe, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      have hc : a' * (a * u * a⁻¹ * u⁻¹) = (a * u * a⁻¹ * u⁻¹) * a' := by
        calc a' * (a * u * a⁻¹ * u⁻¹)
            = a' * (a * u * a⁻¹ * u⁻¹) * a'⁻¹ * a' := by group
          _ = (a * u * a⁻¹ * u⁻¹) * a' := by rw [h2]
      have hc' : a' * (a * u * a⁻¹ * u⁻¹)⁻¹ = (a * u * a⁻¹ * u⁻¹)⁻¹ * a' :=
        (Commute.inv_right (show Commute a' (a * u * a⁻¹ * u⁻¹) from hc)).eq
      rw [commutatorElement_def]
      calc a' * (u * a * u⁻¹ * a⁻¹) = a' * (a * u * a⁻¹ * u⁻¹)⁻¹ := by group
        _ = (a * u * a⁻¹ * u⁻¹)⁻¹ * a' := hc'
        _ = u * a * u⁻¹ * a⁻¹ * a' := by group
    have hle : ⁅U, A⁆ ≤ U ⊓ Subgroup.centralizer (A : Set G) := Subgroup.commutator_le.mpr key
    refine le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans (le_of_eq ?_))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right
  · rw [← hAB, card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hU hAN] at hBcard
    exact hBcard

theorem inf_centralizer_le_pCoreOf {G₂ T M₂ U A : Subgroup G} (hmp : MinParabolic G₂ T M₂)
    (hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G)) (hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥) (hAT : A ≤ T) :
    A ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 G₂ := by
  have hCn : G₂ ≤ Subgroup.normalizer
      ((G₂ ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hG₂U hg⟩
  have hK : ¬ twoResidual G₂ ≤ G₂ ⊓ Subgroup.centralizer (U : Set G) := by
    intro hle
    apply hUP
    rw [← F6.twoResidual_eq_oTwoUpper, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle.trans inf_le_right
  have hker := hmp.le_kerIn_of_not_twoResidual_le inf_le_left hCn hK
  exact hmp.le_pCoreOf_of_isPGroup_of_le_kerIn (hmp.isSylow.2.1.to_le (inf_le_left.trans hAT))
    ((inf_le_inf_right _ (hAT.trans hmp.isSylow.1)).trans hker)

theorem centralizerMod_le_pCoreOf {G₂ T M₂ U L N A : Subgroup G} (hmp : MinParabolic G₂ T M₂)
    (hUT : U ≤ T) (hstep : IsChiefStep G₂ U L N) (hnc : ¬ IsCentralStep G₂ L N) (hAT : A ≤ T) :
    centralizerMod L A N ≤ pCoreOf 2 G₂ := by
  have hTG₂ : T ≤ G₂ := hmp.isSylow.1
  have hG₂L : G₂ ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hG₂N : G₂ ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  set C := centralizerMod L G₂ N with hCdef
  have hconj : ∀ g ∈ G₂, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    refine ⟨G₂.mul_mem (G₂.mul_mem hg hc.1) (G₂.inv_mem hg),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hG₂L hg) hc.2.1) (Subgroup.inv_mem _ (hG₂L hg)),
      fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ N := (Subgroup.mem_normalizer_iff''.mp (hG₂N hg) u).mp hu
    have h1 := (Subgroup.mem_normalizer_iff.mp (hG₂L hg) _).mp (hc.2.2 _ hu')
    have e : g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ * u⁻¹ =
        g * (c * (g⁻¹ * u * g) * c⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  have hCn : G₂ ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (hconj g hg) fun c hc => by
      simpa using hconj g⁻¹ (G₂.inv_mem hg) c hc
  have hK : ¬ twoResidual G₂ ≤ C := by
    intro hle
    apply hnc
    refine isCentralStep_of_commutator_le hmp.isSylow (hUT.trans hTG₂) (hstep.1.1.trans hUT)
      hstep ?_
    rw [Subgroup.commutator_le]
    intro n hn p hp
    have hpC : p ∈ C := hle ((F6.twoResidual_eq_oTwoUpper G₂).symm ▸ hp)
    have h1 := L.inv_mem (hpC.2.2 n hn)
    rwa [show (p * n * p⁻¹ * n⁻¹)⁻¹ = ⁅n, p⁆ by rw [commutatorElement_def]; group] at h1
  have hker := hmp.le_kerIn_of_not_twoResidual_le (centralizerMod_le_left L G₂ N) hCn hK
  exact hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
    (hmp.isSylow.2.1.to_le ((centralizerMod_le_left L A N).trans hAT))
    ((centralizerMod_mono_left N (hAT.trans hTG₂)).trans hker)

omit [Finite G] in
theorem eq_of_le_mul {a b u v : ℕ} (ha : 0 < a) (hb : 0 < b) (hi : u ≤ b * a) (hii : a ^ 2 ≤ u)
    (hiii : b ^ 2 ≤ v) (hiv : v ≤ u) : a = b ∧ v = b ^ 2 := by
  have h1 : a * a ≤ a * b := by nlinarith
  have h2 : b * b ≤ b * a := by nlinarith
  have heq : a = b :=
    le_antisymm (Nat.le_of_mul_le_mul_left h1 ha) (Nat.le_of_mul_le_mul_left h2 hb)
  subst heq
  exact ⟨rfl, le_antisymm (by nlinarith) hiii⟩

variable {G₁ G₂ T V M₂ : Subgroup G}

theorem qInt_le_two (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) (hD125 : D125 G₂ T (conjClosure V G₂)) {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) :
    qInt G₁ V h.reduced.2.2.1 ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.reduced.2.2.1
  have hmp := h.minParabolic hnff
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hTG₁ : T ≤ G₁ := h.sylow₁.1
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hUe : IsElemAbelian 2 U := isElemAbelian_conjClosure h hnff hVR₂
  have hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥ := commutator_ne_bot h
  obtain ⟨A₀, hA₀, hA₀U⟩ : ∃ A₀, IsMaxElemAbelian T A₀ ∧
      ¬ A₀ ≤ Subgroup.centralizer (U : Set G) := by
    by_contra hall
    push Not at hall
    have hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (U : Set G) :=
      iSup₂_le fun A hA => le_inf hA.1 (hall A hA)
    apply h.not_thompsonJ_le_pCoreOf hnff
    rw [← h.thompsonJ_eq hnff]
    exact hJ.trans (inf_centralizer_le_pCoreOf hmp hG₂U hUP le_rfl)
  have hA₀N : A₀ ≤ Subgroup.normalizer (U : Set G) := (hA₀.1.trans hTG₂).trans hG₂U
  obtain ⟨A, hAA₀, hAU, hAquad, hAoff⟩ := exists_quadratic_offender hUe hA₀N hA₀.2.1 hA₀U
    (card_le_relIndex_mul_card hUe hUT hA₀)
  have hAT : A ≤ T := hAA₀.trans hA₀.1
  have hAe : IsElemAbelian 2 A := isElemAbelian_mono hAA₀ hA₀.2.1
  by_contra hq
  have hq2 := fun E hE hEe hquad hnc =>
    sq_relIndex_lt_of_not_qInt_le_two hV h.reduced.2.1 hq (E := E) hE hEe hquad hnc
  set B := R₂ ⊓ A with hBdef
  have hBA : B ≤ A := inf_le_right
  have hCAU : A ⊓ Subgroup.centralizer (U : Set G) ≤ R₂ :=
    inf_centralizer_le_pCoreOf hmp hG₂U hUP hAT
  have ha0 : 0 < R₂.relIndex A := Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have hb0 : 0 < (Subgroup.centralizer (U : Set G)).relIndex B :=
    Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have hab : (Subgroup.centralizer (U : Set G)).relIndex A =
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (U : Set G)) R₂ A
    have e : (Subgroup.centralizer (U : Set G) ⊓ R₂).relIndex A =
        (Subgroup.centralizer (U : Set G)).relIndex A := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G) ⊓ R₂),
        ← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G)) A]
      congr 1
      refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left ?_)
        inf_le_right)
      rintro x ⟨hxC, hxA⟩
      exact hCAU ⟨hxA, hxC⟩
    rw [e] at this
    exact this.symm
  have hi : (Subgroup.centralizer (A : Set G)).relIndex U ≤
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) U
    have hpos : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := Nat.card_pos
    have hoff' : Nat.card U ≤ (Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := by
      rw [Subgroup.inf_relIndex_left] at hAoff
      rwa [inf_comm] at hAoff
    rw [← hab]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e2]
    exact hoff'
  have hii : (R₂.relIndex A) ^ 2 ≤ (Subgroup.centralizer (A : Set G)).relIndex U := by
    refine (Nat.pow_le_pow_right ha0 hc).trans ?_
    refine pow_le_relIndex hUG₂ (hAT.trans hTG₂) (fun L' N' hstep hnc => ?_) hser
    have hquadN : ⁅⁅N', A⁆, A⁆ ≤ L' := by
      have : ⁅⁅N', A⁆, A⁆ ≤ ⁅⁅U, A⁆, A⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono hstep.1.1 le_rfl) le_rfl
      rw [hAquad] at this
      exact this.trans bot_le
    refine (Subgroup.relIndex_le_of_le_left
      (centralizerMod_le_pCoreOf hmp hUT hstep hnc hAT) (relIndex_ne_zero _ _)).trans ?_
    exact hD125 L' N' hstep hnc A hAT hAe hquadN
  have hQ : ∀ k ∈ G₂, ∀ E : Subgroup G, E ≤ B →
      ¬ E ≤ Subgroup.centralizer (cjSub k V : Set G) →
      ((Subgroup.centralizer (cjSub k V : Set G)).relIndex E) ^ 2 <
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub k V) := by
    intro k hk E hEB hnc
    have hEA : E ≤ A := hEB.trans hBA
    have hquad : ⁅⁅cjSub k V, E⁆, E⁆ = ⊥ := by
      have : ⁅⁅cjSub k V, E⁆, E⁆ ≤ ⁅⁅U, A⁆, A⁆ := Subgroup.commutator_mono
        (Subgroup.commutator_mono (cjSub_le_conjClosure hk) hEA) hEA
      rw [hAquad] at this
      exact le_bot_iff.mp this
    exact relIndex_conj_lt hq2 (hR₂T.trans hTG₁) (hG₂R₂ hk) (hEB.trans inf_le_left)
      (isElemAbelian_mono hEA hAe) hquad hnc
  obtain ⟨hiii, hiii'⟩ := sq_relIndex_le hQ B le_rfl
  have hiv : (Subgroup.centralizer (B : Set G)).relIndex U ≤
      (Subgroup.centralizer (A : Set G)).relIndex U :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le fun x hx => hBA hx)
      (relIndex_ne_zero _ _)
  obtain ⟨heq, hvb⟩ := eq_of_le_mul ha0 hb0 hi hii hiii hiv
  by_cases hBU : B ≤ Subgroup.centralizer (U : Set G)
  · have hb1 : (Subgroup.centralizer (U : Set G)).relIndex B = 1 :=
      Subgroup.relIndex_eq_one.mpr hBU
    have hAR₂ : A ≤ R₂ := Subgroup.relIndex_eq_one.mp (heq.trans hb1)
    exact hAU ((le_inf hAR₂ le_rfl).trans hBU)
  · exact (ne_of_gt (hiii' hBU)) hvb

end CFSG.Quasithin.D15Proof
