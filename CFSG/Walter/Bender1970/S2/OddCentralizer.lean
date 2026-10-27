module

public import CFSG.Walter.Bender1970.S2.Cyclic
import CFSG.Walter.Bender1970.S2.AutEven
import CFSG.Walter.Bender1970.S2.AutJR
import CFSG.Walter.Bender1970.S2.AutOdd
import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

theorem pow_conj_eq_mul_pow {G : Type*} [Group G] {w x c : G} (h : w * x * w⁻¹ = x * c)
    (hc : w * c = c * w) (j : ℕ) : w ^ j * x * (w ^ j)⁻¹ = x * c ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hc' : w * c ^ j * w⁻¹ = c ^ j := by
      rw [(Commute.pow_right hc j).eq, mul_inv_cancel_right]
    calc w ^ (j + 1) * x * (w ^ (j + 1))⁻¹ = w * (w ^ j * x * (w ^ j)⁻¹) * w⁻¹ := by group
      _ = w * (x * c ^ j) * w⁻¹ := by rw [ih]
      _ = (w * x * w⁻¹) * (w * c ^ j * w⁻¹) := by group
      _ = x * c ^ (j + 1) := by rw [h, hc', mul_assoc, ← pow_succ']

section CoreFree

variable {Y : Type} [Group Y] [Finite Y]

theorem inf_centralizer_sylow_le_centralizer_component
    (hab : HasAbelianSylowTwo Y)
    (T : Sylow 2 Y) {t : Y} (htT : t ∈ (T : Subgroup Y)) (ht : orderOf t = 2)
    {Q : Subgroup Y} (hQodd : Odd (Nat.card Q)) (hQnil : Group.IsNilpotent Q)
    (hQt : Q ≤ Subgroup.centralizer ({t} : Set Y))
    (hCQ : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (Q : Set Y))
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hZL : Subgroup.center L = ⊥)
    (hLt : IsTypeL2 L ∨ IsTypeJR L) :
    Q ⊓ Subgroup.centralizer ((T : Subgroup Y) : Set Y) ≤ Subgroup.centralizer (L : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2.2
  have : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have h2L : 2 ∣ Nat.card L := IsQuasisimple.two_dvd_card hL.2.2
  obtain ⟨ℓ, ⟨hℓT, hℓL⟩, hℓ⟩ := exists_inner_mem_sylow_inf hab T hL htT
  set ℓ' : L := ⟨ℓ, hℓL⟩ with hℓ'
  have htℓ : ∀ x : L, (x : Y) ∈ Subgroup.centralizer ({t} : Set Y) ↔
      x ∈ Subgroup.centralizer ({ℓ'} : Set L) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hℓ x x.2
    constructor
    · intro h
      apply Subtype.ext
      show (x : Y) * ℓ = ℓ * x
      have h2 : t * (x : Y) * t⁻¹ = x := by rw [← h, mul_inv_cancel_right]
      rw [h2] at h1
      calc (x : Y) * ℓ = (ℓ * x * ℓ⁻¹) * ℓ := by rw [← h1]
        _ = ℓ * x := by group
    · intro h
      have h2 : (x : Y) * ℓ = ℓ * x := congrArg Subtype.val h
      have h3 : ℓ * (x : Y) * ℓ⁻¹ = x := by rw [← h2, mul_inv_cancel_right]
      rw [h3] at h1
      calc (x : Y) * t = (t * x * t⁻¹) * t := by rw [h1]
        _ = t * x := by group
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hℓ2 : ℓ' ^ 2 = 1 := by
    have hc : ℓ' ^ 2 ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hy1 := hℓ y y.2
      have hmy : ℓ * (y : Y) * ℓ⁻¹ ∈ L := L.mul_mem (L.mul_mem hℓL y.2) (L.inv_mem hℓL)
      have hy3 : t * (t * (y : Y) * t⁻¹) * t⁻¹ = y := by
        calc t * (t * (y : Y) * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
          _ = y := by rw [htt]; group
      have hy2 : ℓ * (ℓ * (y : Y) * ℓ⁻¹) * ℓ⁻¹ = y := by
        rw [← hℓ _ hmy, ← hy1]
        exact hy3
      simp only [Subgroup.coe_mul, pow_two]
      calc (y : Y) * (ℓ * ℓ) = (ℓ * (ℓ * y * ℓ⁻¹) * ℓ⁻¹) * (ℓ * ℓ) := by rw [hy2]
        _ = ℓ * ℓ * y := by group
    rw [hZL, Subgroup.mem_bot] at hc
    exact hc
  obtain ⟨SL, hSL⟩ := exists_sylow_map_eq_inf_of_isSubnormal T (isSubnormal_of_isComponentOf hL)
  have hmemSL : ∀ x : L, x ∈ (SL : Subgroup L) ↔ (x : Y) ∈ (T : Subgroup Y) := by
    intro x
    constructor
    · intro hx
      have : (x : Y) ∈ (SL : Subgroup L).map L.subtype := ⟨x, hx, rfl⟩
      rw [hSL] at this
      exact this.1
    · intro hx
      have : (x : Y) ∈ (SL : Subgroup L).map L.subtype := by
        rw [hSL]
        exact ⟨hx, x.2⟩
      obtain ⟨y, hy, hyx⟩ := this
      rwa [show y = x from Subtype.ext hyx] at hy
  have hℓSL : ℓ' ∈ (SL : Subgroup L) := (hmemSL ℓ').mpr hℓT
  set N := Subgroup.normalizer (L : Set Y) with hN
  set ρ : N →* MulAut L := L.normalizerMonoidHom with hρ
  have hρapply : ∀ (y : N) (x : L), ((ρ y x : L) : Y) = (y : Y) * x * (y : Y)⁻¹ := by
    intro y x
    rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  set W := Q ⊓ Subgroup.centralizer ((T : Subgroup Y) : Set Y) with hW
  have hWN : W ≤ N := fun w hw => centralizer_sylow_le_normalizer hab T hL hw.2
  have hcent : ∀ w (hw : w ∈ N), ρ ⟨w, hw⟩ = 1 → w ∈ Subgroup.centralizer (L : Set Y) := by
    intro w hw h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hρapply ⟨w, hw⟩ ⟨x, hx⟩
    rw [h, MulAut.one_apply] at h1
    calc x * w = (w * x * w⁻¹) * w := by rw [← h1]
      _ = w * x := by group
  have hodd : ∀ w (hw : w ∈ W), Odd (orderOf (ρ ⟨w, hWN hw⟩)) := by
    intro w hw
    have h1 : orderOf (ρ ⟨w, hWN hw⟩) ∣ orderOf (⟨w, hWN hw⟩ : N) := orderOf_map_dvd ρ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf w ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨w, hw.1⟩ : Q)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hQodd (h1.trans h2)
  have hfixS : ∀ w (hw : w ∈ W), ∀ x ∈ (SL : Subgroup L), ρ ⟨w, hWN hw⟩ x = x := by
    intro w hw x hx
    apply Subtype.ext
    rw [hρapply]
    have hxw := Subgroup.mem_centralizer_iff.mp hw.2 x ((hmemSL x).mp hx)
    show w * (x : Y) * w⁻¹ = x
    rw [← hxw, mul_inv_cancel_right]
  have hcommQ : ∀ w ∈ Q, ∀ x : L, x ∈ Subgroup.centralizer ({ℓ'} : Set L) →
      (x : Y)⁻¹ * (w * x * w⁻¹) ∈ Q := by
    intro w hwQ x hx
    have hxt : (x : Y) ∈ Subgroup.centralizer ({t} : Set Y) := (htℓ x).mpr hx
    have h1 : (x : Y)⁻¹ * w * x ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hCQ hxt)) w).mp hwQ
      simpa using this
    have h2 : (x : Y)⁻¹ * (w * x * w⁻¹) = ((x : Y)⁻¹ * w * x) * w⁻¹ := by group
    rw [h2]
    exact Q.mul_mem h1 (Q.inv_mem hwQ)
  have hφC : ∀ w (hw : w ∈ W), ∀ x : L, x ∈ Subgroup.centralizer ({ℓ'} : Set L) →
      ρ ⟨w, hWN hw⟩ x ∈ Subgroup.centralizer ({ℓ'} : Set L) := by
    intro w hw x hx
    rw [← htℓ, hρapply]
    have hwt : w ∈ Subgroup.centralizer ({t} : Set Y) := hQt hw.1
    have hxt : (x : Y) ∈ Subgroup.centralizer ({t} : Set Y) := (htℓ x).mpr hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwt hxt) (Subgroup.inv_mem _ hwt)
  set R : Subgroup L := Q.subgroupOf L ⊓ Subgroup.centralizer ({ℓ'} : Set L) with hR
  have hRodd : Odd (Nat.card R) := by
    have h1 : Nat.card R ∣ Nat.card (Q.subgroupOf L) := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (Q.subgroupOf L) ∣ Nat.card Q := by
      have h3 : (Q.subgroupOf L).map L.subtype ≤ Q := by
        rintro _ ⟨y, hy, rfl⟩
        exact hy
      have h4 := Subgroup.card_dvd_of_le h3
      rwa [Subgroup.card_map_of_injective L.subtype_injective] at h4
    exact Odd.of_dvd_nat hQodd (h1.trans h2)
  have hRC : R ≤ Subgroup.centralizer ({ℓ'} : Set L) := inf_le_right
  have hCR : Subgroup.centralizer ({ℓ'} : Set L) ≤ Subgroup.normalizer (R : Set L) := by
    intro c hc
    have hct : (c : Y) ∈ Subgroup.centralizer ({t} : Set Y) := (htℓ c).mpr hc
    have h1 : c ∈ Subgroup.normalizer ((Q.subgroupOf L : Subgroup L) : Set L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hCQ hct) h
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hc⟩
  have hmemR : ∀ w (hw : w ∈ W), ∀ x : L, x ∈ Subgroup.centralizer ({ℓ'} : Set L) →
      x⁻¹ * ρ ⟨w, hWN hw⟩ x ∈ R := by
    intro w hw x hx
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) (hφC w hw x hx)⟩
    show x⁻¹ * ρ ⟨w, hWN hw⟩ x ∈ Q.subgroupOf L
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, hρapply]
    exact hcommQ w hw.1 x hx
  have hfixR : R = ⊥ → ∀ w (hw : w ∈ W), ∀ x : L,
      x ∈ Subgroup.centralizer ({ℓ'} : Set L) → ρ ⟨w, hWN hw⟩ x = x := by
    intro hR1 w hw x hx
    have h1 := hmemR w hw x hx
    rw [hR1, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  intro w hw
  apply hcent w (hWN hw)
  by_cases hℓ1 : ℓ' = 1
  ·
    have hCtop : Subgroup.centralizer ({ℓ'} : Set L) = ⊤ := by
      rw [hℓ1, eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_singleton_iff, one_mul, mul_one]
    have hRn : R.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hCtop]
      exact hCR
    have hR1 : R = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
      · exact h
      · exfalso
        rw [← Subgroup.card_top (G := L), ← h] at h2L
        exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2L)
    apply MulEquiv.ext
    intro x
    exact hfixR hR1 w hw x (hCtop ▸ Subgroup.mem_top x)
  have hℓo : orderOf ℓ' = 2 := orderOf_eq_prime hℓ2 hℓ1
  rcases hLt with (hev | hodd') | hJR
  · exact IsTypeL2Even.mulAut_eq_one hev _ (hodd w hw) SL (hfixS w hw)
  ·
    by_contra hne
    obtain ⟨k, r, hr, hr2, hrk⟩ := exists_pow_orderOf_eq_prime hne (hodd w hw)
    have hw1 : w ^ k ∈ W := W.pow_mem hw k
    set n₁ := orderOf (w ^ k) with hn₁
    have hn₁0 : n₁ ≠ 0 := (orderOf_pos (w ^ k)).ne'
    set w' := (w ^ k) ^ (ordCompl[r] n₁) with hw'
    have hw'W : w' ∈ W := W.pow_mem hw1 _
    have hρw' : ρ ⟨w', hWN hw'W⟩ = (ρ ⟨w, hWN hw⟩ ^ k) ^ (ordCompl[r] n₁) := by
      rw [← map_pow, ← map_pow]
      rfl
    have hw'ord : orderOf (ρ ⟨w', hWN hw'W⟩) = r := by
      rw [hρw', Nat.Coprime.orderOf_pow, hrk]
      rw [hrk]
      exact Nat.coprime_ordCompl hr hn₁0
    have hw'r : orderOf w' = ordProj[r] n₁ := by
      rw [hw', orderOf_pow_of_dvd (Nat.ordCompl_pos r hn₁0).ne' (Nat.ordCompl_dvd n₁ r), ← hn₁]
      exact Nat.div_eq_of_eq_mul_left (Nat.ordCompl_pos r hn₁0)
        (Nat.ordProj_mul_ordCompl_eq_self n₁ r).symm
    apply IsTypeL2Odd.false_of_mulAut hodd' hr hr2 _ hw'ord SL (hfixS w' hw'W) hℓSL hℓo
    intro x hx hcop
    set c : Y := (x : Y)⁻¹ * (w' * x * w'⁻¹) with hc
    have hcQ : c ∈ Q := hcommQ w' hw'W.1 x hx
    have hcord : orderOf c = orderOf (x⁻¹ * ρ ⟨w', hWN hw'W⟩ x) := by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, InvMemClass.coe_inv, hρapply]
    rw [← hcord] at hcop
    have hcomm : Commute (⟨c, hcQ⟩ : Q) ⟨w', hw'W.1⟩ := by
      apply Group.IsNilpotent.commute_of_orderOf_coprime
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hw'r]
      exact Nat.Coprime.pow_right _ hcop
    have hcw : w' * c = c * w' := (congrArg Subtype.val hcomm.eq).symm
    have hconj : w' * x * w'⁻¹ = x * c := by
      rw [hc]
      group
    have h1 := pow_conj_eq_mul_pow hconj hcw (orderOf w')
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, left_eq_mul] at h1
    have h2 : orderOf c ∣ orderOf w' := orderOf_dvd_of_pow_eq_one h1
    rw [hw'r] at h2
    have h3 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ hcop) h2
    rw [orderOf_eq_one_iff] at h3
    apply Subtype.ext
    rw [hρapply]
    have : (x : Y)⁻¹ * (w' * x * w'⁻¹) = 1 := h3
    calc w' * (x : Y) * w'⁻¹ = (x : Y) * ((x : Y)⁻¹ * (w' * x * w'⁻¹)) := by group
      _ = x := by rw [this, mul_one]
  ·
    have hR1 : R = ⊥ :=
      (odd_normal_subgroup_centralizer h2L (Or.inr hJR) hℓ2 hRodd hRC hCR).2 (Or.inr hJR)
    exact hJR.mulAut_eq_one _ (hodd w hw) hℓo (hfixR hR1 w hw)

theorem inf_centralizer_sylow_eq_bot
    (hO : pPrimeCore 2 Y = ⊥) (hab : HasAbelianSylowTwo Y)
    (htype : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ ∧ (IsTypeL2 K ∨ IsTypeJR K))
    (T : Sylow 2 Y) {t : Y} (htT : t ∈ (T : Subgroup Y)) (ht : orderOf t = 2)
    {Q : Subgroup Y} (hQodd : Odd (Nat.card Q)) (hQnil : Group.IsNilpotent Q)
    (hQt : Q ≤ Subgroup.centralizer ({t} : Set Y))
    (hCQ : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (Q : Set Y)) :
    Q ⊓ Subgroup.centralizer ((T : Subgroup Y) : Set Y) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := Q ⊓ Subgroup.centralizer ((T : Subgroup Y) : Set Y) with hW
  set F := CFSG.fittingSubgroup Y with hF
  set Fst := generalizedFittingSubgroupOf (⊤ : Subgroup Y) with hFst
  have hF2 : IsPGroup 2 F :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO
  have hFT : F ≤ (T : Subgroup Y) := fun f hf => hF2.le_sylow_of_normal T hf
  have hfit : CFSG.fittingSubgroupOf (⊤ : Subgroup Y) ≤ F :=
    CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top
  have hWC : W ≤ Subgroup.centralizer (Fst : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ (sSup_le fun L hL => ?_)
    · refine hfit.trans (hFT.trans ?_)
      rw [← Subgroup.le_centralizer_iff]
      exact inf_le_right
    · rw [← Subgroup.le_centralizer_iff]
      obtain ⟨hZL, hLt⟩ := htype L hL
      exact inf_centralizer_sylow_le_centralizer_component hab T htT ht hQodd hQnil hQt hCQ hL
        hZL hLt
  have hWFst : W ≤ Fst := hWC.trans CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le
  have hWfit : W ≤ CFSG.fittingSubgroupOf (⊤ : Subgroup Y) := fun w hw =>
    centralizer_generalizedFitting_intersection_le_fittingSubgroupOf ⟨hWC hw, hWFst hw⟩
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨a, ha⟩ := hF2 ⟨w, hfit (hWfit hw)⟩
  have h1 : orderOf w ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2 : orderOf w ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨w, hw.1⟩ : Q)
    rwa [Subgroup.orderOf_mk] at this
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_right a
      (Nat.coprime_two_right.mpr hQodd))) h1))

end CoreFree

section AStar

variable {X : Type} [Group X] [Finite X]

theorem bender1970_2_5_inf_centralizer_le
    (hX : IsAStar X) {t : X} (ht : orderOf t = 2)
    (T : Sylow 2 X) (htT : t ∈ (T : Subgroup X)) :
    oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) ⊓
      Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ pPrimeCore 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) with hU
  set O := pPrimeCore 2 X with hOdef
  set q : X →* X ⧸ O := QuotientGroup.mk' O with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective O
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hUodd, hUt, hCU⟩ := oddFitting_centralizer_properties t
  have hUnil : Group.IsNilpotent U := by
    set C := Subgroup.centralizer ({t} : Set X)
    have hFC : Group.IsNilpotent (CFSG.fittingSubgroupOf C) := CFSG.fittingSubgroupOf_isNilpotent C
    have hUF : U ≤ CFSG.fittingSubgroupOf C := Subgroup.map_subtype_le _
    have : Group.IsNilpotent (U.subgroupOf (CFSG.fittingSubgroupOf C)) := inferInstance
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUF)
  have htO : t ∉ O := by
    intro h
    have h2 : 2 ∣ Nat.card O := ht ▸ Subgroup.orderOf_dvd_natCard O h
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  have htb : orderOf (q t) = 2 := by
    have h1 : q t ≠ 1 := by
      rw [hq, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htO
    have h2 : (q t) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht] at h
      rw [← map_pow, h, map_one]
    exact orderOf_eq_prime h2 h1
  set Tb : Sylow 2 (X ⧸ O) := T.mapSurjective hqs with hTb
  have htTb : q t ∈ (Tb : Subgroup (X ⧸ O)) := by
    rw [hTb, Sylow.coe_mapSurjective]
    exact ⟨t, htT, rfl⟩
  set Ub := U.map q with hUbdef
  have hUbodd : Odd (Nat.card Ub) := Odd.of_dvd_nat hUodd (Subgroup.card_map_dvd U q)
  have hUbnil : Group.IsNilpotent Ub := Group.nilpotent_of_surjective (q.subgroupMap U)
    (q.subgroupMap_surjective U)
  have hUbt : Ub ≤ Subgroup.centralizer ({q t} : Set (X ⧸ O)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hUt hu)]
  have hCUb : Subgroup.centralizer ({q t} : Set (X ⧸ O)) ≤
      Subgroup.normalizer (Ub : Set (X ⧸ O)) := by
    have htp : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have : Fact (IsPGroup 2 (Subgroup.zpowers t)) := ⟨htp⟩
    have hC := centralizer_map_quotient_eq_map_centralizer (p := 2) (Subgroup.zpowers t) O
      inferInstance (Nat.coprime_two_left.mpr hOodd)
    simp only at hC
    rw [MonoidHom.map_zpowers] at hC
    have hC1 : Subgroup.centralizer ({q t} : Set (X ⧸ O)) =
        (Subgroup.centralizer ({t} : Set X)).map q := by
      rw [← centralizer_zpowers_eq', ← centralizer_zpowers_eq']
      exact hC
    rw [hC1]
    exact (Subgroup.map_mono hCU).trans (Subgroup.le_normalizer_map q)
  have hbot := inf_centralizer_sylow_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    (hX.1.quotient O) (fun K hK => hX.2.2 K hK) Tb htTb htb hUbodd hUbnil hUbt hCUb
  intro u hu
  have h1 : q u ∈ Ub ⊓ Subgroup.centralizer ((Tb : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
    refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
    show q u ∈ Subgroup.centralizer ((Tb : Subgroup (X ⧸ O)) : Set (X ⧸ O))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hTb, Sylow.coe_mapSurjective] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hu.2 s hs]
  rw [hbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem bender1970_2_5
    (hX : IsAStar X) {t : X} (ht : orderOf t = 2) (T : Sylow 2 X)
    (htT : t ∈ (T : Subgroup X)) {U : Subgroup X}
    (hU : U = oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X)))) :
    U ≤ oStar X ∧ U ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ pPrimeCore 2 X ∧
      ∀ E : Subgroup X, IsComponentOf E ⊤ →
        U ≤ Subgroup.normalizer (E : Set X) ∧
          ((Subgroup.centralizer (E : Set X)).subgroupOf U).Normal ∧
          (∀ [((Subgroup.centralizer (E : Set X)).subgroupOf U).Normal],
            IsCyclic (U ⧸ (Subgroup.centralizer (E : Set X)).subgroupOf U)) ∧
          (IsTypeL2Even (E ⧸ Subgroup.center E) ∨ IsTypeJR (E ⧸ Subgroup.center E) →
            U ≤ Subgroup.centralizer (E : Set X)) := by
  have hCU : U ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ pPrimeCore 2 X := by
    rw [hU]
    exact bender1970_2_5_inf_centralizer_le hX ht T htT
  obtain ⟨hUO, hE⟩ := bender1970_2_5_of_inf_centralizer_le hX ht T htT hU hCU
  exact ⟨hUO, hCU, hE⟩

end AStar

end CFSG.Walter
