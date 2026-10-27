module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.Open.StatedDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivLinear
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Arith
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.Subnormal
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615

private lemma ltrspb3a_not_three_dvd_two_pow_sub_one_of_dvd_three {n : ℕ} (hn : n ∣ 3) :
    ¬ 3 ∣ 2 ^ n - 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hn with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

private lemma ltrspb3a_card_proj_sl_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 8) :
    Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) = 504 := by
  have h : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) =
      Nat.card (StatedProj (StatedSL 2 F)) := by
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL]
  rw [h, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  norm_num

private lemma ltrspb3a_padicValNat_two_504 : padicValNat 2 504 = 3 := by
  apply le_antisymm
  · by_contra h
    have h4 : 4 ≤ padicValNat 2 504 := by omega
    have hdvd : 2 ^ 4 ∣ 504 :=
      (pow_dvd_pow 2 h4).trans (pow_padicValNat_dvd (p := 2) (n := 504))
    norm_num at hdvd
  · exact (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 3) (n := 504)
      (by norm_num) (by norm_num)).mp (by norm_num)

theorem spPairedBlock_false {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {x : ↥(StatedSp m K)} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) {A₂ : Subgroup ↥(StatedSp m K)}
    (hxA : x ∈ A₂) (hA₂ : A₂ ≤ Subgroup.centralizer ({x} : Set ↥(StatedSp m K))) {r : ℕ}
    (hr : 1 ≤ r) (e₂ : A₂ ≃* GL (Fin r) K) {C : Subgroup ↥(StatedSp m K)}
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({x} : Set ↥(StatedSp m K))))
    (hle : C ≤ A₂) (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C)) :
    False := by
  classical
  have hxcen : (⟨x, hxA⟩ : A₂) ∈ Subgroup.center A₂ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy := hA₂ y.2
    rw [Subgroup.mem_centralizer_iff] at hy
    have h := hy x (Set.mem_singleton x)
    exact h.symm
  have hx'cen : e₂ ⟨x, hxA⟩ ∈ Subgroup.center (GL (Fin r) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e₂.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e₂ (Subgroup.mem_center_iff.mp hxcen y)
  obtain ⟨c, hc⟩ : ∃ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin r) c = e₂ ⟨x, hxA⟩ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'cen
    exact hx'cen
  have hx3' : (⟨x, hxA⟩ : A₂) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hx3
  have hx'3 : (e₂ ⟨x, hxA⟩) ^ 3 = 1 := by
    rw [← map_pow, hx3', map_one]
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin r) : Kˣ →* GL (Fin r) K) := by
    intro a b hab
    have h00 := congrArg
      (fun g : GL (Fin r) K => (g : Matrix (Fin r) (Fin r) K) ⟨0, by omega⟩ ⟨0, by omega⟩) hab
    exact Units.ext (by simpa using h00)
  have hc3 : c ^ 3 = 1 := by
    apply hscalar_inj
    rw [map_pow, hc, hx'3, map_one]
  have hcne : c ≠ 1 := by
    intro h
    apply hx1
    have h1 : e₂ ⟨x, hxA⟩ = 1 := by rw [← hc, h, map_one]
    have h2 : (⟨x, hxA⟩ : A₂) = 1 := e₂.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  have horder : orderOf c = 3 := by
    have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso
      exact hcne (orderOf_eq_one_iff.mp h)
    · exact h
  have h3dvdK : 3 ∣ Nat.card K - 1 := by
    have h1 : orderOf c ∣ Nat.card Kˣ := orderOf_dvd_natCard c
    rw [horder, Nat.card_units] at h1
    exact h1
  let C' : Subgroup (GL (Fin r) K) := (C.subgroupOf A₂).map e₂.toMonoidHom
  have hcompA₂ : CFSG.Assembly.IsComponentOf C A₂ :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hC hle hA₂
  have hsubC_A₂ : CFSG.Assembly.IsSubnormal C A₂ := hcompA₂.2.1
  have hqC : CFSG.Assembly.IsQuasisimple C := hC.2.2
  have hsubC'_m : C'.IsSubnormal := by
    have h : (C.subgroupOf A₂).IsSubnormal :=
      CFSG.Assembly.IsSubnormal.subgroupOf hsubC_A₂
    have h2 := Subgroup.IsSubnormal.map (f := e₂.toMonoidHom) e₂.surjective h
    simpa [C'] using h2
  have hsubC'_top : CFSG.Assembly.IsSubnormal C' ⊤ :=
    CFSG.Assembly.IsSubnormal.of_mathlib hsubC'_m
  have hq' : CFSG.Assembly.IsQuasisimple C' := by
    have hqsub : CFSG.Assembly.IsQuasisimple (C.subgroupOf A₂) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hqC
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (C.subgroupOf A₂) e₂.toMonoidHom e₂.injective).symm hqsub
  have hcompC'_top : CFSG.Assembly.IsComponentOf C' ⊤ := ⟨le_top, hsubC'_top, hq'⟩
  have hC'leSL : C' ≤ StatedSL r K := by
    have hcomm : ⁅C', C'⁆ = C' :=
      CFSG.LieType.SemisimpleCentralizers.Held.commutator_eq_self_of_isComponentOf_top
        ((CFSG.Assembly.isComponentOf_iff_open).mp hcompC'_top)
    rw [← hcomm, Subgroup.commutator_le]
    intro a _ b _
    exact CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL a b
  have hcompC'_SL : CFSG.Assembly.IsComponentOf C' (StatedSL r K) :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hcompC'_top hC'leSL le_top
  have hcompC'_SL_open : CFSG.Open.IsComponentOf C' (StatedSL r K) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hcompC'_SL
  have hord1 : (orderOf (1 : GL (Fin r) K) : K) ≠ 0 := by
    rw [orderOf_one]
    simpa using (one_ne_zero : (1 : K) ≠ 0)
  have hJ : CFSG.Open.IsComponentOf C'
      (Subgroup.centralizer ({1} : Set (GL (Fin r) K)) ⊓ StatedSL r K) := by
    have hcent : Subgroup.centralizer ({1} : Set (GL (Fin r) K)) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    rw [hcent, top_inf_eq]
    exact hcompC'_SL_open
  obtain ⟨a, E, hEfield, hEalg, hEfin, ha2, ⟨eE⟩⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.held_linear_components_unconditional
      (s := (1 : GL (Fin r) K)) (Subgroup.one_mem _) hord1 C' hJ
  letI : Field E := hEfield
  letI : Algebra K E := hEalg
  letI : Finite E := hEfin
  have hcardC : Nat.card (↥C ⧸ Subgroup.center ↥C) = 504 := by
    unfold GGHasLabel at hlab
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeLinear] at hlab
    obtain ⟨K', hK'field, hK'fin, hK'card, ⟨e0⟩⟩ := hlab
    letI : Field K' := hK'field
    letI : Finite K' := hK'fin
    have hK'8 : Nat.card K' = 8 := by rw [hK'card]; norm_num
    calc Nat.card (↥C ⧸ Subgroup.center ↥C)
        = Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) K')) :=
          Nat.card_congr e0.toEquiv
      _ = 504 := ltrspb3a_card_proj_sl_two hK'8
  have eCC' : ↥C ≃* ↥C' :=
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (Subgroup.equivMapOfInjective (C.subgroupOf A₂) e₂.toMonoidHom e₂.injective)
  have hqiso : (↥C ⧸ Subgroup.center ↥C) ≃* (↥C' ⧸ Subgroup.center ↥C') :=
    QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥C') eCC'
      (Subgroup.map_center_eq eCC')
  have hcardC' : Nat.card (↥C' ⧸ Subgroup.center ↥C') = 504 := by
    rw [← Nat.card_congr hqiso.toEquiv, hcardC]
  have hcardE : Nat.card (StatedProj (StatedSL a E)) = 504 := by
    rw [← Nat.card_congr eE.toEquiv, hcardC']
  haveI : Algebra (ZMod 2) K := ZMod.algebra K 2
  set n : ℕ := Module.finrank (ZMod 2) K with hn
  have hKcard : Nat.card K = 2 ^ n := (FiniteField.pow_finrank_eq_natCard 2 K).symm
  set e : ℕ := n * Module.finrank K E with he
  have hEcard : Nat.card E = 2 ^ e := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hKcard, pow_mul]
  have hEtwo : 2 ≤ Nat.card E := by
    haveI : Fintype E := Fintype.ofFinite E
    have h : 1 < Fintype.card E := Fintype.one_lt_card (α := E)
    rw [Nat.card_eq_fintype_card]
    omega
  have he1 : 1 ≤ e := by
    by_contra h
    have h0 : e = 0 := by omega
    rw [h0, pow_zero] at hEcard
    omega
  have hpad :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.padicValNat_card_statedProj_statedSL
      (p := 2) (m := e) (a := a) (K := E) Nat.prime_two he1 hEcard (by omega)
  have h504 : padicValNat 2 (Nat.card (StatedProj (StatedSL a E))) = 3 := by
    rw [hcardE]
    exact ltrspb3a_padicValNat_two_504
  have hek : e * (a * (a - 1) / 2) = 3 := by rw [← hpad, h504]
  have hndvd : n ∣ 3 := ⟨Module.finrank K E * (a * (a - 1) / 2), by
    have h1 : n * (Module.finrank K E * (a * (a - 1) / 2)) =
        e * (a * (a - 1) / 2) := by rw [he]; ring
    rw [h1, hek]⟩
  have h3dvd : 3 ∣ 2 ^ n - 1 := by
    rw [← hKcard]
    exact h3dvdK
  exact absurd h3dvd (ltrspb3a_not_three_dvd_two_pow_sub_one_of_dvd_three hndvd)

end S2MathAs3_1619Final

end
