module

public import CFSG.Permutation.FiveTransitive.Degree24Order96Support
public import CFSG.Permutation.FiveTransitive.Degree24Order96Automorphism
public import CFSG.Permutation.FiveTransitive.Degree24Order96CentralExclusion
public import CFSG.Permutation.FiveTransitive.Degree24Order96KernelGenerated
public import CFSG.Permutation.FiveTransitive.Degree24Order96NonTwelve
public import CFSG.Permutation.FiveTransitive.Degree24Order96Quotient

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private theorem card_support_eq_of_isConj
    {Y : Type} [Fintype Y] [DecidableEq Y]
    {a b : Equiv.Perm Y} (h : IsConj a b) :
    a.support.card = b.support.card := by
  rw [← a.sum_cycleType, ← b.sum_cycleType]
  exact congrArg Multiset.sum
    (Equiv.Perm.isConj_iff_cycleType_eq.mp h)

private theorem perm_six_order_two_support_cases
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (hYcard : Fintype.card Y = 6)
    (a : Equiv.Perm Y) (haOrder : orderOf a = 2) :
    a.support.card = 2 ∨
      a.support.card = 4 ∨
      a.support.card = 6 := by
  have haPrime : (orderOf a).Prime := by
    rw [haOrder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order haPrime
  have hsum := a.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, haOrder] at hsum
  have hsupportLe : a.support.card ≤ 6 := by
    calc
      a.support.card ≤ Fintype.card Y :=
        Finset.card_le_univ a.support
      _ = 6 := hYcard
  omega

private theorem image_swaps_have_equal_support
    (F B : Type)
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (α : Equiv.Perm F →* Equiv.Perm B)
    (τ σ : Equiv.Perm F)
    (hτ : τ.IsSwap) (hσ : σ.IsSwap) :
    (α τ).support.card = (α σ).support.card := by
  have hconj : IsConj τ σ := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq,
      Equiv.Perm.isSwap_iff_cycleType] at *
    exact hτ.trans hσ.symm
  exact
    card_support_eq_of_isConj
      (α.map_isConj hconj)

private theorem perm_six_centralizer_card_of_order_two_support_four
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (hYcard : Fintype.card Y = 6)
    (a : Equiv.Perm Y)
    (haOrder : orderOf a = 2)
    (haSupport : a.support.card = 4) :
    Nat.card
        (Subgroup.centralizer
          ({a} : Set (Equiv.Perm Y))) = 16 := by
  have haPrime : (orderOf a).Prime := by
    rw [haOrder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order haPrime
  have hsum := a.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, haOrder, haSupport] at hsum
  have hmTwo : m + 1 = 2 := by omega
  rw [Equiv.Perm.nat_card_centralizer,
    hm, haOrder, hmTwo, hYcard]
  norm_num

private theorem preimage_swap_support_six_of_swap_image_support_six
    (F B : Type)
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (hFcard : Fintype.card F = 6)
    (hBcard : Fintype.card B = 6)
    (α : Equiv.Perm F →* Equiv.Perm B)
    (hα : Function.Bijective α)
    (τ : Equiv.Perm F) (hτ : τ.IsSwap)
    (hατ : (α τ).support.card = 6)
    (β : Equiv.Perm B) (hβ : β.IsSwap) :
    ∃ δ : Equiv.Perm F,
      α δ = β ∧ δ.support.card = 6 := by
  classical
  obtain ⟨δ, hαδ⟩ := hα.2 β
  have hδOrder : orderOf δ = 2 := by
    rw [← orderOf_injective α hα.1, hαδ]
    exact hβ.orderOf
  rcases
      perm_six_order_two_support_cases
        F hFcard δ hδOrder with
    hδTwo | hδFour | hδSix
  · have hδSwap : δ.IsSwap :=
      Equiv.Perm.card_support_eq_two.mp hδTwo
    have heq :=
      image_swaps_have_equal_support
        F B α δ τ hδSwap hτ
    rw [hαδ,
      Equiv.Perm.card_support_eq_two.mpr hβ,
      hατ] at heq
    norm_num at heq
  · let e : Equiv.Perm F ≃* Equiv.Perm B :=
      MulEquiv.ofBijective α hα
    have hδCentralizer :
        Nat.card
            (Subgroup.centralizer
              ({δ} : Set (Equiv.Perm F))) = 16 :=
      perm_six_centralizer_card_of_order_two_support_four
        F hFcard δ hδOrder hδFour
    have hβCentralizer :
        Nat.card
            (Subgroup.centralizer
              ({β} : Set (Equiv.Perm B))) = 48 := by
      rw [Equiv.Perm.nat_card_centralizer,
        Equiv.Perm.isSwap_iff_cycleType.mp hβ,
        hBcard]
      norm_num
    have hcardEq :
        Nat.card
            (Subgroup.centralizer
              ({δ} : Set (Equiv.Perm F))) =
          Nat.card
            (Subgroup.centralizer
              ({β} : Set (Equiv.Perm B))) := by
      have h :=
        Nat.card_congr
          (centralizerEquivOfMulEquiv e δ)
      simpa only [e, MulEquiv.ofBijective_apply,
        hαδ] using h
    rw [hδCentralizer, hβCentralizer] at hcardEq
    norm_num at hcardEq
  · exact ⟨δ, hαδ, hδSix⟩

private theorem cycleSupport_eq_of_common_mem
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (g : Equiv.Perm Y)
    (b d : cycleSupportFinset g)
    {x : Y} (hxb : x ∈ b.1) (hxd : x ∈ d.1) :
    b = d := by
  classical
  obtain ⟨c, hc, hcb⟩ :=
    Finset.mem_image.mp b.2
  obtain ⟨e, he, hed⟩ :=
    Finset.mem_image.mp d.2
  have hxc : x ∈ c.support := by
    rwa [hcb]
  have hxe : x ∈ e.support := by
    rwa [hed]
  have hcEq :
      c = g.cycleOf x :=
    Equiv.Perm.cycle_is_cycleOf hxc hc
  have heEq :
      e = g.cycleOf x :=
    Equiv.Perm.cycle_is_cycleOf hxe he
  apply Subtype.ext
  rw [← hcb, ← hed, hcEq, heEq]

private theorem order_three_support_eq_eighteen_of_support_le_nineteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (w : P) (hwOrder : orderOf w = 3)
    (hwSupportLe :
      (w : Equiv.Perm X).support.card ≤ 19) :
    (w : Equiv.Perm X).support.card = 18 := by
  classical
  let g : Equiv.Perm X := w
  have hfixedCard :
      5 ≤ Fintype.card (Function.fixedPoints g) := by
    rw [Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard]
    change 5 ≤ 24 - (w : Equiv.Perm X).support.card
    omega
  let e : Fin 5 ↪ Function.fixedPoints g :=
    Classical.choice
      (Function.Embedding.nonempty_of_card_le
        hfixedCard)
  let eX : Fin 5 ↪ X :=
    e.trans (Function.Embedding.subtype _)
  let t : Set X := Set.range eX
  have ht : t.ncard = 5 := by
    rw [Set.ncard_range_of_injective eX.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hTcard :
      Nat.card (fixingSubgroup P t) = 96 := by
    have heq :=
      five_point_stabilizers_have_equal_card
        X P h5 s t hs ht
    rw [← heq]
    exact hHcard
  let wT : fixingSubgroup P t :=
    ⟨w, by
      rw [mem_fixingSubgroup_iff]
      rintro _ ⟨i, rfl⟩
      exact (e i).2⟩
  have hwTOrder : orderOf wT = 3 := by
    calc
      orderOf wT = orderOf (wT : P) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf w := by rfl
      _ = 3 := hwOrder
  simpa only [wT, g] using
    order_three_mem_five_stabilizer_support_eq_eighteen_of_card_eq_ninety_six
      X P hcard h5 hnotAlt t ht hTcard wT hwTOrder

private theorem exists_order_three_power_of_image_order_three
    (N Y : Type) [Group N] [Fintype N]
    [Group Y]
    (ρ : N →* Y) (c : N)
    (hcImage : orderOf (ρ c) = 3) :
    ∃ k : ℕ, orderOf (c ^ k) = 3 := by
  have hthreeDvd : 3 ∣ orderOf c := by
    rw [← hcImage]
    exact orderOf_map_dvd ρ c
  refine
    ⟨orderOf c / 3,
      orderOf_pow_orderOf_div
        (Nat.ne_of_gt (orderOf_pos c))
        hthreeDvd⟩

theorem five_point_stabilizer_card_ne_ninety_six
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 96 := by
  classical
  intro hHcard
  obtain ⟨u, _hUcard, _hNcard, hRange,
      hKerCard, t, htOrder, hinverts⟩ :=
    order96_cyclic_orderThree_inverting_kernel_data
      X P hcard h5 hnotAlt s hs hHcard
  let uP : P := u.1
  let R : Subgroup P := Subgroup.zpowers uP
  let F : Set X := MulAction.fixedPoints R X
  letI : Fintype F := Fintype.ofFinite F
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let r : R :=
    ⟨uP, Subgroup.mem_zpowers uP⟩
  have hRgenerated :
      R = Subgroup.zpowers (r : P) := by
    rfl
  have hrOrder : orderOf r = 3 := by
    rw [← Subgroup.orderOf_coe r]
    simpa only [r, uP] using u.2.1
  have hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18 := by
    simpa only [r, uP] using u.2.2
  let B :=
    cycleSupportFinset
      ((r : P) : Equiv.Perm X)
  let ψ : N →* Equiv.Perm B :=
    normalizerCycleSupportMap
      X P R r hRgenerated hrOrder
  let t₀ : ρ.ker := t
  have htSupport :
      (((((t₀ : ρ.ker) : N) : P) :
          Equiv.Perm X).support.card = 12) := by
    by_contra hne
    exact hnotAlt
      (alternatingGroup_le_of_order96_inverting_kernel_support_ne_twelve
        X P hcard h5 s hs hHcard u
          (by
            simpa only [ρ, N, F, R, uP] using
              hKerCard)
          t₀
          (by
            simpa only [t₀, ρ, N, F, R, uP] using
              htOrder)
          (by
            simpa only [MulAut.conj_apply, t₀,
              ρ, N, F, R, r, uP] using
              hinverts)
          (by
            simpa only [t₀, ρ, N, F, R, uP] using
              hne))
  have hker : ρ.ker ≤ ψ.ker := by
    simpa only [ψ, B, ρ, N, F, R, r, uP] using
      fixed_action_ker_le_cycleSupport_ker_of_support_twelve
        X P R r hRgenerated hrOrder hrSupport
          (by
            simpa only [ρ, N, F, R, uP] using
              hKerCard)
          t₀
          (by
            simpa only [t₀, ρ, N, F, R, uP] using
              htOrder)
          (by
            simpa only [MulAut.conj_apply, t₀,
              ρ, N, F, R, r, uP] using
              hinverts)
          (by
            simpa only [t₀, ρ, N, F, R, uP] using
              htSupport)
  obtain ⟨hFcardNat, _⟩ :=
    order96_cyclic_orderThree_normalizer_fixed_action
      X P hcard h5 s hs hHcard u
  have hFcard : Fintype.card F = 6 := by
    rw [← Nat.card_eq_fintype_card]
    simpa only [F, R, uP] using hFcardNat
  have hBcard : Fintype.card B = 6 := by
    simpa only [B] using
      cycleSupportFinset_card_of_order_three_support_eighteen
        ((r : P) : Equiv.Perm X)
        (by
          calc
            orderOf ((r : P) : Equiv.Perm X) =
                orderOf (r : P) :=
              Subgroup.orderOf_coe _
            _ = orderOf r :=
              Subgroup.orderOf_coe _
            _ = 3 := hrOrder)
        hrSupport
  have hρ : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    simpa only [ρ, N, F, R, uP] using hRange
  have hsmallOrFactor :=
    perm_six_factor_small_or_bijective
      N F B
        (by
          rw [Nat.card_eq_fintype_card, hFcard])
        (by
          rw [Nat.card_eq_fintype_card, hBcard])
        ρ hρ ψ hker
  obtain ⟨α, hα, hcomp⟩ :
      ∃ α : Equiv.Perm F →* Equiv.Perm B,
        Function.Bijective α ∧ α.comp ρ = ψ := by
    rcases hsmallOrFactor with hsmall | hfactor
    · have hCentralLe :
          Nat.card
              (FiveTransitive.NormalizerGoursat.centralizerCycleMap
                X P R r).range ≤
            Nat.card ψ.range := by
        simpa only [ψ, B] using
          centralizer_cycle_range_card_le_normalizer_cycleSupport_range_card
            X P R r hRgenerated hrOrder
      have hCycleSmall :
          Nat.card
              (FiveTransitive.NormalizerGoursat.centralizerCycleMap
                X P R r).range < 360 :=
        hCentralLe.trans_lt hsmall
      exact False.elim
        (hnotAlt
          (alternatingGroup_le_of_order96_cycle_range_small
            X P hcard h5 s hs hHcard u (by
              simpa only [uP, R, r] using
                hCycleSmall)))
    · exact hfactor
  let rN : N :=
    ⟨(r : P), R.le_normalizer r.prop⟩
  let tN : N := t₀
  have hrKer : ρ rN = 1 := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact
      MulAction.mem_fixedPoints.mp z.2 r
  have htKer : ρ tN = 1 := by
    exact t₀.prop
  have hrNOrder : orderOf rN = 3 := by
    calc
      orderOf rN = orderOf (rN : P) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf (r : P) := by rfl
      _ = orderOf r :=
        Subgroup.orderOf_coe _
      _ = 3 := hrOrder
  have hinvertsN :
      MulAut.conj tN rN = rN⁻¹ := by
    apply Subtype.ext
    change
      MulAut.conj (tN : P) (rN : P) =
        (rN : P)⁻¹
    simpa only [tN, t₀, rN, ρ, N, F, R, r, uP]
      using hinverts
  have hlift
      (a : Equiv.Perm F)
      (haOrder : orderOf a = 2) :
      ∃ q : N,
        orderOf q = 2 ∧
          Commute q rN ∧
          ρ q = a ∧
          ψ q = α a ∧
          ((((q : N) : P) :
              Equiv.Perm X).support.card =
            a.support.card +
              3 * (α a).support.card) := by
    obtain ⟨n, hnρ⟩ := hρ a
    have hnNormalizer :
        (n : P) ∈
          Subgroup.normalizer
            (Subgroup.zpowers (r : P) : Set P) := by
      simpa only [R, uP, r] using n.prop
    have hnConjP :=
      conj_eq_or_eq_inv_of_mem_normalizer_zpowers_order_three
        (r : P) (n : P)
          ((Subgroup.orderOf_coe r).trans hrOrder)
          hnNormalizer
    have hnConj :
        MulAut.conj n rN = rN ∨
          MulAut.conj n rN = rN⁻¹ := by
      exact hnConjP.imp
        (fun h => by
          apply Subtype.ext
          exact h)
        (fun h => by
          apply Subtype.ext
          exact h)
    obtain ⟨q, hqOrder, hqComm, hρq, hψq⟩ :=
      exists_involution_lift_of_order_two
        N F B ρ ψ hker
          (by
            simpa only [ρ, N, F, R, uP] using
              hKerCard)
          rN tN hrKer htKer hrNOrder hinvertsN
          α hcomp a haOrder n hnρ hnConj
    have hqOrderX :
        orderOf
            ((((q : N) : P) :
              Equiv.Perm X)) = 2 := by
      calc
        orderOf
            ((((q : N) : P) :
              Equiv.Perm X)) =
            orderOf ((q : N) : P) :=
          Subgroup.orderOf_coe _
        _ = orderOf q :=
          Subgroup.orderOf_coe _
        _ = 2 := hqOrder
    have hqCommX :
        Commute
          ((((q : N) : P) :
            Equiv.Perm X))
          ((r : P) : Equiv.Perm X) := by
      exact
        congrArg Subtype.val
          (congrArg Subtype.val hqComm.eq)
    have hformula :=
      normalizer_support_card_of_commuting_involution
        X P R r hRgenerated hrOrder q
          hqOrderX hqCommX
    refine ⟨q, hqOrder, hqComm, hρq, hψq, ?_⟩
    change
      ((((q : N) : P) :
          Equiv.Perm X).support.card =
        (ρ q).support.card +
          3 * (ψ q).support.card) at hformula
    rw [hρq, hψq] at hformula
    exact hformula
  let eF : Fin 3 ↪ F :=
    Classical.choice
      (Function.Embedding.nonempty_of_card_le
        (by rw [hFcard]; norm_num))
  let x : F := eF 0
  let y : F := eF 1
  let z : F := eF 2
  have hxy : x ≠ y := eF.injective.ne (by decide)
  have hyz : y ≠ z := eF.injective.ne (by decide)
  have hxz : x ≠ z := eF.injective.ne (by decide)
  let τ : Equiv.Perm F := Equiv.swap y x
  let σ : Equiv.Perm F := Equiv.swap y z
  have hτSwap : τ.IsSwap := by
    simpa only [τ, Equiv.Perm.swap_isSwap_iff] using
      hxy.symm
  have hσSwap : σ.IsSwap := by
    simpa only [σ, Equiv.Perm.swap_isSwap_iff] using
      hyz
  have hτσThree : (τ * σ).IsThreeCycle := by
    exact
      Equiv.Perm.isThreeCycle_swap_mul_swap_same
        hxy.symm hyz hxz
  have hατCases :
      (α τ).support.card = 2 ∨
        (α τ).support.card = 6 :=
    perm_six_bijectiveHom_swap_support
      F B hFcard hBcard α hα τ hτSwap
  rcases hατCases with hατTwo | hατSix
  · have hασTwo : (α σ).support.card = 2 := by
      rw [← hατTwo]
      exact
        image_swaps_have_equal_support
          F B α σ τ hσSwap hτSwap
    obtain
        ⟨q₁, _hq₁Order, _hq₁Comm, hρq₁,
          hψq₁, hq₁SupportFormula⟩ :=
      hlift τ hτSwap.orderOf
    obtain
        ⟨q₂, _hq₂Order, _hq₂Comm, hρq₂,
          hψq₂, hq₂SupportFormula⟩ :=
      hlift σ hσSwap.orderOf
    have hq₁Support :
        ((((q₁ : N) : P) :
          Equiv.Perm X).support.card = 8) := by
      rw [Equiv.Perm.card_support_eq_two.mpr hτSwap,
        hατTwo] at hq₁SupportFormula
      norm_num at hq₁SupportFormula ⊢
      exact hq₁SupportFormula
    have hq₂Support :
        ((((q₂ : N) : P) :
          Equiv.Perm X).support.card = 8) := by
      rw [Equiv.Perm.card_support_eq_two.mpr hσSwap,
        hασTwo] at hq₂SupportFormula
      norm_num at hq₂SupportFormula ⊢
      exact hq₂SupportFormula
    let p₁ : Equiv.Perm X := ((q₁ : N) : P)
    let p₂ : Equiv.Perm X := ((q₂ : N) : P)
    have hp₁Support : p₁.support.card = 8 := by
      simpa only [p₁] using hq₁Support
    have hp₂Support : p₂.support.card = 8 := by
      simpa only [p₂] using hq₂Support
    let c : N := q₁ * q₂
    let cPerm : Equiv.Perm X := ((c : N) : P)
    have hcPermEq : cPerm = p₁ * p₂ := by
      rfl
    have hρc : ρ c = τ * σ := by
      simp only [c, map_mul, hρq₁, hρq₂]
    have hρcOrder : orderOf (ρ c) = 3 := by
      rw [hρc]
      exact hτσThree.orderOf
    obtain ⟨k, hkOrder⟩ :=
      exists_order_three_power_of_image_order_three
        N (Equiv.Perm F) ρ c hρcOrder
    let wN : N := c ^ k
    let wP : P := wN
    have hwOrder : orderOf wP = 3 := by
      calc
        orderOf wP = orderOf wN :=
          Subgroup.orderOf_coe _
        _ = 3 := by
          simpa only [wN] using hkOrder
    have hcSupport :
        cPerm.support.card ≤ 16 := by
      calc
        cPerm.support.card ≤
            (p₁.support ∪ p₂.support).card := by
          apply Finset.card_le_card
          rw [hcPermEq]
          exact Equiv.Perm.support_mul_le p₁ p₂
        _ ≤
            p₁.support.card + p₂.support.card :=
          Finset.card_union_le p₁.support p₂.support
        _ = 16 := by rw [hp₁Support, hp₂Support]
    have hwSupport :
        (wP : Equiv.Perm X).support.card ≤ 16 := by
      have hpowPerm :
          (wP : Equiv.Perm X) = cPerm ^ k := by
        simp only [wP, wN, cPerm, Subgroup.coe_pow]
      calc
        (wP : Equiv.Perm X).support.card ≤
            cPerm.support.card := by
          apply Finset.card_le_card
          rw [hpowPerm]
          exact
            Equiv.Perm.support_pow_le cPerm k
        _ ≤ 16 := hcSupport
    have hwEighteen :=
      order_three_support_eq_eighteen_of_support_le_nineteen
        X P hcard h5 hnotAlt s hs hHcard
          wP hwOrder (by omega)
    omega
  · let eB : Fin 3 ↪ B :=
      Classical.choice
        (Function.Embedding.nonempty_of_card_le
          (by rw [hBcard]; norm_num))
    let b₀ : B := eB 0
    let b₁ : B := eB 1
    let b₂ : B := eB 2
    have hb₀b₁ : b₀ ≠ b₁ :=
      eB.injective.ne (by decide)
    have hb₁b₂ : b₁ ≠ b₂ :=
      eB.injective.ne (by decide)
    have hb₀b₂ : b₀ ≠ b₂ :=
      eB.injective.ne (by decide)
    let β₁ : Equiv.Perm B := Equiv.swap b₁ b₀
    let β₂ : Equiv.Perm B := Equiv.swap b₁ b₂
    have hβ₁Swap : β₁.IsSwap := by
      simpa only [β₁, Equiv.Perm.swap_isSwap_iff] using
        hb₀b₁.symm
    have hβ₂Swap : β₂.IsSwap := by
      simpa only [β₂, Equiv.Perm.swap_isSwap_iff] using
        hb₁b₂
    have hβProdThree :
        (β₁ * β₂).IsThreeCycle := by
      exact
        Equiv.Perm.isThreeCycle_swap_mul_swap_same
          hb₀b₁.symm hb₁b₂ hb₀b₂
    obtain ⟨δ₁, hαδ₁, hδ₁Support⟩ :=
      preimage_swap_support_six_of_swap_image_support_six
        F B hFcard hBcard α hα τ hτSwap hατSix
          β₁ hβ₁Swap
    obtain ⟨δ₂, hαδ₂, hδ₂Support⟩ :=
      preimage_swap_support_six_of_swap_image_support_six
        F B hFcard hBcard α hα τ hτSwap hατSix
          β₂ hβ₂Swap
    have hδ₁Order : orderOf δ₁ = 2 := by
      rw [← orderOf_injective α hα.1, hαδ₁]
      exact hβ₁Swap.orderOf
    have hδ₂Order : orderOf δ₂ = 2 := by
      rw [← orderOf_injective α hα.1, hαδ₂]
      exact hβ₂Swap.orderOf
    obtain
        ⟨q₁, _hq₁Order, _hq₁Comm, hρq₁,
          hψq₁, hq₁SupportFormula⟩ :=
      hlift δ₁ hδ₁Order
    obtain
        ⟨q₂, _hq₂Order, _hq₂Comm, hρq₂,
          hψq₂, hq₂SupportFormula⟩ :=
      hlift δ₂ hδ₂Order
    have hq₁Support :
        ((((q₁ : N) : P) :
          Equiv.Perm X).support.card = 12) := by
      rw [hδ₁Support, hαδ₁,
        Equiv.Perm.card_support_eq_two.mpr hβ₁Swap]
          at hq₁SupportFormula
      norm_num at hq₁SupportFormula ⊢
      exact hq₁SupportFormula
    have hq₂Support :
        ((((q₂ : N) : P) :
          Equiv.Perm X).support.card = 12) := by
      rw [hδ₂Support, hαδ₂,
        Equiv.Perm.card_support_eq_two.mpr hβ₂Swap]
          at hq₂SupportFormula
      norm_num at hq₂SupportFormula ⊢
      exact hq₂SupportFormula
    let p₁ : Equiv.Perm X := ((q₁ : N) : P)
    let p₂ : Equiv.Perm X := ((q₂ : N) : P)
    have hp₁Support : p₁.support.card = 12 := by
      simpa only [p₁] using hq₁Support
    have hp₂Support : p₂.support.card = 12 := by
      simpa only [p₂] using hq₂Support
    have hδ₁SupportUniv :
        δ₁.support = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
        (Finset.subset_univ δ₁.support)
      rw [hδ₁Support, Finset.card_univ, hFcard]
    have hδ₂SupportUniv :
        δ₂.support = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
        (Finset.subset_univ δ₂.support)
      rw [hδ₂Support, Finset.card_univ, hFcard]
    let g : Equiv.Perm X := (r : P)
    have hgOrder : orderOf g = 3 := by
      calc
        orderOf g = orderOf (r : P) :=
          Subgroup.orderOf_coe _
        _ = orderOf r :=
          Subgroup.orderOf_coe _
        _ = 3 := hrOrder
    have hgSupport : g.support.card = 18 := by
      simpa only [g] using hrSupport
    have hblockSubset :
        b₁.1 ⊆ g.support := by
      obtain ⟨d, hd, hdb⟩ :=
        Finset.mem_image.mp b₁.2
      rw [← hdb]
      exact
        Equiv.Perm.mem_cycleFactorsFinset_support_le
          hd
    have hFBlockDisjoint :
        Disjoint F.toFinset b₁.1 := by
      rw [Finset.disjoint_left]
      intro a haF hab
      have haFixed :=
        MulAction.mem_fixedPoints.mp
          (Set.mem_toFinset.mp haF) r
      exact
        Equiv.Perm.mem_support.mp
          (hblockSubset hab)
          (by
            simpa [g, Subgroup.smul_def,
              Equiv.Perm.smul_def] using haFixed)
    have hFtoFinsetCard :
        F.toFinset.card = 6 := by
      rw [← Set.ncard_eq_toFinset_card' F,
        ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card, hFcard]
    have hb₁Card : b₁.1.card = 3 :=
      mem_cycleSupportFinset_card_three
        g hgOrder hgSupport b₁.1
          (by simpa only [B, g] using b₁.2)
    have hcommonCard :
        (F.toFinset ∪ b₁.1).card = 9 := by
      rw [Finset.card_union_of_disjoint hFBlockDisjoint,
        hFtoFinsetCard, hb₁Card]
    have hβ₁Moves : β₁ b₁ ≠ b₁ := by
      simp only [β₁, Equiv.swap_apply_left]
      exact hb₀b₁
    have hβ₂Moves : β₂ b₁ ≠ b₁ := by
      simp only [β₂, Equiv.swap_apply_left]
      exact hb₁b₂.symm
    have hmovedSubset
        (q : N)
        (δ : Equiv.Perm F)
        (β : Equiv.Perm B)
        (hρq : ρ q = δ)
        (hψq : ψ q = β)
        (hδSupportUniv :
          δ.support = Finset.univ)
        (hβMoves : β b₁ ≠ b₁) :
        F.toFinset ∪ b₁.1 ⊆
          ((((q : N) : P) :
            Equiv.Perm X).support) := by
      intro a ha
      rw [Finset.mem_union] at ha
      rcases ha with haF | hab
      · have haF' : a ∈ F :=
          Set.mem_toFinset.mp haF
        have haMoved :
            δ ⟨a, haF'⟩ ≠ ⟨a, haF'⟩ := by
          apply Equiv.Perm.mem_support.mp
          rw [hδSupportUniv]
          exact Finset.mem_univ _
        rw [Equiv.Perm.mem_support]
        intro haFixed
        apply haMoved
        rw [← hρq]
        apply Subtype.ext
        exact haFixed
      · rw [Equiv.Perm.mem_support]
        intro haFixed
        have haImage :
            a ∈ ((ψ q) b₁).1 := by
          have hval :=
            normalizerCycleSupportMap_apply_val
              X P R r hRgenerated hrOrder q b₁
          change
            ((ψ q) b₁).1 =
              ((q : N) : P) • b₁.1 at hval
          rw [hval]
          exact
            Finset.mem_smul_finset.mpr
              ⟨a, hab, haFixed⟩
        have heq :
            (ψ q) b₁ = b₁ :=
          cycleSupport_eq_of_common_mem
            g ((ψ q) b₁) b₁ haImage hab
        apply hβMoves
        rw [← hψq]
        exact heq
    have hcommonLe₁ :
        F.toFinset ∪ b₁.1 ⊆ p₁.support := by
      have hψq₁' : ψ q₁ = β₁ :=
        hψq₁.trans hαδ₁
      simpa only [p₁] using
        hmovedSubset q₁ δ₁ β₁ hρq₁ hψq₁'
          hδ₁SupportUniv hβ₁Moves
    have hcommonLe₂ :
        F.toFinset ∪ b₁.1 ⊆ p₂.support := by
      have hψq₂' : ψ q₂ = β₂ :=
        hψq₂.trans hαδ₂
      simpa only [p₂] using
        hmovedSubset q₂ δ₂ β₂ hρq₂ hψq₂'
          hδ₂SupportUniv hβ₂Moves
    have hinterCard :
        9 ≤ (p₁.support ∩ p₂.support).card := by
      rw [← hcommonCard]
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_inter]
      exact ⟨hcommonLe₁ ha, hcommonLe₂ ha⟩
    have hunionCard :
        (p₁.support ∪ p₂.support).card ≤ 15 := by
      have hsum :=
        Finset.card_union_add_card_inter
          p₁.support p₂.support
      rw [hp₁Support, hp₂Support] at hsum
      omega
    let c : N := q₁ * q₂
    let cPerm : Equiv.Perm X := ((c : N) : P)
    have hcPermEq : cPerm = p₁ * p₂ := by
      rfl
    have hρc : ρ c = δ₁ * δ₂ := by
      simp only [c, map_mul, hρq₁, hρq₂]
    have hδProdOrder :
        orderOf (δ₁ * δ₂) = 3 := by
      rw [← orderOf_injective α hα.1,
        map_mul, hαδ₁, hαδ₂]
      exact hβProdThree.orderOf
    have hρcOrder : orderOf (ρ c) = 3 := by
      rw [hρc]
      exact hδProdOrder
    obtain ⟨k, hkOrder⟩ :=
      exists_order_three_power_of_image_order_three
        N (Equiv.Perm F) ρ c hρcOrder
    let wN : N := c ^ k
    let wP : P := wN
    have hwOrder : orderOf wP = 3 := by
      calc
        orderOf wP = orderOf wN :=
          Subgroup.orderOf_coe _
        _ = 3 := by
          simpa only [wN] using hkOrder
    have hcSupport :
        cPerm.support.card ≤ 15 := by
      calc
        cPerm.support.card ≤
            (p₁.support ∪ p₂.support).card := by
          apply Finset.card_le_card
          rw [hcPermEq]
          exact Equiv.Perm.support_mul_le p₁ p₂
        _ ≤ 15 := hunionCard
    have hwSupport :
        (wP : Equiv.Perm X).support.card ≤ 15 := by
      have hpowPerm :
          (wP : Equiv.Perm X) = cPerm ^ k := by
        simp only [wP, wN, cPerm, Subgroup.coe_pow]
      calc
        (wP : Equiv.Perm X).support.card ≤
            cPerm.support.card := by
          apply Finset.card_le_card
          rw [hpowPerm]
          exact
            Equiv.Perm.support_pow_le cPerm k
        _ ≤ 15 := hcSupport
    have hwEighteen :=
      order_three_support_eq_eighteen_of_support_le_nineteen
        X P hcard h5 hnotAlt s hs hHcard
          wP hwOrder (by omega)
    omega

end FiveTransitive.Degree24

end CFSG
