module

public import CFSG.Permutation.FiveTransitive.Degree24Order96Goursat
public import CFSG.Permutation.FiveTransitive.Degree24Order96Kernel

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_order96_centralizing_kernel_involution
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (u : OrderPrimeSupportElements X P 3 18) :
    let R : Subgroup P := Subgroup.zpowers (u.1 : P)
    let F₀ : Set X := MulAction.fixedPoints R X
    let N : Subgroup P := Subgroup.normalizer (R : Set P)
    let ρ₀ : N →* Equiv.Perm F₀ :=
      MulAction.toPermHom N F₀
    ∀ (_hKerCard : Nat.card ρ₀.ker = 6)
      (t : ρ₀.ker),
      orderOf t = 2 →
      MulAut.conj
          ((((t : ρ₀.ker) : N) : P))
          (u.1 : P) =
        (u.1 : P) →
      alternatingGroup X ≤ P := by
  classical
  dsimp
  intro hKerCard t htOrder hcentral
  let uP : P := u.1
  let R : Subgroup P := Subgroup.zpowers uP
  let F₀ : Set X := MulAction.fixedPoints R X
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ₀ : N →* Equiv.Perm F₀ :=
    MulAction.toPermHom N F₀
  let SN : Subgroup N := R.subgroupOf N
  let F : Set X := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let r : R :=
    ⟨uP, Subgroup.mem_zpowers uP⟩
  let g : Equiv.Perm X := uP
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hF_eq_F₀ : F = F₀ := by
    ext x
    rw [MulAction.mem_fixedPoints,
      MulAction.mem_fixedPoints]
    constructor
    · intro hx q
      let qN : N :=
        ⟨q, R.le_normalizer q.prop⟩
      let qSN : SN := ⟨qN, q.prop⟩
      exact hx qSN
    · intro hx q
      let qR : R :=
        ⟨((q : SN) : N), q.prop⟩
      exact hx qR
  have hfixed₀ :
      F₀ = Function.fixedPoints g := by
    ext x
    rw [MulAction.mem_fixedPoints,
      Function.mem_fixedPoints_iff]
    constructor
    · intro hx
      exact hx
        ⟨uP, Subgroup.mem_zpowers uP⟩
    · intro hx z
      have huStab :
          uP ∈ MulAction.stabilizer P x := by
        rw [MulAction.mem_stabilizer_iff]
        exact hx
      have hzStab :
          (z : P) ∈ MulAction.stabilizer P x :=
        (Subgroup.zpowers_le.mpr huStab) z.prop
      exact MulAction.mem_stabilizer_iff.mp hzStab
  have hfixed :
      F = Function.fixedPoints g :=
    hF_eq_F₀.trans hfixed₀
  obtain ⟨hF₀card, _⟩ :=
    order96_cyclic_orderThree_normalizer_fixed_action
      X P hcard h5 s hs hHcard u
  have hFcard : Nat.card F = 6 := by
    rw [hF_eq_F₀]
    simpa only [F₀, R, uP] using hF₀card
  have huPOrder : orderOf uP = 3 := by
    simpa only [uP] using u.2.1
  have hN5 :
      ∀ a b : Fin 5 → F,
        Function.Injective a →
        Function.Injective b →
        ∃ c : N, ∀ i, c • a i = b i := by
    intro a b ha hb
    let aX : Fin 5 ↪ X := {
      toFun := fun i => (a i).1
      inj' := fun i j hij =>
        ha (Subtype.ext hij) }
    let bX : Fin 5 ↪ X := {
      toFun := fun i => (b i).1
      inj' := fun i j hij =>
        hb (Subtype.ext hij) }
    let uN : N :=
      ⟨uP, R.le_normalizer
        (Subgroup.mem_zpowers uP)⟩
    let uSN : SN :=
      ⟨uN, Subgroup.mem_zpowers uP⟩
    have haFix (i : Fin 5) :
        uP • aX i = aX i := by
      exact
        MulAction.mem_fixedPoints.mp
          (a i).prop uSN
    have hbFix (i : Fin 5) :
        uP • bX i = bX i := by
      exact
        MulAction.mem_fixedPoints.mp
          (b i).prop uSN
    obtain ⟨c, hcNormalizer, hc⟩ :=
      order96_cyclic_orderThree_normalizer_maps_fixed_five_tuples
        X P h5 s hs hHcard uP huPOrder
          aX bX haFix hbFix
    let cN : N :=
      ⟨c, by
        simpa only [N, R] using hcNormalizer⟩
    refine ⟨cN, ?_⟩
    intro i
    apply Subtype.ext
    exact hc i
  let Q : Subgroup (Equiv.Perm F) := ρ.range
  have hQ5 :
      MulAction.IsMultiplyPretransitive Q F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨c, hc⟩ :=
      hN5 a b a.injective b.injective
    let q : Q := ⟨ρ c, ⟨c, rfl⟩⟩
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hc i)
  letI :
      MulAction.IsMultiplyPretransitive Q F 5 :=
    hQ5
  have hQdegree :
      MulAction.IsMultiplyPretransitive
        Q F (Nat.card F - 1) := by
    exact
      MulAction.isMultiplyPretransitive_of_le
        (by rw [hFcard])
        (by rw [hFcard]; norm_num)
  have hQtop : Q = ⊤ :=
    Equiv.Perm.eq_top_of_isMultiplyPretransitive
      hQdegree
  have hRangeTop : ρ.range = ⊤ := by
    simpa only [Q] using hQtop
  have hAlt :
      alternatingGroup F ≤ ρ.range := by
    rw [hRangeTop]
    exact le_top
  letI : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card, hFcard]
      norm_num)
  have hAltCard :
      Nat.card (alternatingGroup F) = 360 := by
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup,
      ← Nat.card_eq_fintype_card, hFcard]
    norm_num
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers]
    simpa only [uP] using u.2.1
  letI : IsCyclic R := by
    dsimp only [R]
    infer_instance
  have hAutCard :
      Nat.card (MulAut R) = 2 := by
    rw [IsCyclic.card_mulAut R, hRcard,
      Nat.totient_prime (by norm_num : Nat.Prime 3)]
  have hrOrder : orderOf r = 3 := by
    rw [← Subgroup.orderOf_coe r]
    simpa only [r, uP] using u.2.1
  have hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18 := by
    simpa only [r, uP] using u.2.2
  have hRgenerated :
      R = Subgroup.zpowers (r : P) := by
    rfl
  let t₀ : ρ₀.ker := t
  have hCycleSmall :
      Nat.card
          (FiveTransitive.NormalizerGoursat.centralizerCycleMap
            X P R r).range < 360 := by
    exact
      centralizer_cycle_range_small_of_kernel_involution
        X P R r hRgenerated
        (by
          simpa only [ρ₀, N, F₀, R, uP] using
            hKerCard)
        t₀ hrOrder hrSupport
        (by
          simpa only [t₀, ρ₀, N, F₀, R, uP] using
            htOrder)
        (by
          simpa only [MulAut.conj_apply, t₀, ρ₀,
            N, F₀, R, r, uP] using
            hcentral)
  have hgOrder : orderOf g = 3 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = 3 := huPOrder
  have hgSupport : g.support.card = 18 := by
    simpa only [g, uP] using u.2.2
  have hKernelCard :
      Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom
            gSupport).ker = 729 := by
    simpa only [gSupport] using
      cycle_factor_kernel_card_of_order_three_support_eighteen
        g hgOrder hgSupport
  apply
    FiveTransitive.NormalizerGoursat.alternatingGroup_le_of_fixed_action_cycle_kernel
      X P (by omega) h5 R r
  · simpa only [F, SN, N, g, r, uP] using hfixed
  · change 5 ≤ Fintype.card F
    rw [← Nat.card_eq_fintype_card, hFcard]
    norm_num
  · simpa only [N, SN, F, ρ] using hAlt
  · change
      Nat.card (MulAut R) <
        Nat.card (alternatingGroup F)
    rw [hAutCard, hAltCard]
    norm_num
  · change
      Nat.card
          (FiveTransitive.NormalizerGoursat.centralizerCycleMap
            X P R r).range <
        Nat.card (alternatingGroup F)
    rw [hAltCard]
    exact hCycleSmall
  · change
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom
            gSupport).ker
    rw [hAltCard, hKernelCard]
    norm_num

theorem order96_cyclic_orderThree_inverting_kernel_data
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96) :
    let U := OrderPrimeSupportElements X P 3 18
    ∃ u : U,
      let R : Subgroup P := Subgroup.zpowers (u.1 : P)
      let F : Set X := MulAction.fixedPoints R X
      let N : Subgroup P :=
        Subgroup.normalizer (R : Set P)
      let ρ : N →* Equiv.Perm F :=
        MulAction.toPermHom N F
      Nat.card U = 226688 ∧
        Nat.card N = 4320 ∧
        ρ.range = ⊤ ∧
        Nat.card ρ.ker = 6 ∧
        ∃ t : ρ.ker,
          orderOf t = 2 ∧
            MulAut.conj
                ((((t : ρ.ker) : N) : P))
                (u.1 : P) =
              (u.1 : P)⁻¹ := by
  classical
  dsimp
  obtain ⟨u, hUcard, hNcard, hRange,
      hKerCard, t, htOrder, _⟩ :=
    order96_cyclic_orderThree_fixed_action_kernel_data
      X P hcard h5 hnotAlt s hs hHcard
  let R : Subgroup P :=
    Subgroup.zpowers (u.1 : P)
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let t₀ : ρ.ker := t
  let tN : N := t₀
  let tP : P := tN
  have htNormalizer :
      tP ∈ Subgroup.normalizer
        (Subgroup.zpowers (u.1 : P) : Set P) := by
    simpa only [tP, tN, t₀, ρ, N, F, R] using
      tN.prop
  have hdichotomy :=
    conj_eq_or_eq_inv_of_mem_normalizer_zpowers_order_three
      (u.1 : P) tP u.2.1 htNormalizer
  have hinverts :
      MulAut.conj tP (u.1 : P) =
        (u.1 : P)⁻¹ := by
    rcases hdichotomy with hcentral | hinverts
    · exact False.elim
        (hnotAlt
          (alternatingGroup_le_of_order96_centralizing_kernel_involution
            X P hcard h5 s hs hHcard u
              (by
                simpa only [ρ, N, F, R] using hKerCard)
              t₀
              (by
                simpa only [t₀, ρ, N, F, R] using
                  htOrder)
              (by
                simpa only [tP, tN, t₀, ρ, N, F, R] using
                  hcentral)))
    · exact hinverts
  refine ⟨u, hUcard, ?_, ?_, ?_, t₀, ?_, ?_⟩
  · simpa only [N, R] using hNcard
  · simpa only [ρ, N, F, R] using hRange
  · simpa only [ρ, N, F, R] using hKerCard
  · simpa only [t₀, ρ, N, F, R] using htOrder
  · simpa only [MulAut.conj_apply, tP, tN] using hinverts

end FiveTransitive.Degree24

end CFSG
