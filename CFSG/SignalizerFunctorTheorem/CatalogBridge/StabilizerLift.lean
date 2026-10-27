module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue

public section

open CFSG.Open (signalizerFixedSubgroup)
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem centralizer_eq_bot_of_nonLocalized {X : Type*} [Group X] {C : Subgroup X}
    (hNL : NonLocalized C) : Subgroup.centralizer (C : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  refine hNL (Subgroup.zpowers y) (by rwa [Ne, Subgroup.zpowers_eq_bot]) inferInstance ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have hcy : c * y = y * c := Subgroup.mem_centralizer_iff.1 hy c hc
  have hcom : ∀ z ∈ Subgroup.zpowers y, c * z * c⁻¹ = z := by
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h : Commute c y := hcy
    rw [(h.zpow_right n).eq, mul_inv_cancel_right]
  intro z
  constructor
  · intro hz
    rw [hcom z hz]
    exact hz
  · intro hz
    have h1 : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    have hc' : c⁻¹ ∈ C := C.inv_mem hc
    have hcy' : c⁻¹ * y = y * c⁻¹ := Subgroup.mem_centralizer_iff.1 hy c⁻¹ hc'
    have h : Commute c⁻¹ y := hcy'
    have hz' : z ∈ Subgroup.zpowers y := by
      have hzc : c * z * c⁻¹ ∈ Subgroup.zpowers y := hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hzc
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      calc y ^ n = c⁻¹ * y ^ n * c := by
            rw [(h.zpow_right n).eq, inv_mul_cancel_right]
        _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hn]
        _ = z := h1
    exact hz'

theorem commutator_mem_inner_of_hom {X : Type*} [Group X] {A : Type*} [Group A]
    (hA : ∀ a b : A, a * b = b * a) (Θ : MulAut X →* A)
    (hker : Θ.ker = (MulAut.conj : X →* MulAut X).range) (a b : MulAut X) :
    ⁅a, b⁆ ∈ (MulAut.conj : X →* MulAut X).range := by
  rw [← hker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hA (Θ a) (Θ b)]
  group

theorem mem_zpowers_of_fixes_of_outer_abelian {X : Type*} [Group X] {δ : MulAut X}
    {N : Subgroup X} (hN : ∀ x, x ∈ N ↔ δ x = x)
    (hOut : ∀ a b : MulAut X, ⁅a, b⁆ ∈ (MulAut.conj : X →* MulAut X).range)
    (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (hS : ∀ β : MulAut X, β * δ = δ * β → (∀ x ∈ N, β x = x) → β ∈ Subgroup.zpowers δ)
    {g : MulAut X} (hg : ∀ x ∈ N, g x = x) : g ∈ Subgroup.zpowers δ := by
  obtain ⟨y, hy⟩ := hOut g δ
  have hfix : ∀ x ∈ N, ⁅g, δ⁆ x = x := by
    intro x hx
    have hδx : δ x = x := (hN x).1 hx
    have hδinv : δ⁻¹ x = x := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact hδx.symm
    have hginv : g⁻¹ x = x := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact (hg x hx).symm
    rw [commutatorElement_def]
    simp only [MulAut.mul_apply, hδinv, hginv, hδx, hg x hx]
  have hy1 : y = 1 := by
    have hyC : y ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hfix x hx
      rw [← hy, MulAut.conj_apply] at h1
      calc x * y = y * x * y⁻¹ * y := by rw [h1]
        _ = y * x := by group
    rw [hC, Subgroup.mem_bot] at hyC
    exact hyC
  have hcomm : ⁅g, δ⁆ = 1 := by rw [← hy, hy1, map_one]
  have hmul : g * δ = δ * g := (commutatorElement_eq_one_iff_mul_comm.1 hcomm)
  exact hS g hmul hg

theorem center_eq_bot_of_isSimpleGroup_of_noncomm {P : Type*} [Group P] (hs : IsSimpleGroup P)
    (hn : ∃ a b : P, a * b ≠ b * a) : Subgroup.center P = ⊥ := by
  have := hs
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center P) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have ha : a ∈ Subgroup.center P := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem isFStarSimple_of_derived_simple {G : Type*} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) (hs : IsSimpleGroup ↥(commutator G))
    (hn : ∃ a b : ↥(commutator G), a * b ≠ b * a) :
    McBride.Nonsolv.L514.IsFStarSimple G := by
  have : IsSimpleGroup ↥(commutator G) := hs
  have hZ' := center_eq_bot_of_isSimpleGroup_of_noncomm hs hn
  refine isFStarSimple_of_simple_normal (commutator G) hn ?_
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hdZ : d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hcd : ⁅d, g⁆ ∈ Subgroup.centralizer ((commutator G : Subgroup G) : Set G) := by
      rw [commutatorElement_def]
      have h1 : g * d * g⁻¹ ∈ Subgroup.centralizer ((commutator G : Subgroup G) : Set G) :=
        (inferInstance :
          (Subgroup.centralizer ((commutator G : Subgroup G) : Set G)).Normal).conj_mem d hd g
      have h2 := Subgroup.mul_mem _ hd (Subgroup.inv_mem _ h1)
      simpa [mul_assoc] using h2
    have hcm : ⁅d, g⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top d) (Subgroup.mem_top g)
    have hc1 : (⟨⁅d, g⁆, hcm⟩ : ↥(commutator G)) ∈ Subgroup.center ↥(commutator G) := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcd x x.2)
    rw [hZ', Subgroup.mem_bot] at hc1
    have hc2 : ⁅d, g⁆ = 1 := congrArg Subtype.val hc1
    rw [commutatorElement_eq_one_iff_mul_comm] at hc2
    exact hc2.symm
  rw [hZ] at hdZ
  exact hdZ

theorem fixedClauses_of_simple_normal_stabilizer {P : Type*} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) (hs : IsSimpleGroup P) (hn : ∃ a b : P, a * b ≠ b * a)
    (hpP : ¬ p ∣ Nat.card P) {a : MulAut P} (ha : orderOf a = p) {J N : Subgroup P}
    (hJN : J ≤ N) (hJnorm : (J.subgroupOf N).Normal) (hJs : IsSimpleGroup J)
    (hJn : ∃ x y : J, x * y ≠ y * x) (hfix : ∀ t, a t = t ↔ t ∈ N)
    (hJst : ∀ g : MulAut P, (∀ x ∈ J, g x = x) → g ∈ Subgroup.zpowers a)
    (hNL : FStarSimple (signalizerFixedSubgroup a) → NonLocalized (signalizerFixedSubgroup a)) :
    FixedClauses p (signalizerFixedSubgroup a) := by
  have hN : signalizerFixedSubgroup a = N := Subgroup.ext hfix
  have hZ := center_eq_bot_of_isSimpleGroup_of_noncomm hs hn
  have hC : Subgroup.centralizer ((J.subgroupOf N : Subgroup N) : Set N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hcomm : ∀ j ∈ J, j * (x : P) = (x : P) * j := by
      intro j hj
      have := hx ⟨j, hJN hj⟩ (Subgroup.mem_subgroupOf.mpr hj)
      exact congrArg Subtype.val this
    have hfixJ : ∀ j ∈ J, MulAut.conj (x : P) j = j := by
      intro j hj
      rw [MulAut.conj_apply, ← hcomm j hj]
      group
    have hmem := hJst _ hfixJ
    have hd1 : orderOf (MulAut.conj (x : P)) ∣ p := by
      rw [← ha]
      exact orderOf_dvd_of_mem_zpowers hmem
    have hd2 : orderOf (MulAut.conj (x : P)) ∣ Nat.card P :=
      (orderOf_map_dvd (MulAut.conj : P →* MulAut P) (x : P)).trans (orderOf_dvd_natCard _)
    have hcop : Nat.Coprime p (Nat.card P) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpP
    have h1 : orderOf (MulAut.conj (x : P)) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    have hone : MulAut.conj (x : P) = 1 := orderOf_eq_one_iff.mp h1
    have hcen : (x : P) ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun f : MulAut P => f g) hone
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * (x : P) = (x : P) * g * (x : P)⁻¹ * (x : P) := by rw [this]
        _ = (x : P) * g := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    exact (Subgroup.mem_bot).mpr (Subtype.ext hcen)
  have hFN : FStarSimple N := by
    have : (J.subgroupOf N).Normal := hJnorm
    have : IsSimpleGroup J := hJs
    let e : J.subgroupOf N ≃* J := Subgroup.subgroupOfEquivOfLe hJN
    have : IsSimpleGroup (J.subgroupOf N) := e.isSimpleGroup
    have hnJ : ∃ x y : J.subgroupOf N, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hJn
      exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by simpa using h))⟩
    exact (fStarSimple_iff_isFStarSimple N).mpr
      (isFStarSimple_of_simple_normal (J.subgroupOf N) hnJ hC)
  have hF : FStarSimple (signalizerFixedSubgroup a) := by
    rw [hN]
    exact hFN
  exact fixedClauses_of_stabilizer ha hF hNL fun g hg =>
    hJst g fun x hx => hg x ((hfix x).2 (hJN hx))

theorem fixedClauses_of_simple_fixed_S2 {X : Type*} [Group X] {p : ℕ} {δ : MulAut X}
    (hδ : orderOf δ = p) (hs : IsSimpleGroup (signalizerFixedSubgroup δ))
    (hn : ∃ a b : signalizerFixedSubgroup δ, a * b ≠ b * a)
    (hOut : ∀ a b : MulAut X, ⁅a, b⁆ ∈ (MulAut.conj : X →* MulAut X).range)
    (hS2 : ∀ β : MulAut X, β * δ = δ * β → (∀ x ∈ signalizerFixedSubgroup δ, β x = x) →
      β ∈ Subgroup.zpowers δ)
    (hNL : FStarSimple (signalizerFixedSubgroup δ) → NonLocalized (signalizerFixedSubgroup δ)) :
    FixedClauses p (signalizerFixedSubgroup δ) := by
  have hF : FStarSimple (signalizerFixedSubgroup δ) := fStarSimple_of_simple hs hn
  have hC : Subgroup.centralizer ((signalizerFixedSubgroup δ : Subgroup X) : Set X) = ⊥ :=
    centralizer_eq_bot_of_nonLocalized (hNL hF)
  exact fixedClauses_of_stabilizer hδ hF hNL fun g hg =>
    mem_zpowers_of_fixes_of_outer_abelian (δ := δ) (N := signalizerFixedSubgroup δ)
      (fun x => Iff.rfl) hOut hC hS2 hg

theorem hS2_of_centralizer_inf_eq_of_conj_mem {X : Type*} [Group X] (δ : MulAut X)
    (N : Subgroup X) (M : Subgroup (MulAut X)) (hM : ∀ m ∈ M, ∃ x ∈ N, MulAut.conj x = m)
    (hcent : Subgroup.centralizer {δ} ⊓ Subgroup.centralizer (M : Set (MulAut X)) =
      Subgroup.zpowers δ) :
    ∀ β : MulAut X, β * δ = δ * β → (∀ x ∈ N, β x = x) → β ∈ Subgroup.zpowers δ := by
  intro β hcomm hfix
  rw [← hcent]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hcomm.symm
  · rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨x, hx, rfl⟩ := hM m hm
    have h1 : β * MulAut.conj x * β⁻¹ = MulAut.conj x := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self,
        hfix x hx]
    calc MulAut.conj x * β = (β * MulAut.conj x * β⁻¹) * β := by rw [h1]
      _ = β * MulAut.conj x := by group

theorem not_mem_inner_range_of_orderOf {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hpX : ¬ p ∣ Nat.card X) {α : MulAut X} (hα : orderOf α = p) :
    α ∉ (MulAut.conj : X →* MulAut X).range := by
  rintro ⟨x, rfl⟩
  apply hpX
  rw [← hα]
  exact (orderOf_map_dvd (MulAut.conj : X →* MulAut X) x).trans (orderOf_dvd_natCard x)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
