module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG


/-!
# Shared infrastructure for the PSL₂ Fact 1.10(ii) normalizer centralization

Common helpers used by the D-group model cases of the classification of
`N = N_G(X)` (the A₇, PSL₂, and PGL₂ quotient cases):

* the odd-order and containment facts for `N_F(X) ≤ F(U) ∩ N`;
* the layer-centralizes-`O₂'(N)` fact and the perfect-layer
  central-automorphism tail: if the induced action on `E(N)/O₂'(N)` is
  trivial, the element centralizes `E(N)`;
* the cardinality bound `|E/Z(E)| ≤ |image of E|` for a quotient with
  kernel contained in the center.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## The Fact 1.10(ii) inner-action hypothesis -/

/-- Bender's Fact 1.10(ii) for the normalizer `N = N_G(X)`: every element of
`F(U) ∩ N` (the odd Fitting part of the transported involution centralizer)
induces an inner automorphism on the component layer `E(N)`.  This is the
semilinear field-projection transport, isolated so that the PSL₂ and PGL₂
model cases can be discharged independently. -/
@[expose] public def secondCase_psl2_normalizer_innerAction
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (X : Subgroup G) : Prop :=
  ∀ p ∈ (c.FU ⊓ Subgroup.normalizer (X : Set G)),
    ∃ ℓ ∈ componentLayerOf (Subgroup.normalizer (X : Set G)),
      ∀ x ∈ componentLayerOf (Subgroup.normalizer (X : Set G)),
        p * x * p⁻¹ = ℓ * x * ℓ⁻¹

/-! ## Small generic helpers -/

/-- The elements of `F` that normalize `X` lie in `F(U) ∩ N_G(X)`. -/
public theorem normalizerInF_le_fu_inter_normalizer
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) :
    normalizerInF F X ≤ c.FU ⊓ Subgroup.normalizer (X : Set G) := by
  intro f hf
  exact ⟨hFleFU hf.1, hf.2⟩

/-- An element of `F` has odd order: `F ≤ F(U) ⊆ U = O₂'(H)`. -/
public theorem orderOf_mem_normalizerInF_odd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) {f : G} (hf : f ∈ normalizerInF F X) :
    Odd (orderOf f) := by
  have hfU : f ∈ c.U := fittingSubgroupOf_le c.U (hFleFU hf.1)
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  exact Odd.of_dvd_nat hUodd (Subgroup.orderOf_dvd_natCard c.U hfU)

/-- A subgroup containing a nontrivial subgroup is nontrivial. -/
public theorem ne_bot_of_le_ne_bot
    {G : Type u} [Group G] (A B : Subgroup G)
    (hAB : A ≤ B) (hAne : A ≠ ⊥) : B ≠ ⊥ := by
  intro hB
  apply hAne
  rw [hB] at hAB
  exact le_bot_iff.mp hAB

/-- The layer of `N` centralizes the odd core of `N`: the odd core is a
solvable subgroup of `N` normalized by the layer. -/
public theorem layer_centralizes_oddCore
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) :
    componentLayerOf N ≤
      Subgroup.centralizer (((pPrimeCore 2 N).map N.subtype) : Set G) := by
  let Oamb : Subgroup G := (pPrimeCore 2 N).map N.subtype
  have hOleN : Oamb ≤ N := Subgroup.map_subtype_le (pPrimeCore 2 N)
  have hOodd : Odd (Nat.card (pPrimeCore 2 N)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := N))
  have hOsolv : Group.IsSolvable (pPrimeCore 2 N) :=
    odd_order_theorem (pPrimeCore 2 N) hOodd
  have hOamb_solvable : Group.IsSolvable Oamb :=
    isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective (pPrimeCore 2 N) N.subtype
        N.subtype_injective)
  have hOamb_normal : IsNormalIn Oamb N := by
    refine ⟨hOleN, ?_⟩
    intro n hn o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨n, hn⟩ : N) * o0 * (⟨n, hn⟩ : N)⁻¹,
        (pPrimeCore_normal (p := 2) (G := N)).conj_mem
          o0 ho0 (⟨n, hn⟩ : N), rfl⟩
  have hL_norm_O : componentLayerOf N ≤ Subgroup.normalizer (Oamb : Set G) :=
    (componentLayerOf_isNormalIn N).1.trans
      (le_normalizer_of_isNormalIn hOamb_normal)
  have hcomm : ⁅componentLayerOf N, Oamb⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      N Oamb hOleN hOamb_solvable hL_norm_O
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := componentLayerOf N) (H₂ := Oamb)).mp hcomm

/-- Conjugation by `f ∈ N` on a normal subgroup `L` of `N`. -/
@[expose] public def conjOnSubgroup
    {G : Type u} [Group G]
    (N L : Subgroup G) (f : G) (hf : f ∈ N)
    (hLnorm : IsNormalIn L N) : L →* L :=
  { toFun := fun x => ⟨f * (x : G) * f⁻¹, hLnorm.2 f hf (x : G) x.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change f * ((x : G) * (y : G)) * f⁻¹ =
        (f * (x : G) * f⁻¹) * (f * (y : G) * f⁻¹)
      group }

/-- The inverse of `conjOnSubgroup`, conjugation by `f⁻¹`. -/
public def conjOnSubgroupInv
    {G : Type u} [Group G]
    (N L : Subgroup G) (f : G) (hf : f ∈ N)
    (hLnorm : IsNormalIn L N) : L →* L :=
  conjOnSubgroup N L f⁻¹ (N.inv_mem hf) hLnorm

public theorem conjOnSubgroup_left
    {G : Type u} [Group G]
    (N L : Subgroup G) (f : G) (hf : f ∈ N)
    (hLnorm : IsNormalIn L N) (x : L) :
    conjOnSubgroupInv N L f hf hLnorm (conjOnSubgroup N L f hf hLnorm x) = x := by
  apply Subtype.ext
  simp [conjOnSubgroup, conjOnSubgroupInv]
  group

public theorem conjOnSubgroup_right
    {G : Type u} [Group G]
    (N L : Subgroup G) (f : G) (hf : f ∈ N)
    (hLnorm : IsNormalIn L N) (x : L) :
    conjOnSubgroup N L f hf hLnorm (conjOnSubgroupInv N L f hf hLnorm x) = x := by
  apply Subtype.ext
  simp [conjOnSubgroup, conjOnSubgroupInv]
  group

/-- The conjugation automorphism of a normal subgroup induced by an element
of the overgroup. -/
@[expose] public def conjOnSubgroupEquiv
    {G : Type u} [Group G]
    (N L : Subgroup G) (f : G) (hf : f ∈ N)
    (hLnorm : IsNormalIn L N) : L ≃* L :=
  MulEquiv.ofBijective (conjOnSubgroup N L f hf hLnorm) ⟨
    (Function.LeftInverse.injective (conjOnSubgroup_left N L f hf hLnorm)),
    (fun y => ⟨conjOnSubgroupInv N L f hf hLnorm y,
      conjOnSubgroup_right N L f hf hLnorm y⟩)⟩

/-- If the induced action of `f` on the image of the layer in `N/O₂'(N)` is
trivial, then `f` centralizes the layer: the automorphism of the perfect
layer induced by `f` is a central automorphism, hence the identity. -/
public theorem centralizes_layer_of_quotient_action_trivial
    {G : Type u} [Group G] [Finite G]
    (N L : Subgroup G) (f : G)
    (hLleN : L ≤ N) (hLnorm : IsNormalIn L N) (hfN : f ∈ N)
    (hLperf : Group.IsPerfect L)
    (hLcentO : L ≤ Subgroup.centralizer
      (((pPrimeCore 2 N).map N.subtype) : Set G))
    (hquot : ∀ x : L,
      QuotientGroup.mk' (pPrimeCore 2 N)
          (⟨f * (x : G) * f⁻¹, hLnorm.1 (hLnorm.2 f hfN (x : G) x.2)⟩ : N) =
        QuotientGroup.mk' (pPrimeCore 2 N) (⟨(x : G), hLleN x.2⟩ : N)) :
    f ∈ Subgroup.centralizer (L : Set G) := by
  classical
  let O : Subgroup N := pPrimeCore 2 N
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  let α : L ≃* L := conjOnSubgroupEquiv N L f hfN hLnorm
  have hdelta : ∀ x : L, α x * x⁻¹ ∈ Subgroup.center L := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    let a : N := ⟨f * (x : G) * f⁻¹, hLnorm.1 (hLnorm.2 f hfN (x : G) x.2)⟩
    let b : N := ⟨(x : G), hLleN x.2⟩
    have hqab : q (a * b⁻¹) = 1 := by
      calc
        q (a * b⁻¹) = q a * q (b⁻¹) := map_mul q a (b⁻¹)
        _ = q a * (q b)⁻¹ := by rw [map_inv]
        _ = q b * (q b)⁻¹ := by rw [hquot x]
        _ = 1 := by simp
    have habO : (a * b⁻¹ : N) ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) (a * b⁻¹)).mp hqab
    have hcO : (f * (x : G) * f⁻¹) * (x : G)⁻¹ ∈
        (pPrimeCore 2 N).map N.subtype := by
      refine Subgroup.mem_map.mpr ⟨a * b⁻¹, habO, ?_⟩
      change ((a * b⁻¹ : N) : G) = (f * (x : G) * f⁻¹) * (x : G)⁻¹
      rfl
    have hcent := (Subgroup.mem_centralizer_iff.mp (hLcentO y.2))
      ((f * (x : G) * f⁻¹) * (x : G)⁻¹) hcO
    change (y : G) * ((f * (x : G) * f⁻¹) * (x : G)⁻¹) =
      (f * (x : G) * f⁻¹) * (x : G)⁻¹ * (y : G)
    exact hcent.symm
  have hαeq : α = MulEquiv.refl L :=
    perfect_central_automorphism_eq hLperf α (MulEquiv.refl L) hdelta
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxα := congrArg (fun ψ : L ≃* L => ψ ⟨x, hx⟩) hαeq
  have hxα' : f * x * f⁻¹ = x := by
    have hsub : α ⟨x, hx⟩ = ⟨x, hx⟩ := by simpa using hxα
    have hval : (α ⟨x, hx⟩ : G) = x := congrArg Subtype.val hsub
    simpa [α, conjOnSubgroupEquiv, conjOnSubgroup] using hval
  exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxα')).symm

/-- For a homomorphism with kernel contained in the center, the central
quotient is no larger than the image. -/
public theorem card_central_quotient_le_card_image_of_central_kernel
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hker : f.ker ≤ Subgroup.center G) :
    Nat.card (G ⧸ Subgroup.center G) ≤ Nat.card f.range := by
  classical
  have htopc : Nat.card (↥(⊤ : Subgroup G)) = Nat.card G := by
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have h1 : Nat.card G =
      Nat.card ((⊤ : Subgroup G).map f) *
        Nat.card (((⊤ : Subgroup G) ⊓ f.ker : Subgroup G)) := by
    rw [← htopc]
    exact card_map_eq_card_mul_card_ker f (⊤ : Subgroup G)
  have hrange : (⊤ : Subgroup G).map f = f.range := by
    ext y
    simp [Subgroup.mem_map, MonoidHom.mem_range]
  have h1' : Nat.card G = Nat.card f.range * Nat.card f.ker := by
    have hint : (⊤ : Subgroup G) ⊓ f.ker = f.ker := by
      ext x
      simp
    simpa [hrange, hint, htopc] using h1
  have h2 : Nat.card G = Nat.card (Subgroup.center G) *
      Nat.card (G ⧸ Subgroup.center G) := by
    calc
      Nat.card G = (Subgroup.center G).index * Nat.card (Subgroup.center G) :=
        (Subgroup.index_mul_card (Subgroup.center G)).symm
      _ = Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) := by
        rw [Subgroup.index_eq_card]
      _ = Nat.card (Subgroup.center G) * Nat.card (G ⧸ Subgroup.center G) := by
        rw [mul_comm]
  have hkz : Nat.card f.ker ≤ Nat.card (Subgroup.center G) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hker)
  have hmul : Nat.card f.range * Nat.card f.ker =
      Nat.card (Subgroup.center G) * Nat.card (G ⧸ Subgroup.center G) := by
    rw [← h1', h2]
  have hge : Nat.card (Subgroup.center G) * Nat.card (G ⧸ Subgroup.center G) ≥
      Nat.card f.ker * Nat.card (G ⧸ Subgroup.center G) :=
    Nat.mul_le_mul_right _ hkz
  have hmge : Nat.card f.ker * Nat.card (G ⧸ Subgroup.center G) ≤
      Nat.card f.ker * Nat.card f.range := by
    have h1h : Nat.card f.range * Nat.card f.ker ≥
        Nat.card f.ker * Nat.card (G ⧸ Subgroup.center G) := by
      rw [hmul]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hge
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1h
  exact Nat.le_of_mul_le_mul_left hmge Nat.card_pos

/-! ## The Fact 1.10(ii) Fitting package -/

/-- A normal nilpotent subgroup of odd order (ambient formulation): it lies
in the Fitting subgroup of the ambient group, and in the odd core of that
Fitting subgroup. -/
public theorem normal_nilpotent_odd_le_fitting_oddCore_ambient
    {G : Type u} [Group G] [Finite G]
    (A P : Subgroup G)
    (hPleA : P ≤ A)
    (hPconj : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ ∈ P)
    (hPnilp : Group.IsNilpotent P)
    (hPodd : Odd (Nat.card P)) :
    P ≤ fittingSubgroupOf A ∧ P ≤ oddCoreOf (fittingSubgroupOf A) := by
  classical
  let P0 : Subgroup A := P.subgroupOf A
  have hP0normal : P0.Normal := by
    refine ⟨?_⟩
    intro n hn g
    apply Subgroup.mem_subgroupOf.mpr
    exact hPconj (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.mp hn)
  have hP0nilp : Group.IsNilpotent P0 := by
    let : Group.IsNilpotent P := hPnilp
    exact Group.nilpotent_of_mulEquiv (G := P) (G' := P0)
      (Subgroup.subgroupOfEquivOfLe hPleA).symm
  have hP0leF : P0 ≤ fittingSubgroup A := le_sSup ⟨hP0normal, hP0nilp⟩
  have hPleF : P ≤ fittingSubgroupOf A := by
    intro p hp
    change p ∈ Subgroup.map A.subtype (fittingSubgroup A)
    rw [Subgroup.mem_map]
    refine ⟨⟨p, hPleA hp⟩, hP0leF (Subgroup.mem_subgroupOf.mpr hp), rfl⟩
  have hFleA : fittingSubgroupOf A ≤ A := Subgroup.map_subtype_le (fittingSubgroup A)
  have hPoddCop : Nat.Coprime 2 (Nat.card P) := Nat.coprime_two_left.mpr hPodd
  have hPleOC : P ≤ oddCoreOf (fittingSubgroupOf A) := by
    intro p hp
    change p ∈ Subgroup.map (fittingSubgroupOf A).subtype
      (pPrimeCore 2 (fittingSubgroupOf A))
    rw [Subgroup.mem_map]
    refine ⟨⟨p, hPleF hp⟩, ?_, rfl⟩
    have hP0''le : P.subgroupOf (fittingSubgroupOf A) ≤
        pPrimeCore 2 (fittingSubgroupOf A) := by
      apply le_sSup
      refine ⟨?_, ?_⟩
      · refine ⟨?_⟩
        intro n hn g
        apply Subgroup.mem_subgroupOf.mpr
        exact hPconj (g : G) (hFleA g.2) (n : G) (Subgroup.mem_subgroupOf.mp hn)
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleF).toEquiv]
        exact hPoddCop
    exact hP0''le (Subgroup.mem_subgroupOf.mpr hp)
  exact ⟨hPleF, hPleOC⟩

/-- The Fact 1.10(ii) input package for the normalizer `N = N_G(X)` of the
second case: with `C = C_N(t) = N ∩ C_G(t)` and `P = F(U) ∩ N`, the
subgroup `P` is normal in `C`, of odd order, nilpotent, contained in
`F(C)`, and contained in `O₂'(F(C))`.  Hence, by Fact 1.10(ii), the
elements of `P` induce inner automorphisms on `E(N)` (formalized as the
hypothesis `secondCase_psl2_normalizer_innerAction`). -/
public theorem secondCase_psl2_normalizer_fitting_package
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (X : Subgroup G) :
    let P : Subgroup G := c.FU ⊓ Subgroup.normalizer (X : Set G)
    let C : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ c.H
    P ≤ C ∧ IsNormalIn P C ∧ Odd (Nat.card P) ∧ Group.IsNilpotent P ∧
      P ≤ fittingSubgroupOf C ∧ P ≤ oddCoreOf (fittingSubgroupOf C) := by
  classical
  let P : Subgroup G := c.FU ⊓ Subgroup.normalizer (X : Set G)
  let C : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ c.H
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hFUleU : c.FU ≤ c.U := Subgroup.map_subtype_le (fittingSubgroup c.U)
  have hFUleH : c.FU ≤ c.H := hFUleU.trans hUleH
  have hPleC : P ≤ C := by
    intro p hp
    exact ⟨hp.2, hFUleH hp.1⟩
  have hPconj : ∀ a ∈ C, ∀ p ∈ P, a * p * a⁻¹ ∈ P := by
    intro a ha p hp
    exact ⟨(centralizerSetup_FU_isNormalIn_H c).2 a ha.2 p hp.1,
      (Subgroup.normalizer (X : Set G)).mul_mem
        ((Subgroup.normalizer (X : Set G)).mul_mem ha.1 hp.2)
        ((Subgroup.normalizer (X : Set G)).inv_mem ha.1)⟩
  have hPodd : Odd (Nat.card P) := by
    have hPleU : P ≤ c.U := by
      intro p hp
      exact hFUleU hp.1
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hPleU)
  have hPnilp : Group.IsNilpotent P := by
    let : Group.IsNilpotent c.FU := fittingSubgroupOf_isNilpotent c.U
    have hP0 : Group.IsNilpotent (P.subgroupOf c.FU) := by infer_instance
    exact Group.nilpotent_of_mulEquiv (G := P.subgroupOf c.FU) (G' := P)
      (Subgroup.subgroupOfEquivOfLe (show P ≤ c.FU from inf_le_left))
  have hPkg := normal_nilpotent_odd_le_fitting_oddCore_ambient C P hPleC hPconj hPnilp hPodd
  exact ⟨hPleC, ⟨⟨hPleC, hPconj⟩, ⟨hPodd, ⟨hPnilp, hPkg⟩⟩⟩⟩

end CFSG.GorensteinWalter
