module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970) Statement 1.7 — centralizer and F\*-commutation helpers

This module closes the two gaps named by the `gw-bender1970-17` owner:

1. `fstar_normalizer_center_qCoreOf_fitting_eq_A` — for `p ∈ π(F(A))`,
   `N_G(Z(O_p(F(A)))) = A`.  The proof is the characteristic-chain
   argument: `O_p(F(A))` is characteristic in `F(A)`, `F(A) ⊴ A`, the
   center of `O_p(F(A))` is characteristic in `O_p(F(A))`, so
   `Z(O_p(F(A))) ⊴ A`; the normalizer contains `A`, is not `G` by
   simplicity (the center is nontrivial), and is not larger than `A` by
   maximality.
2. `centralizer_qCoreOf_S_le_A` — for the 1.7 hypotheses and
   `p ∈ π(F(A))`, the centralizer of `O_p(S)` lies in `A`.  This is the
   exact statement imported by `Bender1970_17i` under the name
   `bender1970_1_7_centralizer_qCoreOf_S_le_A`.

The residual Thompson-lemma assembly (paper 1.7 proof steps 3–4) is **not**
landed here: the unconditional three-conjunct bridge
`bender1970_1_7_residual_commutator_assembly` declared in
`Bender1970_17i.lean` is mathematically false (explicit counterexample in
`A₅`: `A = S₃`, `S = C₃ = F*(A)`, `B = A₄` satisfies all 1.7 hypotheses
but `F*(B) = V₄ ⊄ A`), and the honest two-conjunct statement
`[O_p(B) ⊓ A, O^p(F*(A))] = ⊥ ∧ (p ∈ π(F(A)) → [O_p(B), O^p(F*(A))] = ⊥)`
requires the paper's "obvious" step `[O_p(B) ⊓ A, O^p(S)] = 1` (equivalently
`O_p(B) ⊓ A ≤ O_p(A)`) and the p-residual generation lemma
`O^p(F*(A)) = ⟨O^p(S), O_q(A) (q ≠ p)⟩`, neither of which exists in the
allowed module graph.  See the task card for the exact gap list.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Characteristic transport through a normal intermediate subgroup -/

/-- The image of a characteristic subgroup of a subgroup normal in `A` is
normal in `A`. -/
public theorem fstar_characteristic_subgroupOf_map_normal_in
    {G : Type u} [Group G] {A F : Subgroup G} {K : Subgroup (↥F)}
    (hK : K.Characteristic) (hF : IsNormalIn F A) :
    IsNormalIn (K.map F.subtype) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact hF.1 y.2
  · intro a ha z hz
    rcases (Subgroup.mem_map).1 hz with ⟨y, hy, rfl⟩
    let α : ↥F ≃* ↥F :=
      { toFun := fun y => ⟨a * (y : G) * a⁻¹, hF.2 a ha (y : G) y.2⟩
        invFun := fun y =>
          ⟨a⁻¹ * (y : G) * a, by
            have h := hF.2 a⁻¹ (A.inv_mem ha) (y : G) y.2
            simpa [mul_assoc] using h⟩
        left_inv := by intro y; ext; group
        right_inv := by intro y; ext; group
        map_mul' := by
          intro x y
          ext
          change a * ((x * y : ↥F) : G) * a⁻¹ =
            (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹)
          rw [Subgroup.coe_mul]
          group }
    have hmap : K.map α.toMonoidHom = K :=
      (Subgroup.characteristic_iff_map_eq.mp hK) α
    have hαy : α y ∈ K := by
      rw [← hmap]
      exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    refine (Subgroup.mem_map).mpr ⟨α y, hαy, ?_⟩
    change (α y).1 = a * (y : G) * a⁻¹
    rfl

/-! ## Normalizer of `Z(O_p(F(A)))` -/

/-- The normalizer of `Z(O_p(F(A)))` is the maximal subgroup `A` when
`p ∈ π(F(A))`. -/
public theorem fstar_normalizer_center_qCoreOf_fitting_eq_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.normalizer
      ((Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
        (qCoreOf (fittingSubgroupOf A) p).subtype : Set G) = A := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hFleA : F ≤ A := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hPleF : P ≤ F := qCoreOf_le F p
  have hPleA : P ≤ A := hPleF.trans hFleA
  have hZleP : Z ≤ P := Subgroup.map_subtype_le (H := P) (Subgroup.center (↥P))
  have hZleA : Z ≤ A := hZleP.trans hPleA
  have hPnormalA : IsNormalIn P A := by
    simpa [P, qCoreOf] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := fittingSubgroupOf A)
        (K := pCore p (↥(fittingSubgroupOf A)))
        (pCore_characteristic (p := p)) (fittingSubgroupOf_isNormalIn A))
  have hZnormalA : IsNormalIn Z A := by
    simpa [Z] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := P)
        (K := Subgroup.center (↥P)) (Subgroup.centerCharacteristic) hPnormalA)
  have hAleN : A ≤ Subgroup.normalizer (Z : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro a ha z hz
    exact hZnormalA.2 a ha z hz
  have hPne : P ≠ ⊥ := by
    simpa [P, F] using
      (fstar_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder A p hp hpF)
  have hPnt : Nontrivial (↥P) := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  have : Fact p.Prime := ⟨hp⟩
  have hCne : (Subgroup.center (↥P)) ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial (Subgroup.center (↥P)) :=
      IsPGroup.center_nontrivial (qCoreOf_isPGroup F p)
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center (↥P))).1 hnt hbot
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    have hcbot :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (↥P))
        (f := P.subtype) P.subtype_injective).1 hZbot
    exact hCne hcbot
  have hNne_top : Subgroup.normalizer (Z : Set G) ≠ ⊤ := by
    intro htop
    have hZnormalG : Z.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hZnormalG; hsimple.eq_bot_or_eq_top_of_normal Z) with hbot | htopZ
    · exact hZne hbot
    · have hAtop : A = ⊤ := by
        have htopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          exact hZleA (htopZ ▸ hx)
        exact le_antisymm le_top htopLeA
      exact hA.1 hAtop
  have hNleA : Subgroup.normalizer (Z : Set G) ≤ A := by
    by_cases hEq : A = Subgroup.normalizer (Z : Set G)
    · rw [hEq]
    · have hlt : A < Subgroup.normalizer (Z : Set G) :=
        lt_of_le_of_ne hAleN (by
          intro h
          exact hEq h)
      have htop := hA.2 (Subgroup.normalizer (Z : Set G)) hlt
      exact False.elim (hNne_top htop)
  exact le_antisymm hNleA hAleN

/-! ## Centralizer of `O_p(S)` for the 1.7 hypotheses -/

/-- For the 1.7 hypotheses with `p ∈ π(F(A))`, the centralizer of
`O_p(S)` lies in the maximal subgroup `A`. -/
public theorem centralizer_qCoreOf_S_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A S : Subgroup G) (hA : IsCoatom A)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A := by
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZleQ : Z ≤ qCoreOf S p := by
    simpa [Z, P] using (fstar_center_qCoreOf_fitting_le_qCoreOf_S A S
      hSF hSsub hCS p hp hpF)
  have hNZ : Subgroup.normalizer (Z : Set G) = A := by
    simpa [Z, P] using (fstar_normalizer_center_qCoreOf_fitting_eq_A
      hsimple A hA hp hpF)
  calc
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G)
        ≤ Subgroup.centralizer (Z : Set G) :=
      Subgroup.centralizer_le (show (Z : Set G) ⊆ (qCoreOf S p : Set G) from hZleQ)
    _ ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer (Z : Set G)
    _ = A := hNZ

/-- The exact centralizer statement imported by `Bender1970_17i`. -/
public theorem bender1970_1_7_centralizer_qCoreOf_S_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A := by
  exact centralizer_qCoreOf_S_le_A hsimple A S hA hSF hSsub hCS hp hpF

/-! ## `O^p(F*(A))` centralizes `O_p(A)` -/

/-- The p-residual of `F*(A)` centralizes `O_p(A)`.  This is one of the two
engine facts needed by the Thompson-lemma assembly of 1.7 (the other is the
p-residual generation lemma recorded in the task card). -/
public theorem fstar_pResidualOf_generalizedFitting_centralizer_qCore
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≤
      Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) := by
  classical
  let H : Subgroup G := generalizedFittingSubgroupOf A
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let P : Subgroup G := qCoreOf A p
  let Z : Subgroup G := Subgroup.centralizer (P : Set G)
  let K : Subgroup G := H ⊓ Z
  have hHF : F ≤ H := le_sup_left
  have hHE : E ≤ H := le_sup_right
  have hHA : H ≤ A := fstar_generalizedFittingSubgroupOf_le A
  have hFA : F ≤ A := hHF.trans hHA
  have hPleF : P ≤ F := fstar_qCoreOf_le_fittingSubgroupOf A p hp
  have hPleH : P ≤ H := hPleF.trans hHF
  have hPleA : P ≤ A := hPleF.trans hFA
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := E) (H₂ := F)).mp (layer_centralizes_fitting A)
  have hZF : Subgroup.centralizer (F : Set G) ≤ Z :=
    Subgroup.centralizer_le (show (P : Set G) ⊆ (F : Set G) from hPleF)
  have hEcentral : E ≤ Z := hEF.trans hZF
  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro h hh z hz
    exact (qCoreOf_normal_in A p).2 h (hHA hh) z hz
  have hKleH : K ≤ H := inf_le_left
  have hKnormal : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKleH]
    intro x h hx hh
    have hxH : x ∈ H := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxZ' : x ∈ Subgroup.centralizer (P : Set G) := hxZ
    have hmH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    have hmZ : h * x * h⁻¹ ∈ Z := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : h⁻¹ * z * h ∈ P :=
        by simpa using
          (Subgroup.le_set_normalizer_iff).1 hHnormP (h⁻¹) (H.inv_mem hh) z hz
      have hkx : x * (h⁻¹ * z * h) = (h⁻¹ * z * h) * x :=
        (Subgroup.mem_centralizer_iff.mp hxZ' (h⁻¹ * z * h) hz').symm
      have hmain : (h * x * h⁻¹) * z = z * (h * x * h⁻¹) := by
        calc
          (h * x * h⁻¹) * z = h * (x * (h⁻¹ * z * h)) * h⁻¹ := by group
          _ = h * ((h⁻¹ * z * h) * x) * h⁻¹ := by rw [hkx]
          _ = z * (h * x * h⁻¹) := by group
      exact hmain.symm
    exact ⟨hmH, hmZ⟩
  let π : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  have hKmap : (K.subgroupOf H).map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := K.subgroupOf H) (f := π)).2
    intro x hx
    simpa [π, QuotientGroup.ker_mk'] using hx
  have hPsub : IsPGroup p (P.subgroupOf H) :=
    (qCoreOf_isPGroup A p).of_equiv (Subgroup.subgroupOfEquivOfLe hPleH).symm
  have hPm : IsPGroup p ((P.subgroupOf H).map π) :=
    IsPGroup.map hPsub π
  have hFleKP : F ≤ K ⊔ P := by
    change fittingSubgroupOf A ≤ K ⊔ P
    rw [fstar_fittingSubgroupOf_eq_iSup_qCoreOf A]
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      exact le_sup_right
    · have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hQleZ : qCoreOf A q.1.1 ≤ Z :=
        fstar_qCoreOf_centralizer_of_ne A hp hqprime (by
          intro hpq
          exact hqp hpq.symm)
      have hQleH : qCoreOf A q.1.1 ≤ H :=
        (fstar_qCoreOf_le_fittingSubgroupOf A q.1.1 hqprime).trans hHF
      exact le_trans (le_inf hQleH hQleZ) le_sup_left
  have hFm_le : (F.subgroupOf H).map π ≤ (P.subgroupOf H).map π := by
    calc
      (F.subgroupOf H).map π ≤ ((K ⊔ P).subgroupOf H).map π :=
        Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono H hFleKP)
      _ = ((K.subgroupOf H ⊔ P.subgroupOf H).map π) := by
        rw [Subgroup.subgroupOf_sup hKleH hPleH]
      _ = (P.subgroupOf H).map π := by
        rw [Subgroup.map_sup, hKmap]
        simp
  have hFm : IsPGroup p ((F.subgroupOf H).map π) :=
    IsPGroup.to_le hPm hFm_le
  have hEm : IsPGroup p ((E.subgroupOf H).map π) := by
    have hEmap : (E.subgroupOf H).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := E.subgroupOf H) (f := π)).2
      intro e he
      have heH : e.1 ∈ H := hHE (Subgroup.mem_subgroupOf.mp he)
      have heZ : e.1 ∈ Z := hEcentral (Subgroup.mem_subgroupOf.mp he)
      have heK : (e : G) ∈ K := ⟨heH, heZ⟩
      simpa [π, QuotientGroup.ker_mk'] using (Subgroup.mem_subgroupOf).mpr heK
    rw [hEmap]
    exact IsPGroup.of_bot
  have htop_eq : (⊤ : Subgroup H) = F.subgroupOf H ⊔ E.subgroupOf H := by
    rw [← Subgroup.subgroupOf_self H]
    change (F ⊔ E).subgroupOf H = F.subgroupOf H ⊔ E.subgroupOf H
    exact Subgroup.subgroupOf_sup hHF hHE
  have hQ : IsPGroup p ((⊤ : Subgroup H).map π) := by
    rw [htop_eq, Subgroup.map_sup]
    have hEmap : (E.subgroupOf H).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := E.subgroupOf H) (f := π)).2
      intro e he
      have heH : e.1 ∈ H := hHE (Subgroup.mem_subgroupOf.mp he)
      have heZ : e.1 ∈ Z := hEcentral (Subgroup.mem_subgroupOf.mp he)
      have heK : (e : G) ∈ K := ⟨heH, heZ⟩
      simpa [π, QuotientGroup.ker_mk'] using (Subgroup.mem_subgroupOf).mpr heK
    have : ((E.subgroupOf H).map π).Normal := by
      rw [hEmap]
      infer_instance
    exact IsPGroup.to_sup_of_normal_right hFm hEm
  have hQquot : IsPGroup p (H ⧸ K.subgroupOf H) := by
    have htopmap : (⊤ : Subgroup H).map π = ⊤ :=
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (K.subgroupOf H))
    have hQtop : IsPGroup p (⊤ : Subgroup (H ⧸ K.subgroupOf H)) := by
      rw [← htopmap]
      exact hQ
    exact hQtop.of_equiv Subgroup.topEquiv
  have hRes : pResidualOf H p ≤ K :=
    fstar_pResidualOf_le_of_quotient_isPGroup H K p hp hKleH hKnormal hQquot
  exact hRes.trans inf_le_right

/-!
## Residual Thompson-lemma assembly — status

The paper's step `[O_p(B) ∩ A, O^p(F*(A))] = 1` (all primes) and the
`p ∈ π(F(A))` step `[O_p(B), O^p(F*(A))] = 1` are **not** declared here.
The earlier bridge `residual_commutator_assembly` was
removed rather than left as a `sorry`: its proof requires the two missing
facts listed in the module header, and the 17i three-conjunct bridge is
false as stated.  `Bender1970_17ii` currently imports this module for
`residual_commutator_assembly`; that import must be re-routed to a future
assembly lemma (see `tasks/gw-bender1970-17.md` Route Ledger).
-/

end CFSG.GorensteinWalter
