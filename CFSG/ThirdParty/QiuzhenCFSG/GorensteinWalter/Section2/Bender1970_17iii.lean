module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17i
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17ii
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970), Statement 1.7(iii)

The proof derives `F*(B) ≤ A` from the two-conjunct residual
commutator-assembly (Statement 1.7(i) applied to the pair `(B, Sbar)` with
the self-centralizing subnormal subgroup `Sbar`), derives `F*(A) ≤ B` by
symmetry, and then applies the landed Statement 1.6 theorem
(`bender1970_1_6_maximalSubgroups_pGroups` from `Bender1970_16`) together
with the two-prime hypothesis to force `A = B`.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Local q-core helpers for the (iii)-case -/

/-- A normal `p`-subgroup of `A` lies in `O_p(A)`. -/
public theorem le_qCoreOf_of_isNormalIn_pGroup
    {G : Type u} [Group G] [Finite G]
    (A Q : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hQA : Q ≤ A) (hQ : IsNormalIn Q A) (hQp : IsPGroup p Q) :
    Q ≤ qCoreOf A p := by
  let : Fact p.Prime := ⟨hp⟩
  have hQsub : Q.subgroupOf A ≤ pCore p (↥A) :=
    le_sSup ⟨by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := A) (N := Q)
        (by
          intro x hx
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            exact hQ.2 x hx y hy
          · intro hy
            have hxinv : x⁻¹ ∈ A := A.inv_mem hx
            have h := hQ.2 x⁻¹ hxinv (x * y * x⁻¹) hy
            simpa [mul_assoc] using h), by
      exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm⟩
  have hmap := Subgroup.map_mono (f := A.subtype) hQsub
  have hQmap : (Q.subgroupOf A).map A.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQA
  simpa [qCoreOf, hQmap] using hmap

/-- `O_p(F*(A)) ≤ O_p(A)`. -/
private theorem qCoreOf_generalizedFitting_le_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    qCoreOf (generalizedFittingSubgroupOf A) p ≤ qCoreOf A p := by
  let S : Subgroup G := generalizedFittingSubgroupOf A
  let Q : Subgroup G := qCoreOf S p
  have hQnormalA : IsNormalIn Q A := by
    simpa [Q, qCoreOf] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := S)
        (K := pCore p (↥S)) (pCore_characteristic (p := p))
        (fstar_generalizedFittingSubgroupOf_isNormalIn A))
  have hQp : IsPGroup p Q := qCoreOf_isPGroup S p
  exact le_qCoreOf_of_isNormalIn_pGroup A Q p hp hQnormalA.1 hQnormalA hQp

/-- For `p ∈ π(F(A))`, the centralizer of `O_p(A)` lies in the maximal
subgroup `A`. -/
private theorem centralizer_qCoreOf_A_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) ≤ A := by
  let S : Subgroup G := generalizedFittingSubgroupOf A
  have hSF : S ≤ S := le_rfl
  have hSsub : (S.subgroupOf S).IsSubnormal := by
    simpa [Subgroup.subgroupOf_self] using
      (Subgroup.IsSubnormal.top : (⊤ : Subgroup (↥S)).IsSubnormal)
  have hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S :=
    inf_le_left
  have hcentS : Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A :=
    centralizer_qCoreOf_S_le_A hsimple A S hA hSF hSsub hCS hp hpF
  exact (Subgroup.centralizer_le
    (show (qCoreOf S p : Set G) ⊆ (qCoreOf A p : Set G) from
      qCoreOf_generalizedFitting_le_qCoreOf A p hp)).trans hcentS

/-- `O_p(F(A))` is a normal `p`-subgroup of `A`, hence lies in `O_p(A)`. -/
private theorem qCoreOf_fitting_le_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    qCoreOf (fittingSubgroupOf A) p ≤ qCoreOf A p := by
  let F : Subgroup G := fittingSubgroupOf A
  let Q : Subgroup G := qCoreOf F p
  have hQleF : Q ≤ F := qCoreOf_le F p
  have hQleA : Q ≤ A := hQleF.trans (by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2)
  have hQnormalA : IsNormalIn Q A := by
    simpa [Q, qCoreOf] using
      (fstar_characteristic_subgroupOf_map_normal_in (F := F)
        (K := pCore p (↥F)) (pCore_characteristic (p := p))
        (fittingSubgroupOf_isNormalIn A))
  have hQp : IsPGroup p Q := qCoreOf_isPGroup F p
  exact le_qCoreOf_of_isNormalIn_pGroup A Q p hp hQleA hQnormalA hQp

/-- The center of `O_p(F(A))` lies in every subnormal self-centralizing
`S ≤ F*(A)`. -/
private theorem center_qCoreOf_fitting_le_selfCentralizingSubnormal
    {G : Type u} [Group G] [Finite G]
    (A S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    (Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
      (qCoreOf (fittingSubgroupOf A) p).subtype ≤ S := by
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let X : Subgroup G := generalizedFittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZF : Z ≤ Subgroup.centralizer (F : Set G) := by
    simpa [Z, P] using (fstar_center_qCoreOf_fitting_centralizes_fitting A p hp)
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := E) (H₂ := F)).1
      (layer_centralizes_fitting A)
  have hZE : Z ≤ Subgroup.centralizer (E : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hzF : z ∈ F := by
      rcases (Subgroup.mem_map).1 hz with ⟨c, _hc, rfl⟩
      exact (qCoreOf_le F p) (c : ↥P).2
    exact ((Subgroup.mem_centralizer_iff.mp (hEF he)) z hzF).symm
  have hZX : Z ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    change x ∈ F ⊔ E at hx
    rw [Subgroup.sup_eq_closure] at hx
    have hgen : ∀ y : G,
        y ∈ ((F : Set G) ∪ (E : Set G)) → y * z = z * y := by
      intro y hy
      rcases hy with hyF | hyE
      · exact (Subgroup.mem_centralizer_iff.mp (hZF hz)) y hyF
      · exact (Subgroup.mem_centralizer_iff.mp (hZE hz)) y hyE
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hx
    · intro y hy
      have hcomm : y * z = z * y := hgen y hy
      calc
        y⁻¹ * z = y⁻¹ * (z * y * y⁻¹) := by group
        _ = y⁻¹ * (y * z * y⁻¹) := by rw [hcomm]
        _ = z * y⁻¹ := by group
    · simp
    · intro y w _ _ hy' hw'
      calc
        (y * w) * z = y * (w * z) := by group
        _ = y * (z * w) := by rw [hw']
        _ = (y * z) * w := by group
        _ = (z * y) * w := by rw [hy']
        _ = z * (y * w) := by group
  have hZXle : Z ≤ X := by
    intro z hz
    exact (le_sup_left : F ≤ X) (by
      rcases (Subgroup.mem_map).1 hz with ⟨c, _hc, rfl⟩
      exact (qCoreOf_le F p) (c : ↥P).2)
  intro z hz
  have hzS : z ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.centralizer_le (show (S : Set G) ⊆ (X : Set G) from hSF)) (hZX hz)
  exact hCS ⟨hZXle hz, hzS⟩

/-- If `p` divides `|F(A)|`, the center of `O_p(F(A))` is nontrivial. -/
private theorem center_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    (Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
      (qCoreOf (fittingSubgroupOf A) p).subtype ≠ ⊥ := by
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
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
  intro hZbot
  have hcbot :=
    (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (↥P))
      (f := P.subtype) P.subtype_injective).1 hZbot
  exact hCne hcbot

/-- A nontrivial `O_p(A)` forces `p ∈ π(F(A))`. -/
public theorem mem_primesOfOrder_of_qCoreOf_ne_bot
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hQ : qCoreOf A p ≠ ⊥) :
    p ∈ primesOfOrder (fittingSubgroupOf A) := by
  let F : Subgroup G := fittingSubgroupOf A
  let Q : Subgroup G := qCoreOf A p
  have hQleF : Q ≤ F := fstar_qCoreOf_le_fittingSubgroupOf A p hp
  have hQnt : Nontrivial (↥Q) := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ
  have : Fact p.Prime := ⟨hp⟩
  rcases exists_ne (1 : ↥Q) with ⟨xQ, hxne⟩
  let x : G := (xQ : ↥Q)
  rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup A p)) xQ with ⟨k, hk⟩
  have hkpos : k ≠ 0 := by
    intro hk0
    have hord : orderOf xQ = 1 := by simpa [hk0] using hk
    exact hxne (orderOf_eq_one_iff.mp hord)
  have hpdvd : p ∣ orderOf xQ := by
    rw [hk]
    exact dvd_pow_self p hkpos
  have hordG : orderOf x = orderOf xQ :=
    (orderOf_injective Q.subtype Q.subtype_injective xQ)
  have hpdvdG : p ∣ orderOf x := by
    rw [hordG]
    exact hpdvd
  have hxG : x ∈ F := hQleF xQ.2
  have hordF : orderOf x ∣ Nat.card (↥F) := by
    have : Fintype (↥F) := Fintype.ofFinite _
    let xF : ↥F := ⟨x, hxG⟩
    have hord : orderOf xF = orderOf x :=
      (orderOf_injective F.subtype F.subtype_injective xF).symm
    simpa [hord] using orderOf_dvd_card (G := ↥F) (x := xF)
  have hpdvdF : p ∣ Nat.card (↥F) := hpdvdG.trans hordF
  have hpf : p ∈ (Nat.card (↥F)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvdF, Nat.card_pos.ne'⟩
  simpa [primesOfOrder] using hpf

/-- A `p`-core of `A` lies in the `s`-residual of `F*(A)` whenever
`p ≠ s`. -/
private theorem qCoreOf_le_pResidualOf_of_ne
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p s : ℕ) (hp : p.Prime) (hs : s.Prime) (hne : p ≠ s) :
    qCoreOf A p ≤ pResidualOf (generalizedFittingSubgroupOf A) s := by
  let H : Subgroup G := generalizedFittingSubgroupOf A
  intro x hx
  have hxH : x ∈ H :=
    (fstar_qCoreOf_le_fittingSubgroupOf A p hp).trans le_sup_left hx
  let xQ : ↥(qCoreOf A p) := ⟨x, hx⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact s.Prime := ⟨hs⟩
  rcases (IsPGroup.iff_orderOf.mp (qCoreOf_isPGroup A p)) xQ with ⟨k, hk⟩
  have hpndvd : ¬ p ∣ s := by
    intro hdiv
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hs).mp hdiv)
  have hcopPow : Nat.Coprime s (p ^ k) := hp.coprime_pow_of_not_dvd hpndvd
  have hord : orderOf x = orderOf xQ :=
    (orderOf_injective (qCoreOf A p).subtype (qCoreOf A p).subtype_injective xQ)
  have hcop : Nat.Coprime s (orderOf x) := by
    rw [hord, hk]
    exact hcopPow
  exact fstar_mem_pResidualOf_of_order_coprime H s hs hxH hcop

/-- Under the two 1.7 pairs, `π(F(B)) ⊆ π(F(A))`. -/
private theorem mem_primesOfOrder_fitting_of_mem_primesOfOrder_fitting_pair
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    {Sbar : Subgroup G}
    (hSbarA : Sbar ≤ A) (hSbarF : Sbar ≤ generalizedFittingSubgroupOf B)
    (hSbarSub : (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal)
    (hSbarCS : generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar)
    {p : ℕ} (hp : p.Prime)
    (hpB : p ∈ primesOfOrder (fittingSubgroupOf B)) :
    p ∈ primesOfOrder (fittingSubgroupOf A) := by
  by_contra hpA
  let F : Subgroup G := fittingSubgroupOf B
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZne : Z ≠ ⊥ :=
    center_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder B p hp hpB
  have hZleSbar : Z ≤ Sbar :=
    center_qCoreOf_fitting_le_selfCentralizingSubnormal B Sbar hSbarF hSbarSub hSbarCS
      p hp hpB
  have hZleQ : Z ≤ qCoreOf B p :=
    (Subgroup.map_subtype_le (H := P) (Subgroup.center (↥P))).trans
      (qCoreOf_fitting_le_qCoreOf B p hp)
  have hdisj : qCoreOf B p ⊓ A = ⊥ :=
    (bender1970_1_7_residual_commutator_assembly hsimple A hA S hSF hSsub hCS hSB).1
      p hp hpA
  have hZnt : Nontrivial (↥Z) := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
  rcases exists_ne (1 : ↥Z) with ⟨z, hz1⟩
  have hzSbar : (z : G) ∈ Sbar := hZleSbar z.2
  have hzA : (z : G) ∈ A := hSbarA hzSbar
  have hzQ : (z : G) ∈ qCoreOf B p := hZleQ z.2
  have hzinf : (z : G) ∈ qCoreOf B p ⊓ A := Subgroup.mem_inf.mpr ⟨hzQ, hzA⟩
  have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
    simpa [hdisj] using hzinf
  have hzG : (z : G) = 1 := by simpa using hzbot
  have hzsub : z = 1 := by ext; exact hzG
  exact hz1 hzsub

/-- Under the two 1.7 pairs, `π(F(A)) ⊆ π(F(B))`. -/
private theorem mem_primesOfOrder_fitting_of_mem_primesOfOrder_fitting_pair_symm
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    {Sbar : Subgroup G}
    (hSbarA : Sbar ≤ A) (hSbarF : Sbar ≤ generalizedFittingSubgroupOf B)
    (hSbarSub : (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal)
    (hSbarCS : generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar)
    {p : ℕ} (hp : p.Prime)
    (hpA : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    p ∈ primesOfOrder (fittingSubgroupOf B) := by
  by_contra hpB
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZne : Z ≠ ⊥ :=
    center_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder A p hp hpA
  have hZleS : Z ≤ S :=
    center_qCoreOf_fitting_le_selfCentralizingSubnormal A S hSF hSsub hCS p hp hpA
  have hZleQ : Z ≤ qCoreOf A p :=
    (Subgroup.map_subtype_le (H := P) (Subgroup.center (↥P))).trans
      (qCoreOf_fitting_le_qCoreOf A p hp)
  have hdisj : qCoreOf A p ⊓ B = ⊥ :=
    (bender1970_1_7_residual_commutator_assembly hsimple B hB Sbar hSbarF hSbarSub hSbarCS hSbarA).1
      p hp hpB
  have hZnt : Nontrivial (↥Z) := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
  rcases exists_ne (1 : ↥Z) with ⟨z, hz1⟩
  have hzS : (z : G) ∈ S := hZleS z.2
  have hzB : (z : G) ∈ B := hSB hzS
  have hzQ : (z : G) ∈ qCoreOf A p := hZleQ z.2
  have hzinf : (z : G) ∈ qCoreOf A p ⊓ B := Subgroup.mem_inf.mpr ⟨hzQ, hzB⟩
  have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
    simpa [hdisj] using hzinf
  have hzG : (z : G) = 1 := by simpa using hzbot
  have hzsub : z = 1 := by ext; exact hzG
  exact hz1 hzsub

/-- The centralizer of a nontrivial layer lies in the maximal subgroup
containing it. -/
private theorem centralizer_componentLayer_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (hEne : componentLayerOf A ≠ ⊥) :
    Subgroup.centralizer ((componentLayerOf A : Set G)) ≤ A := by
  let E : Subgroup G := componentLayerOf A
  have hEsubA : E ≤ A := by
    change sSup {K : Subgroup G | IsComponentOf K A} ≤ A
    exact sSup_le (fun K hK => hK.1)
  have hEnormA : IsNormalIn E A := fstar_componentLayerOf_isNormalIn A
  have hAleN : A ≤ Subgroup.normalizer (E : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro a ha z hz
    exact hEnormA.2 a ha z hz
  have hNne_top : Subgroup.normalizer (E : Set G) ≠ ⊤ := by
    intro htop
    have hEnormG : E.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hEnormG; hsimple.eq_bot_or_eq_top_of_normal E) with hbot | htopE
    · exact hEne hbot
    · have hAtop : A = ⊤ := by
        have hle : (⊤ : Subgroup G) ≤ A := by
          intro x _hx
          exact hEsubA (htopE ▸ trivial)
        exact le_antisymm le_top hle
      exact hA.1 hAtop
  have hNleA : Subgroup.normalizer (E : Set G) ≤ A := by
    by_cases hEq : A = Subgroup.normalizer (E : Set G)
    · rw [hEq]
    · have hlt : A < Subgroup.normalizer (E : Set G) :=
        lt_of_le_of_ne hAleN (by
          intro h
          exact hEq h)
      have htop := hA.2 (Subgroup.normalizer (E : Set G)) hlt
      exact False.elim (hNne_top htop)
  exact (Subgroup.centralizer_le_normalizer (E : Set G)).trans hNleA

/-- A perfect subgroup of `H` lies in every p-residual of `H`. -/
private theorem perfect_subgroup_le_pResidualOf
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hKH : K ≤ H) (hKperf : Group.IsPerfect K) :
    K ≤ pResidualOf H p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let R : Subgroup G := pResidualOf H p
  let Q : Type u := H ⧸ R.subgroupOf H
  let K' : Subgroup (↥H) := K.subgroupOf H
  have hK'perf : Group.IsPerfect (↥K') := by
    let e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKH
    exact Group.IsPerfect.ofSurjective (G := K) (G' := ↥K') (f := e.symm.toMonoidHom)
      e.symm.toEquiv.surjective
  let f : ↥K' →* Q := (QuotientGroup.mk' (R.subgroupOf H)).comp K'.subtype
  let I : Subgroup Q := (⊤ : Subgroup (↥K')).map f
  have hQp : IsPGroup p Q := fstar_isPGroup_quotient_pResidualOf H p hp
  have hIbot : I = ⊥ := by
    by_contra hIne
    have : Nontrivial (↥I) := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    have : Group.IsPerfect (↥I) := by
      change Group.IsPerfect (↥((⊤ : Subgroup (↥K')).map f))
      exact Group.IsPerfect.map (G := ↥K') (H := (⊤ : Subgroup (↥K'))) (f := f)
    have hIp : IsPGroup p (↥I) := by
      simpa using (hQp.to_subgroup I)
    have hInil : Group.IsNilpotent (↥I) := IsPGroup.isNilpotent hIp
    exact (Group.IsPerfect.not_isNilpotent (G := ↥I)) hInil
  intro x hx
  have hxH : x ∈ H := hKH hx
  let xH : ↥H := ⟨x, hxH⟩
  have hxK' : xH ∈ K' := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hxI : f ⟨xH, hxK'⟩ ∈ I := by
    exact Subgroup.mem_map.mpr ⟨⟨xH, hxK'⟩, trivial, rfl⟩
  have hxR : xH ∈ R.subgroupOf H := by
    have hb : f ⟨xH, hxK'⟩ ∈ (⊥ : Subgroup Q) := by
      simpa [hIbot] using hxI
    exact (QuotientGroup.eq_one_iff (N := R.subgroupOf H) (x := xH)).1 hb
  exact (Subgroup.mem_subgroupOf).1 hxR

/-- The layer `E(A)` lies in every p-residual of `F*(A)`. -/
private theorem componentLayerOf_le_pResidualOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    componentLayerOf A ≤ pResidualOf (generalizedFittingSubgroupOf A) p := by
  change sSup {K : Subgroup G | IsComponentOf K A} ≤
    pResidualOf (generalizedFittingSubgroupOf A) p
  refine sSup_le ?_
  intro K hK
  have hKperf : Group.IsPerfect K := (Group.isPerfect_def).2 hK.2.2.2.1
  have hKleFstar : K ≤ generalizedFittingSubgroupOf A := by
    exact (le_sSup (s := {E : Subgroup G | IsComponentOf E A}) (a := K) hK).trans
      le_sup_right
  exact perfect_subgroup_le_pResidualOf (generalizedFittingSubgroupOf A) K p hp
    hKleFstar hKperf

/-- If `H` is a `p`-group, its prime-divisor set has cardinality at most one. -/
private theorem card_primesOfOrder_le_one_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hH : IsPGroup p H) :
    Nat.card (primesOfOrder H) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hunique : ∀ r : ℕ, r ∈ primesOfOrder H → r = p := by
    intro r hr
    have hrpf : r ∈ (Nat.card (↥H)).primeFactors := by simpa [primesOfOrder] using hr
    have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrpf
    have hrdvd : r ∣ Nat.card (↥H) := Nat.dvd_of_mem_primeFactors hrpf
    rcases (IsPGroup.iff_card.mp hH) with ⟨n, hcard⟩
    have hrdvd' : r ∣ p ^ n := hcard ▸ hrdvd
    exact (Nat.prime_dvd_prime_iff_eq hrprime hp).mp (hrprime.dvd_of_dvd_pow hrdvd')
  have hset : primesOfOrder H = ↑((Nat.card (↥H)).primeFactors) := by
    ext r
    simp [primesOfOrder]
  change (primesOfOrder H).ncard ≤ 1
  exact (Set.ncard_le_one (s := primesOfOrder H) (hs := by
    rw [hset]
    exact Finset.finite_toSet _)).mpr (by
    intro a ha b hb
    exact (hunique a ha).trans (hunique b hb).symm)

/-! ## `F*(A)` is self-centralizing inside `A` (transported from the
ambient theorem in `Bender1970_18`) -/

/-- The image of the center under a group isomorphism is the center. -/
private lemma map_center_eq_center_of_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- Quasisimplicity is invariant under a group isomorphism. -/
private theorem isQuasisimple_mulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
      map_center_eq_center_of_mulEquiv e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- A component of the ambient group is subnormal in the ambient group. -/
private theorem isSubnormal_of_isComponentOf_top
    {G : Type u} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G)) :
    K.IsSubnormal := by
  have h' : ((K.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
    hK.2.1.map (f := (⊤ : Subgroup G).subtype)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K ≤ (⊤ : Subgroup G))] at h'

/-- A component of the ambient group contained in `H` is a component of
`H`. -/
private theorem isComponentOf_of_isComponentOf_top_map
    {G : Type u} [Group G] {B : Subgroup G} {E : Subgroup (↥B)}
    (hE : IsComponentOf E (⊤ : Subgroup (↥B))) :
    IsComponentOf (E.map B.subtype) B := by
  refine ⟨Subgroup.map_subtype_le E, ?_, ?_⟩
  · have hEsub : E.IsSubnormal := isSubnormal_of_isComponentOf_top hE
    have hEq : (E.map B.subtype).subgroupOf B = E := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxy⟩
        have hyx : x = y := B.subtype_injective (by simpa using hxy)
        simpa [hyx] using hx
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    simpa [hEq] using hEsub
  · exact isQuasisimple_mulEquiv
      (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective) hE.2.2

/-- A component of `A` descends to a component of the ambient group of
`A`. -/
private theorem isComponentOf_of_isComponentOf_subgroup
    {G : Type u} [Group G] {A E : Subgroup G} (hE : IsComponentOf E A) :
    IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
  ⟨le_top, hE.2.1.subgroupOf,
    isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2⟩

/-- The component layer is preserved by the subgroup embedding:
`E(⊤_{B})` maps onto `E(B)`. -/
private theorem componentLayer_top_map_eq_componentLayerOf
    {G : Type u} [Group G] (B : Subgroup G) :
    (componentLayerOf (⊤ : Subgroup (↥B))).map B.subtype = componentLayerOf B := by
  apply le_antisymm
  · refine (Subgroup.map_le_iff_le_comap).2 ?_
    change sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))} ≤
      Subgroup.comap B.subtype (componentLayerOf B)
    refine sSup_le ?_
    intro E hE
    intro y hy
    rw [Subgroup.mem_comap]
    exact le_sSup (s := {E' : Subgroup G | IsComponentOf E' B})
      (a := E.map B.subtype)
      (isComponentOf_of_isComponentOf_top_map hE)
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  · change sSup {E : Subgroup G | IsComponentOf E B} ≤
      Subgroup.map B.subtype
        (sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))})
    refine sSup_le ?_
    intro E hE
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hE.1 hy⟩,
        Subgroup.mem_sSup_of_mem
          (isComponentOf_of_isComponentOf_subgroup hE)
          (by
            rw [Subgroup.mem_subgroupOf]
            exact hy),
        rfl⟩

/-- The image of the Fitting subgroup under a surjective homomorphism lies
in the Fitting subgroup of the target. -/
private theorem map_fittingSubgroup_le_of_surjective
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (fittingSubgroup G).map f ≤ fittingSubgroup H := by
  have hmap_normal : ((fittingSubgroup G).map f).Normal :=
    Subgroup.Normal.map (H := fittingSubgroup G) inferInstance f hf
  have hmap_nil : Group.IsNilpotent ↥((fittingSubgroup G).map f) := by
    have : Group.IsNilpotent ↥(fittingSubgroup G) := by infer_instance
    let ψ : fittingSubgroup G →* ↥((fittingSubgroup G).map f) :=
      { toFun := fun g => ⟨f g, Subgroup.mem_map.mpr ⟨g.1, g.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
    have hψsurj : Function.Surjective ψ := by
      intro x
      rcases (Subgroup.mem_map).1 x.2 with ⟨g, hg, hx⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      exact hx
    exact Group.nilpotent_of_surjective ψ hψsurj
  exact le_sSup ⟨hmap_normal, hmap_nil⟩

/-- The Fitting subgroup commutes with a group isomorphism. -/
private theorem map_fittingSubgroup_of_mulEquiv
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm
  · exact map_fittingSubgroup_le_of_surjective e.toMonoidHom e.surjective
  · have hback : (fittingSubgroup H).map e.symm.toMonoidHom ≤ fittingSubgroup G :=
      map_fittingSubgroup_le_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hmap : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (fittingSubgroup G).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hback
    have hleft : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom =
        fittingSubgroup H := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [hleft] at hmap
    exact hmap

/-- `F*(⊤_{B})` maps onto `F*(B)`. -/
private theorem map_generalizedFittingSubgroupOf_top_subtype
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))).map B.subtype =
      generalizedFittingSubgroupOf B := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup]
  rw [componentLayer_top_map_eq_componentLayerOf B]
  have : Finite (↥(⊤ : Subgroup (↥B))) :=
    Finite.of_equiv (↥B) (Subgroup.topEquiv (G := ↥B)).toEquiv.symm
  change Subgroup.map B.subtype ((fittingSubgroup (↥(⊤ : Subgroup (↥B)))).map
      (⊤ : Subgroup (↥B)).subtype) ⊔ componentLayerOf B =
    Subgroup.map B.subtype (fittingSubgroup (↥B)) ⊔ componentLayerOf B
  have hTopSubtype :
      (⊤ : Subgroup (↥B)).subtype =
        (Subgroup.topEquiv (G := ↥B)).toMonoidHom := by
    ext x
    rfl
  rw [hTopSubtype]
  rw [map_fittingSubgroup_of_mulEquiv (Subgroup.topEquiv (G := ↥B))]

/-! ## The (iii)-case: `F*(B) ≤ A` from the two pairs plus the two-prime
hypothesis -/

/-- If a component layer is a `p`-group, it is trivial. -/
private theorem componentLayerOf_eq_bot_of_isPGroup_layer
    {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hE : IsPGroup p (componentLayerOf B)) :
    componentLayerOf B = ⊥ := by
  apply le_bot_iff.mp
  rw [componentLayerOf]
  refine sSup_le ?_
  intro E hEcomp
  have hEq : IsPGroup p E :=
    IsPGroup.to_le hE
      (le_sSup (s := {E' : Subgroup G | IsComponentOf E' B}) (a := E) hEcomp)
  have : Fact p.Prime := ⟨hp⟩
  have hEnil : Group.IsNilpotent E := hEq.isNilpotent
  exact False.elim (not_isNilpotent_of_isQuasisimple E hEcomp.2.2 hEnil)

/-- If every prime divisor of `|H|` is `p`, then `H` is a `p`-group. -/
private theorem isPGroup_of_primeDivisors_eq
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hpf : ∀ r : ℕ, r ∈ (Nat.card (↥H)).primeFactors → r = p) :
    IsPGroup p H :=
  isPGroup_of_primeFactors_subset_singleton H hp hpf

/-- If `O^p(H) = 1`, then `H` is a `p`-group. -/
public theorem isPGroup_of_pResidualOf_eq_bot
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hRes : pResidualOf H p = ⊥) :
    IsPGroup p H := by
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (H ⧸ (pResidualOf H p).subgroupOf H) :=
    fstar_isPGroup_quotient_pResidualOf H p hp
  have hResbot : (pResidualOf H p).subgroupOf H = ⊥ := by
    ext x
    simp [hRes]
  have hcard' : Nat.card (H ⧸ (pResidualOf H p).subgroupOf H) = Nat.card H :=
    Nat.card_congr ((Subgroup.quotientEquivOfEq hResbot).trans
      QuotientGroup.quotientBot.toEquiv)
  rcases (IsPGroup.iff_card.mp hQ) with ⟨n, hn⟩
  refine IsPGroup.of_card (n := n) ?_
  rw [← hcard']
  exact hn

/-- Every prime dividing `|H|` is `p` when `H` is a `p`-group. -/
private theorem mem_primesOfOrder_eq_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hH : IsPGroup p H) :
    ∀ r : ℕ, r ∈ primesOfOrder H → r = p := by
  let : Fact p.Prime := ⟨hp⟩
  intro r hr
  have hrpf : r ∈ (Nat.card (↥H)).primeFactors := by simpa [primesOfOrder] using hr
  have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrpf
  have hrdvd : r ∣ Nat.card (↥H) := Nat.dvd_of_mem_primeFactors hrpf
  rcases (IsPGroup.iff_card.mp hH) with ⟨n, hcard⟩
  have hrdvd' : r ∣ p ^ n := hcard ▸ hrdvd
  exact (Nat.prime_dvd_prime_iff_eq hrprime hp).mp (hrprime.dvd_of_dvd_pow hrdvd')

/-- `O^p(F*(A))` is normal in `A`. -/
public theorem pResidualOf_generalizedFitting_isNormalIn
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) :
    IsNormalIn (pResidualOf (generalizedFittingSubgroupOf A) p) A := by
  let R : Subgroup G := pResidualOf (generalizedFittingSubgroupOf A) p
  have hKmap : (R.subgroupOf (generalizedFittingSubgroupOf A)).map
      (generalizedFittingSubgroupOf A).subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le (pResidualOf_le (generalizedFittingSubgroupOf A) p)
  have h := fstar_characteristic_subgroupOf_map_normal_in
    (F := generalizedFittingSubgroupOf A)
    (K := R.subgroupOf (generalizedFittingSubgroupOf A))
    (fstar_pResidualOf_subgroupOf_characteristic (generalizedFittingSubgroupOf A) p)
    (fstar_generalizedFittingSubgroupOf_isNormalIn A)
  simpa [R, hKmap] using h

/-- If `O^p(F*(A)) ≠ 1`, its normalizer in `G` is exactly the maximal
subgroup `A`. -/
private theorem normalizer_pResidualOf_generalizedFitting_eq
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (p : ℕ) (hp : p.Prime)
    (hne : pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥) :
    Subgroup.normalizer ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) = A := by
  let R : Subgroup G := pResidualOf (generalizedFittingSubgroupOf A) p
  let N : Subgroup G := Subgroup.normalizer (R : Set G)
  have hRnormA : IsNormalIn R A := by
    simpa [R] using (pResidualOf_generalizedFitting_isNormalIn A p)
  have hAleN : A ≤ N := le_normalizer_of_isNormalIn hRnormA
  have hNne_top : N ≠ ⊤ := by
    intro htop
    have hRnormG : R.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hRnormG; hsimple.eq_bot_or_eq_top_of_normal R) with hbot | htopR
    · exact hne hbot
    · have hAtop : A = ⊤ := by
        have hTopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          have hxR : x ∈ R := by
            rw [htopR]
            exact hx
          exact (pResidualOf_le (generalizedFittingSubgroupOf A) p).trans
            (fstar_generalizedFittingSubgroupOf_le A) hxR
        exact le_antisymm le_top hTopLeA
      exact hA.1 hAtop
  refine le_antisymm ?_ hAleN
  intro x hx
  by_cases hEq : A = N
  · rw [hEq]
    exact hx
  · have hlt : A < N := lt_of_le_of_ne hAleN (by intro h; exact hEq h)
    have htop := hA.2 N hlt
    exact False.elim (hNne_top htop)

/-- From `(ii)` and `O^p(F*(A)) ≠ 1`, the `p`-core of `B` lies in `A`. -/
private theorem qCoreOf_B_le_A_of_pResidual_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    {p : ℕ} (hp : p.Prime)
    (hpA : p ∈ primesOfOrder (fittingSubgroupOf A))
    (hRes : pResidualOf (generalizedFittingSubgroupOf A) p ≠ ⊥) :
    qCoreOf B p ≤ A := by
  have hcomm : ⁅qCoreOf B p, pResidualOf (generalizedFittingSubgroupOf A) p⁆ = ⊥ :=
    bender1970_1_7_ii_commutator_pResidual hsimple A hA S hSF hSsub hCS hSB p hp hpA
  have hCle : qCoreOf B p ≤
      Subgroup.centralizer ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := qCoreOf B p) (H₂ := pResidualOf (generalizedFittingSubgroupOf A) p)).1 hcomm
  have hN : Subgroup.normalizer
      ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) = A :=
    normalizer_pResidualOf_generalizedFitting_eq hsimple A hA p hp hRes
  calc
    qCoreOf B p ≤ Subgroup.centralizer
        ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) := hCle
    _ ≤ Subgroup.normalizer
        ((pResidualOf (generalizedFittingSubgroupOf A) p : Set G)) :=
      Subgroup.centralizer_le_normalizer _
    _ ≤ A := le_of_eq hN

/-- The hard case `O^p(F*(A)) = 1` contradicts the two-prime hypothesis:
then `F*(A)` is a `p`-group, so `|π(F*(B))| ≥ 2` forces the layer `E(B)`
to be nontrivial; but `(ii')` makes `E(B)` centralize `F*(A)`, and the
self-centralizing property of `F*(A)` in `A` (via `Sbar ≤ A`) makes
`E(B)` a `p`-group, hence trivial. -/
private theorem pResidualOf_generalizedFitting_eq_bot_contradiction
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    {Sbar : Subgroup G}
    (hSbarA : Sbar ≤ A) (hSbarF : Sbar ≤ generalizedFittingSubgroupOf B)
    (hSbarSub : (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal)
    (hSbarCS : generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)))
    {p : ℕ} (hp : p.Prime)
    (hpB : p ∈ primesOfOrder (fittingSubgroupOf B))
    (hRes : pResidualOf (generalizedFittingSubgroupOf A) p = ⊥) :
    False := by
  let PA : Subgroup G := generalizedFittingSubgroupOf A
  have hPA : IsPGroup p PA := by
    simpa [PA] using (isPGroup_of_pResidualOf_eq_bot
      (generalizedFittingSubgroupOf A) p hp hRes)
  have hpiA_le : Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ≤ 1 :=
    card_primesOfOrder_le_one_of_isPGroup (generalizedFittingSubgroupOf A) hp hPA
  have hpiB_ge : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)) := by
    rcases hpi with hA2 | hB2
    · omega
    · exact hB2
  have hEne : componentLayerOf B ≠ ⊥ := by
    intro hEbot
    have hFstarB : generalizedFittingSubgroupOf B = fittingSubgroupOf B := by
      rw [generalizedFittingSubgroupOf, hEbot]
      simp
    have hfun : ∀ r : ℕ,
        r ∈ primesOfOrder (generalizedFittingSubgroupOf B) → r = p := by
      intro r hr
      have hrF : r ∈ primesOfOrder (fittingSubgroupOf B) := by
        simpa [hFstarB] using hr
      have hrprime : r.Prime := by
        have hrpf : r ∈ (Nat.card (↥(fittingSubgroupOf B))).primeFactors := by
          simpa [primesOfOrder] using hrF
        exact Nat.prime_of_mem_primeFactors hrpf
      have hrA : r ∈ primesOfOrder (fittingSubgroupOf A) :=
        mem_primesOfOrder_fitting_of_mem_primesOfOrder_fitting_pair
          hsimple A hA S hSF hSsub hCS hSB hB
          hSbarA hSbarF hSbarSub hSbarCS (p := r) hrprime hrF
      have hrFstarA : r ∈ primesOfOrder (generalizedFittingSubgroupOf A) :=
        primesOfOrder_subset_of_le
          (le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A) hrA
      exact mem_primesOfOrder_eq_of_isPGroup (generalizedFittingSubgroupOf A) (p := p) hp hPA
        r hrFstarA
    have hFBp : IsPGroup p (generalizedFittingSubgroupOf B) := by
      refine isPGroup_of_primeDivisors_eq (generalizedFittingSubgroupOf B) hp ?_
      intro r hrpf
      exact hfun r (by simpa [primesOfOrder] using hrpf)
    have hpiB_le : Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)) ≤ 1 :=
      card_primesOfOrder_le_one_of_isPGroup (generalizedFittingSubgroupOf B) hp hFBp
    omega
  have hpA : p ∈ primesOfOrder (fittingSubgroupOf A) :=
    mem_primesOfOrder_fitting_of_mem_primesOfOrder_fitting_pair
      hsimple A hA S hSF hSsub hCS hSB hB
      hSbarA hSbarF hSbarSub hSbarCS (p := p) hp hpB
  have hcomm : ⁅qCoreOf A p, pResidualOf (generalizedFittingSubgroupOf B) p⁆ = ⊥ :=
    bender1970_1_7_ii_commutator_pResidual hsimple B hB Sbar hSbarF hSbarSub hSbarCS
      hSbarA p hp hpB
  have hP : generalizedFittingSubgroupOf A = qCoreOf A p := by
    rw [generalizedFittingSubgroupOf]
    rw [componentLayerOf_eq_bot_of_isPGroup A (q := p) hp hPA]
    rw [← qCoreOf_eq_fittingSubgroupOf_of_isPGroup A (q := p) hp hPA]
    simp
  have hEres : componentLayerOf B ≤ pResidualOf (generalizedFittingSubgroupOf B) p :=
    componentLayerOf_le_pResidualOf B p hp
  have hPcomm : ⁅generalizedFittingSubgroupOf A,
      pResidualOf (generalizedFittingSubgroupOf B) p⁆ = ⊥ := by
    simpa [hP] using hcomm
  have hPE : ⁅generalizedFittingSubgroupOf A, componentLayerOf B⁆ = ⊥ := by
    apply bot_unique
    rw [← hPcomm]
    exact Subgroup.commutator_mono le_rfl hEres
  have hPE' : ⁅componentLayerOf B, generalizedFittingSubgroupOf A⁆ = ⊥ :=
    (Subgroup.commutator_comm (H₁ := generalizedFittingSubgroupOf A)
      (H₂ := componentLayerOf B)).symm.trans hPE
  have hEleC : componentLayerOf B ≤
      Subgroup.centralizer ((generalizedFittingSubgroupOf A : Set G)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := componentLayerOf B) (H₂ := generalizedFittingSubgroupOf A)).1 hPE'
  have hEleA : componentLayerOf B ≤ A :=
    (fstar_componentLayer_le_selfCentralizingSubnormal B Sbar hSbarF hSbarSub hSbarCS).trans
      hSbarA
  have hEleP : componentLayerOf B ≤ generalizedFittingSubgroupOf A := by
    intro x hx
    exact centralizer_intersection_fstar_le_fstar A ⟨hEleC hx, hEleA hx⟩
  have hEp : IsPGroup p (componentLayerOf B) := IsPGroup.to_le hPA hEleP
  have hEbot : componentLayerOf B = ⊥ :=
    componentLayerOf_eq_bot_of_isPGroup_layer B (p := p) hp hEp
  exact hEne hEbot

/-- For `p ∈ π(F(B))`, the `p`-core of `B` lies in `A`. -/
private theorem qCoreOf_B_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    {Sbar : Subgroup G}
    (hSbarA : Sbar ≤ A) (hSbarF : Sbar ≤ generalizedFittingSubgroupOf B)
    (hSbarSub : (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal)
    (hSbarCS : generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)))
    {p : ℕ} (hp : p.Prime)
    (hpB : p ∈ primesOfOrder (fittingSubgroupOf B)) :
    qCoreOf B p ≤ A := by
  by_cases hRes : pResidualOf (generalizedFittingSubgroupOf A) p = ⊥
  · exact False.elim (pResidualOf_generalizedFitting_eq_bot_contradiction
      hsimple A hA S hSF hSsub hCS hSB hB
      hSbarA hSbarF hSbarSub hSbarCS hpi hp hpB hRes)
  · have hpA : p ∈ primesOfOrder (fittingSubgroupOf A) :=
      mem_primesOfOrder_fitting_of_mem_primesOfOrder_fitting_pair
        hsimple A hA S hSF hSsub hCS hSB hB
        hSbarA hSbarF hSbarSub hSbarCS (p := p) hp hpB
    exact qCoreOf_B_le_A_of_pResidual_ne_bot hsimple A hA S hSF hSsub hCS hSB
      hp hpA hRes

/-- `F(B) ≤ A` under the two control pairs and the two-prime hypothesis. -/
private theorem fittingSubgroupOf_B_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    {Sbar : Subgroup G}
    (hSbarA : Sbar ≤ A) (hSbarF : Sbar ≤ generalizedFittingSubgroupOf B)
    (hSbarSub : (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal)
    (hSbarCS : generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B))) :
    fittingSubgroupOf B ≤ A := by
  rw [fstar_fittingSubgroupOf_eq_iSup_qCoreOf B]
  refine iSup_le ?_
  intro q
  by_cases hq : qCoreOf B q.1.1 = ⊥
  · exact hq ▸ bot_le
  · have hqin : q.1.1 ∈ primesOfOrder (fittingSubgroupOf B) :=
      mem_primesOfOrder_of_qCoreOf_ne_bot B q.1.1 (Nat.prime_of_mem_primeFactors q.1.2) hq
    exact qCoreOf_B_le_A hsimple A hA S hSF hSsub hCS hSB hB
      hSbarA hSbarF hSbarSub hSbarCS hpi (p := q.1.1)
      (Nat.prime_of_mem_primeFactors q.1.2) hqin

/-- `F*(B) ≤ A` under the two control pairs and the two-prime hypothesis. -/
private theorem generalizedFittingSubgroupOf_B_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    {Sbar : Subgroup G}
    (hSbarA : Sbar ≤ A) (hSbarF : Sbar ≤ generalizedFittingSubgroupOf B)
    (hSbarSub : (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal)
    (hSbarCS : generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B))) :
    generalizedFittingSubgroupOf B ≤ A := by
  rw [generalizedFittingSubgroupOf]
  exact sup_le
    (fittingSubgroupOf_B_le_A hsimple A hA S hSF hSsub hCS hSB hB
      hSbarA hSbarF hSbarSub hSbarCS hpi)
    ((fstar_componentLayer_le_selfCentralizingSubnormal B Sbar hSbarF hSbarSub hSbarCS).trans
      hSbarA)

/-- Bender [1], Statement 1.7(iii): equality of maximal subgroups under the
two control-core hypotheses and a two-prime condition. -/
public theorem bender1970_1_7_iii_equalityOfMaximal
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B)
    (hB : IsCoatom B)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B))) :
    (∃ Sbar : Subgroup G,
      Sbar ≤ A ∧ Sbar ≤ generalizedFittingSubgroupOf B ∧
        (Sbar.subgroupOf (generalizedFittingSubgroupOf B)).IsSubnormal ∧
          generalizedFittingSubgroupOf B ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar) →
      A = B := by
  intro hSbar
  rcases hSbar with ⟨Sbar, hSbarA, hSbarF, hSbarSub, hSbarCS⟩
  have hFBA : generalizedFittingSubgroupOf B ≤ A :=
    generalizedFittingSubgroupOf_B_le_A hsimple A hA S hSF hSsub hCS hSB hB
      hSbarA hSbarF hSbarSub hSbarCS hpi
  have hFAB : generalizedFittingSubgroupOf A ≤ B :=
    generalizedFittingSubgroupOf_B_le_A hsimple B hB Sbar hSbarF hSbarSub hSbarCS
      hSbarA hA hSB hSF hSsub hCS (by
        rcases hpi with hA2 | hB2
        · exact Or.inr hA2
        · exact Or.inl hB2)
  by_contra hne
  rcases bender1970_1_6_maximalSubgroups_pGroups
    hsimple A B hA hB hne hFAB hFBA with ⟨p, hp, hAp, hBp⟩
  have hpiA : Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ≤ 1 :=
    card_primesOfOrder_le_one_of_isPGroup (generalizedFittingSubgroupOf A) hp hAp
  have hpiB : Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)) ≤ 1 :=
    card_primesOfOrder_le_one_of_isPGroup (generalizedFittingSubgroupOf B) hp hBp
  rcases hpi with hpiA' | hpiB'
  · omega
  · omega

end CFSG.GorensteinWalter
