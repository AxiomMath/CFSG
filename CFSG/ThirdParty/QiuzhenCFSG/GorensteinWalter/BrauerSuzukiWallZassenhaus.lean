module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearULift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_11_16
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# The Zassenhaus endpoint of the Brauer--Suzuki--Wall theorem

The structural conclusion acts by conjugation on the conjugates of its TI
subgroup `Q`.  The resulting finite Zassenhaus action is classified by
Huppert--Blackburn XI.11.16 and yields the required `D`-group conclusion.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki
open scoped Pointwise

universe u

private abbrev ConjugateOrbit {G : Type u} [Group G] (Q : Subgroup G) :=
  @MulAction.orbit G (Subgroup G)
    (MulAction.compHom _ MulAut.conj).toSMul Q

private theorem card_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type u} [Group G]
    (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.2
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr
        (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem BrauerSuzukiWallConclusion.three_le_q
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    3 ≤ h.q := by
  have hGne : Nat.card G ≠ 0 := Nat.ne_of_gt Nat.card_pos
  have hq0 : h.q ≠ 0 := by
    intro hq
    apply hGne
    rw [h.group_card, hq]
  have hq1 : h.q ≠ 1 := by
    intro hq
    apply hGne
    rw [h.group_card, hq]
  rcases h.q_odd with ⟨k, hk⟩
  omega

private theorem BrauerSuzukiWallConclusion.Q_isMulCommutative
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    IsMulCommutative h.Q := by
  apply IsMulCommutative.of_comm
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  by_cases hx : (x : G) = 1
  · simp [hx]
  have hycent : (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    rw [h.centralizer_eq_Q (x : G) x.property hx]
    exact y.property
  exact Subgroup.mem_centralizer_iff.mp hycent (x : G) (by simp)

private theorem card_conjBy
    {G : Type u} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (A.conjBy g) = Nat.card A := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := A) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective)

private theorem BrauerSuzukiWallConclusion.orbit_card_and_commutative
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G)
    (A : ConjugateOrbit h.Q) :
    Nat.card (A : Subgroup G) = h.q ∧ IsMulCommutative (A : Subgroup G) := by
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  rcases MulAction.mem_orbit_iff.mp A.property with ⟨g, hg⟩
  change h.Q.map (MulAut.conj g).toMonoidHom = (A : Subgroup G) at hg
  have hA : (A : Subgroup G) = h.Q.conjBy g := by
    simpa [Subgroup.conjBy] using hg.symm
  rw [hA]
  constructor
  · rw [card_conjBy, h.Q_card]
  · let : IsMulCommutative h.Q := h.Q_isMulCommutative
    exact Subgroup.map_isMulCommutative h.Q (MulAut.conj g).toMonoidHom

private theorem BrauerSuzukiWallConclusion.disjoint_Q_of_orbit_ne
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G)
    (A : ConjugateOrbit h.Q)
    (hA : (A : Subgroup G) ≠ h.Q) :
    Disjoint h.Q (A : Subgroup G) := by
  rw [Subgroup.disjoint_def]
  intro x hxQ hxA
  by_contra hx
  have hxne : x ≠ 1 := by simpa using hx
  have hAcomm : IsMulCommutative (A : Subgroup G) :=
    (h.orbit_card_and_commutative A).2
  have hAleCent : (A : Subgroup G) ≤
      Subgroup.centralizer ({x} : Set G) := by
    intro y hyA
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    let : IsMulCommutative (A : Subgroup G) := hAcomm
    exact congrArg Subtype.val
      (mul_comm' (⟨x, hxA⟩ : (A : Subgroup G))
        (⟨y, hyA⟩ : (A : Subgroup G)))
  have hAleQ : (A : Subgroup G) ≤ h.Q := by
    intro y hyA
    have hycent := hAleCent hyA
    rw [h.centralizer_eq_Q x hxQ hxne] at hycent
    exact hycent
  apply hA
  apply Subgroup.eq_of_le_of_card_ge hAleQ
  rw [(h.orbit_card_and_commutative A).1, h.Q_card]

private theorem BrauerSuzukiWallConclusion.fixed_orbit_eq_Q
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G)
    (A : ConjugateOrbit h.Q) (x : G)
    (hxQ : x ∈ h.Q) (hxne : x ≠ 1)
    (hxnorm : x ∈ Subgroup.normalizer ((A : Subgroup G) : Set G)) :
    (A : Subgroup G) = h.Q := by
  by_contra hA
  have hdisj : Disjoint h.Q (A : Subgroup G) :=
    h.disjoint_Q_of_orbit_ne A hA
  let Z : Subgroup G := Subgroup.zpowers x
  have hZQ : Z ≤ h.Q := Subgroup.zpowers_le.mpr hxQ
  have hZnorm : Z ≤ Subgroup.normalizer ((A : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hxnorm
  have hxorder_ne : orderOf x ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hxne
  let p : ℕ := (orderOf x).minFac
  have hp : Nat.Prime p := by
    simpa [p] using Nat.minFac_prime hxorder_ne
  let : Fact p.Prime := ⟨hp⟩
  have hpZ : p ∣ Nat.card Z := by
    rw [show Nat.card Z = orderOf x by simp [Z, Nat.card_zpowers]]
    exact Nat.minFac_dvd (orderOf x)
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Z) p hpZ
  let zG : G := z
  have hzGorder : orderOf zG = p := by
    simpa [zG, Subgroup.orderOf_coe] using hzorder
  have hzGne : zG ≠ 1 := by
    intro hz
    apply hp.ne_one
    rw [← hzGorder, hz, orderOf_one]
  have hzQ : zG ∈ h.Q := hZQ z.property
  have hzNorm : zG ∈ Subgroup.normalizer ((A : Subgroup G) : Set G) :=
    hZnorm z.property
  let P : Subgroup G := Subgroup.zpowers zG
  have hPcard : Nat.card P = p := by
    simp [P, Nat.card_zpowers, hzGorder]
  have hPleQ : P ≤ h.Q := Subgroup.zpowers_le.mpr hzQ
  have hPnormA : P ≤ Subgroup.normalizer ((A : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hzNorm
  let : MulDistribMulAction P (A : Subgroup G) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      (G := G) P (A : Subgroup G) hPnormA
  have hfixedOne :
      ∀ a : MulAction.fixedPoints P (A : Subgroup G),
        (a : (A : Subgroup G)) = 1 := by
    intro a
    let zP : P := ⟨zG, Subgroup.mem_zpowers zG⟩
    have hazfix : zP • (a : (A : Subgroup G)) = (a : (A : Subgroup G)) :=
      a.property zP
    have hazfixG : zG * (a : G) * zG⁻¹ = (a : G) := by
      rw [← Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        P (A : Subgroup G) hPnormA zP (a : (A : Subgroup G))]
      exact congrArg Subtype.val hazfix
    have hazcomm : (a : G) ∈ Subgroup.centralizer ({zG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      have hmul := congrArg (fun y : G => y * zG) hazfixG
      simpa [mul_assoc] using hmul
    have haQ : (a : G) ∈ h.Q := by
      exact (Iff.of_eq (congrArg
        (fun L : Subgroup G => (a : G) ∈ L)
        (h.centralizer_eq_Q zG hzQ hzGne))).mp hazcomm
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisj haQ (a : (A : Subgroup G)).property
  have hfixedSubsingleton :
      Subsingleton (MulAction.fixedPoints P (A : Subgroup G)) := by
    constructor
    intro a b
    apply Subtype.ext
    rw [hfixedOne a, hfixedOne b]
  have hfixedNonempty :
      Nonempty (MulAction.fixedPoints P (A : Subgroup G)) := by
    exact ⟨⟨1, fun y => smul_one y⟩⟩
  have hfixedCard :
      Nat.card (MulAction.fixedPoints P (A : Subgroup G)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hfixedSubsingleton, hfixedNonempty⟩
  have hPp : IsPGroup p P :=
    IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hmod : Nat.card (A : Subgroup G) ≡ 1 [MOD p] := by
    simpa [hfixedCard] using hPp.card_modEq_card_fixedPoints (A : Subgroup G)
  have hpA : p ∣ Nat.card (A : Subgroup G) := by
    have hpQ : p ∣ Nat.card h.Q := by
      simpa [hPcard] using Subgroup.card_dvd_of_le hPleQ
    rw [(h.orbit_card_and_commutative A).1, ← h.Q_card]
    exact hpQ
  exact hp.not_dvd_one ((hmod.dvd_iff (dvd_refl p)).mp hpA)

private theorem BrauerSuzukiWallConclusion.normalizer_Q_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    Nat.card (Subgroup.normalizer (h.Q : Set G)) =
      h.q * ((h.q - 1) / 2) := by
  have hDnorm : h.D ≤ Subgroup.normalizer (h.Q : Set G) := by
    rw [h.normalizer_Q_eq]
    exact le_sup_right
  calc
    Nat.card (Subgroup.normalizer (h.Q : Set G)) =
        Nat.card (h.Q ⊔ h.D : Subgroup G) := by rw [h.normalizer_Q_eq]
    _ = Nat.card h.Q * Nat.card h.D :=
      card_sup_eq_mul_of_disjoint_of_le_normalizer
        h.Q h.D hDnorm h.Q_disjoint_D
    _ = h.q * ((h.q - 1) / 2) := by rw [h.Q_card, h.D_card]

private theorem BrauerSuzukiWallConclusion.group_card_factorized
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    Nat.card G = (h.q + 1) * (h.q * ((h.q - 1) / 2)) := by
  have htwo : 2 ∣ h.q - 1 := by
    rcases h.q_odd with ⟨k, hk⟩
    use k
    omega
  have hmul : 2 * ((h.q - 1) / 2) = h.q - 1 :=
    Nat.mul_div_cancel' htwo
  calc
    Nat.card G = h.q * (h.q + 1) * (h.q - 1) / 2 := h.group_card
    _ = h.q * (h.q + 1) * (2 * ((h.q - 1) / 2)) / 2 := by
      rw [hmul]
    _ =
        2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) / 2 := by
      congr 1
      ring
    _ = (h.q + 1) * (h.q * ((h.q - 1) / 2)) :=
      Nat.mul_div_right _ (by omega)

private def conjugateBase {G : Type u} [Group G] (Q : Subgroup G) :
    ConjugateOrbit Q :=
  ⟨Q, @MulAction.mem_orbit_self G (Subgroup G) _
    (MulAction.compHom _ MulAut.conj) Q⟩

private theorem conjBy_eq_iff_mem_normalizer
    {G : Type u} [Group G] (A : Subgroup G) (g : G) :
    A.conjBy g = A ↔ g ∈ Subgroup.normalizer (A : Set G) := by
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : g * x * g⁻¹ ∈ A.conjBy g := by
        exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
      simpa [hg] using hx'
    · intro hx
      have hx' : g * x * g⁻¹ ∈ A.conjBy g := by simpa [hg] using hx
      rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
      have hxy : x = y := by
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * (MulAut.conj g).toMonoidHom y * g := by
            exact congrArg (fun z : G => g⁻¹ * z * g) hyx.symm
          _ = y := by simp [MulAut.conj_apply, mul_assoc]
      simpa [hxy] using hy
  · intro hg
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using
        ((Subgroup.mem_normalizer_iff.mp hg y).mp hy)
    · intro hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
      · have hginv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
          (Subgroup.normalizer (A : Set G)).inv_mem hg
        simpa [mul_assoc] using
          ((Subgroup.mem_normalizer_iff.mp hginv x).mp hx)
      · simp [MulAut.conj_apply, mul_assoc]

private theorem BrauerSuzukiWallConclusion.stabilizer_conjugateBase
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    MulAction.stabilizer G (conjugateBase h.Q) =
      Subgroup.normalizer (h.Q : Set G) := by
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    have hgval := congrArg Subtype.val hg
    change h.Q.conjBy g = h.Q at hgval
    exact (conjBy_eq_iff_mem_normalizer h.Q g).mp hgval
  · intro hg
    apply Subtype.ext
    change h.Q.conjBy g = h.Q
    exact (conjBy_eq_iff_mem_normalizer h.Q g).mpr hg

private theorem BrauerSuzukiWallConclusion.orbit_degree
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    Nat.card (ConjugateOrbit h.Q) = h.q + 1 := by
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  have htrans : MulAction.IsPretransitive G Omega := by
    constructor
    intro A B
    rcases MulAction.mem_orbit_iff.mp A.property with ⟨a, ha⟩
    rcases MulAction.mem_orbit_iff.mp B.property with ⟨b, hb⟩
    refine ⟨b * a⁻¹, ?_⟩
    apply Subtype.ext
    change (b * a⁻¹) • (A : Subgroup G) = (B : Subgroup G)
    rw [← ha, ← hb]
    simp [mul_smul]
  let : MulAction.IsPretransitive G Omega := htrans
  have hstab : MulAction.stabilizer G base =
      Subgroup.normalizer (h.Q : Set G) := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      have hgval := congrArg Subtype.val hg
      change h.Q.conjBy g = h.Q at hgval
      exact (conjBy_eq_iff_mem_normalizer h.Q g).mp hgval
    · intro hg
      apply Subtype.ext
      change h.Q.conjBy g = h.Q
      exact (conjBy_eq_iff_mem_normalizer h.Q g).mpr hg
  have hindex : (Subgroup.normalizer (h.Q : Set G)).index =
      Nat.card Omega := by
    rw [← hstab]
    exact MulAction.index_stabilizer_of_transitive G base
  have hmul := (Subgroup.normalizer (h.Q : Set G)).card_mul_index
  rw [hindex, h.normalizer_Q_card, h.group_card_factorized] at hmul
  have hfactorPos : 0 < h.q * ((h.q - 1) / 2) := by
    have hq := h.three_le_q
    have hd : 0 < (h.q - 1) / 2 := by omega
    exact Nat.mul_pos (by omega) hd
  apply Nat.eq_of_mul_eq_mul_left hfactorPos
  calc
    h.q * ((h.q - 1) / 2) * Nat.card Omega =
        (h.q + 1) * (h.q * ((h.q - 1) / 2)) := hmul
    _ = h.q * ((h.q - 1) / 2) * (h.q + 1) := by ring

private theorem BrauerSuzukiWallConclusion.orbit_two_transitive
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    MulAction.IsMultiplyPretransitive G (ConjugateOrbit h.Q) 2 := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  have hQfix : ∀ q : h.Q, (q : G) • base = base := by
    intro q
    apply Subtype.ext
    change h.Q.conjBy (q : G) = h.Q
    apply (conjBy_eq_iff_mem_normalizer h.Q (q : G)).mpr
    rw [h.normalizer_Q_eq]
    exact Subgroup.mem_sup_left q.property
  have hQtrans :
      ∀ A B : Omega, A ≠ base → B ≠ base →
        ∃ q : h.Q, (q : G) • A = B := by
    intro A B hA hB
    let Away := {C : Omega // C ≠ base}
    let orbitMap : h.Q → Away := fun q => ⟨(q : G) • A, by
      intro hqA
      apply hA
      calc
        A = (q : G)⁻¹ • ((q : G) • A) := (inv_smul_smul (q : G) A).symm
        _ = (q : G)⁻¹ • base := by rw [hqA]
        _ = base := hQfix ⟨(q : G)⁻¹, h.Q.inv_mem q.property⟩⟩
    have horbitMapInj : Function.Injective orbitMap := by
      intro q r hqr
      have hqrval : (q : G) • A = (r : G) • A :=
        congrArg (fun C : Away => (C : Omega)) hqr
      let x : G := (r : G)⁻¹ * (q : G)
      have hxQ : x ∈ h.Q :=
        h.Q.mul_mem (h.Q.inv_mem r.property) q.property
      have hxfix : x • A = A := by
        calc
          x • A = (r : G)⁻¹ • ((q : G) • A) := by
            simp [x, mul_smul]
          _ = (r : G)⁻¹ • ((r : G) • A) := by rw [hqrval]
          _ = A := inv_smul_smul (r : G) A
      have hxnorm : x ∈
          Subgroup.normalizer (((A : Omega) : Subgroup G) : Set G) := by
        apply (conjBy_eq_iff_mem_normalizer (A : Subgroup G) x).mp
        have hxfixVal := congrArg Subtype.val hxfix
        change (A : Subgroup G).conjBy x = (A : Subgroup G) at hxfixVal
        exact hxfixVal
      have hxone : x = 1 := by
        by_contra hxne
        have hAQ := h.fixed_orbit_eq_Q A x hxQ hxne hxnorm
        apply hA
        apply Subtype.ext
        exact hAQ
      apply Subtype.ext
      have hmul := congrArg (fun z : G => (r : G) * z) hxone
      simpa [x, mul_assoc] using hmul
    have hAwayCard : Nat.card Away = h.q := by
      change Nat.card {C : Omega // C ≠ base} = h.q
      calc
        Nat.card {C : Omega // C ≠ base} = Nat.card Omega - 1 := by
          let : Fintype {C : Omega // C ≠ base} := Fintype.ofFinite _
          simpa [Nat.card_eq_fintype_card] using
            (Fintype.card_subtype_compl (fun C : Omega => C = base))
        _ = h.q := by rw [h.orbit_degree]; omega
    let : Fintype h.Q := Fintype.ofFinite h.Q
    let : Fintype Away := Fintype.ofFinite Away
    have horbitMapBij : Function.Bijective orbitMap :=
      (Fintype.bijective_iff_injective_and_card orbitMap).2
        ⟨horbitMapInj, by
          calc
            Fintype.card h.Q = Nat.card h.Q := Nat.card_eq_fintype_card.symm
            _ = h.q := h.Q_card
            _ = Nat.card Away := hAwayCard.symm
            _ = Fintype.card Away := Nat.card_eq_fintype_card⟩
    let bAway : Away := ⟨B, hB⟩
    rcases horbitMapBij.2 bAway with ⟨q, hq⟩
    exact ⟨q, congrArg (fun C : Away => (C : Omega)) hq⟩
  have htrans : MulAction.IsPretransitive G Omega := by
    constructor
    intro A B
    rcases MulAction.mem_orbit_iff.mp A.property with ⟨a, ha⟩
    rcases MulAction.mem_orbit_iff.mp B.property with ⟨b, hb⟩
    refine ⟨b * a⁻¹, ?_⟩
    apply Subtype.ext
    change (b * a⁻¹) • (A : Subgroup G) = (B : Subgroup G)
    rw [← ha, ← hb]
    simp [mul_smul]
  let : MulAction.IsPretransitive G Omega := htrans
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨r, hra⟩ := MulAction.exists_smul_eq G a base
  obtain ⟨s, hsc⟩ := MulAction.exists_smul_eq G c base
  have hrb : r • b ≠ base := by
    intro hrb
    apply hab
    apply (MulAction.toPerm r).injective
    change r • a = r • b
    exact hra.trans hrb.symm
  have hsd : s • d ≠ base := by
    intro hsd
    apply hcd
    apply (MulAction.toPerm s).injective
    change s • c = s • d
    exact hsc.trans hsd.symm
  obtain ⟨q, hq⟩ := hQtrans (r • b) (s • d) hrb hsd
  refine ⟨s⁻¹ * (q : G) * r, ?_, ?_⟩
  · calc
      (s⁻¹ * (q : G) * r) • a =
          s⁻¹ • ((q : G) • (r • a)) := by simp [mul_smul]
      _ = s⁻¹ • ((q : G) • base) := by rw [hra]
      _ = s⁻¹ • base := by rw [hQfix q]
      _ = c := by
        simpa using (congrArg (fun C : Omega => s⁻¹ • C) hsc).symm
  · calc
      (s⁻¹ * (q : G) * r) • b =
          s⁻¹ • ((q : G) • (r • b)) := by simp [mul_smul]
      _ = s⁻¹ • (s • d) := by rw [hq]
      _ = d := inv_smul_smul s d

private theorem BrauerSuzukiWallConclusion.existsUnique_Q_smul_eq_away
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G)
    (A B : ConjugateOrbit h.Q)
    (hA : A ≠ conjugateBase h.Q)
    (hB : B ≠ conjugateBase h.Q) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    ∃! q : h.Q, (q : G) • A = B := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  let Away := {C : Omega // C ≠ base}
  let orbitMap : h.Q → Away := fun q => ⟨(q : G) • A, by
    intro hqA
    apply hA
    calc
      A = (q : G)⁻¹ • ((q : G) • A) := (inv_smul_smul (q : G) A).symm
      _ = (q : G)⁻¹ • base := by rw [hqA]
      _ = base := by
        apply Subtype.ext
        change h.Q.conjBy (q : G)⁻¹ = h.Q
        apply (conjBy_eq_iff_mem_normalizer h.Q (q : G)⁻¹).mpr
        rw [h.normalizer_Q_eq]
        exact Subgroup.mem_sup_left (h.Q.inv_mem q.property)⟩
  have horbitMapInj : Function.Injective orbitMap := by
    intro q r hqr
    have hqrval : (q : G) • A = (r : G) • A :=
      congrArg (fun C : Away => (C : Omega)) hqr
    let x : G := (r : G)⁻¹ * (q : G)
    have hxQ : x ∈ h.Q :=
      h.Q.mul_mem (h.Q.inv_mem r.property) q.property
    have hxfix : x • A = A := by
      calc
        x • A = (r : G)⁻¹ • ((q : G) • A) := by
          simp [x, mul_smul]
        _ = (r : G)⁻¹ • ((r : G) • A) := by rw [hqrval]
        _ = A := inv_smul_smul (r : G) A
    have hxnorm : x ∈
        Subgroup.normalizer ((A : Subgroup G) : Set G) := by
      apply (conjBy_eq_iff_mem_normalizer (A : Subgroup G) x).mp
      exact congrArg Subtype.val hxfix
    have hxone : x = 1 := by
      by_contra hxne
      have hAQ := h.fixed_orbit_eq_Q A x hxQ hxne hxnorm
      apply hA
      apply Subtype.ext
      exact hAQ
    apply Subtype.ext
    have hmul := congrArg (fun z : G => (r : G) * z) hxone
    simpa [x, mul_assoc] using hmul
  have hAwayCard : Nat.card Away = h.q := by
    change Nat.card {C : Omega // C ≠ base} = h.q
    calc
      Nat.card {C : Omega // C ≠ base} = Nat.card Omega - 1 := by
        let : Fintype {C : Omega // C ≠ base} := Fintype.ofFinite _
        simpa [Nat.card_eq_fintype_card] using
          (Fintype.card_subtype_compl (fun C : Omega => C = base))
      _ = h.q := by rw [h.orbit_degree]; omega
  let : Fintype h.Q := Fintype.ofFinite h.Q
  let : Fintype Away := Fintype.ofFinite Away
  have horbitMapBij : Function.Bijective orbitMap :=
    (Fintype.bijective_iff_injective_and_card orbitMap).2
      ⟨horbitMapInj, by
        calc
          Fintype.card h.Q = Nat.card h.Q := Nat.card_eq_fintype_card.symm
          _ = h.q := h.Q_card
          _ = Nat.card Away := hAwayCard.symm
          _ = Fintype.card Away := Nat.card_eq_fintype_card⟩
  let bAway : Away := ⟨B, hB⟩
  obtain ⟨q, hq⟩ := horbitMapBij.2 bAway
  refine ⟨q, congrArg (fun C : Away => (C : Omega)) hq, ?_⟩
  intro r hr
  apply horbitMapInj
  apply Subtype.ext
  exact hr.trans (congrArg (fun C : Away => (C : Omega)) hq).symm

private theorem BrauerSuzukiWallConclusion.orbit_faithful
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    FaithfulSMul G (ConjugateOrbit h.Q) := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  have hOmegaLarge : 1 < Fintype.card Omega := by
    rw [← Nat.card_eq_fintype_card, h.orbit_degree]
    have hq := h.three_le_q
    omega
  obtain ⟨A, B, hAB⟩ := Fintype.one_lt_card_iff.mp hOmegaLarge
  obtain ⟨away, haway⟩ : ∃ away : Omega, away ≠ base := by
    by_cases hA : A = base
    · exact ⟨B, fun hB => hAB (hA.trans hB.symm)⟩
    · exact ⟨A, hA⟩
  rw [faithfulSMul_iff]
  intro g hfix
  have hginvfix : ∀ C : Omega, g⁻¹ • C = C := by
    intro C
    calc
      g⁻¹ • C = g⁻¹ • (g • C) := by rw [hfix C]
      _ = C := inv_smul_smul g C
  have hgnormQ : g ∈ Subgroup.normalizer (h.Q : Set G) := by
    apply (conjBy_eq_iff_mem_normalizer h.Q g).mp
    have hgbase := congrArg Subtype.val (hfix base)
    change h.Q.conjBy g = h.Q at hgbase
    exact hgbase
  have hcommQ : ∀ q : h.Q, g * (q : G) = (q : G) * g := by
    intro q
    let x : G := g * (q : G) * g⁻¹ * (q : G)⁻¹
    have hxQ : x ∈ h.Q := by
      apply h.Q.mul_mem
      · exact (Subgroup.mem_normalizer_iff.mp hgnormQ (q : G)).mp q.property
      · exact h.Q.inv_mem q.property
    have hxfix : ∀ C : Omega, x • C = C := by
      intro C
      calc
        x • C = g • ((q : G) • (g⁻¹ • ((q : G)⁻¹ • C))) := by
          simp [x, mul_smul, mul_assoc]
        _ = (q : G) • (g⁻¹ • ((q : G)⁻¹ • C)) := hfix _
        _ = (q : G) • ((q : G)⁻¹ • C) := by rw [hginvfix]
        _ = C := smul_inv_smul (q : G) C
    have hxnormAway : x ∈
        Subgroup.normalizer (((away : Omega) : Subgroup G) : Set G) := by
      apply (conjBy_eq_iff_mem_normalizer (away : Subgroup G) x).mp
      have hxaway := congrArg Subtype.val (hxfix away)
      change (away : Subgroup G).conjBy x = (away : Subgroup G) at hxaway
      exact hxaway
    have hxone : x = 1 := by
      by_contra hxne
      have hawayQ := h.fixed_orbit_eq_Q away x hxQ hxne hxnormAway
      apply haway
      apply Subtype.ext
      exact hawayQ
    calc
      g * (q : G) = x * ((q : G) * g) := by
        simp [x, mul_assoc]
      _ = (q : G) * g := by rw [hxone]; simp
  have hQne : h.Q ≠ ⊥ := by
    intro hbot
    have hcardOne : Nat.card h.Q = 1 := by simp [hbot]
    have hq := h.three_le_q
    rw [h.Q_card] at hcardOne
    omega
  obtain ⟨q, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have hqGne : (q : G) ≠ 1 := by
    intro hqone
    exact hqne (Subtype.ext hqone)
  have hgcent : g ∈ Subgroup.centralizer ({(q : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact (hcommQ q).symm
  have hgQ : g ∈ h.Q := by
    exact (Iff.of_eq (congrArg
      (fun L : Subgroup G => g ∈ L)
      (h.centralizer_eq_Q (q : G) q.property hqGne))).mp hgcent
  have hgnormAway : g ∈
      Subgroup.normalizer (((away : Omega) : Subgroup G) : Set G) := by
    apply (conjBy_eq_iff_mem_normalizer (away : Subgroup G) g).mp
    have hgaway := congrArg Subtype.val (hfix away)
    change (away : Subgroup G).conjBy g = (away : Subgroup G) at hgaway
    exact hgaway
  by_contra hgne
  have hawayQ := h.fixed_orbit_eq_Q away g hgQ hgne hgnormAway
  apply haway
  apply Subtype.ext
  exact hawayQ

private theorem BrauerSuzukiWallConclusion.iso_alternatingGroup_four_of_q_eq_three
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q = 3) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  let : FaithfulSMul G Omega := h.orbit_faithful
  let rho : G →* Equiv.Perm Omega := MulAction.toPermHom G Omega
  let K : Subgroup (Equiv.Perm Omega) := rho.range
  have hrho : Function.Injective rho := MulAction.toPerm_injective
  let e : G ≃* K :=
    MulEquiv.ofBijective rho.rangeRestrict
      ⟨fun a b hab => hrho (congrArg Subtype.val hab),
        rho.rangeRestrict_surjective⟩
  have hGcard : Nat.card G = 12 := by
    rw [h.group_card, hq]
  have hKcard : Nat.card K = 12 := by
    rw [← hGcard]
    exact (Nat.card_congr e.toEquiv).symm
  have hOmegaCard : Nat.card Omega = 4 := by
    rw [h.orbit_degree, hq]
  have hPermCard : Nat.card (Equiv.Perm Omega) = 24 := by
    rw [Nat.card_perm, hOmegaCard]
    norm_num [Nat.factorial]
  have hKindex : K.index = 2 := by
    have hcard := K.index_mul_card
    rw [hKcard, hPermCard] at hcard
    omega
  have hKalt : K = alternatingGroup Omega :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hKindex
  rw [hKalt] at e
  let eOmega : Omega ≃ Fin 4 := Finite.equivFinOfCardEq hOmegaCard
  exact ⟨e.trans (Equiv.altCongrHom eOmega)⟩

private theorem BrauerSuzukiWallConclusion.pPrimeCore_eq_bot_of_q_eq_three
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q = 3) :
    pPrimeCore 2 G = ⊥ := by
  classical
  let O : Subgroup G := pPrimeCore 2 G
  have hGcard : Nat.card G = 12 := by
    rw [h.group_card, hq]
  have hOdiv : Nat.card O ∣ 12 := by
    rw [← hGcard]
    exact O.card_subgroup_dvd_card
  have hOcop : Nat.Coprime 2 (Nat.card O) :=
    pPrimeCore_coprime_card (p := 2) (G := G)
  have hFourO : Nat.Coprime 4 (Nat.card O) := by
    simpa using hOcop.pow_left 2
  have hOdivThree : Nat.card O ∣ 3 := by
    apply hFourO.symm.dvd_of_dvd_mul_right
    norm_num at hOdiv ⊢
    exact hOdiv
  have hOcard : Nat.card O = 1 ∨ Nat.card O = 3 := by
    exact (Nat.dvd_prime Nat.prime_three).mp hOdivThree
  rcases hOcard with hOone | hOthree
  · exact (Subgroup.eq_bot_iff_card O).2 hOone
  · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hfactor : 3 ^ (Nat.card G).factorization 3 = 3 := by
      rw [hGcard]
      rw [Nat.factorization_def _ Nat.prime_three]
      rw [show 12 = 4 * 3 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.self] <;>
        norm_num
    let Qsyl : Sylow 3 G := Sylow.ofCard h.Q (by
      rw [h.Q_card, hq, hfactor])
    let Osyl : Sylow 3 G := Sylow.ofCard O (by
      rw [hOthree, hfactor])
    let : Unique (Sylow 3 G) :=
      Sylow.unique_of_normal Osyl (show O.Normal from pPrimeCore_normal)
    have hQO : h.Q = O := by
      exact congrArg (fun P : Sylow 3 G => (P : Subgroup G))
        (Subsingleton.elim Qsyl Osyl)
    have hQnormal : h.Q.Normal := by
      rw [hQO]
      exact pPrimeCore_normal
    let : h.Q.Normal := hQnormal
    have hDbot : h.D = ⊥ := by
      apply (Subgroup.eq_bot_iff_card h.D).2
      rw [h.D_card, hq]
    have hnormQ : Subgroup.normalizer (h.Q : Set G) = h.Q := by
      rw [h.normalizer_Q_eq, hDbot, sup_bot_eq]
    have hQtop : h.Q = ⊤ := by
      rw [← hnormQ, Subgroup.normalizer_eq_top]
    have hcardQtop : Nat.card h.Q = Nat.card G := by
      rw [hQtop]
      exact Subgroup.card_top
    rw [h.Q_card, hq, hGcard] at hcardQtop
    omega

private theorem BrauerSuzukiWallConclusion.hasDihedralSylowTwo_of_q_eq_three
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q = 3) :
    HasDihedralSylowTwo G := by
  classical
  let e : G ≃* alternatingGroup (Fin 4) :=
    (h.iso_alternatingGroup_four_of_q_eq_three hq).some
  apply hasDihedralSylowTwo_of_mulEquiv e
  intro S
  refine ⟨1, by omega, ?_⟩
  rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) S]
  let : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour (by simp)
  simpa using
    (IsKleinFour.nonempty_mulEquiv
      (G₁ := alternatingGroup.kleinFour (Fin 4))
      (G₂ := DihedralGroup 2))

private theorem BrauerSuzukiWallConclusion.D_ne_bot_of_q_ne_three
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q ≠ 3) :
    h.D ≠ ⊥ := by
  intro hDbot
  have hDcardOne : Nat.card h.D = 1 := by simp [hDbot]
  have hhalf : (h.q - 1) / 2 = 1 := by
    rw [← h.D_card, hDcardOne]
  rcases h.q_odd with ⟨k, hk⟩
  have hqge := h.three_le_q
  omega

private theorem eq_one_or_eq_of_mem_zpowers_involution_zassenhaus
    {G : Type u} [Group G] [Finite G]
    {a x : G} (ha : IsInvolution a)
    (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a := by
  let Z : Subgroup G := Subgroup.zpowers a
  have haOrder : orderOf a = 2 := orderOf_eq_prime ha.2 ha.1
  have hZcard : Nat.card Z = 2 := by
    simp [Z, Nat.card_zpowers, haOrder]
  have haZ : a ∈ Z := Subgroup.mem_zpowers a
  have haZne : (⟨a, haZ⟩ : Z) ≠ 1 := by
    intro heq
    exact ha.1 (congrArg Subtype.val heq)
  have hZeq : ∀ z : Z, z = 1 ∨ z = ⟨a, haZ⟩ := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' (1 : Z)).mp hZcard with
        ⟨z0, _hz0ne, hz0uniq⟩
      exact Or.inr
        ((hz0uniq z hz).trans (hz0uniq ⟨a, haZ⟩ haZne).symm)
  rcases hZeq ⟨x, hx⟩ with hx1 | hxa
  · exact Or.inl (congrArg Subtype.val hx1)
  · exact Or.inr (congrArg Subtype.val hxa)

private theorem BrauerSuzukiWallConclusion.normalizer_Q_inf_normalizer_D_eq_D
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q ≠ 3) :
    Subgroup.normalizer (h.Q : Set G) ⊓
        Subgroup.normalizer (h.D : Set G) = h.D := by
  classical
  let NQ : Subgroup G := Subgroup.normalizer (h.Q : Set G)
  let ND : Subgroup G := Subgroup.normalizer (h.D : Set G)
  let I : Subgroup G := NQ ⊓ ND
  have hDne : h.D ≠ ⊥ := h.D_ne_bot_of_q_ne_three hq
  obtain ⟨u, _hNX, hND, hu, huD, _huinv⟩ :=
    h.normalizer_subgroup_data h.D hDne le_rfl
  let Z : Subgroup G := Subgroup.zpowers u
  have huOrder : orderOf u = 2 := orderOf_eq_prime hu.2 hu.1
  have hZcard : Nat.card Z = 2 := by
    simp [Z, Nat.card_zpowers, huOrder]
  have hDZ : Disjoint h.D Z := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxZ
    rcases eq_one_or_eq_of_mem_zpowers_involution_zassenhaus hu hxZ with
      hxone | hxu
    · exact hxone
    · exact (huD (hxu ▸ hxD)).elim
  have hZleND : Z ≤ ND := by
    change Z ≤ Subgroup.normalizer (h.D : Set G)
    rw [hND]
    exact le_sup_right
  have hNDcard : Nat.card ND = 2 * ((h.q - 1) / 2) := by
    calc
      Nat.card ND = Nat.card (h.D ⊔ Z : Subgroup G) := by
        change Nat.card (Subgroup.normalizer (h.D : Set G)) = _
        rw [hND]
      _ = Nat.card h.D * Nat.card Z :=
        card_sup_eq_mul_of_disjoint_of_le_normalizer
          h.D Z hZleND hDZ
      _ = 2 * ((h.q - 1) / 2) := by
        rw [h.D_card, hZcard]
        ring
  have hIdivNQ : Nat.card I ∣ h.q * ((h.q - 1) / 2) := by
    have hdiv : Nat.card I ∣ Nat.card NQ :=
      Subgroup.card_dvd_of_le (show I ≤ NQ from inf_le_left)
    simpa [NQ, h.normalizer_Q_card] using hdiv
  have hIdivND : Nat.card I ∣ 2 * ((h.q - 1) / 2) := by
    have hdiv : Nat.card I ∣ Nat.card ND :=
      Subgroup.card_dvd_of_le (show I ≤ ND from inf_le_right)
    simpa [hNDcard] using hdiv
  have hqCoprimeTwo : Nat.Coprime h.q 2 :=
    Nat.coprime_two_right.mpr h.q_odd
  have hIdivD : Nat.card I ∣ (h.q - 1) / 2 := by
    have hgcd := Nat.dvd_gcd hIdivNQ hIdivND
    rw [Nat.gcd_mul_right, hqCoprimeTwo.gcd_eq_one, one_mul] at hgcd
    exact hgcd
  have hDleI : h.D ≤ I := by
    apply le_inf
    · change h.D ≤ Subgroup.normalizer (h.Q : Set G)
      rw [h.normalizer_Q_eq]
      exact le_sup_right
    · exact Subgroup.le_normalizer
  have hDpos : 0 < (h.q - 1) / 2 := by
    rw [← h.D_card]
    exact Nat.card_pos
  have hIleDcard : Nat.card I ≤ Nat.card h.D := by
    rw [h.D_card]
    exact Nat.le_of_dvd hDpos hIdivD
  have hDI : h.D = I :=
    Subgroup.eq_of_le_of_card_ge hDleI hIleDcard
  exact hDI.symm

private theorem BrauerSuzukiWallConclusion.exists_reflection_two_point_stabilizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q ≠ 3) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    ∃ u : G,
      Subgroup.normalizer (h.D : Set G) =
          h.D ⊔ Subgroup.zpowers u ∧
        IsInvolution u ∧
        u ∉ h.D ∧
        (∀ d : G, d ∈ h.D → u * d * u⁻¹ = d⁻¹) ∧
        conjugateBase h.Q ≠ u • conjugateBase h.Q ∧
        MulAction.stabilizer G (conjugateBase h.Q) ⊓
            MulAction.stabilizer G (u • conjugateBase h.Q) = h.D := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  have hDne : h.D ≠ ⊥ := h.D_ne_bot_of_q_ne_three hq
  obtain ⟨u, _hNX, hND, hu, huD, huinv⟩ :=
    h.normalizer_subgroup_data h.D hDne le_rfl
  refine ⟨u, hND, hu, huD, huinv, ?_, ?_⟩
  · intro hbase
    have huNQ : u ∈ Subgroup.normalizer (h.Q : Set G) := by
      rw [← h.stabilizer_conjugateBase]
      exact MulAction.mem_stabilizer_iff.mpr hbase.symm
    have huND : u ∈ Subgroup.normalizer (h.D : Set G) := by
      rw [hND]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have huInf : u ∈
        Subgroup.normalizer (h.Q : Set G) ⊓
          Subgroup.normalizer (h.D : Set G) := ⟨huNQ, huND⟩
    rw [h.normalizer_Q_inf_normalizer_D_eq_D hq] at huInf
    exact huD huInf
  · let H : Subgroup G := MulAction.stabilizer G base
    let beta : Omega := u • base
    let T : Subgroup G := H ⊓ MulAction.stabilizer G beta
    have hbaseNe : base ≠ beta := by
      intro hbase
      have huNQ : u ∈ Subgroup.normalizer (h.Q : Set G) := by
        rw [← h.stabilizer_conjugateBase]
        exact MulAction.mem_stabilizer_iff.mpr hbase.symm
      have huND : u ∈ Subgroup.normalizer (h.D : Set G) := by
        rw [hND]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      have huInf : u ∈
          Subgroup.normalizer (h.Q : Set G) ⊓
            Subgroup.normalizer (h.D : Set G) := ⟨huNQ, huND⟩
      rw [h.normalizer_Q_inf_normalizer_D_eq_D hq] at huInf
      exact huD huInf
    have hDleH : h.D ≤ H := by
      change h.D ≤ MulAction.stabilizer G base
      rw [h.stabilizer_conjugateBase, h.normalizer_Q_eq]
      exact le_sup_right
    have huNDmem : u ∈ Subgroup.normalizer (h.D : Set G) := by
      rw [hND]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have huSelf : u⁻¹ = u := by
      have huu : u * u = 1 := by simpa [pow_two] using hu.2
      exact inv_eq_of_mul_eq_one_right huu
    have hDleBeta : h.D ≤ MulAction.stabilizer G beta := by
      intro d hd
      rw [MulAction.mem_stabilizer_iff]
      have hdconj : u⁻¹ * (d : G) * u ∈ h.D := by
        simpa [huSelf] using
          ((Subgroup.mem_normalizer_iff.mp huNDmem (d : G)).mp hd)
      calc
        (d : G) • beta = u • ((u⁻¹ * (d : G) * u) • base) := by
          simp [beta, mul_smul, mul_assoc]
        _ = u • base := by
          rw [MulAction.mem_stabilizer_iff.mp (hDleH hdconj)]
        _ = beta := rfl
    have hDleT : h.D ≤ T := le_inf hDleH hDleBeta
    let Away := SubMulAction.ofStabilizer G base
    let betaAway : Away := ⟨beta, hbaseNe.symm⟩
    let S : Subgroup H := MulAction.stabilizer H betaAway
    have htwo : MulAction.IsMultiplyPretransitive G Omega 2 :=
      h.orbit_two_transitive
    let : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    let : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hAwayTrans : MulAction.IsPretransitive H Away := by
      rw [← MulAction.is_one_pretransitive_iff]
      exact (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := G) (a := base) (n := 1)).mp htwo
    let : MulAction.IsPretransitive H Away := hAwayTrans
    have hAwayCard : Nat.card Away = h.q := by
      change Nat.card {C : Omega // C ≠ base} = h.q
      calc
        Nat.card {C : Omega // C ≠ base} = Nat.card Omega - 1 := by
          let : Fintype {C : Omega // C ≠ base} := Fintype.ofFinite _
          simpa [Nat.card_eq_fintype_card] using
            (Fintype.card_subtype_compl (fun C : Omega => C = base))
        _ = h.q := by rw [h.orbit_degree]; omega
    have hSindex : S.index = h.q := by
      change (MulAction.stabilizer H betaAway).index = h.q
      rw [MulAction.index_stabilizer_of_transitive H betaAway, hAwayCard]
    have hHcard : Nat.card H = h.q * ((h.q - 1) / 2) := by
      change Nat.card (MulAction.stabilizer G base) = _
      rw [h.stabilizer_conjugateBase, h.normalizer_Q_card]
    have hScard : Nat.card S = (h.q - 1) / 2 := by
      have hcard := S.card_mul_index
      rw [hSindex, hHcard] at hcard
      apply Nat.eq_of_mul_eq_mul_right (by
        have hqge := h.three_le_q
        omega : 0 < h.q)
      calc
        Nat.card S * h.q = h.q * ((h.q - 1) / 2) := hcard
        _ = ((h.q - 1) / 2) * h.q := by ring
    have hTleH : T ≤ H := inf_le_left
    have hTsubEq : T.subgroupOf H = S := by
      ext x
      change ((x : G) ∈ T) ↔ (x : H) • betaAway = betaAway
      constructor
      · intro hx
        apply Subtype.ext
        exact MulAction.mem_stabilizer_iff.mp hx.2
      · intro hx
        refine ⟨x.property, MulAction.mem_stabilizer_iff.mpr ?_⟩
        exact congrArg Subtype.val hx
    have hTcard : Nat.card T = (h.q - 1) / 2 := by
      rw [← hScard, ← hTsubEq]
      exact (natCard_subgroupOf_eq T H hTleH).symm
    exact (Subgroup.eq_of_le_of_card_ge hDleT (by
      rw [hTcard, h.D_card])).symm

private theorem BrauerSuzukiWallConclusion.at_most_two_fixed_points
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q ≠ 3) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    ∀ g : G, g ≠ 1 →
      ∀ a b c : ConjugateOrbit h.Q,
        a ≠ b → a ≠ c → b ≠ c →
        ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  obtain ⟨u, _hND, _hu, _huD, _huinv, hbaseNe, hDtwo⟩ :=
    h.exists_reflection_two_point_stabilizer hq
  let beta : Omega := u • base
  intro g hg a b c hab hac hbc hfix
  obtain ⟨k, hka, hkb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp h.orbit_two_transitive)
      hab hbaseNe
  let x : G := k * g * k⁻¹
  have hxne : x ≠ 1 := by
    intro hx
    apply hg
    have hconj := congrArg (fun z : G => k⁻¹ * z * k) hx
    simpa [x, mul_assoc] using hconj
  have hxbase : x • base = base := by
    calc
      x • base = k • (g • (k⁻¹ • base)) := by
        simp [x, mul_smul, mul_assoc]
      _ = k • (g • a) := by
        apply congrArg (fun z => k • (g • z))
        simpa using congrArg (fun z => k⁻¹ • z) hka.symm
      _ = k • a := by rw [hfix.1]
      _ = base := hka
  have hxbeta : x • beta = beta := by
    calc
      x • beta = k • (g • (k⁻¹ • beta)) := by
        simp [x, mul_smul, mul_assoc]
      _ = k • (g • b) := by
        apply congrArg (fun z => k • (g • z))
        simpa using congrArg (fun z => k⁻¹ • z) hkb.symm
      _ = k • b := by rw [hfix.2.1]
      _ = beta := hkb
  let third : Omega := k • c
  have hxthird : x • third = third := by
    simp [x, third, mul_smul, mul_assoc, hfix.2.2]
  have hbaseThird : base ≠ third := by
    intro heq
    apply hac
    apply (MulAction.toPerm k).injective
    simpa [hka, third] using heq
  have hbetaThird : beta ≠ third := by
    intro heq
    apply hbc
    apply (MulAction.toPerm k).injective
    simpa [hkb, third] using heq
  have hxD : x ∈ h.D := by
    have hxTwo : x ∈
        MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta :=
      ⟨MulAction.mem_stabilizer_iff.mpr hxbase,
        MulAction.mem_stabilizer_iff.mpr hxbeta⟩
    rw [hDtwo] at hxTwo
    exact hxTwo
  obtain ⟨q, hqthird, _hqunique⟩ :=
    h.existsUnique_Q_smul_eq_away beta third hbaseNe.symm hbaseThird.symm
  have hqne : (q : G) ≠ 1 := by
    intro hqone
    apply hbetaThird
    calc
      beta = (q : G) • beta := by simp [hqone]
      _ = third := hqthird
  have hqbase : (q : G) • base = base := by
    apply Subtype.ext
    change h.Q.conjBy (q : G) = h.Q
    apply (conjBy_eq_iff_mem_normalizer h.Q (q : G)).mpr
    rw [h.normalizer_Q_eq]
    exact Subgroup.mem_sup_left q.property
  let y : G := (q : G)⁻¹ * x * (q : G)
  have hybase : y • base = base := by
    calc
      y • base = (q : G)⁻¹ • (x • ((q : G) • base)) := by
        simp [y, mul_smul, mul_assoc]
      _ = (q : G)⁻¹ • (x • base) := by rw [hqbase]
      _ = (q : G)⁻¹ • base := by rw [hxbase]
      _ = base := by
        simpa using (congrArg (fun z : Omega => (q : G)⁻¹ • z) hqbase).symm
  have hybeta : y • beta = beta := by
    calc
      y • beta = (q : G)⁻¹ • (x • ((q : G) • beta)) := by
        simp [y, mul_smul, mul_assoc]
      _ = (q : G)⁻¹ • (x • third) := by rw [hqthird]
      _ = (q : G)⁻¹ • third := by rw [hxthird]
      _ = beta := by
        simpa using (congrArg (fun z : Omega => (q : G)⁻¹ • z) hqthird).symm
  have hyD : y ∈ h.D := by
    have hyTwo : y ∈
        MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta :=
      ⟨MulAction.mem_stabilizer_iff.mpr hybase,
        MulAction.mem_stabilizer_iff.mpr hybeta⟩
    rw [hDtwo] at hyTwo
    exact hyTwo
  let X : Subgroup G := Subgroup.zpowers x
  let Xq : Subgroup G := X.conjBy (q : G)⁻¹
  have hXne : X ≠ ⊥ := by
    intro hXbot
    apply hxne
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hXbot]
      exact Subgroup.mem_zpowers x
    simpa using hxbot
  have hXleD : X ≤ h.D := Subgroup.zpowers_le.mpr hxD
  have hXqEq : Xq = Subgroup.zpowers y := by
    change (Subgroup.zpowers x).map
        (MulAut.conj (q : G)⁻¹).toMonoidHom = Subgroup.zpowers y
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, y]
  have hXqne : Xq ≠ ⊥ := by
    intro hXqbot
    apply hXne
    apply (Subgroup.eq_bot_iff_card X).2
    rw [← card_conjBy X (q : G)⁻¹, ← show Xq = X.conjBy (q : G)⁻¹ from rfl,
      hXqbot]
    simp
  have hXqleD : Xq ≤ h.D := by
    rw [hXqEq]
    exact Subgroup.zpowers_le.mpr hyD
  obtain ⟨v, hNX, _hNDv, _hv, _hvD, _hvinv⟩ :=
    h.normalizer_subgroup_data X hXne hXleD
  obtain ⟨w, hNXq, _hNDw, _hw, _hwD, _hwinv⟩ :=
    h.normalizer_subgroup_data Xq hXqne hXqleD
  have hnormalizerConj :
      (Subgroup.normalizer (X : Set G)).conjBy (q : G)⁻¹ =
        Subgroup.normalizer (Xq : Set G) := by
    simpa [Subgroup.conjBy, Xq] using
      (Subgroup.map_equiv_normalizer_eq X (MulAut.conj (q : G)⁻¹))
  have hNDconj :
      (Subgroup.normalizer (h.D : Set G)).conjBy (q : G)⁻¹ =
        Subgroup.normalizer (h.D : Set G) := by
    calc
      (Subgroup.normalizer (h.D : Set G)).conjBy (q : G)⁻¹ =
          (Subgroup.normalizer (X : Set G)).conjBy (q : G)⁻¹ := by
            rw [hNX]
      _ = Subgroup.normalizer (Xq : Set G) := hnormalizerConj
      _ = Subgroup.normalizer (h.D : Set G) := hNXq
  have hqinvNormND : (q : G)⁻¹ ∈
      Subgroup.normalizer
        ((Subgroup.normalizer (h.D : Set G) : Subgroup G) : Set G) :=
    (conjBy_eq_iff_mem_normalizer
      (Subgroup.normalizer (h.D : Set G)) (q : G)⁻¹).mp hNDconj
  have hqNormND : (q : G) ∈
      Subgroup.normalizer
        ((Subgroup.normalizer (h.D : Set G) : Subgroup G) : Set G) := by
    simpa using (Subgroup.normalizer
      ((Subgroup.normalizer (h.D : Set G) : Subgroup G) : Set G)).inv_mem
        hqinvNormND
  have hqNQ : (q : G) ∈ Subgroup.normalizer (h.Q : Set G) := by
    rw [h.normalizer_Q_eq]
    exact Subgroup.mem_sup_left q.property
  have hqNormNQ : (q : G) ∈
      Subgroup.normalizer
        ((Subgroup.normalizer (h.Q : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hqNQ
  have hqNormInf : (q : G) ∈
      Subgroup.normalizer
        ((Subgroup.normalizer (h.Q : Set G) ⊓
          Subgroup.normalizer (h.D : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hqNormNQ, hqNormND⟩
  have hqND : (q : G) ∈ Subgroup.normalizer (h.D : Set G) := by
    rw [h.normalizer_Q_inf_normalizer_D_eq_D hq] at hqNormInf
    exact hqNormInf
  have hqD : (q : G) ∈ h.D := by
    have hqInf : (q : G) ∈
        Subgroup.normalizer (h.Q : Set G) ⊓
          Subgroup.normalizer (h.D : Set G) := ⟨hqNQ, hqND⟩
    rw [h.normalizer_Q_inf_normalizer_D_eq_D hq] at hqInf
    exact hqInf
  exact hqne (Subgroup.disjoint_def.mp h.Q_disjoint_D q.property hqD)

private theorem BrauerSuzukiWallConclusion.regularNormal_two_structure
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G)
    (R : Subgroup G) (hRnormal : R.Normal)
    (hregular :
      letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
      ∀ a b : ConjugateOrbit h.Q,
        ∃! r : R, (r : G) • a = b) :
    IsPGroup 2 R ∧ ∀ r : R, r ≠ 1 → orderOf r = 2 := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  let : Fintype R := Fintype.ofFinite R
  have hfreeBase : ∀ r : R, (r : G) • base = base → r = 1 := by
    intro r hr
    obtain ⟨s, hs, hsuniq⟩ := hregular base base
    have hrs : r = s := hsuniq r hr
    have hones : (1 : R) = s := hsuniq 1 (by simp)
    exact hrs.trans hones.symm
  let orbitMap : R → Omega := fun r => (r : G) • base
  have horbitBij : Function.Bijective orbitMap := by
    constructor
    · intro r s hrs
      obtain ⟨u, hu, huuniq⟩ := hregular base (orbitMap r)
      have hur : u = r := (huuniq r rfl).symm
      have hus : u = s :=
        (huuniq s (by simpa [orbitMap] using hrs.symm)).symm
      exact hur.symm.trans hus
    · intro A
      obtain ⟨r, hr, _⟩ := hregular base A
      exact ⟨r, hr⟩
  have hRcard : Nat.card R = h.q + 1 := by
    calc
      Nat.card R = Nat.card Omega :=
        Nat.card_congr (Equiv.ofBijective orbitMap horbitBij)
      _ = h.q + 1 := h.orbit_degree
  have htwoDivR : 2 ∣ Nat.card R := by
    rw [hRcard]
    exact h.q_odd.add_one.two_dvd
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) 2 htwoDivR
  have htne : t ≠ 1 := by
    intro ht
    rw [ht, orderOf_one] at htorder
    omega
  let Rstar := {r : R // r ≠ 1}
  let conjR : h.Q → R := fun a =>
    ⟨(a : G) * (t : G) * (a : G)⁻¹,
      hRnormal.conj_mem (t : G) t.property (a : G)⟩
  have hconjRne : ∀ a : h.Q, conjR a ≠ 1 := by
    intro a ha
    apply htne
    apply Subtype.ext
    have haG : (a : G) * (t : G) * (a : G)⁻¹ = 1 :=
      congrArg Subtype.val ha
    have hback := congrArg (fun z : G => (a : G)⁻¹ * z * (a : G)) haG
    simpa [mul_assoc] using hback
  let conjMap : h.Q → Rstar := fun a => ⟨conjR a, hconjRne a⟩
  have hconjMapInj : Function.Injective conjMap := by
    intro a b hab
    have habR : conjR a = conjR b := congrArg Subtype.val hab
    have habG :
        (a : G) * (t : G) * (a : G)⁻¹ =
          (b : G) * (t : G) * (b : G)⁻¹ :=
      congrArg Subtype.val habR
    let z : G := (b : G)⁻¹ * (a : G)
    have hzQ : z ∈ h.Q :=
      h.Q.mul_mem (h.Q.inv_mem b.property) a.property
    have hzcomm : z * (t : G) = (t : G) * z := by
      have hmul := congrArg
        (fun w : G => (b : G)⁻¹ * w * (a : G)) habG
      simpa [z, mul_assoc] using hmul
    have hzbase : z • base = base := by
      apply Subtype.ext
      change h.Q.conjBy z = h.Q
      apply (conjBy_eq_iff_mem_normalizer h.Q z).mpr
      rw [h.normalizer_Q_eq]
      exact Subgroup.mem_sup_left hzQ
    let A : Omega := (t : G) • base
    have hAne : A ≠ base := by
      intro hA
      apply htne
      apply hfreeBase t
      exact hA
    have hzA : z • A = A := by
      calc
        z • A = (z * (t : G)) • base := by simp [A, mul_smul]
        _ = ((t : G) * z) • base := by rw [hzcomm]
        _ = (t : G) • (z • base) := by rw [mul_smul]
        _ = A := by rw [hzbase]
    have hzone : z = 1 := by
      by_contra hz
      have hzNorm : z ∈
          Subgroup.normalizer ((A : Subgroup G) : Set G) := by
        apply (conjBy_eq_iff_mem_normalizer (A : Subgroup G) z).mp
        exact congrArg Subtype.val hzA
      have hAQ := h.fixed_orbit_eq_Q A z hzQ hz hzNorm
      apply hAne
      apply Subtype.ext
      exact hAQ
    apply Subtype.ext
    have hmul := congrArg (fun w : G => (b : G) * w) hzone
    simpa [z, mul_assoc] using hmul
  have hRstarCard : Nat.card Rstar = h.q := by
    change Nat.card {r : R // r ≠ 1} = h.q
    calc
      Nat.card {r : R // r ≠ 1} = Nat.card R - 1 := by
        let : Fintype {r : R // r ≠ 1} := Fintype.ofFinite _
        simpa [Nat.card_eq_fintype_card] using
          (Fintype.card_subtype_compl (fun r : R => r = 1))
      _ = h.q := by rw [hRcard]; omega
  let : Fintype h.Q := Fintype.ofFinite h.Q
  let : Fintype Rstar := Fintype.ofFinite Rstar
  have hconjMapBij : Function.Bijective conjMap :=
    (Fintype.bijective_iff_injective_and_card conjMap).2
      ⟨hconjMapInj, by
        calc
          Fintype.card h.Q = Nat.card h.Q := Nat.card_eq_fintype_card.symm
          _ = h.q := h.Q_card
          _ = Nat.card Rstar := hRstarCard.symm
          _ = Fintype.card Rstar := Nat.card_eq_fintype_card⟩
  have hRorderTwo : ∀ r : R, r ≠ 1 → orderOf r = 2 := by
    intro r hr
    let rstar : Rstar := ⟨r, hr⟩
    obtain ⟨a, ha⟩ := hconjMapBij.2 rstar
    have har : conjR a = r := congrArg Subtype.val ha
    have harG : (a : G) * (t : G) * (a : G)⁻¹ = (r : G) :=
      congrArg Subtype.val har
    have htSq : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp htorder).1
    have htSqG : (t : G) ^ 2 = 1 := by
      exact congrArg Subtype.val htSq
    have hrSq : r ^ 2 = 1 := by
      apply Subtype.ext
      change (r : G) ^ 2 = 1
      rw [← harG]
      calc
        ((a : G) * (t : G) * (a : G)⁻¹) ^ 2 =
            (a : G) * (t : G) ^ 2 * (a : G)⁻¹ := by
              simp only [pow_two]
              group
        _ = 1 := by rw [htSqG]; simp
    exact orderOf_eq_prime hrSq hr
  refine ⟨?_, hRorderTwo⟩
  rw [IsPGroup.iff_orderOf]
  intro r
  by_cases hr : r = 1
  · exact ⟨0, by simp [hr]⟩
  · exact ⟨1, by simpa using hRorderTwo r hr⟩

private theorem eq_one_of_mem_odd_subgroup_of_sq_eq_one_zassenhaus
    {G : Type u} [Group G] [Finite G]
    {D : Subgroup G} (hDodd : Odd (Nat.card D))
    {x : G} (hxD : x ∈ D) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  let xD : D := ⟨x, hxD⟩
  have hxD2 : xD ^ 2 = 1 := by
    apply Subtype.ext
    simpa [xD] using hx2
  have horderTwo : orderOf xD ∣ 2 := orderOf_dvd_of_pow_eq_one hxD2
  have horderCard : orderOf xD ∣ Nat.card D := orderOf_dvd_natCard xD
  have horderOne : orderOf xD = 1 :=
    Nat.eq_one_of_dvd_coprimes
      hDodd.coprime_two_right horderCard horderTwo
  have hxDone : xD = 1 := orderOf_eq_one_iff.mp horderOne
  simpa [xD] using congrArg Subtype.val hxDone

private theorem BrauerSuzukiWallConclusion.no_regular_normal
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) (hq : h.q ≠ 3) :
    letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
    ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
      ∀ a b : ConjugateOrbit h.Q,
        ∃! r : R, (r : G) • a = b := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  let Omega := ConjugateOrbit h.Q
  let base : Omega := conjugateBase h.Q
  let : Fintype Omega := Fintype.ofFinite Omega
  rintro ⟨R, hRnormal, _hRne, hregular⟩
  obtain ⟨hRtwo, hRorderTwo⟩ :=
    h.regularNormal_two_structure R hRnormal hregular
  let orbitMap : R → Omega := fun r => (r : G) • base
  have horbitBij : Function.Bijective orbitMap := by
    constructor
    · intro r s hrs
      obtain ⟨u, hu, huuniq⟩ := hregular base (orbitMap r)
      have hur : u = r := (huuniq r rfl).symm
      have hus : u = s :=
        (huuniq s (by simpa [orbitMap] using hrs.symm)).symm
      exact hur.symm.trans hus
    · intro A
      obtain ⟨r, hr, _⟩ := hregular base A
      exact ⟨r, hr⟩
  have hRcard : Nat.card R = h.q + 1 := by
    calc
      Nat.card R = Nat.card Omega :=
        Nat.card_congr (Equiv.ofBijective orbitMap horbitBij)
      _ = h.q + 1 := h.orbit_degree
  obtain ⟨n, hRpow⟩ := hRtwo.exists_card_eq
  have hqpow : h.q + 1 = 2 ^ n := hRcard.symm.trans hRpow
  have hnTwo : 2 ≤ n := by
    by_contra hn
    have hnle : n ≤ 1 := by omega
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hqpow
    · have hqge := h.three_le_q
      omega
    · have hqge := h.three_le_q
      omega
  obtain ⟨m, hn⟩ := Nat.exists_eq_add_of_le hnTwo
  have hqpowFour : h.q + 1 = 4 * 2 ^ m := by
    calc
      h.q + 1 = 2 ^ n := hqpow
      _ = 2 ^ (2 + m) := by rw [hn]
      _ = 4 * 2 ^ m := by rw [pow_add]; norm_num
  have hhalfOdd : Odd ((h.q - 1) / 2) := by
    refine ⟨2 ^ m - 1, ?_⟩
    have hpowPos : 0 < 2 ^ m := pow_pos (by norm_num) m
    omega
  have hDodd : Odd (Nat.card h.D) := by
    rw [h.D_card]
    exact hhalfOdd
  obtain ⟨u, hND, hu, _huD, huinv, hbaseNe, hDtwo⟩ :=
    h.exists_reflection_two_point_stabilizer hq
  let beta : Omega := u • base
  obtain ⟨r, hrbeta, hrunique⟩ := hregular base beta
  have hrne : r ≠ 1 := by
    intro hr
    apply hbaseNe
    simpa [hr, beta] using hrbeta
  have hrOrderR : orderOf r = 2 := hRorderTwo r hrne
  have hrOrderG : orderOf (r : G) = 2 := by
    simpa [Subgroup.orderOf_coe] using hrOrderR
  have hrInv : IsInvolution (r : G) := by
    have hrdata := orderOf_eq_prime_iff.mp hrOrderG
    exact ⟨hrdata.2, hrdata.1⟩
  have hrSelf : (r : G)⁻¹ = (r : G) := by
    have hrr : (r : G) * (r : G) = 1 := by
      simpa [pow_two] using hrInv.2
    exact inv_eq_of_mul_eq_one_right hrr
  have hrbetaBack : (r : G) • beta = base := by
    calc
      (r : G) • beta = (r : G) • ((r : G) • base) := by rw [hrbeta]
      _ = ((r : G) * (r : G)) • base := by rw [mul_smul]
      _ = base := by
        have hrr : (r : G) * (r : G) = 1 := by
          simpa [pow_two] using hrInv.2
        rw [hrr, one_smul]
  have hDfixBase : ∀ d : G, d ∈ h.D → d • base = base := by
    intro d hd
    apply MulAction.mem_stabilizer_iff.mp
    have hdTwo : d ∈
        MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta := by
      rw [hDtwo]
      exact hd
    exact hdTwo.1
  have hDfixBeta : ∀ d : G, d ∈ h.D → d • beta = beta := by
    intro d hd
    apply MulAction.mem_stabilizer_iff.mp
    have hdTwo : d ∈
        MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta := by
      rw [hDtwo]
      exact hd
    exact hdTwo.2
  have hDconjRle : h.D.conjBy (r : G) ≤ h.D := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨d, hd, rfl⟩
    have hfixBase :
        ((r : G) * d * (r : G)⁻¹) • base = base := by
      calc
        ((r : G) * d * (r : G)⁻¹) • base =
            (r : G) • (d • ((r : G)⁻¹ • base)) := by
              simp [mul_smul, mul_assoc]
        _ = (r : G) • (d • beta) := by rw [hrSelf, hrbeta]
        _ = (r : G) • beta := by rw [hDfixBeta d hd]
        _ = base := hrbetaBack
    have hfixBeta :
        ((r : G) * d * (r : G)⁻¹) • beta = beta := by
      calc
        ((r : G) * d * (r : G)⁻¹) • beta =
            (r : G) • (d • ((r : G)⁻¹ • beta)) := by
              simp [mul_smul, mul_assoc]
        _ = (r : G) • (d • base) := by rw [hrSelf, hrbetaBack]
        _ = (r : G) • base := by rw [hDfixBase d hd]
        _ = beta := hrbeta
    have hzTwo : (r : G) * d * (r : G)⁻¹ ∈
        MulAction.stabilizer G base ⊓ MulAction.stabilizer G beta :=
      ⟨MulAction.mem_stabilizer_iff.mpr hfixBase,
        MulAction.mem_stabilizer_iff.mpr hfixBeta⟩
    rw [hDtwo] at hzTwo
    exact hzTwo
  have hDconjReq : h.D.conjBy (r : G) = h.D := by
    apply Subgroup.eq_of_le_of_card_ge hDconjRle
    rw [card_conjBy]
  have hrND : (r : G) ∈ Subgroup.normalizer (h.D : Set G) :=
    (conjBy_eq_iff_mem_normalizer h.D (r : G)).mp hDconjReq
  have hrNotD : (r : G) ∉ h.D := by
    intro hrD
    apply hbaseNe
    calc
      base = (r : G) • base := (hDfixBase (r : G) hrD).symm
      _ = beta := hrbeta
  let Z : Subgroup G := Subgroup.zpowers u
  have hZleND : Z ≤ Subgroup.normalizer (h.D : Set G) := by
    rw [hND]
    exact le_sup_right
  have hrSup : (r : G) ∈ h.D ⊔ Z := by
    rw [← hND]
    exact hrND
  have hrProd : (r : G) ∈ (h.D : Set G) * (Z : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left h.D Z hZleND]
    exact hrSup
  rcases hrProd with ⟨d, hdD, z, hzZ, hdz⟩
  have hzu : z = u := by
    rcases eq_one_or_eq_of_mem_zpowers_involution_zassenhaus hu hzZ with
      hzone | hzu
    · exfalso
      apply hrNotD
      have hrEqD : (r : G) = d := by
        simpa [hzone] using hdz.symm
      rw [hrEqD]
      exact hdD
    · exact hzu
  have hrdu : (r : G) = d * u := by
    simpa [hzu] using hdz.symm
  have hrCentralizesD : ∀ e : G, e ∈ h.D →
      (r : G) * e * (r : G)⁻¹ = e := by
    intro e heD
    let er : R :=
      ⟨e * (r : G) * e⁻¹,
        hRnormal.conj_mem (r : G) r.property e⟩
    have herMap : (er : G) • base = beta := by
      calc
        (er : G) • base = e • ((r : G) • (e⁻¹ • base)) := by
          simp [er, mul_smul, mul_assoc]
        _ = e • ((r : G) • base) := by
          rw [hDfixBase e⁻¹ (h.D.inv_mem heD)]
        _ = e • beta := by rw [hrbeta]
        _ = beta := hDfixBeta e heD
    have herEq : er = r := hrunique er herMap
    have herG : e * (r : G) * e⁻¹ = (r : G) :=
      congrArg Subtype.val herEq
    have herComm : e * (r : G) = (r : G) * e := by
      have hmul := congrArg (fun w : G => w * e) herG
      simpa [mul_assoc] using hmul
    calc
      (r : G) * e * (r : G)⁻¹ =
          e * (r : G) * (r : G)⁻¹ := by rw [herComm]
      _ = e := by group
  have hrInvertsD : ∀ e : G, e ∈ h.D →
      (r : G) * e * (r : G)⁻¹ = e⁻¹ := by
    intro e heD
    have hdeInv : d * e⁻¹ = e⁻¹ * d := by
      let : IsMulCommutative h.D := h.D_commutative
      exact congrArg Subtype.val
        (mul_comm' (⟨d, hdD⟩ : h.D)
          (⟨e⁻¹, h.D.inv_mem heD⟩ : h.D))
    calc
      (r : G) * e * (r : G)⁻¹ =
          d * (u * e * u⁻¹) * d⁻¹ := by rw [hrdu]; group
      _ = d * e⁻¹ * d⁻¹ := by rw [huinv e heD]
      _ = e⁻¹ := by rw [hdeInv]; group
  have hDbot : h.D = ⊥ := by
    apply le_bot_iff.mp
    intro e heD
    rw [Subgroup.mem_bot]
    have heInv : e = e⁻¹ :=
      (hrCentralizesD e heD).symm.trans (hrInvertsD e heD)
    have heSq : e ^ 2 = 1 := by
      calc
        e ^ 2 = e * e := pow_two e
        _ = e * e⁻¹ := congrArg (fun x : G => e * x) heInv
        _ = 1 := mul_inv_cancel e
    exact eq_one_of_mem_odd_subgroup_of_sq_eq_one_zassenhaus
      hDodd heD heSq
  exact h.D_ne_bot_of_q_ne_three hq hDbot

private theorem card_eq_descFactorial_three_of_sharp_three_transitive
    {G : Type u} {Omega : Type u}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (hthree : 2 < Fintype.card Omega)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c') :
    Nat.card G = (Fintype.card Omega).descFactorial 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp hthree
  let source : Fin 3 ↪ Omega :=
    ⟨![a, b, c], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let orbit : G → (Fin 3 ↪ Omega) := fun g =>
    source.trans (MulAction.toPermHom G Omega g).toEmbedding
  have horbitInjective : Function.Injective orbit := by
    intro g k hgk
    have hga : g • a = k • a := by
      have h := congrArg (fun e : Fin 3 ↪ Omega => e 0) hgk
      change g • a = k • a at h
      exact h
    have hgb : g • b = k • b := by
      have h := congrArg (fun e : Fin 3 ↪ Omega => e 1) hgk
      change g • b = k • b at h
      exact h
    have hgc : g • c = k • c := by
      have h := congrArg (fun e : Fin 3 ↪ Omega => e 2) hgk
      change g • c = k • c at h
      exact h
    have hgab : g • a ≠ g • b := by
      intro heq
      exact hab ((MulAction.toPerm g).injective heq)
    have hgac : g • a ≠ g • c := by
      intro heq
      exact hac ((MulAction.toPerm g).injective heq)
    have hgbc : g • b ≠ g • c := by
      intro heq
      exact hbc ((MulAction.toPerm g).injective heq)
    have hu := hsharp a b c (g • a) (g • b) (g • c)
      hab hac hbc hgab hgac hgbc
    exact hu.unique ⟨rfl, rfl, rfl⟩ ⟨hga.symm, hgb.symm, hgc.symm⟩
  have horbitSurjective : Function.Surjective orbit := by
    intro target
    have h01 : target 0 ≠ target 1 := by
      intro h
      exact Fin.zero_ne_one (target.injective h)
    have h02 : target 0 ≠ target 2 := by
      intro h
      exact (by decide : (0 : Fin 3) ≠ 2) (target.injective h)
    have h12 : target 1 ≠ target 2 := by
      intro h
      exact (by decide : (1 : Fin 3) ≠ 2) (target.injective h)
    obtain ⟨g, hg, _huniq⟩ :=
      hsharp a b c (target 0) (target 1) (target 2)
        hab hac hbc h01 h02 h12
    refine ⟨g, ?_⟩
    ext i
    fin_cases i
    · change g • a = target 0
      exact hg.1
    · change g • b = target 1
      exact hg.2.1
    · change g • c = target 2
      exact hg.2.2
  calc
    Nat.card G = Nat.card (Fin 3 ↪ Omega) :=
      Nat.card_congr
        (Equiv.ofBijective orbit ⟨horbitInjective, horbitSurjective⟩)
    _ = Fintype.card (Fin 3 ↪ Omega) := Nat.card_eq_fintype_card
    _ = (Fintype.card Omega).descFactorial 3 := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]

/-- The Brauer--Suzuki--Wall structural conclusion is a `D`-group. -/
public theorem BrauerSuzukiWallConclusion.isDGroup
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallConclusion G) : IsDGroup G := by
  classical
  by_cases hq : h.q = 3
  · have eA4 := h.iso_alternatingGroup_four_of_q_eq_three hq
    have ePSL : Nonempty (G ≃* PSL2 (ZMod 3)) :=
      ⟨eA4.some.trans psl2_three_equiv_alternatingGroup.symm⟩
    exact isDGroup_of_iso_PSL2_three
      (h.pPrimeCore_eq_bot_of_q_eq_three hq)
      (h.hasDihedralSylowTwo_of_q_eq_three hq) ePSL
  · let : MulAction G (Subgroup G) :=
      MulAction.compHom _ MulAut.conj
    let Omega := ConjugateOrbit h.Q
    let : Fintype Omega := Fintype.ofFinite Omega
    let : FaithfulSMul G Omega := h.orbit_faithful
    have hdegree : Fintype.card Omega = h.q + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact h.orbit_degree
    obtain ⟨p, f, hp, hf, hqpow, hcases⟩ :=
      BenderSuzuki.External.huppert_blackburn_XI_11_16_zassenhaus_classification.{u, u, 0}
        h.q ((h.q - 1) / 2)
        hdegree (by simpa [mul_assoc] using h.group_card_factorized)
        h.orbit_two_transitive
        (h.at_most_two_fixed_points hq) (h.no_regular_normal hq)
    have hpNeTwo : p ≠ 2 := by
      intro hpTwo
      have hqEven : Even h.q := by
        rw [hqpow, hpTwo]
        exact Even.pow_of_ne_zero even_two hf.ne'
      exact (Nat.not_even_iff_odd.mpr h.q_odd) hqEven
    have hpOdd : Odd p := hp.odd_of_ne_two hpNeTwo
    have hhalfDouble : 2 * ((h.q - 1) / 2) = h.q - 1 := by
      apply Nat.mul_div_cancel'
      exact (Nat.Odd.sub_odd h.q_odd odd_one).two_dvd
    have hmainPos :
        0 < (h.q + 1) * (h.q * ((h.q - 1) / 2)) := by
      have hqge := h.three_le_q
      have hhalfPos : 0 < (h.q - 1) / 2 := by omega
      exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hhalfPos)
    rcases hcases with hPGL | hPSL | hsharp | hSuzuki
    · rcases hPGL with
        ⟨K, hKfield, hKfinite, hKcard, ⟨eG⟩⟩
      let : Field K := hKfield
      let : Finite K := hKfinite
      have hfactor : h.q ^ 2 - 1 = (h.q - 1) * (h.q + 1) := by
        simpa [mul_comm] using (Nat.sq_sub_sq h.q 1)
      have hcardFull : Nat.card G =
          2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) := by
        calc
          Nat.card G = Nat.card (PGL2 K) := Nat.card_congr eG.toEquiv
          _ = Nat.card K * (Nat.card K ^ 2 - 1) := pgl2_card_formula K
          _ = h.q * (h.q ^ 2 - 1) := by rw [hKcard]
          _ = h.q * ((h.q - 1) * (h.q + 1)) := by rw [hfactor]
          _ = h.q * ((2 * ((h.q - 1) / 2)) * (h.q + 1)) := by
            rw [hhalfDouble]
          _ = 2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) := by
            ring
      have hcollapse :
          (h.q + 1) * (h.q * ((h.q - 1) / 2)) =
            2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) :=
        h.group_card_factorized.symm.trans hcardFull
      omega
    · rcases hPSL with
        ⟨_hpOdd, K, hKfield, hKfinite, hKcard, ⟨eG⟩⟩
      let : Field K := hKfield
      let : Finite K := hKfinite
      have hKprime : IsOddPrimePower (Nat.card K) :=
        ⟨p, f, hp, hpOdd, hf, hKcard.trans hqpow⟩
      have hSylowD : HasDihedralSylowTwo G :=
        hasDihedralSylowTwo_of_mulEquiv eG
          (psl2_odd_hasDihedralSylowTwo_model K hKprime)
      have hKgt : 3 < Nat.card K := by
        rw [hKcard]
        have hqge := h.three_le_q
        omega
      rcases BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a K with
        ⟨_hproj, _rho, _iota, _hrho, _hiota, _hiotaApply,
          _hrhoApply, _hiotaNormal, _hiotaIndex, _hsharp,
          hlarge, _hsmallTwo, _hsmallThree⟩
      have hsimplePSL : IsSimpleGroup (PSL2 K) :=
        (hlarge hKgt).1
      let : IsSimpleGroup (PSL2 K) := hsimplePSL
      let : IsSimpleGroup G := eG.isSimpleGroup
      have hGeven : 2 ∣ Nat.card G := by
        rw [h.group_card_factorized]
        exact dvd_mul_of_dvd_left (h.q_odd.add_one.two_dvd) _
      have hcore : pPrimeCore 2 G = ⊥ :=
        pPrimeCore_eq_bot_of_simple_of_even hGeven
      have hSylow : HasCyclicOrDihedralSylowTwo G := by
        intro S
        exact Or.inr (hSylowD S)
      have hKprimeLift :
          IsOddPrimePower (Nat.card (ULift.{u} K)) := by
        simpa using hKprime
      refine IsDGroup.quotientHasLinearNormalSubgroup
        hSylow (ULift.{u} K) hKprimeLift
        (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) inferInstance (by simp) ?_
      left
      refine ⟨Subgroup.topEquiv.trans ?_⟩
      exact ((QuotientGroup.quotientMulEquivOfEq (G := G) hcore).trans
        (QuotientGroup.quotientBot (G := G))).trans
          (eG.trans (psl2ULiftEquiv (R := K)).symm)
    · have hsharpCard :
          Nat.card G = (Fintype.card Omega).descFactorial 3 :=
        card_eq_descFactorial_three_of_sharp_three_transitive
          (by
            have hqge := h.three_le_q
            rw [hdegree]
            omega)
          hsharp.2.2
      have hdesc :
          (Fintype.card Omega).descFactorial 3 =
            (h.q + 1) * h.q * (h.q - 1) := by
        rw [hdegree]
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one]
        have hsubOne : h.q + 1 - 1 = h.q := by omega
        have hsubTwo : h.q + 1 - 2 = h.q - 1 := by omega
        rw [hsubOne, hsubTwo]
        simp only [Nat.sub_zero]
        ac_rfl
      have hcardFull : Nat.card G =
          2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) := by
        calc
          Nat.card G = (h.q + 1) * h.q * (h.q - 1) :=
            hsharpCard.trans hdesc
          _ = (h.q + 1) * h.q *
              (2 * ((h.q - 1) / 2)) := by rw [hhalfDouble]
          _ = 2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) := by
            ring
      have hcollapse :
          (h.q + 1) * (h.q * ((h.q - 1) / 2)) =
            2 * ((h.q + 1) * (h.q * ((h.q - 1) / 2))) :=
        h.group_card_factorized.symm.trans hcardFull
      omega
    · exact (hpNeTwo hSuzuki.1).elim

end CFSG.GorensteinWalter
