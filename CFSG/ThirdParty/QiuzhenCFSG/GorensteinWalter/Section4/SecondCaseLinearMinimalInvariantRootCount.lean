module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylowUnique
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearMinimalInvariantPuncturedCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearTwoRootDisjointFamilyCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Root-Sylow count for minimal invariant subgroups

A family of nontrivial minimal `X`-invariant subgroups of `P × E` whose
orders divide the defining-characteristic field order injects, after
projection to `PSL₂`, into the two root Sylows normalized by a nonidentity
image of `X`.  The punctured-cardinality estimate then gives the
`(q - 1) / p` bound.
-/

noncomputable section
namespace CFSG.GorensteinWalter

open scoped Pointwise MatrixGroups

universe u

/-- The minimal-invariant family in a central product projects into at most
 two root Sylows, and therefore has cardinality at most `(q - 1) / p`. -/
public theorem secondCase_linear_minimalInvariant_root_count
    {G : Type u} [Group G] [Finite G]
    (PE E X : Subgroup G) (hElePE : E ≤ PE)
    {p q r f : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hpodd : Odd p) (hqodd : Odd q)
    (K : Type u) [Field K] [Finite K]
    (hKcard : Nat.card K = r ^ f) (hqK : q = Nat.card K)
    (eE : E ≃* PSL2 K)
    (π : PE →* PSL2 K) (hXlePE : X ≤ PE)
    (hπXinj : Function.Injective (π.comp (Subgroup.inclusion hXlePE)))
    (hπE : ∀ z : E,
      π ⟨z, hElePE z.2⟩ = eE z)
    (hXcard : Nat.card X = p)
    (hWleE : ∀ W : Subgroup G,
      W ∈ MinimalXInvariantFamily PE q X → W ≤ E)
    (hnotcent : ∀ W : Subgroup G,
      W ∈ MinimalXInvariantFamily PE q X →
        ¬ X ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card (MinimalXInvariantFamily PE q X) ≤ (q - 1) / p := by
  classical
  let Fam := MinimalXInvariantFamily PE q X
  have hFamSpec : ∀ W : Fam,
      W.1 ≤ PE ∧ Nat.card W.1 ∣ q ∧ MinimalXInvariant X W.1 := by
    intro W
    exact W.2
  let iX : X →* PE := Subgroup.inclusion hXlePE
  have hXgt : 1 < Nat.card X := by
    rw [hXcard]
    exact (Fact.out : Nat.Prime p).one_lt
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hXgt
  obtain ⟨a, ha⟩ : ∃ a : X, a ≠ 1 := exists_ne 1
  let g : PSL2 K := π (iX a)
  have hg : g ≠ 1 := by
    intro hg1
    apply ha
    apply hπXinj
    simpa [g] using hg1
  let WE : Fam → Subgroup E := fun W => W.1.subgroupOf E
  let WB : Fam → Subgroup (PSL2 K) := fun W => (WE W).map eE.toMonoidHom
  have hWEcard : ∀ W : Fam, Nat.card (WE W) = Nat.card W.1 := by
    intro W
    calc
      Nat.card (WE W) = Nat.card ((WE W).map E.subtype) :=
        (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ = Nat.card (W.1 ⊓ E : Subgroup G) := by
        dsimp [WE]
        rw [Subgroup.subgroupOf_map_subtype]
      _ = Nat.card W.1 := by rw [inf_eq_left.mpr (hWleE W.1 W.2)]
  have hWBcard : ∀ W : Fam, Nat.card (WB W) = Nat.card W.1 := by
    intro W
    dsimp [WB]
    rw [Subgroup.card_map_of_injective eE.injective, hWEcard]
  have hWBp : ∀ W : Fam, IsPGroup r (WB W) := by
    intro W
    rw [IsPGroup.iff_orderOf]
    intro z
    have hordWB : orderOf (z : PSL2 K) ∣ Nat.card (WB W) :=
      Subgroup.orderOf_dvd_natCard (WB W) z.2
    have hWBq : Nat.card (WB W) ∣ q := by
      rw [hWBcard]
      exact (hFamSpec W).2.1
    have hordpow : orderOf (z : PSL2 K) ∣ r ^ f := by
      rw [← hKcard, ← hqK]
      exact hordWB.trans hWBq
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime r)).mp hordpow with
      ⟨k, hk, hord⟩
    refine ⟨k, ?_⟩
    simpa only [Subgroup.orderOf_coe] using hord
  have hRootExists : ∀ W : Fam, ∃ S : Sylow r (PSL2 K),
      WB W ≤ (S : Subgroup (PSL2 K)) := by
    intro W
    exact (hWBp W).exists_le_sylow
  let root0 : Fam → Sylow r (PSL2 K) := fun W => Classical.choose (hRootExists W)
  have hroot0 : ∀ W : Fam, WB W ≤ (root0 W : Subgroup (PSL2 K)) := by
    intro W
    exact Classical.choose_spec (hRootExists W)
  have hWBmap : ∀ W : Fam,
      (WB W).map (MulAut.conj g).toMonoidHom = WB W := by
    intro W
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
      rcases Subgroup.mem_map.mp hz with ⟨w, hw, hzw⟩
      have hwW : (w : G) ∈ W.1 := Subgroup.mem_subgroupOf.mp hw
      have hconjW : (a : G) * (w : G) * (a : G)⁻¹ ∈ W.1 :=
        (hFamSpec W).2.2.2.1 (a : G) a.2 (w : G) hwW
      have hconjE : (a : G) * (w : G) * (a : G)⁻¹ ∈ E :=
        hWleE W.1 W.2 hconjW
      let v : E := ⟨(a : G) * (w : G) * (a : G)⁻¹, hconjE⟩
      refine Subgroup.mem_map.mpr ⟨v, Subgroup.mem_subgroupOf.mpr hconjW, ?_⟩
      have hprod : iX a * ⟨(w : G), hElePE w.2⟩ * (iX a)⁻¹ =
          (⟨(v : G), hElePE v.2⟩ : PE) := by
        apply Subtype.ext
        rfl
      calc
        eE v = π ⟨v, hElePE v.2⟩ := (hπE v).symm
        _ = π (iX a * ⟨(w : G), hElePE w.2⟩ * (iX a)⁻¹) := by rw [hprod]
        _ = π (iX a) * π ⟨(w : G), hElePE w.2⟩ * (π (iX a))⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        _ = g * eE w * g⁻¹ := by rw [hπE w]
        _ = g * z * g⁻¹ := by
          exact congrArg (fun u : PSL2 K => g * u * g⁻¹) hzw
    · exact (Subgroup.card_map_of_injective
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).ge
  have hWBne : ∀ W : Fam, WB W ≠ ⊥ := by
    intro W hbot
    have hcard1 : Nat.card (WB W) = 1 := by rw [hbot]; simp
    have hWcard1 : Nat.card W.1 = 1 := by rwa [hWBcard W] at hcard1
    exact (hFamSpec W).2.2.1 (Subgroup.card_eq_one.mp hWcard1)
  have hconjmap : (MulAut.conj g).toMonoidHom =
      MulDistribMulAction.toMonoidHom (PSL2 K) (MulAut.conj g) := by
    ext z
    rfl
  have hrootNorm : ∀ W : Fam,
      g ∈ Subgroup.normalizer
        ((root0 W : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
    intro W
    let T : Sylow r (PSL2 K) := g • root0 W
    have hWBleT : WB W ≤ (T : Subgroup (PSL2 K)) := by
      have hmaple : (WB W).map (MulAut.conj g).toMonoidHom ≤
          (root0 W : Subgroup (PSL2 K)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (hroot0 W)
      rw [hWBmap W] at hmaple
      rw [hconjmap] at hmaple
      simpa [T, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] using hmaple
    have hWBgt : 1 < Nat.card (WB W) :=
      (Subgroup.one_lt_card_iff_ne_bot (WB W)).2 (hWBne W)
    let : Nontrivial (WB W) := Finite.one_lt_card_iff_nontrivial.mp hWBgt
    obtain ⟨b, hb⟩ : ∃ b : WB W, b ≠ 1 := exists_ne 1
    have hbG : (b : PSL2 K) ≠ 1 := by
      intro hb1
      exact hb (Subtype.ext hb1)
    have hST : root0 W = T :=
      psl2_sylow_eq_of_mem_nontrivial K hKcard (root0 W) T (b : PSL2 K)
        (hroot0 W b.2) hbG (hWBleT b.2)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hTS := congrArg
      (fun S : Sylow r (PSL2 K) => (S : Subgroup (PSL2 K))) hST.symm
    rw [Sylow.coe_subgroup_smul] at hTS
    exact hTS
  let Roots := {S : Sylow r (PSL2 K) //
    g ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))}
  let root : Fam → Roots := fun W => ⟨root0 W, hrootNorm W⟩
  have hRoots : Nat.card Roots ≤ 2 :=
    psl2_normalized_rootSylow_card_le_two K hKcard g hg
  let RootG : Roots → Subgroup G := fun S =>
    ((S.1 : Subgroup (PSL2 K)).map eE.symm.toMonoidHom).map E.subtype
  have hWleRoot : ∀ W : Fam, W.1 ≤ RootG (root W) := by
    intro W z hz
    let zE : E := ⟨z, hWleE W.1 W.2 hz⟩
    have hzWB : eE zE ∈ WB W := by
      exact Subgroup.mem_map.mpr
        ⟨zE, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    have hzS : eE zE ∈ (root0 W : Subgroup (PSL2 K)) := hroot0 W hzWB
    refine Subgroup.mem_map.mpr ⟨eE.symm (eE zE), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨eE zE, hzS, rfl⟩
    · simp [zE]
  have hdisj : ∀ i j : Fam, i ≠ j → ∀ z : G,
      z ∈ i.1 → z ∈ j.1 → z = 1 := by
    intro i j hij z hzi hzj
    let V : Subgroup G := i.1 ⊓ j.1
    have hVinv : ∀ x : G, x ∈ X → ∀ v : G, v ∈ V →
        x * v * x⁻¹ ∈ V := by
      intro x hx v hv
      exact ⟨(hFamSpec i).2.2.2.1 x hx v hv.1,
        (hFamSpec j).2.2.2.1 x hx v hv.2⟩
    rcases (hFamSpec i).2.2.2.2 V inf_le_left hVinv with hVbot | hVi
    · have hzV : z ∈ V := ⟨hzi, hzj⟩
      rw [hVbot] at hzV
      exact Subgroup.mem_bot.mp hzV
    · have hijle : i.1 ≤ j.1 := by rw [← hVi]; exact inf_le_right
      rcases (hFamSpec j).2.2.2.2 i.1 hijle
          (hFamSpec i).2.2.2.1 with hibot | hijeq
      · exact False.elim ((hFamSpec i).2.2.1 (by simpa using hibot))
      · exact False.elim (hij (Subtype.ext hijeq))
  have hsize : ∀ W : Fam,
      2 * p ≤ Nat.card {z : W.1 // (z : G) ≠ 1} := by
    intro W
    have hWodd : Odd (Nat.card W.1) :=
      Odd.of_dvd_nat hqodd (hFamSpec W).2.1
    exact secondCase_linear_minimalInvariant_punctured_card
      X W.1 hXcard hpodd hWodd (hFamSpec W).2.2 (hnotcent W.1 W.2)
  have hRootCard : ∀ S : Roots, Nat.card (RootG S) = q := by
    intro S
    calc
      Nat.card (RootG S) =
          Nat.card ((S.1 : Subgroup (PSL2 K)).map eE.symm.toMonoidHom) := by
        dsimp [RootG]
        rw [Subgroup.card_map_of_injective E.subtype_injective]
      _ = Nat.card (S.1 : Subgroup (PSL2 K)) :=
        Subgroup.card_map_of_injective eE.symm.injective
      _ = Nat.card
          (psl2UpperUnipotentSylow K hKcard : Subgroup (PSL2 K)) :=
        Nat.card_congr (Sylow.equiv S.1 (psl2UpperUnipotentSylow K hKcard)).toEquiv
      _ = Nat.card (psl2UpperUnipotentSubgroup K) := by
        rw [psl2UpperUnipotentSylow_coe]
      _ = Nat.card K := psl2UpperUnipotentSubgroup_card K
      _ = q := hqK.symm
  exact secondCase_linear_twoRoot_disjoint_family_count
    (fun W : Fam => W.1) RootG root p q (Fact.out : Nat.Prime p).pos
      hWleRoot hdisj hsize hRoots hRootCard

end CFSG.GorensteinWalter
