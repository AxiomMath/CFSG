module

import CFSG.GroupTheory.PerfectSylowInversion
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y1

theorem exists_reflection {A : Subgroup G} (hA : A ∈ partTwoF G) {B : Subgroup G}
    (hBA : IsHyperplane A B)
    {Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))} (hYc : CFSG.IsComponent Yc)
    {a : G} (haA : a ∈ A) (haB : a ∉ B)
    (haY : a ∈ (Yc.comap (QuotientGroup.mk'
      (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
        (Subgroup.centralizer (B : Set G)).subtype)
    (hBY : (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ⊓ Yc = ⊥) :
    ∃ s ∈ Subgroup.normalizer (A : Set G), s ∈ Subgroup.centralizer (B : Set G) ∧
      s * a * s⁻¹ = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  let N : Subgroup C := CFSG.pPrimeCore 3 C
  let π : C →* C ⧸ N := QuotientGroup.mk' N
  let A' : Subgroup C := A.subgroupOf C
  let B' : Subgroup C := B.subgroupOf C
  let At : Subgroup (C ⧸ N) := A'.map π
  let Bt : Subgroup (C ⧸ N) := B'.map π
  have hCdef : C = Subgroup.centralizer (B : Set G) := rfl
  have hNdef : N = CFSG.pPrimeCore 3 C := rfl
  have hπdef : π = QuotientGroup.mk' N := rfl
  have hA'def : A' = A.subgroupOf C := rfl
  have hB'def : B' = B.subgroupOf C := rfl
  have hAtdef : At = A'.map π := rfl
  have hBtdef : Bt = B'.map π := rfl
  haveI hNnormal : N.Normal := by
    rw [hNdef]
    exact CFSG.pPrimeCore_normal
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hNdef]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  rw [Subgroup.mem_map] at haY
  obtain ⟨aC, haCmem, haCval⟩ := haY
  have haCval' : (aC : G) = a := haCval
  have haC : a ∈ C := haCval' ▸ aC.2
  have haYc : π aC ∈ Yc := haCmem
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hAC : A ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA.1 hb⟩ ⟨x, hx⟩)
  have hA'3 : IsPGroup 3 A' := by
    have h := (hAab.subgroupOf C).isPGroup
    simpa [hA'def] using h
  have hBA' : IsHyperplane A' B' := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hBA.1 (Subgroup.mem_subgroupOf.mp hx)
    · have hA'c : Nat.card A' = Nat.card A := by
        rw [hA'def]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
      have hB'c : Nat.card B' = Nat.card B := by
        rw [hB'def]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBA.1.trans hAC)).toEquiv
      rw [hA'c, hB'c, hBA.2]
  have haC_A' : aC ∈ A' := by
    rw [hA'def, Subgroup.mem_subgroupOf, haCval']
    exact haA
  have haC_notB' : aC ∉ B' := by
    rw [hB'def, Subgroup.mem_subgroupOf, haCval']
    exact haB
  have hA'eq : A' = B' ⊔ Subgroup.zpowers aC :=
    (CFSG.RankThree.PartTwo.Sec14.Item148HJ.sup_zpowers_eq_of_isHyperplane hBA'
      haC_A' haC_notB').symm
  have hAtilde_eq : At = Bt ⊔ Subgroup.zpowers (π aC) := by
    rw [hAtdef, hA'eq, Subgroup.map_sup, MonoidHom.map_zpowers, hBtdef]
  have hBtilde_central : Bt ≤ Subgroup.center (C ⧸ N) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N z
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp m.2 (b : G)
      (Subgroup.mem_subgroupOf.mp hb)).symm
  have hBnorm : Bt.Normal := Subgroup.normal_of_le_center hBtilde_central
  have hBY' : Bt ⊓ Yc = ⊥ := by
    simpa [hBtdef, hB'def, hNdef, hCdef, hπdef] using hBY
  have hR1 : ∀ y ∈ Yc, y * π aC = π aC * y → y ^ 3 = 1 →
      y ∈ Subgroup.zpowers (π aC) := by
    intro y hyY hycomm hy3
    have hAtelem : CFSG.Assembly.IsElemAbelian 3 At :=
      (hAab.subgroupOf C).map π
    have hcommA : ∀ e ∈ At, e * y = y * e := by
      intro e he
      rw [hAtilde_eq] at he
      obtain ⟨b, hb, z, hz, rfl⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := Bt)
          (t := Subgroup.zpowers (π aC))).mp he
      have hbcomm : b * y = y * b :=
        (Subgroup.mem_center_iff.mp (hBtilde_central hb) y).symm
      have hzcomm : z * y = y * z := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (((commute_iff_eq _ _).mpr hycomm.symm).zpow_left k).eq
      calc (b * z) * y = b * (z * y) := by group
        _ = b * (y * z) := by rw [hzcomm]
        _ = (b * y) * z := by group
        _ = (y * b) * z := by rw [hbcomm]
        _ = y * (b * z) := by group
    set E : Subgroup (C ⧸ N) := At ⊔ Subgroup.zpowers y with hEdef
    have hE : CFSG.Assembly.IsElemAbelian 3 E := by
      rw [hEdef]
      exact isElemAbelian_sup_zpowers hAtelem hy3 hcommA
    obtain ⟨S, hA'S, hSmap, hS_elem, hScard⟩ :=
      Sylow155T51.exists_elemAbelian_lift_le N hN3 hA'3 hE (by
        rw [hEdef, ← hAtdef]
        exact le_sup_left)
    have hA_le_S : A ≤ S.map C.subtype := by
      intro x hx
      exact ⟨⟨x, hAC hx⟩, hA'S (show (⟨x, hAC hx⟩ : C) ∈ A' from hx), rfl⟩
    have hSmapA : S.map C.subtype = A :=
      hA.2.1 (S.map C.subtype) (hS_elem.map C.subtype) hA_le_S
    have hScardA : Nat.card S = Nat.card A := by
      rw [← hSmapA, Subgroup.card_map_of_injective C.subtype_injective]
    have hA'card : Nat.card A' = Nat.card A := by
      rw [hA'def]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
    have hSeq : S = A' :=
      (Subgroup.eq_of_le_of_card_ge hA'S (by rw [hScardA, hA'card])).symm
    have hEeq : E = At := by
      rw [← hSmap, hSeq, hAtdef]
    have hyA : y ∈ At := by
      rw [← hEeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rw [hAtilde_eq] at hyA
    obtain ⟨b, hb, z, hz, hbz⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Bt)
        (t := Subgroup.zpowers (π aC))).mp hyA
    have hb_eq : b = y * z⁻¹ := by
      rw [← hbz]
      group
    have hbY : b ∈ Yc := by
      rw [hb_eq]
      exact Yc.mul_mem hyY (Yc.inv_mem ((Subgroup.zpowers_le.mpr haYc) hz))
    have hbBot : b ∈ (⊥ : Subgroup (C ⧸ N)) := by
      have h : b ∈ Bt ⊓ Yc := ⟨hb, hbY⟩
      rwa [hBY'] at h
    have hb1 : b = 1 := by simpa using hbBot
    rw [hb1, one_mul] at hbz
    rw [← hbz]
    exact hz
  have haCpow : aC ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, haCval']
    exact hAab.2 a haA
  have hpow3 : (π aC) ^ 3 = 1 := by
    rw [← map_pow, haCpow, map_one]
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp A'.subtype) :=
    Sylow155T51.injective_mk_comp_subtype N hN3 hA'3
  have hne : π aC ≠ 1 := by
    intro h
    have h1 : (⟨aC, haC_A'⟩ : A') = ⟨1, A'.one_mem⟩ := by
      apply hinj
      change π aC = π (1 : C)
      rw [map_one]
      exact h
    have haC1 : aC = 1 := congrArg Subtype.val h1
    have ha1 : a = 1 := by
      rw [← haCval', haC1]
      rfl
    exact haB (by rw [ha1]; exact B.one_mem)
  have hxord : orderOf (π aC) = 3 := orderOf_eq_prime hpow3 hne
  obtain ⟨r, hrY, hr_inv⟩ :=
    CFSG.GroupTheory.exists_conj_eq_inv_of_isPerfect hYc.1.1 haYc hxord hR1
  have hrB : r ∈ Subgroup.normalizer (Bt : Set (C ⧸ N)) := by
    haveI : Bt.Normal := hBnorm
    exact Subgroup.le_normalizer_of_normal (H := Bt) (K := ⊤) (Subgroup.mem_top r)
  have hrZ : r ∈ Subgroup.normalizer (Subgroup.zpowers (π aC) : Set (C ⧸ N)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (r * π aC * r⁻¹) = Subgroup.zpowers (π aC)
    rw [hr_inv, Subgroup.zpowers_inv]
  have hrN : r ∈ Subgroup.normalizer (At : Set (C ⧸ N)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hAtilde_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hrB,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hrZ]
  obtain ⟨s, hsNA', hπs⟩ :=
    CFSG.GroupTheory.exists_mem_normalizer_mk'_eq N hN3 hA'3 (r := r) (by
      simpa [hAtdef, hπdef, hA'def, hNdef, hCdef] using hrN)
  have hπs' : π s = r := by simpa [hπdef] using hπs
  have hsNA : (s : G) ∈ Subgroup.normalizer (A : Set G) := by
    have hs' : s ∈ (Subgroup.normalizer (A : Set G)).subgroupOf C := by
      rwa [hA'def, ← Subgroup.subgroupOf_normalizer_eq hAC] at hsNA'
    exact Subgroup.mem_subgroupOf.mp hs'
  have hconjA' : (s : C) * aC * (s : C)⁻¹ ∈ A' :=
    (Subgroup.mem_normalizer_iff.mp hsNA' aC).mp haC_A'
  have heqA' : (⟨(s : C) * aC * (s : C)⁻¹, hconjA'⟩ : A') =
      ⟨aC⁻¹, A'.inv_mem haC_A'⟩ := by
    apply hinj
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    calc π ((s : C) * aC * (s : C)⁻¹) = π s * π aC * (π s)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = r * π aC * r⁻¹ := by rw [hπs']
      _ = (π aC)⁻¹ := hr_inv
      _ = π aC⁻¹ := by rw [map_inv]
  have heqC : (s : C) * aC * (s : C)⁻¹ = aC⁻¹ := by
    simpa using congrArg Subtype.val heqA'
  have hfinal : (s : G) * a * (s : G)⁻¹ = a⁻¹ := by
    have h := congrArg (fun x : C => (x : G)) heqC
    simpa [haCval'] using h
  exact ⟨(s : G), hsNA, show (s : G) ∈ C from s.2, hfinal⟩

end Gagen155Y1

end CFSG.RankThree.PartTwo.Sec15
