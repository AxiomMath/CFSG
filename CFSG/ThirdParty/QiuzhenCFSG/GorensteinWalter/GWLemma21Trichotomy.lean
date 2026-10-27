module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Gorenstein--Walter Part I, Lemma 2.1: the three-case trichotomy

This module proves all three cases of the trichotomy in full and declares the
pinned theorem `gw_lemma_2_1` with the same name and exact statement as the
wrapper `GorensteinWalter.GW1965`.  The index-four branch uses Burnside's
normal-complement transfer; the index-two/no-index-four branch uses the
Grün-kernel reflection-extension classification plus the Klein-four model;
the no-index-two branch uses the Grün kernel for Sylow order `> 4` and the
Burnside normalizer argument (transfer kernel of index four) for the
Klein-four Sylow case `|S| = 4`.  The module is sorry-free.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External
open scoped Pointwise

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## The even-rotation subgroup of a dihedral Sylow `2`-subgroup -/

/-- The ambient image of the even-rotation subgroup `⟨r 2⟩` of the dihedral
model, transported to a Sylow `2`-subgroup `S`.  For `m ≥ 1` this is exactly
`S'` and has relative index four in `S`. -/
private abbrev evenRotations
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) : Subgroup G :=
  ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
    (S : Subgroup G).subtype

/-- The even rotations have relative index four in a dihedral Sylow `2`-group. -/
private theorem evenRotations_relIndex_eq_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) :
    (evenRotations S e).relIndex (S : Subgroup G) = 4 := by
  classical
  let B : Subgroup G := evenRotations S e
  let B' : Subgroup (DihedralGroup (2 ^ m)) := dihedralRotationSubgroup m 1
  have hBleS : B ≤ (S : Subgroup G) := Subgroup.map_subtype_le _
  have hBS : B.subgroupOf (S : Subgroup G) = B'.comap e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rcases Subgroup.mem_map.mp hx with ⟨s, hs, hval⟩
      have hsx : s = x := by
        apply Subtype.ext
        exact hval
      simpa [hsx] using hs
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      change (x : G) ∈ B
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hindex : (B.subgroupOf (S : Subgroup G)).index = 4 := by
    rw [hBS]
    rw [Subgroup.index_comap_of_surjective B' e.surjective]
    let R2 : Subgroup (DihedralGroup (2 ^ m)) :=
      Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
    have hB'eq : B' = R2 := by
      simp [B', R2, dihedralRotationSubgroup_def]
    rw [hB'eq]
    have hcardR2 : Nat.card (↥R2) = 2 ^ (m - 1) := by
      have hc := card_dihedralRotationSubgroup (m := m) (k := 1) hm
      simpa [R2, dihedralRotationSubgroup_def] using hc
    have hindex2 := R2.index_mul_card
    rw [hcardR2, DihedralGroup.nat_card] at hindex2
    have hpow : 2 * 2 ^ m = 4 * 2 ^ (m - 1) := by
      calc
        2 * 2 ^ m = 2 * (2 * 2 ^ (m - 1)) := by
          congr 1
          calc
            2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
            _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
            _ = 2 * 2 ^ (m - 1) := by rw [mul_comm]
        _ = 4 * 2 ^ (m - 1) := by ring
    rw [hpow] at hindex2
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) (m - 1)) hindex2
  rw [Subgroup.relIndex]
  exact hindex

/-- Each reflection extension of the even rotations has relative index two in a
dihedral Sylow `2`-group. -/
private theorem indexTwoSubgroup_relIndex_eq_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m)) :
    (((dihedralIndexTwoSubgroup m j).comap e.toMonoidHom).map
      (S : Subgroup G).subtype).relIndex (S : Subgroup G) = 2 := by
  classical
  let E : Subgroup G :=
    ((dihedralIndexTwoSubgroup m j).comap e.toMonoidHom).map
      (S : Subgroup G).subtype
  let E' : Subgroup (DihedralGroup (2 ^ m)) := dihedralIndexTwoSubgroup m j
  have hE : E.subgroupOf (S : Subgroup G) = E'.comap e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rcases Subgroup.mem_map.mp hx with ⟨s, hs, hval⟩
      have hsx : s = x := by
        apply Subtype.ext
        exact hval
      simpa [hsx] using hs
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      change (x : G) ∈ E
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Subgroup.relIndex, hE]
  rw [Subgroup.index_comap_of_surjective E' e.surjective]
  exact dihedralIndexTwoSubgroup_index_eq_two hm j

/-! ## The Grün kernel in the presence of an index-four normal subgroup -/

/-- Grün's first theorem together with the dihedral four-case classification
identifies the Grün kernel with the even rotations whenever a normal subgroup
of index four exists. -/
private theorem grunKernel_eq_evenRotations_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) (hN : N.Normal) (hindex : N.index = 4)
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* DihedralGroup (2 ^ m)) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) = evenRotations S e := by
  classical
  let D : Subgroup G := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hdvd : 4 ∣ D.relIndex (S : Subgroup G) := by
    have hd := normal_index_four_dvd_sylow_inf_commutator_relIndex S N hN hindex
    rw [huppert_IV_3_4_first_grun (Q := G) (q := 2) S] at hd
    simpa [D] using hd
  by_cases hm2 : 2 ≤ m
  · have hAut : IsPGroup 2 (MulAut S) :=
      (dihedral_mulAut_is_twoGroup hm2).of_equiv (MulAut.congr e).symm
    rcases dihedral_grun_subgroup_four_cases S hm2 e hAut with
      hB | hE0 | hE1 | hS
    · exact hB
    · exfalso
      have h2 : (((dihedralIndexTwoSubgroup m 0).comap e.toMonoidHom).map
          (S : Subgroup G).subtype).relIndex (S : Subgroup G) = 2 :=
        indexTwoSubgroup_relIndex_eq_two S hm e 0
      have : 4 ∣ (((dihedralIndexTwoSubgroup m 0).comap e.toMonoidHom).map
          (S : Subgroup G).subtype).relIndex (S : Subgroup G) := by
        simpa [D, hE0] using hdvd
      rw [h2] at this
      norm_num at this
    · exfalso
      have h2 : (((dihedralIndexTwoSubgroup m 1).comap e.toMonoidHom).map
          (S : Subgroup G).subtype).relIndex (S : Subgroup G) = 2 :=
        indexTwoSubgroup_relIndex_eq_two S hm e 1
      have : 4 ∣ (((dihedralIndexTwoSubgroup m 1).comap e.toMonoidHom).map
          (S : Subgroup G).subtype).relIndex (S : Subgroup G) := by
        simpa [D, hE1] using hdvd
      rw [h2] at this
      norm_num at this
    · exfalso
      have : 4 ∣ (1 : ℕ) := by
        simpa [D, hS, Subgroup.relIndex] using hdvd
      norm_num at this
  · have hm1 : m = 1 := by omega
    have hSle : D ≤ (S : Subgroup G) := by
      change huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤ (S : Subgroup G)
      rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
      exact inf_le_left
    have hcardS : Nat.card (S : Subgroup G) = 4 := by
      have hc : Nat.card (DihedralGroup (2 ^ 1)) = 4 := by
        rw [DihedralGroup.nat_card]
        norm_num
      calc
        Nat.card (S : Subgroup G) = Nat.card (DihedralGroup (2 ^ m)) := Nat.card_congr e.toEquiv
        _ = Nat.card (DihedralGroup (2 ^ 1)) := by rw [hm1]
        _ = 4 := hc
    have hrel4 : D.relIndex (S : Subgroup G) = 4 := by
      have hrel_dvd_card : D.relIndex (S : Subgroup G) ∣ Nat.card (S : Subgroup G) := by
        have hprod : Nat.card (D.subgroupOf (S : Subgroup G)) * (D.subgroupOf (S : Subgroup G)).index =
            Nat.card (S : Subgroup G) :=
          Subgroup.card_mul_index (H := D.subgroupOf (S : Subgroup G))
        refine ⟨Nat.card (D.subgroupOf (S : Subgroup G)), ?_⟩
        rw [Subgroup.relIndex]
        simpa [mul_comm] using hprod.symm
      have hle4 : D.relIndex (S : Subgroup G) ∣ 4 := by simpa [hcardS] using hrel_dvd_card
      exact Nat.dvd_antisymm hle4 hdvd
    have hDbot : D = ⊥ := by
      apply (Subgroup.card_eq_one (H := D)).mp
      have hprod : Nat.card (D.subgroupOf (S : Subgroup G)) * (D.subgroupOf (S : Subgroup G)).index =
          Nat.card (S : Subgroup G) :=
        Subgroup.card_mul_index (H := D.subgroupOf (S : Subgroup G))
      rw [hcardS] at hprod
      have hrel : (D.subgroupOf (S : Subgroup G)).index = 4 := by
        simpa [Subgroup.relIndex] using hrel4
      rw [hrel] at hprod
      have hcardDsub : Nat.card (D.subgroupOf (S : Subgroup G)) = 1 := by
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) (by simpa [mul_comm] using hprod)
      have hcardD : Nat.card D = 1 := by
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := D) (K := S) hSle).toEquiv).symm.trans hcardDsub
      simpa [hcardD]
    have hBbot : evenRotations S e = ⊥ := by
      apply (Subgroup.card_eq_one (H := evenRotations S e)).mp
      have hc := card_dihedralRotationSubgroup (m := m) (k := 1) hm
      have hBcard : Nat.card (evenRotations S e) = 2 ^ (m - 1) := by
        let Bc : Subgroup S := (dihedralRotationSubgroup m 1).comap e.toMonoidHom
        have e1 : ↥Bc ≃* ↥(evenRotations S e) :=
          Bc.equivMapOfInjective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
        have hc' : Nat.card (↥(dihedralRotationSubgroup m 1)) = 2 ^ (m - 1) := hc
        have hc'' : Nat.card (↥Bc) = 2 ^ (m - 1) := by
          have e2 : ↥Bc ≃* ↥(dihedralRotationSubgroup m 1) := by
            let B' : Subgroup (DihedralGroup (2 ^ m)) := dihedralRotationSubgroup m 1
            change ↥Bc ≃* ↥B'
            have hmap : Bc.map e.toMonoidHom = B' :=
              Subgroup.map_comap_eq_self_of_surjective e.surjective B'
            have e2' : ↥Bc ≃* ↥(Bc.map e.toMonoidHom) :=
              Bc.equivMapOfInjective e.toMonoidHom e.injective
            exact e2'.trans (MulEquiv.subgroupCongr hmap)
          exact (Nat.card_congr e2.toEquiv).trans hc'
        exact (Nat.card_congr e1.toEquiv).symm.trans hc''
      simpa [hm1] using hBcard
    change D = evenRotations S e
    rw [hDbot, hBbot]

/-- The even rotations are cyclic. -/
private theorem evenRotations_cyclic
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) :
    IsCyclic ↥(evenRotations S e) := by
  classical
  let B : Subgroup G := evenRotations S e
  let Bc : Subgroup S := (dihedralRotationSubgroup m 1).comap e.toMonoidHom
  have e1 : ↥Bc ≃* ↥B :=
    Bc.equivMapOfInjective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
  have e2 : ↥Bc ≃* ↥(dihedralRotationSubgroup m 1) := by
    let B' : Subgroup (DihedralGroup (2 ^ m)) := dihedralRotationSubgroup m 1
    change ↥Bc ≃* ↥B'
    have hmap : Bc.map e.toMonoidHom = B' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective B'
    have e2' : ↥Bc ≃* ↥(Bc.map e.toMonoidHom) :=
      Bc.equivMapOfInjective e.toMonoidHom e.injective
    exact e2'.trans (MulEquiv.subgroupCongr hmap)
  have hB' : IsCyclic ↥(dihedralRotationSubgroup m 1) := by
    rw [dihedralRotationSubgroup_def]
    infer_instance
  exact (MulEquiv.isCyclic (e1.symm.trans e2)).mpr hB'

/-- With a normal index-four subgroup the intersection `S ∩ N` is exactly the
even-rotation subgroup. -/
private theorem evenRotations_eq_sylow_inf_normal_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) (hN : N.Normal) (hindex : N.index = 4)
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* DihedralGroup (2 ^ m))
    (hD : huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) = evenRotations S e) :
    (S : Subgroup G) ⊓ N = evenRotations S e := by
  classical
  let D : Subgroup G := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  let B : Subgroup G := evenRotations S e
  have hDleG' : D ≤ commutator G := by
    change huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤ commutator G
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    exact inf_le_right
  have hG'leN : commutator G ≤ N := commutator_le_of_normal_index_four N hN hindex
  have hBleSN : B ≤ (S : Subgroup G) ⊓ N := by
    intro x hx
    refine ⟨Subgroup.map_subtype_le _ hx, ?_⟩
    have hxD : x ∈ D := by
      change x ∈ huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
      rw [hD]
      exact hx
    exact hG'leN (hDleG' hxD)
  have hquot : IsPGroup 2 (G ⧸ N) := by
    apply IsPGroup.of_card (n := 2)
    rw [← N.index_eq_card, hindex]
    norm_num
  have hrelN : N.relIndex (S : Subgroup G) = 4 := by
    rw [normal_relIndex_sylow_eq_index_of_quotient_isPGroup S N hN hquot]
    exact hindex
  have hrelSN : ((S : Subgroup G) ⊓ N).relIndex (S : Subgroup G) = 4 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact hrelN
  have hrelB : B.relIndex (S : Subgroup G) = 4 := evenRotations_relIndex_eq_four S hm e
  have hrel_mul : B.relIndex ((S : Subgroup G) ⊓ N) * (((S : Subgroup G) ⊓ N).relIndex (S : Subgroup G)) =
      B.relIndex (S : Subgroup G) :=
    Subgroup.relIndex_mul_relIndex (H := B) (K := (S : Subgroup G) ⊓ N) (L := (S : Subgroup G))
      hBleSN (inf_le_left : (S : Subgroup G) ⊓ N ≤ (S : Subgroup G))
  have hrel1 : B.relIndex ((S : Subgroup G) ⊓ N) = 1 := by
    have : B.relIndex ((S : Subgroup G) ⊓ N) * 4 = 4 := by
      calc
        B.relIndex ((S : Subgroup G) ⊓ N) * 4 =
            B.relIndex ((S : Subgroup G) ⊓ N) * (((S : Subgroup G) ⊓ N).relIndex (S : Subgroup G)) := by
          rw [hrelSN]
        _ = B.relIndex (S : Subgroup G) := hrel_mul
        _ = 4 := hrelB
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 4) (by simpa [mul_comm] using this)
  have hSNleB : (S : Subgroup G) ⊓ N ≤ B := Subgroup.relIndex_eq_one.mp hrel1
  exact le_antisymm hSNleB hBleSN

/-! ## The even rotations are a cyclic Sylow subgroup of `N` -/

/-- The even-rotation subgroup is a Sylow `2`-subgroup of the index-four normal
subgroup `N`. -/
private theorem evenRotations_is_sylow_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) (hN : N.Normal) (hindex : N.index = 4)
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* DihedralGroup (2 ^ m))
    (hSN : (S : Subgroup G) ⊓ N = evenRotations S e) :
    ∃ P : Sylow 2 (↥N), (P : Subgroup (↥N)) = (evenRotations S e).subgroupOf N := by
  classical
  let B : Subgroup G := evenRotations S e
  have hBleN : B ≤ N := by
    intro x hx
    have hxSN : x ∈ (S : Subgroup G) ⊓ N := by
      rw [hSN]
      exact hx
    exact hxSN.2
  have hBleS : B ≤ (S : Subgroup G) := by
    intro x hx
    have hxSN : x ∈ (S : Subgroup G) ⊓ N := by
      rw [hSN]
      exact hx
    exact hxSN.1
  have hBp : IsPGroup 2 ↥(B.subgroupOf N) := by
    have hBpG : IsPGroup 2 ↥B := (S.isPGroup').to_le hBleS
    have eB : ↥(B.subgroupOf N) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBleN
    exact hBpG.of_equiv eB.symm
  obtain ⟨Q, hBQ⟩ := IsPGroup.exists_le_sylow (p := 2) (G := ↥N) hBp
  have hBindex : (B.subgroupOf N).index = (S : Subgroup G).index := by
    have h1 : B.relIndex N * N.index = B.index :=
      Subgroup.relIndex_mul_index (H := B) (K := N) hBleN
    have h2 : B.relIndex (S : Subgroup G) * (S : Subgroup G).index = B.index :=
      Subgroup.relIndex_mul_index (H := B) (K := (S : Subgroup G)) hBleS
    have hrelB : B.relIndex (S : Subgroup G) = 4 := evenRotations_relIndex_eq_four S hm e
    have : (B.subgroupOf N).index * 4 = (S : Subgroup G).index * 4 := by
      calc
        (B.subgroupOf N).index * 4 = (B.subgroupOf N).index * N.index := by rw [hindex]
        _ = B.index := h1
        _ = 4 * (S : Subgroup G).index := by simpa [hrelB] using h2.symm
        _ = (S : Subgroup G).index * 4 := by rw [mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 4) this
  have hoddB : Odd (B.subgroupOf N).index := by
    have h2ndvd : ¬ 2 ∣ (B.subgroupOf N).index := by
      rw [hBindex]
      exact S.not_dvd_index
    rw [← Nat.not_even_iff_odd]
    intro hEven
    exact h2ndvd (even_iff_two_dvd.mp hEven)
  have hrelpow : ∃ k, (B.subgroupOf N).relIndex (Q : Subgroup (↥N)) = 2 ^ k := by
    have hQp : IsPGroup 2 ↥(Q : Subgroup (↥N)) := Q.isPGroup'
    rcases hQp.index ((B.subgroupOf N).subgroupOf (Q : Subgroup (↥N))) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [Subgroup.relIndex] using hk
  have hrel1 : (B.subgroupOf N).relIndex (Q : Subgroup (↥N)) = 1 := by
    rcases hrelpow with ⟨k, hk⟩
    have hdvd : (B.subgroupOf N).relIndex (Q : Subgroup (↥N)) ∣ (B.subgroupOf N).index := by
      have hmul := Subgroup.relIndex_mul_index (H := B.subgroupOf N) (K := (Q : Subgroup (↥N))) hBQ
      exact ⟨(Q : Subgroup (↥N)).index, hmul.symm⟩
    have hk0 : k = 0 := by
      by_contra hkne
      have h2dvd : 2 ∣ 2 ^ k := by
        obtain ⟨k0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
        exact ⟨2 ^ k0, by rw [pow_succ]; ring⟩
      have h2dvd_idx : 2 ∣ (B.subgroupOf N).index := by
        rw [← hk] at h2dvd
        exact h2dvd.trans hdvd
      exact (Nat.not_even_iff_odd.mpr hoddB) (even_iff_two_dvd.mpr h2dvd_idx)
    have hk0pow : 2 ^ k = 1 := by
      rw [hk0]
      norm_num
    exact hk.trans hk0pow
  have hQleB : (Q : Subgroup (↥N)) ≤ B.subgroupOf N := Subgroup.relIndex_eq_one.mp hrel1
  have hQeq : (Q : Subgroup (↥N)) = B.subgroupOf N := le_antisymm hQleB hBQ
  exact ⟨Q, hQeq⟩

/-- All Sylow `2`-subgroups of an index-four normal subgroup are cyclic. -/
private theorem cyclic_sylow_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) (hN : N.Normal) (hindex : N.index = 4)
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* DihedralGroup (2 ^ m))
    (hSN : (S : Subgroup G) ⊓ N = evenRotations S e) :
    ∀ P : Sylow 2 (↥N), IsCyclic ↥(P : Subgroup (↥N)) := by
  classical
  let B : Subgroup G := evenRotations S e
  have hBleN : B ≤ N := by
    intro x hx
    have hxSN : x ∈ (S : Subgroup G) ⊓ N := by
      rw [hSN]
      exact hx
    exact hxSN.2
  obtain ⟨Q, hQeq⟩ := evenRotations_is_sylow_of_normal_index_four S N hN hindex hm e hSN
  have hBcyc : IsCyclic ↥B := evenRotations_cyclic S e
  have hQcyc : IsCyclic Q := by
    have eB : ↥(B.subgroupOf N) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBleN
    have eQ : Q ≃* ↥B := (MulEquiv.subgroupCongr hQeq).trans eB
    exact (MulEquiv.isCyclic eQ).mpr hBcyc
  intro P
  have ePQ : P ≃* Q := Sylow.equiv P Q
  exact (MulEquiv.isCyclic ePQ).mpr hQcyc

/-! ## Burnside's normal-complement step -/

/-- A finite group whose Sylow `2`-subgroups are cyclic has a normal
`2`-complement (Burnside's transfer theorem). -/
private theorem hasNormalPComplement_of_cyclic_sylow
    {G : Type u} [Group G] [Finite G]
    (hcyc : ∀ P : Sylow 2 G, IsCyclic ↥(P : Subgroup G)) :
    HasNormalPComplement 2 G := by
  classical
  by_cases h2 : 2 ∣ Nat.card G
  · let S : Sylow 2 G := Classical.choice Sylow.nonempty
    have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff (Nat.card G)).2 h2
    have hNC : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) :=
      (hcyc S).normalizer_le_centralizer hmin
    have hScenter : (S : Subgroup G) ≤ centerIn (G := G) (Subgroup.normalizer (S : Set G)) := by
      intro s hs
      refine ⟨Subgroup.le_normalizer hs, ?_⟩
      change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
    exact hasNormalPComplement_of_sylow_le_center_normalizer (G := G) 2 S hScenter
  · have hodd : Odd (Nat.card G) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h2
    refine ⟨⊤, inferInstance, ?_, ?_⟩
    · simpa using hodd.coprime_two_left
    · intro x
      refine ⟨0, ?_⟩
      have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
      simpa using (@Subsingleton.elim _ hsub x 1)

/-- A normal subgroup with a normal `2`-complement and a `2`-group quotient
gives a normal `2`-complement of the ambient group. -/
private theorem hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hGNp : IsPGroup 2 (G ⧸ N))
    (hNcomp : HasNormalPComplement 2 (↥N)) :
    HasNormalPComplement 2 G := by
  classical
  let K : Subgroup G := (pPrimeCore 2 (↥N)).map N.subtype
  have : K.Normal := by
    dsimp [K]
    infer_instance
  have hKcop : Nat.Coprime 2 (Nat.card K) := by
    have hcard : Nat.card K = Nat.card (pPrimeCore 2 (↥N)) := by
      simpa [K] using (Subgroup.card_map_of_injective (K := pPrimeCore 2 (↥N)) (f := N.subtype) N.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (G := ↥N) (p := 2)
  have hNKp : IsPGroup 2 ((↥N) ⧸ pPrimeCore 2 (↥N)) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) (H := ↥N) hNcomp
  let Nbar : Subgroup (G ⧸ K) := N.map (QuotientGroup.mk' K)
  have hNbar_p : IsPGroup 2 Nbar := by
    let φ : ↥N →* G ⧸ K := (QuotientGroup.mk' K).comp N.subtype
    have hφker : φ.ker = pPrimeCore 2 (↥N) := by
      ext n
      change QuotientGroup.mk' K (n : G) = 1 ↔ n ∈ pPrimeCore 2 (↥N)
      have hq : QuotientGroup.mk' K (n : G) = 1 ↔ (n : G) ∈ K :=
        QuotientGroup.eq_one_iff (N := K) (x := (n : G))
      rw [hq]
      change (n : G) ∈ (pPrimeCore 2 (↥N)).map N.subtype ↔ n ∈ pPrimeCore 2 (↥N)
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨m, hm, hval⟩
        have hmn : m = n := by
          apply Subtype.ext
          exact hval
        simpa [hmn] using hm
      · intro hn
        exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hφrange : φ.range = Nbar := by
      ext x
      constructor
      · intro hx
        rw [MonoidHom.mem_range] at hx
        rcases hx with ⟨n, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(n : G), n.property, rfl⟩
      · intro hx
        rw [Subgroup.mem_map] at hx
        rcases hx with ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, rfl⟩
    have eN : Nbar ≃* (↥N) ⧸ pPrimeCore 2 (↥N) := by
      let e0 : (↥N) ⧸ φ.ker ≃* Nbar :=
        (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange)
      exact e0.symm.trans (QuotientGroup.quotientMulEquivOfEq hφker)
    exact hNKp.of_equiv eN.symm
  have hNbar_normal : Nbar.Normal := inferInstance
  have hKN : K ≤ N := Subgroup.map_subtype_le _
  have hthird : (G ⧸ K) ⧸ Nbar ≃* G ⧸ N :=
    QuotientGroup.quotientQuotientEquivQuotient K N hKN
  have hquot_p : IsPGroup 2 ((G ⧸ K) ⧸ Nbar) := hGNp.of_equiv hthird.symm
  have hGKp : IsPGroup 2 (G ⧸ K) := by
    rw [IsPGroup.iff_card]
    have hcard : Nat.card (G ⧸ K) = Nat.card Nbar * Nat.card ((G ⧸ K) ⧸ Nbar) := by
      have hprod := Subgroup.card_mul_index (H := Nbar)
      rw [Subgroup.index_eq_card] at hprod
      exact hprod.symm
    rcases (IsPGroup.iff_card (p := 2) (G := Nbar)).mp hNbar_p with ⟨a, ha⟩
    rcases (IsPGroup.iff_card (p := 2) (G := (G ⧸ K) ⧸ Nbar)).mp hquot_p with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    calc
      Nat.card (G ⧸ K) = Nat.card Nbar * Nat.card ((G ⧸ K) ⧸ Nbar) := hcard
      _ = 2 ^ a * 2 ^ b := by rw [ha, hb]
      _ = 2 ^ (a + b) := by rw [pow_add]
  exact ⟨K, inferInstance, hKcop, hGKp⟩

/-- Convert the Feit--Thompson transfer predicate to Glauberman's
`O_{2',2}(G) = G` form. -/
private theorem normalPComplement_of_hasNormalPComplement
    {G : Type u} [Group G] [Finite G]
    (hcomp : HasNormalPComplement 2 G) :
    Glauberman.NormalPComplement 2 G := by
  let Q := G ⧸ pPrimeCore 2 G
  have hq : IsPGroup 2 Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) G hcomp
  have hqtop : IsPGroup 2 (⊤ : Subgroup Q) := hq.to_subgroup ⊤
  have hpcore : pCore 2 Q = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, hqtop⟩
  apply Glauberman.normalPComplement_of_eq_top
  simp [Op_p'p, Q, hpcore]

/-! ## The index-four branch of Lemma 2.1 -/

/-- Case (iii) of Gorenstein--Walter Part I Lemma 2.1: a normal subgroup of
index four forces a normal `2`-complement.

The proof follows Gorenstein--Walter 1962, Lemma 8(iii): Grün's first theorem
identifies `S ∩ G'` with the even-rotation subgroup `B`; since `G' ≤ N`, the
intersection `S ∩ N` is exactly `B`, which is a cyclic Sylow `2`-subgroup of
`N` (its index in `N` is odd).  Burnside's transfer theorem gives the normal
`2`-complement of `N`, and the extension by the `2`-group quotient `G/N`
lifts it to `G`. -/
public theorem normal_index_four_dihedral_sylow_normalPComplement
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (hN4 : ∃ N : Subgroup G, N.Normal ∧ N.index = 4) :
    Glauberman.NormalPComplement 2 G := by
  classical
  rcases hN4 with ⟨N, hN, hindex⟩
  let : N.Normal := hN
  let S : Sylow 2 G := Classical.choice Sylow.nonempty
  obtain ⟨m, hm, ⟨e⟩⟩ := hdihedral S
  have hD : huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) = evenRotations S e :=
    grunKernel_eq_evenRotations_of_normal_index_four S N hN hindex hm e
  have hSN : (S : Subgroup G) ⊓ N = evenRotations S e :=
    evenRotations_eq_sylow_inf_normal_of_normal_index_four S N hN hindex hm e hD
  have hcycN : ∀ P : Sylow 2 (↥N), IsCyclic ↥(P : Subgroup (↥N)) :=
    cyclic_sylow_of_normal_index_four S N hN hindex hm e hSN
  have hcompN : HasNormalPComplement 2 (↥N) := hasNormalPComplement_of_cyclic_sylow hcycN
  have hGNp : IsPGroup 2 (G ⧸ N) := by
    apply IsPGroup.of_card (n := 2)
    rw [← N.index_eq_card, hindex]
    norm_num
  have hcompG : HasNormalPComplement 2 G :=
    hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient N hGNp hcompN
  exact normalPComplement_of_hasNormalPComplement hcompG

/-! ## The no-index-two branch: Grün kernel is the whole Sylow subgroup -/

/-- A normal subgroup of index four forces a normal subgroup of index two:
the quotient has order four and every group of order four has an index-two
subgroup, pulled back along the quotient map. -/
private theorem normal_index_two_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (hN4 : ∃ N : Subgroup G, N.Normal ∧ N.index = 4) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  rcases hN4 with ⟨N4, hN4, hindex4⟩
  let : N4.Normal := hN4
  let : Fintype (G ⧸ N4) := N4.fintypeQuotientOfFiniteIndex
  have hcardQ : Nat.card (G ⧸ N4) = 4 := by
    rw [← N4.index_eq_card, hindex4]
  have h2dvd : 2 ∣ Fintype.card (G ⧸ N4) := by
    rw [← Nat.card_eq_fintype_card, hcardQ]
    norm_num
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card (G := G ⧸ N4) 2 h2dvd
  let H : Subgroup (G ⧸ N4) := Subgroup.zpowers x
  have hHcard : Nat.card H = 2 := by
    rw [Nat.card_zpowers, hx2]
  have hHindex : H.index = 2 := by
    have hprod := H.index_mul_card
    rw [hHcard, hcardQ] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by simpa [mul_comm] using hprod)
  have hHnormal : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  let N : Subgroup G := H.comap (QuotientGroup.mk' N4)
  have hNnormal : N.Normal := hHnormal.comap (QuotientGroup.mk' N4)
  have hNindex : N.index = 2 := by
    rw [Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective N4)]
    exact hHindex
  exact ⟨N, hNnormal, hNindex⟩

/-- If no normal subgroup of index two exists, the Grün kernel of a dihedral
Sylow `2`-subgroup is the whole Sylow subgroup.  The Grün kernel is one of
the even rotations (relative index four), a reflection extension (relative
index two), or the whole Sylow subgroup; the first two alternatives would
produce an index-four or index-two normal subgroup. -/
private theorem grunKernel_eq_sylow_of_no_normal_index_two
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G) (S : Sylow 2 G)
    (hno2 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) = (S : Subgroup G) := by
  classical
  let D : Subgroup G := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  obtain ⟨m, hm, ⟨e⟩⟩ := hdihedral S
  by_cases hm2 : 2 ≤ m
  · have hAut : IsPGroup 2 (MulAut S) :=
      (dihedral_mulAut_is_twoGroup hm2).of_equiv (MulAut.congr e).symm
    rcases dihedral_grun_subgroup_four_cases S hm2 e hAut with hB | hE0 | hE1 | hS
    · exfalso
      have hrel : D.relIndex (S : Subgroup G) = 4 := by
        change (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
          (S : Subgroup G) = 4
        rw [hB]
        exact evenRotations_relIndex_eq_four S hm e
      have hN4 : ∃ N : Subgroup G, N.Normal ∧ N.index = 4 :=
        exists_normal_index_four_of_grun_relIndex_eq_four S hrel
      exact hno2 (normal_index_two_of_normal_index_four hN4)
    · exfalso
      have hrel : D.relIndex (S : Subgroup G) = 2 := by
        change (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
          (S : Subgroup G) = 2
        rw [hE0]
        exact indexTwoSubgroup_relIndex_eq_two S hm e 0
      exact hno2 (exists_normal_index_two_of_grun_relIndex_eq_two S hrel)
    · exfalso
      have hrel : D.relIndex (S : Subgroup G) = 2 := by
        change (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
          (S : Subgroup G) = 2
        rw [hE1]
        exact indexTwoSubgroup_relIndex_eq_two S hm e 1
      exact hno2 (exists_normal_index_two_of_grun_relIndex_eq_two S hrel)
    · exact hS
  · have hm1 : m = 1 := by omega
    have hSle : D ≤ (S : Subgroup G) := by
      change huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤ (S : Subgroup G)
      rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
      exact inf_le_left
    have hcardS : Nat.card (S : Subgroup G) = 4 := by
      have hc : Nat.card (DihedralGroup (2 ^ 1)) = 4 := by
        rw [DihedralGroup.nat_card]
        norm_num
      calc
        Nat.card (S : Subgroup G) = Nat.card (DihedralGroup (2 ^ m)) := Nat.card_congr e.toEquiv
        _ = Nat.card (DihedralGroup (2 ^ 1)) := by rw [hm1]
        _ = 4 := hc
    have hrel_dvd : D.relIndex (S : Subgroup G) ∣ 4 := by
      have hdvd := Subgroup.relIndex_dvd_card D (S : Subgroup G)
      simpa [hcardS] using hdvd
    have hne2 : D.relIndex (S : Subgroup G) ≠ 2 := by
      intro h2
      exact hno2 (exists_normal_index_two_of_grun_relIndex_eq_two S h2)
    have hne4 : D.relIndex (S : Subgroup G) ≠ 4 := by
      intro h4
      exact hno2
        (normal_index_two_of_normal_index_four
          (exists_normal_index_four_of_grun_relIndex_eq_four S h4))
    have hrel1 : D.relIndex (S : Subgroup G) = 1 := by
      have hrel4pow : D.relIndex (S : Subgroup G) ∣ 2 ^ 2 := by
        rw [← show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact hrel_dvd
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hrel4pow with ⟨n, hn, hrelpow⟩
      interval_cases n
      · rw [hrelpow]
        norm_num
      · exfalso
        exact hne2 (by simpa [hrelpow])
      · exfalso
        exact hne4 (by simpa [hrelpow])
    have hSleD : (S : Subgroup G) ≤ D := Subgroup.relIndex_eq_one.mp hrel1
    exact le_antisymm hSle hSleD

/-! ## The Klein-four model of a dihedral Sylow `2`-subgroup -/

/-- The central involution `r (2^(m-1))` of the dihedral model. -/
private abbrev dCentral (m : ℕ) : DihedralGroup (2 ^ m) :=
  DihedralGroup.r ((2 : ZMod (2 ^ m)) ^ (m - 1))

/-- The carrier `{1, z, sr i, sr (i + half)}` of the Klein-four subgroup
`⟨sr i, z⟩` of the dihedral model. -/
private def dKleinCarrier (m : ℕ) (i : ZMod (2 ^ m)) : Set (DihedralGroup (2 ^ m)) :=
  {x | x = 1 ∨ x = dCentral m ∨ x = DihedralGroup.sr i ∨
    x = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1))}

private lemma half_add_self {m : ℕ} (hm : 1 ≤ m) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) + (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
  have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    calc
      2 ^ (m - 1) + 2 ^ (m - 1) = 2 * 2 ^ (m - 1) := by ring
      _ = 2 ^ m := by
        rw [← pow_succ']
        congr 1
        omega
  have hcast : ((2 ^ (m - 1) + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
    rw [hpow, ZMod.natCast_self]
  have hcast2 : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
    rw [Nat.cast_pow]
    norm_num
  simpa [Nat.cast_add, hcast2] using hcast

private lemma half_neg {m : ℕ} (hm : 1 ≤ m) :
    -((2 : ZMod (2 ^ m)) ^ (m - 1)) = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
  rw [neg_eq_iff_add_eq_zero]
  exact half_add_self hm

private lemma sr_i_half {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) ^ (m - 1)) =
      DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
  apply congrArg DihedralGroup.sr
  rw [sub_eq_add_neg, half_neg hm]

private lemma dKleinCarrier_one {m : ℕ} (i : ZMod (2 ^ m)) :
    (1 : DihedralGroup (2 ^ m)) ∈ dKleinCarrier m i := by
  simp [dKleinCarrier]

private lemma dKleinCarrier_mul {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m))
    {x y : DihedralGroup (2 ^ m)} (hx : x ∈ dKleinCarrier m i) (hy : y ∈ dKleinCarrier m i) :
    x * y ∈ dKleinCarrier m i := by
  rw [dKleinCarrier] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [dCentral, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_zero,
      add_assoc, add_zero, half_add_self hm, half_neg hm, sr_i_half hm i]

private lemma dKleinCarrier_inv {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m))
    {x : DihedralGroup (2 ^ m)} (hx : x ∈ dKleinCarrier m i) :
    x⁻¹ ∈ dKleinCarrier m i := by
  rw [dKleinCarrier] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [dCentral, DihedralGroup.inv_r, DihedralGroup.inv_sr, half_neg hm]

/-- The Klein-four subgroup `⟨sr i, dCentral m⟩` of the dihedral model. -/
private def dKlein (m : ℕ) (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    Subgroup (DihedralGroup (2 ^ m)) where
  carrier := dKleinCarrier m i
  one_mem' := dKleinCarrier_one i
  mul_mem' := dKleinCarrier_mul hm i
  inv_mem' := dKleinCarrier_inv hm i

private lemma mem_dKlein_iff {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m))
    (x : DihedralGroup (2 ^ m)) :
    x ∈ dKlein m hm i ↔
      x = 1 ∨ x = dCentral m ∨ x = DihedralGroup.sr i ∨
        x = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
  rfl

private lemma dCentral_ne_one {m : ℕ} (hm : 1 ≤ m) : dCentral m ≠ 1 := by
  intro h
  have hinj : (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
    apply DihedralGroup.r.inj
    rw [DihedralGroup.one_def] at h
    exact h
  have hcast : (2 : ZMod (2 ^ m)) ^ (m - 1) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [Nat.cast_pow]
    norm_num
  have hnat : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
    rw [← hcast]
    exact hinj
  have hdvd : 2 ^ m ∣ 2 ^ (m - 1) := by
    have hval : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)).val = 0 := by
      exact (ZMod.val_eq_zero (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).mpr hnat
    rw [ZMod.val_natCast] at hval
    exact Nat.dvd_iff_mod_eq_zero.mpr hval
  have hlt : 2 ^ (m - 1) < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m - 1 < m)
  exact (not_lt_of_ge (Nat.le_of_dvd (pow_pos (by norm_num : 0 < 2) (m - 1)) hdvd)) hlt

/-- The central involution of the dihedral model has square one. -/
private lemma dCentral_mul_self {m : ℕ} (hm : 1 ≤ m) :
    dCentral m * dCentral m = 1 := by
  rw [dCentral, DihedralGroup.r_mul_r, DihedralGroup.one_def]
  congr 1
  exact half_add_self hm

/-- The central involution of the dihedral model is its own inverse. -/
private lemma dCentral_inv_self {m : ℕ} (hm : 1 ≤ m) :
    (dCentral m)⁻¹ = dCentral m := by
  rw [inv_eq_iff_mul_eq_one]
  exact dCentral_mul_self hm

/-- The central involution has order two. -/
private lemma dCentral_order_two {m : ℕ} (hm : 1 ≤ m) :
    orderOf (dCentral m) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    exact dCentral_mul_self hm
  · exact dCentral_ne_one hm

private lemma sr_ne_one {m : ℕ} (i : ZMod (2 ^ m)) : DihedralGroup.sr i ≠ 1 := by
  intro h
  cases h

private lemma sr_ne_dCentral {m : ℕ} (i : ZMod (2 ^ m)) :
    DihedralGroup.sr i ≠ dCentral m := by
  intro h
  cases h

private lemma half_ne_zero {m : ℕ} (hm : 1 ≤ m) : (2 : ZMod (2 ^ m)) ^ (m - 1) ≠ 0 := by
  intro h0
  apply dCentral_ne_one hm
  simpa [dCentral, h0]

private lemma sr_half_ne_sr {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) ≠ DihedralGroup.sr i := by
  intro h
  apply half_ne_zero hm
  have hij := DihedralGroup.sr.inj h
  have : (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
    calc
      (2 : ZMod (2 ^ m)) ^ (m - 1) = (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) - i := by abel
      _ = i - i := by rw [hij]
      _ = 0 := by abel
  exact this

private lemma sr_half_ne_one {m : ℕ} (i : ZMod (2 ^ m)) :
    DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) ≠ 1 := by
  intro h
  cases h

private lemma sr_half_ne_dCentral {m : ℕ} (i : ZMod (2 ^ m)) :
    DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) ≠ dCentral m := by
  intro h
  cases h

private lemma dKlein_card_four {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    Nat.card ↥(dKlein m hm i) = 4 := by
  have hset : Nat.card ↥(dKlein m hm i) =
      ((dKlein m hm i : Set (DihedralGroup (2 ^ m))).ncard) := by
    simpa using (Nat.card_coe_set_eq ((dKlein m hm i : Set (DihedralGroup (2 ^ m)))))
  have hfour : ((dKlein m hm i : Set (DihedralGroup (2 ^ m))).ncard) = 4 := by
    change ({x : DihedralGroup (2 ^ m) |
      x = 1 ∨ x = dCentral m ∨ x = DihedralGroup.sr i ∨
        x = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1))}).ncard = 4
    rw [Set.ncard_eq_four]
    refine ⟨1, dCentral m, DihedralGroup.sr i,
      DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)), ?_⟩
    constructor
    · exact (dCentral_ne_one hm).symm
    · constructor
      · exact (sr_ne_one i).symm
      · constructor
        · exact (sr_half_ne_one i).symm
        · constructor
          · exact (sr_ne_dCentral i).symm
          · constructor
            · exact (sr_half_ne_dCentral i).symm
            · constructor
              · exact (sr_half_ne_sr hm i).symm
              · ext x
                simp [dKleinCarrier]
  exact hset.trans hfour

private lemma dKlein_sq_one {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    ∀ x : ↥(dKlein m hm i), (x : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
  intro x
  have hx : (x : DihedralGroup (2 ^ m)) ∈ dKlein m hm i := x.property
  rw [mem_dKlein_iff hm i (x : DihedralGroup (2 ^ m))] at hx
  rcases hx with h1 | h2 | h3 | h4
  · simpa [h1, pow_two]
  · simp [h2, pow_two, dCentral, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_zero,
      half_add_self hm, half_neg hm, sr_i_half hm i]
  · simpa [h3, pow_two]
  · simp [h4, pow_two, dCentral, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r_zero,
      half_add_self hm, half_neg hm, sr_i_half hm i]

private lemma dKlein_not_cyclic {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    ¬ IsCyclic ↥(dKlein m hm i) := by
  intro hcyc
  rcases (isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc) with ⟨g, hg⟩
  have hg2 : (g : DihedralGroup (2 ^ m)) ^ 2 = 1 := dKlein_sq_one hm i g
  have hord2 : orderOf (g : DihedralGroup (2 ^ m)) ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have hord_eq : orderOf (g : DihedralGroup (2 ^ m)) = orderOf g :=
    orderOf_injective (dKlein m hm i).subtype (dKlein m hm i).subtype_injective g
  have hord2' : orderOf g ∣ 2 := by simpa [hord_eq] using hord2
  have hord4 : orderOf g = 4 := hg.trans (dKlein_card_four hm i)
  have : 4 ∣ 2 := by simpa [hord4] using hord2'
  norm_num at this

private lemma isKleinFour_dKlein {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    IsKleinFour ↥(dKlein m hm i) := by
  have hcard : Nat.card ↥(dKlein m hm i) = 4 := dKlein_card_four hm i
  have hnc : ¬ IsCyclic ↥(dKlein m hm i) := dKlein_not_cyclic hm i
  exact {
    card_four := hcard
    exponent_two := (not_isCyclic_iff_exponent_eq_prime Nat.prime_two (by simpa using hcard)).mp hnc
  }

private lemma dCentral_mem_center {m : ℕ} (hm : 2 ≤ m) :
    dCentral m ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
  rw [Subgroup.mem_center_iff]
  intro x
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [dCentral, DihedralGroup.r_mul_r, add_comm]
  · simp [dCentral, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      sr_i_half (by omega : 1 ≤ m) i]

private lemma dKlein_le_of_mem {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m))
    (W : Subgroup (DihedralGroup (2 ^ m)))
    (hz : dCentral m ∈ W) (hsr : DihedralGroup.sr i ∈ W) :
    dKlein m hm i ≤ W := by
  intro x hx
  rw [mem_dKlein_iff hm i x] at hx
  rcases hx with h1 | h2 | h3 | h4
  · simpa [h1] using W.one_mem
  · simpa [h2] using hz
  · simpa [h3] using hsr
  · rw [h4]
    have hprod : DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) =
        DihedralGroup.sr i * dCentral m := by
      simp [dCentral, DihedralGroup.sr_mul_r]
    rw [hprod]
    exact W.mul_mem hsr hz

private lemma dKlein_sr_mem {m : ℕ} (hm : 1 ≤ m) (i : ZMod (2 ^ m)) :
    DihedralGroup.sr i ∈ dKlein m hm i := by
  rw [mem_dKlein_iff hm i (DihedralGroup.sr i)]
  exact Or.inr (Or.inr (Or.inl rfl))

private lemma isKleinFour_eq_dKlein {m : ℕ} (hm : 2 ≤ m)
    (W : Subgroup (DihedralGroup (2 ^ m))) (hW : IsKleinFour W) :
    ∃ i : ZMod (2 ^ m), W = dKlein m (by omega : 1 ≤ m) i := by
  classical
  have hz : dCentral m ∈ W := by
    exact center_mem_kleinFour_of_dihedral_mulEquiv (by omega : 1 ≤ m)
      (MulEquiv.refl (DihedralGroup (2 ^ m))) W hW
      (dCentral_mem_center hm)
  have hWnc : ¬ IsCyclic W := IsKleinFour.not_isCyclic
  have hRcyc : IsCyclic ↥(dihedralRotationSubgroup m 0) := by
    rw [dihedralRotationSubgroup_def, show (2 ^ 0 : ZMod (2 ^ m)) = 1 by norm_num]
    infer_instance
  have hnotR : ¬ W ≤ dihedralRotationSubgroup m 0 := by
    intro hle
    exact hWnc (@Subgroup.isCyclic_of_le (DihedralGroup (2 ^ m)) _ W
      (dihedralRotationSubgroup m 0) hle hRcyc)
  rcases SetLike.not_le_iff_exists.mp hnotR with ⟨x, hxW, hxR⟩
  rcases dihedralGroup_cases x with ⟨i, hi⟩ | ⟨i, hi⟩
  · exfalso
    exact hxR (by
      rw [hi]
      simpa [dihedralRotationSubgroup_def,
        show (2 ^ 0 : ZMod (2 ^ m)) = 1 by norm_num] using (r_mem_zpowers_r_one i))
  · refine ⟨i, ?_⟩
    have hle : dKlein m (by omega : 1 ≤ m) i ≤ W :=
      dKlein_le_of_mem (by omega : 1 ≤ m) i W hz (by
        simpa [hi] using hxW)
    exact (Subgroup.eq_of_le_of_card_ge hle (by
      rw [dKlein_card_four (by omega : 1 ≤ m) i, IsKleinFour.card_four])).symm

/-- In a dihedral `2`-group of order at least eight, for every reflection
`sr j` there is a Klein-four subgroup disjoint from the cyclic subgroup
generated by that reflection. -/
public theorem exists_kleinFour_disjoint_from_reflection_zpowers
    {m : ℕ} (hm : 2 ≤ m) (j : ZMod (2 ^ m)) :
    ∃ W : Subgroup (DihedralGroup (2 ^ m)),
      IsKleinFour W ∧ W ⊓ Subgroup.zpowers (DihedralGroup.sr j) = ⊥ := by
  let h : ZMod (2 ^ m) := (2 : ZMod (2 ^ m)) ^ (m - 1)
  let W : Subgroup (DihedralGroup (2 ^ m)) := dKlein m (by omega : 1 ≤ m) (j + 1)
  refine ⟨W, isKleinFour_dKlein (by omega : 1 ≤ m) (j + 1), ?_⟩
  have h1 : DihedralGroup.sr (j + 1) ≠ DihedralGroup.sr j := by
    intro hsr
    have hz : (1 : ZMod (2 ^ m)) = 0 := by
      have hsub : (j + 1) - j = j - j :=
        congrArg (fun z : ZMod (2 ^ m) => z - j) (DihedralGroup.sr.inj hsr)
      simpa using hsub
    have hdvd : 2 ^ m ∣ 1 :=
      (ZMod.natCast_eq_zero_iff (1 : ℕ) (2 ^ m)).mp (by simpa using hz)
    have hle : 2 ^ m ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 4 ≤ 2 ^ m := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : DihedralGroup.sr (j + 1 + h) ≠ DihedralGroup.sr j := by
    intro hsr
    have hz : (1 : ZMod (2 ^ m)) + h = 0 := by
      have hsub : (j + 1 + h) - j = j - j :=
        congrArg (fun z : ZMod (2 ^ m) => z - j) (DihedralGroup.sr.inj hsr)
      simpa [h, add_assoc] using hsub
    have hcast : ((1 + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) =
        (1 : ZMod (2 ^ m)) + h := by
      rw [Nat.cast_add]
      have hp : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = h := by
        simpa [h, Nat.cast_pow]
      simp [hp]
    have hval : (((1 + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)).val = 0) := by
      rw [hcast, hz]
      simp
    have hval' : (((1 + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)).val =
        1 + 2 ^ (m - 1)) := by
      have hlt : 1 + 2 ^ (m - 1) < 2 ^ m := by
        have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
        have htwo : 2 ≤ 2 ^ (m - 1) := by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (m - 1) :=
              Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ m - 1)
        omega
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    have hzero : 1 + 2 ^ (m - 1) = 0 := hval'.symm.trans hval
    have hpos : 0 < 1 + 2 ^ (m - 1) := by positivity
    omega
  have hnotW : DihedralGroup.sr j ∉ W := by
    intro hmem
    rw [mem_dKlein_iff (by omega : 1 ≤ m) (j + 1) (DihedralGroup.sr j)] at hmem
    rcases hmem with hmem1 | hmem2 | hmem3 | hmem4
    · exact (sr_ne_one j) hmem1
    · exact (sr_ne_dCentral j) hmem2
    · exact h1 hmem3.symm
    · exact h2 hmem4.symm
  apply le_bot_iff.mp
  intro x hx
  have hxW : x ∈ W := hx.1
  have hxP : x ∈ Subgroup.zpowers (DihedralGroup.sr j) := hx.2
  rcases Subgroup.mem_zpowers_iff.mp hxP with ⟨k, rfl⟩
  have hk2 : (DihedralGroup.sr j) ^ k = (DihedralGroup.sr j) ^ (k % 2 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, DihedralGroup.orderOf_sr]
    exact (Int.mod_modEq k 2).symm
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · have hx1 : (DihedralGroup.sr j) ^ k = 1 := by
      rw [hk2, hk0, zpow_zero]
    exact hx1 ▸ Subgroup.one_mem ⊥
  · have hxs : (DihedralGroup.sr j) ^ k = DihedralGroup.sr j := by
      rw [hk2, hk1, zpow_one]
    exact False.elim (hnotW (hxs ▸ hxW))

/-- In a finite dihedral `2`-group of order at least eight, every non-central
involution of a Klein-four subgroup generates a cyclic subgroup which is
disjoint from some other Klein-four subgroup. -/
public theorem exists_kleinFour_disjoint_from_noncentral_involution_of_kleinFour
    {K : Type u} [Group K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (e : K ≃* DihedralGroup (2 ^ m))
    (V : Subgroup K) (hV : IsKleinFour V)
    (z : K) (hzV : z ∈ V)
    (hzModel : e z = DihedralGroup.r ((2 : ZMod (2 ^ m)) ^ (m - 1)))
    (u : K) (huV : u ∈ V) (hu : IsInvolution u)
    (huNotCentral : u ≠ z) :
    ∃ W : Subgroup K, IsKleinFour W ∧ W ⊓ Subgroup.zpowers u = ⊥ := by
  classical
  let Vm : Subgroup (DihedralGroup (2 ^ m)) := V.map e.toMonoidHom
  have eVV : V ≃* Vm := V.equivMapOfInjective e.toMonoidHom e.injective
  have hVm : IsKleinFour Vm := {
    card_four := (Nat.card_congr eVV.toEquiv).symm.trans hV.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eVV).symm.trans hV.exponent_two
  }
  have heuV : e u ∈ Vm := Subgroup.mem_map.mpr ⟨u, huV, rfl⟩
  rcases isKleinFour_eq_dKlein hm Vm hVm with ⟨i, hi⟩
  rw [hi, mem_dKlein_iff (by omega : 1 ≤ m) i (e u)] at heuV
  rcases heuV with heu1 | heuC | heui | heuih
  · exfalso
    apply hu.1
    apply e.injective
    simpa using heu1
  · exfalso
    apply huNotCentral
    apply e.injective
    change e u = e z
    rw [heuC, hzModel]
  · let j : ZMod (2 ^ m) := i
    obtain ⟨Wm, hWm, hdisj⟩ :=
      exists_kleinFour_disjoint_from_reflection_zpowers hm j
    let W : Subgroup K := Wm.map e.symm.toMonoidHom
    have eWW : Wm ≃* W :=
      Wm.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have hW : IsKleinFour W := {
      card_four := (Nat.card_congr eWW.toEquiv).symm.trans hWm.card_four
      exponent_two :=
        (Monoid.exponent_eq_of_mulEquiv eWW).symm.trans hWm.exponent_two
    }
    refine ⟨W, hW, ?_⟩
    apply le_bot_iff.mp
    intro x hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hyWm, hyx⟩
    have hxWm : e x ∈ Wm := by
      rw [← hyx]
      simpa using hyWm
    have hxP : e x ∈ Subgroup.zpowers (DihedralGroup.sr j) := by
      rcases Subgroup.mem_zpowers_iff.mp hx.2 with ⟨k, hk⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← congrArg e hk, map_zpow, heui]
    have hxbot : e x ∈ (⊥ : Subgroup (DihedralGroup (2 ^ m))) := by
      have hmem : e x ∈ Wm ⊓ Subgroup.zpowers (DihedralGroup.sr j) :=
        ⟨hxWm, hxP⟩
      rw [hdisj] at hmem
      exact hmem
    have hx1 : x = 1 := by
      apply e.injective
      have h := Subgroup.mem_bot.mp hxbot
      simpa using h
    exact hx1 ▸ Subgroup.one_mem ⊥
  · let j : ZMod (2 ^ m) := i + (2 : ZMod (2 ^ m)) ^ (m - 1)
    obtain ⟨Wm, hWm, hdisj⟩ :=
      exists_kleinFour_disjoint_from_reflection_zpowers hm j
    let W : Subgroup K := Wm.map e.symm.toMonoidHom
    have eWW : Wm ≃* W :=
      Wm.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have hW : IsKleinFour W := {
      card_four := (Nat.card_congr eWW.toEquiv).symm.trans hWm.card_four
      exponent_two :=
        (Monoid.exponent_eq_of_mulEquiv eWW).symm.trans hWm.exponent_two
    }
    refine ⟨W, hW, ?_⟩
    apply le_bot_iff.mp
    intro x hx
    rcases Subgroup.mem_map.mp hx.1 with ⟨y, hyWm, hyx⟩
    have hxWm : e x ∈ Wm := by
      rw [← hyx]
      simpa using hyWm
    have hxP : e x ∈ Subgroup.zpowers (DihedralGroup.sr j) := by
      rcases Subgroup.mem_zpowers_iff.mp hx.2 with ⟨k, hk⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← congrArg e hk, map_zpow, heuih]
    have hxbot : e x ∈ (⊥ : Subgroup (DihedralGroup (2 ^ m))) := by
      have hmem : e x ∈ Wm ⊓ Subgroup.zpowers (DihedralGroup.sr j) :=
        ⟨hxWm, hxP⟩
      rw [hdisj] at hmem
      exact hmem
    have hx1 : x = 1 := by
      apply e.injective
      have h := Subgroup.mem_bot.mp hxbot
      simpa using h
    exact hx1 ▸ Subgroup.one_mem ⊥

private lemma dKlein_eq_dKlein_iff {m : ℕ} (hm : 2 ≤ m) (i j : ZMod (2 ^ m)) :
    dKlein m (by omega : 1 ≤ m) i = dKlein m (by omega : 1 ≤ m) j ↔
      j = i ∨ j = i + (2 : ZMod (2 ^ m)) ^ (m - 1) := by
  classical
  constructor
  · intro h
    have hsr0 : DihedralGroup.sr j ∈ dKlein m (by omega : 1 ≤ m) j :=
      dKlein_sr_mem (by omega : 1 ≤ m) j
    have hsr : DihedralGroup.sr j ∈ dKlein m (by omega : 1 ≤ m) i := by
      rw [← h] at hsr0
      exact hsr0
    rw [mem_dKlein_iff (by omega : 1 ≤ m) i (DihedralGroup.sr j)] at hsr
    rcases hsr with h1 | h2 | h3 | h4
    · cases h1
    · cases h2
    · exact Or.inl (DihedralGroup.sr.inj h3)
    · exact Or.inr (DihedralGroup.sr.inj h4)
  · intro h
    rcases h with rfl | h
    · rfl
    · have hle : dKlein m (by omega : 1 ≤ m) i ≤
        dKlein m (by omega : 1 ≤ m) (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
        intro x hx
        rw [mem_dKlein_iff (by omega : 1 ≤ m) i x] at hx
        rw [mem_dKlein_iff (by omega : 1 ≤ m) (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) x]
        rcases hx with h1 | h2 | h3 | h4
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · right; right; right
          rw [h3]
          congr 1
          rw [add_assoc, half_add_self (by omega : 1 ≤ m), add_zero]
        · exact Or.inr (Or.inr (Or.inl h4))
      rw [h]
      exact Subgroup.eq_of_le_of_card_ge hle (by
        rw [dKlein_card_four (by omega : 1 ≤ m) i,
          dKlein_card_four (by omega : 1 ≤ m) (i + (2 : ZMod (2 ^ m)) ^ (m - 1))])

private lemma dKlein_conj_r {m : ℕ} (hm : 2 ≤ m) (i : ZMod (2 ^ m)) (k : ZMod (2 ^ m)) :
    conjugateSubgroup (dKlein m (by omega : 1 ≤ m) i) (DihedralGroup.r k) =
      dKlein m (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) := by
  ext x
  rw [conjugateSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hx⟩
    rw [mem_dKlein_iff (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) x]
    rw [mem_dKlein_iff (by omega : 1 ≤ m) i y] at hy
    rcases hy with h1 | h2 | h3 | h4
    · left
      rw [← hx, h1]
      simpa [MulAut.conj_apply]
    · right; left
      rw [← hx, h2]
      have hzcomm : DihedralGroup.r k * dCentral m = dCentral m * DihedralGroup.r k := by
        simp [dCentral, DihedralGroup.r_mul_r, add_comm]
      calc
        DihedralGroup.r k * dCentral m * (DihedralGroup.r k)⁻¹ =
            dCentral m * DihedralGroup.r k * (DihedralGroup.r k)⁻¹ := by rw [hzcomm]
        _ = dCentral m := by group
    · right; right; left
      have hx' : x = DihedralGroup.r k * y * (DihedralGroup.r k)⁻¹ := by
        simpa [MulAut.conj_apply] using hx.symm
      rw [hx', h3]
      calc
        DihedralGroup.r k * DihedralGroup.sr i * (DihedralGroup.r k)⁻¹
            = DihedralGroup.sr (i - k) * (DihedralGroup.r k)⁻¹ := by rw [DihedralGroup.r_mul_sr]
        _ = DihedralGroup.sr (i - k) * DihedralGroup.r (-k) := by rw [DihedralGroup.inv_r]
        _ = DihedralGroup.sr (i - k + (-k)) := by rw [DihedralGroup.sr_mul_r]
        _ = DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k) := by
            apply congrArg DihedralGroup.sr
            ring
    · right; right; right
      have hx' : x = DihedralGroup.r k * y * (DihedralGroup.r k)⁻¹ := by
        simpa [MulAut.conj_apply] using hx.symm
      rw [hx', h4]
      calc
        DihedralGroup.r k * DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) * (DihedralGroup.r k)⁻¹
            = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1) - k) * (DihedralGroup.r k)⁻¹ := by rw [DihedralGroup.r_mul_sr]
        _ = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1) - k) * DihedralGroup.r (-k) := by rw [DihedralGroup.inv_r]
        _ = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1) - k + (-k)) := by rw [DihedralGroup.sr_mul_r]
        _ = DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
            apply congrArg DihedralGroup.sr
            ring
  · intro hx
    rw [mem_dKlein_iff (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) x] at hx
    let y0 : DihedralGroup (2 ^ m) := (DihedralGroup.r k)⁻¹ * x * DihedralGroup.r k
    refine ⟨y0, ?_, ?_⟩
    · rw [mem_dKlein_iff (by omega : 1 ≤ m) i y0]
      rcases hx with h1 | h2 | h3 | h4
      · left
        dsimp [y0]
        rw [h1]
        simp
      · right; left
        dsimp [y0]
        rw [h2]
        have hzcomm : DihedralGroup.r k * dCentral m = dCentral m * DihedralGroup.r k := by
          simp [dCentral, DihedralGroup.r_mul_r, add_comm]
        calc
          (DihedralGroup.r k)⁻¹ * dCentral m * DihedralGroup.r k =
              (DihedralGroup.r k)⁻¹ * (DihedralGroup.r k * dCentral m) := by
            rw [hzcomm]
            exact mul_assoc _ _ _
          _ = dCentral m := by group
      · right; right; left
        dsimp [y0]
        rw [h3]
        calc
          (DihedralGroup.r k)⁻¹ * DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k) * DihedralGroup.r k
              = DihedralGroup.r (-k) * DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k) * DihedralGroup.r k := by rw [DihedralGroup.inv_r]
          _ = DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k - (-k)) * DihedralGroup.r k := by rw [DihedralGroup.r_mul_sr]
          _ = DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k - (-k) + k) := by rw [DihedralGroup.sr_mul_r]
          _ = DihedralGroup.sr i := by
              apply congrArg DihedralGroup.sr
              ring
      · right; right; right
        dsimp [y0]
        rw [h4]
        calc
          (DihedralGroup.r k)⁻¹ *
              DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k + (2 : ZMod (2 ^ m)) ^ (m - 1)) *
                DihedralGroup.r k
              = DihedralGroup.r (-k) *
                  DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k + (2 : ZMod (2 ^ m)) ^ (m - 1)) *
                  DihedralGroup.r k := by rw [DihedralGroup.inv_r]
          _ = DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k + (2 : ZMod (2 ^ m)) ^ (m - 1) - (-k)) *
                  DihedralGroup.r k := by rw [DihedralGroup.r_mul_sr]
          _ = DihedralGroup.sr (i - (2 : ZMod (2 ^ m)) * k + (2 : ZMod (2 ^ m)) ^ (m - 1) - (-k) + k) := by rw [DihedralGroup.sr_mul_r]
          _ = DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
              apply congrArg DihedralGroup.sr
              ring
    · change DihedralGroup.r k * y0 * (DihedralGroup.r k)⁻¹ = x
      dsimp [y0]
      change DihedralGroup.r k * ((DihedralGroup.r k)⁻¹ * x * DihedralGroup.r k) * (DihedralGroup.r k)⁻¹ = x
      group

private lemma exists_dKlein_conj_zero_or_one {m : ℕ} (hm : 2 ≤ m) (i : ZMod (2 ^ m)) :
    (∃ k : ZMod (2 ^ m),
        conjugateSubgroup (dKlein m (by omega : 1 ≤ m) i) (DihedralGroup.r k) =
          dKlein m (by omega : 1 ≤ m) 0) ∨
      (∃ k : ZMod (2 ^ m),
        conjugateSubgroup (dKlein m (by omega : 1 ≤ m) i)
            (DihedralGroup.r k) =
          dKlein m (by omega : 1 ≤ m) 1) := by
  rcases i.val.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine ⟨(k : ZMod (2 ^ m)), ?_⟩
    rw [dKlein_conj_r hm i (k : ZMod (2 ^ m))]
    apply (dKlein_eq_dKlein_iff hm (i - (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) 0).mpr
    left
    have hcast : ((2 * k : ℕ) : ZMod (2 ^ m)) =
        (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)) := by
      rw [Nat.cast_mul]
      norm_num
    have hi : i = (2 * k : ℕ) := by
      rw [← ZMod.natCast_zmod_val i, hk]
      ring
    rw [hi, hcast]
    ring_nf
  · right
    refine ⟨(k : ZMod (2 ^ m)), ?_⟩
    rw [dKlein_conj_r hm i (k : ZMod (2 ^ m))]
    apply (dKlein_eq_dKlein_iff hm (i - (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) 1).mpr
    left
    have hcast : ((2 * k + 1 : ℕ) : ZMod (2 ^ m)) =
        (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)) + 1 := by
      rw [Nat.cast_add, Nat.cast_mul]
      norm_num
    have hi : i = (2 * k + 1 : ℕ) := by
      rw [← ZMod.natCast_zmod_val i, hk]
    rw [hi, hcast]
    ring_nf

/-! ## Ambient Klein-four subgroups of a dihedral Sylow `2`-subgroup -/

/-- The ambient image of the model Klein-four subgroup `⟨sr i, dCentral m⟩`
inside a Sylow `2`-subgroup `S`. -/
private abbrev dKleinAmbient
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) : Subgroup G :=
  ((dKlein m hm i).comap e.toMonoidHom).map (S : Subgroup G).subtype

private lemma dKleinAmbient_le_S {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) :
    dKleinAmbient S hm e i ≤ (S : Subgroup G) :=
  Subgroup.map_subtype_le _

private lemma dKleinAmbient_isKleinFour {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) :
    IsKleinFour (dKleinAmbient S hm e i) := by
  classical
  let W : Subgroup G := dKleinAmbient S hm e i
  let Wm : Subgroup (DihedralGroup (2 ^ m)) := dKlein m hm i
  let Bc : Subgroup S := Wm.comap e.toMonoidHom
  let eBW : Bc ≃* Wm :=
    (Bc.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
        e.surjective Wm))
  let eW : Bc ≃* W :=
    Bc.equivMapOfInjective
      (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
  have hWm : IsKleinFour Wm := isKleinFour_dKlein hm i
  have hW : IsKleinFour W := {
    card_four := (Nat.card_congr eW.toEquiv).symm.trans
      ((Nat.card_congr eBW.toEquiv).trans hWm.card_four)
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eW).symm.trans
        ((Monoid.exponent_eq_of_mulEquiv eBW).trans hWm.exponent_two)
  }
  simpa [W, dKleinAmbient] using hW

private lemma dCentralAmbient_mem_dKleinAmbient {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) :
    (e.symm (dCentral m) : G) ∈ dKleinAmbient S hm e i := by
  rw [dKleinAmbient]
  exact Subgroup.mem_map.mpr
    ⟨e.symm (dCentral m), by
      simpa using (show dCentral m ∈ dKlein m hm i from by
        rw [mem_dKlein_iff hm i (dCentral m)]
        exact Or.inr (Or.inl rfl)), rfl⟩

private lemma conjugate_dKleinAmbient_r {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (i k : ZMod (2 ^ m)) :
    conjugateSubgroup (dKleinAmbient S (by omega : 1 ≤ m) e i)
        (e.symm (DihedralGroup.r k) : G) =
      dKleinAmbient S (by omega : 1 ≤ m) e (i - (2 : ZMod (2 ^ m)) * k) := by
  classical
  let K : Subgroup G := dKleinAmbient S (by omega : 1 ≤ m) e i
  let K' : Subgroup G :=
    dKleinAmbient S (by omega : 1 ≤ m) e (i - (2 : ZMod (2 ^ m)) * k)
  let g : G := (e.symm (DihedralGroup.r k) : G)
  ext x
  rw [conjugateSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hx⟩
    rw [dKleinAmbient] at hy
    rcases Subgroup.mem_map.mp hy with ⟨yS, hyS, hyval⟩
    have hgS : (e.symm (DihedralGroup.r k) : G) ∈ (S : Subgroup G) := by
      exact (e.symm (DihedralGroup.r k)).property
    have hyS' : y ∈ (S : Subgroup G) := by
      rw [← hyval]
      exact yS.property
    have hxS : x ∈ (S : Subgroup G) := by
      rw [← hx]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hgS hyS')
        ((S : Subgroup G).inv_mem hgS)
    let xS : S := ⟨x, hxS⟩
    have hxG : g * y * g⁻¹ = x := by
      simpa [g, MulAut.conj_apply] using hx
    have hxS_eq : xS = e.symm (DihedralGroup.r k) * yS *
        (e.symm (DihedralGroup.r k))⁻¹ := by
      apply Subtype.ext
      dsimp [xS, g]
      change x = g * (yS : G) * g⁻¹
      rw [← hyval] at hxG
      exact hxG.symm
    have hxSe : e xS = DihedralGroup.r k * e yS * (DihedralGroup.r k)⁻¹ := by
      have h' := congrArg e hxS_eq
      simpa using h'
    have hyD : e yS ∈ dKlein m (by omega : 1 ≤ m) i := by
      simpa [dKleinAmbient, hyval] using hyS
    have hmem : DihedralGroup.r k * e yS * (DihedralGroup.r k)⁻¹ ∈
        dKlein m (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) := by
      rw [← dKlein_conj_r hm i k]
      exact Subgroup.mem_map.mpr ⟨e yS, hyD, rfl⟩
    rw [dKleinAmbient]
    exact Subgroup.mem_map.mpr ⟨xS, by
      have hxSe' : e xS = DihedralGroup.r k * e yS * DihedralGroup.r (-k) := by
        simpa [DihedralGroup.inv_r] using hxSe
      simpa [dKleinAmbient, ← hxSe'] using hmem, rfl⟩
  · intro hx
    rw [dKleinAmbient, Subgroup.mem_map] at hx
    rcases hx with ⟨xS, hxS, hxval⟩
    have hxSnew : e xS ∈
        dKlein m (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) := by
      simpa [dKleinAmbient, hxval] using hxS
    have hmemModel : e xS ∈
        conjugateSubgroup (dKlein m (by omega : 1 ≤ m) i) (DihedralGroup.r k) := by
      rw [dKlein_conj_r hm i k]
      exact hxSnew
    rw [conjugateSubgroup, Subgroup.mem_map] at hmemModel
    rcases hmemModel with ⟨yD, hyD, hyx⟩
    let yS : S := e.symm yD
    refine ⟨(yS : G), ?_, ?_⟩
    · rw [dKleinAmbient]
      exact Subgroup.mem_map.mpr ⟨yS, by
        simpa [yS] using hyD, rfl⟩
    · have hxS_eq : xS = e.symm (DihedralGroup.r k) * yS *
          (e.symm (DihedralGroup.r k))⁻¹ := by
        have hIm : e xS = e (e.symm (DihedralGroup.r k) * yS *
            (e.symm (DihedralGroup.r k))⁻¹) := by
          calc
            e xS = DihedralGroup.r k * yD * (DihedralGroup.r k)⁻¹ := hyx.symm
            _ = e (e.symm (DihedralGroup.r k) * yS *
                (e.symm (DihedralGroup.r k))⁻¹) := by
              simp [yS]
        exact e.injective hIm
      change g * (yS : G) * g⁻¹ = x
      rw [← hxval]
      exact (congrArg Subtype.val hxS_eq).symm

private lemma isKleinFour_eq_dKleinAmbient {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (Z : Subgroup G) (hZle : Z ≤ (S : Subgroup G)) (hZ : IsKleinFour Z) :
    ∃ i : ZMod (2 ^ m), Z = dKleinAmbient S (by omega : 1 ≤ m) e i := by
  classical
  let ZS : Subgroup S := Z.subgroupOf (S : Subgroup G)
  let W : Subgroup (DihedralGroup (2 ^ m)) := ZS.map e.toMonoidHom
  have eZS : ZS ≃* Z := Subgroup.subgroupOfEquivOfLe hZle
  have eW : ZS ≃* W := ZS.equivMapOfInjective e.toMonoidHom e.injective
  have hZS : IsKleinFour ZS := {
    card_four := (Nat.card_congr eZS.toEquiv).trans hZ.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eZS).trans hZ.exponent_two
  }
  have hW : IsKleinFour W := {
    card_four := (Nat.card_congr eW.toEquiv).symm.trans hZS.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eW).symm.trans hZS.exponent_two
  }
  rcases isKleinFour_eq_dKlein hm W hW with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  have hZeq : Z = (W.comap e.toMonoidHom).map (S : Subgroup G).subtype := by
    calc
      Z = ZS.map (S : Subgroup G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hZle).symm
      _ = (W.comap e.toMonoidHom).map (S : Subgroup G).subtype := by
        congr 1
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        calc
          ZS.map e.toMonoidHom = W := rfl
          _ = (W.comap e.toMonoidHom).map e.toMonoidHom := by
            symm
            exact Subgroup.map_comap_eq_self_of_surjective e.surjective W
  simpa [dKleinAmbient, hi] using hZeq

private lemma exists_conj_dKleinAmbient_zero_or_one {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (Z : Subgroup G) (hZle : Z ≤ (S : Subgroup G)) (hZ : IsKleinFour Z) :
    (∃ g : G, g ∈ (S : Subgroup G) ∧
        conjugateSubgroup Z g = dKleinAmbient S (by omega : 1 ≤ m) e 0) ∨
      (∃ g : G, g ∈ (S : Subgroup G) ∧
        conjugateSubgroup Z g = dKleinAmbient S (by omega : 1 ≤ m) e 1) := by
  rcases isKleinFour_eq_dKleinAmbient S hm e Z hZle hZ with ⟨i, hZi⟩
  rcases exists_dKlein_conj_zero_or_one hm i with h | h
  · rcases h with ⟨k, hk⟩
    left
    refine ⟨(e.symm (DihedralGroup.r k) : G), ?_, ?_⟩
    · exact (e.symm (DihedralGroup.r k)).property
    · rw [hZi, conjugate_dKleinAmbient_r S hm e i k]
      have hEq : dKlein m (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) =
          dKlein m (by omega : 1 ≤ m) 0 := by
        rw [← dKlein_conj_r hm i k]
        exact hk
      simpa [dKleinAmbient] using congrArg
        (fun H : Subgroup (DihedralGroup (2 ^ m)) =>
          (H.comap e.toMonoidHom).map (S : Subgroup G).subtype) hEq
  · rcases h with ⟨k, hk⟩
    right
    refine ⟨(e.symm (DihedralGroup.r k) : G), ?_, ?_⟩
    · exact (e.symm (DihedralGroup.r k)).property
    · rw [hZi, conjugate_dKleinAmbient_r S hm e i k]
      have hEq : dKlein m (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) =
          dKlein m (by omega : 1 ≤ m) 1 := by
        rw [← dKlein_conj_r hm i k]
        exact hk
      simpa [dKleinAmbient] using congrArg
        (fun H : Subgroup (DihedralGroup (2 ^ m)) =>
          (H.comap e.toMonoidHom).map (S : Subgroup G).subtype) hEq

/-! ## Reflection classes and the Grün-kernel fusion classification -/

/-- The `j`-th reflection class of the dihedral model: reflections with index
`j + 2k` (`j = 0` even, `j = 1` odd). -/
private def reflClass (m : ℕ) (j : ZMod (2 ^ m)) : Set (DihedralGroup (2 ^ m)) :=
  {x | ∃ k : ZMod (2 ^ m), x = DihedralGroup.sr (j + (2 : ZMod (2 ^ m)) * k)}

private lemma sr_mem_reflClass_zero_or_one (m : ℕ) (i : ZMod (2 ^ m)) :
    DihedralGroup.sr i ∈ reflClass m 0 ∨ DihedralGroup.sr i ∈ reflClass m 1 := by
  rcases i.val.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine ⟨(k : ZMod (2 ^ m)), ?_⟩
    congr 1
    rw [← ZMod.natCast_zmod_val i, hk]
    push_cast
    ring
  · right
    refine ⟨(k : ZMod (2 ^ m)), ?_⟩
    congr 1
    rw [← ZMod.natCast_zmod_val i, hk]
    push_cast
    ring

private lemma reflClass_zero_union_evenRotations {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    (reflClass m j ∪ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m)))) =
      (dihedralIndexTwoSubgroup m j : Set (DihedralGroup (2 ^ m))) := by
  ext x
  change x ∈ reflClass m j ∪ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) ↔
    x ∈ dihedralIndexTwoSubgroup m j
  rw [mem_dihedralIndexTwoSubgroup_iff hm j x]
  constructor
  · rintro (⟨k, hk⟩ | hxB)
    · right
      refine ⟨k.val, ?_⟩
      rw [hk]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
    · left
      rw [dihedralRotationSubgroup_def] at hxB
      rcases (Subgroup.mem_zpowers_iff.mp hxB) with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk, DihedralGroup.r_zpow]
      congr 1
      norm_num
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · right
      rw [dihedralRotationSubgroup_def]
      norm_num
      change x ∈ Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        rw [DihedralGroup.r_zpow]
        exact hk.symm⟩
    · left
      refine ⟨(k : ZMod (2 ^ m)), hk⟩

private lemma reflClass_eq_sr_mul_evenRotations {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    reflClass m j = {x | ∃ b ∈ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))),
      x = DihedralGroup.sr j * b} := by
  ext x
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨DihedralGroup.r ((2 : ZMod (2 ^ m)) * k), ?_, ?_⟩
    · rw [dihedralRotationSubgroup_def]
      norm_num
      change DihedralGroup.r ((2 : ZMod (2 ^ m)) * k) ∈
        Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k.val, ?_⟩
      rw [DihedralGroup.r_zpow]
      congr 1
      rw [Int.cast_natCast]
      rw [ZMod.natCast_zmod_val]
    · rw [hk, DihedralGroup.sr_mul_r]
  · rintro ⟨b, hb, hx⟩
    rw [dihedralRotationSubgroup_def] at hb
    norm_num at hb
    change b ∈ Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) at hb
    rcases (Subgroup.mem_zpowers_iff.mp hb) with ⟨k, hk⟩
    refine ⟨(k : ZMod (2 ^ m)), ?_⟩
    rw [hx, ← hk, DihedralGroup.r_zpow, DihedralGroup.sr_mul_r]

private lemma r_two_mul_mem_evenRotations_model {m : ℕ} (k : ZMod (2 ^ m)) :
    DihedralGroup.r ((2 : ZMod (2 ^ m)) * k) ∈ dihedralRotationSubgroup m 1 := by
  rw [dihedralRotationSubgroup_def]
  norm_num
  change DihedralGroup.r ((2 : ZMod (2 ^ m)) * k) ∈
    Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k.val, ?_⟩
  rw [DihedralGroup.r_zpow]
  congr 1
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

private lemma reflClass_zero_not_mem_reflClass_one {m : ℕ} (hm : 1 ≤ m) (x : DihedralGroup (2 ^ m)) :
    x ∈ reflClass m 0 → x ∈ reflClass m 1 → False := by
  intro hx0 hx1
  rcases hx0 with ⟨k, hk⟩
  rcases hx1 with ⟨l, hl⟩
  have hij := DihedralGroup.sr.inj (hk.symm.trans hl)
  have h2 : (2 : ZMod (2 ^ m)) * (k - l) = 1 := by
    have hsum : (2 : ZMod (2 ^ m)) * k - (2 : ZMod (2 ^ m)) * l = 1 := by
      calc
        (2 : ZMod (2 ^ m)) * k - (2 : ZMod (2 ^ m)) * l =
            ((0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k) -
              ((1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * l) + 1 := by ring
        _ = 1 := by rw [hij]; ring
    rw [mul_sub]
    exact hsum
  exact zmod_two_mul_ne_one hm (k - l) h2

private lemma two_mul_eq_zero_of_zmod {m : ℕ} (hm : 1 ≤ m) (x : ZMod (2 ^ m)) :
    2 * x = 0 → x = 0 ∨ x = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  intro h
  have hval : ZMod.val (2 * x) = 0 := by
    simpa using congrArg ZMod.val h
  have hnat : (2 * x : ZMod (2 ^ m)) = (((2 * x.val : ℕ) : ZMod (2 ^ m))) := by
    rw [← ZMod.natCast_zmod_val x]
    norm_num
  rw [hnat] at hval
  rw [ZMod.val_natCast] at hval
  have hdvd : 2 ^ m ∣ 2 * x.val := Nat.dvd_iff_mod_eq_zero.mpr hval
  rcases hdvd with ⟨t, ht⟩
  have hlt : 2 * x.val < 2 * 2 ^ m := by
    have hxlt : x.val < 2 ^ m := ZMod.val_lt x
    nlinarith
  have htlt : t < 2 := by
    nlinarith
  interval_cases t
  · left
    have hx0 : x.val = 0 := by nlinarith
    rw [← ZMod.natCast_zmod_val x, hx0]
    norm_num
  · right
    have hmm : 2 * 2 ^ (m - 1) = 2 ^ m := by
      rw [mul_comm, ← pow_succ]
      congr 1
      omega
    have hxpow : x.val = 2 ^ (m - 1) := by
      nlinarith [hmm]
    rw [← ZMod.natCast_zmod_val x, hxpow]

/-- A rotation of order two in a dihedral `2`-group is the central
involution. -/
private lemma rotation_order_two_eq_dCentral {m : ℕ} (hm : 1 ≤ m)
    (i : ZMod (2 ^ m)) (h : orderOf (DihedralGroup.r i) = 2) :
    DihedralGroup.r i = dCentral m := by
  classical
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  have hsq : (DihedralGroup.r i : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
    exact (congrArg (fun n : ℕ => (DihedralGroup.r i) ^ n) h.symm).trans
      (pow_orderOf_eq_one (DihedralGroup.r i))
  have htwo : (2 : ZMod (2 ^ m)) * i = 0 := by
    have hp : (DihedralGroup.r i : DihedralGroup (2 ^ m)) ^ 2 =
        DihedralGroup.r ((2 : ZMod (2 ^ m)) * i) := by
      rw [pow_two, DihedralGroup.r_mul_r]
      congr 1
      ring
    have h0 : DihedralGroup.r ((2 : ZMod (2 ^ m)) * i) = 1 := by
      rw [← hp]
      exact hsq
    have h0' : DihedralGroup.r ((2 : ZMod (2 ^ m)) * i) =
        DihedralGroup.r 0 := by
      rw [DihedralGroup.one_def] at h0
      exact h0
    exact DihedralGroup.r.inj h0'
  have hne : DihedralGroup.r i ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h
    norm_num at h
  rcases two_mul_eq_zero_of_zmod hm i htwo with hi0 | hihalf
  · exfalso
    apply hne
    rw [hi0, DihedralGroup.r_zero]
  · rw [dCentral]
    congr 1
    rw [hihalf]
    norm_num

/-- If two rotations of a dihedral `2`-group have the same order, their
difference is an even rotation. -/
private lemma rotation_sub_mem_even_of_order_eq
    {m : ℕ} (hm : 1 ≤ m) {i j : ZMod (2 ^ m)}
    (h : orderOf (DihedralGroup.r i) = orderOf (DihedralGroup.r j)) :
    DihedralGroup.r (j - i) ∈ dihedralRotationSubgroup m 1 := by
  classical
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  let n : ℕ := 2 ^ m
  have hnpos : 0 < n := by dsimp [n]; positivity
  have h2n : 2 ∣ n := by dsimp [n]; exact pow_dvd_pow 2 (by omega : 1 ≤ m)
  have hord (x : ZMod (2 ^ m)) : orderOf (DihedralGroup.r x) =
      n / n.gcd x.val := by
    dsimp [n]
    rw [DihedralGroup.orderOf_r]
  have hdvd (x : ZMod (2 ^ m)) : n.gcd x.val ∣ n := Nat.gcd_dvd_left n x.val
  have hqpos (x : ZMod (2 ^ m)) : 0 < n / n.gcd x.val := by
    exact Nat.div_pos (Nat.gcd_le_left x.val hnpos)
      (Nat.gcd_pos_of_pos_left x.val hnpos)
  have hq (x : ZMod (2 ^ m)) : n.gcd x.val * (n / n.gcd x.val) = n := by
    have hgpos : 0 < n.gcd x.val := Nat.gcd_pos_of_pos_left x.val hnpos
    have h := (Nat.div_eq_iff_eq_mul_left (a := n) (b := n.gcd x.val)
      (c := n / n.gcd x.val) hgpos (hdvd x)).mp rfl
    simpa [mul_comm] using h.symm
  have hquot_eq : n / n.gcd i.val = n / n.gcd j.val := by
    rw [← hord i, ← hord j, h]
  have hg_eq : n.gcd i.val = n.gcd j.val := by
    have h1 := hq i
    have h2 := hq j
    have h1' : n.gcd i.val * (n / n.gcd j.val) = n := by
      rw [← hquot_eq]
      exact h1
    have hboth : n.gcd i.val * (n / n.gcd j.val) =
        n.gcd j.val * (n / n.gcd j.val) := by
      rw [h1', h2]
    exact Nat.eq_of_mul_eq_mul_left (hqpos j) (by simpa [mul_comm] using hboth)
  have hpar : (2 ∣ i.val) ↔ (2 ∣ j.val) := by
    constructor
    · intro hdiv
      have hdivi : 2 ∣ n.gcd i.val := Nat.dvd_gcd h2n hdiv
      have hdivj : 2 ∣ n.gcd j.val := by rwa [← hg_eq]
      exact hdivj.trans (Nat.gcd_dvd_right n j.val)
    · intro hdiv
      have hdivj : 2 ∣ n.gcd j.val := Nat.dvd_gcd h2n hdiv
      have hdivi : 2 ∣ n.gcd i.val := by rwa [hg_eq]
      exact hdivi.trans (Nat.gcd_dvd_right n i.val)
  rcases i.val.even_or_odd with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hdivj : 2 ∣ j.val := hpar.mp ⟨a, by omega⟩
    have hjeven : Even j.val := even_iff_two_dvd.mpr hdivj
    rcases hjeven with ⟨b, hb⟩
    have hEq : j - i = (2 : ZMod (2 ^ m)) * (b - a) := by
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, ha, hb]
      push_cast
      ring
    rw [hEq]
    exact r_two_mul_mem_evenRotations_model _
  · have hoddj : Odd j.val := by
      have hni : ¬ 2 ∣ i.val := by
        intro hdiv
        rcases hdiv with ⟨c, hc⟩
        rw [ha] at hc
        omega
      have hnj : ¬ 2 ∣ j.val := by
        intro hdiv
        exact hni (hpar.mpr hdiv)
      exact Nat.not_even_iff_odd.mp (fun h => hnj (even_iff_two_dvd.mp h))
    rcases hoddj with ⟨b, hb⟩
    have hEq : j - i = (2 : ZMod (2 ^ m)) * (b - a) := by
      rw [← ZMod.natCast_zmod_val i, ← ZMod.natCast_zmod_val j, ha, hb]
      push_cast
      ring
    rw [hEq]
    exact r_two_mul_mem_evenRotations_model _

/-- Reflections in the same class of a dihedral `2`-group are conjugate. -/
private lemma sameClass_isConj_model {m : ℕ} (i k : ZMod (2 ^ m)) :
    IsConj (DihedralGroup.sr i)
      (DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) * k)) := by
  let t : ZMod (2 ^ m) := -k
  let u : (DihedralGroup (2 ^ m))ˣ :=
    ⟨DihedralGroup.r t, DihedralGroup.r (-t), by
      rw [DihedralGroup.r_mul_r]
      rw [show t + -t = 0 by abel]
      rw [DihedralGroup.r_zero], by
      rw [DihedralGroup.r_mul_r]
      rw [show -t + t = 0 by abel]
      rw [DihedralGroup.r_zero]⟩
  refine ⟨u, ?_⟩
  change DihedralGroup.r t * DihedralGroup.sr i =
    DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) * k) * DihedralGroup.r t
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  congr 1
  change i - t = i + (2 : ZMod (2 ^ m)) * k + t
  dsimp [t]
  ring

/-- Model conjugacy transports through the Sylow equivalence to the ambient
group. -/
private lemma isConj_ambient_of_model_isConj
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) {a b : DihedralGroup (2 ^ m)}
    (h : IsConj a b) :
    IsConj (e.symm a : G) (e.symm b : G) := by
  exact MonoidHom.map_isConj ((S : Subgroup G).subtype.comp e.symm.toMonoidHom) h

/-- The central involution of the model, transported to the ambient Sylow
subgroup. -/
private abbrev zAmbient {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) : G :=
  (e.symm (dCentral m) : G)

/-- The model reflection class whose representative is conjugate to the
central involution. -/
private def fusedClass {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m)) : Prop :=
  IsConj (zAmbient S e) (e.symm (DihedralGroup.sr j) : G)

/-- The model reflections that are conjugate to the central involution. -/
private def fusedReflSet {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) : Set (DihedralGroup (2 ^ m)) :=
  {x | IsConj (zAmbient S e) (e.symm x : G)}

/-- Ambient conjugacy of two Sylow elements implies equal order in the model. -/
private lemma orderOf_eq_of_isConj_ambient
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) {a b : DihedralGroup (2 ^ m)}
    (hconj : IsConj (e.symm a : G) (e.symm b : G)) :
    orderOf a = orderOf b := by
  have hordG : orderOf (e.symm a : G) = orderOf (e.symm b : G) := by
    rcases hconj with ⟨u, hu⟩
    have he : (u : G) * (e.symm a : G) * (u : G)⁻¹ = (e.symm b : G) := by
      rw [hu]
      simp
    let eG : G ≃* G := MulAut.conj (u : G)
    have he' : eG (e.symm a : G) = (e.symm b : G) := by
      change (u : G) * (e.symm a : G) * (u : G)⁻¹ = (e.symm b : G)
      exact he
    calc
      orderOf (e.symm a : G) =
          orderOf (eG (e.symm a : G)) := (MulEquiv.orderOf_eq eG (e.symm a : G)).symm
      _ = orderOf (e.symm b : G) := by rw [he']
  have h1 : orderOf (e.symm a : S) = orderOf a := MulEquiv.orderOf_eq e.symm a
  have h2 : orderOf (e.symm a : G) = orderOf (e.symm a : S) :=
    orderOf_injective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
      (e.symm a)
  have h3 : orderOf (e.symm b : S) = orderOf b := MulEquiv.orderOf_eq e.symm b
  have h4 : orderOf (e.symm b : G) = orderOf (e.symm b : S) :=
    orderOf_injective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
      (e.symm b)
  calc
    orderOf a = orderOf (e.symm a : S) := h1.symm
    _ = orderOf (e.symm a : G) := h2.symm
    _ = orderOf (e.symm b : G) := hordG
    _ = orderOf (e.symm b : S) := h4
    _ = orderOf b := h3

/-- If a reflection is conjugate to the central involution, so is every
reflection in the same class. -/
private lemma isConj_z_sr_of_sameClass
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) {i : ZMod (2 ^ m)}
    (h : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr i) : G))
    (k : ZMod (2 ^ m)) :
    IsConj (zAmbient S e)
      (e.symm (DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) * k)) : G) := by
  exact h.trans (isConj_ambient_of_model_isConj S e
    (sameClass_isConj_model i k))

/-- The difference of two reflections in the same class is an even rotation. -/
private lemma reflection_sub_mem_even_of_same_reflClass
    {m : ℕ} (hm : 1 ≤ m) {i j : ZMod (2 ^ m)}
    (h : (DihedralGroup.sr i ∈ reflClass m 0 ∧
          DihedralGroup.sr j ∈ reflClass m 0) ∨
        (DihedralGroup.sr i ∈ reflClass m 1 ∧
          DihedralGroup.sr j ∈ reflClass m 1)) :
    DihedralGroup.r (j - i) ∈ dihedralRotationSubgroup m 1 := by
  rcases h with ⟨h0i, h0j⟩ | ⟨h1i, h1j⟩
  · rcases h0i with ⟨a, ha⟩
    rcases h0j with ⟨b, hb⟩
    have hEq : j - i = (2 : ZMod (2 ^ m)) * (b - a) := by
      have hi : i = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * a :=
        DihedralGroup.sr.inj ha
      have hj : j = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * b :=
        DihedralGroup.sr.inj hb
      rw [hi, hj]
      ring
    rw [hEq]
    exact r_two_mul_mem_evenRotations_model _
  · rcases h1i with ⟨a, ha⟩
    rcases h1j with ⟨b, hb⟩
    have hEq : j - i = (2 : ZMod (2 ^ m)) * (b - a) := by
      have hi : i = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * a :=
        DihedralGroup.sr.inj ha
      have hj : j = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * b :=
        DihedralGroup.sr.inj hb
      rw [hi, hj]
      ring
    rw [hEq]
    exact r_two_mul_mem_evenRotations_model _

/-- The half rotation is twice an element of `ZMod (2^m)` when `m ≥ 2`. -/
private lemma exists_two_mul_eq_half {m : ℕ} (hm : 2 ≤ m) :
    ∃ k : ZMod (2 ^ m),
      (2 : ZMod (2 ^ m)) ^ (m - 1) = (2 : ZMod (2 ^ m)) * k := by
  refine ⟨((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)), ?_⟩
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    calc
      2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by congr 1; omega
      _ = 2 ^ (m - 2) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (m - 2) := by rw [mul_comm]
  have hcast : (2 : ZMod (2 ^ m)) ^ (m - 1) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [Nat.cast_pow]
    norm_num
  rw [hcast]
  rw [hpow]
  norm_num

/-- The index of the central involution is twice an element. -/
private lemma dCentral_index_eq_two_mul {m : ℕ} (hm : 2 ≤ m)
    (i : ZMod (2 ^ m)) (h : DihedralGroup.r i = dCentral m) :
    ∃ k : ZMod (2 ^ m), i = (2 : ZMod (2 ^ m)) * k := by
  rcases exists_two_mul_eq_half hm with ⟨k, hk⟩
  have hi : i = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
    apply DihedralGroup.r.inj
    rw [h]
  refine ⟨k, ?_⟩
  rw [hi, hk]

/-- A rotation moving one reflection class to the other in the dihedral
model: if `2k` is the half-rotation, conjugation by `r k` sends `sr i` to
`sr (i + half)`. -/
private lemma r_k_conj_sr_i {m : ℕ} (hm : 2 ≤ m) (i k : ZMod (2 ^ m))
    (hk : (2 : ZMod (2 ^ m)) * k = (2 : ZMod (2 ^ m)) ^ (m - 1)) :
    DihedralGroup.r k * DihedralGroup.sr i * (DihedralGroup.r k)⁻¹ =
      DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
  congr 1
  have hk2 : -((2 : ZMod (2 ^ m)) * k) = (2 : ZMod (2 ^ m)) * k := by
    rw [hk]
    exact half_neg (by omega : 1 ≤ m)
  ring_nf
  rw [mul_comm]
  rw [← hk]
  simp only [sub_eq_add_neg]
  rw [hk2]

/-- The inverse of the previous calculation: conjugation by the same
rotation sends `sr (i + half)` back to `sr i`. -/
private lemma r_k_conj_sr_i_half {m : ℕ} (hm : 2 ≤ m) (i k : ZMod (2 ^ m))
    (hk : (2 : ZMod (2 ^ m)) * k = (2 : ZMod (2 ^ m)) ^ (m - 1)) :
    DihedralGroup.r k *
        DihedralGroup.sr (i + (2 : ZMod (2 ^ m)) ^ (m - 1)) *
          (DihedralGroup.r k)⁻¹ =
      DihedralGroup.sr i := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
  congr 1
  ring_nf
  rw [mul_comm]
  rw [← hk]
  ring

/-- Rotations of the dihedral model centralize the central involution. -/
private lemma r_k_centralizes_dCentral {m : ℕ} (hm : 2 ≤ m) (k : ZMod (2 ^ m)) :
    DihedralGroup.r k * dCentral m * (DihedralGroup.r k)⁻¹ = dCentral m := by
  have hcomm : DihedralGroup.r k * dCentral m =
      dCentral m * DihedralGroup.r k := by
    simp [dCentral, DihedralGroup.r_mul_r, add_comm]
  calc
    DihedralGroup.r k * dCentral m * (DihedralGroup.r k)⁻¹ =
        dCentral m * DihedralGroup.r k * (DihedralGroup.r k)⁻¹ := by
      rw [hcomm]
    _ = dCentral m := by group

/-- Every Klein-four subgroup of a dihedral Sylow `2`-subgroup of order at
least eight contains a rotation of the Sylow subgroup which fixes the central
involution and swaps the two non-central involutions of the Klein four. -/
private lemma exists_dihedral_transposition_of_kleinFour_le_sylow
    {G : Type u} [Group G] (P : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : P ≃* DihedralGroup (2 ^ m))
    {W : Subgroup G} (hWle : W ≤ (P : Subgroup G)) (hW : IsKleinFour W) :
    ∃ τ : G, τ ∈ (P : Subgroup G) ∧
      τ ∈ Subgroup.normalizer (W : Set G) ∧
      τ * zAmbient P e * τ⁻¹ = zAmbient P e ∧
      (∀ U : Subgroup G, U ≤ (P : Subgroup G) → IsKleinFour U →
        ∀ x : G, x ∈ U → x ≠ 1 → x ≠ zAmbient P e → τ * x * τ⁻¹ ≠ x) ∧
      (∀ U : Subgroup G, U ≤ (P : Subgroup G) → IsKleinFour U →
        τ ∈ Subgroup.normalizer (U : Set G)) := by
  classical
  rcases isKleinFour_eq_dKleinAmbient P hm e W hWle hW with ⟨i, hWi⟩
  rcases exists_two_mul_eq_half hm with ⟨k, hk⟩
  have hk' : (2 : ZMod (2 ^ m)) * k = (2 : ZMod (2 ^ m)) ^ (m - 1) := hk.symm
  let τ : G := (e.symm (DihedralGroup.r k) : G)
  have hτP : τ ∈ (P : Subgroup G) := (e.symm (DihedralGroup.r k)).property
  have hEqModel : dKlein m (by omega : 1 ≤ m) (i - (2 : ZMod (2 ^ m)) * k) =
      dKlein m (by omega : 1 ≤ m) i := by
    apply (dKlein_eq_dKlein_iff hm (i - (2 : ZMod (2 ^ m)) * k) i).mpr
    right
    rw [← hk']
    ring
  have hconjW : conjugateSubgroup W τ = W := by
    rw [hWi, conjugate_dKleinAmbient_r P hm e i k]
    apply congrArg (fun H : Subgroup (DihedralGroup (2 ^ m)) =>
      (H.comap e.toMonoidHom).map (P : Subgroup G).subtype) hEqModel
  have hτN : τ ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [conjugateSubgroup] using hconjW
  have hτAll : ∀ U : Subgroup G, U ≤ (P : Subgroup G) → IsKleinFour U →
      τ ∈ Subgroup.normalizer (U : Set G) := by
    intro U hUle hU
    rcases isKleinFour_eq_dKleinAmbient P hm e U hUle hU with ⟨j, hUj⟩
    have hEqU : dKlein m (by omega : 1 ≤ m) (j - (2 : ZMod (2 ^ m)) * k) =
        dKlein m (by omega : 1 ≤ m) j := by
      apply (dKlein_eq_dKlein_iff hm (j - (2 : ZMod (2 ^ m)) * k) j).mpr
      right
      rw [← hk']
      ring
    have hconjU : conjugateSubgroup U τ = U := by
      rw [hUj, conjugate_dKleinAmbient_r P hm e j k]
      apply congrArg (fun H : Subgroup (DihedralGroup (2 ^ m)) =>
        (H.comap e.toMonoidHom).map (P : Subgroup G).subtype) hEqU
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [conjugateSubgroup] using hconjU
  have hfix : τ * zAmbient P e * τ⁻¹ = zAmbient P e := by
    have hP : (e.symm (DihedralGroup.r k) : P) *
          (e.symm (dCentral m) : P) *
            (e.symm (DihedralGroup.r k) : P)⁻¹ =
        (e.symm (dCentral m) : P) := by
      apply e.injective
      simp [r_k_centralizes_dCentral hm k]
    dsimp [τ, zAmbient]
    exact congrArg (fun y : P => (y : G)) hP
  have hmoveAll : ∀ U : Subgroup G, U ≤ (P : Subgroup G) → IsKleinFour U →
      ∀ x : G, x ∈ U → x ≠ 1 → x ≠ zAmbient P e → τ * x * τ⁻¹ ≠ x := by
    intro U hUle hU x hxU hx1 hxz
    rcases isKleinFour_eq_dKleinAmbient P hm e U hUle hU with ⟨j, hUj⟩
    rw [hUj] at hxU
    rcases Subgroup.mem_map.mp hxU with ⟨xP, hxP, hxval⟩
    let xM : DihedralGroup (2 ^ m) := e xP
    have hxM : xM ∈ dKlein m (by omega : 1 ≤ m) j := by
      simpa [dKleinAmbient, xM, hxval] using hxP
    have hτx : τ * x * τ⁻¹ =
        (e.symm (DihedralGroup.r k * xM * (DihedralGroup.r k)⁻¹) : G) := by
      have hP : (e.symm (DihedralGroup.r k) : P) * xP *
            (e.symm (DihedralGroup.r k) : P)⁻¹ =
          (e.symm (DihedralGroup.r k * xM * (DihedralGroup.r k)⁻¹) : P) := by
        apply e.injective
        simp [xM]
      rw [← hxval]
      dsimp [τ, xM]
      exact congrArg (fun y : P => (y : G)) hP
    rw [mem_dKlein_iff (by omega : 1 ≤ m) j xM] at hxM
    rcases hxM with h1 | h2 | h3 | h4
    · exfalso
      apply hx1
      have hxM1 : xM = 1 := h1
      have hxP1 : xP = 1 := by
        apply e.injective
        simpa [xM, hxM1]
      simpa [hxP1] using hxval.symm
    · exfalso
      apply hxz
      have hxM2 : xM = dCentral m := h2
      have hxP2 : xP = e.symm (dCentral m) := by
        apply e.injective
        simpa [xM, hxM2]
      simpa [zAmbient, hxP2] using hxval.symm
    · intro hEq
      have hτx' : τ * x * τ⁻¹ =
          (e.symm (DihedralGroup.sr
            (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) := by
        rw [hτx, h3, r_k_conj_sr_i hm j k hk']
      have hx_eq : x = (e.symm (DihedralGroup.sr j) : G) := by
        rw [← hxval]
        have hxP : xP = e.symm (DihedralGroup.sr j) := by
          apply e.injective
          simpa [xM, h3]
        simpa [hxP]
      have hM : DihedralGroup.sr (j + (2 : ZMod (2 ^ m)) ^ (m - 1)) =
          DihedralGroup.sr j := by
        have hG : (e.symm (DihedralGroup.sr
              (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) =
            (e.symm (DihedralGroup.sr j) : G) := by
          rw [← hτx', hEq, hx_eq]
        have hP : (e.symm (DihedralGroup.sr
              (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : P) =
            (e.symm (DihedralGroup.sr j) : P) := by
          apply Subtype.ext
          exact hG
        exact e.symm.injective hP
      exact sr_half_ne_sr (by omega : 1 ≤ m) j hM
    · intro hEq
      have hτx' : τ * x * τ⁻¹ =
          (e.symm (DihedralGroup.sr j) : G) := by
        rw [hτx, h4, r_k_conj_sr_i_half hm j k hk']
      have hx_eq : x = (e.symm (DihedralGroup.sr
          (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) := by
        rw [← hxval]
        have hxP : xP = e.symm (DihedralGroup.sr
            (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) := by
          apply e.injective
          simpa [xM, h4]
        simpa [hxP]
      have hM : DihedralGroup.sr j =
          DihedralGroup.sr (j + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by
        have hG : (e.symm (DihedralGroup.sr j) : G) =
            (e.symm (DihedralGroup.sr
              (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) := by
          rw [← hτx', hEq, hx_eq]
        have hP : (e.symm (DihedralGroup.sr j) : P) =
            (e.symm (DihedralGroup.sr
              (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : P) := by
          apply Subtype.ext
          exact hG
        exact e.symm.injective hP
      exact (sr_half_ne_sr (by omega : 1 ≤ m) j).symm hM
  exact ⟨τ, hτP, hτN, hfix, hmoveAll, hτAll⟩

/-- Membership in a conjugate subgroup is explicit conjugation. -/
private lemma mem_conjugateSubgroup_iff {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (x : G) :
    x ∈ conjugateSubgroup H g ↔ ∃ h ∈ H, x = g * h * g⁻¹ := by
  constructor
  · intro hx
    rcases (show x ∈ H.map (MulAut.conj g).toMonoidHom from by
      simpa [conjugateSubgroup] using hx) with ⟨h, hh, hval⟩
    refine ⟨h, hh, ?_⟩
    simpa [MulAut.conj_apply] using hval.symm
  · rintro ⟨h, hh, hx⟩
    rw [conjugateSubgroup, Subgroup.mem_map]
    refine ⟨h, hh, ?_⟩
    simpa [MulAut.conj_apply] using hx.symm

/-- Conjugating a conjugate subgroup by a second element is conjugation by
the product. -/
private lemma conjugateSubgroup_conjugateSubgroup {G : Type u} [Group G]
    (H : Subgroup G) (a b : G) :
    conjugateSubgroup (conjugateSubgroup H a) b =
      conjugateSubgroup H (b * a) := by
  ext x
  rw [mem_conjugateSubgroup_iff, mem_conjugateSubgroup_iff]
  constructor
  · rintro ⟨y, hy, hx⟩
    rcases (mem_conjugateSubgroup_iff H a y).mp hy with ⟨h, hh, hy⟩
    refine ⟨h, hh, ?_⟩
    rw [hx, hy]
    group
  · rintro ⟨h, hh, hx⟩
    refine ⟨a * h * a⁻¹, ?_, ?_⟩
    · exact (mem_conjugateSubgroup_iff H a (a * h * a⁻¹)).mpr ⟨h, hh, rfl⟩
    · rw [hx]
      group

/-- Conjugation by the identity is the identity on subgroups. -/
private lemma conjugateSubgroup_one {G : Type u} [Group G] (H : Subgroup G) :
    conjugateSubgroup H 1 = H := by
  ext x
  rw [mem_conjugateSubgroup_iff]
  constructor
  · rintro ⟨h, hh, hx⟩
    rw [hx]
    simpa using hh
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- Conjugation preserves the Klein-four property. -/
private lemma isKleinFour_conjugateSubgroup {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (hH : IsKleinFour H) :
    IsKleinFour (conjugateSubgroup H g) := by
  classical
  let eH : H ≃* conjugateSubgroup H g :=
    H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact {
    card_four := (Nat.card_congr eH.toEquiv).symm.trans hH.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eH).symm.trans hH.exponent_two
  }

/-- In a Klein-four subgroup, an automorphism which fixes one nonidentity
element and moves another sends the moved element to the product of the two. -/
private lemma kleinFour_action_fix_move
    {G : Type u} [Group G] (Z : Subgroup G) (hZ : IsKleinFour Z)
    {x y δ : G} (hxZ : x ∈ Z) (hyZ : y ∈ Z)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hδN : δ ∈ Subgroup.normalizer (Z : Set G))
    (hδx : δ * x * δ⁻¹ = x) (hδy : δ * y * δ⁻¹ ≠ y) :
    δ * y * δ⁻¹ = x * y := by
  classical
  have hbZ : δ * y * δ⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp hδN y).1 hyZ
  have hb1 : δ * y * δ⁻¹ ≠ 1 := by
    intro h
    apply hy1
    calc
      y = δ⁻¹ * (δ * y * δ⁻¹) * δ := by group
      _ = 1 := by rw [h]; simp
  have hbx : δ * y * δ⁻¹ ≠ x := by
    intro h
    apply hxy
    have hx' : δ⁻¹ * x * δ = x := by
      calc
        δ⁻¹ * x * δ = δ⁻¹ * (δ * x * δ⁻¹) * δ := by rw [hδx]
        _ = x := by group
    have hxy' : x = y := by
      calc
        x = δ⁻¹ * x * δ := hx'.symm
        _ = δ⁻¹ * (δ * y * δ⁻¹) * δ := by rw [← h]
        _ = y := by group
    exact hxy'
  let : IsKleinFour Z := hZ
  let xZ : Z := ⟨x, hxZ⟩
  let yZ : Z := ⟨y, hyZ⟩
  let bZ : Z := ⟨δ * y * δ⁻¹, hbZ⟩
  have hb1' : bZ ≠ 1 := by
    intro h
    apply hb1
    exact congrArg Subtype.val h
  have hbx' : bZ ≠ xZ := by
    intro h
    apply hbx
    exact congrArg Subtype.val h
  have hby' : bZ ≠ yZ := by
    intro h
    apply hδy
    exact congrArg Subtype.val h
  have hEq : bZ = xZ * yZ :=
    IsKleinFour.eq_mul_of_ne_all (x := xZ) (y := yZ) (z := bZ)
      (by
        intro h
        apply hx1
        exact congrArg Subtype.val h)
      (by
        intro h
        apply hy1
        exact congrArg Subtype.val h)
      (by
        intro h
        apply hxy
        exact congrArg Subtype.val h)
      hb1' hbx' hby'
  exact congrArg Subtype.val hEq

/-- Two transpositions on the three nonidentity elements of a Klein-four
subgroup generate the full action, so their product lies outside `C'(Z)`. -/
private lemma normalizerContainsCPrime_of_two_transpositions
    {G : Type u} [Group G] (Z : Subgroup G) (hZ : IsKleinFour Z)
    {z a γ γ' : G} (hzZ : z ∈ Z) (haZ : a ∈ Z)
    (hz1 : z ≠ 1) (ha1 : a ≠ 1) (hza : z ≠ a)
    (hγN : γ ∈ Subgroup.normalizer (Z : Set G))
    (hγ'N : γ' ∈ Subgroup.normalizer (Z : Set G))
    (hγz : γ * z * γ⁻¹ = z) (hγa : γ * a * γ⁻¹ = z * a)
    (hγ'a : γ' * a * γ'⁻¹ = a) (hγ'z : γ' * z * γ'⁻¹ = z * a) :
    NormalizerContainsCPrime Z := by
  classical
  let ρ : G := γ * γ'
  have hρN : ρ ∈ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normalizer (Z : Set G)).mul_mem hγN hγ'N
  have hz2 : z * z = 1 := by
    let : IsKleinFour Z := hZ
    have h := IsKleinFour.mul_self (⟨z, hzZ⟩ : Z)
    exact congrArg Subtype.val h
  have hγza : γ * (z * a) * γ⁻¹ = a := by
    calc
      γ * (z * a) * γ⁻¹ = (γ * z * γ⁻¹) * (γ * a * γ⁻¹) := by group
      _ = z * (z * a) := by rw [hγz, hγa]
      _ = a := by
        calc
          z * (z * a) = (z * z) * a := by rw [mul_assoc]
          _ = a := by rw [hz2, one_mul]
  have hρz : ρ * z * ρ⁻¹ = a := by
    calc
      ρ * z * ρ⁻¹ = γ * (γ' * z * γ'⁻¹) * γ⁻¹ := by dsimp [ρ]; group
      _ = γ * (z * a) * γ⁻¹ := by rw [hγ'z]
      _ = a := hγza
  have hρa : ρ * a * ρ⁻¹ = z * a := by
    calc
      ρ * a * ρ⁻¹ = γ * (γ' * a * γ'⁻¹) * γ⁻¹ := by dsimp [ρ]; group
      _ = γ * a * γ⁻¹ := by rw [hγ'a]
      _ = z * a := hγa
  have hne : z * a ≠ z := by
    intro h
    apply ha1
    calc
      a = z⁻¹ * (z * a) := by group
      _ = z⁻¹ * z := by rw [h]
      _ = 1 := by group
  have hρ2 : ρ ^ 2 * z * (ρ ^ 2)⁻¹ = z * a := by
    calc
      ρ ^ 2 * z * (ρ ^ 2)⁻¹ = ρ * (ρ * z * ρ⁻¹) * ρ⁻¹ := by
        rw [pow_two, mul_inv_rev]
        group
      _ = ρ * a * ρ⁻¹ := by rw [hρz]
      _ = z * a := hρa
  have hnotC : ρ ∉ cPrime Z := by
    intro hc
    have hcentral : ρ ^ 2 ∈ Subgroup.centralizer (Z : Set G) := hc.2
    have hcomm : z * (ρ ^ 2) = (ρ ^ 2) * z :=
      Subgroup.mem_centralizer_iff.mp hcentral z hzZ
    have hfix : ρ ^ 2 * z * (ρ ^ 2)⁻¹ = z := by
      rw [← hcomm]
      group
    rw [hρ2] at hfix
    exact hne hfix
  have hsub : cPrime Z ⊆ (Subgroup.normalizer (Z : Set G) : Set G) := by
    intro x hx
    exact hx.1
  have hnotsub : ¬ (Subgroup.normalizer (Z : Set G) : Set G) ⊆ cPrime Z := by
    intro hsub'
    exact hnotC (hsub' hρN)
  exact ⟨hsub, hnotsub⟩

/-- `NormalizerContainsCPrime` is equivalent to the existence of a normalizer
element whose square does not centralize the subgroup. -/
private lemma normalizerContainsCPrime_iff_exists
    {G : Type u} [Group G] (Z : Subgroup G) :
    NormalizerContainsCPrime Z ↔
      ∃ n : G, n ∈ Subgroup.normalizer (Z : Set G) ∧
        n ^ 2 ∉ Subgroup.centralizer (Z : Set G) := by
  constructor
  · intro h
    rcases h with ⟨hsub, hnotsub⟩
    by_contra hnone
    apply hnotsub
    intro n hn
    have hc : n ^ 2 ∈ Subgroup.centralizer (Z : Set G) := by
      by_contra hsq
      exact hnone ⟨n, hn, hsq⟩
    exact ⟨hn, hc⟩
  · rintro ⟨n, hn, hsq⟩
    have hsub : cPrime Z ⊆ (Subgroup.normalizer (Z : Set G) : Set G) := by
      intro x hx
      exact hx.1
    have hnotsub : ¬ (Subgroup.normalizer (Z : Set G) : Set G) ⊆ cPrime Z := by
      intro hsub'
      exact hsq (hsub' hn).2
    exact ⟨hsub, hnotsub⟩

/-- Conjugacy preserves the strict `C'(Z)` containment property. -/
private lemma normalizerContainsCPrime_conjugate
    {G : Type u} [Group G] (Z W : Subgroup G) (g : G)
    (h : conjugateSubgroup Z g = W) :
    NormalizerContainsCPrime Z ↔ NormalizerContainsCPrime W := by
  classical
  have forward : ∀ {A B : Subgroup G} (k : G)
      (hk : conjugateSubgroup A k = B),
      NormalizerContainsCPrime A → NormalizerContainsCPrime B := by
    intro A B k hk hA
    rcases (normalizerContainsCPrime_iff_exists A).mp hA with ⟨n, hn, hsq⟩
    let m : G := k * n * k⁻¹
    have hnsub : conjugateSubgroup A n = A := by
      have hmap := (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := n)).mp hn
      simpa [conjugateSubgroup] using hmap
    have hmN : m ∈ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        conjugateSubgroup B m =
            conjugateSubgroup (conjugateSubgroup A k) m := by rw [hk]
        _ = conjugateSubgroup A (m * k) := conjugateSubgroup_conjugateSubgroup A k m
        _ = conjugateSubgroup A (k * n) := by
          congr 1
          dsimp [m]
          group
        _ = conjugateSubgroup (conjugateSubgroup A n) k :=
          (conjugateSubgroup_conjugateSubgroup A n k).symm
        _ = conjugateSubgroup A k := by rw [hnsub]
        _ = B := hk
    have hmC : m ^ 2 ∉ Subgroup.centralizer (B : Set G) := by
      intro hc
      apply hsq
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hb : k * a * k⁻¹ ∈ B := by
        rw [← hk, mem_conjugateSubgroup_iff]
        exact ⟨a, ha, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hc (k * a * k⁻¹) hb
      have h1 : k * (n ^ 2 * a) * k⁻¹ = k * (a * n ^ 2) * k⁻¹ := by
        have hm2 : m ^ 2 = k * n ^ 2 * k⁻¹ := by
          dsimp [m]
          calc
            (k * n * k⁻¹) ^ 2 = k * n * n * k⁻¹ := by
              rw [pow_two]
              group
            _ = k * (n * n) * k⁻¹ := by group
            _ = k * n ^ 2 * k⁻¹ := by rw [← pow_two]
        calc
          k * (n ^ 2 * a) * k⁻¹ = (k * n ^ 2 * k⁻¹) * (k * a * k⁻¹) := by group
          _ = m ^ 2 * (k * a * k⁻¹) := by rw [hm2]
          _ = (k * a * k⁻¹) * m ^ 2 := hcomm.symm
          _ = k * (a * n ^ 2) * k⁻¹ := by
            rw [hm2]
            group
      calc
        a * n ^ 2 = k⁻¹ * (k * (a * n ^ 2) * k⁻¹) * k := by group
        _ = k⁻¹ * (k * (n ^ 2 * a) * k⁻¹) * k := by rw [← h1]
        _ = n ^ 2 * a := by group
    exact (normalizerContainsCPrime_iff_exists B).mpr ⟨m, hmN, hmC⟩
  constructor
  · exact forward g h
  · intro hW
    have h' : conjugateSubgroup W g⁻¹ = Z := by
      calc
        conjugateSubgroup W g⁻¹ =
            conjugateSubgroup (conjugateSubgroup Z g) g⁻¹ := by rw [h]
        _ = conjugateSubgroup Z (g⁻¹ * g) := conjugateSubgroup_conjugateSubgroup Z g g⁻¹
        _ = conjugateSubgroup Z 1 := by congr 1; group
        _ = Z := conjugateSubgroup_one Z
    exact forward g⁻¹ h' hW

/-- The central involution of a dihedral Sylow subgroup is not the identity. -/
private lemma zAmbient_ne_one {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) :
    zAmbient S e ≠ 1 := by
  intro h
  have hordS : orderOf (e.symm (dCentral m) : S) = orderOf (dCentral m) :=
    MulEquiv.orderOf_eq e.symm (dCentral m)
  have h2 : orderOf (zAmbient S e) =
      orderOf (e.symm (dCentral m) : S) := by
    have hsub := orderOf_injective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective (e.symm (dCentral m))
    simpa [zAmbient] using hsub
  have hordG : orderOf (zAmbient S e) = 2 := by
    calc
      orderOf (zAmbient S e) = orderOf (e.symm (dCentral m) : S) := h2
      _ = orderOf (dCentral m) := hordS
      _ = 2 := dCentral_order_two hm
  rw [h, orderOf_one] at hordG
  norm_num at hordG

/-- The central involution of a dihedral Sylow subgroup is central there. -/
private lemma zAmbient_mem_center {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) :
    (e.symm (dCentral m) : S) ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro s
  apply e.injective
  simpa [zAmbient] using
    (Subgroup.mem_center_iff.mp (dCentral_mem_center hm) (e s))

/-- Centralizer Sylow alignment: if `σ` carries the central involution of `S`
to `a`, then after left multiplication by a suitable element of `C_G(a)`
the conjugate Sylow subgroup contains the given Klein-four `Z`. -/
private lemma exists_centralizer_sylow_alignment
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    {Z : Subgroup G} (hZle : Z ≤ (S : Subgroup G)) (hZ : IsKleinFour Z)
    {a : G} (haZ : a ∈ Z) (σ : G)
    (hσ : σ * zAmbient S e * σ⁻¹ = a) :
    ∃ μ : G, μ ∈ Subgroup.centralizer ({a} : Set G) ∧
      Z ≤ conjugateSubgroup S (μ * σ) := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
  have hZleH : Z ≤ H := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    let : IsKleinFour Z := hZ
    have hxZ : (⟨x, hx⟩ : Z) * ⟨a, haZ⟩ = ⟨a, haZ⟩ * ⟨x, hx⟩ :=
      (IsKleinFour.isMulCommutative (G := Z)).is_comm.comm _ _
    exact (congrArg Subtype.val hxZ).symm
  have hZcard : Nat.card (Z.subgroupOf H) = 4 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleH).toEquiv).trans
      hZ.card_four
  have hZpH : IsPGroup 2 (Z.subgroupOf H) := IsPGroup.of_card (n := 2) hZcard
  obtain ⟨Q, hZQ⟩ := IsPGroup.exists_le_sylow (p := 2) (G := H) hZpH
  let P0 : Sylow 2 G := σ • S
  have hzS : (e.symm (dCentral m) : S) ∈ Subgroup.center S :=
    zAmbient_mem_center S hm e
  have hP0def : (P0 : Subgroup G) = conjugateSubgroup S σ := by
    dsimp [P0]
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hσz : σ⁻¹ * a * σ = zAmbient S e := by
    calc
      σ⁻¹ * a * σ = σ⁻¹ * (σ * zAmbient S e * σ⁻¹) * σ := by rw [hσ]
      _ = zAmbient S e := by group
  have hP0H : (P0 : Subgroup G) ≤ H := by
    intro x hx
    rw [hP0def, mem_conjugateSubgroup_iff] at hx
    rcases hx with ⟨s, hs, hx⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    have hzcomm : (s : G) * zAmbient S e = zAmbient S e * (s : G) :=
      by
        have h := congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hzS ⟨s, hs⟩)
        simpa [zAmbient] using h
    calc
      a * x = a * (σ * (s : G) * σ⁻¹) := by rw [hx]
      _ =
          (σ * zAmbient S e * σ⁻¹) * (σ * (s : G) * σ⁻¹) := by rw [← hσ]
      _ = σ * (zAmbient S e * (s : G)) * σ⁻¹ := by group
      _ = σ * ((s : G) * zAmbient S e) * σ⁻¹ := by rw [hzcomm]
      _ = (σ * (s : G) * σ⁻¹) * (σ * zAmbient S e * σ⁻¹) := by group
      _ = (σ * (s : G) * σ⁻¹) * a := by rw [hσ]
      _ = x * a := by rw [hx]
  let P0H : Sylow 2 H := P0.subtype hP0H
  obtain ⟨μH, hμ⟩ := MulAction.exists_smul_eq H P0H Q
  let μ : G := (μH : H)
  have hμsubH : conjugateSubgroup (P0H : Subgroup H) (μH : H) =
      (Q : Subgroup H) := by
    have hsmul := Sylow.coe_subgroup_smul (P := P0H) (g := μH)
    rw [hμ] at hsmul
    change (P0H : Subgroup H).map (MulAut.conj (μH : H)).toMonoidHom =
      (Q : Subgroup H)
    exact hsmul.symm
  have hP0map : (P0H : Subgroup H).map H.subtype = (P0 : Subgroup G) :=
    Subgroup.map_subgroupOf_eq_of_le hP0H
  have hcomp : (MulAut.conj μ).toMonoidHom.comp H.subtype =
      H.subtype.comp (MulAut.conj (μH : H)).toMonoidHom := by
    ext h
    simp [μ, MulAut.conj_apply]
  have hconjP0 : conjugateSubgroup P0 μ = (Q : Subgroup H).map H.subtype := by
    calc
      conjugateSubgroup P0 μ = P0.map (MulAut.conj μ).toMonoidHom := rfl
      _ = (P0H : Subgroup H).map
          (H.subtype.comp (MulAut.conj (μH : H)).toMonoidHom) := by
        rw [← hP0map]
        rw [Subgroup.map_map]
        rw [hcomp]
      _ = ((P0H : Subgroup H).map
          (MulAut.conj (μH : H)).toMonoidHom).map H.subtype := by
        rw [← Subgroup.map_map]
      _ = (conjugateSubgroup (P0H : Subgroup H) (μH : H)).map H.subtype := rfl
      _ = (Q : Subgroup H).map H.subtype := by rw [hμsubH]
  have hZQmap : Z ≤ (Q : Subgroup H).map H.subtype := by
    intro x hx
    have hxH : x ∈ H := hZleH hx
    have hxZH : (⟨x, hxH⟩ : H) ∈ Z.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hZQ hxZH, rfl⟩
  have hZP0μ : Z ≤ conjugateSubgroup P0 μ := by
    rw [hconjP0]
    exact hZQmap
  have hZS' : Z ≤ conjugateSubgroup S (μ * σ) := by
    calc
      Z ≤ conjugateSubgroup P0 μ := hZP0μ
      _ = conjugateSubgroup (conjugateSubgroup S σ) μ := by rw [hP0def]
      _ = conjugateSubgroup S (μ * σ) := conjugateSubgroup_conjugateSubgroup S σ μ
  exact ⟨μ, μH.property, hZS'⟩

/-- The local transfer step of Gorenstein--Walter 1962, Lemma 8: if a
non-central involution `a` of a Klein-four subgroup `Z ≤ S` is conjugate to
the central involution `z` of the dihedral Sylow subgroup `S`, then some
normalizer element of `Z` moves `z`.  The conjugator carries `Z` to a
Klein-four subgroup of a conjugate Sylow subgroup in which `z` itself is a
non-central involution; the transposition of that Klein four inside the
conjugate Sylow subgroup, conjugated back, is the required normalizer
element. -/
private lemma fusion_to_normalizer_moves_central
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    {Z : Subgroup G} (hZle : Z ≤ (S : Subgroup G)) (hZ : IsKleinFour Z)
    {a : G} (haZ : a ∈ Z) (ha1 : a ≠ 1)
    (haz : a ≠ zAmbient S e)
    (hconj : IsConj (zAmbient S e) a) :
    ∃ n : G, n ∈ Subgroup.normalizer (Z : Set G) ∧
      n * zAmbient S e * n⁻¹ = zAmbient S e * a ∧
      n * a * n⁻¹ = a := by
  classical
  rw [isConj_iff] at hconj
  rcases hconj with ⟨g, hg⟩
  obtain ⟨μ, hμC, hμalign⟩ :=
    exists_centralizer_sylow_alignment S hm e hZle hZ haZ g hg
  let σ : G := μ * g
  have hσ : σ * zAmbient S e * σ⁻¹ = a := by
    calc
      (μ * g) * zAmbient S e * (μ * g)⁻¹ =
          μ * (g * zAmbient S e * g⁻¹) * μ⁻¹ := by group
      _ = μ * a * μ⁻¹ := by rw [hg]
      _ = a := by
        have hcomm : a * μ = μ * a :=
          Subgroup.mem_centralizer_iff.mp hμC a (Set.mem_singleton a)
        rw [← hcomm]
        group
  have hzZ : zAmbient S e ∈ Z := by
    rcases isKleinFour_eq_dKleinAmbient S hm e Z hZle hZ with ⟨i, hZi⟩
    rw [hZi]
    exact dCentralAmbient_mem_dKleinAmbient S (by omega : 1 ≤ m) e i
  have hz1 : zAmbient S e ≠ 1 := zAmbient_ne_one S (by omega : 1 ≤ m) e
  obtain ⟨γ, hγS, hγN, hγfix, hγmove, hγAll⟩ :=
    exists_dihedral_transposition_of_kleinFour_le_sylow S hm e hZle hZ
  let W : Subgroup G := conjugateSubgroup Z σ⁻¹
  have hWleS : W ≤ (S : Subgroup G) := by
    intro x hx
    change x ∈ conjugateSubgroup Z σ⁻¹ at hx
    rw [mem_conjugateSubgroup_iff] at hx
    rcases hx with ⟨h, hh, hx⟩
    rcases (mem_conjugateSubgroup_iff S σ h).mp (hμalign hh) with ⟨s, hs, hs_eq⟩
    rw [hx, hs_eq, inv_inv]
    have : σ⁻¹ * (σ * (s : G) * σ⁻¹) * σ = (s : G) := by group
    rw [this]
    exact hs
  have hW : IsKleinFour W := isKleinFour_conjugateSubgroup Z σ⁻¹ hZ
  have hγW : γ ∈ Subgroup.normalizer (W : Set G) := hγAll W hWleS hW
  have hγWsub : conjugateSubgroup W γ = W := by
    have hmap := (Subgroup.mem_normalizer_iff_map_conj_eq (H := W) (g := γ)).mp hγW
    simpa [conjugateSubgroup] using hmap
  let γ' : G := σ * γ * σ⁻¹
  have hZW : conjugateSubgroup W σ = Z := by
    change conjugateSubgroup (conjugateSubgroup Z σ⁻¹) σ = Z
    calc
      conjugateSubgroup (conjugateSubgroup Z σ⁻¹) σ =
          conjugateSubgroup Z (σ * σ⁻¹) := conjugateSubgroup_conjugateSubgroup Z σ⁻¹ σ
      _ = conjugateSubgroup Z 1 := by congr 1; group
      _ = Z := conjugateSubgroup_one Z
  have hγ'Wsub : conjugateSubgroup Z γ' = Z := by
    calc
      conjugateSubgroup Z γ' =
          conjugateSubgroup (conjugateSubgroup W σ) γ' := by rw [← hZW]
      _ = conjugateSubgroup W (γ' * σ) := conjugateSubgroup_conjugateSubgroup W σ γ'
      _ = conjugateSubgroup W (σ * γ) := by
        congr 1
        dsimp [γ']
        group
      _ = conjugateSubgroup (conjugateSubgroup W γ) σ :=
        (conjugateSubgroup_conjugateSubgroup W γ σ).symm
      _ = conjugateSubgroup W σ := by rw [hγWsub]
      _ = Z := hZW
  have hγ'N : γ' ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [conjugateSubgroup] using hγ'Wsub
  have hzσ : σ⁻¹ * a * σ = zAmbient S e := by
    calc
      σ⁻¹ * a * σ = σ⁻¹ * (σ * zAmbient S e * σ⁻¹) * σ := by rw [hσ]
      _ = zAmbient S e := by group
  have hzW : zAmbient S e ∈ W := by
    change zAmbient S e ∈ conjugateSubgroup Z σ⁻¹
    rw [mem_conjugateSubgroup_iff]
    refine ⟨a, haZ, ?_⟩
    rw [inv_inv]
    exact hzσ.symm
  let c : G := σ⁻¹ * zAmbient S e * σ
  have hcW : c ∈ W := by
    change σ⁻¹ * zAmbient S e * σ ∈ conjugateSubgroup Z σ⁻¹
    rw [mem_conjugateSubgroup_iff]
    refine ⟨zAmbient S e, hzZ, ?_⟩
    rw [inv_inv]
  have hc1 : c ≠ 1 := by
    intro h
    apply hz1
    calc
      zAmbient S e = σ * c * σ⁻¹ := by dsimp [c]; group
      _ = 1 := by rw [h]; simp
  have hcz : c ≠ zAmbient S e := by
    intro h
    apply haz
    have hzσ : σ⁻¹ * zAmbient S e * σ = zAmbient S e := h
    have hσz0 : zAmbient S e = σ * zAmbient S e * σ⁻¹ := by
      calc
        zAmbient S e = σ * (σ⁻¹ * zAmbient S e * σ) * σ⁻¹ := by group
        _ = σ * zAmbient S e * σ⁻¹ := by rw [hzσ]
    exact hσ.symm.trans hσz0.symm
  have hγc_ne : γ * c * γ⁻¹ ≠ c := hγmove W hWleS hW c hcW hc1 hcz
  have hγc : γ * c * γ⁻¹ = zAmbient S e * c :=
    kleinFour_action_fix_move W hW (x := zAmbient S e) (y := c) (δ := γ)
      hzW hcW hz1 hc1 hcz.symm hγW hγfix hγc_ne
  have hγ'a : γ' * a * γ'⁻¹ = a := by
    calc
      γ' * a * γ'⁻¹ = σ * (γ * (σ⁻¹ * a * σ) * γ⁻¹) * σ⁻¹ := by
        dsimp [γ']
        group
      _ = σ * (γ * zAmbient S e * γ⁻¹) * σ⁻¹ := by rw [hzσ]
      _ = σ * zAmbient S e * σ⁻¹ := by rw [hγfix]
      _ = a := hσ
  have hσc : σ * c * σ⁻¹ = zAmbient S e := by
    dsimp [c]
    group
  have haz_comm : a * zAmbient S e = zAmbient S e * a := by
    let : IsKleinFour Z := hZ
    have h := (IsKleinFour.isMulCommutative (G := Z)).is_comm.comm
      ⟨a, haZ⟩ ⟨zAmbient S e, hzZ⟩
    exact congrArg Subtype.val h
  have hγ'z : γ' * zAmbient S e * γ'⁻¹ = zAmbient S e * a := by
    calc
      γ' * zAmbient S e * γ'⁻¹ =
          σ * (γ * (σ⁻¹ * zAmbient S e * σ) * γ⁻¹) * σ⁻¹ := by
        dsimp [γ']
        group
      _ = σ * (γ * c * γ⁻¹) * σ⁻¹ := by rfl
      _ = σ * (zAmbient S e * c) * σ⁻¹ := by rw [hγc]
      _ = (σ * zAmbient S e * σ⁻¹) * (σ * c * σ⁻¹) := by group
      _ = a * zAmbient S e := by rw [hσ, hσc]
      _ = zAmbient S e * a := haz_comm
  have hne : zAmbient S e * a ≠ zAmbient S e := by
    intro h
    apply ha1
    calc
      a = (zAmbient S e)⁻¹ * (zAmbient S e * a) := by group
      _ = (zAmbient S e)⁻¹ * zAmbient S e := by rw [h]
      _ = 1 := by group
  exact ⟨γ', hγ'N, hγ'z, hγ'a⟩

/-- A non-central involution of a Klein-four subgroup of a dihedral Sylow
`2`-subgroup of order at least eight. -/
private lemma exists_noncentral_of_kleinFour_le_sylow
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    {Z : Subgroup G} (hZle : Z ≤ (S : Subgroup G)) (hZ : IsKleinFour Z) :
    ∃ a : G, a ∈ Z ∧ a ≠ 1 ∧ a ≠ zAmbient S e ∧ a ^ 2 = 1 ∧
      zAmbient S e ∈ Z := by
  classical
  rcases isKleinFour_eq_dKleinAmbient S hm e Z hZle hZ with ⟨i, hZi⟩
  let a : G := (e.symm (DihedralGroup.sr i) : G)
  have hzZ : zAmbient S e ∈ Z := by
    rw [hZi]
    exact dCentralAmbient_mem_dKleinAmbient S (by omega : 1 ≤ m) e i
  have haZ : a ∈ Z := by
    rw [hZi, dKleinAmbient, Subgroup.mem_map]
    refine ⟨e.symm (DihedralGroup.sr i), ?_, rfl⟩
    simpa [dKleinAmbient] using dKlein_sr_mem (by omega : 1 ≤ m) i
  have ha1 : a ≠ 1 := by
    intro h
    have hS : (e.symm (DihedralGroup.sr i) : S) = 1 := by
      apply Subtype.ext
      exact h
    have hS' : e.symm (DihedralGroup.sr i) = e.symm (1 : DihedralGroup (2 ^ m)) := by
      simpa using hS
    have hM : DihedralGroup.sr i = 1 := e.symm.injective hS'
    exact sr_ne_one i hM
  have haz : a ≠ zAmbient S e := by
    intro h
    have hS : (e.symm (DihedralGroup.sr i) : S) = e.symm (dCentral m) := by
      apply Subtype.ext
      exact h
    have hM : DihedralGroup.sr i = dCentral m := e.symm.injective hS
    exact sr_ne_dCentral i hM
  have hsqM : (DihedralGroup.sr i : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr]
    simp
  have hsqS : ((e.symm (DihedralGroup.sr i) : S)) ^ 2 = 1 := by
    calc
      ((e.symm (DihedralGroup.sr i) : S)) ^ 2 =
          e.symm ((DihedralGroup.sr i : DihedralGroup (2 ^ m)) ^ 2) := by
        rw [map_pow]
      _ = 1 := by rw [hsqM]; simp
  have ha2 : a ^ 2 = 1 := by
    change (((e.symm (DihedralGroup.sr i) : S) : G)) ^ 2 = 1
    exact congrArg Subtype.val hsqS
  exact ⟨a, haZ, ha1, haz, ha2, hzZ⟩

/-- A fused reflection class gives `NormalizerContainsCPrime` for the
corresponding Klein-four class. -/
private lemma normalizerContainsCPrime_of_fused
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m))
    (hfused : fusedClass S e j) :
    NormalizerContainsCPrime (dKleinAmbient S (by omega : 1 ≤ m) e j) := by
  classical
  let Z : Subgroup G := dKleinAmbient S (by omega : 1 ≤ m) e j
  have hZle : Z ≤ (S : Subgroup G) := dKleinAmbient_le_S S (by omega : 1 ≤ m) e j
  have hZ : IsKleinFour Z := dKleinAmbient_isKleinFour S (by omega : 1 ≤ m) e j
  have hzZ : zAmbient S e ∈ Z := by
    simpa [Z] using dCentralAmbient_mem_dKleinAmbient S (by omega : 1 ≤ m) e j
  let a : G := (e.symm (DihedralGroup.sr j) : G)
  have haZ : a ∈ Z := by
    change a ∈ dKleinAmbient S (by omega : 1 ≤ m) e j
    rw [dKleinAmbient, Subgroup.mem_map]
    refine ⟨e.symm (DihedralGroup.sr j), ?_, rfl⟩
    simpa [dKleinAmbient] using dKlein_sr_mem (by omega : 1 ≤ m) j
  have ha1 : a ≠ 1 := by
    intro h
    have hS : (e.symm (DihedralGroup.sr j) : S) = 1 := by
      apply Subtype.ext
      exact h
    have hS' : e.symm (DihedralGroup.sr j) = e.symm (1 : DihedralGroup (2 ^ m)) := by
      simpa using hS
    exact sr_ne_one j (e.symm.injective hS')
  have haz : a ≠ zAmbient S e := by
    intro h
    have hS : (e.symm (DihedralGroup.sr j) : S) = e.symm (dCentral m) := by
      apply Subtype.ext
      exact h
    exact sr_ne_dCentral j (e.symm.injective hS)
  have hsqM : (DihedralGroup.sr j : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr]
    simp
  have hsqS : ((e.symm (DihedralGroup.sr j) : S)) ^ 2 = 1 := by
    calc
      ((e.symm (DihedralGroup.sr j) : S)) ^ 2 =
          e.symm ((DihedralGroup.sr j : DihedralGroup (2 ^ m)) ^ 2) := by
        rw [map_pow]
      _ = 1 := by rw [hsqM]; simp
  have ha2 : a ^ 2 = 1 := by
    change (((e.symm (DihedralGroup.sr j) : S) : G)) ^ 2 = 1
    exact congrArg Subtype.val hsqS
  have hconj : IsConj (zAmbient S e) a := by
    simpa [a, fusedClass] using hfused
  rcases fusion_to_normalizer_moves_central S hm e hZle hZ haZ ha1 haz hconj with
    ⟨n, hN, hnz, hna⟩
  obtain ⟨γ, _hγS, hγN, hγfix, hγmove, _hγAll⟩ :=
    exists_dihedral_transposition_of_kleinFour_le_sylow S hm e hZle hZ
  have hγa_ne : γ * a * γ⁻¹ ≠ a :=
    hγmove Z hZle hZ a haZ ha1 haz
  have hγa : γ * a * γ⁻¹ = zAmbient S e * a :=
    kleinFour_action_fix_move Z hZ (x := zAmbient S e) (y := a) (δ := γ)
      hzZ haZ (zAmbient_ne_one S (by omega : 1 ≤ m) e) ha1 haz.symm
      hγN hγfix hγa_ne
  exact normalizerContainsCPrime_of_two_transpositions Z hZ
    (z := zAmbient S e) (a := a) (γ := γ) (γ' := n) hzZ haZ
    (zAmbient_ne_one S (by omega : 1 ≤ m) e) ha1 haz.symm
    hγN hN hγfix hγa hna hnz

/-- Every rotation of the dihedral model lies in the full rotation subgroup. -/
private lemma r_mem_rotation_all {m : ℕ} (i : ZMod (2 ^ m)) :
    DihedralGroup.r i ∈ dihedralRotationSubgroup m 0 := by
  rw [dihedralRotationSubgroup_def]
  norm_num
  change DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1)
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨i.val, ?_⟩
  rw [DihedralGroup.r_zpow]
  congr 1
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp

/-- The even rotations are contained in the full rotation subgroup. -/
private lemma evenRotations_le_allRotations {m : ℕ} :
    dihedralRotationSubgroup m 1 ≤ dihedralRotationSubgroup m 0 := by
  rw [dihedralRotationSubgroup_def, dihedralRotationSubgroup_def]
  norm_num
  simpa [dihedralRotationSubgroup_def] using r_mem_rotation_all (2 : ZMod (2 ^ m))

/-- A focal generator of a dihedral Sylow subgroup is either an even
rotation, a reflection fused to the central involution, or (if the two
reflection classes are mutually fused) an odd rotation. -/
private lemma focal_generator_mem_B_or_fused_or_iff_odd
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) {a b : DihedralGroup (2 ^ m)}
    (hconj : IsConj (e.symm a : G) (e.symm b : G)) :
    a⁻¹ * b ∈ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) ∨
    a⁻¹ * b ∈ fusedReflSet S e ∨
      ((fusedClass S e 0 ↔ fusedClass S e 1) ∧
        a⁻¹ * b ∈ (dihedralRotationSubgroup m 0 : Set (DihedralGroup (2 ^ m)))) := by
  rcases dihedralGroup_cases a with ⟨i, ha⟩ | ⟨i, ha⟩
  · rcases dihedralGroup_cases b with ⟨j, hb⟩ | ⟨j, hb⟩
    · left
      rw [ha, hb, DihedralGroup.inv_r, DihedralGroup.r_mul_r]
      have hord : orderOf (DihedralGroup.r i) = orderOf (DihedralGroup.r j) := by
        simpa [ha, hb] using orderOf_eq_of_isConj_ambient S e hconj
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using
        rotation_sub_mem_even_of_order_eq (by omega : 1 ≤ m) hord
    · right; left
      rw [ha, hb, DihedralGroup.inv_r, DihedralGroup.r_mul_sr]
      have hzr : DihedralGroup.r i = dCentral m := by
        have hord : orderOf (DihedralGroup.r i) = 2 := by
          have hord' := orderOf_eq_of_isConj_ambient S e hconj
          simpa [ha, hb, DihedralGroup.orderOf_sr] using hord'
        exact rotation_order_two_eq_dCentral (by omega : 1 ≤ m) i hord
      have hz : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr j) : G) := by
        have h' : IsConj (e.symm (DihedralGroup.r i) : G)
            (e.symm (DihedralGroup.sr j) : G) := by simpa [ha, hb] using hconj
        simpa [zAmbient, hzr] using h'
      rcases dCentral_index_eq_two_mul hm i hzr with ⟨k, hk⟩
      change DihedralGroup.sr (j - (-i)) ∈ fusedReflSet S e
      rw [fusedReflSet]
      have hEq : j - (-i) = j + (2 : ZMod (2 ^ m)) * k := by
        rw [hk]
        ring
      rw [hEq]
      exact isConj_z_sr_of_sameClass S e hz k
  · rcases dihedralGroup_cases b with ⟨j, hb⟩ | ⟨j, hb⟩
    · right; left
      rw [ha, hb, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r]
      have hzr : DihedralGroup.r j = dCentral m := by
        have hord : orderOf (DihedralGroup.r j) = 2 := by
          have hord' := orderOf_eq_of_isConj_ambient S e hconj
          simpa [ha, hb, DihedralGroup.orderOf_sr] using hord'.symm
        exact rotation_order_two_eq_dCentral (by omega : 1 ≤ m) j hord
      have hz : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr i) : G) := by
        have h' : IsConj (e.symm (DihedralGroup.sr i) : G)
            (e.symm (DihedralGroup.r j) : G) := by simpa [ha, hb] using hconj
        have hzi : IsConj (e.symm (DihedralGroup.sr i) : G) (zAmbient S e) := by
          simpa [zAmbient, hzr] using h'
        exact hzi.symm
      rcases dCentral_index_eq_two_mul hm j hzr with ⟨k, hk⟩
      change DihedralGroup.sr (i + j) ∈ fusedReflSet S e
      rw [fusedReflSet]
      have hEq : i + j = i + (2 : ZMod (2 ^ m)) * k := by
        rw [hk]
      rw [hEq]
      exact isConj_z_sr_of_sameClass S e hz k
    · rw [ha, hb, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
      rcases sr_mem_reflClass_zero_or_one m i with hi0 | hi1
      · rcases sr_mem_reflClass_zero_or_one m j with hj0 | hj1
        · left
          exact reflection_sub_mem_even_of_same_reflClass (by omega : 1 ≤ m)
            (Or.inl ⟨hi0, hj0⟩)
        · right; right
          have hconj' : IsConj (e.symm (DihedralGroup.sr i) : G)
              (e.symm (DihedralGroup.sr j) : G) := by
            simpa [ha, hb] using hconj
          constructor
          · constructor
            · intro hf0
              rcases hi0 with ⟨a, ha0⟩
              have hzi : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr i) : G) := by
                have hi_eq : i = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * a :=
                  DihedralGroup.sr.inj ha0
                simpa [hi_eq, fusedClass] using
                  (isConj_z_sr_of_sameClass S e (i := 0) hf0 a)
              have hzj : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr j) : G) := hzi.trans hconj'
              rcases hj1 with ⟨b, hb1⟩
              have hj_eq : j = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * b :=
                DihedralGroup.sr.inj hb1
              simpa [hj_eq, fusedClass] using
                (isConj_z_sr_of_sameClass S e (i := j) hzj (-b))
            · intro hf1
              rcases hj1 with ⟨b, hb1⟩
              have hj_eq : j = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * b :=
                DihedralGroup.sr.inj hb1
              have hzj : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr j) : G) := by
                simpa [hj_eq, fusedClass] using
                  (isConj_z_sr_of_sameClass S e (i := 1) hf1 b)
              have hzi : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr i) : G) :=
                hzj.trans hconj'.symm
              rcases hi0 with ⟨a, ha0⟩
              have hi_eq : i = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * a :=
                DihedralGroup.sr.inj ha0
              simpa [hi_eq, fusedClass] using
                (isConj_z_sr_of_sameClass S e (i := i) hzi (-a))
          · exact r_mem_rotation_all (j - i)
      · rcases sr_mem_reflClass_zero_or_one m j with hj0 | hj1
        · right; right
          have hconj' : IsConj (e.symm (DihedralGroup.sr i) : G)
              (e.symm (DihedralGroup.sr j) : G) := by
            simpa [ha, hb] using hconj
          constructor
          · constructor
            · intro hf0
              rcases hj0 with ⟨b, hb0⟩
              have hj_eq : j = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * b :=
                DihedralGroup.sr.inj hb0
              have hzj : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr j) : G) := by
                simpa [hj_eq, fusedClass] using
                  (isConj_z_sr_of_sameClass S e (i := 0) hf0 b)
              have hzi : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr i) : G) :=
                hzj.trans hconj'.symm
              rcases hi1 with ⟨a, ha1⟩
              have hi_eq : i = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * a :=
                DihedralGroup.sr.inj ha1
              simpa [hi_eq, fusedClass] using
                (isConj_z_sr_of_sameClass S e (i := i) hzi (-a))
            · intro hf1
              rcases hi1 with ⟨a, ha1⟩
              have hzi : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr i) : G) := by
                have hi_eq : i = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * a :=
                  DihedralGroup.sr.inj ha1
                simpa [hi_eq, fusedClass] using
                  (isConj_z_sr_of_sameClass S e (i := 1) hf1 a)
              have hzj : IsConj (zAmbient S e)
                  (e.symm (DihedralGroup.sr j) : G) := hzi.trans hconj'
              rcases hj0 with ⟨b, hb0⟩
              have hj_eq : j = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * b :=
                DihedralGroup.sr.inj hb0
              simpa [hj_eq, fusedClass] using
                (isConj_z_sr_of_sameClass S e (i := j) hzj (-b))
          · exact r_mem_rotation_all (j - i)
        · left
          exact reflection_sub_mem_even_of_same_reflClass (by omega : 1 ≤ m)
            (Or.inr ⟨hi1, hj1⟩)

/-- The ambient image of the full rotation subgroup of the model. -/
private abbrev allRotationsAmbient
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) : Subgroup G :=
  ((dihedralRotationSubgroup m 0).comap e.toMonoidHom).map
    (S : Subgroup G).subtype

/-- The ambient image of a reflection extension of the even rotations. -/
private abbrev indexTwoAmbient
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m)) : Subgroup G :=
  ((dihedralIndexTwoSubgroup m j).comap e.toMonoidHom).map
    (S : Subgroup G).subtype

/-- The ambient image of the reflections fused to the central involution. -/
private abbrev fusedReflAmbient
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) : Set G :=
  {x | ∃ p : DihedralGroup (2 ^ m), p ∈ fusedReflSet S e ∧ x = (e.symm p : G)}

/-- Model membership in the even rotations transports to the ambient
subgroup. -/
private lemma ambient_mem_evenRotations_of_model
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) {p : DihedralGroup (2 ^ m)}
    (hp : p ∈ dihedralRotationSubgroup m 1) :
    (e.symm p : G) ∈ evenRotations S e := by
  exact Subgroup.mem_map.mpr ⟨e.symm p, by simpa using hp, rfl⟩

/-- Model membership in the full rotations transports to the ambient
subgroup. -/
private lemma ambient_mem_allRotations_of_model
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) {p : DihedralGroup (2 ^ m)}
    (hp : p ∈ dihedralRotationSubgroup m 0) :
    (e.symm p : G) ∈ allRotationsAmbient S e := by
  exact Subgroup.mem_map.mpr ⟨e.symm p, by simpa using hp, rfl⟩

/-- The even rotations are contained in every reflection extension. -/
private lemma evenRotations_le_indexTwo {m : ℕ} (hm : 1 ≤ m)
    (j : ZMod (2 ^ m)) :
    dihedralRotationSubgroup m 1 ≤ dihedralIndexTwoSubgroup m j := by
  intro x hx
  rw [mem_dihedralIndexTwoSubgroup_iff hm j x]
  left
  rw [dihedralRotationSubgroup_def] at hx
  rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [← hk, DihedralGroup.r_zpow]
  congr 1
  norm_num

/-- Ambient containment of the even rotations in a reflection extension. -/
private lemma sr_not_mem_allRotations {m : ℕ} (i : ZMod (2 ^ m)) :
    DihedralGroup.sr i ∉ dihedralRotationSubgroup m 0 := by
  rw [dihedralRotationSubgroup_def]
  norm_num
  exact sr_not_mem_zpowers_r_one i

/-- A non-rotation of the model is not in the ambient rotation subgroup. -/
private lemma not_mem_allRotationsAmbient_of_model_not
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) {p : DihedralGroup (2 ^ m)}
    (hp : p ∉ dihedralRotationSubgroup m 0) :
    (e.symm p : G) ∉ allRotationsAmbient S e := by
  intro hx
  rcases Subgroup.mem_map.mp hx with ⟨s, hs, hval⟩
  have hs_eq : s = e.symm p := by
    apply Subtype.ext
    exact hval
  have hp' : p ∈ dihedralRotationSubgroup m 0 := by
    simpa [hs_eq] using hs
  exact hp hp'

/-- The central involution of the model is an even rotation for `m ≥ 2`. -/
private lemma dCentral_mem_evenRotations_model {m : ℕ} (hm : 2 ≤ m) :
    dCentral m ∈ dihedralRotationSubgroup m 1 := by
  rcases exists_two_mul_eq_half hm with ⟨k, hk⟩
  rw [dCentral, hk]
  exact r_two_mul_mem_evenRotations_model k

/-- A rotation in the fused reflection set is necessarily the central
involution, hence an even rotation. -/
private lemma rotation_mem_even_of_fused
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) {i : ZMod (2 ^ m)}
    (h : IsConj (zAmbient S e) (e.symm (DihedralGroup.r i) : G)) :
    DihedralGroup.r i ∈ dihedralRotationSubgroup m 1 := by
  have hord' := orderOf_eq_of_isConj_ambient S e
    (a := dCentral m) (b := DihedralGroup.r i) h
  have hord : orderOf (DihedralGroup.r i) = 2 := by
    rw [dCentral_order_two (by omega : 1 ≤ m)] at hord'
    exact hord'.symm
  have hz : DihedralGroup.r i = dCentral m :=
    rotation_order_two_eq_dCentral (by omega : 1 ≤ m) i hord
  simpa [hz] using dCentral_mem_evenRotations_model hm

/-- With class zero fused and class one not, the fused reflections lie in the
zero reflection extension. -/
private lemma fusedReflSet_subset_indexTwo_of_fused0_not1
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : fusedClass S e 0) (h1 : ¬ fusedClass S e 1)
    {p : DihedralGroup (2 ^ m)} (hp : p ∈ fusedReflSet S e) :
    p ∈ dihedralIndexTwoSubgroup m 0 := by
  rcases dihedralGroup_cases p with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact evenRotations_le_indexTwo (by omega : 1 ≤ m) 0
      (rotation_mem_even_of_fused S hm e hp)
  · rcases sr_mem_reflClass_zero_or_one m i with hi0 | hi1
    · have hi0E : DihedralGroup.sr i ∈
          (dihedralIndexTwoSubgroup m 0 : Set (DihedralGroup (2 ^ m))) := by
        rw [← reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 0]
        exact Or.inl hi0
      exact hi0E
    · exfalso
      apply h1
      rcases hi1 with ⟨k, hk⟩
      have hi_eq : i = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k :=
        DihedralGroup.sr.inj hk
      have hzi : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr i) : G) := hp
      simpa [hi_eq, fusedClass] using
        (isConj_z_sr_of_sameClass S e (i := i) hzi (-k))

/-- With class one fused and class zero not, the fused reflections lie in the
one reflection extension. -/
private lemma fusedReflSet_subset_indexTwo_of_fused1_not0
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h1 : fusedClass S e 1) (h0 : ¬ fusedClass S e 0)
    {p : DihedralGroup (2 ^ m)} (hp : p ∈ fusedReflSet S e) :
    p ∈ dihedralIndexTwoSubgroup m 1 := by
  rcases dihedralGroup_cases p with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact evenRotations_le_indexTwo (by omega : 1 ≤ m) 1
      (rotation_mem_even_of_fused S hm e hp)
  · rcases sr_mem_reflClass_zero_or_one m i with hi0 | hi1
    · exfalso
      apply h0
      rcases hi0 with ⟨k, hk⟩
      have hi_eq : i = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k :=
        DihedralGroup.sr.inj hk
      have hzi : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr i) : G) := hp
      simpa [hi_eq, fusedClass] using
        (isConj_z_sr_of_sameClass S e (i := i) hzi (-k))
    · have hi1E : DihedralGroup.sr i ∈
          (dihedralIndexTwoSubgroup m 1 : Set (DihedralGroup (2 ^ m))) := by
        rw [← reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 1]
        exact Or.inl hi1
      exact hi1E

/-- A non-member of a model reflection extension is not in the ambient image. -/
private lemma not_mem_indexTwoAmbient_of_model_not
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m))
    {p : DihedralGroup (2 ^ m)} (hp : p ∉ dihedralIndexTwoSubgroup m j) :
    (e.symm p : G) ∉ indexTwoAmbient S e j := by
  intro hx
  rcases Subgroup.mem_map.mp hx with ⟨s, hs, hval⟩
  have hs_eq : s = e.symm p := by
    apply Subtype.ext
    exact hval
  have hp' : p ∈ dihedralIndexTwoSubgroup m j := by
    simpa [hs_eq] using hs
  exact hp hp'

/-- A reflection belongs to its own reflection extension. -/
private lemma sr_mem_indexTwo {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    DihedralGroup.sr j ∈ dihedralIndexTwoSubgroup m j := by
  rw [mem_dihedralIndexTwoSubgroup_iff hm j (DihedralGroup.sr j)]
  right
  refine ⟨0, ?_⟩
  simp

/-- The centralizer of a reflection in a dihedral `2`-group is its
Klein-four subgroup. -/
private lemma centralizer_reflection_eq_dKlein {m : ℕ} (hm : 2 ≤ m)
    (j : ZMod (2 ^ m)) :
    Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))) =
      dKlein m (by omega : 1 ≤ m) j := by
  classical
  let V : Subgroup (DihedralGroup (2 ^ m)) := dKlein m (by omega : 1 ≤ m) j
  have hV : IsKleinFour V := isKleinFour_dKlein (by omega : 1 ≤ m) j
  have hCV : Subgroup.centralizer (V : Set (DihedralGroup (2 ^ m))) ≤ V :=
    centralizer_kleinFour_le_of_dihedral_mulEquiv (by omega : 1 ≤ m)
      (MulEquiv.refl (DihedralGroup (2 ^ m))) V hV
  apply le_antisymm
  · intro x hx
    apply hCV
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y ∈ dKlein m (by omega : 1 ≤ m) j at hy
    rw [mem_dKlein_iff (by omega : 1 ≤ m) j y] at hy
    rcases hy with h1 | h2 | h3 | h4
    · simp [h1]
    · have hzcentral : dCentral m ∈ Subgroup.center (DihedralGroup (2 ^ m)) :=
        dCentral_mem_center hm
      rw [h2]
      exact (Subgroup.mem_center_iff.mp hzcentral x).symm
    · rw [h3]
      exact (Subgroup.mem_centralizer_iff.mp hx) (DihedralGroup.sr j)
        (by simp)
    · rcases exists_two_mul_eq_half hm with ⟨k, hk⟩
      have hy_eq : DihedralGroup.sr (j + (2 : ZMod (2 ^ m)) ^ (m - 1)) =
          DihedralGroup.sr j * dCentral m := by
        rw [dCentral, DihedralGroup.sr_mul_r]
      rw [h4, hy_eq]
      have hxcomm := (Subgroup.mem_centralizer_iff.mp hx)
        (DihedralGroup.sr j) (by simp)
      have hzcentral : dCentral m ∈ Subgroup.center (DihedralGroup (2 ^ m)) :=
        dCentral_mem_center hm
      have hzx : x * dCentral m = dCentral m * x :=
        Subgroup.mem_center_iff.mp hzcentral x
      calc
        (DihedralGroup.sr j * dCentral m) * x =
            DihedralGroup.sr j * (dCentral m * x) := by rw [mul_assoc]
        _ = DihedralGroup.sr j * (x * dCentral m) := by rw [hzx]
        _ = (DihedralGroup.sr j * x) * dCentral m := by rw [← mul_assoc]
        _ = (x * DihedralGroup.sr j) * dCentral m := by rw [hxcomm]
        _ = x * (DihedralGroup.sr j * dCentral m) := by rw [mul_assoc]
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    let : IsKleinFour V := hV
    let xV : V := ⟨x, hx⟩
    let sV : V := ⟨DihedralGroup.sr j, dKlein_sr_mem (by omega : 1 ≤ m) j⟩
    have hxV : xV * sV = sV * xV :=
      (IsKleinFour.isMulCommutative (G := V)).is_comm.comm xV sV
    exact (congrArg Subtype.val hxV).symm

/-- The zero reflection is not in the one reflection extension. -/
private lemma sr0_not_mem_indexTwo_one {m : ℕ} (hm : 1 ≤ m) :
    DihedralGroup.sr 0 ∉ dihedralIndexTwoSubgroup m 1 := by
  rw [mem_dihedralIndexTwoSubgroup_iff hm 1 (DihedralGroup.sr 0)]
  rintro (⟨k, hk⟩ | ⟨k, hk⟩)
  · cases hk
  · have hEq : (0 : ZMod (2 ^ m)) = 1 + (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)) :=
      DihedralGroup.sr.inj hk
    have htwo : (2 : ZMod (2 ^ m)) * (-(k : ZMod (2 ^ m))) = 1 := by
      rw [mul_neg]
      exact (neg_eq_iff_add_eq_zero).mpr (by simpa [add_comm] using hEq.symm)
    exact zmod_two_mul_ne_one hm (-(k : ZMod (2 ^ m))) htwo

/-- The one reflection is not in the zero reflection extension. -/
private lemma sr1_not_mem_indexTwo_zero {m : ℕ} (hm : 1 ≤ m) :
    DihedralGroup.sr 1 ∉ dihedralIndexTwoSubgroup m 0 := by
  rw [mem_dihedralIndexTwoSubgroup_iff hm 0 (DihedralGroup.sr 1)]
  rintro (⟨k, hk⟩ | ⟨k, hk⟩)
  · cases hk
  · have hEq : (1 : ZMod (2 ^ m)) = 0 + (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)) :=
      DihedralGroup.sr.inj hk
    have htwo : (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)) = 1 := by
      simpa using hEq.symm
    exact zmod_two_mul_ne_one hm (k : ZMod (2 ^ m)) htwo

/-- If the Grün subgroup is the whole Sylow subgroup, both reflection classes
are fused to the central involution. -/
private lemma focalSubgroup_le_indexTwo_of_fusion
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m))
    (hfused : ∀ p ∈ fusedReflSet S e, p ∈ dihedralIndexTwoSubgroup m j)
    (hodd : ¬ (fusedClass S e 0 ↔ fusedClass S e 1)) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤
      indexTwoAmbient S e j := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = (S : Subgroup G).feitThompsonFocalSubgroup := by
    dsimp [D]
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    rw [inf_comm]
    exact (Subgroup.commutator_inf_eq_feitThompsonFocalSubgroup (P := S))
  have hgen : {z : G | ∃ x ∈ (S : Subgroup G), ∃ y ∈ (S : Subgroup G),
      IsConj x y ∧ z = x⁻¹ * y} ⊆ (indexTwoAmbient S e j : Set G) := by
    intro z hz
    rcases hz with ⟨x, hxS, y, hyS, hconj, hzxy⟩
    let xS : S := ⟨x, hxS⟩
    let yS : S := ⟨y, hyS⟩
    have hconjM : IsConj (e.symm (e xS) : G) (e.symm (e yS) : G) := by
      simpa [xS, yS] using hconj
    rcases focal_generator_mem_B_or_fused_or_iff_odd S hm e hconjM with
      hB | hF | hO
    · rw [hzxy]
      let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
      refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
      have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
        apply Subtype.ext
        simp [xS, yS]
      have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
        rw [hSub]
        simp
      simpa [hE] using
        (evenRotations_le_indexTwo (by omega : 1 ≤ m) j
          (by simpa [xS, yS] using hB))
    · rw [hzxy]
      let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
      refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
      have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
        apply Subtype.ext
        simp [xS, yS]
      have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
        rw [hSub]
        simp
      have hp : (e xS)⁻¹ * (e yS) ∈ dihedralIndexTwoSubgroup m j :=
        hfused ((e xS)⁻¹ * (e yS)) (by simpa [xS, yS] using hF)
      simpa [hE] using hp
    · exact False.elim (hodd hO.1)
  change D ≤ indexTwoAmbient S e j
  rw [hDeq]
  rw [Subgroup.feitThompsonFocalSubgroup_def]
  exact (Subgroup.closure_le (indexTwoAmbient S e j)).mpr hgen

/-- With no reflection class fused to the central involution, every fused
reflection set element is a rotation (in fact none can be a reflection). -/
private lemma fusedReflSet_subset_allRotations_of_no_fused
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : ¬ fusedClass S e 0) (h1 : ¬ fusedClass S e 1)
    {p : DihedralGroup (2 ^ m)} (hp : p ∈ fusedReflSet S e) :
    p ∈ dihedralRotationSubgroup m 0 := by
  rcases dihedralGroup_cases p with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact r_mem_rotation_all i
  · exfalso
    rcases sr_mem_reflClass_zero_or_one m i with hi0 | hi1
    · apply h0
      rcases hi0 with ⟨k, hk⟩
      have hi_eq : i = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k :=
        DihedralGroup.sr.inj hk
      have hzi : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr i) : G) := hp
      simpa [hi_eq, fusedClass] using
        (isConj_z_sr_of_sameClass S e (i := i) hzi (-k))
    · apply h1
      rcases hi1 with ⟨k, hk⟩
      have hi_eq : i = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k :=
        DihedralGroup.sr.inj hk
      have hzi : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr i) : G) := hp
      simpa [hi_eq, fusedClass] using
        (isConj_z_sr_of_sameClass S e (i := i) hzi (-k))

/-- If no reflection class is fused to the central involution, the
Grün/focal subgroup is contained in the full rotation subgroup. -/
private lemma focalSubgroup_le_allRotations_of_no_fused
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : ¬ fusedClass S e 0) (h1 : ¬ fusedClass S e 1) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤
      allRotationsAmbient S e := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = (S : Subgroup G).feitThompsonFocalSubgroup := by
    dsimp [D]
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    rw [inf_comm]
    exact (Subgroup.commutator_inf_eq_feitThompsonFocalSubgroup (P := S))
  have hgen : {z : G | ∃ x ∈ (S : Subgroup G), ∃ y ∈ (S : Subgroup G),
      IsConj x y ∧ z = x⁻¹ * y} ⊆ (allRotationsAmbient S e : Set G) := by
    intro z hz
    rcases hz with ⟨x, hxS, y, hyS, hconj, hzxy⟩
    let xS : S := ⟨x, hxS⟩
    let yS : S := ⟨y, hyS⟩
    have hconjM : IsConj (e.symm (e xS) : G) (e.symm (e yS) : G) := by
      simpa [xS, yS] using hconj
    rcases focal_generator_mem_B_or_fused_or_iff_odd S hm e hconjM with
      hB | hF | hO
    · rw [hzxy]
      let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
      refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
      have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
        apply Subtype.ext
        simp [xS, yS]
      have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
        rw [hSub]
        simp
      simpa [hE] using
        (evenRotations_le_allRotations (by simpa [xS, yS] using hB))
    · rw [hzxy]
      let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
      refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
      have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
        apply Subtype.ext
        simp [xS, yS]
      have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
        rw [hSub]
        simp
      simpa [hE] using
        (fusedReflSet_subset_allRotations_of_no_fused S e h0 h1
          (by simpa [xS, yS] using hF))
    · rw [hzxy]
      let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
      refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
      have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
        apply Subtype.ext
        simp [xS, yS]
      have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
        rw [hSub]
        simp
      simpa [hE] using (by simpa [xS, yS] using hO.2)
  change D ≤ allRotationsAmbient S e
  rw [hDeq]
  rw [Subgroup.feitThompsonFocalSubgroup_def]
  exact (Subgroup.closure_le (allRotationsAmbient S e)).mpr hgen

/-- Multiplying a reflection by the central involution keeps it in the same
reflection class (for `m ≥ 2`). -/
private lemma both_fused_of_grun_eq_sylow
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (hD : huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) =
      (S : Subgroup G)) :
    fusedClass S e 0 ∧ fusedClass S e 1 := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = (S : Subgroup G) := hD
  by_cases h0 : fusedClass S e 0
  · by_cases h1 : fusedClass S e 1
    · exact ⟨h0, h1⟩
    · exfalso
      have hle : D ≤ indexTwoAmbient S e 0 :=
        focalSubgroup_le_indexTwo_of_fusion S hm e 0
          (fun p hp => fusedReflSet_subset_indexTwo_of_fused0_not1
            S hm e h0 h1 (p := p) hp)
          (by intro hiff; exact h1 (hiff.mp h0))
      rw [hDeq] at hle
      have hsS : (e.symm (DihedralGroup.r 1) : G) ∈ (S : Subgroup G) :=
        (e.symm (DihedralGroup.r 1)).property
      have hsE : (e.symm (DihedralGroup.r 1) : G) ∈ indexTwoAmbient S e 0 :=
        hle hsS
      exact not_mem_indexTwoAmbient_of_model_not S e 0
        (r_one_not_mem_dihedralIndexTwoSubgroup (by omega : 1 ≤ m) 0) hsE
  · by_cases h1 : fusedClass S e 1
    · exfalso
      have hle : D ≤ indexTwoAmbient S e 1 :=
        focalSubgroup_le_indexTwo_of_fusion S hm e 1
          (fun p hp => fusedReflSet_subset_indexTwo_of_fused1_not0
            S hm e h1 h0 (p := p) hp)
          (by intro hiff; exact h0 (hiff.mpr h1))
      rw [hDeq] at hle
      have hsS : (e.symm (DihedralGroup.r 1) : G) ∈ (S : Subgroup G) :=
        (e.symm (DihedralGroup.r 1)).property
      have hsE : (e.symm (DihedralGroup.r 1) : G) ∈ indexTwoAmbient S e 1 :=
        hle hsS
      exact not_mem_indexTwoAmbient_of_model_not S e 1
        (r_one_not_mem_dihedralIndexTwoSubgroup (by omega : 1 ≤ m) 1) hsE
    · exfalso
      have hle : D ≤ allRotationsAmbient S e :=
        focalSubgroup_le_allRotations_of_no_fused S hm e h0 h1
      rw [hDeq] at hle
      have hsS : (e.symm (DihedralGroup.sr 0) : G) ∈ (S : Subgroup G) :=
        (e.symm (DihedralGroup.sr 0)).property
      have hsA : (e.symm (DihedralGroup.sr 0) : G) ∈ allRotationsAmbient S e :=
        hle hsS
      exact not_mem_allRotationsAmbient_of_model_not S e
        (sr_not_mem_allRotations 0) hsA

private lemma evenRotationsAmbient_le_indexTwoAmbient
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m)) :
    evenRotations S e ≤ indexTwoAmbient S e j := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨s, hs, rfl⟩
  exact Subgroup.mem_map.mpr ⟨s, evenRotations_le_indexTwo hm j hs, rfl⟩

/-- Model membership in a reflection extension transports to the ambient
subgroup. -/
private lemma ambient_mem_indexTwo_of_model
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m))
    {p : DihedralGroup (2 ^ m)} (hp : p ∈ dihedralIndexTwoSubgroup m j) :
    (e.symm p : G) ∈ indexTwoAmbient S e j := by
  exact Subgroup.mem_map.mpr ⟨e.symm p, by simpa using hp, rfl⟩

/-- If only one reflection class is fused to the central involution, the
Grün/focal subgroup is contained in the corresponding reflection extension. -/
private lemma dCentral_mul_sr_mem_reflClass {m : ℕ} (hm : 2 ≤ m)
    (j : ZMod (2 ^ m)) :
    dCentral m * DihedralGroup.sr j ∈ reflClass m j := by
  rcases exists_two_mul_eq_half hm with ⟨k, hk⟩
  rw [dCentral, DihedralGroup.r_mul_sr]
  refine ⟨-k, ?_⟩
  congr 1
  rw [hk]
  ring

/-- A reflection that is fused to the central involution gives a reflection of
the same class inside the Grün/focal subgroup. -/
private lemma reflection_of_fusedClass_mem_grun
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m))
    (hfused : fusedClass S e j) :
    (e.symm (dCentral m * DihedralGroup.sr j) : G) ∈
      huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = (S : Subgroup G).feitThompsonFocalSubgroup := by
    dsimp [D]
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    rw [inf_comm]
    exact (Subgroup.commutator_inf_eq_feitThompsonFocalSubgroup (P := S))
  change (e.symm (dCentral m * DihedralGroup.sr j) : G) ∈ D
  rw [hDeq]
  rw [Subgroup.feitThompsonFocalSubgroup_def]
  apply Subgroup.subset_closure
  refine ⟨zAmbient S e, (e.symm (dCentral m)).property,
    (e.symm (DihedralGroup.sr j) : G), (e.symm (DihedralGroup.sr j)).property,
    hfused, ?_⟩
  have hEq : (zAmbient S e)⁻¹ * (e.symm (DihedralGroup.sr j) : G) =
      (e.symm (dCentral m * DihedralGroup.sr j) : G) := by
    rw [zAmbient]
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul]
    rw [← map_inv, ← map_mul]
    congr 1
    rw [dCentral_inv_self (by omega : 1 ≤ m)]
  exact hEq.symm

/-- The ambient even rotations are contained in the Grün/focal subgroup. -/
private lemma evenRotations_le_grunKernel
    {G : Type u} [Group G] (S : Sylow 2 G) {m : ℕ}
    (e : S ≃* DihedralGroup (2 ^ m)) :
    evenRotations S e ≤
      huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) := by
  intro x hx
  have hx' : x ∈ (commutator (S : Subgroup G)).map (S : Subgroup G).subtype := by
    rw [embedded_commutator_eq_even_rotations (S : Subgroup G) e]
    exact hx
  exact embedded_commutator_le_grunKernelSubgroup (S : Subgroup G) hx'


/-- The Grün/focal subgroup of a dihedral Sylow subgroup is contained in the
subgroup generated by all rotations and the reflections fused to the central
involution. -/
private lemma focalSubgroup_le_closure_allRotations_fused
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤
      Subgroup.closure
        ((allRotationsAmbient S e : Set G) ∪ fusedReflAmbient S e) := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = (S : Subgroup G).feitThompsonFocalSubgroup := by
    dsimp [D]
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    rw [inf_comm]
    exact (Subgroup.commutator_inf_eq_feitThompsonFocalSubgroup (P := S))
  let C := Subgroup.closure ((allRotationsAmbient S e : Set G) ∪ fusedReflAmbient S e)
  have hgen : {z : G | ∃ x ∈ (S : Subgroup G), ∃ y ∈ (S : Subgroup G),
      IsConj x y ∧ z = x⁻¹ * y} ⊆ (C : Set G) := by
    intro z hz
    rcases hz with ⟨x, hxS, y, hyS, hconj, hzxy⟩
    let xS : S := ⟨x, hxS⟩
    let yS : S := ⟨y, hyS⟩
    have hconjM : IsConj (e.symm (e xS) : G) (e.symm (e yS) : G) := by
      simpa [xS, yS] using hconj
    rcases focal_generator_mem_B_or_fused_or_iff_odd S hm e hconjM with
      hB | hF | hO
    · apply Subgroup.subset_closure
      left
      have hzA : z ∈ allRotationsAmbient S e := by
        rw [hzxy]
        let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
          (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
        refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
        have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
          apply Subtype.ext
          simp [xS, yS]
        have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
          rw [hSub]
          simp
        simpa [hE] using
          (evenRotations_le_allRotations (by simpa [xS, yS] using hB))
      exact hzA
    · apply Subgroup.subset_closure
      right
      refine ⟨(e xS)⁻¹ * (e yS), hF, ?_⟩
      have hzE : z = (e.symm ((e xS)⁻¹ * (e yS)) : G) := by
        rw [hzxy]
        simp [xS, yS]
      exact hzE
    · apply Subgroup.subset_closure
      left
      have hzA : z ∈ allRotationsAmbient S e := by
        rw [hzxy]
        let hzS : x⁻¹ * y ∈ (S : Subgroup G) :=
          (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hxS) hyS
        refine Subgroup.mem_map.mpr ⟨⟨x⁻¹ * y, hzS⟩, ?_, rfl⟩
        have hSub : (⟨x⁻¹ * y, hzS⟩ : S) = xS⁻¹ * yS := by
          apply Subtype.ext
          simp [xS, yS]
        have hE : e ⟨x⁻¹ * y, hzS⟩ = (e xS)⁻¹ * (e yS) := by
          rw [hSub]
          simp
        simpa [hE] using (by simpa [xS, yS] using hO.2)
      exact hzA
  change D ≤ Subgroup.closure ((allRotationsAmbient S e : Set G) ∪ fusedReflAmbient S e)
  rw [hDeq]
  rw [Subgroup.feitThompsonFocalSubgroup_def]
  simpa [C] using Subgroup.closure_mono hgen

/-- The unique involution of the even-rotation subgroup is the central
involution `dCentral m`. -/
private lemma order_two_mem_evenRotations_eq_dCentral {m : ℕ} (hm : 2 ≤ m)
    (x : DihedralGroup (2 ^ m)) (hx : x ∈ dihedralRotationSubgroup m 1) (hx2 : orderOf x = 2) :
    x = dCentral m := by
  classical
  rw [dihedralRotationSubgroup_def] at hx
  rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
  have hx' : x = DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) := by
    rw [← hk, DihedralGroup.r_zpow]
    congr 1
    norm_num
  rw [hx']
  have hsq : x ^ 2 = 1 := by
    exact (congrArg (fun n : ℕ => x ^ n) hx2.symm).trans (pow_orderOf_eq_one x)
  have hsq' : (DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) ^ 2 = 1 := by
    rw [← hx']
    exact hsq
  have h4 : 2 * ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) = 0 := by
    have hp : (DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) ^ 2 =
        DihedralGroup.r ((2 : ZMod (2 ^ m)) * ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) := by
      rw [pow_two, DihedralGroup.r_mul_r]
      congr 1
      ring
    have hsqr : DihedralGroup.r ((2 : ZMod (2 ^ m)) * ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) = 1 := by
      rw [← hp]
      exact hsq'
    exact DihedralGroup.r.inj (by
      rw [hsqr, DihedralGroup.one_def])
  have hcases := two_mul_eq_zero_of_zmod (by omega : 1 ≤ m)
    ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) h4
  have hne1 : DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m))) ≠ 1 := by
    intro h1
    have hord : orderOf (DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) = 2 := by
      simpa [hx'] using hx2
    rw [h1, orderOf_one] at hord
    norm_num at hord
  rcases hcases with h0 | hpow
  · exfalso
    apply hne1
    rw [h0]
    rfl
  · simpa [dCentral, hpow, Nat.cast_pow]

private lemma center_le_evenRotations {m : ℕ} (hm : 2 ≤ m) :
    (Subgroup.center (DihedralGroup (2 ^ m)) : Set (DihedralGroup (2 ^ m))) ≤
      (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) := by
  intro x hx
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hcomm := Subgroup.mem_center_iff.mp hx (DihedralGroup.sr (0 : ZMod (2 ^ m)))
    have hneg : i = -i := by
      simpa [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] using hcomm
    have hsq : (DihedralGroup.r i : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
      rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def]
      congr 1
      calc
        i + i = i + -i := congrArg (fun z => i + z) hneg
        _ = 0 := by simp
    have hord2 : orderOf (DihedralGroup.r i : DihedralGroup (2 ^ m)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    have h2pow : 2 ∣ 2 ^ (m - 1) := by
      change (2 : ℕ) ^ 1 ∣ 2 ^ (m - 1)
      exact pow_dvd_pow (2 : ℕ) (by omega : 1 ≤ m - 1)
    exact rotation_mem_even_of_orderOf_dvd (by omega) _
      (by
        rw [dihedralRotationSubgroup_def]
        simpa using r_mem_zpowers_r_one i)
      (hord2.trans h2pow)
  · exfalso
    have hcomm := Subgroup.mem_center_iff.mp hx (DihedralGroup.r (1 : ZMod (2 ^ m)))
    have hi : i - 1 = i + 1 := by
      simpa [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] using hcomm
    have htwo : (2 : ZMod (2 ^ m)) = 0 := by
      have h1 : (1 : ZMod (2 ^ m)) = -1 := by
        have hi' : i + 1 = i + (-1 : ZMod (2 ^ m)) := by
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hi.symm
        exact add_left_cancel hi'
      rw [show (2 : ZMod (2 ^ m)) = 1 + 1 by norm_num]
      nth_rewrite 1 [h1]
      abel
    have htwo_nat : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by simpa using htwo
    have hdvd : 2 ^ m ∣ 2 := by
      have hval : ((2 : ℕ) : ZMod (2 ^ m)).val = 0 := by
        exact (ZMod.val_eq_zero ((2 : ℕ) : ZMod (2 ^ m))).mpr htwo_nat
      rw [ZMod.val_natCast] at hval
      exact Nat.dvd_iff_mod_eq_zero.mpr hval
    have hlt : 2 < 2 ^ m := by
      have hpow : 4 ≤ 2 ^ m := by
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hm)
      omega
    exact (not_le_of_gt hlt) (Nat.le_of_dvd (by norm_num : 0 < 2) hdvd)

private lemma mem_closure_evenRotations_sup_refl_iff {m : ℕ} (hm : 2 ≤ m)
    (R : Set (DihedralGroup (2 ^ m)))
    (hR : R ⊆ reflClass m 0 ∪ reflClass m 1) (x : DihedralGroup (2 ^ m)) :
    x ∈ Subgroup.closure
        ((dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) ∪ R) ↔
      x ∈ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) ∨
        ((∃ i : ZMod (2 ^ m), x = DihedralGroup.sr i) ∧
          (x ∈ reflClass m 0 → (R ∩ reflClass m 0).Nonempty) ∧
          (x ∈ reflClass m 1 → (R ∩ reflClass m 1).Nonempty)) ∨
        ((R ∩ reflClass m 0).Nonempty ∧ (R ∩ reflClass m 1).Nonempty) := by
  classical
  let B : Set (DihedralGroup (2 ^ m)) := dihedralRotationSubgroup m 1
  let C0 : Set (DihedralGroup (2 ^ m)) := reflClass m 0
  let C1 : Set (DihedralGroup (2 ^ m)) := reflClass m 1
  let cov0 : Prop := (R ∩ C0).Nonempty
  let cov1 : Prop := (R ∩ C1).Nonempty
  let P : Set (DihedralGroup (2 ^ m)) :=
    {x | x ∈ B ∨ ((∃ i, x = DihedralGroup.sr i) ∧
      (x ∈ C0 → cov0) ∧ (x ∈ C1 → cov1)) ∨ (cov0 ∧ cov1)}
  have hcov0_univ : cov0 → cov1 → ∀ x, x ∈ P := by
    intro hc0 hc1 x
    exact Or.inr (Or.inr ⟨hc0, hc1⟩)
  have hcov0_E0 : cov0 → ¬ cov1 → P = (dihedralIndexTwoSubgroup m 0 : Set _) := by
    intro hc0 hnc1
    ext z
    constructor
    · intro hz
      rcases hz with hzB | hzr | hzcov
      · rw [← reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 0]
        exact Or.inr hzB
      · rcases hzr with ⟨⟨i, rfl⟩, hz0, hz1⟩
        rcases sr_mem_reflClass_zero_or_one m i with hzi0 | hzi1
        · rw [← reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 0]
          exact Or.inl hzi0
        · exfalso
          exact hnc1 (hz1 hzi1)
      · exact False.elim (hnc1 hzcov.2)
    · intro hz
      have hz' : z ∈ reflClass m 0 ∪ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) := by
        simpa [reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 0] using hz
      rcases hz' with hzC0 | hzB
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · rcases hzC0 with ⟨k, hk⟩
          exact ⟨0 + (2 : ZMod (2 ^ m)) * k, hk⟩
        · intro hzC0'
          exact hc0
        · intro hzC1
          exact False.elim (reflClass_zero_not_mem_reflClass_one (by omega : 1 ≤ m) z hzC0 hzC1)
      · exact Or.inl hzB
  have hcov1_E1 : ¬ cov0 → cov1 → P = (dihedralIndexTwoSubgroup m 1 : Set _) := by
    intro hnc0 hc1
    ext z
    constructor
    · intro hz
      rcases hz with hzB | hzr | hzcov
      · rw [← reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 1]
        exact Or.inr hzB
      · rcases hzr with ⟨⟨i, rfl⟩, hz0, hz1⟩
        rcases sr_mem_reflClass_zero_or_one m i with hzi0 | hzi1
        · exfalso
          exact hnc0 (hz0 hzi0)
        · rw [← reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 1]
          exact Or.inl hzi1
      · exact False.elim (hnc0 hzcov.1)
    · intro hz
      have hz' : z ∈ reflClass m 1 ∪ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) := by
        simpa [reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 1] using hz
      rcases hz' with hzC1 | hzB
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · rcases hzC1 with ⟨k, hk⟩
          exact ⟨1 + (2 : ZMod (2 ^ m)) * k, hk⟩
        · intro hzC0
          exact False.elim (reflClass_zero_not_mem_reflClass_one (by omega : 1 ≤ m) z hzC0 hzC1)
        · intro hzC1'
          exact hc1
      · exact Or.inl hzB
  have hnocov_B : ¬ cov0 → ¬ cov1 → P = B := by
    intro hnc0 hnc1
    ext z
    constructor
    · intro hz
      rcases hz with hzB | hzr | hzcov
      · exact hzB
      · exfalso
        rcases hzr with ⟨⟨i, rfl⟩, hz0, hz1⟩
        rcases sr_mem_reflClass_zero_or_one m i with hzi0 | hzi1
        · exact hnc0 (hz0 hzi0)
        · exact hnc1 (hz1 hzi1)
      · exact False.elim (hnc0 hzcov.1)
    · intro hz
      exact Or.inl hz
  have hB_le_P : B ⊆ P := by
    intro x hx
    exact Or.inl hx
  have hR_le_P : R ⊆ P := by
    intro x hx
    rcases hR hx with hC0 | hC1
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · rcases hC0 with ⟨k, hk⟩
        exact ⟨0 + (2 : ZMod (2 ^ m)) * k, hk⟩
      · intro hxC0
        exact ⟨x, hx, hxC0⟩
      · intro hxC1
        exfalso
        exact reflClass_zero_not_mem_reflClass_one (by omega : 1 ≤ m) x hC0 hxC1
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · rcases hC1 with ⟨k, hk⟩
        exact ⟨1 + (2 : ZMod (2 ^ m)) * k, hk⟩
      · intro hxC0
        exfalso
        exact reflClass_zero_not_mem_reflClass_one (by omega : 1 ≤ m) x hxC0 hC1
      · intro hxC1
        exact ⟨x, hx, hxC1⟩
  have hP_inv : ∀ {x : DihedralGroup (2 ^ m)}, x ∈ P → x⁻¹ ∈ P := by
    intro x hx
    by_cases hc0 : cov0 <;> by_cases hc1 : cov1
    · exact hcov0_univ hc0 hc1 x⁻¹
    · rw [hcov0_E0 hc0 hc1] at hx ⊢
      exact (dihedralIndexTwoSubgroup m 0).inv_mem hx
    · rw [hcov1_E1 hc0 hc1] at hx ⊢
      exact (dihedralIndexTwoSubgroup m 1).inv_mem hx
    · rw [hnocov_B hc0 hc1] at hx ⊢
      exact (dihedralRotationSubgroup m 1).inv_mem hx
  have hP_mul : ∀ {x y : DihedralGroup (2 ^ m)}, x ∈ P → y ∈ P → x * y ∈ P := by
    intro x y hx hy
    by_cases hc0 : cov0 <;> by_cases hc1 : cov1
    · exact hcov0_univ hc0 hc1 (x * y)
    · rw [hcov0_E0 hc0 hc1] at hx hy ⊢
      exact (dihedralIndexTwoSubgroup m 0).mul_mem hx hy
    · rw [hcov1_E1 hc0 hc1] at hx hy ⊢
      exact (dihedralIndexTwoSubgroup m 1).mul_mem hx hy
    · rw [hnocov_B hc0 hc1] at hx hy ⊢
      exact (dihedralRotationSubgroup m 1).mul_mem hx hy
  have hclosure_le_P : Subgroup.closure ((B : Set _) ∪ R) ≤ P := by
    intro x hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyB | hyR
      · exact hB_le_P hyB
      · exact hR_le_P hyR
    · exact hB_le_P ((dihedralRotationSubgroup m 1).one_mem)
    · intro a b ha hb haP hbP
      exact hP_mul haP hbP
    · intro a ha haP
      exact hP_inv haP
  have hP_le_closure : P ⊆ Subgroup.closure ((B : Set _) ∪ R) := by
    intro x hx
    by_cases hc0 : cov0 <;> by_cases hc1 : cov1
    · -- both covered: use sr0, sr1 in R; every element is a product involving them
      rcases hc0 with ⟨r0, hr0R, hr0C0⟩
      rcases hc1 with ⟨r1, hr1R, hr1C1⟩
      have hcl0 : r0 ∈ Subgroup.closure ((B : Set _) ∪ R) := Subgroup.subset_closure (Or.inr hr0R)
      have hcl1 : r1 ∈ Subgroup.closure ((B : Set _) ∪ R) := Subgroup.subset_closure (Or.inr hr1R)
      have hcl_sr0 : DihedralGroup.sr (0 : ZMod (2 ^ m)) ∈
          Subgroup.closure ((B : Set _) ∪ R) := by
        rcases hr0C0 with ⟨k0, hk0⟩
        have hprod0 : DihedralGroup.sr (0 : ZMod (2 ^ m)) =
            r0 * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (-k0)) := by
          rw [hk0, DihedralGroup.sr_mul_r]
          congr 1
          ring
        rw [hprod0]
        exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem hcl0
          (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model (-k0))))
      have hcl_sr1 : DihedralGroup.sr (1 : ZMod (2 ^ m)) ∈
          Subgroup.closure ((B : Set _) ∪ R) := by
        rcases hr1C1 with ⟨k1, hk1⟩
        have hprod1 : DihedralGroup.sr (1 : ZMod (2 ^ m)) =
            r1 * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (-k1)) := by
          rw [hk1, DihedralGroup.sr_mul_r]
          congr 1
          ring
        rw [hprod1]
        exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem hcl1
          (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model (-k1))))
      rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rcases i.val.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
        · refine Subgroup.subset_closure (Or.inl ?_)
          rw [← ZMod.natCast_zmod_val i, hk]
          push_cast
          rw [← two_mul]
          exact r_two_mul_mem_evenRotations_model (k : ZMod (2 ^ m))
        · have hprod : DihedralGroup.r i =
            DihedralGroup.sr 0 * (DihedralGroup.sr 1 * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)))) := by
            rw [← ZMod.natCast_zmod_val i, hk]
            push_cast
            rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
            congr 1
            ring
          rw [hprod]
          exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem hcl_sr0
            ((Subgroup.closure ((B : Set _) ∪ R)).mul_mem hcl_sr1
              (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model k))))
      · rcases sr_mem_reflClass_zero_or_one m i with hzi0 | hzi1
        · rcases hzi0 with ⟨k, hk⟩
          rcases hr0C0 with ⟨k0, hk0⟩
          have hprod : DihedralGroup.sr i =
              r0 * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k - k0)) := by
            rw [hk, hk0, DihedralGroup.sr_mul_r]
            congr 1
            ring
          rw [hprod]
          exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem hcl0
            (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model (k - k0))))
        · rcases hzi1 with ⟨k, hk⟩
          rcases hr1C1 with ⟨k1, hk1⟩
          have hprod : DihedralGroup.sr i =
              r1 * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k - k1)) := by
            rw [hk, hk1, DihedralGroup.sr_mul_r]
            congr 1
            ring
          rw [hprod]
          exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem hcl1
            (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model (k - k1))))
    · -- only cov0
      have hPeq := hcov0_E0 hc0 hc1
      rw [hPeq] at hx
      have hx' : x ∈ reflClass m 0 ∪ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) := by
        simpa [reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 0] using hx
      rcases hx' with hC0x | hBx
      · rcases hC0x with ⟨k, hk⟩
        rcases hc0 with ⟨r, hrR, hrC0⟩
        rcases hrC0 with ⟨k0, hk0⟩
        have hprod : x = r * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k - k0)) := by
          rw [hk, hk0, DihedralGroup.sr_mul_r]
          congr 1
          ring
        rw [hprod]
        exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem
          (Subgroup.subset_closure (Or.inr hrR))
          (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model (k - k0))))
      · exact Subgroup.subset_closure (Or.inl hBx)
    · -- only cov1
      have hPeq := hcov1_E1 hc0 hc1
      rw [hPeq] at hx
      have hx' : x ∈ reflClass m 1 ∪ (dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) := by
        simpa [reflClass_zero_union_evenRotations (by omega : 1 ≤ m) 1] using hx
      rcases hx' with hC1x | hBx
      · rcases hC1x with ⟨k, hk⟩
        rcases hc1 with ⟨r, hrR, hrC1⟩
        rcases hrC1 with ⟨k1, hk1⟩
        have hprod : x = r * DihedralGroup.r ((2 : ZMod (2 ^ m)) * (k - k1)) := by
          rw [hk, hk1, DihedralGroup.sr_mul_r]
          congr 1
          ring
        rw [hprod]
        exact (Subgroup.closure ((B : Set _) ∪ R)).mul_mem
          (Subgroup.subset_closure (Or.inr hrR))
          (Subgroup.subset_closure (Or.inl (r_two_mul_mem_evenRotations_model (k - k1))))
      · exact Subgroup.subset_closure (Or.inl hBx)
    · -- no coverage
      have hPeq := hnocov_B hc0 hc1
      rw [hPeq] at hx
      exact Subgroup.subset_closure (Or.inl hx)
  constructor
  · intro hx
    exact hclosure_le_P hx
  · intro hx
    exact hP_le_closure hx

/-- If both reflection classes are fused to the central involution, the
Grün/focal subgroup is the whole Sylow subgroup. -/
private lemma grun_eq_sylow_of_both_fused
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : fusedClass S e 0) (h1 : fusedClass S e 1) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) = (S : Subgroup G) := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  let R : Set (DihedralGroup (2 ^ m)) :=
    {dCentral m * DihedralGroup.sr 0, dCentral m * DihedralGroup.sr 1}
  have hR : R ⊆ reflClass m 0 ∪ reflClass m 1 := by
    intro x hx
    rcases hx with rfl | rfl
    · exact Or.inl (dCentral_mul_sr_mem_reflClass hm 0)
    · exact Or.inr (dCentral_mul_sr_mem_reflClass hm 1)
  have hcov0 : (R ∩ reflClass m 0).Nonempty :=
    ⟨dCentral m * DihedralGroup.sr 0, by simp [R],
      dCentral_mul_sr_mem_reflClass hm 0⟩
  have hcov1 : (R ∩ reflClass m 1).Nonempty :=
    ⟨dCentral m * DihedralGroup.sr 1, by simp [R],
      dCentral_mul_sr_mem_reflClass hm 1⟩
  have hSleD : (S : Subgroup G) ≤ D := by
    intro s hs
    let sS : S := ⟨s, hs⟩
    have hcl : e sS ∈ Subgroup.closure
        ((dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) ∪ R) := by
      have hiff := mem_closure_evenRotations_sup_refl_iff hm R hR (e sS)
      exact hiff.2 (Or.inr (Or.inr ⟨hcov0, hcov1⟩))
    have hP : ∀ y ∈ Subgroup.closure
        ((dihedralRotationSubgroup m 1 : Set (DihedralGroup (2 ^ m))) ∪ R),
        (e.symm y : G) ∈ D := by
      intro y hy
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro x hx
        rcases hx with hxB | hxR
        · exact evenRotations_le_grunKernel S e
            (ambient_mem_evenRotations_of_model S e hxB)
        · rcases hxR with rfl | rfl
          · exact reflection_of_fusedClass_mem_grun S hm e 0 h0
          · exact reflection_of_fusedClass_mem_grun S hm e 1 h1
      · simpa using D.one_mem
      · intro x y _hx _hy hxP hyP
        have hmul : (e.symm (x * y) : G) = (e.symm x : G) * (e.symm y : G) := by
          rw [← Subgroup.coe_mul, ← map_mul]
        rw [hmul]
        exact D.mul_mem hxP hyP
      · intro x _hx hxP
        have hinv : (e.symm x⁻¹ : G) = (e.symm x : G)⁻¹ := by
          rw [← Subgroup.coe_inv, ← map_inv]
        rw [hinv]
        exact D.inv_mem hxP
    have hsD : (e.symm (e sS) : G) ∈ D := hP (e sS) hcl
    simpa [sS] using hsD
  have hDleS : D ≤ (S : Subgroup G) := by
    change huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤ (S : Subgroup G)
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    exact inf_le_left
  exact le_antisymm hDleS hSleD

/-- If the Grün subgroup is the one reflection extension, exactly the one
reflection class is fused to the central involution. -/
private lemma fused_one_of_grun_eq_indexTwo_one
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (hD : huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) =
      indexTwoAmbient S e 1) :
    fusedClass S e 1 ∧ ¬ fusedClass S e 0 := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = indexTwoAmbient S e 1 := hD
  by_cases h1 : fusedClass S e 1
  · constructor
    · exact h1
    · intro h0
      have hS : D = (S : Subgroup G) :=
        grun_eq_sylow_of_both_fused S hm e h0 h1
      rw [hDeq] at hS
      have hsS : (e.symm (DihedralGroup.r 1) : G) ∈ (S : Subgroup G) :=
        (e.symm (DihedralGroup.r 1)).property
      have hsE : (e.symm (DihedralGroup.r 1) : G) ∈ indexTwoAmbient S e 1 := by
        simpa [hS] using hsS
      exact not_mem_indexTwoAmbient_of_model_not S e 1
        (r_one_not_mem_dihedralIndexTwoSubgroup (by omega : 1 ≤ m) 1) hsE
  · exfalso
    by_cases h0 : fusedClass S e 0
    · have hle : D ≤ indexTwoAmbient S e 0 :=
        focalSubgroup_le_indexTwo_of_fusion S hm e 0
          (fun p hp => fusedReflSet_subset_indexTwo_of_fused0_not1
            S hm e h0 h1 (p := p) hp)
          (by intro hiff; exact h1 (hiff.mp h0))
      rw [hDeq] at hle
      have hsE1 : (e.symm (DihedralGroup.sr 1) : G) ∈ indexTwoAmbient S e 1 :=
        ambient_mem_indexTwo_of_model S e 1 (sr_mem_indexTwo (by omega : 1 ≤ m) 1)
      exact not_mem_indexTwoAmbient_of_model_not S e 0
        (sr1_not_mem_indexTwo_zero (by omega : 1 ≤ m)) (hle hsE1)
    · have hle : D ≤ allRotationsAmbient S e :=
        focalSubgroup_le_allRotations_of_no_fused S hm e h0 h1
      rw [hDeq] at hle
      have hsE1 : (e.symm (DihedralGroup.sr 1) : G) ∈ indexTwoAmbient S e 1 :=
        ambient_mem_indexTwo_of_model S e 1 (sr_mem_indexTwo (by omega : 1 ≤ m) 1)
      exact not_mem_allRotationsAmbient_of_model_not S e
        (sr_not_mem_allRotations 1) (hle hsE1)

/-- If the Grün subgroup is the zero reflection extension, exactly the zero
reflection class is fused to the central involution. -/
private lemma fused_zero_of_grun_eq_indexTwo_zero
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (hD : huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) =
      indexTwoAmbient S e 0) :
    fusedClass S e 0 ∧ ¬ fusedClass S e 1 := by
  classical
  let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  have hDeq : D = indexTwoAmbient S e 0 := hD
  by_cases h0 : fusedClass S e 0
  · constructor
    · exact h0
    · intro h1
      have hS : D = (S : Subgroup G) :=
        grun_eq_sylow_of_both_fused S hm e h0 h1
      rw [hDeq] at hS
      have hsS : (e.symm (DihedralGroup.r 1) : G) ∈ (S : Subgroup G) :=
        (e.symm (DihedralGroup.r 1)).property
      have hsE : (e.symm (DihedralGroup.r 1) : G) ∈ indexTwoAmbient S e 0 := by
        simpa [hS] using hsS
      exact not_mem_indexTwoAmbient_of_model_not S e 0
        (r_one_not_mem_dihedralIndexTwoSubgroup (by omega : 1 ≤ m) 0) hsE
  · exfalso
    by_cases h1 : fusedClass S e 1
    · have hle : D ≤ indexTwoAmbient S e 1 :=
        focalSubgroup_le_indexTwo_of_fusion S hm e 1
          (fun p hp => fusedReflSet_subset_indexTwo_of_fused1_not0
            S hm e h1 h0 (p := p) hp)
          (by intro hiff; exact h0 (hiff.mpr h1))
      rw [hDeq] at hle
      have hsE0 : (e.symm (DihedralGroup.sr 0) : G) ∈ indexTwoAmbient S e 0 :=
        ambient_mem_indexTwo_of_model S e 0 (sr_mem_indexTwo (by omega : 1 ≤ m) 0)
      exact not_mem_indexTwoAmbient_of_model_not S e 1
        (sr0_not_mem_indexTwo_one (by omega : 1 ≤ m)) (hle hsE0)
    · have hle : D ≤ allRotationsAmbient S e :=
        focalSubgroup_le_allRotations_of_no_fused S hm e h0 h1
      rw [hDeq] at hle
      have hsE0 : (e.symm (DihedralGroup.sr 0) : G) ∈ indexTwoAmbient S e 0 :=
        ambient_mem_indexTwo_of_model S e 0 (sr_mem_indexTwo (by omega : 1 ≤ m) 0)
      exact not_mem_allRotationsAmbient_of_model_not S e
        (sr_not_mem_allRotations 0) (hle hsE0)

/-- An involution of a Sylow subgroup with both reflection classes fused is
conjugate to the central involution. -/
private lemma isConj_z_of_involution_in_sylow
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : fusedClass S e 0) (h1 : fusedClass S e 1)
    {x : G} (hxS : x ∈ (S : Subgroup G))
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    IsConj (zAmbient S e) x := by
  classical
  let xS : S := ⟨x, hxS⟩
  let a : DihedralGroup (2 ^ m) := e xS
  have hxord : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx2) hx1
  have hxSord : orderOf xS = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa [pow_two] using hx2
    · intro h
      apply hx1
      exact congrArg Subtype.val h
  have haord : orderOf a = 2 := by
    simpa [a] using (MulEquiv.orderOf_eq e xS).trans hxSord
  rcases dihedralGroup_cases a with ⟨i, hai⟩ | ⟨i, hai⟩
  · have hord_i : orderOf (DihedralGroup.r i) = 2 := by simpa [hai] using haord
    have hz : DihedralGroup.r i = dCentral m :=
      rotation_order_two_eq_dCentral (by omega : 1 ≤ m) i hord_i
    have hxz : x = zAmbient S e := by
      dsimp [zAmbient]
      have h1 : (e.symm (e xS) : G) = x := by simp [xS]
      have h2 : (e.symm (DihedralGroup.r i) : G) =
          (e.symm (dCentral m) : G) := by rw [hz]
      have h3 : (e.symm a : G) = (e.symm (DihedralGroup.r i) : G) := by
        rw [hai]
      calc
        x = (e.symm (e xS) : G) := h1.symm
        _ = (e.symm a : G) := rfl
        _ = (e.symm (DihedralGroup.r i) : G) := h3
        _ = (e.symm (dCentral m) : G) := h2
    rw [hxz]
  · rcases sr_mem_reflClass_zero_or_one m i with hi0 | hi1
    · rcases hi0 with ⟨k, hk⟩
      have hi_eq : i = (0 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k :=
        DihedralGroup.sr.inj hk
      have hzi : IsConj (zAmbient S e)
          (e.symm (DihedralGroup.sr i) : G) := by
        simpa [hi_eq, fusedClass] using
          (isConj_z_sr_of_sameClass S e (i := 0) h0 k)
      have hxeq : x = (e.symm (DihedralGroup.sr i) : G) := by
        have h := congrArg (fun y : DihedralGroup (2 ^ m) => (e.symm y : G)) hai
        simpa [a, xS] using h
      rw [hxeq]
      exact hzi

    · rcases hi1 with ⟨k, hk⟩
      have hi_eq : i = (1 : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) * k :=
        DihedralGroup.sr.inj hk
      have hzi : IsConj (zAmbient S e)
          (e.symm (DihedralGroup.sr i) : G) := by
        simpa [hi_eq, fusedClass] using
          (isConj_z_sr_of_sameClass S e (i := 1) h1 k)
      have hxeq : x = (e.symm (DihedralGroup.sr i) : G) := by
        have h := congrArg (fun y : DihedralGroup (2 ^ m) => (e.symm y : G)) hai
        simpa [a, xS] using h
      rw [hxeq]
      exact hzi

/-- Every involution of `G` is conjugate to the central involution of a fixed
Sylow subgroup when both reflection classes are fused. -/
private lemma exists_isConj_z_of_involution
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : fusedClass S e 0) (h1 : fusedClass S e 1)
    {x : G} (hx : IsInvolution x) :
    IsConj (zAmbient S e) x := by
  classical
  let H : Subgroup G := Subgroup.zpowers x
  have hxord : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx.2) hx.1
  have hHp : IsPGroup 2 H := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hxord]
    norm_num
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow (p := 2) (G := G) hHp
  have hxP : x ∈ (P : Subgroup G) := hPle (Subgroup.mem_zpowers x)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hxS : g * x * g⁻¹ ∈ (S : Subgroup G) := by
    have hsmul : (MulAut.conj g) x ∈ (MulAut.conj g) • (P : Set G) :=
      Set.smul_mem_smul_set hxP
    have hS : (MulAut.conj g) • (P : Set G) = (S : Set G) := by
      rw [← Sylow.coe_smul, hg]
    have hxS' : g * x * g⁻¹ ∈ (S : Set G) := by
      simpa [MulAut.conj_apply, hS] using hsmul
    exact hxS'
  have hy2 : (g * x * g⁻¹) ^ 2 = 1 := by
    calc
      (g * x * g⁻¹) ^ 2 = g * (x * x) * g⁻¹ := by
        rw [pow_two]
        group
      _ = g * 1 * g⁻¹ := by rw [← pow_two, hx.2]
      _ = 1 := by simp
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx.1
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by simp
  have hconj : IsConj (zAmbient S e) (g * x * g⁻¹) :=
    isConj_z_of_involution_in_sylow S hm e h0 h1 hxS hy2 hy1
  have hyx : IsConj (g * x * g⁻¹) x := by
    rw [isConj_iff]
    refine ⟨g⁻¹, ?_⟩
    group
  exact hconj.trans hyx

/-- With both reflection classes fused, all involutions of `G` are
conjugate. -/
private lemma involutions_conjugate_of_both_fused
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (h0 : fusedClass S e 0) (h1 : fusedClass S e 1) :
    ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y := by
  intro x y hx hy
  have hxz := exists_isConj_z_of_involution S hm e h0 h1 hx
  have hyz := exists_isConj_z_of_involution S hm e h0 h1 hy
  have hxy : IsConj x y := hxz.symm.trans hyz
  rw [isConj_iff] at hxy
  exact hxy

/-! ## The Klein-four Sylow case (`m = 1`) -/

/-- In a Klein-four group, an automorphism with neither itself nor its square
trivial acts transitively on the three nonidentity elements. -/
private lemma kleinFour_aut_orbit_all
    {K : Type u} [Group K] [IsKleinFour K]
    (φ : MulAut K) (_hφ1 : φ ≠ 1) (hφ2 : φ ^ 2 ≠ 1) :
    ∀ a b : K, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (φ ^ k) a = b := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by simp [IsKleinFour.card_four])
  let : Fintype K := Fintype.ofFinite K
  intro a b ha hb
  have hfix_none : ∀ x : K, x ≠ 1 → φ x ≠ x := by
    intro x hx hfix
    exact hφ2 (mulAut_sq_eq_one_of_fixed_ne_one φ hx hfix)
  have hφa1 : φ a ≠ 1 := by
    intro h
    apply ha
    exact φ.injective (by simpa using h)
  have hφa_ne_a : φ a ≠ a := hfix_none a ha
  have hφ2a1 : φ (φ a) ≠ 1 := by
    intro h
    apply hφa1
    exact φ.injective (by simpa using h)
  have hφ2a_ne_φa : φ (φ a) ≠ φ a := hfix_none (φ a) hφa1
  have hφ2a_ne_a : φ (φ a) ≠ a := by
    intro h
    let z : K := a * φ a
    have hz1 : z ≠ 1 := by
      intro hz
      have hφa_eq : φ a = a := by
        calc
          φ a = ((φ a)⁻¹)⁻¹ := by simp
          _ = a⁻¹ := by rw [← mul_eq_one_iff_eq_inv.mp hz]
          _ = a := IsKleinFour.inv_eq_self a
      exact False.elim (hfix_none a ha hφa_eq)
    have hφz : φ z = z := by
      calc
        φ z = φ (a * φ a) := rfl
        _ = φ a * φ (φ a) := map_mul φ a (φ a)
        _ = φ a * a := by rw [h]
        _ = a * φ a := (IsKleinFour.isMulCommutative (G := K)).is_comm.comm (φ a) a
        _ = z := rfl
    exact hfix_none z hz1 hφz
  have hφ2a_eq : φ (φ a) = a * φ a :=
    IsKleinFour.eq_mul_of_ne_all (x := a) (y := φ a) (z := φ (φ a))
      ha hφa1 hφa_ne_a.symm hφ2a1 hφ2a_ne_a hφ2a_ne_φa
  have hmem : b ∈ ({a * φ a, a, φ a, (1 : K)} : Finset K) := by
    rw [IsKleinFour.eq_finset_univ ha hφa1 hφa_ne_a.symm]
    exact Finset.mem_univ b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hb2 | hb1 | hbφ | hb0
  · refine ⟨2, ?_⟩
    simpa [pow_two, hb2] using hφ2a_eq
  · exact ⟨0, by simpa [hb1]⟩
  · exact ⟨1, by simpa [hbφ]⟩
  · exfalso
    exact hb hb0

/-- A Sylow `2`-subgroup of dihedral order four is a Klein-four group. -/
private lemma m1_sylow_isKleinFour {G : Type u} [Group G]
    (S : Sylow 2 G) {m : ℕ} (hm : m = 1)
    (e : S ≃* DihedralGroup (2 ^ m)) : IsKleinFour (S : Subgroup G) := by
  classical
  subst m
  let e2 : S ≃* DihedralGroup 2 := e
  exact {
    card_four := by
      have hc := Nat.card_congr e2.toEquiv
      simpa using hc.trans (inferInstance : IsKleinFour (DihedralGroup 2)).card_four
    exponent_two := by
      rw [Monoid.exponent_eq_of_mulEquiv e2]
      exact (inferInstance : IsKleinFour (DihedralGroup 2)).exponent_two
  }

/-- If a normalizer element of `S` has square in the centralizer but is not
there itself, then two divides the relative index of the centralizer in the
normalizer. -/
private lemma two_dvd_centralizer_relIndex_normalizer_of_sq_mem_not_mem
    {G : Type u} [Group G] [Finite G] (S : Subgroup G)
    {n : G} (hnN : n ∈ Subgroup.normalizer (S : Set G))
    (hnC : n ∉ Subgroup.centralizer (S : Set G))
    (hn2C : n ^ 2 ∈ Subgroup.centralizer (S : Set G)) :
    2 ∣ (Subgroup.centralizer (S : Set G)).relIndex (Subgroup.normalizer (S : Set G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (S : Set G)
  let C : Subgroup N := (Subgroup.centralizer (S : Set G)).subgroupOf N
  have : C.Normal := Subgroup.normal_subgroupOf_centralizer_normalizer (S : Set G)
  let q : N ⧸ C := QuotientGroup.mk ⟨n, hnN⟩
  have hq1 : q ≠ 1 := by
    intro hq
    apply hnC
    have hmem : ⟨n, hnN⟩ ∈ C := (QuotientGroup.eq_one_iff (N := C) (x := ⟨n, hnN⟩)).mp hq
    exact hmem
  have hq2 : q ^ 2 = 1 := by
    change (QuotientGroup.mk (⟨n, hnN⟩ ^ 2) : N ⧸ C) = 1
    apply (QuotientGroup.eq_one_iff (N := C) (x := ⟨n, hnN⟩ ^ 2)).mpr
    change n ^ 2 ∈ Subgroup.centralizer (S : Set G)
    exact hn2C
  have hqord : orderOf q = 2 := orderOf_eq_prime hq2 hq1
  have hdvd : 2 ∣ Nat.card (N ⧸ C) := by
    rw [← hqord]
    exact orderOf_dvd_natCard q
  change 2 ∣ (Subgroup.centralizer (S : Set G)).relIndex N
  rw [Subgroup.relIndex]
  change 2 ∣ Nat.card (N ⧸ C)
  exact hdvd

/-- The `k`-th power of the conjugation automorphism of a normalizer element
is conjugation by the `k`-th power. -/
private lemma normalizerMonoidHom_pow_apply
    {G : Type u} [Group G] (H : Subgroup G) (n : G)
    (hn : n ∈ Subgroup.normalizer (H : Set G)) (k : ℕ) (x : H) :
    (H.normalizerMonoidHom ⟨n, hn⟩ ^ k) x =
      ⟨n ^ k * (x : G) * (n ^ k)⁻¹,
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set G)).pow_mem hn k) (x : G)).1 x.2⟩ := by
  induction k generalizing x with
  | zero =>
      rw [pow_zero, MulAut.one_apply]
      apply Subtype.ext
      simp
  | succ k ih =>
      rw [pow_succ, MulAut.mul_apply]
      have hbase : H.normalizerMonoidHom ⟨n, hn⟩ x =
          ⟨n * (x : G) * n⁻¹,
            (Subgroup.mem_normalizer_iff.mp hn (x : G)).1 x.2⟩ := by
        rfl
      rw [hbase]
      rw [ih ⟨n * (x : G) * n⁻¹,
        (Subgroup.mem_normalizer_iff.mp hn (x : G)).1 x.2⟩]
      apply Subtype.ext
      change n ^ k * (n * (x : G) * n⁻¹) * (n ^ k)⁻¹ =
        n ^ (k + 1) * (x : G) * (n ^ (k + 1))⁻¹
      rw [pow_succ]
      group

private theorem case1_no_index_two_fusion_and_normalizer
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (hno2 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) :
    (∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y) ∧
      (∀ S : Sylow 2 G, ∀ Z : Subgroup G, Z ≤ (S : Subgroup G) →
        IsKleinFour Z → NormalizerContainsCPrime Z) := by
  classical
  let S0 : Sylow 2 G := Classical.choice Sylow.nonempty
  obtain ⟨m, hm, ⟨e⟩⟩ := hdihedral S0
  have hcard (Q : Sylow 2 G) {n : ℕ} (hn : 1 ≤ n)
      (eqQ : Q ≃* DihedralGroup (2 ^ n)) :
      Nat.card (Q : Subgroup G) = 2 * 2 ^ n := by
    have hc := Nat.card_congr eqQ.toEquiv
    rw [DihedralGroup.nat_card] at hc
    exact hc
  by_cases hm2 : 2 ≤ m
  · have hD0 : huppertIV34GrunKernelSubgroup (Q := G) (S0 : Subgroup G) =
        (S0 : Subgroup G) :=
      grunKernel_eq_sylow_of_no_normal_index_two hdihedral S0 hno2
    have hFused0 := both_fused_of_grun_eq_sylow S0 hm2 e hD0
    have hConjAll :=
      involutions_conjugate_of_both_fused S0 hm2 e hFused0.1 hFused0.2
    have hNorm : ∀ S' : Sylow 2 G, ∀ Z : Subgroup G,
        Z ≤ (S' : Subgroup G) → IsKleinFour Z → NormalizerContainsCPrime Z := by
      intro S' Z hZleS' hZ
      obtain ⟨m', hm', ⟨e'⟩⟩ := hdihedral S'
      have hm2' : 2 ≤ m' := by
        by_contra h
        have hsmall : 2 * 2 ^ m' ≤ 4 := by
          interval_cases m' <;> norm_num
        have hpow : 4 ≤ 2 ^ m := by
          exact Nat.pow_le_pow_right (by decide : 0 < 2) hm2
        have hbig : 8 ≤ 2 * 2 ^ m := by nlinarith
        have hcardEq : Nat.card (S0 : Subgroup G) =
            Nat.card (S' : Subgroup G) := by
          exact Nat.card_congr (Sylow.equiv S0 S').toEquiv
        have hbigS' : 8 ≤ Nat.card (S' : Subgroup G) := by
          rw [← hcardEq, hcard S0 hm e]
          exact hbig
        rw [hcard S' hm' e'] at hbigS'
        omega
      have hD' : huppertIV34GrunKernelSubgroup (Q := G) (S' : Subgroup G) =
          (S' : Subgroup G) :=
        grunKernel_eq_sylow_of_no_normal_index_two hdihedral S' hno2
      have hFused' := both_fused_of_grun_eq_sylow S' hm2' e' hD'
      rcases exists_noncentral_of_kleinFour_le_sylow S' hm2' e' hZleS' hZ with
        ⟨a, haZ, ha1, haz, ha2, hzZ⟩
      have haS' : a ∈ (S' : Subgroup G) := hZleS' haZ
      have hconj : IsConj (zAmbient S' e') a :=
        isConj_z_of_involution_in_sylow S' hm2' e' hFused'.1 hFused'.2
          haS' ha2 ha1
      rcases fusion_to_normalizer_moves_central S' hm2' e' hZleS' hZ
        haZ ha1 haz hconj with ⟨n, hN, hnz, hna⟩
      obtain ⟨γ, _hγS, hγN, hγfix, hγmove, _hγAll⟩ :=
        exists_dihedral_transposition_of_kleinFour_le_sylow S' hm2' e' hZleS' hZ
      have hγa_ne : γ * a * γ⁻¹ ≠ a :=
        hγmove Z hZleS' hZ a haZ ha1 haz
      have hγa : γ * a * γ⁻¹ = zAmbient S' e' * a :=
        kleinFour_action_fix_move Z hZ (x := zAmbient S' e') (y := a) (δ := γ)
          hzZ haZ (zAmbient_ne_one S' (by omega : 1 ≤ m') e') ha1 haz.symm
          hγN hγfix hγa_ne
      exact normalizerContainsCPrime_of_two_transpositions Z hZ
        (z := zAmbient S' e') (a := a) (γ := γ) (γ' := n) hzZ haZ
        (zAmbient_ne_one S' (by omega : 1 ≤ m') e') ha1 haz.symm
        hγN hN hγfix hγa hna hnz
    exact ⟨hConjAll, hNorm⟩
  · have hm1 : m = 1 := by omega
    let S : Subgroup G := (S0 : Subgroup G)
    have hScard : Nat.card S = 4 := by
      dsimp [S]
      rw [hcard S0 hm e, hm1]
      norm_num
    let : IsKleinFour S := by
      dsimp [S]
      exact m1_sylow_isKleinFour S0 hm1 e
    have hSC : S ≤ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.le_centralizer_iff_isMulCommutative]
      exact IsKleinFour.isMulCommutative (G := S)
    have hNC : ¬ (Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) := by
      intro hNC'
      let K : Subgroup G := (MonoidHom.transferSylow S0 hNC').ker
      have : K.Normal := inferInstance
      have hKindex : K.index = 4 := by
        have h := (Subgroup.IsComplement'.symm
          (MonoidHom.ker_transferSylow_isComplement' S0 hNC')).index_eq_card
        change K.index = Nat.card (S0 : Subgroup G) at h
        rw [h, hScard]
      exact hno2 (normal_index_two_of_normal_index_four ⟨K, inferInstance, hKindex⟩)
    have hNexists : ∃ n : G,
        n ∈ Subgroup.normalizer (S : Set G) ∧ n ∉ Subgroup.centralizer (S : Set G) := by
      by_contra h
      apply hNC
      intro x hx
      by_contra hxC
      exact h ⟨x, hx, hxC⟩
    rcases hNexists with ⟨n, hnN, hnC⟩
    have hn2C : n ^ 2 ∉ Subgroup.centralizer (S : Set G) := by
      intro hn2C'
      have h2dvd : 2 ∣ (Subgroup.centralizer (S : Set G)).relIndex
          (Subgroup.normalizer (S : Set G)) :=
        two_dvd_centralizer_relIndex_normalizer_of_sq_mem_not_mem S hnN hnC hn2C'
      have hdvd1 : (Subgroup.centralizer (S : Set G)).relIndex
            (Subgroup.normalizer (S : Set G)) ∣
          S.relIndex (Subgroup.normalizer (S : Set G)) :=
        Subgroup.relIndex_dvd_of_le_left (L := Subgroup.normalizer (S : Set G)) hSC
      have hdvd2 : S.relIndex (Subgroup.normalizer (S : Set G)) ∣ S.index :=
        Subgroup.relIndex_dvd_index_of_le S.le_normalizer
      have h2dvdS : 2 ∣ S.index := h2dvd.trans (hdvd1.trans hdvd2)
      exact S0.not_dvd_index (by simpa [S] using h2dvdS)
    let φ : MulAut S := S.normalizerMonoidHom ⟨n, hnN⟩
    have hφ1 : φ ≠ 1 := by
      intro hφ
      apply hnC
      have hker : ⟨n, hnN⟩ ∈ S.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hφ
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      rw [Subgroup.mem_subgroupOf] at hker
      exact hker
    have hφ2 : φ ^ 2 ≠ 1 := by
      intro hφ2'
      apply hn2C
      have hφ2eq : φ ^ 2 = S.normalizerMonoidHom (⟨n, hnN⟩ ^ 2) := by
        dsimp [φ]
        exact (map_pow S.normalizerMonoidHom ⟨n, hnN⟩ 2).symm
      rw [hφ2eq] at hφ2'
      have hker : ⟨n, hnN⟩ ^ 2 ∈ S.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hφ2'
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      change n ^ 2 ∈ Subgroup.centralizer (S : Set G)
      rw [Subgroup.mem_subgroupOf] at hker
      exact hker
    have horbit : ∀ a b : S, a ≠ 1 → b ≠ 1 →
        ∃ n' : G, n' ∈ Subgroup.normalizer (S : Set G) ∧
          n' * (a : G) * n'⁻¹ = (b : G) := by
      intro a b ha hb
      rcases kleinFour_aut_orbit_all φ hφ1 hφ2 a b ha hb with ⟨k, hk⟩
      refine ⟨n ^ k, (Subgroup.normalizer (S : Set G)).pow_mem hnN k, ?_⟩
      have hpow := normalizerMonoidHom_pow_apply S n hnN k a
      exact congrArg Subtype.val (hpow.symm.trans hk)
    have hCprimeS : NormalizerContainsCPrime S :=
      (normalizerContainsCPrime_iff_exists S).mpr ⟨n, hnN, hn2C⟩
    have hConjAll : ∀ x y : G, IsInvolution x → IsInvolution y →
        ∃ g : G, g * x * g⁻¹ = y := by
      intro x y hx hy
      let X : Subgroup G := Subgroup.zpowers x
      have hxord : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx.2) hx.1
      have hXp : IsPGroup 2 X := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, hxord]
        norm_num
      obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow (p := 2) (G := G) hXp
      have hxP : x ∈ (P : Subgroup G) := hPle (Subgroup.mem_zpowers x)
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S0
      have hxg : g * x * g⁻¹ ∈ (S0 : Subgroup G) := by
        have hsmul : (MulAut.conj g) x ∈ (MulAut.conj g) • (P : Set G) :=
          Set.smul_mem_smul_set hxP
        have hS : (MulAut.conj g) • (P : Set G) = (S0 : Set G) := by
          rw [← Sylow.coe_smul, hg]
        have hxS' : g * x * g⁻¹ ∈ (S0 : Set G) := by
          simpa [MulAut.conj_apply, hS] using hsmul
        exact hxS'
      have hxg1 : g * x * g⁻¹ ≠ 1 := by
        intro h
        apply hx.1
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h]
          _ = 1 := by simp
      let Y : Subgroup G := Subgroup.zpowers y
      have hyord : orderOf y = 2 := orderOf_eq_prime (by simpa [pow_two] using hy.2) hy.1
      have hYp : IsPGroup 2 Y := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, hyord]
        norm_num
      obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow (p := 2) (G := G) hYp
      have hyQ : y ∈ (Q : Subgroup G) := hQle (Subgroup.mem_zpowers y)
      obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G Q S0
      have hyh : h * y * h⁻¹ ∈ (S0 : Subgroup G) := by
        have hsmul : (MulAut.conj h) y ∈ (MulAut.conj h) • (Q : Set G) :=
          Set.smul_mem_smul_set hyQ
        have hS : (MulAut.conj h) • (Q : Set G) = (S0 : Set G) := by
          rw [← Sylow.coe_smul, hh]
        have hyS' : h * y * h⁻¹ ∈ (S0 : Set G) := by
          simpa [MulAut.conj_apply, hS] using hsmul
        exact hyS'
      have hyh1 : h * y * h⁻¹ ≠ 1 := by
        intro hr
        apply hy.1
        calc
          y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = h⁻¹ * 1 * h := by rw [hr]
          _ = 1 := by simp
      rcases horbit ⟨g * x * g⁻¹, hxg⟩ ⟨h * y * h⁻¹, hyh⟩
        (by simpa using hxg1) (by simpa using hyh1) with ⟨n', hn'N, hn'⟩
      refine ⟨h⁻¹ * n' * g, ?_⟩
      calc
        (h⁻¹ * n' * g) * x * (h⁻¹ * n' * g)⁻¹ =
            h⁻¹ * (n' * (g * x * g⁻¹) * n'⁻¹) * h := by group
        _ = h⁻¹ * (h * y * h⁻¹) * h := by rw [hn']
        _ = y := by group
    have hNorm : ∀ S' : Sylow 2 G, ∀ Z : Subgroup G, Z ≤ (S' : Subgroup G) →
        IsKleinFour Z → NormalizerContainsCPrime Z := by
      intro S' Z hZleS' hZ
      obtain ⟨m', hm', ⟨e'⟩⟩ := hdihedral S'
      have hm2' : ¬ 2 ≤ m' := by
        intro h
        have hpow4 : 4 ≤ 2 ^ m' := Nat.pow_le_pow_right (by decide : 0 < 2) h
        have hbigS' : 8 ≤ Nat.card (S' : Subgroup G) := by
          rw [hcard S' hm' e']
          nlinarith
        have hcardEq : Nat.card (S0 : Subgroup G) = Nat.card (S' : Subgroup G) := by
          exact Nat.card_congr (Sylow.equiv S0 S').toEquiv
        have hsmallS' : Nat.card (S' : Subgroup G) ≤ 4 := by
          rw [← hcardEq]
          simpa [S] using hScard.le
        omega
      have hm1' : m' = 1 := by omega
      let T : Subgroup G := (S' : Subgroup G)
      have hTcard : Nat.card T = 4 := by
        dsimp [T]
        rw [hcard S' hm' e', hm1']
        norm_num
      let : IsKleinFour T := by
        dsimp [T]
        exact m1_sylow_isKleinFour S' hm1' e'
      have hZeq : Z = T := by
        exact Subgroup.eq_of_le_of_card_ge (H := Z) (K := T) hZleS'
          (by simp)
      have hCprimeT : NormalizerContainsCPrime T := by
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 S'
        have hconj : conjugateSubgroup S g = T := by
          have hSyl := congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
          have hdef : ((g • S0 : Sylow 2 G) : Subgroup G) = conjugateSubgroup S g := by
            rw [Sylow.coe_subgroup_smul]
            rfl
          rw [hdef] at hSyl
          simpa [T] using hSyl
        exact (normalizerContainsCPrime_conjugate S T g hconj).mp hCprimeS
      simpa [hZeq] using hCprimeT
    exact ⟨hConjAll, hNorm⟩

/-- If the one-reflection class is not fused to the central involution, the
corresponding Klein-four class has no element of order three in its
normalizer quotient. -/
private lemma not_normalizerContainsCPrime_of_not_fused
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m)) (j : ZMod (2 ^ m))
    (hnot : ¬ fusedClass S e j) :
    ¬ NormalizerContainsCPrime (dKleinAmbient S (by omega : 1 ≤ m) e j) := by
  classical
  let Z₁ : Subgroup G := dKleinAmbient S (by omega : 1 ≤ m) e j
  have hZ₁le : Z₁ ≤ (S : Subgroup G) := dKleinAmbient_le_S S (by omega : 1 ≤ m) e j
  have hZ₁ : IsKleinFour Z₁ := dKleinAmbient_isKleinFour S (by omega : 1 ≤ m) e j
  have hzZ₁ : zAmbient S e ∈ Z₁ := by
    simpa [Z₁] using dCentralAmbient_mem_dKleinAmbient S (by omega : 1 ≤ m) e j
  have hz1 : zAmbient S e ≠ 1 := zAmbient_ne_one S (by omega : 1 ≤ m) e
  intro hN
  rcases (normalizerContainsCPrime_iff_exists Z₁).mp hN with ⟨n, hn, hsq⟩
  have hnz : n * zAmbient S e * n⁻¹ ≠ zAmbient S e := by
    intro hfix
    apply hsq
    let : IsKleinFour Z₁ := hZ₁
    let nsub : Subgroup.normalizer (Z₁ : Set G) := ⟨n, hn⟩
    let φ : MulAut Z₁ := Z₁.normalizerMonoidHom nsub
    let zsub : Z₁ := ⟨zAmbient S e, hzZ₁⟩
    have hzsub1 : zsub ≠ 1 := by
      intro h
      apply hz1
      exact congrArg Subtype.val h
    have hfixsub : φ zsub = zsub := by
      apply Subtype.ext
      exact hfix
    have hφ2 : φ ^ 2 = 1 := mulAut_sq_eq_one_of_fixed_ne_one φ hzsub1 hfixsub
    have hker : nsub ^ 2 ∈ Z₁.normalizerMonoidHom.ker := by
      change Z₁.normalizerMonoidHom (nsub ^ 2) = 1
      rw [map_pow, hφ2]
    have hcen : n ^ 2 ∈ Subgroup.centralizer (Z₁ : Set G) := by
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      exact hker
    exact hcen
  let a : G := n * zAmbient S e * n⁻¹
  have haZ₁ : a ∈ Z₁ :=
    (Subgroup.mem_normalizer_iff.mp hn (zAmbient S e)).1 hzZ₁
  have ha1 : a ≠ 1 := by
    intro h
    apply hz1
    calc
      zAmbient S e = n⁻¹ * a * n := by dsimp [a]; group
      _ = n⁻¹ * 1 * n := by rw [h]
      _ = 1 := by simp
  have haz : a ≠ zAmbient S e := hnz
  have hconj : IsConj (zAmbient S e) a := by
    rw [isConj_iff]
    exact ⟨n, by dsimp [a]⟩
  have haZ₁' : a ∈ dKleinAmbient S (by omega : 1 ≤ m) e j := by
    simpa [Z₁] using haZ₁
  rw [dKleinAmbient, Subgroup.mem_map] at haZ₁'
  rcases haZ₁' with ⟨xS, hxS, hxval⟩
  let p : DihedralGroup (2 ^ m) := e xS
  have hp : p ∈ dKlein m (by omega : 1 ≤ m) j := by
    simpa [dKleinAmbient, p] using hxS
  rw [mem_dKlein_iff (by omega : 1 ≤ m) j p] at hp
  rcases hp with h1 | h2 | h3 | h4
  · exfalso
    apply ha1
    have hxS1 : xS = 1 := by
      apply e.injective
      simpa [p, h1]
    rw [← hxval, hxS1]
    simp
  · exfalso
    apply haz
    have hxS2 : xS = e.symm (dCentral m) := by
      apply e.injective
      simpa [p, h2]
    rw [← hxval, hxS2]
    simp [zAmbient]
  · apply hnot
    have ha_eq : a = (e.symm (DihedralGroup.sr j) : G) := by
      have hxS3 : xS = e.symm (DihedralGroup.sr j) := by
        apply e.injective
        simpa [p, h3]
      rw [← hxval, hxS3]
      rfl
    simpa [fusedClass, ha_eq] using hconj
  · exfalso
    apply hnot
    rcases exists_two_mul_eq_half hm with ⟨k, hk⟩
    have ha_eq : a = (e.symm (DihedralGroup.sr
        (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) := by
      have hxS4 : xS = e.symm (DihedralGroup.sr
          (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) := by
        apply e.injective
        simpa [p, h4]
      rw [← hxval, hxS4]
      rfl
    have hAB : IsConj (e.symm (DihedralGroup.sr j) : G)
        (e.symm (DihedralGroup.sr
          (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) :=
      isConj_ambient_of_model_isConj S e
        (by simpa [hk] using sameClass_isConj_model j (k : ZMod (2 ^ m)))
    have hconj' : IsConj (zAmbient S e)
        (e.symm (DihedralGroup.sr
          (j + (2 : ZMod (2 ^ m)) ^ (m - 1))) : G) := by
      simpa [← ha_eq] using hconj
    have hz1 : IsConj (zAmbient S e) (e.symm (DihedralGroup.sr j) : G) := by
      exact hconj'.trans hAB.symm
    exact hz1

/-- A Sylow `2`-subgroup of a group whose order is twice an odd number has
order two. -/
private lemma sylow_card_two_of_card_two_mul_odd
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hcard : Nat.card G = 2 * n) (hn : Odd n)
    (P : Sylow 2 G) :
    Nat.card (P : Subgroup G) = 2 := by
  classical
  have h2dvdG : 2 ∣ Nat.card G := by
    rw [hcard]
    exact dvd_mul_right 2 n
  have h2dvdP : 2 ∣ Nat.card (P : Subgroup G) := P.dvd_card_of_dvd_card h2dvdG
  rcases (IsPGroup.iff_card (p := 2) (G := P)).mp P.isPGroup' with ⟨a, ha⟩
  have hale : a ≤ 1 := by
    by_contra h
    have h4 : 4 ∣ Nat.card (P : Subgroup G) := by
      rw [ha]
      exact pow_dvd_pow 2 (by omega : 2 ≤ a)
    have h4G : 4 ∣ Nat.card G :=
      h4.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup G))
    have h2dvdn : 2 ∣ n := by
      rcases h4G with ⟨t, ht⟩
      have hmul : 2 * (2 * t) = 2 * n := by
        have h4n : 4 * t = 2 * n := by rw [← hcard, ht]
        nlinarith
      have hcancel : 2 * t = n := Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
      exact ⟨t, hcancel.symm⟩
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h2dvdn)
  have hane0 : a ≠ 0 := by
    intro h0
    have hcardP1 : Nat.card (P : Subgroup G) = 1 := by
      rw [ha, h0]
      norm_num
    have : 2 ∣ (1 : ℕ) := by simpa [hcardP1] using h2dvdP
    norm_num at this
  have ha1 : a = 1 := by omega
  rw [ha, ha1]
  norm_num

/-- If a group has order twice an odd number and its prime `2`-core quotient
is a `2`-group, the prime `2`-core has index two. -/
private lemma pPrimeCore_index_two_of_sylow_two
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hcard : Nat.card G = 2 * n) (hn : Odd n)
    (hNKp : IsPGroup 2 (G ⧸ pPrimeCore 2 G)) :
    (pPrimeCore 2 G).index = 2 := by
  classical
  let K : Subgroup G := pPrimeCore 2 G
  have hKcop : Nat.Coprime 2 (Nat.card K) :=
    pPrimeCore_coprime_card (G := G) (p := 2)
  have h2ndvdK : ¬ 2 ∣ Nat.card K := by
    intro h
    have hgcd : 2 ∣ Nat.gcd 2 (Nat.card K) := Nat.dvd_gcd (dvd_refl 2) h
    have hgcd1 : Nat.gcd 2 (Nat.card K) = 1 := hKcop
    rw [hgcd1] at hgcd
    norm_num at hgcd
  rcases (IsPGroup.iff_card (p := 2) (G := G ⧸ K)).mp hNKp with ⟨a, ha⟩
  have hindex : K.index = 2 ^ a := by
    rw [Subgroup.index_eq_card, ← ha]
  have hprod := Subgroup.card_mul_index (H := K)
  have hale : a ≤ 1 := by
    by_contra h
    have h2le : 2 ≤ a := by omega
    have h4 : 4 ∣ K.index := by
      rw [hindex]
      exact pow_dvd_pow 2 h2le
    have h4G : 4 ∣ Nat.card G := by
      rcases h4 with ⟨t, ht⟩
      refine ⟨Nat.card K * t, ?_⟩
      calc
        Nat.card G = Nat.card K * K.index := hprod.symm
        _ = Nat.card K * (4 * t) := by rw [ht]
        _ = 4 * (Nat.card K * t) := by ring
    have h2dvdn : 2 ∣ n := by
      rcases h4G with ⟨t, ht⟩
      have hmul : 2 * (2 * t) = 2 * n := by
        have h4n : 4 * t = 2 * n := by rw [← hcard, ht]
        nlinarith
      have hcancel : 2 * t = n := Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
      exact ⟨t, hcancel.symm⟩
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h2dvdn)
  have hane0 : a ≠ 0 := by
    intro h0
    have h2dvdG : 2 ∣ Nat.card G := by
      rw [hcard]
      exact dvd_mul_right 2 n
    have hcardG : Nat.card G = Nat.card K := by
      rw [← hprod, hindex, h0]
      simp
    have h2dvdK' : 2 ∣ Nat.card K := by
      rw [← hcardG]
      exact h2dvdG
    exact h2ndvdK h2dvdK'
  have ha1 : a = 1 := by omega
  change (pPrimeCore 2 G).index = 2
  rw [hindex, ha1]
  norm_num

private theorem case2_index_two_no_index_four_two_class
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (h2 : ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hno4 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4) :
    ∃ S : Sylow 2 G,
      4 < Nat.card (S : Subgroup G) ∧
      ∃ Z₀ Z₁ : Subgroup G,
        Z₀ ≤ (S : Subgroup G) ∧ Z₁ ≤ (S : Subgroup G) ∧
        IsKleinFour Z₀ ∧ IsKleinFour Z₁ ∧
        ¬ (∃ g : G, conjugateSubgroup Z₀ g = Z₁) ∧
        (∀ Z : Subgroup G, Z ≤ (S : Subgroup G) → IsKleinFour Z →
          (∃ g : G, conjugateSubgroup Z g = Z₀) ∨ (∃ g : G, conjugateSubgroup Z g = Z₁)) ∧
        ((NormalizerContainsCPrime Z₀ ∧ ¬ NormalizerContainsCPrime Z₁) ∨
          (NormalizerContainsCPrime Z₁ ∧ ¬ NormalizerContainsCPrime Z₀)) := by
  classical
  let S0 : Sylow 2 G := Classical.choice Sylow.nonempty
  obtain ⟨m, hm, ⟨e⟩⟩ := hdihedral S0
  have hcard (Q : Sylow 2 G) {n : ℕ} (hn : 1 ≤ n)
      (eqQ : Q ≃* DihedralGroup (2 ^ n)) :
      Nat.card (Q : Subgroup G) = 2 * 2 ^ n := by
    have hc := Nat.card_congr eqQ.toEquiv
    rw [DihedralGroup.nat_card] at hc
    exact hc
  by_cases hm2 : 2 ≤ m
  · have hAut : IsPGroup 2 (MulAut S0) :=
      (dihedral_mulAut_is_twoGroup hm2).of_equiv (MulAut.congr e).symm
    rcases dihedral_grun_subgroup_four_cases S0 hm2 e hAut with
      hB | hE0 | hE1 | hS
    · exfalso
      have hrel : (huppertIV34GrunKernelSubgroup (Q := G) (S0 : Subgroup G)).relIndex
          (S0 : Subgroup G) = 4 := by
        change (huppertIV34GrunKernelSubgroup (Q := G) (S0 : Subgroup G)).relIndex
          (S0 : Subgroup G) = 4
        rw [hB]
        exact evenRotations_relIndex_eq_four S0 hm e
      exact hno4 (exists_normal_index_four_of_grun_relIndex_eq_four S0 hrel)
    · have hfused := fused_zero_of_grun_eq_indexTwo_zero S0 hm2 e hE0
      let Z₀ : Subgroup G := dKleinAmbient S0 (by omega : 1 ≤ m) e 0
      let Z₁ : Subgroup G := dKleinAmbient S0 (by omega : 1 ≤ m) e 1
      have hpos0 : NormalizerContainsCPrime Z₀ := by
        simpa [Z₀] using normalizerContainsCPrime_of_fused S0 hm2 e 0 hfused.1
      have hneg1 : ¬ NormalizerContainsCPrime Z₁ := by
        simpa [Z₁] using not_normalizerContainsCPrime_of_not_fused S0 hm2 e 1 hfused.2
      have hnotconj : ¬ ∃ g : G, conjugateSubgroup Z₀ g = Z₁ := by
        rintro ⟨g, hg⟩
        exact hneg1 ((normalizerContainsCPrime_conjugate Z₀ Z₁ g hg).mp hpos0)
      have hcover : ∀ Z : Subgroup G, Z ≤ (S0 : Subgroup G) → IsKleinFour Z →
          (∃ g : G, conjugateSubgroup Z g = Z₀) ∨
            (∃ g : G, conjugateSubgroup Z g = Z₁) := by
        intro Z hZle hZ
        rcases exists_conj_dKleinAmbient_zero_or_one S0 hm2 e Z hZle hZ with h0 | h1
        · rcases h0 with ⟨g, _hgS, hg⟩
          left
          exact ⟨g, by simpa [Z₀] using hg⟩
        · rcases h1 with ⟨g, _hgS, hg⟩
          right
          exact ⟨g, by simpa [Z₁] using hg⟩
      have hcardS : 4 < Nat.card (S0 : Subgroup G) := by
        have hc : Nat.card (S0 : Subgroup G) = 2 * 2 ^ m := hcard S0 hm e
        have hpow : 4 ≤ 2 ^ m :=
          Nat.pow_le_pow_right (by decide : 0 < 2) hm2
        rw [hc]
        nlinarith
      refine ⟨S0, hcardS, Z₀, Z₁, ?_, ?_, ?_, ?_, hnotconj, hcover,
        Or.inl ⟨hpos0, hneg1⟩⟩
      · simpa [Z₀] using dKleinAmbient_le_S S0 (by omega : 1 ≤ m) e 0
      · simpa [Z₁] using dKleinAmbient_le_S S0 (by omega : 1 ≤ m) e 1
      · simpa [Z₀] using dKleinAmbient_isKleinFour S0 (by omega : 1 ≤ m) e 0
      · simpa [Z₁] using dKleinAmbient_isKleinFour S0 (by omega : 1 ≤ m) e 1
    · have hfused := fused_one_of_grun_eq_indexTwo_one S0 hm2 e hE1
      let Z₀ : Subgroup G := dKleinAmbient S0 (by omega : 1 ≤ m) e 0
      let Z₁ : Subgroup G := dKleinAmbient S0 (by omega : 1 ≤ m) e 1
      have hpos1 : NormalizerContainsCPrime Z₁ := by
        simpa [Z₁] using normalizerContainsCPrime_of_fused S0 hm2 e 1 hfused.1
      have hneg0 : ¬ NormalizerContainsCPrime Z₀ := by
        simpa [Z₀] using not_normalizerContainsCPrime_of_not_fused S0 hm2 e 0 hfused.2
      have hnotconj : ¬ ∃ g : G, conjugateSubgroup Z₀ g = Z₁ := by
        rintro ⟨g, hg⟩
        exact hneg0 ((normalizerContainsCPrime_conjugate Z₀ Z₁ g hg).mpr hpos1)
      have hcover : ∀ Z : Subgroup G, Z ≤ (S0 : Subgroup G) → IsKleinFour Z →
          (∃ g : G, conjugateSubgroup Z g = Z₀) ∨
            (∃ g : G, conjugateSubgroup Z g = Z₁) := by
        intro Z hZle hZ
        rcases exists_conj_dKleinAmbient_zero_or_one S0 hm2 e Z hZle hZ with h0 | h1
        · rcases h0 with ⟨g, _hgS, hg⟩
          left
          exact ⟨g, by simpa [Z₀] using hg⟩
        · rcases h1 with ⟨g, _hgS, hg⟩
          right
          exact ⟨g, by simpa [Z₁] using hg⟩
      have hcardS : 4 < Nat.card (S0 : Subgroup G) := by
        have hc : Nat.card (S0 : Subgroup G) = 2 * 2 ^ m := hcard S0 hm e
        have hpow : 4 ≤ 2 ^ m :=
          Nat.pow_le_pow_right (by decide : 0 < 2) hm2
        rw [hc]
        nlinarith
      refine ⟨S0, hcardS, Z₀, Z₁, ?_, ?_, ?_, ?_, hnotconj, hcover,
        Or.inr ⟨hpos1, hneg0⟩⟩
      · simpa [Z₀] using dKleinAmbient_le_S S0 (by omega : 1 ≤ m) e 0
      · simpa [Z₁] using dKleinAmbient_le_S S0 (by omega : 1 ≤ m) e 1
      · simpa [Z₀] using dKleinAmbient_isKleinFour S0 (by omega : 1 ≤ m) e 0
      · simpa [Z₁] using dKleinAmbient_isKleinFour S0 (by omega : 1 ≤ m) e 1
    · exfalso
      have hrel : (huppertIV34GrunKernelSubgroup (Q := G) (S0 : Subgroup G)).relIndex
          (S0 : Subgroup G) = 1 := by
        change (huppertIV34GrunKernelSubgroup (Q := G) (S0 : Subgroup G)).relIndex
          (S0 : Subgroup G) = 1
        rw [hS]
        simp [Subgroup.relIndex]
      exact no_normal_index_two_of_grun_relIndex_eq_one S0 hrel h2
  · exfalso
    rcases h2 with ⟨N, hNnormal, hNindex⟩
    let : N.Normal := hNnormal
    let S : Subgroup G := (S0 : Subgroup G)
    have hScard : Nat.card S = 4 := by
      have hm1 : m = 1 := by omega
      dsimp [S]
      rw [hcard S0 hm e, hm1]
      norm_num
    have hGcard : Nat.card G = 4 * S.index := by
      calc
        Nat.card G = Nat.card S * S.index := (Subgroup.card_mul_index (H := S)).symm
        _ = 4 * S.index := by rw [hScard]
    have hNcard : Nat.card N = 2 * S.index := by
      have hNprod := Subgroup.card_mul_index (H := N)
      have hmul : Nat.card N * 2 = 4 * S.index := by
        calc
          Nat.card N * 2 = Nat.card N * N.index := by rw [hNindex]
          _ = Nat.card G := hNprod
          _ = 4 * S.index := hGcard
      have hmul' : 2 * Nat.card N = 2 * (2 * S.index) := by
        nlinarith
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hmul'
    have hSindexOdd : Odd S.index := by
      rw [← Nat.not_even_iff_odd]
      intro h
      exact S0.not_dvd_index (even_iff_two_dvd.mp h)
    have hcycN : ∀ P : Sylow 2 (↥N), IsCyclic ↥(P : Subgroup (↥N)) := by
      intro P
      have hPcard : Nat.card (P : Subgroup (↥N)) = 2 :=
        sylow_card_two_of_card_two_mul_odd (G := ↥N)
          (n := S.index) hNcard hSindexOdd P
      exact isCyclic_of_prime_card (p := 2) hPcard
    have hcompN : HasNormalPComplement 2 (↥N) :=
      hasNormalPComplement_of_cyclic_sylow (G := ↥N) hcycN
    have hNKp : IsPGroup 2 ((↥N) ⧸ pPrimeCore 2 (↥N)) :=
      isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) (H := ↥N) hcompN
    have hK0index : (pPrimeCore 2 (↥N)).index = 2 :=
      pPrimeCore_index_two_of_sylow_two (G := ↥N)
        (n := S.index) hNcard hSindexOdd hNKp
    let K : Subgroup G := (pPrimeCore 2 (↥N)).map N.subtype
    have : K.Normal := by
      dsimp [K]
      infer_instance
    have hKindex : K.index = 4 := by
      change ((pPrimeCore 2 (↥N)).map N.subtype).index = 4
      rw [Subgroup.index_map_subtype, hK0index, hNindex]
    exact hno4 ⟨K, inferInstance, hKindex⟩

/-! ## The pinned trichotomy statement -/

/-- Lemma 2.1 (Part I, pp. 90--91): the three-case classification of groups
with dihedral Sylow `2`-subgroups.  See the wrapper
`GorensteinWalter.GW1965.gw_lemma_2_1` for the statement provenance.

All three cases are proved in this module: the index-four branch via
Burnside's normal-complement transfer, the index-two/no-index-four branch
via the Grün-kernel reflection-extension classification, and the no-index-two
branch via the Grün kernel (Sylow order `> 4`) or the Burnside normalizer
argument (Klein-four Sylow, `|S| = 4`). -/
public theorem gw_lemma_2_1
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G) :
    ((¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧
        (∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y) ∧
        (∀ S : Sylow 2 G, ∀ Z : Subgroup G, Z ≤ (S : Subgroup G) →
          IsKleinFour Z → NormalizerContainsCPrime Z)) ∨
      ((∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧
        (¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4) ∧
        (∃ S : Sylow 2 G,
          4 < Nat.card (S : Subgroup G) ∧
          ∃ Z₀ Z₁ : Subgroup G,
            Z₀ ≤ (S : Subgroup G) ∧ Z₁ ≤ (S : Subgroup G) ∧
            IsKleinFour Z₀ ∧ IsKleinFour Z₁ ∧
            ¬ (∃ g : G, conjugateSubgroup Z₀ g = Z₁) ∧
            (∀ Z : Subgroup G, Z ≤ (S : Subgroup G) → IsKleinFour Z →
              (∃ g : G, conjugateSubgroup Z g = Z₀) ∨ (∃ g : G, conjugateSubgroup Z g = Z₁)) ∧
            ((NormalizerContainsCPrime Z₀ ∧ ¬ NormalizerContainsCPrime Z₁) ∨
              (NormalizerContainsCPrime Z₁ ∧ ¬ NormalizerContainsCPrime Z₀)))) ∨
      ((∃ N : Subgroup G, N.Normal ∧ N.index = 4) ∧
        Glauberman.NormalPComplement 2 G) := by
  classical
  by_cases h4 : ∃ N : Subgroup G, N.Normal ∧ N.index = 4
  · exact Or.inr (Or.inr ⟨h4, normal_index_four_dihedral_sylow_normalPComplement hdihedral h4⟩)
  · by_cases h2 : ∃ N : Subgroup G, N.Normal ∧ N.index = 2
    · exact Or.inr (Or.inl ⟨h2, h4, case2_index_two_no_index_four_two_class hdihedral h2 h4⟩)
    · exact Or.inl ⟨h2, case1_no_index_two_fusion_and_normalizer hdihedral h2⟩

end CFSG.GorensteinWalter
