module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S72Core
public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Five
import CFSG.RankThree.GF2n.Tim81.Sec7.S71TIProof
import CFSG.RankThree.GF2n.Tim81.Sec7.S77Basic
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.QuotMod
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B C D : Subgroup G} {h : G} {n f : ℕ}

theorem L2Datum.r0Hyp (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    QuotMod.Hyp (r0Of M V (A ⊔ B)) (p0Of M V (A ⊔ B)) V where
  le := L2Datum.V_le_p0 hS.toSec6Hyp hD
  comm := by
    intro x hx y hy
    have h := Subgroup.commutator_mem_commutator
      (H₁ := p0Of M V (A ⊔ B)) (H₂ := p0Of M V (A ⊔ B)) hx hy
    have hle : ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ ≤ ⁅Pc M V, Pc M V⁆ :=
      Subgroup.commutator_mono inf_le_left inf_le_left
    rw [hS.sec5.commutator_Pc_eq_V hS.ne] at hle
    simpa only [commutatorElement_def] using hle h
  conj := by
    intro g hg y hy
    have hR0R : r0Of M V (A ⊔ B) ≤ rOf M h :=
      (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans (L2Datum.inf_cenOf_le_rOf hD)
    have hN : rOf M h ≤ Subgroup.normalizer (p0Of M V (A ⊔ B) : Set G) :=
      L2Datum.rOf_le_normalizer_p0 hS.toSec6Hyp hD (L2Datum.p0_zpowers_eq hS hD)
    exact (Subgroup.mem_normalizer_iff.mp (hN (hR0R hg)) y).mp hy
  conj₀ := by
    intro g hg y hy
    have hR0M : r0Of M V (A ⊔ B) ≤ M :=
      (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans inf_le_left
    exact (Subgroup.mem_normalizer_iff.mp
      (hS.sec5.toRootHyp.toHyp.le_normalizer (hR0M hg)) y).mp hy

theorem L2Datum.r0Normal (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    (V.subgroupOf (p0Of M V (A ⊔ B))).Normal :=
  (L2Datum.r0Hyp hS hD).normal

@[instance_reducible] noncomputable def L2Datum.r0Module (hS : Sec7Hyp M V n f)
    (hD : L2Datum M V A B h) [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal] :
    Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD)) :=
  SecMod.module (L2Datum.r0Hyp hS hD) fun x hx =>
    Hyp.mul_self_mem_of_mem_Pc hS.sec5.toRootHyp.toHyp hx.1

noncomputable def L2Datum.r0Rep (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))] :
    Representation (ZMod 2) ↥(imgQ M (r0Of M V (A ⊔ B))) (SecMod (L2Datum.r0Hyp hS hD)) :=
  secDescend (L2Datum.r0Hyp hS hD) (r0BarMap hS.toSec6Hyp A B)
    (r0BarMap_surjective hS.toSec6Hyp A B) fun z hz => by
      refine secConj_eq_one (L2Datum.r0Hyp hS hD) fun x hx => ?_
      have hzM : (z : G) ∈ M := r0Of_le_M hS.toSec6Hyp (A ⊔ B) z.2
      have hzP : (z : G) ∈ Pc M V := by
        have h1 : QuotientGroup.mk' (pCore 2 ↥M) ⟨(z : G), hzM⟩ = 1 := by
          rw [← r0BarMap_apply hS.toSec6Hyp A B z]
          exact congrArg Subtype.val hz
        exact (hS.toSec6Hyp.mk_eq_one_iff ⟨(z : G), hzM⟩).mp h1
      have hzC : (z : G) ∈ cenOf (A ⊔ B) :=
        (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD z.2).2
      have hzP0 : (z : G) ∈ p0Of M V (A ⊔ B) := ⟨hzP, hzC⟩
      have hcomm : ⁅(z : G), x⁆ ∈ V := by
        have h := Subgroup.commutator_mem_commutator
          (H₁ := p0Of M V (A ⊔ B)) (H₂ := p0Of M V (A ⊔ B)) hzP0 hx
        have hle : ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ ≤ V := by
          refine (Subgroup.commutator_mono inf_le_left inf_le_left).trans ?_
          rw [hS.sec5.commutator_Pc_eq_V hS.ne]
        exact hle h
      simpa only [commutatorElement_def] using hcomm

private theorem L2Datum.r0Rep_apply (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))]
    (z : ↥(r0Of M V (A ⊔ B))) (w : SecMod (L2Datum.r0Hyp hS hD)) :
    L2Datum.r0Rep hS hD (r0BarMap hS.toSec6Hyp A B z) w =
      SecMod.secConj (L2Datum.r0Hyp hS hD) z w := by
  rw [L2Datum.r0Rep, secDescend_apply]

theorem L2Datum.span_r0Rep (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))]
    (hC : C ∈ sigmaSet M V) (hCX : C ≤ cenOf (A ⊔ B)) :
    Submodule.span (ZMod 2) {u | ∃ a ∈ (imgQ M C).subgroupOf (imgQ M (r0Of M V (A ⊔ B))),
        ∃ w, u = L2Datum.r0Rep hS hD a w - w} = subSec (L2Datum.r0Hyp hS hD) ⁅Pc M V, C⁆ := by
  have hCR0 : C ≤ r0Of M V (A ⊔ B) := le_iSup₂_of_le C ⟨hC, hCX⟩ le_rfl
  have hset : {u | ∃ a ∈ (imgQ M C).subgroupOf (imgQ M (r0Of M V (A ⊔ B))),
      ∃ w, u = L2Datum.r0Rep hS hD a w - w} =
      {u | ∃ z : ↥(r0Of M V (A ⊔ B)), (z : G) ∈ C ∧
        ∃ w, u = SecMod.secConj (L2Datum.r0Hyp hS hD) z w - w} := by
    ext u
    constructor
    · rintro ⟨a, ha, w, rfl⟩
      have haC : (a : MBar M) ∈ imgQ M C := Subgroup.mem_subgroupOf.mp ha
      obtain ⟨c, hcC, hca⟩ := mem_imgQ_iff.mp haC
      refine ⟨⟨(c : G), hCR0 hcC⟩, hcC, w, ?_⟩
      have haz : a = r0BarMap hS.toSec6Hyp A B ⟨(c : G), hCR0 hcC⟩ := by
        refine Subtype.ext ?_
        rw [r0BarMap_apply]
        exact hca.symm
      rw [haz, L2Datum.r0Rep_apply hS hD]
    · rintro ⟨z, hzC, w, rfl⟩
      refine ⟨r0BarMap hS.toSec6Hyp A B z, ?_, w, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        change ((r0BarMap hS.toSec6Hyp A B z :
          ↥(imgQ M (r0Of M V (A ⊔ B)))) : MBar M) ∈ imgQ M C
        rw [r0BarMap_apply]
        exact mk_mem_imgQ hzC
      · rw [L2Datum.r0Rep_apply hS hD]
  have hVE : V ≤ ⁅p0Of M V (A ⊔ B), C⁆ := by
    rw [← L2Datum.commutator_Pc_eq_p0 hS hD (L2Datum.p0_zpowers_eq hS hD) hC hCX]
    exact hS.sec5.V_le_commutator hC
  rw [hset, span_secConj_eq (L2Datum.r0Hyp hS hD) hCR0,
    show ⁅p0Of M V (A ⊔ B), C⁆ ⊔ V = ⁅p0Of M V (A ⊔ B), C⁆ from sup_eq_left.mpr hVE,
    L2Datum.commutator_Pc_eq_p0 hS hD (L2Datum.p0_zpowers_eq hS hD) hC hCX]

theorem L2Datum.card_r0Sec (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    Nat.card (SecMod (L2Datum.r0Hyp hS hD)) = (2 ^ f) ^ (2 * (n - 2)) := by
  letI := L2Datum.r0Normal hS hD
  letI := L2Datum.r0Module hS hD
  have h := natCard_secMod (L2Datum.r0Hyp hS hD)
  rw [L2Datum.card_p0 hS hD, hS.card_V] at h
  have hn4 : 4 ≤ n := hS.four_le
  have hexp : 2 * n - 3 = (2 * (n - 2)) + 1 := by omega
  rw [hexp, pow_succ] at h
  exact Nat.mul_right_cancel (by positivity) h

private theorem L2Datum.exists_r0Rep_ne (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))] :
    ∃ x ∈ (⊤ : Subgroup ↥(imgQ M (r0Of M V (A ⊔ B)))),
      ∃ w : SecMod (L2Datum.r0Hyp hS hD), L2Datum.r0Rep hS hD x w ≠ w := by
  obtain ⟨C, hC, hCX⟩ := L2Datum.exists_sigma_cenOf hS hLP hD
  have hCR0 : C ≤ r0Of M V (A ⊔ B) := le_iSup₂_of_le C ⟨hC, hCX⟩ le_rfl
  have hex : ∃ p ∈ p0Of M V (A ⊔ B), ∃ c ∈ C, ⁅p, c⁆ ∉ V :=
    L2Datum.exists_commutator_not_mem_V hS hD (L2Datum.p0_zpowers_eq hS hD) hC hCX
  obtain ⟨p, hpP0, c, hcC, hpc⟩ := hex
  let z : ↥(r0Of M V (A ⊔ B)) := ⟨c, hCR0 hcC⟩
  let w : SecMod (L2Datum.r0Hyp hS hD) :=
    SecMod.mk (L2Datum.r0Hyp hS hD) ⟨p, hpP0⟩
  refine ⟨r0BarMap hS.toSec6Hyp A B z, Subgroup.mem_top _,
    w, fun heq => ?_⟩
  have hconj : SecMod.secConj (L2Datum.r0Hyp hS hD) z w = w := by
    rw [← hD.r0Rep_apply hS z w]
    exact heq
  rw [secConj_mk] at hconj
  let a : ↥(p0Of M V (A ⊔ B)) :=
    ⟨(z : G) * p * (z : G)⁻¹,
      (L2Datum.r0Hyp hS hD).conj z z.2 p hpP0⟩
  let b : ↥(p0Of M V (A ⊔ B)) := ⟨p, hpP0⟩
  have hqeq : SecMod.mk (L2Datum.r0Hyp hS hD) a = SecMod.mk (L2Datum.r0Hyp hS hD) b := by
    simpa only [w, a, b] using hconj
  have hzero : SecMod.mk (L2Datum.r0Hyp hS hD) (a⁻¹ * b) = 0 := by
    rw [SecMod.mk_mul, SecMod.mk_inv, hqeq]
    simp
  have hmem : ((a⁻¹ * b : ↥(p0Of M V (A ⊔ B))) : G) ∈ V :=
    (SecMod.mk_eq_zero_iff (L2Datum.r0Hyp hS hD) (a⁻¹ * b)).mp hzero
  have hpcV : ⁅p, c⁆ ∈ V := by
    have hpM : p ∈ M := hS.sec5.toRootHyp.toHyp.Pc_le_M hpP0.1
    have hnorm : p ∈ Subgroup.normalizer (V : Set G) :=
      hS.sec5.toRootHyp.toHyp.le_normalizer hpM
    have h1 : p * (((z : G) * p * (z : G)⁻¹)⁻¹ * p) * p⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hnorm _).mp hmem
    have h2 : p * (((z : G) * p * (z : G)⁻¹)⁻¹ * p) * p⁻¹ = ⁅p, c⁆ := by
      rw [commutatorElement_def]
      simp only [z]
      group
    rwa [h2] at h1
  exact hpc hpcV

private theorem L2Datum.r0Rep_TI (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))] :
    ∀ U ∈ (fun E : Subgroup (MBar M) =>
        E.subgroupOf (imgQ M (r0Of M V (A ⊔ B)))) ''
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}),
    ∀ W ∈ (fun E : Subgroup (MBar M) =>
        E.subgroupOf (imgQ M (r0Of M V (A ⊔ B)))) ''
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}),
      Submodule.span (ZMod 2) {u | ∃ a ∈ U, ∃ w : SecMod (L2Datum.r0Hyp hS hD),
          u = L2Datum.r0Rep hS hD a w - w} =
        Submodule.span (ZMod 2) {u | ∃ b ∈ W, ∃ w : SecMod (L2Datum.r0Hyp hS hD),
          u = L2Datum.r0Rep hS hD b w - w} ∨
      Submodule.span (ZMod 2) {u | ∃ a ∈ U, ∃ w : SecMod (L2Datum.r0Hyp hS hD),
          u = L2Datum.r0Rep hS hD a w - w} ⊓
        Submodule.span (ZMod 2) {u | ∃ b ∈ W, ∃ w : SecMod (L2Datum.r0Hyp hS hD),
          u = L2Datum.r0Rep hS hD b w - w} = ⊥ := by
  rintro U ⟨E, hE, rfl⟩ W ⟨F, hF, rfl⟩
  obtain ⟨C, hC, rfl⟩ := hE
  obtain ⟨D, hD', rfl⟩ := hF
  rw [L2Datum.span_r0Rep hS hD hC.1 hC.2, L2Datum.span_r0Rep hS hD hD'.1 hD'.2]
  rcases Sec6Hyp.stmt71TI hS.toSec6Hyp C hC.1 D hD'.1 with hEq | hInf
  · exact Or.inl (congrArg (subSec (L2Datum.r0Hyp hS hD)) hEq)
  · refine Or.inr ?_
    rw [← subSec_inf (L2Datum.r0Hyp hS hD) (hS.sec5.V_le_commutator hD'.1), hInf,
      subSec_eq_bot_of_le (L2Datum.r0Hyp hS hD) le_rfl]

private theorem L2Datum.r0Rep_subSec_invariant (hS : Sec7Hyp M V n f)
    (hD : L2Datum M V A B h) [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))] {N : Subgroup G}
    (hNR0 : r0Of M V (A ⊔ B) ≤ Subgroup.normalizer (N : Set G)) :
    ∀ x ∈ (⊤ : Subgroup ↥(imgQ M (r0Of M V (A ⊔ B)))),
      (subSec (L2Datum.r0Hyp hS hD) N).map (L2Datum.r0Rep hS hD x) ≤
        subSec (L2Datum.r0Hyp hS hD) N := by
  intro x _
  obtain ⟨z, rfl⟩ := r0BarMap_surjective hS.toSec6Hyp A B x
  have hrepr : L2Datum.r0Rep hS hD (r0BarMap hS.toSec6Hyp A B z) =
      SecMod.secConj (L2Datum.r0Hyp hS hD) z :=
    LinearMap.ext fun w => hD.r0Rep_apply hS z w
  rw [hrepr]
  exact map_secConj_subSec_le (L2Datum.r0Hyp hS hD) z (hNR0 z.2)

private theorem L2Datum.eq_V_or_p0_of_subSec (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    [hN : (V.subgroupOf (p0Of M V (A ⊔ B))).Normal]
    [hM : Module (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD))] {N : Subgroup G}
    (hVN : V ≤ N) (hNP0 : N ≤ p0Of M V (A ⊔ B))
    (h : subSec (L2Datum.r0Hyp hS hD) N = ⊥ ∨
      subSec (L2Datum.r0Hyp hS hD) N = ⊤) :
    N = V ∨ N = p0Of M V (A ⊔ B) := by
  rcases h with hbot | htop
  · left
    have hsub : subSec (L2Datum.r0Hyp hS hD) N =
        subSec (L2Datum.r0Hyp hS hD) V := by
      rw [hbot]
      exact (subSec_eq_bot_of_le (L2Datum.r0Hyp hS hD) le_rfl).symm
    exact (subSec_inj (L2Datum.r0Hyp hS hD) hNP0 hVN
      (L2Datum.V_le_p0 hS.toSec6Hyp hD) le_rfl).mp hsub
  · right
    have hsub : subSec (L2Datum.r0Hyp hS hD) N =
        subSec (L2Datum.r0Hyp hS hD) (p0Of M V (A ⊔ B)) := by
      rw [htop]
      exact (subSec_self (L2Datum.r0Hyp hS hD)).symm
    exact (subSec_inj (L2Datum.r0Hyp hS hD) hNP0 hVN le_rfl
      (L2Datum.V_le_p0 hS.toSec6Hyp hD)).mp hsub

theorem L2Datum.irred_r0_of_five_le (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hT : UnitaryTIModule) (hSU3 : SU3ModuleBound) (hD : L2Datum M V A B h) (h5 : 5 ≤ n) :
    ∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) →
      r0Of M V (A ⊔ B) ≤ Subgroup.normalizer (N : Set G) → N = V ∨ N = p0Of M V (A ⊔ B) := by
  intro N hVN hNP0 hNR0
  let R0 := r0Of M V (A ⊔ B)
  let P0 := p0Of M V (A ⊔ B)
  let Δ : Set (Subgroup (MBar M)) :=
    imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}
  let K := ↥(imgQ M R0)
  letI := L2Datum.r0Normal hS hD
  letI := L2Datum.r0Module hS hD
  have hX : IsSUImage (⊤ : Subgroup K)
      ((fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M R0)) '' Δ) f (n - 2)
      hS.one_le (Nat.le_sub_of_add_le (Nat.le_trans (Nat.le_succ 4) h5)) :=
    (hD.isSUImage_r0 hS hLP hS.one_le h5).toTop
  let U : Submodule (ZMod 2) (SecMod (L2Datum.r0Hyp hS hD)) :=
    subSec (L2Datum.r0Hyp hS hD) N
  have hU : ∀ x ∈ (⊤ : Subgroup K), U.map (L2Datum.r0Rep hS hD x) ≤ U :=
    L2Datum.r0Rep_subSec_invariant hS hD hNR0
  have hnt := L2Datum.exists_r0Rep_ne hS hLP hD
  have hTI := L2Datum.r0Rep_TI hS hD
  have hdich : U = ⊥ ∨ U = ⊤ := by
    rcases Nat.lt_or_ge n 6 with hlt | h6
    · have hn5 : n = 5 := by omega
      have hcard : Nat.card (SecMod (L2Datum.r0Hyp hS hD)) = (2 ^ f) ^ 6 := by
        rw [L2Datum.card_r0Sec hS hD, hn5]
      have hX3 : IsSUImage (⊤ : Subgroup K)
          ((fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M R0)) '' Δ) f 3
          hS.one_le (Nat.le_succ 2) := hX.congr_rank (by omega) (Nat.le_succ 2)
      have hS9 : ∀ (hf : 1 ≤ f) (h5' : 5 ≤ n),
          IsSUImage (imgQ M R0) (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
            f (n - 2) hf (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5')) :=
        fun hf h5' => hD.isSUImage_r0 hS hLP hf h5'
      have hperf : commutator ↥(imgQ M R0) = ⊤ :=
        (L2Datum.isQuasisimple_imgQ_r0 hS hS9 h5).1.commutator_eq_top
      obtain ⟨x, -, w, hw⟩ := hnt
      by_cases hbot : U = ⊥
      · exact Or.inl hbot
      · refine Or.inr (by_contra fun htop => ?_)
        exact hSU3.false_of_invariant_submodule
          (W := SecMod (L2Datum.r0Hyp hS hD))
          ((fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M R0)) '' Δ) f hS.one_le
          hS.two_le hX3 (L2Datum.r0Rep hS hD) ⟨x, w, hw⟩ hperf
          (fun g => hU g (Subgroup.mem_top g)) hbot htop hcard
    · have hn4 : 4 ≤ n - 2 := by omega
      exact hT K ⊤ ((fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M R0)) '' Δ)
        f (n - 2) hS.one_le hn4 hS.two_le hX (SecMod (L2Datum.r0Hyp hS hD))
        (L2Datum.r0Rep hS hD) hnt hTI (L2Datum.card_r0Sec hS hD) U hU
  exact L2Datum.eq_V_or_p0_of_subSec hS hD hVN hNP0 hdich

theorem L2Datum.p0_le_r0 (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hT : UnitaryTIModule) (hSU3 : SU3ModuleBound) (hD : L2Datum M V A B h) :
    p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B) := by
  rcases Nat.lt_or_ge n 5 with hlt | h5
  · have h4 : n = 4 := by
      have := hS.four_le
      omega
    exact L2Datum.p0_le_r0_four hS hLP hD h4
  · let R0 := r0Of M V (A ⊔ B)
    let P0 := p0Of M V (A ⊔ B)
    let N := R0 ⊓ P0
    have hVN : V ≤ N := le_inf (L2Datum.V_le_r0 hS hLP hD) (L2Datum.V_le_p0 hS.toSec6Hyp hD)
    have hNP0 : N ≤ P0 := inf_le_right
    have hNR0 : R0 ≤ Subgroup.normalizer (N : Set G) := by
      intro r hr
      refine mem_normalizer_inf (Subgroup.le_normalizer hr) ?_
      have hR0R : R0 ≤ rOf M h :=
        (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans (L2Datum.inf_cenOf_le_rOf hD)
      exact (L2Datum.rOf_le_normalizer_p0 hS.toSec6Hyp hD
        (L2Datum.p0_zpowers_eq hS hD)) (hR0R hr)
    have hne : N ≠ V := by
      intro hNV
      obtain ⟨C, hC, hCX⟩ := L2Datum.exists_sigma_cenOf hS hLP hD
      have hEC : ⁅Pc M V, C⁆ ≤ N :=
        le_inf (L2Datum.commutator_Pc_le_r0 hS hD hC hCX)
          (L2Datum.commutator_Pc_le_p0 hS.toSec6Hyp hD hC hCX)
      rw [hNV] at hEC
      have hcard := hS.sec5.card_commutator_Pc hC
      have hcardle : Nat.card ↥⁅Pc M V, C⁆ ≤ Nat.card V := Subgroup.card_le_of_le hEC
      rw [hcard] at hcardle
      have hq : 2 ≤ Nat.card V := by
        have := hS.sec5.toRootHyp.four_le_card
        omega
      have h31 : 3 ≤ 1 :=
        (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card V)).mp (by simpa using hcardle)
      omega
    rcases L2Datum.irred_r0_of_five_le hS hLP hT hSU3 hD h5 N hVN hNP0 hNR0 with hNV | hNP
    · exact absurd hNV hne
    · rw [← hNP]
      exact inf_le_left

theorem L2Datum.r0_inf_cenOf_p0 (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) :
    r0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) = V := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨hyR0, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyM : y ∈ M := (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD hyR0).1
    have hyX : y ∈ cenOf (A ⊔ B) := (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD hyR0).2
    have hyE : y ∈ cenOf ⁅Pc M V, A ⊔ B⁆ :=
      L2Datum.r0_le_cenOf_commutator hS.toSec6Hyp hD hyR0
    have hyV : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V := by
      intro p hp
      have h1 : y * p = p * y := (Subgroup.mem_centralizer_iff.mp hyC p hp).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr h1]
      exact V.one_mem
    have hyPc : y ∈ Pc M V :=
      L2Datum.mem_Pc_of_trivial_p0 hS hD (L2Datum.p0_zpowers_eq hS hD) hyM hyE hyV
    have hmem : y ∈ p0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) :=
      ⟨⟨hyPc, hyX⟩, hyC⟩
    rwa [L2Datum.p0_inf_cenOf_p0 hS hD] at hmem
  · intro v hv
    refine Subgroup.mem_inf.mpr ⟨L2Datum.V_le_r0 hS hLP hD hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp hp.1.2 v hv).symm

theorem Sec7Hyp.stmt72 (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair) (hT : UnitaryTIModule)
    (hSU3 : SU3ModuleBound) : Sec7.Stmt72 M V n f := by
  intro A B h hD
  exact ⟨L2Datum.p0_zpowers_eq hS hD, L2Datum.card_p0 hS hD,
    L2Datum.commutator_p0_eq hS hLP hD, L2Datum.p0_inf_cenOf_p0 hS hD,
    fun x hx => Hyp.mul_self_mem_of_mem_Pc hS.sec5.toRootHyp.toHyp hx.1,
    L2Datum.sigma_cenOf_zpowers_eq hS hLP hD,
    L2Datum.p0_le_r0 hS hLP hT hSU3 hD,
    L2Datum.r0_inf_cenOf_p0 hS hLP hD,
    fun hf h5 => L2Datum.isSUImage_r0 hS hLP hD hf h5,
    L2Datum.r0_eq_four hS hLP hD⟩

end CFSG.RankThree.GF2n.Tim81
