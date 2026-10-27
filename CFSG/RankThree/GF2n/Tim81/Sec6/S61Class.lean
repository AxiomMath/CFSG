module

public import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
public import CFSG.RankThree.GF2n.Tim81.Sec6.S61
public import CFSG.RankThree.GF2n.Tim81.Sec6.S63
public import CFSG.RankThree.GF2n.Tim81.Sec6.S61Tools
import CFSG.GroupTheory.OddOrderPGroup
public import CFSG.RankThree.GF2n.Tim81.Sec6.Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

@[expose] def orbitM0 (M V U : Subgroup G) : Set (Subgroup G) :=
  {C | ∃ x ∈ m0Of M V, C = conjSubgroup x U}

@[expose] def restM0 (M V U : Subgroup G) : Set (Subgroup G) :=
  {C | C ∈ sigmaSet M V ∧ C ∉ orbitM0 M V U}

@[expose] def fM0 (M V U : Subgroup G) : Subgroup G := ⨆ C ∈ restM0 M V U, C

theorem Sec5Hyp.orbitM0_subset (hS : Sec5Hyp M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    orbitM0 M V U ⊆ sigmaSet M V := by
  rintro C ⟨x, hx, rfl⟩
  exact hS.conj_mem_sigmaSet (hS.m0Of_le_M hx) hU

theorem Sec6Hyp.commutator_orbitM0_restM0 (hS : Sec6Hyp M V) {U D C : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hD : D ∈ orbitM0 M V U) (hC : C ∈ restM0 M V U) :
    ⁅D, C⁆ = ⊥ := by
  obtain ⟨x₀, hx₀, rfl⟩ := hD
  have hDσ : conjSubgroup x₀ U ∈ sigmaSet M V := hS.sec5.orbitM0_subset hU ⟨x₀, hx₀, rfl⟩
  rcases hS.res.s513 M V hS.sec5 (conjSubgroup x₀ U) hDσ C hC.1 with ⟨hcomm, -⟩ | ⟨hl2, -⟩
  · exact hcomm
  · obtain ⟨x, hx, hxC⟩ := hl2.exists_conj
    exfalso
    apply hC.2
    refine ⟨x * x₀, ?_, ?_⟩
    · exact (m0Of M V).mul_mem
        (sup_le (le_m0Of_of_mem_sigmaSet hDσ) (le_m0Of_of_mem_sigmaSet hC.1) hx) hx₀
    · rw [conjSubgroup_mul, hxC]

theorem Sec6Hyp.exists_partner_restM0 (hS : Sec6Hyp M V) {U C : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hC : C ∈ restM0 M V U) :
    ∃ C' ∈ restM0 M V U, IsL2Gen C C' := by
  obtain ⟨C', hC'σ, hl2⟩ := hS.exists_isL2Gen hC.1
  refine ⟨C', ⟨hC'σ, ?_⟩, hl2⟩
  intro hC'orbit
  apply hl2.commutator_ne_bot
  rw [Subgroup.commutator_comm]
  exact hS.commutator_orbitM0_restM0 hU hC'orbit hC

theorem Sec5Hyp.conj_mem_restM0 (hS : Sec5Hyp M V) {U C : Subgroup G}
    {l : G} (hlM : l ∈ M)
    (hlU : l ∈ Subgroup.normalizer (U : Set G)) (hC : C ∈ restM0 M V U) :
    conjSubgroup l C ∈ restM0 M V U := by
  refine ⟨hS.conj_mem_sigmaSet hlM hC.1, ?_⟩
  rintro ⟨x, hx, hxeq⟩
  apply hC.2
  have hUfix : conjSubgroup l U = U := conjSubgroup_eq_self_iff.mpr hlU
  have hxl : l⁻¹ * x * l ∈ m0Of M V := by
    have hinv : l⁻¹ ∈ Subgroup.normalizer (m0Of M V : Set G) :=
      Subgroup.inv_mem _ (hS.toRootHyp.toHyp.le_normalizer_m0Of hlM)
    simpa using (Subgroup.mem_normalizer_iff.mp hinv x).mp hx
  refine ⟨l⁻¹ * x * l, hxl, ?_⟩
  calc C = conjSubgroup l⁻¹ (conjSubgroup l C) := by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    _ = conjSubgroup l⁻¹ (conjSubgroup x U) := by rw [hxeq]
    _ = conjSubgroup (l⁻¹ * x) U := (conjSubgroup_mul l⁻¹ x U).symm
    _ = conjSubgroup (l⁻¹ * x * l) U := by
        rw [conjSubgroup_mul (l⁻¹ * x) l U, hUfix]

theorem Sec5Hyp.le_normalizer_fM0 (hS : Sec5Hyp M V) {U : Subgroup G} :
    M ⊓ Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (fM0 M V U : Set G) := by
  have hconj : ∀ m : G, m ∈ M ⊓ Subgroup.normalizer (U : Set G) →
      conjSubgroup m (fM0 M V U) ≤ fM0 M V U := by
    intro m hm
    obtain ⟨hmM, hmU⟩ := Subgroup.mem_inf.mp hm
    have hmap : conjSubgroup m (fM0 M V U) =
        ⨆ C ∈ restM0 M V U, conjSubgroup m C := by
      unfold CGT.Timmesfeld75.conjSubgroup fM0
      simp only [Subgroup.map_iSup]
    rw [hmap]
    refine iSup₂_le fun C hC => ?_
    exact le_iSup₂_of_le (conjSubgroup m C) (hS.conj_mem_restM0 hmM hmU hC) le_rfl
  intro l hl
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine le_antisymm (hconj l hl) ?_
  have hlinv : l⁻¹ ∈ M ⊓ Subgroup.normalizer (U : Set G) :=
    Subgroup.mem_inf.mpr ⟨M.inv_mem (Subgroup.mem_inf.mp hl).1,
      Subgroup.inv_mem _ (Subgroup.mem_inf.mp hl).2⟩
  calc fM0 M V U = conjSubgroup l (conjSubgroup l⁻¹ (fM0 M V U)) := by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    _ ≤ conjSubgroup l (fM0 M V U) := conjSubgroup_mono (hconj l⁻¹ hlinv)

theorem Sec6Hyp.m0Of_le_normalizer_fM0 (hS : Sec6Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    m0Of M V ≤ Subgroup.normalizer (fM0 M V U : Set G) := by
  refine iSup₂_le fun C hC => ?_
  by_cases hCorbit : C ∈ orbitM0 M V U
  · have hCF : C ≤ Subgroup.centralizer (fM0 M V U : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine iSup₂_le fun D hD => ?_
      rw [Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hS.commutator_orbitM0_restM0 (U := U) (D := C) (C := D) hU hCorbit hD)
    exact hCF.trans (Subgroup.centralizer_le_normalizer _)
  · have hCle : C ≤ fM0 M V U := le_iSup₂_of_le C ⟨hC, hCorbit⟩ le_rfl
    exact hCle.trans (Subgroup.le_normalizer (H := fM0 M V U))

theorem Sec6Hyp.fM0_le_M_m0Of_centralizer (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    fM0 M V (conjSubgroup g V) ≤ M ∧
      fM0 M V (conjSubgroup g V) ≤ m0Of M V ∧
      fM0 M V (conjSubgroup g V) ≤
        Subgroup.centralizer (conjSubgroup g V : Set G) := by
  have horbit : conjSubgroup g V ∈ orbitM0 M V (conjSubgroup g V) :=
    ⟨1, one_mem _, (conjSubgroup_one _).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · exact iSup₂_le fun C hC => (hS.sec5.le_M_of_mem_sigmaSet hC.1).1
  · exact iSup₂_le fun C hC => le_m0Of_of_mem_sigmaSet hC.1
  · refine iSup₂_le fun C hC => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hS.commutator_orbitM0_restM0 hg horbit hC)

theorem Sec6Hyp.fM0_le_normalizer_lOf_hOf (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    fM0 M V (conjSubgroup g V) ≤ Subgroup.normalizer (lOf M V g : Set G) ∧
      fM0 M V (conjSubgroup g V) ≤ Subgroup.normalizer (hOf M V g : Set G) := by
  have hFM : fM0 M V (conjSubgroup g V) ≤ M :=
    (hS.fM0_le_M_m0Of_centralizer hg).1
  have hFC : fM0 M V (conjSubgroup g V) ≤
      Subgroup.centralizer (conjSubgroup g V : Set G) :=
    (hS.fM0_le_M_m0Of_centralizer hg).2.2
  constructor
  · intro f hf
    exact mem_normalizer_inf (E := conjSubgroup g (Pc M V)) (F := M)
      (hS.sec5.mem_normalizer_conj_Pc g (hFC hf)) (Subgroup.le_normalizer (hFM hf))
  · intro f hf
    refine Subgroup.inf_normalizer_le_normalizer_sup (Pc M V)
      (conjSubgroup g (Pc M V)) ⟨?_, hS.sec5.mem_normalizer_conj_Pc g (hFC hf)⟩
    exact hS.sec5.toRootHyp.toHyp.le_normalizer_Pc (hFM hf)

theorem Sec6Hyp.fM0_le_centralizer_xOf (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    fM0 M V (conjSubgroup g V) ≤
      Subgroup.centralizer (Tim79a.xOf V (hOf M V g) : Set G) := by
  have horbit : conjSubgroup g V ∈ orbitM0 M V (conjSubgroup g V) :=
    ⟨1, one_mem _, (conjSubgroup_one _).symm⟩
  have hcent := (hS.sec5.exists_conj_data hg).choose_spec.2.2.2.2
  refine iSup₂_le fun C hC u hu => ?_
  have hCU : C ≤ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hS.commutator_orbitM0_restM0 hg horbit hC)
  have hPC : ⁅Pc M V, C⁆ ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) := by
    rcases hS.res.s513 M V hS.sec5 C hC.1 (conjSubgroup g V) hg with ⟨-, h⟩ | ⟨hl2, -⟩
    · exact h
    · exact absurd (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCU) hl2.commutator_ne_bot
  exact (hS.twoPoint_of_commute (hS.sec5.shape hg) hC.1 hCU hPC hcent rfl u hu).2

theorem Sec6Hyp.fM0_inf_lOf_le_Pc (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    fM0 M V (conjSubgroup g V) ⊓ lOf M V g ≤ Pc M V := by
  have hR := hS.sec5.toRootHyp
  have hSg := hS.sec5.shape hg
  have hFM0 : fM0 M V (conjSubgroup g V) ≤ m0Of M V :=
    (hS.fM0_le_M_m0Of_centralizer hg).2.1
  have hFN : fM0 M V (conjSubgroup g V) ≤
      Subgroup.normalizer (lOf M V g : Set G) :=
    (hS.fM0_le_normalizer_lOf_hOf hg).1
  have h1 : fM0 M V (conjSubgroup g V) ⊓ lOf M V g ≤
      inSubgroup (pCore 2) (fM0 M V (conjSubgroup g V)) := by
    refine Tim78.le_inSubgroup_pCore inf_le_left ?_ ?_
    · intro f hf
      exact mem_normalizer_inf (Subgroup.le_normalizer hf) (hFN hf)
    · exact (isPGroup_conj_Pc M V g).to_le (inf_le_right.trans inf_le_left)
  have h2 : inSubgroup (pCore 2) (fM0 M V (conjSubgroup g V)) ≤
      inSubgroup (pCore 2) (m0Of M V) := by
    refine Tim78.le_inSubgroup_pCore ((inSubgroup_pCore_two _).2.1.trans hFM0) ?_
      (inSubgroup_pCore_two _).1
    intro m hm
    exact mem_normalizer_map_subtype_of_characteristic
      ((hS.m0Of_le_normalizer_fM0 hg) hm) (pCore 2 ↥(fM0 M V (conjSubgroup g V)))
  have h3 : inSubgroup (pCore 2) (m0Of M V) ≤ inSubgroup (pCore 2) M := by
    refine Tim78.le_inSubgroup_pCore ((inSubgroup_pCore_two _).2.1.trans hS.sec5.m0Of_le_M) ?_
      (inSubgroup_pCore_two _).1
    intro m hm
    exact mem_normalizer_map_subtype_of_characteristic
      (hR.toHyp.le_normalizer_m0Of hm) (pCore 2 ↥(m0Of M V))
  rw [← (hSg.pCore_eq_and hR).1]
  exact h1.trans (h2.trans h3)

theorem Sec6Hyp.commutator_fM0_lOf_mem_xOf (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {f l : G}
    (hf : f ∈ fM0 M V (conjSubgroup g V)) (hl : l ∈ lOf M V g) :
    ⁅f, l⁆ ∈ Tim79a.xOf V (hOf M V g) := by
  have hR := hS.sec5.toRootHyp
  have hSg := hS.sec5.shape hg
  have hFL : f ∈ Subgroup.normalizer (lOf M V g : Set G) :=
    (hS.fM0_le_normalizer_lOf_hOf hg).1 hf
  have hLmem : ⁅f, l⁆ ∈ lOf M V g := by
    have h1 : f * l * f⁻¹ ∈ lOf M V g := (Subgroup.mem_normalizer_iff.mp hFL l).mp hl
    have h2 : (f * l * f⁻¹) * l⁻¹ ∈ lOf M V g :=
      (lOf M V g).mul_mem h1 ((lOf M V g).inv_mem hl)
    simpa [commutatorElement_def] using h2
  have hLNF : lOf M V g ≤ Subgroup.normalizer (fM0 M V (conjSubgroup g V) : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans
      ((conjSubgroup_Pc_le_centralizer M V g).trans
        (Subgroup.centralizer_le_normalizer _)))).trans (hS.sec5.le_normalizer_fM0)
  have hFmem : ⁅f, l⁆ ∈ fM0 M V (conjSubgroup g V) := by
    have hconj : l * f⁻¹ * l⁻¹ ∈ fM0 M V (conjSubgroup g V) :=
      (Subgroup.mem_normalizer_iff.mp (hLNF hl) f⁻¹).mp (Subgroup.inv_mem _ hf)
    have heq : ⁅f, l⁆ = f * (l * f⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact (fM0 M V (conjSubgroup g V)).mul_mem hf hconj
  have hP : ⁅f, l⁆ ∈ Pc M V :=
    hS.fM0_inf_lOf_le_Pc hg (Subgroup.mem_inf.mpr ⟨hFmem, hLmem⟩)
  have hPg : ⁅f, l⁆ ∈ conjSubgroup g (Pc M V) := hLmem.1
  exact hSg.Pc_inf_conj_le_xOf hR (Subgroup.mem_inf.mpr ⟨hP, hPg⟩)

theorem Sec6Hyp.commutator_fM0_kOf_mem_xOf (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {f : G}
    (hf : f ∈ fM0 M V (conjSubgroup g V)) {k : G}
    (hk : k ∈ kOf V (hOf M V g)) : ⁅f, k⁆ ∈ Tim79a.xOf V (hOf M V g) := by
  have hR := hS.sec5.toRootHyp
  have hSg := hS.sec5.shape hg
  have hFH : f ∈ Subgroup.normalizer (hOf M V g : Set G) :=
    (hS.fM0_le_normalizer_lOf_hOf hg).2 hf
  have hFW : f ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V g) : Set G) :=
    (hS.fM0_le_centralizer_xOf hg) hf
  have hKW : kOf V (hOf M V g) ≤
      Subgroup.normalizer (Tim79a.xOf V (hOf M V g) : Set G) :=
    (kOf_le V (hOf M V g)).trans (Tim79a.H_le_normalizer_xOf V (hOf M V g))
  have hsup : (Pc M V ⊓ kOf V (hOf M V g)) ⊔
      (conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g)) ≤
      CFSG.GroupTheory.commMemSubgroup (kOf V (hOf M V g))
        (Tim79a.xOf V (hOf M V g)) hKW f := by
    refine sup_le ?_ ?_
    · rintro k ⟨hkP, hkK⟩
      obtain ⟨y, hyH, hPy, -, -, -⟩ := hS.sec5.exists_conj_data hg
      have hk'K : y * k * y⁻¹ ∈ kOf V (hOf M V g) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V (hOf M V g) hyH) k).mp hkK
      have hkP' : k ∈ Pc M V := hkP
      have hk'P : y * k * y⁻¹ ∈ conjSubgroup g (Pc M V) := by
        rw [hPy]
        exact mem_conjSubgroup.mpr
          (by simpa only [show y⁻¹ * (y * k * y⁻¹) * y = k by group] using hkP')
      have hk'L : y * k * y⁻¹ ∈ lOf M V g :=
        Subgroup.mem_inf.mpr ⟨hk'P, hSg.kOf_le_M hR hk'K⟩
      have hfk' : ⁅f, y * k * y⁻¹⁆ ∈ Tim79a.xOf V (hOf M V g) :=
        hS.commutator_fM0_lOf_mem_xOf hg hf hk'L
      have hfH : ∀ z ∈ hOf M V g, ⁅f, z⁆ ∈ kOf V (hOf M V g) := fun z hz =>
        commutator_mem_kOf_of_mem_normalizer hFH hFW hz
      have hmain := commutator_conj_mem_of_quotMod (hSg.quotModHyp hR) hfH
        ((hOf M V g).inv_mem hyH) hk'K hfk'
      have heq : y⁻¹ * (y * k * y⁻¹) * (y⁻¹)⁻¹ = k := by group
      rw [heq] at hmain
      refine ⟨hkK, ?_⟩
      rw [show ⁅k, f⁆ = ⁅f, k⁆⁻¹ from (commutatorElement_inv f k).symm]
      exact (Tim79a.xOf V (hOf M V g)).inv_mem hmain
    · rintro k ⟨hkP, hkK⟩
      have hkL : k ∈ lOf M V g :=
        Subgroup.mem_inf.mpr ⟨hkP, hSg.kOf_le_M hR hkK⟩
      have hfk : ⁅f, k⁆ ∈ Tim79a.xOf V (hOf M V g) :=
        hS.commutator_fM0_lOf_mem_xOf hg hf hkL
      refine ⟨hkK, ?_⟩
      rw [show ⁅k, f⁆ = ⁅f, k⁆⁻¹ from (commutatorElement_inv f k).symm]
      exact (Tim79a.xOf V (hOf M V g)).inv_mem hfk
  have hk' : k ∈ (Pc M V ⊓ kOf V (hOf M V g)) ⊔
      (conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g)) := by
    rwa [hSg.kFact] at hk
  have hcomm : ⁅k, f⁆ ∈ Tim79a.xOf V (hOf M V g) :=
    ((CFSG.GroupTheory.mem_commMemSubgroup hKW f k).mp (hsup hk')).2
  rw [show ⁅f, k⁆ = ⁅k, f⁆⁻¹ from (commutatorElement_inv k f).symm]
  exact (Tim79a.xOf V (hOf M V g)).inv_mem hcomm

theorem Sec6Hyp.false_of_mem_restM0 (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {C : Subgroup G}
    (hC : C ∈ restM0 M V (conjSubgroup g V)) : False := by
  obtain ⟨C', hC', hl2⟩ := hS.exists_partner_restM0 hg hC
  obtain ⟨a, haC, b, hbC', hord⟩ := hl2.exists_orderOf_eq_three
  have hR := hS.sec5.toRootHyp
  have hSg := hS.sec5.shape hg
  have haF : a ∈ fM0 M V (conjSubgroup g V) :=
    (le_iSup₂ (f := fun D (_ : D ∈ restM0 M V (conjSubgroup g V)) => D) C hC) haC
  have hbF : b ∈ fM0 M V (conjSubgroup g V) :=
    (le_iSup₂ (f := fun D (_ : D ∈ restM0 M V (conjSubgroup g V)) => D) C' hC') hbC'
  have htF : a * b ∈ fM0 M V (conjSubgroup g V) := mul_mem haF hbF
  have htW : a * b ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V g) : Set G) :=
    (hS.fM0_le_centralizer_xOf hg) htF
  have ht3 : (a * b) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one (a * b)
  have hW2 : IsPGroup 2 (Tim79a.xOf V (hOf M V g)) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx2 : ((x : G)) ^ 2 = 1 := (hSg.isElemAbelian hR).2 x x.2
    have hx2' : x ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have htK : a * b ∈ Subgroup.centralizer (kOf V (hOf M V g) : Set G) := by
    refine CFSG.mem_centralizer_of_odd_pow_eq_one (N := Tim79a.xOf V (hOf M V g))
      (P := kOf V (hOf M V g)) hW2 (by norm_num) ht3 htW ?_
    intro p hp
    exact hS.commutator_fM0_kOf_mem_xOf hg htF hp
  have htP : a * b ∈ Subgroup.centralizer (Pc M V : Set G) := by
    refine CFSG.mem_centralizer_of_odd_pow_eq_one (N := kOf V (hOf M V g))
      (P := Pc M V) (hR.isPGroup_kOf_of_factorization hSg.kFact) (by norm_num) ht3 htK ?_
    intro p hp
    exact commutator_mem_kOf_of_mem_normalizer
      ((hS.fM0_le_normalizer_lOf_hOf hg).2 htF) htW (hSg.Pc_le hp)
  have htV : a * b ∈ V := by
    rw [← hR.toHyp.centralizer_Pc]
    exact htP
  have ht2 : (a * b) ^ 2 = 1 := hR.toHyp.elem.2 (a * b) htV
  have hdvd : 3 ∣ 2 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one ht2
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  omega

end CFSG.RankThree.GF2n.Tim81
