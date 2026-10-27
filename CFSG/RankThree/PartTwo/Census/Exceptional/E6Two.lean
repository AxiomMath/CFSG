module

public import CFSG.RankThree.PartTwo.Census.Exceptional.E6E7
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Minuscule
  CFSG.RankThree.CentralCover CFSG.Assembly.RankThreeEven TauCeti
open scoped MatrixGroups commutatorElement

section Normalizer

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem conj_xm_mem {δ γ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hγ : IsRoot τ γ)
    (hne : δ + γ ≠ 0) {P : Subgroup (hV.minGroup k)} (hγP : hV.rootGroup k γ ≤ P)
    (hδγP : IsRoot τ (δ + γ) → hV.rootGroup k (δ + γ) ≤ P) (c e : k) :
    hV.xm k δ c * hV.xm k γ e * (hV.xm k δ c)⁻¹ ∈ P := by
  have e1 : hV.xm k δ c * hV.xm k γ e * (hV.xm k δ c)⁻¹ =
      ⁅hV.xm k δ c, hV.xm k γ e⁆ * hV.xm k γ e := by
    rw [commutatorElement_def]
    group
  rw [e1]
  refine P.mul_mem ?_ (hγP (hV.xm_mem_rootGroup k γ e))
  by_cases hr : IsRoot τ (δ + γ)
  · obtain ⟨σ, -, h⟩ := (hV.commutator_xm k hδ hγ hne).1 hr
    rw [h c e]
    exact hδγP hr (hV.xm_mem_rootGroup k _ _)
  · rw [(hV.commutator_xm k hδ hγ hne).2 hr c e]
    exact P.one_mem

theorem rootGroup_le_normalizer_iSup {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) {m : ℕ}
    (S : Fin m → Fin τ.rank → ℤ) (hS : ∀ j, IsRoot τ (S j))
    (h : ∀ j, δ + S j ≠ 0 ∧ (IsRoot τ (δ + S j) → ∃ l, S l = δ + S j)) :
    hV.rootGroup k δ ≤
      Subgroup.normalizer ((⨆ j, hV.rootGroup k (S j) : Subgroup (hV.minGroup k)) :
        Set (hV.minGroup k)) := by
  set P : Subgroup (hV.minGroup k) := ⨆ j, hV.rootGroup k (S j)
  have hconj : ∀ c : k, ∀ u ∈ P, hV.xm k δ c * u * (hV.xm k δ c)⁻¹ ∈ P := by
    intro c u hu
    have hle : P.map (MulAut.conj (hV.xm k δ c)).toMonoidHom ≤ P := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨e, rfl⟩ := (hV.mem_rootGroup k).1 hx
      refine conj_xm_mem hV k hδ (hS j) (h j).1 (le_iSup (fun j => hV.rootGroup k (S j)) j)
        (fun hr => ?_) c e
      obtain ⟨l, hl⟩ := (h j).2 hr
      rw [← hl]
      exact le_iSup (fun j => hV.rootGroup k (S j)) l
    exact hle ⟨u, hu, rfl⟩
  intro g hg
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
  refine mem_normalizer_of_conj_mem (hconj c) fun u hu => ?_
  have := hconj (-c) u hu
  rwa [← hV.xm_neg, inv_inv] at this

theorem isPGroup_iSup_rootGroup [CharP k 2] {m : ℕ} (S : Fin m → Fin τ.rank → ℤ)
    (hcomm : ∀ i j, ∀ x ∈ hV.rootGroup k (S i), ∀ y ∈ hV.rootGroup k (S j), x * y = y * x) :
    IsPGroup 2 (⨆ j, hV.rootGroup k (S j) : Subgroup (hV.minGroup k)) := by
  set P : Subgroup (hV.minGroup k) := ⨆ j, hV.rootGroup k (S j)
  have hP : P = Subgroup.closure (⋃ j, (hV.rootGroup k (S j) : Set (hV.minGroup k))) := by
    rw [Subgroup.closure_iUnion]
    simp only [Subgroup.closure_eq]
    rfl
  have hpair : (⋃ j, (hV.rootGroup k (S j) : Set (hV.minGroup k))).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact hcomm i j x hi y hj
  have hPc : IsMulCommutative P := hP ▸ Subgroup.isMulCommutative_closure hpair
  have hsq : ∀ x ∈ P, x ^ 2 = 1 := by
    intro x hx
    rw [hP] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hj
      rw [pow_two, ← hV.xm_add, ← two_mul, CharTwo.two_eq_zero, zero_mul, hV.xm_zero]
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := congrArg Subtype.val
        (hPc.is_comm.comm ⟨x, hP ▸ hx⟩ ⟨y, hP ▸ hy⟩)
      calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
            rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← hxy, mul_assoc,
              mul_assoc]
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hsq g g.2, Subgroup.coe_one])⟩

end Normalizer

theorem card_le_localRank_three_of_commuting_SL2_of_le_normalizer {G : Type} [Group G]
    [Finite G] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {K : Type*} [Field K] (φ : ι → SL(2, K) →* G)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) {P : Subgroup G}
    (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (hφP : ∀ i, φ i (sl2Three K) ∈ Subgroup.normalizer (P : Set G)) :
    Fintype.card ι ≤ localRank 3 G := by
  refine card_le_localRank_three_of_le_normalizer (fun i => (φ i).range) ?_
    (fun i => φ i (sl2Three K)) (fun i => ⟨_, rfl⟩) (fun i h => ?_) (fun i => ?_) hP hP2 hφP
  · rintro i j hij _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact hcomm i j hij A B
  · have h1 := Subgroup.mem_centralizer_iff.1 h (φ i (sl2Upper 1)) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact sl2Three_not_commute K ((hφ i) h1).symm
  · rw [← map_pow, sl2Three_pow_three, map_one]
    exact Subgroup.one_mem _


@[expose] def e6OrthoRoots : Fin 4 → Fin (Tag.rank .E6) → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def e6ModuleRoots : Fin 4 → Fin (Tag.rank .E6) → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 0, 0]]

open CFSG.LieType.Chevalley.RootOps in
theorem e6Two_check :
    (∀ i, isRootB .E6 (e6OrthoRoots i) = true) ∧ (∀ j, isRootB .E6 (e6ModuleRoots j) = true) ∧
    (∀ i j, i ≠ j → e6OrthoRoots i + e6OrthoRoots j ≠ 0 ∧ e6OrthoRoots i - e6OrthoRoots j ≠ 0 ∧
      isRootB .E6 (e6OrthoRoots i + e6OrthoRoots j) = false ∧
      isRootB .E6 (e6OrthoRoots i - e6OrthoRoots j) = false) ∧
    (∀ j l, j ≠ l → e6ModuleRoots j + e6ModuleRoots l ≠ 0 ∧
      isRootB .E6 (e6ModuleRoots j + e6ModuleRoots l) = false) ∧
    (∀ i j, e6OrthoRoots i + e6ModuleRoots j ≠ 0 ∧
      (isRootB .E6 (e6OrthoRoots i + e6ModuleRoots j) = true →
        ∃ l, e6ModuleRoots l = e6OrthoRoots i + e6ModuleRoots j)) ∧
    (∀ i j, -e6OrthoRoots i + e6ModuleRoots j ≠ 0 ∧
      (isRootB .E6 (-e6OrthoRoots i + e6ModuleRoots j) = true →
        ∃ l, e6ModuleRoots l = -e6OrthoRoots i + e6ModuleRoots j)) ∧
    isRootB .E6 (e6OrthoRoots 0 + e6ModuleRoots 0) = true := by
  decide +kernel

open CFSG.LieType.Chevalley.RootOps in
theorem four_le_twoLocalOddRank_e6Index_two (d : TypeE6LieIndex) (hq : d.1.fieldOrder = 2)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.steinberg) := by
  obtain ⟨hr1, hr2, hso, hmod, hplus, hminus, h13⟩ := e6Two_check
  have hroot : ∀ {v}, isRootB .E6 v = true → IsRoot .E6 v := fun h => isRootB_iff.1 h
  have hnot : ∀ {v : Fin (Tag.rank .E6) → ℤ}, isRootB .E6 v = false → ¬ IsRoot .E6 v :=
    fun hv hr => by
      rw [← isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  have h2 : ringChar d.1.fixedField = 2 := ringChar_fixedField_eq_two hq
  have : CharP d.1.fixedField 2 := ringChar.of_eq h2
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  set θ := toQuot (e6Embed d) hC with hθ
  choose ρ hinj hmem hcen using fun i =>
    exists_rootSL2' e6Data_valid d.1.fixedField neighbour_cartan_E6 (hroot (hr1 i))
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hij A B
    obtain ⟨h1, h2', h3, h4⟩ := hso i j hij
    exact (Subgroup.mem_centralizer_iff.1 (rankOne_le_centralizer e6Data_valid _ (hroot (hr1 i))
      (hroot (hr1 j)) h1 h2' (hnot h3) (hnot h4) (hmem i A)) (ρ j B) (hmem j B)).symm
  have hθρ : ∀ i, Function.Injective (θ.comp (ρ i)) := fun i =>
    toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i)
  set PC : Subgroup ↥(e6Data_valid.minGroup d.1.fixedField) :=
    ⨆ j, e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j) with hPC
  have hP2 : IsPGroup 2 PC := by
    refine isPGroup_iSup_rootGroup e6Data_valid _ e6ModuleRoots fun i j x hx y hy => ?_
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hx
    obtain ⟨e, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hy
    by_cases hij : i = j
    · subst hij
      rw [← e6Data_valid.xm_add, ← e6Data_valid.xm_add, add_comm]
    · exact commute_xm e6Data_valid _ (hroot (hr2 i)) (hroot (hr2 j)) (hmod i j hij).1
        (hnot (hmod i j hij).2) c e
  have hnorm : ∀ i A, ρ i A ∈ Subgroup.normalizer (PC : Set _) := by
    intro i A
    refine (sup_le ?_ ?_ : _ ≤ Subgroup.normalizer (PC : Set _)) (hmem i A)
    · exact rootGroup_le_normalizer_iSup e6Data_valid _ (hroot (hr1 i)) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hplus i j).1, fun h => (hplus i j).2 (isRootB_iff.2 h)⟩
    · exact rootGroup_le_normalizer_iSup e6Data_valid _
        (CFSG.LieType.Chevalley.IsRoot.neg (hroot (hr1 i))) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hminus i j).1, fun h => (hminus i j).2
          (isRootB_iff.2 h)⟩
  have hnc : e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1 ∉ Subgroup.center _ := by
    intro hc
    obtain ⟨σ, hσ, h⟩ := (e6Data_valid.commutator_xm d.1.fixedField (hroot (hr1 0))
      (hroot (hr2 0)) (hplus 0 0).1).1 (hroot h13)
    have h1 := h 1 1
    have h1' : ⁅e6Data_valid.xm d.1.fixedField (e6OrthoRoots 0) 1,
        e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1⁆ = 1 := by
      rw [commutatorElement_def, Subgroup.mem_center_iff.1 hc]
      group
    rw [h1', mul_one, mul_one] at h1
    have h0 := e6Data_valid.xm_injective d.1.fixedField (hroot h13)
      (h1.symm.trans (e6Data_valid.xm_zero _ _).symm)
    rcases hσ with rfl | rfl <;> simp at h0
  have hP : PC.map θ ≠ ⊥ := by
    intro hbot
    apply hnc
    refine mem_center_of_toQuot_eq_one (e6Embed_injective d) hC ?_
    have : θ (e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1) ∈ PC.map θ :=
      ⟨_, le_iSup (fun j => e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j)) 0
        (e6Data_valid.xm_mem_rootGroup _ _ _), rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h4 := card_le_localRank_three_of_commuting_SL2_of_le_normalizer (ι := Fin 4)
    (fun i => θ.comp (ρ i)) hθρ (fun i j hij A B => by
      simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]) hP (hP2.map θ)
    (fun i => Subgroup.le_normalizer_map θ ⟨_, hnorm i _, rfl⟩)
  rw [Fintype.card_fin] at h4
  exact four_le_twoLocalOddRank_of_localRank Nat.prime_three (by norm_num) h4

theorem four_le_twoLocalOddRank_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    [hfin : Finite (CFSGIndex.lie ⟨.E6 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  by_cases hq : q.card = 2
  · exact @four_le_twoLocalOddRank_e6Index_two
      ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩
      (by change (LieTypeIndex.E6 q).fieldOrder = 2; rw [LieTypeIndex.fieldOrder_E6]; exact hq)
      hfin
  · exact four_le_twoLocalOddRank_E6_of_ne_two q hv hq

end CFSG.RankThree.PartTwo.Census.Exceptional
