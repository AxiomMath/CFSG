module

public import CFSG.Quasithin.Vol2.KGFactC31HSBase
public import CFSG.RankThree.Native.HSMcLOuter
public import CFSG.Quasithin.Vol2.KGFactC31Fix

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.RankThree.Native

theorem centralizer_b0_eq :
    Subgroup.centralizer ({elt [1]} : Set G₀) = caGroup := by
  obtain ⟨hL, hconj⟩ := conj_of_tree rep_b0 c_treeA
  have h := card_centralizer_le_of_conj_list hL (nodup_of_keysDistinct hL c_keysA) hconj
  rw [Array.length_toList, c_sizeA, card_G₀] at h
  refine (Subgroup.eq_of_le_of_card_ge caGroup_le ?_).symm
  rw [card_caGroup]
  omega

theorem rep_b0' : Rep 100 b0T permA := rep_toTable hn100 _

@[expose] noncomputable def cbG : List (Equiv.Perm (Fin 100)) := (enumeration caChain).reverse

theorem forall₂_cbT : List.Forall₂ (Rep 100) cbT cbG := by
  have h := filterProducts_spec (f := fun _ => true) (P := fun _ => True)
    (fun T g hT => by simp) (forall₂_levelTables hn100 caChain) (Rep.idT hn100)
    (acc := []) (accG := []) .nil
  simp only [one_mul, List.map_id', List.append_nil, decide_true, List.filter_true] at h
  exact h

theorem mem_caChain_iff
    (g : Equiv.Perm (Fin 100)) :
    g ∈ caChain.originalSubgroup ↔ g ∈ hs100P ∧ g * permA = permA * g := by
  rw [caChain, certificate_originalSubgroup, ← map_genOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have hx' : x ∈ Subgroup.centralizer ({elt [1]} : Set G₀) := caGroup_le hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx'
    have := congrArg Subtype.val hx'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, b0_eq] at this
    exact this
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show ⟨g, hg⟩ ∈ caGroup
    rw [← centralizer_b0_eq, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, b0_eq]
    exact hc

theorem card_eq_countP_cbT
    {f : Table → Bool} {P : Equiv.Perm (Fin 100) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 100 T g → (f T = true ↔ P g)) (hPb : ∀ g, P g → g * permA = permA * g) :
    Nat.card {x : hs100P // P x} = cbT.countP f := by
  rw [countP_eq_of_forall₂ forall₂_cbT (q := fun g => decide (P g))
    (fun T g hT _ => by rw [hfP T g hT, decide_eq_true_iff]), cbG, List.countP_reverse,
    ← card_subtype_eq_countP caChain.originalSubgroup (enumeration caChain)
      (enumeration_nodup _ c_caCheck) (mem_enumeration_iff _ c_caCheck) P]
  refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ hs100P) P).trans
    ((Equiv.subtypeEquivRight fun g => ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ caChain.originalSubgroup) P).symm))
  rw [mem_caChain_iff]
  exact ⟨fun h => ⟨⟨h.1, hPb g h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem card_le_cosetCount
    {f : Table → Bool} {P : Equiv.Perm (Fin 100) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 100 T g → (f T = true ↔ P g)) {rsT : List Table}
    {rsG : List (Equiv.Perm (Fin 100))} (hrs : List.Forall₂ (Rep 100) rsT rsG)
    (hrsM : ∀ r ∈ rsG, r ∈ hs100P)
    (hP : ∀ g ∈ hs100P, P g → ∃ r ∈ rsG, g * permA * g⁻¹ = r * permA * r⁻¹) :
    Nat.card {g : hs100P // P g} ≤ cosetCount 100 cbT rsT f := by
  classical
  refine (card_le_sum_coset permA rsG P hP hrsM).trans (le_of_eq ?_)
  rw [cosetCount]
  refine (sum_map_eq_of_forall₂ hrs fun rT r hr hrm => ?_).symm
  have hr' : r ∈ hs100P := hrsM r hrm
  rw [card_eq_countP_cbT (P := fun c => c * permA = permA * c ∧ P (r * c))
    (f := fun c => commT 100 b0T c && f (compT 100 rT c))]
  · rw [countP_eq_of_forall₂ forall₂_cbT
      (q := fun c => decide (c * permA = permA * c ∧ P (r * c))) (fun T g hT hg => ?_),
      countP_eq_of_forall₂ forall₂_cbT
      (q := fun c => decide (c * permA = permA * c ∧ P (r * c))) (fun T g hT hg => ?_)]
    · rw [Bool.and_eq_true, commT, tblEq_iff_eq (Rep.compT rep_b0' hT) (Rep.compT hT rep_b0'),
        hfP _ _ (Rep.compT hr hT), decide_eq_true_iff]
      exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
    · have hc : g * permA = permA * g := by
        rw [cbG, List.mem_reverse, mem_enumeration_iff _ c_caCheck, mem_caChain_iff] at hg
        exact hg.2
      rw [hfP _ _ (Rep.compT hr hT), decide_eq_true_iff]
      exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · intro T g hT
    rw [Bool.and_eq_true, commT, tblEq_iff_eq (Rep.compT rep_b0' hT) (Rep.compT hT rep_b0'),
      hfP _ _ (Rep.compT hr hT)]
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
  · exact fun g h => h.1

theorem card_mulAut_le :
    Nat.card (MulAut G₀) ≤ 2 * Nat.card G₀ := by
  have h1 := (CFSG.ComponentClassification.OuterAutomorphisms.inner
    G₀).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner G₀) ≤
      Nat.card G₀ := by
    have hsurj : Function.Surjective
        (MonoidHom.rangeRestrict (MulAut.conj : G₀ →* MulAut G₀)) :=
      MonoidHom.rangeRestrict_surjective _
    exact Nat.card_le_card_of_surjective _ hsurj
  rw [h1]
  exact Nat.mul_le_mul outer_card_hs100P h2

theorem center_eq_bot : Subgroup.center G₀ = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  have hz' : (z : Equiv.Perm (Fin 100)) ∈
      Subgroup.centralizer (hs100P : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
    exact (congrArg Subtype.val this)
  rw [centralizer_hs100P, Subgroup.mem_bot] at hz'
  exact (Subgroup.mem_bot).mpr (Subtype.ext hz')

end CFSG.Quasithin.KGC31.HS

end
