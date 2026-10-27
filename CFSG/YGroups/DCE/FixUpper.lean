module

public import CFSG.YGroups.DCE.OrbitLower
public import CFSG.YGroups.DCE.Maximal
public import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG.YGroups.SymGen.Setup

open CFSG.YGroups.DCE

variable {G E Ω X : Type*} [Group G] [Group E] [MulAction E Ω] [MulAction E X]
  (S : Setup G E Ω)

@[expose] def fixSet (d : G) : Set (G ⧸ S.H) := {c | d • c = c}

@[expose] def fixLabels (y : G) (d : E) (ω₀ : X) : Set X :=
  {ω | ∃ e : E, e⁻¹ • ω₀ = ω ∧ e⁻¹ * d * e ∈ B.stabSub S y}

variable {S}

theorem cosetOf_mem_fixSet_iff {y : G} {e d : E} :
    S.cosetOf y e ∈ S.fixSet (S.ψ d) ↔ e⁻¹ * d * e ∈ B.stabSub S y := by
  rw [fixSet, Set.mem_ofPred_eq, cosetOf, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    B.mem_stabSub]
  have h : (S.ψ d * (S.ψ e * y⁻¹))⁻¹ * (S.ψ e * y⁻¹) = (y * S.ψ (e⁻¹ * d * e) * y⁻¹)⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [h, inv_mem_iff]

theorem smul_mem_fixLabels {y : G} {d : E} {ω₀ ω : X} (hω : ω ∈ S.fixLabels y d ω₀)
    {s : E} (hs : s ∈ B.stabSub S y) : s • ω ∈ S.fixLabels y d ω₀ := by
  obtain ⟨e, rfl, he⟩ := hω
  refine ⟨e * s⁻¹, ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv, mul_smul]
  · have : (e * s⁻¹)⁻¹ * d * (e * s⁻¹) = s * (e⁻¹ * d * e) * s⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hs he) (inv_mem hs)

theorem card_fix_node_le [Finite E] [Finite X] {y : G} {d : E} {ω₀ : X} {s : ℕ}
    (hs : (B.stabSub S y).index ≤ s) (Xc : Finset X)
    (hX : S.fixLabels y d ω₀ ⊆ Xc) :
    {c | ∃ e : E, c = S.cosetOf y e ∧ c ∈ S.fixSet (S.ψ d)}.ncard *
        (MulAction.orbit E ω₀).ncard ≤ Xc.card * s := by
  classical
  have : Fintype E := Fintype.ofFinite E
  set Sn := B.stabSub S y
  set C := {c | ∃ e : E, c = S.cosetOf y e ∧ c ∈ S.fixSet (S.ψ d)}
  let A : Finset E := Finset.univ.filter fun e => e⁻¹ * d * e ∈ Sn
  have hCimg : C = (A.image (S.cosetOf y) : Set (G ⧸ S.H)) := by
    ext c
    simp only [C, Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, A,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, rfl, he⟩
      exact ⟨e, cosetOf_mem_fixSet_iff.1 he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, rfl, cosetOf_mem_fixSet_iff.2 he⟩
  have hfib : ∀ c ∈ A.image (S.cosetOf y), Nat.card Sn ≤ (A.filter fun e => S.cosetOf y e = c).card := by
    intro c hc
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 hc
    have he₀' : e₀⁻¹ * d * e₀ ∈ Sn := (Finset.mem_filter.1 he₀).2
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun s => ⟨e₀ * s.1, ?_⟩) ?_
    · refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have : (e₀ * s.1)⁻¹ * d * (e₀ * s.1) = s.1⁻¹ * (e₀⁻¹ * d * e₀) * s.1 := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem s.2) he₀') s.2
      · rw [S.cosetOf_eq_iff]
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact inv_mem s.2
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel this)
  have hA1 : (A.image (S.cosetOf y)).card * Nat.card Sn ≤ A.card := by
    rw [mul_comm]
    calc Nat.card Sn * (A.image (S.cosetOf y)).card
        = ∑ _c ∈ A.image (S.cosetOf y), Nat.card Sn := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ c ∈ A.image (S.cosetOf y), (A.filter fun e => S.cosetOf y e = c).card :=
          Finset.sum_le_sum hfib
      _ = A.card := (Finset.card_eq_sum_card_image (S.cosetOf y) A).symm
  have hA2 : A.card ≤ Xc.card * Nat.card (MulAction.stabilizer E ω₀) := by
    have hmaps : ∀ e ∈ A, e⁻¹ • ω₀ ∈ Xc := fun e he =>
      hX ⟨e, rfl, (Finset.mem_filter.1 he).2⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := fun e => e⁻¹ • ω₀) (t := Xc) hmaps]
    calc ∑ b ∈ Xc, (A.filter fun e => e⁻¹ • ω₀ = b).card
        ≤ ∑ _b ∈ Xc, Nat.card (MulAction.stabilizer E ω₀) := by
          refine Finset.sum_le_sum fun b _ => ?_
          by_cases hb : ∃ e₁ : E, e₁⁻¹ • ω₀ = b
          · obtain ⟨e₁, he₁⟩ := hb
            rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
            refine Fintype.card_le_of_injective
              (fun e => ⟨e₁ * e.1⁻¹, ?_⟩) ?_
            · have he := (Finset.mem_filter.1 e.2).2
              rw [MulAction.mem_stabilizer_iff, mul_smul, he, ← he₁, smul_inv_smul]
            · intro a b hab
              have := congrArg Subtype.val hab
              exact Subtype.ext (inv_injective (mul_left_cancel this))
          · have : (A.filter fun e => e⁻¹ • ω₀ = b) = ∅ := by
              refine Finset.filter_eq_empty_iff.2 fun e _ he => hb ⟨e, he⟩
            rw [this, Finset.card_empty]
            exact Nat.zero_le _
      _ = Xc.card * Nat.card (MulAction.stabilizer E ω₀) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hfinC : C.ncard = (A.image (S.cosetOf y)).card := by
    rw [hCimg, Set.ncard_coe_finset]
  have hidx := Subgroup.index_mul_card Sn
  have horb : (MulAction.orbit E ω₀).ncard * Nat.card (MulAction.stabilizer E ω₀) =
      Nat.card E := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_mul_card _
  have hpos : 0 < Nat.card (MulAction.stabilizer E ω₀) := Nat.card_pos
  have h1 : C.ncard * Nat.card E ≤ Xc.card * Nat.card (MulAction.stabilizer E ω₀) * s := by
    rw [← hidx, hfinC]
    calc (A.image (S.cosetOf y)).card * (Sn.index * Nat.card Sn)
        = (A.image (S.cosetOf y)).card * Nat.card Sn * Sn.index := by ring
      _ ≤ A.card * Sn.index := Nat.mul_le_mul_right _ hA1
      _ ≤ A.card * s := Nat.mul_le_mul_left _ hs
      _ ≤ Xc.card * Nat.card (MulAction.stabilizer E ω₀) * s := Nat.mul_le_mul_right _ hA2
  rw [← horb] at h1
  have h2 : C.ncard * (MulAction.orbit E ω₀).ncard * Nat.card (MulAction.stabilizer E ω₀) ≤
      Xc.card * s * Nat.card (MulAction.stabilizer E ω₀) := by
    calc C.ncard * (MulAction.orbit E ω₀).ncard * Nat.card (MulAction.stabilizer E ω₀)
        = C.ncard * ((MulAction.orbit E ω₀).ncard * Nat.card (MulAction.stabilizer E ω₀)) := by
          ring
      _ ≤ Xc.card * Nat.card (MulAction.stabilizer E ω₀) * s := h1
      _ = Xc.card * s * Nat.card (MulAction.stabilizer E ω₀) := by ring
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem cover_of_points (r : ℕ) (x : ℕ → G) (hx0 : x 0 ∈ S.H)
    (P : ℕ → Subgroup E) (hP : ∀ j < r, ∀ e ∈ P j, x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (R : ℕ → Finset Ω) (hR : ∀ j < r, ∀ p : Ω, ∃ q ∈ R j, ∃ e ∈ P j, e • q = p)
    (tgt : ℕ → Ω → ℕ) (u : ℕ → Ω → E)
    (htgt : ∀ j < r, ∀ q ∈ R j, tgt j q < r ∧ S.RCoset (x j * S.T q) (x (tgt j q) * S.ψ (u j q)))
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤) (hr : 0 < r) :
    ∀ c : G ⧸ S.H, ∃ i < r, ∃ e : E, c = S.cosetOf (x i) e := by
  have hCH : (MulAction.stabilizer E S.o).map S.ψ ≤ S.H := Subgroup.map_le_range _ _
  have htC : ∀ c ∈ (MulAction.stabilizer E S.o).map S.ψ, S.t * c = c * S.t := by
    rintro _ ⟨e, he, rfl⟩
    exact (S.stab_comm e he).symm
  obtain ⟨D, hDx, -, -⟩ := S.exists_pointsData r x hx0 P hP R hR tgt u htgt hr
  intro c
  obtain ⟨⟨i, q⟩, hq⟩ := D.cosetMap_surjective hCH S.t_mul_t htC hgen c
  induction q using QuotientGroup.induction_on with
  | H k =>
    obtain ⟨e, he⟩ := k.2
    refine ⟨i, i.2, e, ?_⟩
    rw [← hq, DoubleCosetData.cosetMap_mk, hDx, cosetOf, he]

theorem card_centralizer_le [Finite G] [Finite E] [Finite X] {d : E} {ω₀ : X} (x : ℕ → G)
    (I : Finset ℕ) (hcover : ∀ c : G ⧸ S.H, ∃ i ∈ I, ∃ e : E, c = S.cosetOf (x i) e)
    (s : ℕ → ℕ) (hs : ∀ i ∈ I, (B.stabSub S (x i)).index ≤ s i) (Xc : ℕ → Finset X)
    (hX : ∀ i ∈ I, S.fixLabels (x i) d ω₀ ⊆ Xc i) :
    Nat.card (Subgroup.centralizer {S.ψ d}) * (MulAction.orbit E ω₀).ncard ≤
      (∑ i ∈ I, (Xc i).card * s i) *
        Nat.card ((Subgroup.centralizer {S.ψ d}).subgroupOf S.H) := by
  classical
  set Z := Subgroup.centralizer {S.ψ d}
  have hfix : (S.fixSet (S.ψ d)).ncard * (MulAction.orbit E ω₀).ncard ≤
      ∑ i ∈ I, (Xc i).card * s i := by
    have hsub : S.fixSet (S.ψ d) ⊆
        ⋃ i ∈ I, {c | ∃ e : E, c = S.cosetOf (x i) e ∧ c ∈ S.fixSet (S.ψ d)} := by
      intro c hc
      obtain ⟨i, hi, e, rfl⟩ := hcover c
      exact Set.mem_biUnion hi ⟨e, rfl, hc⟩
    calc (S.fixSet (S.ψ d)).ncard * (MulAction.orbit E ω₀).ncard
        ≤ (∑ i ∈ I, {c | ∃ e : E, c = S.cosetOf (x i) e ∧ c ∈ S.fixSet (S.ψ d)}.ncard) *
            (MulAction.orbit E ω₀).ncard :=
          Nat.mul_le_mul_right _ ((Set.ncard_le_ncard hsub (Set.toFinite _)).trans
            (I.set_ncard_biUnion_le _))
      _ = ∑ i ∈ I, {c | ∃ e : E, c = S.cosetOf (x i) e ∧ c ∈ S.fixSet (S.ψ d)}.ncard *
            (MulAction.orbit E ω₀).ncard := Finset.sum_mul _ _ _
      _ ≤ ∑ i ∈ I, (Xc i).card * s i :=
          Finset.sum_le_sum fun i hi => card_fix_node_le (hs i hi) (Xc i) (hX i hi)
  have horbZ : (MulAction.orbit Z ((1 : G) : G ⧸ S.H)).ncard ≤ (S.fixSet (S.ψ d)).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    show S.ψ d • (z • ((1 : G) : G ⧸ S.H)) = z • ((1 : G) : G ⧸ S.H)
    have hzd : z * S.ψ d = S.ψ d * z := (Subgroup.mem_centralizer_singleton_iff.1 hz).symm.symm
    rw [smul_smul, ← hzd, mul_smul]
    congr 1
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq]
    simp
  have hstab : Nat.card (MulAction.stabilizer Z ((1 : G) : G ⧸ S.H)) =
      Nat.card (Z.subgroupOf S.H) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨⟨z.1.1, ?_⟩, ?_⟩
        invFun := fun z => ⟨⟨z.1.1, ?_⟩, ?_⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
    · have := z.2
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAction.Quotient.smul_coe,
        smul_eq_mul, mul_one, QuotientGroup.eq] at this
      simpa using this
    · exact z.1.2
    · exact z.2
    · rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAction.Quotient.smul_coe,
        smul_eq_mul, mul_one, QuotientGroup.eq]
      simp
  have hZ : Nat.card Z = (MulAction.orbit Z ((1 : G) : G ⧸ S.H)).ncard *
      Nat.card (Z.subgroupOf S.H) := by
    rw [← hstab, ← MulAction.index_stabilizer]
    exact (Subgroup.index_mul_card _).symm
  calc Nat.card Z * (MulAction.orbit E ω₀).ncard
      = (MulAction.orbit Z ((1 : G) : G ⧸ S.H)).ncard * (MulAction.orbit E ω₀).ncard *
          Nat.card (Z.subgroupOf S.H) := by rw [hZ]; ring
    _ ≤ (S.fixSet (S.ψ d)).ncard * (MulAction.orbit E ω₀).ncard *
          Nat.card (Z.subgroupOf S.H) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ horbZ)
    _ ≤ (∑ i ∈ I, (Xc i).card * s i) * Nat.card (Z.subgroupOf S.H) :=
        Nat.mul_le_mul_right _ hfix

end CFSG.YGroups.SymGen.Setup
