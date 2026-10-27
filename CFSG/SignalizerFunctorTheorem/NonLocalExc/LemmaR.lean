module

public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting

public noncomputable section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

@[expose] def simpleComplement (τ : Tag) (i : Fin τ.rank) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1}

@[expose] def unipComplement
    (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) :
    Subgroup (ModGL τ K) :=
  rootSpan τ K (simpleComplement τ i)

@[expose] def HasCoord
    (i : Fin τ.rank) (y : ModGL τ K) (c : K) : Prop :=
  ∃ b ∈ unipComplement τ K i, y = xUnit τ K i c * b

theorem xUnit_mem_posUnipotent
    (i : Fin τ.rank) (c : K) : xUnit τ K i c ∈ posUnipotent τ K := by
  rw [← pinnedX_single]
  exact pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α})
    ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ c

theorem unipComplement_le
    (i : Fin τ.rank) : unipComplement τ K i ≤ posUnipotent τ K :=
  (simple_positive_root_complement τ K i).1

theorem unipComplement_conj_mem
    (i : Fin τ.rank) {u : ModGL τ K} (hu : u ∈ posUnipotent τ K)
    {b : ModGL τ K} (hb : b ∈ unipComplement τ K i) : u * b * u⁻¹ ∈ unipComplement τ K i := by
  have hn := (simple_positive_root_complement τ K i).2.1
  have := hn.conj_mem ⟨b, unipComplement_le i hb⟩ (Subgroup.mem_subgroupOf.2 hb) ⟨u, hu⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem unipComplement_conj_mem'
    (i : Fin τ.rank) {u : ModGL τ K} (hu : u ∈ posUnipotent τ K)
    {b : ModGL τ K} (hb : b ∈ unipComplement τ K i) : u⁻¹ * b * u ∈ unipComplement τ K i := by
  simpa using unipComplement_conj_mem i (inv_mem hu) hb

theorem exists_coord
    (i : Fin τ.rank) {y : ModGL τ K} (hy : y ∈ posUnipotent τ K) :
    ∃ c, HasCoord i y c := by
  have h3 := (simple_positive_root_complement τ K i).2.2.1
  have hy' : y ∈ (rootSubgroup τ K (Pi.single i 1) : Set (ModGL τ K)) *
      (rootSpan τ K (simpleComplement τ i) : Set (ModGL τ K)) := by
    have hy1 : y ∈ (posUnipotent τ K : Set (ModGL τ K)) := hy
    rw [h3] at hy1
    exact hy1
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 ha
  exact ⟨c, b, hb, by rw [pinnedX_single]⟩

theorem xUnit_mem_rootSubgroup
    (i : Fin τ.rank) (c : K) :
    xUnit τ K i c ∈ rootSubgroup τ K (Pi.single i 1) :=
  mem_rootSubgroup.2 ⟨c, pinnedX_single τ K i c⟩

theorem xUnit_injective
    (i : Fin τ.rank) : Function.Injective (xUnit τ K i) := by
  intro c d h
  have : pinnedX τ K (Pi.single i 1) c = pinnedX τ K (Pi.single i 1) d := by
    rw [pinnedX_single, pinnedX_single, h]
  exact pinnedX_injective τ K _ this

theorem HasCoord.unique
    {i : Fin τ.rank} {y : ModGL τ K} {c c' : K} (h : HasCoord i y c)
    (h' : HasCoord i y c') : c = c' := by
  obtain ⟨b, hb, hy⟩ := h
  obtain ⟨b', hb', hy'⟩ := h'
  have hu := (simple_positive_root_complement τ K i).2.2.2.2.2.1
  exact xUnit_injective i (hu _ (xUnit_mem_rootSubgroup i c) _ (xUnit_mem_rootSubgroup i c') b hb
    b' hb' (hy.symm.trans hy')).1

theorem HasCoord.mul
    {i : Fin τ.rank} {y y' : ModGL τ K} {c c' : K} (h : HasCoord i y c)
    (h' : HasCoord i y' c') : HasCoord i (y * y') (c + c') := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  refine ⟨(xUnit τ K i c')⁻¹ * b * xUnit τ K i c' * b', mul_mem
    (unipComplement_conj_mem' i (xUnit_mem_posUnipotent i c') hb) hb', ?_⟩
  rw [xUnit_add]
  group

theorem HasCoord.inv
    {i : Fin τ.rank} {y : ModGL τ K} {c : K} (h : HasCoord i y c) :
    HasCoord i y⁻¹ (-c) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨xUnit τ K i c * b⁻¹ * (xUnit τ K i c)⁻¹, ?_, ?_⟩
  · exact unipComplement_conj_mem i (xUnit_mem_posUnipotent i c) (inv_mem hb)
  · have h1 : xUnit τ K i (-c) = (xUnit τ K i c)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← xUnit_add, neg_add_cancel, xUnit_zero]
    rw [h1]
    group

theorem hasCoord_xUnit
    (i : Fin τ.rank) (c : K) : HasCoord i (xUnit τ K i c) c :=
  ⟨1, one_mem _, by rw [mul_one]⟩

theorem HasCoord.conj_posUnipotent
    {i : Fin τ.rank} {y : ModGL τ K} {c : K} (h : HasCoord i y c)
    {u : ModGL τ K} (hu : u ∈ posUnipotent τ K) : HasCoord i (u⁻¹ * y * u) c := by
  obtain ⟨d, hd⟩ := exists_coord i hu
  have h1 := (hd.inv.mul h).mul hd
  have h2 : -d + c + d = c := by ring
  rwa [h2] at h1

theorem torus_conj_mem_rootSpan
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {b : ModGL τ K}
    (hb : b ∈ rootSpan τ K S) : h * b * h⁻¹ ∈ rootSpan τ K S := by
  obtain ⟨l, hl⟩ := exists_torus_characters hh
  have hle : rootSpan τ K S ≤ (rootSpan τ K S).comap (MulAut.conj h).toMonoidHom := by
    refine iSup₂_le fun α hα g hg => ?_
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, (hl α (hS α hα)).2]
    exact pinnedX_mem_rootSpan hα _
  exact hle hb

theorem HasCoord.conj_torus
    {i : Fin τ.rank} {y : ModGL τ K} {c : K} (h : HasCoord i y c)
    {t : ModGL τ K} (ht : t ∈ torusGroup τ K) :
    ∃ s : K, s ≠ 0 ∧ HasCoord i (t * y * t⁻¹) (s * c) := by
  obtain ⟨l, hl⟩ := exists_torus_characters ht
  obtain ⟨b, hb, rfl⟩ := h
  set s : K := ((∏ j, l j ^ (Pi.single i 1 : Fin τ.rank → ℤ) j : Kˣ) : K) with hs
  refine ⟨s, Units.ne_zero _, t * b * t⁻¹, torus_conj_mem_rootSpan ht
    (fun α hα => hα.1) hb, ?_⟩
  have h1 := (hl (Pi.single i 1) (isRoot_single τ i)).2 c
  simp only [pinnedX_single] at h1
  calc t * (xUnit τ K i c * b) * t⁻¹ = (t * xUnit τ K i c * t⁻¹) * (t * b * t⁻¹) := by group
    _ = xUnit τ K i (s * c) * (t * b * t⁻¹) := by rw [h1]

theorem borel_le_normalizer_posUnipotent :
    borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).1
    (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1

theorem conj_mem_posUnipotent_of_mem_borel
    {b : ModGL τ K} (hb : b ∈ borelGroup τ K)
    {u : ModGL τ K} (hu : u ∈ posUnipotent τ K) : b * u * b⁻¹ ∈ posUnipotent τ K :=
  (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_posUnipotent hb) u).1 hu

theorem pos_of_coord_of_conj_mem
    {i : Fin τ.rank} {w : WeylGroup τ} {y : ModGL τ K} {c : K}
    (hc : c ≠ 0) (hy : HasCoord i y c) (hyU : y ∈ posUnipotent τ K)
    (hconj : (canonicalRep (coxeterSystem τ) K w)⁻¹ * y * canonicalRep (coxeterSystem τ) K w ∈
      posUnipotent τ K) :
    0 < height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  by_contra hneg
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hu : n⁻¹ * y * n ∈ (posUnipotent τ K : Set (ModGL τ K)) := hconj
  rw [posUnipotent_eq_mul_rootSpan w] at hu
  obtain ⟨uJ, huJ, uI, huI, huu⟩ := hu
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hbij := bijOn_bruhatCell (K := K) w
  have hmem1 : (y, (1 : ModGL τ K)) ∈
      (borelGroup τ K : Set (ModGL τ K)) ×ˢ
        (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) :=
    ⟨hUB hyU, one_mem _⟩
  have hmem2 : (n * uJ * n⁻¹, uI) ∈
      (borelGroup τ K : Set (ModGL τ K)) ×ˢ
        (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) :=
    ⟨hUB (canonicalRep_conj_mem_posUnipotent huJ), huI⟩
  have heq : y * n * 1 = (n * uJ * n⁻¹) * n * uI := by
    have h1 : y * n = n * (n⁻¹ * y * n) := by group
    rw [mul_one, h1, ← huu]
    group
  have hpair := hbij.injOn hmem1 hmem2 heq
  have hyeq : y = n * uJ * n⁻¹ := congrArg Prod.fst hpair
  have hyspan : y ∈ rootSpan τ K ((fun α => w • α) '' nonInversionSet w) := by
    rw [hyeq]
    exact canonicalRep_conj_mem_rootSpan (fun α (h : α ∈ nonInversionSet w) => h.1) huJ
  have hsub : (fun α => w • α) '' nonInversionSet w ⊆ simpleComplement τ i := by
    rintro _ ⟨α, ⟨hα, hαpos, hwα⟩, rfl⟩
    refine ⟨IsRoot.smul hα w, hwα, fun h => hneg ?_⟩
    have : α = w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) := by
      rw [← h, inv_smul_smul]
    rw [← this]
    exact hαpos
  have hle : rootSpan τ K ((fun α => w • α) '' nonInversionSet w) ≤ unipComplement τ K i :=
    biSup_mono hsub
  have hyU' : y ∈ unipComplement τ K i := hle hyspan
  obtain ⟨b, hb, hyb⟩ := hy
  have hxb : xUnit τ K i c ∈ unipComplement τ K i := by
    have : xUnit τ K i c = y * b⁻¹ := by rw [hyb]; group
    rw [this]
    exact mul_mem hyU' (inv_mem hb)
  have hinf : rootSubgroup τ K (Pi.single i 1) ⊓ unipComplement τ K i = ⊥ :=
    (simple_positive_root_complement τ K i).2.2.2.2.1
  have hx1 : xUnit τ K i c ∈ rootSubgroup τ K (Pi.single i 1) ⊓ unipComplement τ K i :=
    Subgroup.mem_inf.2 ⟨xUnit_mem_rootSubgroup i c, hxb⟩
  rw [hinf, Subgroup.mem_bot, ← xUnit_zero i] at hx1
  exact hc (xUnit_injective i hx1)

theorem mem_borelGroup_of_conj_simple_mem_posUnipotent
    {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K)
    (h : ∀ i : Fin τ.rank, g⁻¹ * xUnit τ K i 1 * g ∈ posUnipotent τ K) :
    g ∈ borelGroup τ K := by
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb hb'
  · exfalso
    obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition τ).2.2.2 w⁻¹ (inv_ne_one.2 hw1)
    set n := canonicalRep (coxeterSystem τ) K w with hn
    have hx : xUnit τ K i 1 ∈ posUnipotent τ K := xUnit_mem_posUnipotent i 1
    have hyU : b⁻¹ * xUnit τ K i 1 * b ∈ posUnipotent τ K := by
      simpa using conj_mem_posUnipotent_of_mem_borel (inv_mem hb) hx
    have hb2 : b ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) := by
      rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1]
      exact hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hb2
    have hcoord1 : HasCoord i (u⁻¹ * xUnit τ K i 1 * u) 1 :=
      (hasCoord_xUnit i 1).conj_posUnipotent hu
    obtain ⟨s, hs, hcoord2⟩ := hcoord1.conj_torus (inv_mem ht)
    have hy : (u * t)⁻¹ * xUnit τ K i 1 * (u * t) =
        t⁻¹ * (u⁻¹ * xUnit τ K i 1 * u) * t⁻¹⁻¹ := by group
    have hconj : n⁻¹ * ((u * t)⁻¹ * xUnit τ K i 1 * (u * t)) * n ∈ posUnipotent τ K := by
      have h1 := conj_mem_posUnipotent_of_mem_borel hb' (h i)
      have h2 : b' * ((u * t * n * b')⁻¹ * xUnit τ K i 1 * (u * t * n * b')) * b'⁻¹ =
          n⁻¹ * ((u * t)⁻¹ * xUnit τ K i 1 * (u * t)) * n := by group
      rwa [h2] at h1
    have hyU' : t⁻¹ * (u⁻¹ * xUnit τ K i 1 * u) * t⁻¹⁻¹ ∈ posUnipotent τ K := by
      rw [← hy]
      exact hyU
    rw [hy] at hconj
    rw [mul_one] at hcoord2
    have hpos := pos_of_coord_of_conj_mem hs hcoord2 hyU' hconj
    have := hneg
    omega

end CFSG.SignalizerFunctorTheorem.NonLocalExc
