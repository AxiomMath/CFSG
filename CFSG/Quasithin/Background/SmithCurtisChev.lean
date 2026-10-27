module

public import CFSG.Quasithin.Background.SmithCurtisChevAmb
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.Quasithin.Background.SmithCurtisDatum

public noncomputable section

namespace CFSG.Quasithin.SmithCurtis.Chev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem conj_mem_subgroupOf {M : Type*} [Group M] {A S : Subgroup M} {g x : A}
    (h : (g : M) * x * (g : M)⁻¹ ∈ S) : g * x * g⁻¹ ∈ S.subgroupOf A := h

theorem conj_inv_mem_subgroupOf {M : Type*} [Group M] {A S : Subgroup M} {g x : A}
    (h : (g : M)⁻¹ * x * g ∈ S) : g⁻¹ * x * g ∈ S.subgroupOf A := h

theorem heckeDeg_subgroupOf {M : Type*} [Group M] {A U : Subgroup M} (hU : U ≤ A) (g : A) :
    heckeDeg (U.subgroupOf A) g = heckeDeg U (g : M) := by
  unfold heckeDeg
  have h : (U.subgroupOf A).map (MulAut.conj g).toMonoidHom =
      (U.map (MulAut.conj (g : M)).toMonoidHom).subgroupOf A := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hU hy⟩, hy, Subtype.ext e⟩
  rw [h, Subgroup.relIndex_subgroupOf hU]

variable (τ K) in
@[expose] def nC
    (i : Fin τ.rank) : adjointGroup τ K :=
  ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩

variable (τ K) in
@[expose] def nWC
    (w : WeylGroup τ) : adjointGroup τ K :=
  ⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩

variable (τ K) in
@[expose] def xC
    (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩

variable (τ K) in
@[expose] def yC
    (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩

variable (τ K) in
@[expose] def dC
    (i : Fin τ.rank) (t : Kˣ) : adjointGroup τ K :=
  ⟨torusElt τ K i t, torusElt_mem_adjointGroup i t⟩

open Classical in
variable (τ K) in
@[expose] def torusPart
    (i : Fin τ.rank) (g : adjointGroup τ K) : adjointGroup τ K :=
  if h : ∃ c : Kˣ, (g : ModGL τ K) = xUnit τ K i c then dC τ K i (-h.choose) else 1

theorem negUnipotent_le_adjointGroup'
    : negUnipotent τ K ≤ adjointGroup τ K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem torus_conj_mem_rootSubgroup
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) {g : ModGL τ K} (hg : g ∈ rootSubgroup τ K α) :
    h * g * h⁻¹ ∈ rootSubgroup τ K α := by
  rw [← rootSpan_singleton] at hg ⊢
  exact torus_conj_mem_rootSpan (by simpa using hα) hh hg

theorem torus_inv_conj_mem {S : Subgroup (ModGL τ K)} {h g : ModGL τ K}
    (hN : h ∈ Subgroup.normalizer (S : Set (ModGL τ K))) (hg : g ∈ S) : h⁻¹ * g * h ∈ S := by
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) g).mp hg
  rwa [inv_inv] at this

theorem weylElt_inv_conj_torusElt
    (i : Fin τ.rank) (t : Kˣ) :
    (weylElt τ K i 1)⁻¹ * torusElt τ K i t * weylElt τ K i 1 = torusElt τ K i t⁻¹ := by
  have h := weylElt_one_mul_torusElt_mul_inv (τ := τ) (R := K) i i t⁻¹
  rw [τ.cartan_self, ← torusElt_mul] at h
  have e : t⁻¹ * t⁻¹ ^ (-(2 : ℤ)) = t := by
    rw [inv_zpow', neg_neg, ← zpow_neg_one, ← zpow_add, show (-1 : ℤ) + 2 = 1 from rfl,
      zpow_one]
  rw [e] at h
  rw [← h]
  group

theorem exists_unit_of_mem
    {i : Fin τ.rank} {g : adjointGroup τ K}
    (hg : (g : ModGL τ K) ∈ rootSubgroup τ K (Pi.single i 1)) (hg1 : g ≠ 1) :
    ∃ c : Kˣ, (g : ModGL τ K) = xUnit τ K i c := by
  obtain ⟨c, hc⟩ := mem_rootSubgroup_single.mp hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hg1
    refine Subtype.ext ?_
    rw [← hc, xUnit_zero]
    rfl
  exact ⟨Units.mk0 c hc0, hc.symm⟩

theorem torusPart_eq
    {i : Fin τ.rank} {g : adjointGroup τ K} {c : Kˣ}
    (hg : (g : ModGL τ K) = xUnit τ K i c) : torusPart τ K i g = dC τ K i (-c) := by
  have h : ∃ c : Kˣ, (g : ModGL τ K) = xUnit τ K i c := ⟨c, hg⟩
  have hc : h.choose = c := Units.ext (xUnit_injective i (h.choose_spec.symm.trans hg))
  rw [torusPart, dite_eq_left h, hc]

variable (τ K) in
@[expose] def chevDatum
    [Finite K] (p : ℕ) [CharP K p]
    (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α) :
    CurtisDatum (adjointGroup τ K) (coxeterSystem τ) p where
  U := (posUnipotent τ K).subgroupOf (adjointGroup τ K)
  L := (negUnipotent τ K).subgroupOf (adjointGroup τ K)
  H := (torusGroup τ K).subgroupOf (adjointGroup τ K)
  X i := (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K)
  Y i := (rootSubgroup τ K (-Pi.single i 1)).subgroupOf (adjointGroup τ K)
  Us i := (posComplement τ K i).subgroupOf (adjointGroup τ K)
  Q i := (negComplement τ K i).subgroupOf (adjointGroup τ K)
  n i := nC τ K i
  nW w := nWC τ K w
  phi i := torusPart τ K i
  psi i := torusPart τ K i
  isPGroup_U := ((positive_root_triangularity.{0, 0} τ).2 K p).2.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).symm
  isPGroup_L := ((positive_root_triangularity.{0, 0} τ).2 K p).2.2.2.of_equiv
    (Subgroup.subgroupOfEquivOfLe negUnipotent_le_adjointGroup').symm
  U_inf_L := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have h : (x : ModGL τ K) ∈ posUnipotent τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  H_comm a ha b hb := Subtype.ext ((triangular_borel_structure.{0, 0} τ K).1 _ ha _ hb)
  H_normU h hh u hu := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.mp ((triangular_borel_structure.{0, 0} τ K).2.2.1 hh) u).mp hu)
  H_normU' h hh u hu := conj_inv_mem_subgroupOf
    (torus_inv_conj_mem ((triangular_borel_structure.{0, 0} τ K).2.2.1 hh) hu)
  H_normL h hh l hl := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_negUnipotent hh) l).mp hl)
  H_normX i h hh x hx := conj_mem_subgroupOf (torus_conj_mem_rootSubgroup (isRoot_single τ i) hh hx)
  H_normQ i h hh q hq := conj_mem_subgroupOf (torus_conj_mem_rootSpan (fun γ hγ => hγ.1) hh hq)
  X_le i x hx := rootSubgroup_single_le i hx
  X_ne_bot i := by
    intro h
    have hx : xC τ K i 1 ∈ (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K) :=
      xUnit_mem_rootSubgroup i 1
    rw [h, Subgroup.mem_bot] at hx
    have h1 : xUnit τ K i (1 : K) = xUnit τ K i 0 := by
      rw [xUnit_zero]
      exact congrArg Subtype.val hx
    exact one_ne_zero (xUnit_injective i h1)
  U_eq i u hu := by
    have hU := (simple_positive_root_complement τ K i).2.2.1
    have hu' : (u : ModGL τ K) ∈ (rootSubgroup τ K (Pi.single i 1) : Set (ModGL τ K)) *
        (posComplement τ K i : Set (ModGL τ K)) := by
      rw [posComplement, ← hU]
      exact hu
    obtain ⟨x, hx, v, hv, e⟩ := hu'
    exact ⟨⟨x, rootSubgroup_le_adjointGroup _ hx⟩, hx,
      ⟨v, posUnipotent_le_adjointGroup (posComplement_le i hv)⟩, hv, Subtype.ext e.symm⟩
  Us_le i v hv := posComplement_le i hv
  X_normUs i x hx v hv := by
    have hn := (Subgroup.normal_subgroupOf_iff (posComplement_le (K := K) i)).1
      (simple_positive_root_complement τ K i).2.1
    exact conj_mem_subgroupOf (hn _ _ hv (rootSubgroup_single_le i hx))
  n_normUs i v hv := by
    have h := (simple_Weyl_positive_complement τ K i 1).1
    refine conj_mem_subgroupOf ?_
    rw [← h]
    exact ⟨v, hv, rfl⟩
  n_normUs' i v hv := by
    have h := (simple_Weyl_positive_complement τ K i 1).1
    refine conj_inv_mem_subgroupOf ?_
    have hv' : (v : ModGL τ K) ∈ (posComplement τ K i).map
        (MulAut.conj (weylElt τ K i 1)).toMonoidHom := by
      rw [h]
      exact hv
    obtain ⟨v', hv', e⟩ := hv'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    show (weylElt τ K i 1)⁻¹ * v * weylElt τ K i 1 ∈ posComplement τ K i
    rw [← e]
    group
    exact hv'
  Y_le i y hy := rootSubgroup_neg_single_le i hy
  Q_le i q hq := negComplement_le i hq
  L_le i l hl := by
    obtain ⟨w₁, hw₁⟩ := hw
    obtain ⟨y, hy, q, hq, e⟩ := negUnipotent_eq_mul hw₁ i hl
    have hl' : l = ⟨y, rootSubgroup_le_adjointGroup _ hy⟩ *
        ⟨q, negUnipotent_le_adjointGroup' (negComplement_le i hq)⟩ := Subtype.ext e
    rw [hl']
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)
  X_normQ i x hx q hq := by
    obtain ⟨w₁, hw₁⟩ := hw
    exact conj_mem_subgroupOf (xUnit_conj_negComplement hw₁ i hx hq)
  Y_normQ i y hy q hq := by
    obtain ⟨w₁, hw₁⟩ := hw
    exact conj_mem_subgroupOf (negComplement_normal hw₁ i hy hq)
  n_normQ i q hq := conj_mem_subgroupOf (weylElt_conj_negComplement i hq)
  n_conjX i x hx := by
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := mem_rootSubgroup_single.mp hx
    refine conj_mem_subgroupOf ?_
    change weylElt τ K i 1 * (x : ModGL τ K) * (weylElt τ K i 1)⁻¹ ∈ _
    rw [← hc, weylElt_conj_xUnit]
    exact yUnit_mem_rootSubgroup i _
  n_conjY i y hy := by
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨c, hc⟩ := mem_rootSubgroup_neg_single.mp hy
    refine conj_mem_subgroupOf ?_
    change weylElt τ K i 1 * (y : ModGL τ K) * (weylElt τ K i 1)⁻¹ ∈ _
    rw [← hc, weylElt_conj_yUnit]
    exact xUnit_mem_rootSubgroup i _
  n_sq i := weylElt_sq_mem_torus i
  n_normH i h hh := conj_mem_subgroupOf (weylElt_mem_normalizer_torus' i hh)
  phi_mem i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    exact torusElt_mem_torusGroup i _
  psi_mem i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    exact torusElt_mem_torusGroup i _
  phi_spec i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    refine ⟨yC τ K i ((c⁻¹ : Kˣ) : K), rootSubgroup_neg_single_le i (yUnit_mem_rootSubgroup i _),
      xC τ K i (-((c⁻¹ : Kˣ) : K)), rootSubgroup_single_le i (xUnit_mem_rootSubgroup i _), ?_⟩
    refine Subtype.ext ?_
    change (x : ModGL τ K) * weylElt τ K i 1 = yUnit τ K i ((c⁻¹ : Kˣ) : K) *
      torusElt τ K i (-c) * xUnit τ K i (-((c⁻¹ : Kˣ) : K))
    rw [hc, xUnit_mul_weylElt, weylElt_inv_conj_yUnit, weylElt_one_mul_self, ← torusElt_mul,
      mul_neg_one]
  psi_spec i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    refine ⟨xC τ K i (-((c⁻¹ : Kˣ) : K)), xUnit_mem_rootSubgroup i _,
      xC τ K i (-((c⁻¹ : Kˣ) : K)), rootSubgroup_single_le i (xUnit_mem_rootSubgroup i _), ?_⟩
    refine Subtype.ext ?_
    change weylElt τ K i 1 * (x : ModGL τ K) * weylElt τ K i 1 =
      xUnit τ K i (-((c⁻¹ : Kˣ) : K)) * weylElt τ K i 1 * torusElt τ K i (-c) *
        xUnit τ K i (-((c⁻¹ : Kˣ) : K))
    rw [hc, weylElt_mul_xUnit_mul_weylElt, weylElt_inv_conj_torusElt, weylElt_inv_conj_yUnit,
      inv_neg, inv_inv]
  bruhatY i y hy hy1 := by
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨c, hc⟩ := mem_rootSubgroup_neg_single.mp hy
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hy1
      refine Subtype.ext ?_
      rw [← hc, yUnit_zero]
      rfl
    obtain ⟨h, hh, a, ha, b, hb, e⟩ := yUnit_eq (K := K) i (Units.mk0 c hc0)
    refine ⟨⟨h, (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K |>.1
      (Subgroup.mem_sup_left hh)⟩, hh, ⟨a, rootSubgroup_le_adjointGroup _ ha⟩, ha,
      ⟨b, rootSubgroup_le_adjointGroup _ hb⟩, hb, Subtype.ext ?_⟩
    change (y : ModGL τ K) = a * (h * weylElt τ K i 1) * b
    rw [← hc, ← e, Units.val_mk0]
  nW_one := Subtype.ext (canonicalRep_one _ K)
  nW_simple_mul w i h := Subtype.ext (weylElt_mul_canonicalRep_of_length_eq h).symm
  nW_conj w i h x hx := canonicalRep_inv_conj_mem h hx
  heckeDeg_mul w i h := by
    rw [heckeDeg_subgroupOf posUnipotent_le_adjointGroup,
      heckeDeg_subgroupOf posUnipotent_le_adjointGroup,
      heckeDeg_subgroupOf posUnipotent_le_adjointGroup]
    change heckeDeg _ (weylElt τ K i 1) * heckeDeg _ (canonicalRep (coxeterSystem τ) K w) =
      heckeDeg _ (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).simple i * w))
    rw [← canonicalRep_simple (coxeterSystem τ) K i, heckeDeg_canonicalRep,
      heckeDeg_canonicalRep, heckeDeg_canonicalRep, h, (coxeterSystem τ).length_simple,
      ← pow_add, add_comm]
  cover g := by
    obtain ⟨w₁, hw₁⟩ := hw
    obtain ⟨l, hl, w, h, hh, u, hu, e⟩ := cover_amb hw₁ g.2
    refine ⟨⟨l, negUnipotent_le_adjointGroup' hl⟩, hl, w,
      ⟨h, (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K |>.1
        (Subgroup.mem_sup_left hh)⟩, hh, ⟨u, posUnipotent_le_adjointGroup hu⟩, hu,
      Subtype.ext e⟩

end CFSG.Quasithin.SmithCurtis.Chev
