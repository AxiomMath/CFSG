module

public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.Quasithin.Background.SmithCurtisHecke
public import CFSG.LieType.Chevalley.SimpleRootSubgroups

public section

namespace CFSG.Quasithin.SmithCurtis.Chev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def negComplement
    (i : Fin τ.rank) : Subgroup (ModGL τ K) :=
  rootSpan τ K {γ | IsRoot τ γ ∧ height γ < 0 ∧ γ ≠ -Pi.single i 1}

theorem mem_rootSubgroup_single
    {i : Fin τ.rank} {g : ModGL τ K} :
    g ∈ rootSubgroup τ K (Pi.single i 1) ↔ ∃ c : K, xUnit τ K i c = g := by
  rw [mem_rootSubgroup]
  simp only [pinnedX_single]

theorem mem_rootSubgroup_neg_single
    {i : Fin τ.rank} {g : ModGL τ K} :
    g ∈ rootSubgroup τ K (-Pi.single i 1) ↔ ∃ c : K, yUnit τ K i c = g := by
  rw [mem_rootSubgroup]
  simp only [pinnedX_neg_single]

theorem height_neg_single (i : Fin τ.rank) : height (-Pi.single i 1 : Fin τ.rank → ℤ) = -1 := by
  rw [height_neg, height_single]

theorem rootSubgroup_le_posUnipotent'
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) : rootSubgroup τ K α ≤ posUnipotent τ K :=
  le_iSup₂_of_le α ⟨hα, hpos⟩ le_rfl

theorem rootSubgroup_le_negUnipotent'
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hneg : height α < 0) : rootSubgroup τ K α ≤ negUnipotent τ K :=
  le_iSup₂_of_le α ⟨hα, hneg⟩ le_rfl

theorem rootSubgroup_single_le
    (i : Fin τ.rank) :
    rootSubgroup τ K (Pi.single i 1) ≤ posUnipotent τ K :=
  rootSubgroup_le_posUnipotent' (isRoot_single τ i) (by rw [height_single]; exact one_pos)

theorem rootSubgroup_neg_single_le
    (i : Fin τ.rank) :
    rootSubgroup τ K (-Pi.single i 1) ≤ negUnipotent τ K :=
  rootSubgroup_le_negUnipotent' (isRoot_neg_single τ i) (by rw [height_neg_single]; omega)

theorem posComplement_le
    (i : Fin τ.rank) : posComplement τ K i ≤ posUnipotent τ K :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl

theorem negComplement_le
    (i : Fin τ.rank) : negComplement τ K i ≤ negUnipotent τ K :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl

theorem xUnit_mem_rootSubgroup
    (i : Fin τ.rank) (c : K) :
    xUnit τ K i c ∈ rootSubgroup τ K (Pi.single i 1) :=
  mem_rootSubgroup_single.mpr ⟨c, rfl⟩

theorem yUnit_mem_rootSubgroup
    (i : Fin τ.rank) (c : K) :
    yUnit τ K i c ∈ rootSubgroup τ K (-Pi.single i 1) :=
  mem_rootSubgroup_neg_single.mpr ⟨c, rfl⟩

theorem xUnit_injective
    (i : Fin τ.rank) : Function.Injective (xUnit τ K i) :=
  fun _ _ h => xOp_injective i (congrArg Units.val h)

theorem rootSpan_singleton
    (α : Fin τ.rank → ℤ) :
    rootSpan τ K {α} = rootSubgroup τ K α := by
  simp [rootSpan]

theorem torusGroup_le_normalizer_rootSpan
    (S : Set (Fin τ.rank → ℤ))
    (hS : ∀ α ∈ S, IsRoot τ α) :
    torusGroup τ K ≤ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_conj_image_eq]
  have h : (rootSpan τ K S).map (MulAut.conj (torusElt τ K i s)).toMonoidHom = rootSpan τ K S := by
    simp only [rootSpan, Subgroup.map_iSup]
    exact iSup_congr fun α => iSup_congr fun hα => map_conj_torusElt_rootSubgroup i s (hS α hα)
  have h' := congrArg SetLike.coe h
  rw [Subgroup.coe_map] at h'
  exact h'

theorem torus_conj_mem_rootSpan
    {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {h : ModGL τ K} (hh : h ∈ torusGroup τ K) {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K S) : h * g * h⁻¹ ∈ rootSpan τ K S :=
  (Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_rootSpan S hS hh) g).mp hg

theorem weylElt_conj_xUnit
    (i : Fin τ.rank) (c : K) :
    weylElt τ K i 1 * xUnit τ K i c * (weylElt τ K i 1)⁻¹ = yUnit τ K i (-c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_xUnit, weylElt_mul_xOp_mul_inv, coe_yUnit]
  simp

theorem weylElt_conj_yUnit
    (i : Fin τ.rank) (c : K) :
    weylElt τ K i 1 * yUnit τ K i c * (weylElt τ K i 1)⁻¹ = xUnit τ K i (-c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_yUnit, weylElt_mul_yOp_mul_inv, coe_xUnit]
  simp

theorem weylElt_inv_conj_yUnit
    (i : Fin τ.rank) (c : K) :
    (weylElt τ K i 1)⁻¹ * yUnit τ K i c * weylElt τ K i 1 = xUnit τ K i (-c) := by
  have e : (weylElt τ K i 1)⁻¹ = weylElt τ K i (-1) := weylElt_inv i 1
  refine Units.ext ?_
  have h := weylElt_mul_yOp_mul_inv (τ := τ) i (-1 : Kˣ) c
  rw [e, Units.val_mul, Units.val_mul, coe_yUnit, coe_xUnit]
  rw [show weylElt τ K i 1 = (weylElt τ K i (-1))⁻¹ by rw [← e, inv_inv]]
  rw [h]
  simp

theorem weylElt_inv_conj_xUnit
    (i : Fin τ.rank) (c : K) :
    (weylElt τ K i 1)⁻¹ * xUnit τ K i c * weylElt τ K i 1 = yUnit τ K i (-c) := by
  have e : (weylElt τ K i 1)⁻¹ = weylElt τ K i (-1) := weylElt_inv i 1
  refine Units.ext ?_
  have h := weylElt_mul_xOp_mul_inv (τ := τ) i (-1 : Kˣ) c
  rw [e, Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit]
  rw [show weylElt τ K i 1 = (weylElt τ K i (-1))⁻¹ by rw [← e, inv_inv]]
  rw [h]
  simp

theorem weylElt_mem_normalizer_torus'
    (i : Fin τ.rank) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : weylElt τ K i 1 * h * (weylElt τ K i 1)⁻¹ ∈ torusGroup τ K :=
  (Subgroup.mem_normalizer_iff.mp (weylElt_mem_normalizer_torus τ K i 1) h).mp hh

theorem weylElt_sq_mem_torus
    (i : Fin τ.rank) :
    weylElt τ K i 1 * weylElt τ K i 1 ∈ torusGroup τ K := by
  rw [weylElt_one_mul_self]
  exact torusElt_mem_torusGroup i (-1)

theorem xUnit_mul_weylElt
    (i : Fin τ.rank) (c : Kˣ) :
    xUnit τ K i c * weylElt τ K i 1 = yUnit τ K i ((c⁻¹ : Kˣ) : K) *
      (torusElt τ K i c * (weylElt τ K i 1 * weylElt τ K i 1)) *
      ((weylElt τ K i 1)⁻¹ * yUnit τ K i ((c⁻¹ : Kˣ) : K) * weylElt τ K i 1) := by
  have hx : xUnit τ K i c = yUnit τ K i ((c⁻¹ : Kˣ) : K) * weylElt τ K i c *
      yUnit τ K i ((c⁻¹ : Kˣ) : K) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit, coe_weylElt_eq_yOp_mul, ← mul_assoc,
      ← mul_assoc, yOp_mul_yOp_neg (downTransport τ), one_mul, mul_assoc,
      yOp_neg_mul_yOp (downTransport τ), mul_one]
  rw [hx, weylElt_eq_torusElt_mul_weylElt_one]
  group

theorem weylElt_mul_xUnit_mul_weylElt
    (i : Fin τ.rank) (c : Kˣ) :
    weylElt τ K i 1 * xUnit τ K i c * weylElt τ K i 1 =
      xUnit τ K i (-((c⁻¹ : Kˣ) : K)) * weylElt τ K i 1 *
        ((weylElt τ K i 1)⁻¹ * torusElt τ K i (-c⁻¹) * weylElt τ K i 1) *
        ((weylElt τ K i 1)⁻¹ * yUnit τ K i ((c⁻¹ : Kˣ) : K) * weylElt τ K i 1) := by
  rw [weylElt_one_mul_xUnit]
  group

theorem yUnit_eq
    (i : Fin τ.rank) (c : Kˣ) :
    ∃ h ∈ torusGroup τ K, ∃ a ∈ rootSubgroup τ K (Pi.single i 1),
      ∃ b ∈ rootSubgroup τ K (Pi.single i 1),
        yUnit τ K i c = a * (h * weylElt τ K i 1) * b := by
  have e := weylElt_one_mul_xUnit (τ := τ) (R := K) i c⁻¹
  rw [inv_inv] at e
  have hd : torusElt τ K i (-c) ∈ torusGroup τ K := torusElt_mem_torusGroup i _
  refine ⟨(torusElt τ K i (-c))⁻¹, inv_mem hd,
    (torusElt τ K i (-c))⁻¹ * xUnit τ K i c * ((torusElt τ K i (-c))⁻¹)⁻¹, ?_,
    xUnit τ K i ((c⁻¹ : Kˣ) : K), xUnit_mem_rootSubgroup i _, ?_⟩
  · rw [← rootSpan_singleton]
    refine torus_conj_mem_rootSpan (by simp [isRoot_single]) (inv_mem hd) ?_
    rw [rootSpan_singleton]
    exact xUnit_mem_rootSubgroup i _
  · have e2 : yUnit τ K i c = (xUnit τ K i (-(c : K)) * torusElt τ K i (-c))⁻¹ *
        (weylElt τ K i 1 * xUnit τ K i ((c⁻¹ : Kˣ) : K)) := by
      rw [e]
      group
    rw [e2, mul_inv_rev, ← xUnit_neg, neg_neg]
    group

theorem isRoot_neg {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : IsRoot τ (-v) :=
  CFSG.LieType.Chevalley.IsRoot.neg hv

theorem reflect_neg' (i : Fin τ.rank) (u : Fin τ.rank → ℤ) :
    reflect τ i (-u) = -reflect τ i u := by
  ext j
  simp only [reflect, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib]
  ring

theorem reflect_image_negComplementRoots
    (i : Fin τ.rank) :
    reflect τ i '' {γ | IsRoot τ γ ∧ height γ < 0 ∧ γ ≠ -Pi.single i 1} =
      {γ | IsRoot τ γ ∧ height γ < 0 ∧ γ ≠ -Pi.single i 1} := by
  have hb := bijOn_reflect (τ := τ) i
  ext γ
  constructor
  · rintro ⟨β, ⟨hβ, hneg, hne⟩, rfl⟩
    have h1 := hb.mapsTo (show -β ∈ {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} from
      ⟨isRoot_neg hβ, by rw [height_neg]; omega,
        fun h => hne (by rw [← neg_neg β, h])⟩)
    obtain ⟨h1r, h1p, h1n⟩ := h1
    rw [reflect_neg'] at h1r h1p h1n
    refine ⟨by simpa using isRoot_neg h1r, by rw [height_neg] at h1p; omega,
      fun h => h1n ?_⟩
    rw [h, neg_neg]
  · rintro ⟨hγ, hneg, hne⟩
    obtain ⟨β, ⟨hβ, hpos, hβne⟩, hβeq⟩ := hb.surjOn (show -γ ∈
      {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} from
      ⟨isRoot_neg hγ, by rw [height_neg]; omega,
        fun h => hne (by rw [← neg_neg γ, h])⟩)
    refine ⟨-β, ⟨isRoot_neg hβ, by rw [height_neg]; omega,
      fun h => hβne (by rw [← neg_neg β, h, neg_neg])⟩, ?_⟩
    rw [reflect_neg', hβeq, neg_neg]

theorem map_conj_weylElt_negComplement
    (i : Fin τ.rank) :
    (negComplement τ K i).map (MulAut.conj (weylElt τ K i 1)).toMonoidHom =
      negComplement τ K i := by
  rw [negComplement, map_conj_weylElt_rootSpan K i 1 fun γ hγ => hγ.1,
    reflect_image_negComplementRoots]

theorem weylElt_conj_negComplement
    (i : Fin τ.rank) {q : ModGL τ K}
    (hq : q ∈ negComplement τ K i) :
    weylElt τ K i 1 * q * (weylElt τ K i 1)⁻¹ ∈ negComplement τ K i := by
  rw [← map_conj_weylElt_negComplement i]
  exact ⟨q, hq, rfl⟩

theorem weylElt_inv_conj_negComplement
    (i : Fin τ.rank) {q : ModGL τ K}
    (hq : q ∈ negComplement τ K i) :
    (weylElt τ K i 1)⁻¹ * q * weylElt τ K i 1 ∈ negComplement τ K i := by
  rw [← map_conj_weylElt_negComplement i] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group
  exact hq'

section Opposite

variable {w₁ : WeylGroup τ} (hw₁ : ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
include hw₁

theorem image_smul_eq_neg (S : Set (Fin τ.rank → ℤ)) :
    (fun α => w₁ • α) '' S = {γ | -γ ∈ S} := by
  ext γ
  simp only [Set.mem_image, Set.mem_ofPred_eq, hw₁]
  constructor
  · rintro ⟨α, hα, rfl⟩
    rwa [neg_neg]
  · intro h
    exact ⟨-γ, h, neg_neg γ⟩

theorem map_conj_rootSpan_neg
    (S : Set (Fin τ.rank → ℤ)) (hS : ∀ α ∈ S, IsRoot τ α) :
    (rootSpan τ K S).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w₁)).toMonoidHom =
      rootSpan τ K {γ | -γ ∈ S} := by
  rw [(canonical_weyl_root_transport τ K).1 w₁ S hS, image_smul_eq_neg hw₁]

theorem map_conj_posUnipotent
    :
    (posUnipotent τ K).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w₁)).toMonoidHom =
      negUnipotent τ K := by
  rw [posUnipotent, map_conj_rootSpan_neg hw₁ _ fun α h => h.1, negUnipotent]
  congr 1
  ext γ
  simp only [Set.mem_ofPred_eq, height_neg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using isRoot_neg h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isRoot_neg h1, by omega⟩

theorem map_conj_posComplement
    (i : Fin τ.rank) :
    (posComplement τ K i).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w₁)).toMonoidHom =
      negComplement τ K i := by
  rw [posComplement, map_conj_rootSpan_neg hw₁ _ fun α h => h.1, negComplement]
  congr 1
  ext γ
  simp only [Set.mem_ofPred_eq, height_neg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simpa using isRoot_neg h1, by omega,
      fun h => h3 (by rw [h, neg_neg])⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨isRoot_neg h1, by omega, fun h => h3 (by rw [← neg_neg γ, h])⟩

theorem map_conj_rootSubgroup_single
    (i : Fin τ.rank) :
    (rootSubgroup τ K (Pi.single i 1)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w₁)).toMonoidHom =
      rootSubgroup τ K (-Pi.single i 1) := by
  rw [(canonical_weyl_root_transport τ K).2.1 w₁ _ (isRoot_single τ i), hw₁]

theorem negUnipotent_eq_mul
    (i : Fin τ.rank) {l : ModGL τ K}
    (hl : l ∈ negUnipotent τ K) : ∃ y ∈ rootSubgroup τ K (-Pi.single i 1),
      ∃ q ∈ negComplement τ K i, l = y * q := by
  rw [← map_conj_posUnipotent hw₁] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  have hU := (simple_positive_root_complement τ K i).2.2.1
  have hu' : u ∈ (rootSubgroup τ K (Pi.single i 1) : Set (ModGL τ K)) *
      (posComplement τ K i : Set (ModGL τ K)) := by
    rw [posComplement, ← hU]
    exact hu
  obtain ⟨x, hx, v, hv, rfl⟩ := hu'
  refine ⟨MulAut.conj (canonicalRep (coxeterSystem τ) K w₁) x, ?_,
    MulAut.conj (canonicalRep (coxeterSystem τ) K w₁) v, ?_, map_mul _ x v⟩
  · rw [← map_conj_rootSubgroup_single hw₁ i]
    exact ⟨x, hx, rfl⟩
  · rw [← map_conj_posComplement hw₁ i]
    exact ⟨v, hv, rfl⟩

theorem negComplement_normal
    (i : Fin τ.rank) {y q : ModGL τ K}
    (hy : y ∈ rootSubgroup τ K (-Pi.single i 1)) (hq : q ∈ negComplement τ K i) :
    y * q * y⁻¹ ∈ negComplement τ K i := by
  rw [← map_conj_rootSubgroup_single hw₁ i] at hy
  rw [← map_conj_posComplement hw₁ i] at hq ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨v, hv, rfl⟩ := hq
  have hnorm := (simple_positive_root_complement τ K i).2.1
  have hxv : x * v * x⁻¹ ∈ posComplement τ K i := by
    have hn := (Subgroup.normal_subgroupOf_iff (posComplement_le i)).1 hnorm
    exact hn v x hv (rootSubgroup_single_le i hx)
  exact ⟨x * v * x⁻¹, hxv, by simp only [map_mul, map_inv]⟩

theorem xUnit_conj_negComplement
    (i : Fin τ.rank) {x q : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K (Pi.single i 1)) (hq : q ∈ negComplement τ K i) :
    x * q * x⁻¹ ∈ negComplement τ K i := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup_single.mp hx
  set n := weylElt τ K i 1
  have hy : n⁻¹ * xUnit τ K i c * n ∈ rootSubgroup τ K (-Pi.single i 1) := by
    rw [weylElt_inv_conj_xUnit]
    exact yUnit_mem_rootSubgroup i _
  have e : xUnit τ K i c * q * (xUnit τ K i c)⁻¹ =
      n * ((n⁻¹ * xUnit τ K i c * n) * (n⁻¹ * q * n) * (n⁻¹ * xUnit τ K i c * n)⁻¹) * n⁻¹ := by
    group
  rw [e]
  exact weylElt_conj_negComplement i (negComplement_normal hw₁ i hy
    (weylElt_inv_conj_negComplement i hq))

theorem cover_amb
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    ∃ l ∈ negUnipotent τ K, ∃ w : WeylGroup τ, ∃ h ∈ torusGroup τ K, ∃ u ∈ posUnipotent τ K,
      g = l * canonicalRep (coxeterSystem τ) K w * (h * u) := by
  set n₁ := canonicalRep (coxeterSystem τ) K w₁
  have hn₁ : n₁ ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w₁
  have hg' : n₁⁻¹ * g ∈ (adjointGroup τ K : Set (ModGL τ K)) := mul_mem (inv_mem hn₁) hg
  rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hv
  obtain ⟨-, -, hHnorm, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ K
  have hb2 : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hHU]
    exact hb
  have hb'2 : b' ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hHU]
    exact hb'
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := hb2
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb'2
  obtain ⟨k, hk, hkn⟩ := canonicalRep_mul_mem (R := K) w₁ v
  have hnorm := (canonical_weyl_root_transport τ K).2.2
  set H₀ := n₁ * h₀ * n₁⁻¹
  have hH₀ : H₀ ∈ torusGroup τ K := (Subgroup.mem_normalizer_iff.mp (hnorm w₁) h₀).mp hh₀
  set L₀ := n₁ * u₀ * n₁⁻¹
  have hL₀ : L₀ ∈ negUnipotent τ K := by
    rw [← map_conj_posUnipotent hw₁]
    exact ⟨u₀, hu₀, rfl⟩
  set n' := canonicalRep (coxeterSystem τ) K (w₁ * v)
  have hHk : n'⁻¹ * (H₀ * k) * n' ∈ torusGroup τ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hnorm (w₁ * v)) (H₀ * k)).mp (mul_mem hH₀ hk)
    have e : n'⁻¹ * (H₀ * k) * n' = n'⁻¹ * (H₀ * k) * n'⁻¹⁻¹ := by rw [inv_inv]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem (hnorm (w₁ * v))) (H₀ * k)).mp
      (mul_mem hH₀ hk)
  have hl : H₀ * L₀ * H₀⁻¹ ∈ negUnipotent τ K :=
    (Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_negUnipotent hH₀) L₀).mp hL₀
  refine ⟨H₀ * L₀ * H₀⁻¹, hl, w₁ * v, n'⁻¹ * (H₀ * k) * n' * h₁, mul_mem hHk hh₁, u₁, hu₁, ?_⟩
  have hg2 : g = n₁ * (h₀ * u₀ * canonicalRep (coxeterSystem τ) K v * (h₁ * u₁)) := by
    rw [hbb]
    group
  have e1 : n₁ * canonicalRep (coxeterSystem τ) K v = k * n' := hkn
  rw [hg2]
  have e2 : n₁ * (h₀ * u₀ * canonicalRep (coxeterSystem τ) K v * (h₁ * u₁)) =
      H₀ * L₀ * (n₁ * canonicalRep (coxeterSystem τ) K v) * (h₁ * u₁) := by
    simp only [H₀, L₀]
    group
  rw [e2, e1, show canonicalRep (coxeterSystem τ) K (w₁ * v) = n' from rfl]
  group

end Opposite

theorem canonicalRep_inv_conj_mem
    {w : WeylGroup τ} {i : Fin τ.rank}
    (h : (coxeterSystem τ).length ((coxeterSystem τ).simple i * w) =
      (coxeterSystem τ).length w + 1)
    {x : ModGL τ K} (hx : x ∈ rootSubgroup τ K (Pi.single i 1)) :
    (canonicalRep (coxeterSystem τ) K w)⁻¹ * x * canonicalRep (coxeterSystem τ) K w ∈
      posUnipotent τ K := by
  set β : Fin τ.rank → ℤ := w⁻¹ • Pi.single i 1
  have hβ : IsRoot τ β := IsRoot.smul (isRoot_single τ i) w⁻¹
  have hnd : ¬ (coxeterSystem τ).IsRightDescent w⁻¹ i := by
    rw [not_isRightDescent_iff_length]
    have e : w⁻¹ * simple τ i = ((coxeterSystem τ).simple i * w)⁻¹ := by
      rw [mul_inv_rev, (coxeterSystem τ).inv_simple]
    rw [e, (coxeterSystem τ).length_inv, (coxeterSystem τ).length_inv]
    exact h
  have hpos : 0 < height β :=
    ((mem_posRoots_iff_not_mem_negRoots hβ).2 fun hm =>
      hnd ((smul_single_mem_negRoots_iff w⁻¹ i).1 hm)).2
  have hmap := (canonical_weyl_root_transport τ K).2.1 w β hβ
  have hwβ : w • β = Pi.single i 1 := by simp [β]
  rw [hwβ] at hmap
  rw [← hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group
  exact rootSubgroup_le_posUnipotent' hβ hpos hy

theorem map_conj_posUnipotent_inf
    (w : WeylGroup τ) :
    (posUnipotent τ K).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom ⊓
        posUnipotent τ K =
      (rootSpan τ K (nonInversionSet w)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom := by
  set n := canonicalRep (coxeterSystem τ) K w
  apply le_antisymm
  · rintro x ⟨⟨u, hu, rfl⟩, hxU⟩
    have hu' : u ∈ (posUnipotent τ K : Set (ModGL τ K)) := hu
    rw [posUnipotent_eq_mul_rootSpan w] at hu'
    obtain ⟨uJ, huJ, uI, huI, rfl⟩ := hu'
    have ha : n * uJ * n⁻¹ ∈ posUnipotent τ K := canonicalRep_conj_mem_posUnipotent huJ
    have hb : n * uI * n⁻¹ ∈ negUnipotent τ K := canonicalRep_conj_mem_negUnipotent huI
    have hxU' : n * (uJ * uI) * n⁻¹ ∈ posUnipotent τ K := hxU
    have hbU : n * uI * n⁻¹ ∈ posUnipotent τ K := by
      have e : n * uI * n⁻¹ = (n * uJ * n⁻¹)⁻¹ * (n * (uJ * uI) * n⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem ha) hxU'
    have h1 : n * uI * n⁻¹ ∈ posUnipotent τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2 ⟨hbU, hb⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h1
    have huI1 : uI = 1 := by
      have e : uI = n⁻¹ * (n * uI * n⁻¹) * n := by group
      rw [e, h1]
      group
    refine ⟨uJ, huJ, ?_⟩
    simp only [huI1, mul_one]
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, rootSpan_le_posUnipotent (fun α h => nonInversionSet_pos (w := w) h) hu, rfl⟩,
      canonicalRep_conj_mem_posUnipotent hu⟩

theorem ncard_nonInversionSet_add
    (w : WeylGroup τ) :
    (nonInversionSet w).ncard + (coxeterSystem τ).length w =
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  rw [(weyl_inversion_length τ).1 w]
  have hfin : ∀ S : Set (Fin τ.rank → ℤ), (∀ α ∈ S, IsRoot τ α) → S.Finite :=
    fun S hS => (finite_setOf_isRoot τ).subset hS
  rw [← Set.ncard_union_eq _ (hfin _ fun α h => h.1) (hfin _ fun α h => h.1)]
  · congr 1
    ext α
    simp only [nonInversionSet, inversionSet, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases IsRoot.height_pos_or_neg (IsRoot.smul h1 w) with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, IsRoot.smul h1 w, h⟩
  · rw [Set.disjoint_left]
    rintro α ⟨-, -, h⟩ ⟨-, -, -, h'⟩
    omega

theorem heckeDeg_canonicalRep
    [Finite K] (w : WeylGroup τ) :
    heckeDeg (posUnipotent τ K) (canonicalRep (coxeterSystem τ) K w) =
      Nat.card K ^ (coxeterSystem τ).length w := by
  set n := canonicalRep (coxeterSystem τ) K w
  have h := Subgroup.relIndex_mul_card
    ((posUnipotent τ K).map (MulAut.conj n).toMonoidHom) (posUnipotent τ K)
  rw [map_conj_posUnipotent_inf, Subgroup.card_map_of_injective (MulAut.conj n).injective,
    card_rootSpan (fun α h => nonInversionSet_pos (w := w) h) (nonInversionSet_closed w),
    card_posUnipotent, ← ncard_nonInversionSet_add w, pow_add, mul_comm] at h
  have hq : 0 < Nat.card K ^ (nonInversionSet w).ncard := pow_pos Nat.card_pos _
  rw [heckeDeg]
  exact Nat.eq_of_mul_eq_mul_left hq h.symm |>.symm

end CFSG.Quasithin.SmithCurtis.Chev
