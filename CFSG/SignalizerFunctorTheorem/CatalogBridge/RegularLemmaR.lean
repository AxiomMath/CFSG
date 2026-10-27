module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Assembly

public noncomputable section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem hasCoord_conj_rootDiagUnit
    {i : Fin τ.rank} {y : ModGL τ K} {c : K}
    (h : HasCoord i y c) (a : Fin τ.rank → Kˣ)
    (ht : rootDiagUnit τ a ∈ torusGroup τ K) :
    HasCoord i (rootDiagUnit τ a * y * (rootDiagUnit τ a)⁻¹) ((a i : K) * c) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨rootDiagUnit τ a * b * (rootDiagUnit τ a)⁻¹, torus_conj_mem_rootSpan ht
    (fun α hα => hα.1) hb, ?_⟩
  have h1 := (root_diagonal_conjugation τ K a).1 i c
  calc rootDiagUnit τ a * (xUnit τ K i c * b) * (rootDiagUnit τ a)⁻¹
      = (rootDiagUnit τ a * xUnit τ K i c * (rootDiagUnit τ a)⁻¹) *
          (rootDiagUnit τ a * b * (rootDiagUnit τ a)⁻¹) := by group
    _ = xUnit τ K i ((a i : K) * c) * (rootDiagUnit τ a * b * (rootDiagUnit τ a)⁻¹) := by
        rw [h1]

theorem hasCoord_pinnedX_of_ne
    {i : Fin τ.rank} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hpos : 0 < height β) (hne : β ≠ Pi.single i 1) (c : K) :
    HasCoord i (pinnedX τ K β c) 0 :=
  ⟨pinnedX τ K β c, pinnedX_mem_rootSpan (S := simpleComplement τ i) ⟨hβ, hpos, hne⟩ c, by
    rw [xUnit_zero, one_mul]⟩

theorem hasCoord_pinnedX_single
    (i : Fin τ.rank) (c : K) :
    HasCoord i (pinnedX τ K (Pi.single i 1) c) c := by
  rw [pinnedX_single]
  exact hasCoord_xUnit i c

theorem hasCoord_list_prod_xUnit_one
    (l : List (Fin τ.rank)) (i : Fin τ.rank) :
    HasCoord i (l.map fun j => xUnit τ K j 1).prod (l.count i : K) := by
  induction l with
  | nil =>
    refine ⟨1, one_mem _, ?_⟩
    simp [xUnit_zero]
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hji : j = i
    · subst hji
      have h := (hasCoord_xUnit (τ := τ) (K := K) j 1).mul ih
      rw [List.count_cons_self]
      push_cast
      rwa [add_comm] at h
    · have h0 : HasCoord i (xUnit τ K j 1) 0 := by
        rw [← pinnedX_single]
        exact hasCoord_pinnedX_of_ne (isRoot_single τ j) (by rw [height_single]; exact one_pos)
          (fun h => hji (by
            by_contra hne
            have := congrFun h j
            simp [hne] at this)) 1
      have h := h0.mul ih
      rw [zero_add] at h
      rwa [List.count_cons_of_ne (fun h => hji h)]

theorem mem_borelGroup_of_conj_regular
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    {y : Fin τ.rank → ModGL τ K} (hyU : ∀ i, y i ∈ posUnipotent τ K) {c : Fin τ.rank → K}
    (hc : ∀ i, c i ≠ 0) (hco : ∀ i, HasCoord i (y i) (c i))
    (h : ∀ i, g⁻¹ * y i * g ∈ posUnipotent τ K) : g ∈ borelGroup τ K := by
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
    have hyU' : b⁻¹ * y i * b ∈ posUnipotent τ K := by
      simpa using conj_mem_posUnipotent_of_mem_borel (inv_mem hb) (hyU i)
    have hb2 : b ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) := by
      rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1]
      exact hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hb2
    have hcoord1 : HasCoord i (u⁻¹ * y i * u) (c i) := (hco i).conj_posUnipotent hu
    obtain ⟨s, hs, hcoord2⟩ := hcoord1.conj_torus (inv_mem ht)
    have hy : (u * t)⁻¹ * y i * (u * t) = t⁻¹ * (u⁻¹ * y i * u) * t⁻¹⁻¹ := by group
    have hconj : n⁻¹ * ((u * t)⁻¹ * y i * (u * t)) * n ∈ posUnipotent τ K := by
      have h1 := conj_mem_posUnipotent_of_mem_borel hb' (h i)
      have h2 : b' * ((u * t * n * b')⁻¹ * y i * (u * t * n * b')) * b'⁻¹ =
          n⁻¹ * ((u * t)⁻¹ * y i * (u * t)) * n := by group
      rwa [h2] at h1
    have hyU'' : t⁻¹ * (u⁻¹ * y i * u) * t⁻¹⁻¹ ∈ posUnipotent τ K := by
      rw [← hy]
      exact hyU'
    rw [hy] at hconj
    have hpos := pos_of_coord_of_conj_mem (mul_ne_zero hs (hc i)) hcoord2 hyU'' hconj
    have := hneg
    omega

theorem eq_bot_of_isPGroup_of_normalized_regular
    [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    {J W : Subgroup (ModGL τ K)} (hJC : J ≤ adjointGroup τ K) (hWC : W ≤ adjointGroup τ K)
    (hWr : IsPGroup r W) {y : Fin τ.rank → ModGL τ K} (hyJ : ∀ i, y i ∈ J)
    (hyU : ∀ i, y i ∈ posUnipotent τ K) {c : Fin τ.rank → K} (hc : ∀ i, c i ≠ 0)
    (hco : ∀ i, HasCoord i (y i) (c i)) {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hJn : canonicalRep (coxeterSystem τ) K w₀ ∈ J)
    (hnorm : ∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W) : W = ⊥ := by
  set U₀ : Subgroup (ModGL τ K) := Subgroup.closure (Set.range y) with hU₀
  have hU₀J : U₀ ≤ J := (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hyJ i)
  have hU₀U : U₀ ≤ posUnipotent τ K :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hyU i)
  have hU₀r : IsPGroup r U₀ := IsPGroup.to_le (isPGroup_posUnipotent r) hU₀U
  have hnormW : U₀ ≤ Subgroup.normalizer (W : Set (ModGL τ K)) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm j (hU₀J hj) x hx, fun hx => ?_⟩
    have := hnorm j⁻¹ (inv_mem (hU₀J hj)) _ hx
    simpa [mul_assoc] using this
  have hPr : IsPGroup r (W ⊔ U₀ : Subgroup (ModGL τ K)) := hWr.to_sup_of_normal_left' hU₀r hnormW
  have hPC : (W ⊔ U₀ : Subgroup (ModGL τ K)) ≤ adjointGroup τ K :=
    sup_le hWC (hU₀J.trans hJC)
  obtain ⟨g, hgC, hg⟩ := exists_conj_le_posUnipotent r hPC hPr
  have hgB : g ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_regular hgC hyU hc hco fun i => hg _ ?_
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, rfl⟩)
  have hWU : ∀ x ∈ W, x ∈ posUnipotent τ K := by
    intro x hx
    have h1 := hg x (Subgroup.mem_sup_left hx)
    have h2 := conj_mem_posUnipotent_of_mem_borel hgB h1
    simpa [mul_assoc] using h2
  have hVmap := map_conj_canonicalRep_longest (τ := τ) (K := K) hw₀
  have hWV : ∀ x ∈ W, x ∈ negUnipotent τ K := by
    intro x hx
    have hx' : (canonicalRep (coxeterSystem τ) K w₀)⁻¹ * x * canonicalRep (coxeterSystem τ) K w₀ ∈
        W := by
      simpa using hnorm _ (inv_mem hJn) x hx
    have h1 := hWU _ hx'
    rw [← hVmap]
    refine ⟨_, h1, ?_⟩
    simp [MulAut.conj_apply]
    group
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ posUnipotent τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2 ⟨hWU x hx, hWV x hx⟩
  rwa [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent] at hmem

theorem eq_one_of_commute_regular
    [Finite K] {x : ModGL τ K} (hxC : x ∈ adjointGroup τ K)
    {y : Fin τ.rank → ModGL τ K} (hyU : ∀ i, y i ∈ posUnipotent τ K) {c : Fin τ.rank → K}
    (hc : ∀ i, c i ≠ 0) (hco : ∀ i, HasCoord i (y i) (c i)) {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hs : ∀ i, x * y i = y i * x)
    (hn : x * canonicalRep (coxeterSystem τ) K w₀ = canonicalRep (coxeterSystem τ) K w₀ * x) :
    x = 1 := by
  have hxB : x ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_regular hxC hyU hc hco fun i => ?_
    have : x⁻¹ * y i * x = y i := by
      rw [mul_assoc, ← hs i]
      group
    rw [this]
    exact hyU i
  set n := canonicalRep (coxeterSystem τ) K w₀ with hnn
  have hxn : x = n * x * n⁻¹ := by rw [← hn]; group
  have hB : x ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1]
    exact hxB
  obtain ⟨t, ht, u, hu, hxtu⟩ := hB
  have hT : n * t * n⁻¹ ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 ((canonical_weyl_root_transport τ K).2.2 w₀) t).1 ht
  have hV : n * u * n⁻¹ ∈ negUnipotent τ K := by
    rw [← map_conj_canonicalRep_longest (τ := τ) (K := K) hw₀]
    exact ⟨u, hu, rfl⟩
  have hx2 : x = (n * t * n⁻¹) * (n * u * n⁻¹) := by
    calc x = n * x * n⁻¹ := hxn
      _ = n * (t * u) * n⁻¹ := by simp only [] at hxtu; rw [hxtu]
      _ = (n * t * n⁻¹) * (n * u * n⁻¹) := by group
  have hv : (n * t * n⁻¹)⁻¹ * x ∈ borelGroup τ K ⊓ negUnipotent τ K := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (torusGroup_le_borelGroup hT)) hxB, ?_⟩
    have : (n * t * n⁻¹)⁻¹ * x = n * u * n⁻¹ := by rw [hx2]; group
    rw [this]
    exact hV
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, inv_mul_eq_one] at hv
  have hxT : x ∈ torusGroup τ K := by
    rw [← hv]
    exact hT
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
  have ha : ∀ i, (a i : K) = 1 := by
    intro i
    have h1 := hasCoord_conj_rootDiagUnit (hco i) a hxT
    have h2 : rootDiagUnit τ a * y i * (rootDiagUnit τ a)⁻¹ = y i := by
      rw [hs i]
      group
    rw [h2] at h1
    have h3 := HasCoord.unique (hco i) h1
    exact (mul_eq_right₀ (hc i)).mp h3.symm
  have : a = 1 := funext fun i => Units.ext (ha i)
  rw [this, rootDiagUnit_one]

theorem nonLocalized_of_regular_data
    [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    {X J : Subgroup (ModGL τ K)} (hXC : X ≤ adjointGroup τ K) (hJX : J ≤ X)
    (hJs : IsSimpleGroup ↥(J.subgroupOf X)) {y : Fin τ.rank → ModGL τ K}
    (hyJ : ∀ i, y i ∈ J) (hyU : ∀ i, y i ∈ posUnipotent τ K) {c : Fin τ.rank → K}
    (hc : ∀ i, c i ≠ 0) (hco : ∀ i, HasCoord i (y i) (c i)) {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hJn : canonicalRep (coxeterSystem τ) K w₀ ∈ J)
    {F W : Type*} [Field F] [IsAlgClosed F] [CharP F r] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (ρ : ↥X →* Module.End F W) (hρ : Function.Injective ρ)
    (R : Subgroup ↥X) (hRJ : R ≤ J.subgroupOf X)
    (hR : ¬ Nat.card R ∣ (Module.finrank F W).factorial) :
    NonLocalized (J.subgroupOf X) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite ↥X := Subtype.finite
  have hcent : ∀ x : ↥X, (∀ j ∈ J.subgroupOf X, x * j = j * x) → x = 1 := by
    intro x hx
    refine Subtype.ext (eq_one_of_commute_regular (hXC x.2) hyU hc hco hw₀ (fun i => ?_) ?_)
    · have := hx ⟨y i, hJX (hyJ i)⟩ (Subgroup.mem_subgroupOf.2 (hyJ i))
      exact congrArg Subtype.val this
    · have := hx ⟨canonicalRep (coxeterSystem τ) K w₀, hJX hJn⟩ (Subgroup.mem_subgroupOf.2 hJn)
      exact congrArg Subtype.val this
  have hrsub : ∀ E : Subgroup ↥X, IsPGroup r E →
      (∀ j ∈ J.subgroupOf X, ∀ e ∈ E, j * e * j⁻¹ ∈ E) → E = ⊥ := by
    intro E hEr hEn
    have hWr : IsPGroup r (E.map X.subtype) := hEr.map _
    have hWC : E.map X.subtype ≤ adjointGroup τ K := by
      rintro _ ⟨e, -, rfl⟩
      exact hXC e.2
    have hbot := eq_bot_of_isPGroup_of_normalized_regular r (hJX.trans hXC) hWC hWr hyJ hyU hc hco
      hw₀ hJn (fun j hj w hw => by
        obtain ⟨e, he, rfl⟩ := hw
        have := hEn ⟨j, hJX hj⟩ (Subgroup.mem_subgroupOf.2 hj) e he
        exact ⟨_, this, rfl⟩)
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hbot
  exact nonLocalized_of_perm_data hJs hcent (Fact.out : r.Prime) hrsub ρ hρ R hRJ hR

end CFSG.SignalizerFunctorTheorem.CatalogBridge
