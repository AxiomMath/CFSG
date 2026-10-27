module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveOverlap

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {G : Type} [Group G]

private theorem finrank_top_five (k : ℕ) :
    Module.finrank (ZMod 5) (⊤ : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) = k + 1 := by
  simp [finrank_top]

private theorem fiveForm_sub_smul (k : ℕ) (ε : Bool)
    (x y : Fin (k + 1) → ZMod 5) (t : ZMod 5) :
    fiveForm k ε (x - t • y) (x - t • y) =
      fiveForm k ε x x - t * fiveForm k ε x y - t * fiveForm k ε y x +
        t ^ 2 * fiveForm k ε y y := by
  rw [fiveForm_sub_left, fiveForm_sub_right, fiveForm_smul_left, fiveForm_smul_right,
    fiveForm_sub_right, fiveForm_smul_right]
  ring

private theorem finrank_span_singleton_le_one {k : ℕ} (v : Fin (k + 1) → ZMod 5) :
    Module.finrank (ZMod 5) (Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5))) ≤ 1 :=
  finrank_le_one ⟨v, Submodule.mem_span_singleton_self v⟩ (by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨c, Subtype.ext hc⟩)

private theorem finrank_span_pair_le_two {k : ℕ} (v w : Fin (k + 1) → ZMod 5) :
    Module.finrank (ZMod 5)
      (Submodule.span (ZMod 5) ({v, w} : Set (Fin (k + 1) → ZMod 5))) ≤ 2 := by
  have h := finrank_span_le_card (R := ZMod 5) ({v, w} : Set (Fin (k + 1) → ZMod 5))
  have hc : ({v, w} : Set (Fin (k + 1) → ZMod 5)).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  omega

private theorem finrank_sup_span_le_two {k : ℕ} (v w : Fin (k + 1) → ZMod 5) :
    Module.finrank (ZMod 5) ↥(Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
      Submodule.span (ZMod 5) ({w} : Set (Fin (k + 1) → ZMod 5))) ≤ 2 := by
  have h : Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
      Submodule.span (ZMod 5) ({w} : Set (Fin (k + 1) → ZMod 5)) =
      Submodule.span (ZMod 5) ({v, w} : Set (Fin (k + 1) → ZMod 5)) := by
    rw [← Submodule.span_union]
    rfl
  rw [h]
  exact finrank_span_pair_le_two v w

private theorem le_finrank_fiveOrth_singleton {k : ℕ} {ε : Bool} (v : Fin (k + 1) → ZMod 5) :
    k ≤ Module.finrank (ZMod 5)
      ↥(fiveOrth k ε (Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)))) := by
  have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := ⊤)
    (U := Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)))
    (isFiveNondeg_top k ε) le_top
  rw [top_inf_eq, finrank_top_five] at h
  have hvle := finrank_span_singleton_le_one v
  omega

private theorem exists_fiveForm_eq_of_orth_sup {k : ℕ} {ε : Bool} (hk : 4 ≤ k)
    {v w : Fin (k + 1) → ZMod 5} (hv : fiveForm k ε v v ≠ 0)
    {c : ZMod 5} :
    ∃ y ∈ fiveOrth k ε (Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
      Submodule.span (ZMod 5) ({w} : Set (Fin (k + 1) → ZMod 5))), fiveForm k ε y y = c := by
  set Q := Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
    Submodule.span (ZMod 5) ({w} : Set (Fin (k + 1) → ZMod 5)) with hQdef
  by_cases hQ : IsFiveNondeg k ε Q
  · have hU : IsFiveNondeg k ε (fiveOrth k ε Q) := by
      have h := isFiveNondeg_inf_fiveOrth (k := k) (ε := ε) (W := ⊤) (U := Q)
        (isFiveNondeg_top k ε) hQ le_top
      rwa [top_inf_eq] at h
    have hdim : 2 ≤ Module.finrank (ZMod 5) ↥(fiveOrth k ε Q) := by
      have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := ⊤) (U := Q)
        (isFiveNondeg_top k ε) le_top
      rw [top_inf_eq, finrank_top_five] at h
      have hQle : Module.finrank (ZMod 5) Q ≤ 2 := finrank_sup_span_le_two v w
      have hX : Module.finrank (ZMod 5) ↥(fiveOrth k ε Q) =
          k + 1 - Module.finrank (ZMod 5) Q := by omega
      have h2 : 2 ≤ k + 1 - Module.finrank (ZMod 5) Q := by omega
      omega
    exact exists_fiveForm_eq_of_nondeg hU hdim (c := c)
  · rw [isFiveNondeg_iff] at hQ
    simp only [not_forall] at hQ
    obtain ⟨r, hrQ, hrQorth, hrne⟩ := hQ
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hrQ
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hb : b ≠ 0 := by
      intro hb0
      have hr0 : r = a • v := by rw [← hyz, hb0, zero_smul, add_zero]
      have hrv : fiveForm k ε r v = 0 :=
        hrQorth v (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
      have h0 : a * fiveForm k ε v v = 0 := by rw [← hrv, hr0, fiveForm_smul_left]
      have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_right hv
      exact hrne (by rw [← hyz, hb0, ha0, zero_smul, zero_smul, add_zero])
    have hw_mem : w ∈ Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
        Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) := by
      have hsub : r - a • v = b • w := by
        rw [← hyz]
        ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf
      have hw_eq : w = b⁻¹ • (r - a • v) := by
        rw [hsub, smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [hw_eq]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self r))
        (Submodule.mem_sup_left (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v))))
    have hQle : Q ≤ Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
        Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) := by
      rw [hQdef]
      apply sup_le
      · exact le_sup_left
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem)
    have hQge : Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
        Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ≤ Q := by
      apply sup_le
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
          (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)))
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hrQ)
    have hQeq : Q = Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)) ⊔
        Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) := le_antisymm hQle hQge
    have hQr : fiveForm k ε r r = 0 := hrQorth r hrQ
    set W := fiveOrth k ε (Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)))
      with hWdef
    have hW : IsFiveNondeg k ε W := by
      have h := isFiveNondeg_inf_fiveOrth (k := k) (ε := ε) (W := ⊤)
        (U := Submodule.span (ZMod 5) ({v} : Set (Fin (k + 1) → ZMod 5)))
        (isFiveNondeg_top k ε) (isFiveNondeg_span_singleton hv) le_top
      rwa [top_inf_eq] at h
    have hrW : r ∈ W := by
      rw [hWdef, mem_fiveOrth]
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨t, rfl⟩ := hu
      rw [fiveForm_smul_right,
        hrQorth v (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)), mul_zero]
    have hWdim : k ≤ Module.finrank (ZMod 5) ↥W := by
      rw [hWdef]
      exact le_finrank_fiveOrth_singleton v
    obtain ⟨w', hw'W, hw'r⟩ : ∃ w' ∈ W, fiveForm k ε w' r ≠ 0 := by
      by_contra h
      push Not at h
      exact hrne ((isFiveNondeg_iff.1 hW) r hrW (fun y hy => by rw [fiveForm_comm]; exact h y hy))
    set t : ZMod 5 := fiveForm k ε w' w' * (2 * fiveForm k ε w' r)⁻¹ with ht
    set r₂ : Fin (k + 1) → ZMod 5 := w' - t • r with hr₂
    have h2B : (2 : ZMod 5) * fiveForm k ε w' r ≠ 0 :=
      mul_ne_zero (by decide) hw'r
    have hr₂Q : fiveForm k ε r₂ r₂ = 0 := by
      rw [hr₂, fiveForm_sub_smul, fiveForm_comm k ε r w', hQr, mul_zero, add_zero]
      rw [ht]
      field_simp [h2B]
      ring
    have hr₂r : fiveForm k ε r₂ r = fiveForm k ε w' r := by
      rw [hr₂, fiveForm_sub_left, fiveForm_smul_left, hQr, mul_zero]
      exact sub_zero _
    have hH : IsFiveNondeg k ε
        (Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
          Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5))) := by
      rw [isFiveNondeg_iff]
      intro x hx hxorth
      rw [Submodule.mem_sup] at hx
      obtain ⟨x1, hx1, x2, hx2, hx12⟩ := hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx1
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      have h1 : fiveForm k ε (a • r + b • r₂) r = 0 := by
        rw [hx12]
        exact hxorth r (Submodule.mem_sup_left (Submodule.mem_span_singleton_self r))
      have h2 : fiveForm k ε (a • r + b • r₂) r₂ = 0 := by
        rw [hx12]
        exact hxorth r₂ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self r₂))
      rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hQr, hr₂r, mul_zero,
        zero_add] at h1
      have hb0 : b = 0 := (mul_eq_zero.mp h1).resolve_right hw'r
      rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, fiveForm_comm k ε r r₂,
        hr₂r, hr₂Q, mul_zero, add_zero] at h2
      have ha0 : a = 0 := (mul_eq_zero.mp h2).resolve_right hw'r
      rw [← hx12, ha0, hb0, zero_smul, zero_smul, add_zero]
    have hHW : Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
        Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5)) ≤ W := by
      apply sup_le
      · exact Submodule.span_le.mpr (by
          intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hrW)
      · exact Submodule.span_le.mpr (by
          intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz
          rw [hr₂]
          exact Submodule.sub_mem _ hw'W (Submodule.smul_mem _ _ hrW))
    have hHdim : 2 ≤ Module.finrank (ZMod 5)
        ↥(W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
          Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5)))) := by
      have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := W)
        (U := Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
          Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5))) hW hHW
      have hHle := finrank_sup_span_le_two r r₂
      have hX : Module.finrank (ZMod 5)
          ↥(W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
            Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5)))) =
          Module.finrank (ZMod 5) W - Module.finrank (ZMod 5)
            ↥(Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
              Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5))) := by omega
      have h2 : 2 ≤ Module.finrank (ZMod 5) W - Module.finrank (ZMod 5)
            ↥(Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
              Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5))) := by omega
      omega
    have hHnd : IsFiveNondeg k ε
        (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) ({r} : Set (Fin (k + 1) → ZMod 5)) ⊔
          Submodule.span (ZMod 5) ({r₂} : Set (Fin (k + 1) → ZMod 5)))) :=
      isFiveNondeg_inf_fiveOrth hW hH hHW
    obtain ⟨y, hyH, hyQ⟩ := exists_fiveForm_eq_of_nondeg hHnd hHdim (c := c)
    refine ⟨y, ?_, hyQ⟩
    rw [hQeq, mem_fiveOrth]
    intro u hu
    obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Submodule.mem_sup.mp hu
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu1
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hu2
    have hyv : fiveForm k ε y v = 0 := by
      have h := hyH.1
      rw [hWdef] at h
      exact (mem_fiveOrth.mp h) v (Submodule.mem_span_singleton_self v)
    have hyr : fiveForm k ε y r = 0 := by
      have h := hyH.2
      exact (mem_fiveOrth.mp h) r (Submodule.mem_sup_left (Submodule.mem_span_singleton_self r))
    rw [← hu12, fiveForm_add_right, fiveForm_smul_right, fiveForm_smul_right, hyv, hyr,
      mul_zero, mul_zero, add_zero]

private theorem exists_mem_closure_of_fiveForm_ne_zero {D : Set G} {a : G} {k : ℕ} {ε π : Bool}
    (ca : FiveLocalModel D a k ε π) {y : Fin (k + 1) → ZMod 5}
    (hy0 : fiveForm k ε y y ≠ 0) (hyπ : IsSquare (fiveForm k ε y y) ↔ π = true) :
    ∃ x : Subgroup.closure (commSet D a),
      (ca.toMulEquiv x : GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε y := by
  refine ⟨ca.toMulEquiv.symm
    ⟨fiveReflOf k ε y, Subgroup.subset_closure (fiveReflOf_mem hy0 hyπ)⟩, ?_⟩
  rw [MulEquiv.apply_symm_apply]

theorem edgeCover_five {D : Set G} {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hD : FiveLocalData D k ε π) {u : G} (hu : u ∈ D) :
    ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Commute a b →
      (commSet D u ∩ commSet D a ∩ commSet D b).Nonempty := by
  intro a ha b hb hab hcomm
  obtain ⟨ca⟩ := (hD a ha).1
  have hhyp : FiveHyperplaneData ca := (hD a ha).2 ca
  have hb_mem : b ∈ commSet D a := ⟨hb, hcomm.symm, fun h => hab h.symm⟩
  obtain ⟨β, hβ0, hβπ, hβeq⟩ := exists_axis_of_fiveLocalModel ca hb_mem
  set c : ZMod 5 := fiveSignRep π with hcdef
  have hc0 : c ≠ 0 := fiveSignRep_ne_zero π
  have hcπ : IsSquare c ↔ π = true := isSquare_fiveSignRep_iff π
  have mk_x : ∀ {y : Fin (k + 1) → ZMod 5}, fiveForm k ε y y ≠ 0 →
      (IsSquare (fiveForm k ε y y) ↔ π = true) → fiveForm k ε β y = 0 →
      ∃ x : G, x ∈ commSet D a ∧ x ∈ commSet D b := by
    intro y hy0 hyπ hyβ
    obtain ⟨x, hxeq⟩ := exists_mem_closure_of_fiveForm_ne_zero ca hy0 hyπ
    have hxmem : (x : G) ∈ commSet D a := by
      rw [ca.mem_iff, hxeq]
      exact fiveReflOf_mem hy0 hyπ
    have hxeq' : (ca.toMulEquiv ⟨(x : G), Subgroup.subset_closure hxmem⟩ :
        GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε y := by
      rw [show (⟨(x : G), Subgroup.subset_closure hxmem⟩ :
          Subgroup.closure (commSet D a)) = x from Subtype.ext rfl]
      exact hxeq
    have hxb : (x : G) ∈ commSet D b := by
      refine (mem_commSet_iff_of_fiveLocalModel ca hb_mem hxmem hβ0 hβeq).2 ?_
      rw [hxeq', fiveReflOf_mulVec, hyβ]; simp
    exact ⟨(x : G), hxmem, hxb⟩
  have hcase_ab : (commSet D a ∩ commSet D b).Nonempty := by
    obtain ⟨y, hyU, hyQ⟩ :=
      exists_fiveForm_eq_of_orth_sup (k := k) (ε := ε) hk (v := β) (w := 0) hβ0 (c := c)
    have hy0 : fiveForm k ε y y ≠ 0 := by rw [hyQ]; exact hc0
    have hyπ : IsSquare (fiveForm k ε y y) ↔ π = true := by rw [hyQ]; exact hcπ
    have hyβ : fiveForm k ε β y = 0 := by
      rw [mem_fiveOrth] at hyU
      rw [fiveForm_comm]
      exact hyU β (Submodule.mem_sup_left (Submodule.mem_span_singleton_self β))
    obtain ⟨x, hxmem, hxb⟩ := mk_x hy0 hyπ hyβ
    exact ⟨x, hxmem, hxb⟩
  by_cases hua : u = a
  · obtain ⟨x, hxmem, hxb⟩ := hcase_ab
    refine ⟨x, ⟨⟨?_, hxmem⟩, hxb⟩⟩
    rw [hua]
    exact hxmem
  by_cases hub : u = b
  · obtain ⟨x, hxmem, hxb⟩ := hcase_ab
    refine ⟨x, ⟨⟨?_, hxmem⟩, hxb⟩⟩
    rw [hub]
    exact hxb
  by_cases hcommua : Commute u a
  ·
    have hu_mem : u ∈ commSet D a := ⟨hu, hcommua, hua⟩
    obtain ⟨μ, hμ0, hμπ, hμeq⟩ := exists_axis_of_fiveLocalModel ca hu_mem
    obtain ⟨y, hyU, hyQ⟩ :=
      exists_fiveForm_eq_of_orth_sup (k := k) (ε := ε) hk (v := μ) (w := β) hμ0 (c := c)
    have hy0 : fiveForm k ε y y ≠ 0 := by rw [hyQ]; exact hc0
    have hyπ : IsSquare (fiveForm k ε y y) ↔ π = true := by rw [hyQ]; exact hcπ
    have hyβ : fiveForm k ε β y = 0 := by
      rw [mem_fiveOrth] at hyU
      rw [fiveForm_comm]
      exact hyU β (Submodule.mem_sup_right (Submodule.mem_span_singleton_self β))
    have hyμ : fiveForm k ε μ y = 0 := by
      rw [mem_fiveOrth] at hyU
      rw [fiveForm_comm]
      exact hyU μ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self μ))
    obtain ⟨x', hxeq'⟩ := exists_mem_closure_of_fiveForm_ne_zero ca hy0 hyπ
    have hxmem' : (x' : G) ∈ commSet D a := by
      rw [ca.mem_iff, hxeq']
      exact fiveReflOf_mem hy0 hyπ
    have hxeq'' : (ca.toMulEquiv ⟨(x' : G), Subgroup.subset_closure hxmem'⟩ :
        GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε y := by
      rw [show (⟨(x' : G), Subgroup.subset_closure hxmem'⟩ :
          Subgroup.closure (commSet D a)) = x' from Subtype.ext rfl]
      exact hxeq'
    have hxb' : (x' : G) ∈ commSet D b := by
      refine (mem_commSet_iff_of_fiveLocalModel ca hb_mem hxmem' hβ0 hβeq).2 ?_
      rw [hxeq'', fiveReflOf_mulVec, hyβ]; simp
    have hxu : (x' : G) ∈ commSet D u := by
      refine (mem_commSet_iff_of_fiveLocalModel ca hu_mem hxmem' hμ0 hμeq).2 ?_
      rw [hxeq'', fiveReflOf_mulVec, hyμ]; simp
    exact ⟨(x' : G), ⟨⟨hxu, hxmem'⟩, hxb'⟩⟩
  ·
    obtain ⟨z, hz0, _hzprop, hziff⟩ := hhyp u hu hcommua
    obtain ⟨y, hyU, hyQ⟩ :=
      exists_fiveForm_eq_of_orth_sup (k := k) (ε := ε) hk (v := β) (w := z) hβ0 (c := c)
    have hy0 : fiveForm k ε y y ≠ 0 := by rw [hyQ]; exact hc0
    have hyπ : IsSquare (fiveForm k ε y y) ↔ π = true := by rw [hyQ]; exact hcπ
    have hyβ : fiveForm k ε β y = 0 := by
      rw [mem_fiveOrth] at hyU
      rw [fiveForm_comm]
      exact hyU β (Submodule.mem_sup_left (Submodule.mem_span_singleton_self β))
    have hyz : fiveForm k ε z y = 0 := by
      rw [mem_fiveOrth] at hyU
      rw [fiveForm_comm]
      exact hyU z (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    obtain ⟨x', hxeq'⟩ := exists_mem_closure_of_fiveForm_ne_zero ca hy0 hyπ
    have hxmem' : (x' : G) ∈ commSet D a := by
      rw [ca.mem_iff, hxeq']
      exact fiveReflOf_mem hy0 hyπ
    have hxeq'' : (ca.toMulEquiv ⟨(x' : G), Subgroup.subset_closure hxmem'⟩ :
        GL (Fin (k + 1)) (ZMod 5)) = fiveReflOf k ε y := by
      rw [show (⟨(x' : G), Subgroup.subset_closure hxmem'⟩ :
          Subgroup.closure (commSet D a)) = x' from Subtype.ext rfl]
      exact hxeq'
    have hxb' : (x' : G) ∈ commSet D b := by
      refine (mem_commSet_iff_of_fiveLocalModel ca hb_mem hxmem' hβ0 hβeq).2 ?_
      rw [hxeq'', fiveReflOf_mulVec, hyβ]; simp
    have hxu : (x' : G) ∈ commSet D u := by
      refine ⟨hxmem'.1, ?_, ?_⟩
      · refine (hziff ⟨(x' : G), Subgroup.subset_closure hxmem'⟩ hxmem').2 ?_
        rw [hxeq'', fiveReflOf_mulVec, hyz]; simp
      · intro hxu_eq
        exact hcommua (hxu_eq ▸ hxmem'.2.1)
    exact ⟨(x' : G), ⟨⟨hxu, hxmem'⟩, hxb'⟩⟩

end CFSG.OddTranspositions.PartThree

end
