module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.BruhatNo117
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.F4ExplicitPos.PositiveNo117 CFSG.StandardType.F4ExplicitPos.UnipotentNo117
open scoped Pointwise
variable {K : Type} [Field K]

theorem f4_bruhatCell_simple_mul_of_length_eq_sub_one
    {i : Fin Tag.F4.rank}
    {w : WeylGroup Tag.F4}
    (h : (coxeterSystem Tag.F4).length (simple Tag.F4 i * w) =
      (coxeterSystem Tag.F4).length w - 1) :
    bruhatCell Tag.F4 K (simple Tag.F4 i) * bruhatCell Tag.F4 K w =
      bruhatCell Tag.F4 K (simple Tag.F4 i * w) ∪ bruhatCell Tag.F4 K w := by
  have hlen : (coxeterSystem Tag.F4).length (simple Tag.F4 i * w) + 1 =
      (coxeterSystem Tag.F4).length w := by
    rcases length_simple_mul_cases w i with h' | h'
    · omega
    · exact h'
  have hn : weylElt Tag.F4 K i 1 * canonicalRep (coxeterSystem Tag.F4) K w =
      torusElt Tag.F4 K i (-1) * canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) :=
    weylElt_mul_canonicalRep_of_length_add_one_eq hlen
  have hd : torusElt Tag.F4 K i (-1) ∈ borelGroup Tag.F4 K :=
    (le_sup_left : torusGroup Tag.F4 K ≤ borelGroup Tag.F4 K)
      (torusElt_mem_torusGroup i (-1))
  have hy : ∀ d : K, ∃ b'' ∈ borelGroup Tag.F4 K,
      yUnit Tag.F4 K i d * canonicalRep (coxeterSystem Tag.F4) K w =
        canonicalRep (coxeterSystem Tag.F4) K w * b'' := fun d =>
    exists_mul_canonicalRep_eq (isRoot_neg_single Tag.F4 i) (height_inv_smul_neg_single_pos h)
      (Subgroup.subset_closure ⟨d, pinnedX_neg_single Tag.F4 K i d⟩)
  have hrank := (simple_rank_one_bruhat_identity Tag.F4 K).2 K i
  refine Set.Subset.antisymm (fun x hx => ?_)
    (Set.union_subset (fun x hx => ?_) fun x hx => ?_)
  · obtain ⟨b, hb, b', hb', c, rfl⟩ := f4_exists_of_mem_bruhatCell_simple_mul hx
    by_cases hc : c = 0
    · left
      refine mem_bruhatCell.2 ⟨b * torusElt Tag.F4 K i (-1), mul_mem hb hd, b', hb', ?_⟩
      calc b * torusElt Tag.F4 K i (-1) *
            canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) * b' =
            b * (torusElt Tag.F4 K i (-1) *
              canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w)) * b' := by
            group
        _ = b * (weylElt Tag.F4 K i 1 * canonicalRep (coxeterSystem Tag.F4) K w) * b' := by
            rw [hn]
        _ = _ := by rw [hc, xUnit_zero, mul_one]; group
    · right
      obtain ⟨b₀, hb₀, h₀⟩ := hrank c hc
      obtain ⟨b'', hb'', h''⟩ := hy c⁻¹
      refine mem_bruhatCell.2 ⟨b * b₀, mul_mem hb hb₀, b'' * b', mul_mem hb'' hb', ?_⟩
      calc b * b₀ * canonicalRep (coxeterSystem Tag.F4) K w * (b'' * b') =
            b * b₀ * (canonicalRep (coxeterSystem Tag.F4) K w * b'') * b' := by group
        _ = b * b₀ * (yUnit Tag.F4 K i c⁻¹ * canonicalRep (coxeterSystem Tag.F4) K w) * b' := by
            rw [h'']
        _ = b * (b₀ * yUnit Tag.F4 K i c⁻¹) * canonicalRep (coxeterSystem Tag.F4) K w * b' := by
            group
        _ = _ := by rw [h₀]
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    have e : b * (torusElt Tag.F4 K i (-1))⁻¹ * weylElt Tag.F4 K i 1 * 1 *
        (1 * canonicalRep (coxeterSystem Tag.F4) K w * b') =
          b * canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) * b' := by
      calc _ = b * (torusElt Tag.F4 K i (-1))⁻¹ *
            (weylElt Tag.F4 K i 1 * canonicalRep (coxeterSystem Tag.F4) K w) * b' := by group
        _ = _ := by rw [hn]; group
    rw [← e]
    exact mem_bruhatCell_simple_mul (mul_mem hb (inv_mem hd)) (one_mem _) (one_mem _) hb'
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    obtain ⟨b₀, hb₀, h₀⟩ := hrank 1 one_ne_zero
    obtain ⟨b'', hb'', h''⟩ := hy 1⁻¹
    have key : weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i 1 *
        canonicalRep (coxeterSystem Tag.F4) K w =
        b₀ * (canonicalRep (coxeterSystem Tag.F4) K w * b'') := by
      rw [h₀, mul_assoc, h'']
    have e : b * b₀⁻¹ * weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i 1 *
        (1 * canonicalRep (coxeterSystem Tag.F4) K w * (b''⁻¹ * b')) =
          b * canonicalRep (coxeterSystem Tag.F4) K w * b' := by
      calc _ = b * b₀⁻¹ * (weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i 1 *
            canonicalRep (coxeterSystem Tag.F4) K w) * b''⁻¹ * b' := by group
        _ = _ := by rw [key]; group
    rw [← e]
    exact mem_bruhatCell_simple_mul (mul_mem hb (inv_mem hb₀)) (xUnit_mem_borelGroup i 1)
      (one_mem _) (mul_mem (inv_mem hb'') hb')

theorem f4_bruhatCell_simple_mul_subset
    (i : Fin Tag.F4.rank) (w : WeylGroup Tag.F4) :
    bruhatCell Tag.F4 K (simple Tag.F4 i) * bruhatCell Tag.F4 K w ⊆
      bruhatCell Tag.F4 K (simple Tag.F4 i * w) ∪ bruhatCell Tag.F4 K w := by
  rcases length_simple_mul_cases w i with h | h
  · rw [f4_bruhatCell_simple_mul_of_length_eq_add_one h]
    exact Set.subset_union_left
  · rw [f4_bruhatCell_simple_mul_of_length_eq_sub_one (by omega)]

theorem f4_adjointGroup_eq_iUnion_bruhatCell :
    (adjointGroup Tag.F4 K : Set (ModGL Tag.F4 K)) = ⋃ w, bruhatCell Tag.F4 K w := by
  refine Set.Subset.antisymm (fun g hg => ?_)
    (Set.iUnion_subset fun w => bruhatCell_subset_adjointGroup w)
  set X := ⋃ w, bruhatCell Tag.F4 K w
  have hB : ∀ b ∈ borelGroup Tag.F4 K, ∀ x ∈ X, b * x ∈ X := fun b hb x hx => by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hw
    exact Set.mem_iUnion.2 ⟨w, mem_bruhatCell.2 ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩⟩
  have hn : ∀ i, ∀ x ∈ X, weylElt Tag.F4 K i 1 * x ∈ X := fun i x hx => by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    have hmem : weylElt Tag.F4 K i 1 * x ∈
        bruhatCell Tag.F4 K (simple Tag.F4 i) * bruhatCell Tag.F4 K w := by
      refine Set.mem_mul.2 ⟨_, ?_, x, hw, rfl⟩
      rw [← canonicalRep_simple (coxeterSystem Tag.F4) K i]
      exact canonicalRep_mem_bruhatCell _
    rcases f4_bruhatCell_simple_mul_subset i w hmem with h | h
    exacts [Set.mem_iUnion.2 ⟨_, h⟩, Set.mem_iUnion.2 ⟨_, h⟩]
  have hS : adjointGroup Tag.F4 K ≤ MulAction.stabilizer (ModGL Tag.F4 K) X := by
    rw [(borel_weyl_generation Tag.F4 K).1]
    refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact smul_set_eq_of_forall (hB b hb) (hB b⁻¹ (inv_mem hb))
    · rintro _ ⟨i, rfl⟩
      refine smul_set_eq_of_forall (hn i) fun x hx => ?_
      have e : (weylElt Tag.F4 K i 1)⁻¹ =
          (torusElt Tag.F4 K i (-1))⁻¹ * weylElt Tag.F4 K i 1 := by
        rw [← weylElt_one_mul_self, mul_inv_rev, inv_mul_cancel_right]
      rw [e, mul_assoc]
      exact hB _ (inv_mem ((le_sup_left : torusGroup Tag.F4 K ≤ borelGroup Tag.F4 K)
        (torusElt_mem_torusGroup i (-1)))) _ (hn i x hx)
  have hg' : g • X = X := hS hg
  rw [← hg']
  exact ⟨1, Set.mem_iUnion.2 ⟨1, one_mem_bruhatCell_one⟩, mul_one g⟩

theorem f4_posUnipotent_eq_mul_rootSpan
    (w : WeylGroup Tag.F4) :
    (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) =
      (rootSpan Tag.F4 K (nonInversionSet w) : Set (ModGL Tag.F4 K)) *
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K)) := by
  refine Set.Subset.antisymm (fun u hu => ?_) ?_
  · obtain ⟨αJ, hJinj, hJrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos
      fun α h => nonInversionSet_pos (w := w) h)
    obtain ⟨αI, hIinj, hIrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos
      fun α h => inversionSet_pos (w := w) h)
    have hJ : ∀ k, αJ k ∈ nonInversionSet w := fun k => hJrange ▸ Set.mem_range_self k
    have hI : ∀ k, αI k ∈ inversionSet w := fun k => hIrange ▸ Set.mem_range_self k
    set α := Fin.append αJ αI
    have hdisj : ∀ k l, αJ k ≠ αI l := fun k l h => by
      have h1 := (hJ k).2.2
      have h2 := (hI l).2.2.2
      rw [h] at h1
      omega
    have hinj : Function.Injective α := by
      intro k l h
      induction k using Fin.addCases with
      | left k =>
        induction l using Fin.addCases with
        | left l => simp only [α, Fin.append_left] at h; rw [hJinj h]
        | right l =>
          simp only [α, Fin.append_left, Fin.append_right] at h
          exact absurd h (hdisj k l)
      | right k =>
        induction l using Fin.addCases with
        | left l =>
          simp only [α, Fin.append_left, Fin.append_right] at h
          exact absurd h.symm (hdisj l k)
        | right l => simp only [α, Fin.append_right] at h; rw [hIinj h]
    have hrange : Set.range α = {β | IsRoot Tag.F4 β ∧ 0 < height β} := by
      ext β
      constructor
      · rintro ⟨k, rfl⟩
        induction k using Fin.addCases with
        | left k => simpa [α] using nonInversionSet_pos (hJ k)
        | right k => simpa [α] using inversionSet_pos (hI k)
      · rintro ⟨hβ, hβp⟩
        rcases IsRoot.height_pos_or_neg (IsRoot.smul hβ w) with hp | hn
        · obtain ⟨k, hk⟩ : β ∈ Set.range αJ := by
            rw [hJrange]
            exact ⟨hβ, hβp, hp⟩
          exact ⟨Fin.castAdd _ k, by simp [α, hk]⟩
        · obtain ⟨k, hk⟩ : β ∈ Set.range αI := by
            rw [hIrange]
            exact ⟨hβ, hβp, IsRoot.smul hβ w, hn⟩
          exact ⟨Fin.natAdd _ k, by simp [α, hk]⟩
    obtain ⟨c, -, rfl⟩ := ((f4_positive_root_collection K).2 α hinj hrange).2.2 hu
    refine ⟨_, list_prod_pinnedX_mem_rootSpan αJ hJ (fun k => c (Fin.castAdd _ k)), _,
      list_prod_pinnedX_mem_rootSpan αI hI (fun k => c (Fin.natAdd _ k)), ?_⟩
    simp only
    rw [← List.prod_append, ← List.ofFn_fin_append]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    induction k using Fin.addCases with
    | left k => simp [α]
    | right k => simp [α]
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    exact mul_mem (rootSpan_le_posUnipotent (fun α h => nonInversionSet_pos (w := w) h) hu)
      (rootSpan_le_posUnipotent (fun α h => inversionSet_pos (w := w) h) hv)

theorem f4_hfactor :
    ∀ g ∈ adjointGroup Tag.F4 K, ∃ w : WeylGroup Tag.F4,
    ∃ h ∈ torusGroup Tag.F4 K, ∃ u ∈ posUnipotent Tag.F4 K,
    ∃ v ∈ rootSpan Tag.F4 K (inversionSet w),
      g = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := by
  intro g hg
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  have hg' : g ∈ (adjointGroup Tag.F4 K : Set (ModGL Tag.F4 K)) := hg
  rw [f4_adjointGroup_eq_iUnion_bruhatCell, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem Tag.F4) K w with hn
  obtain ⟨h, hh, u, hu, rfl⟩ := (by
    have : b ∈ (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
        (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [← hTB.2.2.2.2.1]
      exact hb
    exact this)
  obtain ⟨h', hh', u', hu', rfl⟩ := (by
    have : b' ∈ (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
        (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [← hTB.2.2.2.2.1]
      exact hb'
    exact this)
  obtain ⟨uJ, huJ, uw, huw, rfl⟩ := (by
    have : u' ∈ (rootSpan Tag.F4 K (nonInversionSet w) : Set (ModGL Tag.F4 K)) *
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K)) := by
      rw [← f4_posUnipotent_eq_mul_rootSpan w]
      exact hu'
    exact this)
  have hnh' : n * h' * n⁻¹ ∈ torusGroup Tag.F4 K :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) h').1 hh'
  have hnuJ : n * uJ * n⁻¹ ∈ posUnipotent Tag.F4 K := canonicalRep_conj_mem_posUnipotent huJ
  obtain ⟨h'', hh'', u'', hu'', hbu⟩ := (by
    have : (h * u) * (n * h' * n⁻¹) * (n * uJ * n⁻¹) ∈
        (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
        (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [← hTB.2.2.2.2.1]
      exact mul_mem (mul_mem (mul_mem
        ((le_sup_left : torusGroup Tag.F4 K ≤ borelGroup Tag.F4 K) hh)
        ((le_sup_right : posUnipotent Tag.F4 K ≤ borelGroup Tag.F4 K) hu))
        ((le_sup_left : torusGroup Tag.F4 K ≤ borelGroup Tag.F4 K) hnh'))
        ((le_sup_right : posUnipotent Tag.F4 K ≤ borelGroup Tag.F4 K) hnuJ)
    exact this)
  refine ⟨w, h'', hh'', u'', hu'', uw, huw, ?_⟩
  calc (h * u) * n * (h' * (uJ * uw))
      = (h * u) * (n * h' * n⁻¹) * (n * uJ * n⁻¹) * n * uw := by group
    _ = h'' * u'' * n * uw := by rw [← hbu]

theorem f4_sameW_bruhat_unique
    {w : WeylGroup Tag.F4} {h h' u u' v v' : ModGL Tag.F4 K}
    (hh : h ∈ torusGroup Tag.F4 K) (hh' : h' ∈ torusGroup Tag.F4 K)
    (hu : u ∈ posUnipotent Tag.F4 K) (hu' : u' ∈ posUnipotent Tag.F4 K)
    (hv : v ∈ rootSpan Tag.F4 K (inversionSet w))
    (hv' : v' ∈ rootSpan Tag.F4 K (inversionSet w))
    (heq : h * u * canonicalRep (coxeterSystem Tag.F4) K w * v =
           h' * u' * canonicalRep (coxeterSystem Tag.F4) K w * v') :
    h = h' ∧ u = u' ∧ v = v' := by
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  set n := canonicalRep (coxeterSystem Tag.F4) K w
  have hb : h * u ∈ borelGroup Tag.F4 K :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)
  have hb' : h' * u' ∈ borelGroup Tag.F4 K :=
    mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right hu')
  have hconj : (h' * u')⁻¹ * (h * u) = n * (v' * v⁻¹) * n⁻¹ := by
    have h1 : (h' * u')⁻¹ * (h * u) * n = n * (v' * v⁻¹) := by
      calc (h' * u')⁻¹ * (h * u) * n
          = (h' * u')⁻¹ * (h * u * n * v) * v⁻¹ := by group
        _ = (h' * u')⁻¹ * (h' * u' * n * v') * v⁻¹ := by rw [heq]
        _ = n * (v' * v⁻¹) := by group
    calc (h' * u')⁻¹ * (h * u) = (h' * u')⁻¹ * (h * u) * n * n⁻¹ := by group
      _ = n * (v' * v⁻¹) * n⁻¹ := by rw [h1]
  have hmem : (h' * u')⁻¹ * (h * u) ∈ borelGroup Tag.F4 K ⊓ negUnipotent Tag.F4 K := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hb') hb, ?_⟩
    rw [hconj]
    exact canonicalRep_conj_mem_negUnipotent (mul_mem hv' (inv_mem hv))
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
  have hbu : h * u = h' * u' := by
    have := congrArg (fun x => h' * u' * x) hmem
    simpa [mul_assoc] using this
  have hvv : v = v' := by
    have heq' : h' * u' * n * v = h' * u' * n * v' := by
      have h := heq
      rw [hbu] at h
      exact h
    exact mul_left_cancel (mul_left_cancel (mul_left_cancel heq'))
  obtain ⟨h1, h2⟩ := hTB.2.2.2.2.2.2.1 h hh h' hh' u hu u' hu' hbu
  exact ⟨h1, h2, hvv⟩

theorem f4_hX
    (a : Fin Tag.F4.rank → Kˣ) :
    ∀ g ∈ toralCentralizer Tag.F4 K a, ∃ w ∈ rootCharStabilizer a,
      ∃ h ∈ torusGroup Tag.F4 K,
      ∃ u ∈ rootSpan Tag.F4 K (rootCharKernel a ∩ {α | IsRoot Tag.F4 α ∧ 0 < height α}),
      ∃ v ∈ rootSpan Tag.F4 K (rootCharKernel a ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := by
  intro g hg
  have hTB := triangular_borel_structure.{0, 0} Tag.F4 K
  obtain ⟨hgC, hgfix⟩ := mem_toralCentralizer.1 hg
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := f4_hfactor g hgC
  set d := rootDiagUnit Tag.F4 a with hd
  obtain ⟨t, ht, hnt⟩ := exists_conj_canonicalRep a w
  have hdu : d * u * d⁻¹ ∈ posUnipotent Tag.F4 K := by
    have hmap : (posUnipotent Tag.F4 K).map (MulAut.conj d).toMonoidHom =
        posUnipotent Tag.F4 K :=
      map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
    rw [← hmap]
    exact ⟨u, hu, rfl⟩
  have hdv : d * v * d⁻¹ ∈ rootSpan Tag.F4 K (inversionSet w) := by
    have : (rootSpan Tag.F4 K (inversionSet w)).map (MulAut.conj d).toMonoidHom =
        rootSpan Tag.F4 K (inversionSet w) :=
      map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
    rw [← this]
    exact ⟨v, hv, rfl⟩
  have hu' : t⁻¹ * (d * u * d⁻¹) * t ∈ posUnipotent Tag.F4 K := by
    have hN := hTB.2.2.1 (inv_mem ht)
    have := (Subgroup.mem_normalizer_iff.1 hN (d * u * d⁻¹)).1 hdu
    simpa using this
  have heq : h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem Tag.F4) K w *
      (d * v * d⁻¹) = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := by
    calc h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem Tag.F4) K w *
          (d * v * d⁻¹) =
        (d * h * d⁻¹) * (d * u * d⁻¹) * (t * canonicalRep (coxeterSystem Tag.F4) K w) *
          (d * v * d⁻¹) := by
          rw [conj_rootDiagUnit_of_mem_torusGroup a hh]
          group
      _ = (d * h * d⁻¹) * (d * u * d⁻¹) *
          (d * canonicalRep (coxeterSystem Tag.F4) K w * d⁻¹) * (d * v * d⁻¹) := by rw [hnt]
      _ = d * (h * u * canonicalRep (coxeterSystem Tag.F4) K w * v) * d⁻¹ := by group
      _ = h * u * canonicalRep (coxeterSystem Tag.F4) K w * v := hgfix
  obtain ⟨h1, h2, h3⟩ := f4_sameW_bruhat_unique (w := w)
    (h := h * t) (h' := h) (u := t⁻¹ * (d * u * d⁻¹) * t) (u' := u)
    (v := d * v * d⁻¹) (v' := v)
    (mul_mem hh ht) hh hu' hu hdv hv heq
  have ht1 : t = 1 := by
    have := h1
    rwa [mul_eq_left] at this
  subst ht1
  have hufix : d * u * d⁻¹ = u := by simpa using h2
  have hw : w ∈ rootCharStabilizer a := by
    rw [← conj_canonicalRep_eq_iff, ← hd, hnt, one_mul]
  refine ⟨w, hw, h, hh, u, ?_, v, ?_, rfl⟩
  · have hposfin : {β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β}.Finite :=
      (finite_setOf_isRoot Tag.F4).subset fun β hβ => hβ.1
    exact mem_rootSpan_inter_of_conj_eq a hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (f4_positive_root_collection K).2 α hα hr) hu hufix
  · exact mem_rootSpan_inter_of_conj_eq a (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (f4_positive_root_collection K).1 (inversionSet w)
        (fun β hβ => inversionSet_pos hβ)
        (fun α hα β hβ a b ha hb hr => inversionSet_closed w α hα β hβ a b ha hb hr)
        α hα hr) hv h3

end CFSG.StandardType.F4ExplicitPos.BruhatNo117

end

end
